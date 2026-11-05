// WASM.3a/WASM.4a: каталог функций входного языка (--math) для справочника и автодополнения.
// Источник — docs/math-language.md: таблицы «| `имя(args)` | описание |», пункты-описания и строки `math> имя(...)`.
// Тема — ближайший заголовок ##/###; пример — первая строка `math> имя(...)`, которая реально вычисляется.
// Запуск: npm run gen:functions -- app/functions.json   (вызывается из web/build.cmd|.sh)
import { existsSync, readFileSync, writeFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..')
const DOC = join(ROOT, 'docs', 'math-language.md')

const SUMMARY_MAX = 100
const PLACE = '\u25a2'   // ▢ — место ввода

const ROW = /^\|\s*(.+?)\s*\|\s*(.*?)\s*\|\s*$/
const HEAD = /^(#{2,3})\s+(.+?)\s*$/
const CODE = /^\s*math>\s*(.*)$/
const BULLET = /^[*\-]\s+(.*)$/
const CALL = /`([A-Za-z][A-Za-z0-9_]*)\(([^`]*)`/g
const BARE = /`([A-Za-z][A-Za-z0-9_]{1,}(?: [A-Za-z][A-Za-z0-9_]{1,})+)[.,]?`/g
const CALL2 = /(?<![\w`])([A-Za-z][A-Za-z0-9_]*)\(([^()]*)\)/g
// формы-определения и служебные конструкции, которым не место в автодополнении вызовом
const SKIP = new Set(['f', 'foo'])
const SKIP_SIG = [':=']

// WASM.4b: темы справочника — 15 областей в постоянном порядке; «Служебное» всегда последняя.
// Список и порядок — из карточки WASM.4 (П1); «Графиков» и «Преобразований» здесь нет:
// plot(…) рисует интерфейс, а Laplace/Фурье/Z в языке не описаны — тем с пустым набором не заводим.
export const TOPICS = [
  'Арифметика и элементарные функции',
  'Алгебра и многочлены',
  'Уравнения и неравенства',
  'Пределы',
  'Производные и ряды',
  'Интегралы',
  'Суммы и рекуррентности',
  'ОДУ',
  'Линейная алгебра',
  'Теория чисел',
  'Спецфункции',
  'Множества, интервалы, логика',
  'Геометрия и кривые',
  'Программирование',
  'Служебное',
] as const

// привязка «раздел docs/math-language.md → тема» (заголовок без номера шага)
const HEADING_TOPIC: Readonly<Record<string, string>> = {
  'Элементарные функции': 'Арифметика и элементарные функции',
  'Комбинаторные функции': 'Арифметика и элементарные функции',
  'Целые числа и экстремумы': 'Теория чисел',
  'Теория чисел': 'Теория чисел',
  'Численность с сертификатами': 'Теория чисел',
  'Эллиптические интегралы': 'Спецфункции',
  'Бессель, Эйри, Лежандр': 'Спецфункции',
  'Алгебра': 'Алгебра и многочлены',
  'Базисы Грёбнера': 'Алгебра и многочлены',
  'C-конечные последовательности': 'Суммы и рекуррентности',
  'Анализ': 'Интегралы',
  'Уравнения': 'Уравнения и неравенства',
  'piecewise: кусочно-заданные выражения': 'Уравнения и неравенства',
  'ОДУ': 'ОДУ',
  'Векторы и матрицы': 'Линейная алгебра',
  'Линейная алгебра': 'Линейная алгебра',
  'Множества и домены': 'Множества, интервалы, логика',
  'Декларации': 'Множества, интервалы, логика',
  'Интервалы': 'Множества, интервалы, логика',
  'Условия': 'Программирование',
  'Блоки и циклы': 'Программирование',
  'Итераторы': 'Программирование',
  'Ряды Пюизё': 'Геометрия и кривые',
  'Дифференциальные формы и векторный анализ': 'Геометрия и кривые',
  'Особые точки и род кривой': 'Геометрия и кривые',
  'Кратные, криволинейные и поверхностные интегралы': 'Интегралы',
  'Преобразования Лапласа, Z и Фурье': 'Интегралы',
  'Переменные': 'Служебное',
  'Известные ограничения': 'Служебное',
  'Отладка упрощения': 'Служебное',
  'Пошаговые решения': 'Служебное',
  'Основы синтаксиса': 'Программирование',
  'Операторы языка': 'Программирование',
  'Операции и приоритеты': 'Программирование',
  'Литералы и константы': 'Программирование',
  'Функции': 'Программирование',
  'Запуск': 'Служебное',
  'Отличия от Lisp-режима': 'Служебное',
  'Из других программ': 'Служебное',
}

// разделы, в которых лежат функции разных областей: уточнение по имени
const NAME_TOPIC: Readonly<Record<string, string>> = {
  limit: 'Пределы',
  diff: 'Производные и ряды',
  series: 'Производные и ряды',
  taylor: 'Производные и ряды',
  integrate: 'Интегралы',
  risch_integrate: 'Интегралы',
  risch_special: 'Интегралы',
  rootsum: 'Интегралы',
  set_algorithm: 'Служебное',
  Ei: 'Спецфункции',
  li: 'Спецфункции',
  Si: 'Спецфункции',
  Ci: 'Спецфункции',
  erf: 'Спецфункции',
  erfc: 'Спецфункции',
  gamma: 'Спецфункции',
  psi: 'Спецфункции',
  harmonic: 'Суммы и рекуррентности',
  bernoulli: 'Суммы и рекуррентности',
  sum: 'Суммы и рекуррентности',
  product: 'Суммы и рекуррентности',
  iterate: 'Суммы и рекуррентности',
  iterates: 'Суммы и рекуррентности',
  select: 'Программирование',
  vector: 'Программирование',
  min: 'Арифметика и элементарные функции',
  max: 'Арифметика и элементарные функции',
  certified_integral: 'Интегралы',
  certified_sum: 'Суммы и рекуррентности',
  certified_roots: 'Уравнения и неравенства',
  denest: 'Алгебра и многочлены',
  radsimp: 'Алгебра и многочлены',
  steps: 'Служебное',
  print: 'Служебное',
  set_loop_limit: 'Служебное',
  cf_gf: 'Суммы и рекуррентности',
}

/** тема по заголовку раздела; неизвестный заголовок — ошибка сборки, а не «прочее» */
function topicOfHeading(heading: string): string {
  const t = HEADING_TOPIC[heading]
  if (!t) throw new Error('нет темы для раздела: ' + heading)
  return t
}

export interface CatalogEntry {
  name: string
  signature: string
  template: string
  summary: string
  topic: string
  example: string | null
}

interface Entry {
  name: string
  signature: string
  template: string
  summary: string
  topic: string
  prio: number
}

/** аналог re.findall для регулярки с глобальным флагом */
function findAll(re: RegExp, text: string): RegExpExecArray[] {
  const r = new RegExp(re.source, re.flags.includes('g') ? re.flags : re.flags + 'g')
  const out: RegExpExecArray[] = []
  for (;;) {
    const m = r.exec(text)
    if (!m) break
    out.push(m)
    if (m[0] === '') r.lastIndex++
  }
  return out
}

function clean(text: string): string {
  let s = text.trim()
  s = s.replace(/\*\*(.+?)\*\*/g, '$1')
  s = s.replace(/`([^`]*)`/g, '$1')
  s = s.replace(/(?<!\w)\*(?!\s)(.+?)(?<!\s)\*(?!\w)/g, '$1')
  s = s.replace(/\[([^\]]*)\]\([^)]*\)/g, '$1')
  s = s.replace(/\s+/g, ' ')
  return s.replace(/^ *\|+|\|+ *$/g, '').trim()
}

function clip(text: string, limit = SUMMARY_MAX): string {
  // считаем по кодовым точкам: в Python len() — символы, а не единицы UTF-16
  const chars = [...text]
  if (chars.length <= limit) return text
  let cut = chars.slice(0, limit - 1).join('')
  const sp = cut.lastIndexOf(' ')
  if (sp >= 0) cut = cut.slice(0, sp)
  return cut.replace(/[ ,.;:]+$/, '') + '…'
}

/**
 * фраза абзаца, где встречается имя: сначала предложение, затем (если их несколько в одном
 * перечислении) ближайшая часть между «;» — описание не должно быть общим на пять функций
 */
function sentenceOf(text: string, name: string): string {
  const parts = clean(text).split(/(?<=[.!?])\s+/)
  let picked: string | null = null
  for (const p of parts) {
    if (p.includes(name + '(')) { picked = p; break }
  }
  if (picked === null) {
    for (const p of parts) {
      if (p.includes(' ' + name)) { picked = p; break }
    }
  }
  if (picked === null) return parts[0] ?? ''
  // фраза целиком: дробление по «;» давало обрывки («w в евклидовом ℝⁿ…»)
  return picked
}

function templateOf(name: string, argtext: string): string {
  const args = argtext.trim() ? argtext.split(',').map((a) => a.trim()) : []
  if (args.length === 0) return name + '(' + PLACE + ')'
  return name + '(' + [PLACE, ...args.slice(1)].join(', ') + ')'
}

/** элементарные функции — из runtime.lisp (единый источник реализации) */
function elemNames(): string[] {
  const text = readFileSync(join(ROOT, 'lib', 'mathlang', 'runtime.lisp'), 'utf8')
  const m = /\(define m-elem-funs '\((.*?)\)\)/s.exec(text)
  return m && m[1] ? m[1].split(/\s+/).filter((s) => s !== '') : []
}

/** примеры `math> имя(...)` из руководства: имя → список строк (кандидаты в порядке появления) */
function examplesByName(): Map<string, string[]> {
  const out = new Map<string, string[]>()
  for (const line of readFileSync(DOC, 'utf8').split(/\r?\n/)) {
    const m = CODE.exec(line)
    if (!m) continue
    const code = (m[1] ?? '').trim()
    if (!code || code.includes(':=')) continue
    for (const mm of findAll(CALL2, code)) {
      const name = mm[1] ?? ''
      const list = out.get(name)
      if (list) list.push(code)
      else out.set(name, [code])
    }
  }
  return out
}

function lispExe(): string | null {
  for (const cfg of ['Debug', 'Release']) {
    const p = join(ROOT, 'src', 'Lisp.Host', 'bin', cfg, 'net10.0', 'Lisp.exe')
    if (existsSync(p)) return p
  }
  return null
}

/** первый пример, который вычисляется без ошибки (примеры из документации бывают с контекстом) */
function workingExample(exe: string | null, candidates: readonly string[]): string | null {
  if (candidates.length === 0) return null
  if (!exe) return candidates[0] ?? null
  for (const code of candidates) {
    const p = spawnSync(exe, ['--math', '-e', code], { encoding: 'utf8', timeout: 120000 })
    if (p.status === 0 && !String(p.stdout || '').includes('ОШИБКА')) return code
  }
  return null
}

export function buildCatalog(): CatalogEntry[] {
  const lines = readFileSync(DOC, 'utf8').split(/\r?\n/)
  const elem = new Set(elemNames())

  let topicH2 = ''
  let topicH3 = ''
  const entries = new Map<string, Entry>()
  const order: string[] = []
  const paragraphs = new Map<string, string>()
  const bareLists = new Map<string, string>()

  const topic = (name?: string): string =>
    (name ? NAME_TOPIC[name] : undefined) ?? topicOfHeading(topicH3 || topicH2)

  const add = (name: string, rawSignature: string, summary: string, tmpl?: string, prio = 2): void => {
    // односимвольные имена (a, f, g, t, x, y) — переменные из примеров, а не функции языка
    if (name.length < 2 || SKIP.has(name)) return
    // скобки: в ячейках таблиц встречается лишняя «)», а у сигнатур из списка закрывающей нет
    let signature = rawSignature.trim()
    if ((signature.match(/\)/g) ?? []).length > (signature.match(/\(/g) ?? []).length) {
      signature = signature.replace(/\)\s*$/, '')
    }
    if (!signature.endsWith(')')) signature += ')'
    // «имя(...)» — общая запись из текста, а не сигнатура: годится, только если другой нет
    const informative = !signature.includes('...')
    if (SKIP_SIG.some((s) => signature.includes(s))) return
    const existing = entries.get(name)
    if (existing) {
      // сигнатура и описание берутся из ОДНОЙ строки: первую осмысленную запись («имя(args…)»)
      // не перебивает более короткая из другого раздела — иначе описание описывает другую форму
      const betterSource = prio < existing.prio && informative
      if (summary && (betterSource || existing.signature.includes('...'))) {
        existing.prio = prio
        existing.topic = topic(name)
        existing.summary = clip(summary)
        existing.signature = signature
        existing.template = tmpl ?? templateOf(name, signature.slice(name.length + 1, -1))
      }
      if (!existing.summary && summary) existing.summary = clip(summary)
      return
    }
    entries.set(name, {
      name,
      signature,
      template: tmpl ?? templateOf(name, signature.slice(name.length + 1, -1)),
      summary: summary ? clip(summary) : '',
      topic: topic(name),
      prio,
    })
    order.push(name)
  }

  for (const line of lines) {
    const hm = HEAD.exec(line)
    if (hm) {
      if (hm[1] === '##') { topicH2 = hm[2] ?? ''; topicH3 = '' } else { topicH3 = hm[2] ?? '' }
      continue
    }

    const cm = CODE.exec(line)
    if (cm) continue

    // строки с «:=» — примеры определения пользовательской функции, а не описание языка
    if (line.includes(':=')) continue

    const rm = ROW.exec(line)
    if (rm) {
      const first = rm[1] ?? ''
      const desc = rm[2] ?? ''
      const calls = findAll(CALL, first)
      if (calls.length === 0) continue
      for (const [, name = '', rawArgs = ''] of calls) {
        const argtext = rawArgs.trim()
        const sig = name + '(' + argtext + ')'
        if (SKIP_SIG.some((s) => sig.includes(s))) continue
        add(name, sig, clean(desc), undefined, 0)
      }
      continue
    }

    const bm = BULLET.exec(line)
    if (bm) {
      const body = bm[1] ?? ''
      for (const [, name = '', argtext = ''] of findAll(CALL, body)) {
        add(name, name + '(' + argtext + ')', sentenceOf(body, name), undefined, 1)
      }
      continue
    }

    const text = line.trim()
    if (!text) continue
    // описания — только из строки-определения (таблица или пункт списка); проза служит лишь
    // источником абзацев для элементарных функций
    for (const mm of findAll(CALL2, text)) {
      const name = mm[1] ?? ''
      if (!entries.has(name) && !paragraphs.has(name)) paragraphs.set(name, text)
    }
    for (const mm of findAll(BARE, text)) {
      for (const name of (mm[1] ?? '').split(/\s+/)) {
        if (name && !bareLists.has(name)) bareLists.set(name, text)
      }
    }
  }

  // функция, встречающаяся вызовом, но без описания: абзац, где она упомянута
  for (const [name, para] of paragraphs) {
    const e = entries.get(name)
    if (e && !e.summary) e.summary = clip(sentenceOf(para, name))
  }

  // элементарные функции: описание — из раздела, сигнатура — name(x)
  for (const name of [...elem].sort()) {
    if (entries.has(name)) continue
    const para = bareLists.get(name) ?? paragraphs.get(name) ?? ''
    const summary = para
      ? clip(sentenceOf(para, name))
      : 'элементарная функция языка (раздел «Элементарные функции»)'
    add(name, name + '(x)', summary, name + '(' + PLACE + ')')
    const e = entries.get(name)
    if (e) e.topic = 'Элементарные функции'
  }

  const exe = lispExe()
  const cand = examplesByName()
  const rank = new Map<string, number>(TOPICS.map((t, i) => [t, i]))
  const sorted = [...order].sort((a, b) => {
    const ta = rank.get(entries.get(a)?.topic ?? '') ?? TOPICS.length
    const tb = rank.get(entries.get(b)?.topic ?? '') ?? TOPICS.length
    return ta !== tb ? ta - tb : order.indexOf(a) - order.indexOf(b)
  })
  const result: CatalogEntry[] = []
  for (const name of sorted) {
    const e = entries.get(name)
    if (!e) continue
    // пример — первый, который реально вычисляется: в документации бывают строки с контекстом
    result.push({
      name: e.name,
      signature: e.signature,
      template: e.template,
      summary: e.summary,
      topic: e.topic,
      example: workingExample(exe, cand.get(name) ?? []),
    })
  }
  return result
}

function main(): void {
  const outPath = process.argv[2]
  const data = buildCatalog()
  const text = JSON.stringify(data, null, 1) + '\n'
  if (outPath) {
    writeFileSync(outPath, text, 'utf8')
    const noSum = data.filter((x) => !x.summary).map((x) => x.name)
    const topics = new Set(data.map((x) => x.topic))
    console.log(`functions: ${data.length}, no summary: ${noSum.length}, examples: ` +
      `${data.filter((x) => x.example).length}, topics: ${topics.size} -> ${outPath}`)
    if (noSum.length) console.log('no summary: ' + noSum.slice(0, 30).join(', '))
  } else {
    process.stdout.write(text)
  }
}

// запуск только как скрипт (модуль импортируют тесты)
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main()
