// WASM.2c/WASM.4a: интерфейс на bso5 0.4.0 — mount/signal/$/For/Show, каталог на Grid, шаги на Tree,
// редактор формул на MathLive (ленивая загрузка, перевод во входной язык — mathjson.ts).
// Рантайм живёт в Worker (см. ../main.js): window.lispEval / lispLatexOfInput / lispStop / lispReady.
import { mount, signal, computed, $, For, Show } from 'bso5'
import { Grid, Tree, type TreeData } from 'bso5-components'
import { protectNames } from './latexin'
import { visibleNav, navVisible, loadExamplesOpen, saveExamplesOpen } from './nav'
import { toSource } from './mathjson'
import type { StepNode, StepRecord, StepsJson } from './steps'
import { createPlotCard, parsePlotCall, pickRange, type PlotSpec } from './plot'
import {
  createFunctionsPanel, createAssist, insertTemplate, tabToNextPlace, loadFunctions, latexTemplate,
  type Assist, type CatalogFunction,
} from './functions'

const HISTORY_KEY = 'lisp-history-v1'
const HISTORY_MAX = 30

// ---------- KaTeX ----------
function tex(latex: string, display = true): string {
  if (!latex) return ''
  if (typeof katex === 'undefined') return '<span class="err">' + esc(latex) + '</span>'
  try {
    return katex.renderToString(latex, { displayMode: display, throwOnError: false, strict: 'ignore' })
  } catch (e) {
    return '<span class="err">' + esc(String(e)) + '</span>'
  }
}

function esc(s: unknown): string {
  return String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c] ?? c)
}

// ---------- состояние ----------
const status = signal('загрузка рантайма…')
const busy = signal(true)
const code = signal('')
const previewHtml = signal('')
const previewErr = signal(false)
const answerVisible = signal(false)
const answerHtml = signal('')
const answerPretty = signal('')
const answerNote = signal('')
const answerErr = signal(false)
const stepsVisible = signal(false)
const stepsFull = signal(false)   // WASM.3c: по умолчанию brief, «подробно» — флажок
const steps = signal<StepNode | null>(null)
const history = signal<string[]>(loadHistory())
const formulaOpen = signal(false)
const formulaSrc = signal('')
const formulaErr = signal('')
const plots = signal<{ id: number; node: HTMLElement }[]>([])

function safeStorage(): Storage | null {
  try { return window.localStorage } catch { return null }
}
const examplesOpen = signal(loadExamplesOpen(safeStorage()))   // WEB.NAV: по умолчанию свёрнут
const navShown = signal(false)
const navOpen = signal(false)

// WASM.5b: примеры — задачи каталога из web/app/examples/*.json (генерируются tools/gen-examples.ts)
interface ProblemRow {
  id: string
  topic: string
  title: string
  input: string
  level: string
  kind: string
  expect: string
  check: string
}
const examples = signal<ProblemRow[]>([])

async function loadExamples(): Promise<void> {
  try {
    const index = (await (await fetch('./examples/index.json')).json()) as { file: string; topic: string }[]
    const rows: ProblemRow[] = []
    for (const t of index) {
      const part = (await (await fetch('./examples/' + t.file)).json()) as {
        topic: string
        problems: Omit<ProblemRow, 'topic'>[]
      }
      for (const pr of part.problems) if (pr.kind !== 'ошибка') rows.push({ ...pr, topic: part.topic })
    }
    examples.value = rows
  } catch (e) {
    status.value = 'каталог примеров не загружен: ' + String(e)
  }
}
let plotSeq = 0
let lastLatex = ''

// ---------- ответы движка ----------
async function askLisp(lisp: string): Promise<LispAnswer> {
  return JSON.parse(await window.lispEval(lisp, 'lisp')) as LispAnswer
}

async function askMath(src: string): Promise<LispAnswer> {
  return JSON.parse(await window.lispEval(src, 'math')) as LispAnswer
}

function unquote(s: string): string {
  // prettyPrint строки — это "…" без экранирования внутри: снимаем только внешние кавычки
  return s.length >= 2 && s[0] === '"' && s[s.length - 1] === '"' ? s.slice(1, -1) : s
}

// ---------- статус и предпросмотр ----------
function onInput(): void {
  clearTimeout(previewTimer)
  previewTimer = window.setTimeout(() => { void updatePreview() }, 150)
}
let previewTimer = 0

async function updatePreview(): Promise<void> {
  const src = code.value.trim()
  if (!src) { previewHtml.value = ''; previewErr.value = false; return }
  if (!window.lispReady) return
  try {
    const r = JSON.parse(await window.lispLatexOfInput(src)) as LispAnswer
    if (r.status === 'error') {
      previewHtml.value = '<span class="err">' + esc(r.error || 'ошибка разбора') + '</span>'
      return
    }
    previewHtml.value = tex(r.latex, false)
    previewErr.value = false
  } catch (e) {
    previewHtml.value = '<span class="err">' + esc(e instanceof Error ? e.message : e) + '</span>'
  }
}

function watchReady(): void {
  const tick = (): void => {
    if (window.lispReady) {
      status.value = 'готово (старт ' + Math.round(window.lispBootMs) + ' мс)'
      busy.value = false
    } else {
      setTimeout(tick, 150)
    }
  }
  tick()
}

// ---------- вычисление ----------
function litOf(src: string): string {
  return '"' + src.replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"'
}

/** dsolve возвращает служебную запись (ode-solution …); показываем сами уравнения из :solutions */
function isOdeSolution(r: LispAnswer): boolean {
  return typeof r.pretty === 'string' && r.pretty.trimStart().startsWith('(ode-solution')
}

// Движок печатает корневую сумму как вызов rootsum(…): показываем сумму по корням Q(t) = 0.
// В Lisp голова — root-sum с аргументами (t Q E), печать переставляет их в rootsum(E t Q).
// Сумма ищется на любой глубине: у нормированного параметра (t → t/c) перед ней стоит множитель 1/c.
async function rootSumLatex(src: string): Promise<string> {
  const lisp =
    '(let ((r (math-eval ' + litOf(src) + '))) ' +
    '(let loop ((e r)) ' +
    '(cond ((not (list? e)) "") ' +
    '((and (equal? (car e) (quote root-sum)) (= (length e) 4)) ' +
    '(string-append "\\\\sum_{" (math-latex (nth e 2)) "=0} " (math-latex (nth e 3)))) ' +
    '(else (let ((s (loop (car e)))) (if (equal? s "") (loop (cdr e)) s))))))'
  const res = await askLisp(lisp)
  return unquote(String(res.result || ''))
}

/** Множитель перед rootsum в pretty («1/3*», «-2*», пусто) → LaTeX; undefined — множителя нет */
function rootSumFactor(pretty: string): string | undefined {
  const s = String(pretty || '').trim()
  const i = s.indexOf('rootsum(')
  if (i < 0) return undefined
  let head = s.slice(0, i).trim()
  if (!head) return ''
  if (!head.endsWith('*')) return undefined
  head = head.slice(0, -1).trim()
  if (!/^[-+()\d/^*. ]+$/.test(head)) return undefined
  const m = /^\(?(-?\d+)\)?\/\(?(\d+)\)?$/.exec(head)
  if (m) {
    const num = String(m[1] ?? '')
    const den = String(m[2] ?? '')
    return (num[0] === '-' ? '-' : '') + '\\frac{' + num.replace('-', '') + '}{' + den + '}'
  }
  return head
}

async function odeLatex(src: string): Promise<string> {
  const lisp =
    '(let ((r (math-eval ' + litOf(src) + '))) ' +
    '(if (and (pair? r) (equal? (car r) (quote ode-solution))) ' +
    '(foldl (lambda (acc eq) (string-append acc (math-latex eq) "@@")) "" (ode-solutions r)) ' +
    '"__not_ode__"))'
  const res = await askLisp(lisp)
  const s = unquote(String(res.result || ''))
  return s === '__not_ode__' ? '' : s
}

async function evaluate(): Promise<void> {
  const src = code.value.trim()
  if (!src) return
  const spec = parsePlotCall(src)
  if (spec) {
    await addPlot(spec)
    status.value = 'график'
    addHistory(src)
    return
  }
  busy.value = true
  status.value = 'считается…'
  const t0 = performance.now()
  try {
    const r = await askMath(src)
    const ms = Math.round(performance.now() - t0)
    let html = r.latex ? tex(r.latex, true) : tex(r.pretty || '', true)
    let pretty = r.pretty || ''
    // Для значений, которых нет в LaTeX-принтере (ряды с O(…), некоторые записи), хост отдаёт
    // latex = \text{pretty}: перепечатываем pretty через входной язык, чтобы получилась формула.
    if ((!r.latex || String(r.latex).startsWith('\\text{')) && pretty) {
      try {
        const alt = JSON.parse(await window.lispLatexOfInput(pretty)) as LispAnswer
        if (alt.latex && !String(alt.latex).startsWith('\\text{')) html = tex(alt.latex, true)
      } catch (_) { /* оставляем как есть */ }
    }
    const rsFactor = rootSumFactor(r.pretty)
    if (rsFactor !== undefined) {
      const sumLatex = await rootSumLatex(src)
      if (sumLatex) { html = tex(rsFactor + sumLatex, true); pretty = r.pretty }
    }
    if (isOdeSolution(r)) {
      const many = await odeLatex(src)
      if (many) {
        html = many.split('@@').filter((x) => x.trim() !== '').map((one) => tex(one, true)).join('')
        pretty = ''
      }
    }
    answerHtml.value = html
    answerPretty.value = pretty
    answerNote.value = r.error ? 'ошибка: ' + r.error : r.note ? r.note : ''
    answerErr.value = !!r.error
    answerVisible.value = true
    lastLatex = r.latex || ''
    status.value = (r.status === 'error' ? 'ошибка' : 'готово') + ' · ' + ms + ' мс'
    if (r.status !== 'error') addHistory(src)
  } catch (e) {
    status.value = 'ошибка: ' + (e instanceof Error ? e.message : String(e))
  } finally {
    busy.value = false
  }
}

// ---------- шаги ----------
// Дерево шагов: заголовок — title (без номера и кавычек), под ним формула «до ⇒ после»,
// правило и комментарий — мелким текстом. Служебный шаг без LaTeX показывается только текстом.
const TEX_TEXT = '\\text{'

// Глифы, которые KaTeX не принимает в \text{} («Can't use function '∫' in text mode»),
// выносим в математический режим; остальную строку — в \text{} с экранированием.
const TEX_GLYPHS: Readonly<Record<string, string>> = {
  '∫': '\\int ', '∑': '\\sum ', '∏': '\\prod ', '∞': '\\infty ', '∂': '\\partial ',
  '→': '\\to ', '≤': '\\le ', '≥': '\\ge ', '≠': '\\ne ', '·': '\\cdot ',
  '×': '\\times ', '±': '\\pm ', '\\': '\\backslash{}',
}
const TEX_TEXT_ESC: Readonly<Record<string, string>> = {
  '{': '\\{', '}': '\\}', '$': '\\$', '&': '\\&', '#': '\\#',
  '^': '\\^{}', '_': '\\_', '%': '\\%', '~': '\\~{}',
}

/** конец «показателя» после ^ или _: группа в скобках или буквенно-цифровой токен */
function mathTokenEnd(s: string, i: number): number {
  if (s[i] === '(') {
    let depth = 0
    for (let j = i; j < s.length; j++) {
      if (s[j] === '(') depth++
      else if (s[j] === ')' && --depth === 0) return j + 1
    }
    return -1
  }
  let j = i
  while (j < s.length && /[A-Za-z0-9.+\-*/]/.test(s[j] ?? '')) j++
  return j > i ? j : -1
}

function textToTex(text: string): string {
  const s = String(text || '')
  let out = ''
  let buf = ''
  const flush = (): void => { if (buf) { out += TEX_TEXT + buf + '}'; buf = '' } }
  for (let i = 0; i < s.length; i++) {
    const ch = s[i] ?? ''
    const glyph = TEX_GLYPHS[ch]
    if (glyph) { flush(); out += glyph; continue }
    // x^2 и подобные — настоящий индекс, а не «шляпка» в текстовом режиме
    if (ch === '^' || ch === '_') {
      const end = mathTokenEnd(s, i + 1)
      if (end > 0) {
        flush()
        out += (ch === '^' ? '^{' : '_{') + s.slice(i + 1, end).replace(/[{}]/g, (c) => '\\' + c) + '}'
        i = end - 1
        continue
      }
    }
    buf += TEX_TEXT_ESC[ch] ?? ch
  }
  flush()
  return out
}

function texSide(latex: string, text: string): string {
  const l = String(latex || '')
  // \text{…} — не формула (внутренняя запись вида (int/dx …)): перепечатываем по тексту
  if (l && !l.startsWith(TEX_TEXT)) return l
  return textToTex(text)
}

/** сторона шага пуста, если там нет ни формулы, ни текста (math-print пустого списка даёт «()») */
function sideEmpty(st: StepRecord, side: 'before' | 'after'): boolean {
  const latex = String(st[`${side}_latex`] || '').trim()
  const text = String(st[`${side}_text`] || '').trim()
  const blank = latex === '' || /^\\text\{\s*\(\s*\)\s*\}$/.test(latex)
  return blank && (text === '' || text === '()')
}

function stepFormula(st: StepRecord): string {
  const bEmpty = sideEmpty(st, 'before')
  const aEmpty = sideEmpty(st, 'after')
  if (bEmpty && aEmpty) return ''   // служебный шаг: показываем только заголовок и комментарий
  const b = bEmpty ? '' : texSide(st.before_latex, st.before_text)
  const a = aEmpty ? '' : texSide(st.after_latex, st.after_text)
  if (bEmpty) return a
  if (aEmpty) return b
  return b + ' \\Rightarrow ' + a
}

function stepsTree(json: StepsJson | null): StepNode | null {
  const list = (json && json.steps) || []
  if (!list.length) return null
  const finish = (items: readonly StepRecord[]): StepNode[] => items.map((s) => ({
    label: s.title || s.rule || 'шаг',
    meta: s.rule || '',
    step: s,
    children: s.children && s.children.length ? finish(s.children) : null,
  }))
  const count = (function walk(items: readonly StepRecord[]): number {
    return items.reduce((acc, s) => acc + 1 + walk(s.children || []), 0)
  })(list)
  return { label: 'Шаги решения', meta: String(count) + ' ш.', children: finish(list) }
}

// помощник шагов — отдельный файл web/app/steps.lisp (тот же код проверен на десктопе)
let stepsHelpersReady = false

async function ensureStepsHelpers(): Promise<void> {
  if (stepsHelpersReady) return
  const text = await (await fetch('./steps.lisp')).text()
  await window.lispEval(text, 'lisp')
  stepsHelpersReady = true
}

async function showSteps(): Promise<void> {
  const src = code.value.trim()
  if (!src) return
  const level = stepsFull.value ? 'full' : 'brief'
  busy.value = true
  status.value = 'шаги…'
  try {
    await ensureStepsHelpers()
    const r = await askLisp('(app-steps-json ' + litOf(src) + ' (quote ' + level + '))')
    const text = unquote(String(r.result || r.pretty || ''))
    const json = text ? (JSON.parse(text) as StepsJson) : { steps: [] }
    steps.value = stepsTree(json)
    stepsVisible.value = true
    // у Tree нет «раскрыто по умолчанию» — раскрываем всё после перерисовки, чтобы шаги были видны сразу
    requestAnimationFrame(() => {
      const btn = stepsView.querySelector<HTMLElement>('.expand-all')
      if (btn) btn.click()
    })
    status.value = 'готово'
  } catch (e) {
    status.value = 'ошибка шагов: ' + (e instanceof Error ? e.message : String(e))
  } finally {
    busy.value = false
  }
}

// ---------- история ----------
function loadHistory(): string[] {
  try {
    const raw = localStorage.getItem(HISTORY_KEY)
    const arr: unknown = raw ? JSON.parse(raw) : []
    return Array.isArray(arr)
      ? arr.filter((x): x is string => typeof x === 'string').slice(0, HISTORY_MAX)
      : []
  } catch (_) { return [] }
}

function saveHistory(arr: readonly string[]): void {
  try {
    localStorage.setItem(HISTORY_KEY, JSON.stringify(arr.slice(0, HISTORY_MAX)))
  } catch (_) { /* приватный режим */ }
}

function addHistory(src: string): void {
  const arr = history.value.filter((x) => x !== src)
  arr.unshift(src)
  history.value = arr.slice(0, HISTORY_MAX)
  saveHistory(history.value)
}

// ---------- графики ----------
/** spec.auto — диапазон задан по умолчанию, его подбираем по разрешимости кривой */
async function addPlot(spec: PlotSpec): Promise<void> {
  let chosen = spec
  if (spec.auto && spec.kind === 'plot') {
    status.value = 'подбираю диапазон…'
    const [a, b] = await pickRange(spec.expr, spec.vars[0] ?? 'x')
    chosen = { ...spec, ranges: [a ?? 0, b ?? 0] }
    status.value = 'график'
  }
  const node = createPlotCard(chosen)
  plots.value = [...plots.value, { id: ++plotSeq, node }]
}

/** «График»: вызов plot(…) из поля — как есть, иначе выражение от x с автоподбором диапазона */
async function plotFromInput(): Promise<void> {
  const src = code.value.trim()
  if (!src) return
  let spec = parsePlotCall(src)
  if (!spec) {
    spec = parsePlotCall('plot(' + src + ', x, -10, 10)')
    if (spec) spec.auto = true
  }
  if (spec) await addPlot(spec)
}

// Можно ли строить график по тому, что в поле: вызов plot(…) или выражение без команд CAS
const PLOT_CMDS = /\b(integrate|limit|sum|product|series|dsolve|solve|factor|det|inverse|diff|subst|eval)\s*\(/
function plotableInput(): boolean {
  const src = code.value.trim()
  if (!src) return false
  if (parsePlotCall(src)) return true
  return !PLOT_CMDS.test(src)
}

// ---------- элементы управления ----------
function runExample(row: ProblemRow): void {
  code.value = row.input
  onInput()
  void evaluate()
}

async function stopRun(): Promise<void> {
  status.value = 'остановка…'
  busy.value = true
  await window.lispStop()
  status.value = 'рантайм перезапущен'
  busy.value = false
}

async function copyLatex(): Promise<void> {
  try { await navigator.clipboard.writeText(lastLatex) } catch (_) { /* нет прав */ }
}

// ---------- редактор формул (MathLive) ----------
// MathLive (846 КБ) грузится только при первом открытии редактора; шрифты и звуки — локальные.
let mathfield: MathFieldElement | null = null
/** LaTeX → ascii-math MathLive (экспорт модуля mathlive.min.mjs; ставится в ensureMathField) */
let latexToAscii: (latex: string) => string = () => ''

async function openFormula(): Promise<void> {
  formulaOpen.value = true
  requestAnimationFrame(() => {
    void (async () => {
      try {
        await ensureMathField()
        await fillMathFieldMenu()
        updateFormula()
        if (mathfield) mathfield.focus()
      } catch (e) {
        formulaErr.value = 'не удалось загрузить MathLive: ' + (e instanceof Error ? e.message : String(e))
      }
    })()
  })
}

// меню «функция…» в редакторе формул: те же шаблоны, но в записи LaTeX (MathLive понимает \placeholder{})
let allFunctions: CatalogFunction[] = []

async function fillMathFieldMenu(): Promise<void> {
  const sel = document.getElementById('mf-functions') as HTMLSelectElement | null
  if (!sel || sel.dataset.filled) return
  allFunctions = await loadFunctions()
  for (const fn of allFunctions) {
    const opt = document.createElement('option')
    opt.value = fn.name
    opt.textContent = fn.name
    sel.appendChild(opt)
  }
  sel.dataset.filled = '1'
}

function insertMathFieldFn(name: string): void {
  if (!mathfield || !name) return
  const fn = allFunctions.find((f) => f.name === name)
  if (!fn) return
  mathfield.insert(latexTemplate(fn))
  mathfield.focus()
  const sel = document.getElementById('mf-functions') as HTMLSelectElement | null
  if (sel) sel.value = ''
}

async function ensureMathField(): Promise<MathFieldElement | null> {
  if (mathfield) return mathfield
  const box = document.getElementById('math-editor')
  if (!box) return null
  // MathLive лежит в wwwroot/vendor: считаем каталог от import.meta.url, файл — вторым шагом
  // (статический «new URL(…/mathlive.min.mjs, import.meta.url)» Vite выносит в /assets/…)
  const dir = new URL('../../vendor/mathlive/', import.meta.url)
  const lib = (await import(/* @vite-ignore */ new URL('mathlive.min.mjs', dir).href)) as {
    convertLatexToAsciiMath?: (latex: string) => string
  }
  if (typeof lib.convertLatexToAsciiMath === 'function') latexToAscii = lib.convertLatexToAsciiMath
  await customElements.whenDefined('math-field')
  const el = document.createElement('math-field') as MathFieldElement
  el.id = 'math-field'
  el.setAttribute('virtual-keyboard-mode', 'manual')
  el.setAttribute('aria-label', 'Редактор формул')
  el.addEventListener('input', updateFormula)
  box.appendChild(el)
  mathfield = el
  return el
}

/** ascii-math → входной язык; ошибка видна, поле ввода не трогаем.
 *  Перевод — после паузы в наборе (120 мс), а не на каждое нажатие: на Pages разбор MathLive на каждое
 *  нажатие задерживал появление символа до секунды. Без многобуквенных имён — прежний быстрый путь
 *  getValue('ascii-math'); с ними — защита имён и convertLatexToAsciiMath (WEB.OPN). */
let formulaTimer = 0
function updateFormula(): void {
  clearTimeout(formulaTimer)
  formulaTimer = window.setTimeout(translateFormula, 120)
}
function translateFormula(): void {
  if (!mathfield) return
  const p = protectNames(mathfield.getValue('latex'))
  const r = p.names.length === 0 ? toSource(mathfield.getValue('ascii-math')) : toSource(latexToAscii(p.latex), p.names)
  if (r.ok) { formulaSrc.value = r.source; formulaErr.value = '' }
  else { formulaSrc.value = ''; formulaErr.value = 'не поддерживается: ' + r.error }
}

function insertFormula(): void {
  clearTimeout(formulaTimer)
  translateFormula()
  if (!formulaSrc.value) return
  code.value = formulaSrc.value
  onInput()
  formulaOpen.value = false
}

function clearFormula(): void {
  if (mathfield) mathfield.setValue('', { format: 'latex' })
  formulaSrc.value = ''
  formulaErr.value = ''
}

// ---------- разметка ----------
// $() принимает только Signal, поэтому производные строки — через computed
const previewClass = computed(() => 'preview' + (previewErr.value ? ' err' : ''))
const noteClass = computed(() => 'note' + (answerErr.value ? ' err' : ''))
const formulaErrClass = computed(() => (formulaErr.value ? 'note err' : 'note'))
// кнопка «график» в ответе активна, когда по введённому выражению график имеет смысл
const notPlotable = computed(() => !plotableInput())

// Панель редактора формул: math-field создаётся при первом открытии (см. ensureMathField)
const formulaPanel = (
  <section id="formula-box" class="panel">
    <div class="row">
      <span class="lbl">Редактор формул</span>
      <span class="hint">набирайте как в Word; формула переводится во входной язык</span>
      <span class="grow"></span>
      <select id="mf-functions" class="fn-select" title="Вставить функцию языка"
        onChange={(e: Event) => insertMathFieldFn((e.target as HTMLSelectElement).value)}>
        <option value="">функция…</option>
      </select>
      <button class="btn small" onClick={clearFormula}>очистить</button>
      <button class="btn small" onClick={() => { formulaOpen.value = false }}>закрыть</button>
    </div>
    <div id="math-editor" class="math-editor"></div>
    <div class="row">
      <span class="lbl">во входной язык</span>
      <code id="formula-src" class="formula-src">{$(formulaSrc)}</code>
    </div>
    <div id="formula-err" class={$(formulaErrClass)}>{$(formulaErr)}</div>
    <div class="row">
      <button id="formula-insert" class="btn primary" onClick={insertFormula}>вставить в поле ввода</button>
    </div>
  </section>
)

// Каталог задач: Grid даёт поиск, сортировку и группы по теме; клик — по названию задачи.
// WEB.NAV: строится и загружается лениво — при первом раскрытии раздела «Примеры».
const buildCatalog = (): HTMLElement => Grid<ProblemRow>({
  rows: examples,
  rowKey: (r) => r.id,
  groupBy: (r) => r.topic,
  initialSort: { key: 'title', dir: 'asc' },
  filter: (r, q) => (r.title + ' ' + r.input + ' ' + r.topic + ' ' + r.level).toLowerCase().includes(q),
  searchPlaceholder: 'поиск по задачам',
  empty: 'ничего не найдено',
  labels: {
    search: 'поиск по задачам',
    sortDirection: 'направление сортировки',
    descending: '↓ по убыванию',
    ascending: '↑ по возрастанию',
    rows: 'задач',
  },
  columns: [
    {
      key: 'title',
      header: 'Задача',
      sort: (r) => r.title,
      cell: (r) => <button class="link" type="button" title={r.input} onClick={() => runExample(r)}>{r.title}</button>,
    },
    {
      key: 'level',
      header: 'Уровень',
      sort: (r) => r.level,
      cell: (r) => <span class={'lvl ' + r.level}>{r.level}</span>,
    },
    {
      key: 'input',
      header: 'Ввод',
      sort: (r) => r.input,
      cell: (r) => <code>{r.input}</code>,
    },
  ],
}) as HTMLElement

const catalogBox = <div id="catalog" class="catalog"></div> as HTMLElement
let catalogBuilt = false
function ensureCatalog(): void {
  if (catalogBuilt) return
  catalogBuilt = true
  catalogBox.appendChild(buildCatalog())
  void loadExamples()
}
function setExamplesOpen(v: boolean): void {
  examplesOpen.value = v
  saveExamplesOpen(safeStorage(), v)
  if (v) ensureCatalog()
}

// ---------- справочник и автодополнение (WASM.3b) ----------
const inputArea = (
  <textarea
    id="input"
    rows={3}
    spellcheck="false"
    placeholder="2x+1"
    value={$(code)}
    onInput={(e: Event) => {
      code.value = (e.target as HTMLTextAreaElement).value
      onInput()
      void assist.update()
    }}
    onKeydown={(e: Event) => {
      const ke = e as KeyboardEvent
      // ↑/↓/Enter/Esc — только когда список автодополнения открыт; иначе Enter = «вычислить»
      if (assist.keydown(ke)) { ke.preventDefault(); return }
      if (ke.key === 'Tab' && tabToNextPlace(inputArea)) { ke.preventDefault(); return }
      if (ke.key === 'Enter' && !ke.shiftKey) { ke.preventDefault(); void evaluate() }
    }}
  ></textarea>
) as HTMLTextAreaElement

const assist: Assist = createAssist(inputArea)

const fnPanel = createFunctionsPanel({
  onInsert: (fn) => { insertTemplate(inputArea, fn.template) },
  onExample: (fn) => {
    code.value = fn.example || ''
    inputArea.value = code.value
    onInput()
    void evaluate()
  },
})

// Шаги: Tree с поиском и массовым раскрытием; узлы обновляются сигналом steps.
const stepsView = Tree({
  root: steps,
  showExpandAll: true,
  searchPlaceholder: 'поиск по шагам',
  empty: 'шагов нет',
  labels: { search: 'поиск по шагам', matched: 'найдено', expandAll: 'развернуть всё', collapseAll: 'свернуть всё' },
  // узел: заголовок шага, под ним формула «до ⇒ после» (KaTeX), правило и комментарий — мелким текстом
  renderLabel: (node: TreeData) => {
    const st = (node as StepNode).step
    if (!st) return <span class="step-root">{node.label}</span>
    const formula = stepFormula(st)
    return (
      <div class="step">
        <div class="step-head">
          <span class="step-title">{node.label}</span>
          {st.rule && st.rule !== node.label ? <span class="step-rule">{st.rule}</span> : null}
        </div>
        {formula ? <div class="step-tex" innerHTML={tex(formula, false)}></div> : null}
        {st.comment ? <div class="step-comment">{st.comment}</div> : null}
      </div>
    )
  },
})

const view = (
  <div class="app">
    <header class="bar">
      <h1>Qedra</h1>
      <span id="status" class="status">{$(status)}</span>
      <span class="grow"></span>
      <button id="stop" class="btn" title="Прервать вычисление и перезапустить рантайм" onClick={() => { void stopRun() }}>Стоп</button>
    </header>
    <main>
      <section id="sec-input" class="panel">
        <label class="lbl" for="input">Входной язык (например, <code>integrate(1/(x^3+1), x)</code>)</label>
        <div class="input-wrap">
          {inputArea}
          {assist.node}
        </div>
        <div id="preview" class={$(previewClass)} innerHTML={$(previewHtml)}></div>
        <div class="row">
          <button id="eval" class="btn primary" disabled={$(busy)} onClick={() => { void evaluate() }}>Вычислить</button>
          <button id="steps" class="btn" disabled={$(busy)} onClick={() => { void showSteps() }}>Шаги</button>
          <button id="formula" class="btn" onClick={() => { void openFormula() }}>Формула</button>
          <button id="plot" class="btn" onClick={() => { void plotFromInput() }}>График</button>
          <button id="functions" class="btn" onClick={() => { void fnPanel.toggle() }}>Функции</button>
          <span class="hint">Enter — вычислить, «График» — построить; Shift+Enter — новая строка</span>
        </div>
      </section>
      <Show when={() => fnPanel.open.value}>{fnPanel.node}</Show>
      <Show when={() => formulaOpen.value}>{formulaPanel}</Show>
      <Show when={() => answerVisible.value}>
        <section id="answer" class="panel answer">
          <div class="row">
            <span class="lbl">Ответ</span>
            <span class="grow"></span>
            <button id="plot-answer" class="btn small" disabled={$(notPlotable)}
              title="Построить график по выражению из поля ввода"
              onClick={() => { void plotFromInput() }}>график</button>
            <button id="copy" class="btn small" onClick={() => { void copyLatex() }}>копировать LaTeX</button>
          </div>
          <div id="answer-tex" class="tex" innerHTML={$(answerHtml)}></div>
          <div id="answer-pretty" class="pretty">{$(answerPretty)}</div>
          <div id="answer-note" class={$(noteClass)}>{$(answerNote)}</div>
        </section>
      </Show>
      <Show when={() => stepsVisible.value}>
        <section id="steps-box" class="panel">
          <div class="row">
            <span class="lbl">Шаги</span>
            <span class="grow"></span>
            <label class="chk">
              <input
                type="checkbox"
                id="steps-full"
                checked={$(stepsFull)}
                onChange={(e: Event) => {
                  stepsFull.value = (e.target as HTMLInputElement).checked
                  void showSteps()
                }}
              /> подробно
            </label>
          </div>
          <div id="steps-body" class="steps">{stepsView}</div>
        </section>
      </Show>
      <section id="sec-history" class="panel">
        <div class="row">
          <span class="lbl">История</span>
          <span class="grow"></span>
          <button id="clear-history" class="btn small" onClick={() => { history.value = []; saveHistory([]) }}>очистить</button>
        </div>
        <ol id="history" class="history">
          <For each={history} key={(c) => c}>
            {(c: string) => <li title="вернуть в поле ввода" onClick={() => { code.value = c; onInput() }}>{c}</li>}
          </For>
          <Show when={() => history.value.length === 0}><li class="empty">пусто</li></Show>
        </ol>
      </section>
      <section class="panel">
        <div class="row">
          <span class="lbl">Графики</span>
          <span class="grow"></span>
          <button id="clear-plots" class="btn small" onClick={() => { plots.value = [] }}>убрать все</button>
        </div>
        <div id="plots" class="plots">
          <For each={plots} key={(x) => x.id}>{(x) => x.node}</For>
          <Show when={() => plots.value.length === 0}><div class="note">нет графиков</div></Show>
        </div>
      </section>
      <section id="sec-examples" class="panel">
        <div class="row">
          <button id="examples-toggle" class="lbl toggle" type="button"
            aria-expanded={$(computed(() => String(examplesOpen.value)))} aria-controls="catalog"
            onClick={() => setExamplesOpen(!examplesOpen.value)}>
            {$(computed(() => (examplesOpen.value ? 'Примеры ▾' : 'Примеры ▸')))}
          </button>
        </div>
        <Show when={() => examplesOpen.value}>{catalogBox}</Show>
      </section>
    </main>
    <nav class={$(computed(() => 'float-nav' + (navShown.value ? ' shown' : '') + (navOpen.value ? ' open' : '')))}
      aria-label="Разделы страницы">
      <div class="float-nav-list">
        <For each={computed(() => visibleNav(answerVisible.value))} key={(s) => s.id}>
          {(s: { id: string; label: string }) => (
            <button class="btn small" type="button" aria-label={'Перейти к разделу: ' + s.label}
              onClick={() => { void goTo(s.id) }}>{s.label}</button>
          )}
        </For>
      </div>
      <button id="nav-up" class="btn primary nav-up" type="button" aria-label="Наверх, к полю ввода"
        title="Наверх" onClick={() => { void goTo('top') }}>↑</button>
      <button id="nav-menu" class="btn nav-menu" type="button" aria-label="Меню разделов"
        aria-expanded={$(computed(() => String(navOpen.value)))}
        onClick={() => { navOpen.value = !navOpen.value }}>☰</button>
    </nav>
  </div>
)

// WEB.NAV: переход к разделу; свёрнутые (функции, примеры, редактор формул) раскрываются
async function goTo(id: string): Promise<void> {
  navOpen.value = false
  if (id === 'top') {
    window.scrollTo({ top: 0, behavior: 'smooth' })
    inputArea.focus({ preventScroll: true })
    return
  }
  if (id === 'formula-box' && !formulaOpen.value) await openFormula()
  else if (id === 'sec-functions' && !fnPanel.open.value) await fnPanel.toggle()
  else if (id === 'sec-examples') setExamplesOpen(true)
  window.setTimeout(() => {
    document.getElementById(id)?.scrollIntoView({ behavior: 'smooth', block: 'start' })
  }, 50)
}

window.addEventListener('scroll', () => { navShown.value = navVisible(window.scrollY) }, { passive: true })

mount(document.getElementById('app') as HTMLElement, view)
if (examplesOpen.value) ensureCatalog()
watchReady()
window.appReady = true
