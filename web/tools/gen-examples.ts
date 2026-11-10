// WASM.5b: сборка каталога примеров-задач. Исходники — web/tools/examples/<тема>.json
// (постановка: id, title, input, level, kind, check), результат — web/app/examples/<тема>.json
// с полем expect: pretty настольного Lisp.exe. Проверка ответов — независимый оракул в
// web/tests/slow/examples.test.ts. Запуск: npm run gen:examples
import { spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..')
const SRC = join(ROOT, 'web', 'tools', 'examples')
const OUT = join(ROOT, 'web', 'app', 'examples')

export type Level = 'школа' | 'вуз' | 'сложно'
export type Kind = 'ответ' | 'отказ' | 'график' | 'ошибка'
export type Check = 'производная' | 'подстановка' | 'численно' | 'dsolve-check' | 'сертификат' | 'эталон'

export interface Problem {
  id: string
  title: string
  input: string
  level: Level
  kind: Kind
  check: Check
  /** REL.1e: id алгоритма из hard-algos.json (только для уровня «сложно») */
  algo?: string
  /** опорное значение для check: "эталон" (из литературы) — сверяется оракулом */
  ref?: string
}

export interface BuiltProblem extends Problem {
  expect: string
}

function lispExe(): string {
  for (const cfg of ['Debug', 'Release']) {
    const p = join(ROOT, 'src', 'Lisp.Host', 'bin', cfg, 'net10.0', 'Lisp.exe')
    if (existsSync(p)) return p
  }
  throw new Error('нет Lisp.exe — сначала dotnet build src/Lisp.Host')
}

const EXE = lispExe()

/** ответ системы в режиме --math -e */
function expectOf(input: string): { ok: boolean; text: string } {
  const p = spawnSync(EXE, ['--math', '-e', input], { encoding: 'utf8', timeout: 120000 })
  const out = String(p.stdout ?? '').trim()
  const bad = p.status !== 0 || out.includes('ОШИБКА') || out === ''
  return { ok: !bad, text: out }
}

function countBy<T>(list: readonly T[], key: (x: T) => string): Record<string, number> {
  const m: Record<string, number> = {}
  for (const x of list) m[key(x)] = (m[key(x)] ?? 0) + 1
  return m
}

function main(): void {
  mkdirSync(OUT, { recursive: true })
  const all = readdirSync(SRC).filter((f) => f.endsWith('.json'))
  // аргумент — имя файла (или его часть): перегенерировать только эту тему
  const only = process.argv[2]
  const files = only ? all.filter((f) => f.includes(only)) : all
  if (only && files.length === 0) throw new Error(`нет темы по фильтру «${only}» в ${SRC}`)
  let total = 0
  for (const file of files) {
    const src = JSON.parse(readFileSync(join(SRC, file), 'utf8')) as { topic: string; problems: Problem[] }
    const built: BuiltProblem[] = []
    const seen = new Set<string>()
    for (const pr of src.problems) {
      if (seen.has(pr.input)) throw new Error(`${file}: повтор входа: ${pr.input}`)
      seen.add(pr.input)
      const r = expectOf(pr.input)
      if (!r.ok && pr.kind !== 'ошибка') {
        throw new Error(`${file}: ${pr.id} не вычисляется: ${pr.input} → ${r.text.slice(0, 120)}`)
      }
      built.push({ ...pr, expect: r.text })
    }
    writeFileSync(join(OUT, file), JSON.stringify({ topic: src.topic, problems: built }, null, 1) + '\n', 'utf8')
    total += built.length
    const lv = countBy(built, (p) => p.level)
    const kd = countBy(built, (p) => p.kind)
    console.log(`${src.topic}: ${built.length} — ` +
      Object.entries(lv).map(([k, v]) => `${k} ${v}`).join(', ') + '; ' +
      Object.entries(kd).map(([k, v]) => `${k} ${v}`).join(', '))
  }
  // индекс тем для интерфейса: [{ file, topic }]
  const index = all.map((f) => ({
    file: f,
    topic: (JSON.parse(readFileSync(join(SRC, f), 'utf8')) as { topic: string }).topic,
  }))
  writeFileSync(join(OUT, 'index.json'), JSON.stringify(index, null, 1) + '\n', 'utf8')
  console.log(`итого ${total} примеров`)
}

main()
