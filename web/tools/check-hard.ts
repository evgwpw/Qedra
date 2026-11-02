// REL.1e: механическая проверка «сложно» — у задачи есть algo, признак how выполнен,
// медиана 3 повторов в прогретом процессе ≥ 30 мс. Проверка — одним процессом Lisp.
//   npm run check:hard            — проверить каталог (exit 1 при нарушениях)
//   npm run check:hard -- assign  — проставить algo и перевести не прошедшие в «вуз»
import { spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..')
const TMP = join(tmpdir(), 'qedra-hard')
mkdirSync(TMP, { recursive: true })
const SRC = join(ROOT, 'web', 'tools', 'examples')
const APP = join(ROOT, 'web', 'app', 'examples')
const ALGOS = join(ROOT, 'web', 'tools', 'hard-algos.json')
const HC = join(ROOT, 'web', 'tools', 'hard-check.lisp')

type How = {
  type: 'rule' | 'head'
  prefix?: string[]
  head?: string
  minDigits?: number
  minDegree?: number
  minPeriod?: number
}
type Algo = { id: string; name: string; how: How }
type Problem = {
  id: string
  title: string
  input: string
  level: string
  kind: string
  check: string
  ref?: string
  algo?: string
  expect?: string
}
type Topic = { topic: string; problems: Problem[]; file: string }

function lispExe(): string {
  for (const cfg of ['Debug', 'Release']) {
    const p = join(ROOT, 'src', 'Lisp.Host', 'bin', cfg, 'net10.0', 'Lisp.exe')
    if (existsSync(p)) return p
  }
  throw new Error('нет Lisp.exe — сначала dotnet build src/Lisp.Host')
}
const EXE = lispExe()

function readAlgos(): Algo[] {
  return JSON.parse(readFileSync(ALGOS, 'utf8')) as Algo[]
}

function readTopics(dir: string): Topic[] {
  return readdirSync(dir)
    .filter((f) => f.endsWith('.json') && f !== 'index.json')
    .map((f) => {
      const d = JSON.parse(readFileSync(join(dir, f), 'utf8')) as { topic: string; problems: Problem[] }
      return { topic: d.topic, problems: d.problems, file: join(dir, f) }
    })
}

const lit = (s: string): string => s.replace(/\\/g, '\\\\').replace(/"/g, '\\"')

/** большие целые из простой записи: числа, + - * ^ и скобки */
function bigEval(s: string): bigint | null {
  const tokens = s.match(/\d+|[+\-*/^()]/g)
  if (!tokens) return null
  let i = 0
  const peek = (): string | undefined => tokens[i]
  const parseExpr = (): bigint | null => {
    let v = parseTerm()
    if (v === null) return null
    while (peek() === '+' || peek() === '-') {
      const op = tokens[i++]
      const r = parseTerm()
      if (r === null) return null
      v = op === '+' ? v + r : v - r
    }
    return v
  }
  const parseTerm = (): bigint | null => {
    let v = parsePow()
    if (v === null) return null
    while (peek() === '*' || peek() === '/') {
      const op = tokens[i++]
      const r = parsePow()
      if (r === null) return null
      if (op === '*') v = v * r
      else {
        if (r === 0n) return null
        v = v / r
      }
    }
    return v
  }
  const parsePow = (): bigint | null => {
    const base = parseAtom()
    if (base === null) return null
    if (peek() === '^') {
      i++
      const e = parseAtom()
      if (e === null || e < 0n || e > 100000n) return null
      return base ** e
    }
    return base
  }
  const parseAtom = (): bigint | null => {
    const t = peek()
    if (t === undefined) return null
    if (t === '(') {
      i++
      const v = parseExpr()
      if (peek() === ')') i++
      return v
    }
    if (t === '-') {
      i++
      const v = parseAtom()
      return v === null ? null : -v
    }
    if (/^\d+$/.test(t)) {
      i++
      return BigInt(t)
    }
    return null
  }
  const out = parseExpr()
  return out
}

function digitsOf(input: string): number {
  const m = /^\w+\s*\(([\s\S]*)\)\s*$/.exec(input)
  if (!m) return 0
  const n = bigEval(m[1]!.trim())
  if (n === null) return 0
  return (n < 0n ? -n : n).toString().length
}

function maxDegree(input: string): number {
  let d = 0
  for (const m of input.matchAll(/\^\s*(\d+)/g)) d = Math.max(d, Number(m[1]))
  return d
}

function cfPeriod(n: number): number {
  const a0 = Math.floor(Math.sqrt(n))
  if (a0 * a0 === n) return 0
  let m = 0
  let d = 1
  let a = a0
  let k = 0
  for (;;) {
    m = d * a - m
    d = Math.floor((n - m * m) / d)
    a = Math.floor((a0 + m) / d)
    k++
    if (a === 2 * a0) return k
    if (k > 10000) return k
  }
}

function arg1(input: string): string {
  const m = /^\w+\s*\(([\s\S]*)\)\s*$/.exec(input)
  if (!m) return ''
  const s = m[1]!
  let depth = 0
  for (let i = 0; i < s.length; i++) {
    const c = s[i]
    if (c === '(' || c === '[' || c === '{') depth++
    else if (c === ')' || c === ']' || c === '}') depth--
    else if ((c === ',' || c === ';') && depth === 0) return s.slice(0, i).trim()
  }
  return s.trim()
}

function headOf(input: string): string {
  const m = /^\s*([A-Za-z_][A-Za-z_0-9]*)\s*\(/.exec(input)
  return m ? m[1]! : ''
}

/** выполнено ли `how` по данным пробы */
function howOk(how: How, input: string, rules: string[], ms: number): boolean {
  if (ms < 35) return false
  if (how.type === 'rule') {
    if (how.head && headOf(input) !== how.head) return false
    return (how.prefix ?? []).some((p) => rules.some((r) => r.startsWith(p)))
  }
  if (headOf(input) !== how.head) return false
  if (how.minDigits !== undefined && digitsOf(input) < how.minDigits) return false
  if (how.minDegree !== undefined && maxDegree(arg1(input)) < how.minDegree) return false
  if (how.minPeriod !== undefined) {
    const n = bigEval(arg1(input))
    if (n === null || n > 10000000n) return false
    if (cfPeriod(Number(n)) < how.minPeriod) return false
  }
  return true
}

/** одна общая проба: правила шагов + время первого прогона */
function probe(topics: Topic[]): Map<string, { rules: string[]; ms: number }> {
  const lines = [
    `(load "${lit(HC)}")`,
  ]
  for (const t of topics) {
    for (const p of t.problems) {
      if (p.level !== 'сложно') continue
      lines.push(`(hc-probe-raw "${p.id}" "${lit(p.input)}")`)
    }
  }
  const probeLisp = join(TMP, 'hard-probe.lisp')
  writeFileSync(probeLisp, lines.join('\n') + '\n', 'utf8')
  const r = spawnSync(EXE, [probeLisp], { encoding: 'utf8', timeout: 1800000 })
  const out = String(r.stdout ?? '')
  const map = new Map<string, { rules: string[]; ms: number }>()
  for (const line of out.split(/\r?\n/)) {
    const m = /^@@(\S+) (\d+) (.*)$/.exec(line)
    if (!m) continue
    map.set(m[1]!, { ms: Number(m[2]), rules: m[3] === 'err' ? [] : [...m[3]!.matchAll(/"([^"]+)"/g)].map((x) => x[1]!) })
  }
  return map
}

/** проверка всех задач «сложно» (по одной на задачу — одним процессом) */
function checkAll(): number {
  const topics = readTopics(APP)
  const algos = new Map(readAlgos().map((a) => [a.id, a]))
  const lines = [`(load "${lit(HC)}")`]
  const meta = new Map<string, { algo: Algo; mode: string }>()
  for (const t of topics) {
    for (const p of t.problems) {
      if (p.level !== 'сложно') continue
      if (!p.algo) {
        console.log(`НАРУШЕНИЕ ${p.id}: нет algo`)
        continue
      }
      const a = algos.get(p.algo)
      if (!a) {
        console.log(`НАРУШЕНИЕ ${p.id}: algo ${p.algo} нет в hard-algos.json`)
        continue
      }
      const h = a.how
      if (h.type === 'rule') {
        lines.push(`(hc-rule "${p.id}" "${lit(p.input)}" '(${(h.prefix ?? []).map((s) => `"${s}"`).join(' ')}))`)
        meta.set(p.id, { algo: a, mode: 'rule' })
      } else if (h.head && h.minDigits !== undefined) {
        lines.push(`(hc-head-digits "${p.id}" "${lit(p.input)}" '${h.head} ${h.minDigits})`)
        meta.set(p.id, { algo: a, mode: 'digits' })
      } else if (h.head && h.minDegree !== undefined) {
        lines.push(`(hc-head-degree "${p.id}" "${lit(p.input)}" '${h.head} ${h.minDegree})`)
        meta.set(p.id, { algo: a, mode: 'degree' })
      } else if (h.head && h.minPeriod !== undefined) {
        lines.push(`(hc-head-period "${p.id}" "${lit(p.input)}" '${h.head} ${h.minPeriod})`)
        meta.set(p.id, { algo: a, mode: 'period' })
      } else if (h.head) {
        lines.push(`(hc-head-only "${p.id}" "${lit(p.input)}" '${h.head})`)
        meta.set(p.id, { algo: a, mode: 'head' })
      } else {
        console.log(`НАРУШЕНИЕ ${p.id}: пустой how у ${a.id}`)
      }
    }
  }
  const script = join(TMP, 'hard-check.lisp')
  writeFileSync(script, lines.join('\n') + '\n', 'utf8')
  const r = spawnSync(EXE, [script], { encoding: 'utf8', timeout: 1800000 })
  const out = String(r.stdout ?? '')
  let bad = 0
  let total = 0
  for (const line of out.split(/\r?\n/)) {
    const m = /^@@(\S+) (ok|fail) (.*)$/.exec(line)
    if (!m) continue
    total++
    if (m[2] === 'fail') {
      bad++
      const p = meta.get(m[1]!)
      console.log(`НАРУШЕНИЕ ${m[1]} (${p?.algo.id ?? '?'}): ${m[3]}`)
    }
  }
  const expected = [...meta.keys()].length
  if (total !== expected) console.log(`проверено ${total} из ${expected} задач`)
  console.log(`задач «сложно» проверено: ${total}, нарушений: ${bad}`)
  return bad === 0 && total === expected && total > 0 ? 0 : 1
}

/** проставить algo там, где признак выполняется; остальные «сложно» → «вуз» */
function assign(): number {
  const algos = readAlgos()
  const topics = readTopics(SRC)
  const probeData = probe(topics)
  const report: string[] = []
  for (const t of topics) {
    const d = JSON.parse(readFileSync(t.file, 'utf8')) as { topic: string; problems: Problem[] }
    let hard = 0
    for (const p of d.problems) {
      if (p.level !== 'сложно') continue
      const pr = probeData.get(p.id)
      if (!pr) {
        p.level = 'вуз'
        delete p.algo
        report.push(`${p.id} → вуз: проба не дала результата`)
        continue
      }
      const hit = algos.find((a) => howOk(a.how, p.input, pr.rules, pr.ms))
      if (hit) {
        p.algo = hit.id
        hard++
      } else {
        p.level = 'вуз'
        delete p.algo
        report.push(`${p.id} → вуз: нет алгоритма или быстро (${pr.ms} мс)`)
      }
    }
    writeFileSync(t.file, JSON.stringify(d, null, 1) + '\n', 'utf8')
    console.log(`${d.topic}: «сложно» ${hard}`)
  }
  writeFileSync(join(TMP, 'hard-assign.txt'), report.join('\n') + '\n', 'utf8')
  console.log('перенесено в вуз: ' + report.length + ' (журнал ' + join(TMP, 'hard-assign.txt') + ')')
  return 0
}

/** П4: подложные «сложно» должны быть красными */
function selftest(): number {
  const lines = [
    `(load "${lit(HC)}")`,
    `(hc-rule "bad1" "union({1}, {2})" '("groebner-basis"))`,
    `(hc-rule "bad2" "solve(x^2 = 4, x)" '("gal-"))`,
  ]
  const script = join(TMP, 'hard-selftest.lisp')
  writeFileSync(script, lines.join('\n') + '\n', 'utf8')
  const r = spawnSync(EXE, [script], { encoding: 'utf8', timeout: 300000 })
  const fails = String(r.stdout ?? '').split(/\r?\n/).filter((l) => /^@@\S+ fail /.test(l)).length
  console.log(`подложных «сложно» отвергнуто: ${fails} из 2`)
  return fails === 2 ? 0 : 1
}

const mode = process.argv[2]
process.exit(mode === 'assign' ? assign() : mode === 'selftest' ? selftest() : checkAll())
