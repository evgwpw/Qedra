// WASM.5b: независимая проверка каталога примеров (оракул).
// Читает web/app/examples/*.json, проверяет каждый ответ своим способом (см. lisp/examples-check.lisp),
// распределение уровней/видов и уникальность; один запуск Lisp.exe на весь каталог.
import { spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..', '..')
const WEB = join(ROOT, 'web')
const DIR = join(ROOT, 'web', 'app', 'examples')
const CHECKER = join(ROOT, 'tests', 'Lisp.Tests', 'lisp', 'examples-check.lisp')
const TMP = join(tmpdir(), 'qedra-examples')

interface Problem {
  id: string
  title: string
  input: string
  level: 'школа' | 'вуз' | 'сложно'
  kind: 'ответ' | 'отказ' | 'график' | 'ошибка'
  check: string
  expect: string
  ref?: string
  algo?: string
}

interface TopicFile {
  topic: string
  problems: Problem[]
}

function lispExe(): string | null {
  for (const cfg of ['Debug', 'Release']) {
    const p = join(ROOT, 'src', 'Lisp.Host', 'bin', cfg, 'net10.0', 'Lisp.exe')
    if (existsSync(p)) return p
  }
  return null
}

function load(): TopicFile[] {
  return readdirSync(DIR)
    .filter((f) => f.endsWith('.json') && f !== 'index.json')
    .map((f) => JSON.parse(readFileSync(join(DIR, f), 'utf8')) as TopicFile)
}

function lit(s: string): string {
  return '"' + s.replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"'
}

describe('каталог примеров (WASM.5b)', () => {
  const topics = load()

  it('в теме ≥ 100 примеров, ≥ 20 школы и вуза, отказов ≤ 15 %, id уникальны', () => {
    const ids = new Set<string>()
    const bad: string[] = []
    for (const t of topics) {
      const n = t.problems.length
      if (n < 100) bad.push(`${t.topic}: ${n} примеров`)
      const lv = (l: string): number => t.problems.filter((p) => p.level === l).length
      // REL.1e: «сложно» — только по факту (механический оракул), минимума нет
      for (const l of ['школа', 'вуз']) {
        if (lv(l) < 20) bad.push(`${t.topic}: ${l} — ${lv(l)}`)
      }
      // 5–15 % отказов там, где система честно не отвечает; в чистых темах оракула отказов 0
      const ref = t.problems.filter((p) => p.kind === 'отказ').length
      if (ref / n > 0.15) bad.push(`${t.topic}: отказов ${ref} из ${n}`)
      const err = t.problems.filter((p) => p.kind === 'ошибка').length
      if (err > 0) bad.push(`${t.topic}: ошибок системы ${err} — вынести в отчёт`)
      for (const p of t.problems) {
        if (ids.has(p.id)) bad.push(`повтор id ${p.id}`)
        ids.add(p.id)
        if (!p.title.trim()) bad.push(`${p.id}: пустой заголовок`)
      }
    }
    expect(bad, bad.join('; ')).toEqual([])
  })

  it('в каталоге 15 тем', () => {
    expect(topics.length).toBe(15)
  })

  it('каждый ответ проверен независимо', { timeout: 900000 }, async () => {
    const exe = lispExe()
    if (!exe) {
      console.warn('Lisp.exe не найден — независимая проверка пропущена')
      return
    }
    mkdirSync(TMP, { recursive: true })
    const lines = [`(load ${lit(CHECKER)})`]
    const all: Problem[] = []
    for (const t of topics) {
      for (const p of t.problems) {
        all.push(p)
        lines.push(
          `(ex-report ${lit(p.id)} ${lit(p.input)} ${lit(p.expect)} ${lit(p.kind)} ${lit(p.check)} ${lit(p.ref ?? '')})`,
        )
      }
    }
    const file = join(TMP, 'examples-check-run.lisp')
    writeFileSync(file, lines.join('\n') + '\n', 'utf8')
    const r = spawnSync(exe, [file], { encoding: 'utf8', timeout: 900000, maxBuffer: 64 * 1024 * 1024 })
    const out = String(r.stdout ?? '')
    const rows = out.split('\n').filter((l) => l.startsWith('@@')).map((l) => l.slice(2).trim())
    const bad = rows.filter((l) => !l.endsWith(' ok'))
    expect(rows.length, 'проверено примеров').toBe(all.length)
    expect(bad.slice(0, 10), `расхождений ${bad.length}: ${bad.slice(0, 10).join(' | ')}`).toEqual([])
  })

  // REL.1e: «сложно» — механический оракул (algo + признак how + медиана ≥ 30 мс)
  it('«сложно» проходит механический оракул', { timeout: 900000 }, () => {
    const r = spawnSync('npm', ['run', 'check:hard'], { cwd: WEB, shell: true, encoding: 'utf8', timeout: 900000 })
    expect(String(r.stdout ?? '') + String(r.stderr ?? '')).toMatch(/нарушений: 0/)
    expect(r.status).toBe(0)
  })

  it('подложные «сложно» отвергаются', { timeout: 300000 }, () => {
    const r = spawnSync('npm', ['run', 'check:hard', '--', 'selftest'], {
      cwd: WEB,
      shell: true,
      encoding: 'utf8',
      timeout: 300000,
    })
    expect(String(r.stdout ?? '')).toMatch(/отвергнуто: 2 из 2/)
    expect(r.status).toBe(0)
  })
})
