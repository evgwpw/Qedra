import { describe, it, expect } from 'vitest'
import { parseAttempts, lastStatement, needsAttempts, countAttempts } from '../app/src/attempts'

const SAMPLE = [
  'Интегрирование по x — отказ: нет подходящего приёма интегрирования — 251.1 мс',
  '  Интегрирование по частям — отказ: нет результата (#f) — 25.1 мс',
  '    Выбор u и dv — отказ: нет результата (#f) — 24.7 мс',
  '  Алгоритм Риша — отказ: Риш не решил: не знаю — 10.4 мс',
].join('\n')

describe('parseAttempts', () => {
  it('отступы дают вложенность', () => {
    const t = parseAttempts(SAMPLE)
    expect(t.nodes).toHaveLength(1)
    const root = t.nodes[0]!
    expect(root.label).toBe('Интегрирование по x')
    expect(root.children.map((c) => c.label)).toEqual(['Интегрирование по частям', 'Алгоритм Риша'])
    expect(root.children[0]!.children[0]!.label).toBe('Выбор u и dv')
    expect(countAttempts(t.nodes)).toBe(4)
  })
  it('отказ, причина с двоеточием, мс', () => {
    const n = parseAttempts(SAMPLE).nodes[0]!.children[1]!
    expect(n.ok).toBe(false)
    expect(n.reason).toBe('Риш не решил: не знаю')
    expect(n.ms).toBeCloseTo(10.4)
  })
  it('успех и ×N', () => {
    const t = parseAttempts('Подстановка — успех: u = x^2 ×3 — 1.5 мс\nДругое — успех ×2 — 0.2 мс')
    expect(t.nodes[0]).toMatchObject({ ok: true, reason: 'u = x^2', repeats: 3, ms: 1.5 })
    expect(t.nodes[1]).toMatchObject({ ok: true, reason: '', repeats: 2, label: 'Другое' })
  })
  it('сиблинги после глубокой ветки; пометка об обрезке; мусор пропускается', () => {
    const t = parseAttempts('A — отказ — 1 мс\n  B — отказ — 1 мс\n    C — отказ — 1 мс\nD — успех — 2 мс\nмусор\n… показаны первые 3')
    expect(t.nodes.map((n) => n.label)).toEqual(['A', 'D'])
    expect(t.note).toBe('показаны первые 3')
  })
  it('пустой текст', () => {
    expect(parseAttempts('').nodes).toEqual([])
  })
})

describe('lastStatement / needsAttempts', () => {
  it('последний оператор; «;» в скобках и кавычках не делит', () => {
    expect(lastStatement('x:=1; integrate(f(x), x)')).toBe('integrate(f(x), x)')
    expect(lastStatement('f("a;b", 2)')).toBe('f("a;b", 2)')
    expect(lastStatement('a; b;  ')).toBe('b')
    expect(lastStatement('')).toBe('')
  })
  it('explain только для unknown/nonelementary или пустых шагов', () => {
    expect(needsAttempts('unknown', false)).toBe(true)
    expect(needsAttempts('nonelementary', false)).toBe(true)
    expect(needsAttempts('answer', false)).toBe(false)
    expect(needsAttempts('error', false)).toBe(false)
    expect(needsAttempts('answer', true)).toBe(true)
    expect(needsAttempts('error', true)).toBe(false)
  })
})
