import { describe, it, expect } from 'vitest'
import { ambiguousPowerHint } from '../app/src/inputhints'

describe('ambiguousPowerHint', () => {
  it('x^1/3', () => {
    expect(ambiguousPowerHint('x^1/3')).toBe('x^1/3 читается как (x^1)/3; корень — x^(1/3)')
  })
  it('x^2/3 с пробелами', () => {
    expect(ambiguousPowerHint('x ^ 2 / 3')).toContain('корень — x^(2/3)')
  })
  it('скобочная база (x+1)^1/2', () => {
    expect(ambiguousPowerHint('(x+1)^1/2')).toBe('(x+1)^1/2 читается как ((x+1)^1)/2; корень — (x+1)^(1/2)')
  })
  it('внутри ввода из задачи', () => {
    expect(ambiguousPowerHint('integrate(sin(x)^2 / (ln (x^1/3) + tan(x)), x)')).toContain('x^1/3')
  })
  it('нет: x^(1/3)', () => { expect(ambiguousPowerHint('x^(1/3)')).toBeNull() })
  it('нет: (x^2)/3', () => { expect(ambiguousPowerHint('(x^2)/3')).toBeNull() })
  it('нет: sin(x)^2 / (x+1) — деление на скобку', () => { expect(ambiguousPowerHint('sin(x)^2 / (x+1)')).toBeNull() })
  it('нет: деление на переменную и на дробное', () => {
    expect(ambiguousPowerHint('x^2/y')).toBeNull()
    expect(ambiguousPowerHint('x^2/3.5')).toBeNull()
    expect(ambiguousPowerHint('x^2.5/3')).toBeNull()
  })
  it('нет: без степени', () => { expect(ambiguousPowerHint('x/3 + 1/2')).toBeNull() })
  it('нет: пустой ввод', () => { expect(ambiguousPowerHint('')).toBeNull() })
})
