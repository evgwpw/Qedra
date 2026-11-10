// WEB.OPN: многобуквенные имена в вводе формул. MathLive в node не работает (нужен браузер), поэтому
// «ascii» в таблице — реальный вывод MathLive 0.111.4 (convertLatexToAsciiMath / getValue('ascii-math')),
// снятый в Edge headless на защищённом LaTeX (метки \operatorname{Q9000}…); такой же вывод даёт поле ввода.
import { describe, expect, it } from 'vitest'
import { cleanName, latexToSource, protectNames } from '../app/src/latexin'
import { toSource } from '../app/src/mathjson'

// [LaTeX поля, защищённый LaTeX, ascii-math MathLive для него, ожидаемый вход языка]
const ROWS: ReadonlyArray<readonly [string, string, string, string]> = [
  ['\\operatorname{\\mathrm{potential}}\\left(122\\right)', '\\operatorname{Q9000}\\left(122\\right)', 'Q9000 (122)', 'potential(122)'],
  ['\\operatorname{potential}\\left(122\\right)', '\\operatorname{Q9000}\\left(122\\right)', 'Q9000 (122)', 'potential(122)'],
  ['\\mathrm{potential}(122)', '\\operatorname{Q9000}(122)', 'Q9000 (122)', 'potential(122)'],
  ['\\operatorname*{potential}(122)', '\\operatorname{Q9000}(122)', 'Q9000 (122)', 'potential(122)'],
  ['\\text{potential}(122)', '\\operatorname{Q9000}(122)', 'Q9000 (122)', 'potential(122)'],
  ['\\operatorname{grad}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'grad(x)'],
  ['\\operatorname{div}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'div(x)'],
  ['\\operatorname{rootsum}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'rootsum(x)'],
  ['\\operatorname{BesselJ}\\left(0,x\\right)', '\\operatorname{Q9000}\\left(0,x\\right)', 'Q9000 (0,x)', 'BesselJ(0, x)'],
  ['\\operatorname{abs}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'abs(x)'],
  ['\\operatorname{arctg}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'arctg(x)'],
  ['\\operatorname{set\\_difference}\\left(a,b\\right)', '\\operatorname{Q9000}\\left(a,b\\right)', 'Q9000 (a,b)', 'set_difference(a, b)'],
  ['\\operatorname{set_{difference}}\\left(a,b\\right)', '\\operatorname{Q9000}\\left(a,b\\right)', 'Q9000 (a,b)', 'set_difference(a, b)'],
  ['\\operatorname{certified\\_sum}\\left(a,b\\right)', '\\operatorname{Q9000}\\left(a,b\\right)', 'Q9000 (a,b)', 'certified_sum(a, b)'],
  ['\\mathrm{poly\\_gcd}\\left(a,b\\right)', '\\operatorname{Q9000}\\left(a,b\\right)', 'Q9000 (a,b)', 'poly_gcd(a, b)'],
  ['\\text{poly\\_gcd}\\left(a,b\\right)', '\\operatorname{Q9000}\\left(a,b\\right)', 'Q9000 (a,b)', 'poly_gcd(a, b)'],
  ['\\operatorname{f2}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'f2(x)'],
  ['\\operatorname{potential}\\left(x,y\\right)+\\operatorname{grad}\\left(x\\right)',
    '\\operatorname{Q9000}\\left(x,y\\right)+\\operatorname{Q9001}\\left(x\\right)', 'Q9000 (x,y)+Q9001 (x)', 'potential(x, y) + grad(x)'],
  ['2\\operatorname{potential}\\left(x\\right)^2', '2\\operatorname{Q9000}\\left(x\\right)^2', '2Q9000 (x)^2', '2 * potential(x)^2'],
  ['\\operatorname{potential}^{2}\\left(x\\right)', '\\operatorname{Q9000}^{2}\\left(x\\right)', 'Q9000 ^2(x)', 'potential(x)^2'],
  ['\\operatorname{potential}\\left(\\operatorname{grad}\\left(x\\right)\\right)',
    '\\operatorname{Q9000}\\left(\\operatorname{Q9001}\\left(x\\right)\\right)', 'Q9000 (Q9001 (x))', 'potential(grad(x))'],
  ['\\operatorname{integrate}\\left(\\frac{1}{x^2+1},x\\right)', '\\operatorname{Q9000}\\left(\\frac{1}{x^2+1},x\\right)',
    'Q9000 ((1)/(x^2+1),x)', 'integrate((1)/(x^2 + 1), x)'],
  ['\\operatorname{\\mathrm{series}}\\left(x,x,0,5\\right)', '\\operatorname{Q9000}\\left(x,x,0,5\\right)', 'Q9000 (x,x,0,5)', 'series(x, x, 0, 5)'],
  ['\\operatorname{ln}\\left(x\\right)', '\\operatorname{Q9000}\\left(x\\right)', 'Q9000 (x)', 'log(x)'],
  // без имён защита ничего не меняет
  ['xy', 'xy', 'x y', 'x * y'],
  ['2x', '2x', '2x', '2 * x'],
  ['2xy+3', '2xy+3', '2x y+3', '2 * x * y + 3'],
  ['\\sin x', '\\sin x', 'sin x', 'sin(x)'],
  ['\\sin^2x', '\\sin^2x', 'sin ^2x', 'sin(x)^2'],
  ['\\arcsin x', '\\arcsin x', 'arcsin x', 'asin(x)'],
  ['\\ln x', '\\ln x', 'ln x', 'log(x)'],
  ['\\sinh x', '\\sinh x', 'sinh x', 'sinh(x)'],
  ['\\frac{x}{2}', '\\frac{x}{2}', '(x)/(2)', '(x)/(2)'],
  ['\\sqrt{x+1}', '\\sqrt{x+1}', 'sqrt(x+1)', 'sqrt(x + 1)'],
  ['x^2', 'x^2', 'x^2', 'x^2'],
  ['\\max\\left(a,b\\right)', '\\max\\left(a,b\\right)', 'max (a,b)', 'max(a, b)'],
  ['\\det\\left(A\\right)', '\\det\\left(A\\right)', 'det (A)', 'det(A)'],
  ['\\int_0^1x^2\\mathrm{d}x', '\\int_0^1x^2\\mathrm{d}x', ' int  _0^1x^2d x', 'integrate(x^2, x, 0, 1)'],
  ['\\sum_{k=1}^{n}k^2', '\\sum_{k=1}^{n}k^2', ' sum  _(k=1)^n k^2', 'sum(k^2, k, 1, n)'],
  ['\\lim_{x\\to0}\\frac{\\sin x}{x}', '\\lim_{x\\to0}\\frac{\\sin x}{x}', 'lim _(x->0)(sin x)/(x)', 'limit((sin(x))/(x), x, 0)'],
]

describe('latexToSource: имена функций из LaTeX поля MathLive', () => {
  for (const [latex, prot, ascii, want] of ROWS) {
    it(latex, () => {
      expect(protectNames(latex).latex).toBe(prot)
      const r = latexToSource(latex, (l) => {
        expect(l).toBe(prot)
        return ascii
      })
      expect(r).toEqual({ ok: true, source: want })
    })
  }
})

describe('cleanName', () => {
  it('снимает обёртки и экранирование', () => {
    expect(cleanName('potential')).toBe('potential')
    expect(cleanName('\\mathrm{potential}')).toBe('potential')
    expect(cleanName('\\mathrm{\\text{x2}}')).toBe('x2')
    expect(cleanName('set\\_difference')).toBe('set_difference')
    expect(cleanName('set_{difference}')).toBe('set_difference')
  })
  it('не имя: одна буква, дифференциал, пробел, команда', () => {
    expect(cleanName('d')).toBeNull()
    expect(cleanName('dx')).toBeNull()
    expect(cleanName('poly gcd')).toBeNull()
    expect(cleanName('\\alpha')).toBeNull()
    expect(cleanName('2x')).toBeNull()
  })
})

describe('protectNames: граничные случаи', () => {
  it('одиночные \\mathrm{d} и \\mathrm{e} не трогает', () => {
    expect(protectNames('\\mathrm{e}^{x}').names).toEqual([])
    expect(protectNames('\\int x\\mathrm{d}x').names).toEqual([])
  })
  it('несбалансированная скобка не падает', () => {
    expect(() => protectNames('\\operatorname{abc')).not.toThrow()
  })
  it('одно имя — одна метка', () => {
    const p = protectNames('\\operatorname{f2}\\left(x\\right)+\\operatorname{f2}\\left(y\\right)')
    expect(p.names).toEqual(['f2'])
    expect(p.latex).toBe('\\operatorname{Q9000}\\left(x\\right)+\\operatorname{Q9000}\\left(y\\right)')
  })
})

describe('toSource: функции без скобок (\\sin x)', () => {
  const src = (a: string): string => {
    const r = toSource(a)
    if (!r.ok) throw new Error(r.error)
    return r.source
  }
  it('sin x, ln x, sin 2x', () => {
    expect(src('sin x')).toBe('sin(x)')
    expect(src('ln x')).toBe('log(x)')
    expect(src('sin 2x')).toBe('sin(2 * x)')
    expect(src('sin 2x cos y')).toBe('sin(2 * x) * cos(y)')
    expect(src('sin x cos x')).toBe('sin(x) * cos(x)')
  })
  it('sin x cos x — два множителя', () => {
    expect(src('sin x cos x')).toBe('sin(x) * cos(x)')
  })
  it('sin ^2x', () => {
    expect(src('sin ^2x')).toBe('sin(x)^2')
  })
  it('метка без имён не срабатывает', () => {
    expect(src('Q9000')).toBe('Q * 9000')
  })
})
