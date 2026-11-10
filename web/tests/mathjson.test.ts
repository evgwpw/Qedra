// WASM.4a: юнит-тесты перевода ascii-math (MathLive) во входной язык.
// Эталоны сняты со стенда и сверены со старой JS-реализацией (85 случаев, расхождений 0).
import { describe, expect, it } from 'vitest'
import { toSource } from '../app/src/mathjson'

/** успешный перевод: строка результата */
function src(ascii: string): string {
  const r = toSource(ascii)
  if (!r.ok) throw new Error('ожидался перевод, получено: ' + r.error)
  return r.source
}

describe('toSource: числа и арифметика', () => {
  it('соположение даёт произведение', () => {
    expect(src('2x+1')).toBe('2 * x + 1')
    expect(src('2 x')).toBe('2 * x')
    expect(src('a b')).toBe('a * b')
  })

  it('дробь печатается как отношение в скобках', () => {
    expect(src('x^2/2')).toBe('(x^2)/(2)')
    expect(src('1/(2*x)')).toBe('(1)/(2 * x)')
  })

  it('унарный минус и разность скобок', () => {
    expect(src('x - (b - c)')).toBe('x - (b - c)')
    expect(src('-x^2')).toBe('-x^2')
  })

  it('степень и корень', () => {
    expect(src('x^(1/3)')).toBe('x^((1)/(3))')
    expect(src('root(3)(x)')).toBe('x^((1)/(3))')
    expect(src('x^(-1)')).toBe('x^(-1)')
  })

  it('факториал', () => {
    expect(src('n!')).toBe('n!')
  })

  it('константы', () => {
    expect(src('oo')).toBe('inf')
    expect(src('infinity')).toBe('inf')
  })
})

describe('toSource: функции и экспонента', () => {
  it('e^{…} — это exp(…)', () => {
    expect(src('e^(x^2)')).toBe('exp(x^2)')
    expect(src('exp(-x^2)')).toBe('exp(-x^2)')
  })

  it('тригонометрия и гиперболические', () => {
    expect(src('sin(x)^2')).toBe('sin(x)^2')
    expect(src('sinh(x)')).toBe('sinh(x)')
    expect(src('atan(x)')).toBe('atan(x)')
  })

  it('arcsin переименовывается в asin', () => {
    expect(src('arcsin(x)')).toBe('asin(x)')
  })

  it('log_b(x) = log(x)/log(b)', () => {
    expect(src('log_2(x)')).toBe('(log(x))/(log(2))')
    expect(src('log_10(x^4)')).toBe('(log(x^4))/(log(10))')
  })

  it('модуль', () => {
    expect(src('|x|')).toBe('abs(x)')
    expect(src('abs(x)')).toBe('abs(x)')
  })

  it('вызов с пробелом перед скобкой — всё равно вызов', () => {
    expect(src('sin (x)')).toBe('sin(x)')
  })

  it('имя, напечатанное по буквам, склеивается перед «(»', () => {
    expect(src('s e r i e s ( x , x , 0 , 4 )')).toBe('series(x, x, 0, 4)')
  })
})

describe('toSource: интегралы, суммы, пределы', () => {
  it('неопределённый интеграл', () => {
    expect(src('int x dx')).toBe('integrate(x, x)')
  })

  it('интеграл с пределами', () => {
    expect(src('int_0^1 x^2 dx')).toBe('integrate(x^2, x, 0, 1)')
    expect(src('int_(0)^(oo) e^(-x) dx')).toBe('integrate(exp(-x), x, 0, inf)')
  })

  it('сумма и произведение', () => {
    expect(src('sum_(k=1)^oo 1/k^2')).toBe('sum((1)/(k^2), k, 1, inf)')
    expect(src('prod_(k=1)^4 k')).toBe('product(k, k, 1, 4)')
  })

  it('предел', () => {
    expect(src('lim_(x->0) sin(x)/x')).toBe('limit((sin(x))/(x), x, 0)')
    expect(src('lim_(x->oo) (1+1/x)^x')).toBe('limit((1 + (1)/(x))^x, x, inf)')
  })
})

describe('toSource: множества, матрицы, логика', () => {
  it('множество и вектор', () => {
    expect(src('{1, 2, 3}')).toBe('{1, 2, 3}')
    expect(src('[[1,2],[3,4]]')).toBe('[[1, 2], [3, 4]]')
  })

  it('отношения и логика', () => {
    expect(src('x > 0 and y > 0')).toBe('x > 0 and y > 0')
    expect(src('not (x = 0)')).toBe('not (x = 0)')
    expect(src('x <= 1')).toBe('x <= 1')
  })
})

describe('toSource: отказы', () => {
  it('пустая формула', () => {
    const r = toSource('   ')
    expect(r.ok).toBe(false)
    if (!r.ok) expect(r.error).toBe('пустая формула')
  })

  it('неизвестный узел — понятная ошибка', () => {
    const r = toSource('x|y')
    expect(r.ok).toBe(false)
    if (!r.ok) expect(r.error).toContain('лишние символы')
  })

  it('индекс у неизвестной функции не поддерживается', () => {
    const r = toSource('foo_2(x)(y)')
    expect(r.ok).toBe(false)
    if (!r.ok) expect(r.error).toContain('не поддерживается')
  })

  it('ошибка не бросается наружу', () => {
    expect(() => toSource('(((')).not.toThrow()
  })
})
