// WASM.4a: юнит-тесты разбора plot(…), переименования id в SVG и оценки автоподбора диапазона.
import { describe, expect, it } from 'vitest'
import { callSource, cardLabel, isOneDim, parseDsolveCall, parsePlotCall, renameIds, splitTop, turnRateOf } from '../app/src/plot-spec'

describe('parsePlotCall', () => {
  it('plot(expr, x, a, b)', () => {
    const p = parsePlotCall('plot(sin(x)/x, x, -10, 10)')
    expect(p).not.toBeNull()
    expect(p).toMatchObject({ kind: 'plot', expr: 'sin(x)/x', vars: ['x'], ranges: [-10, 10], az: 30, el: 25 })
  })

  it('пробелы и края строки не мешают', () => {
    expect(parsePlotCall('  plot(1/(x^2-1), x, -3, 3)  ')).toMatchObject({ expr: '1/(x^2-1)' })
  })

  it('plot3d: две переменные и четыре границы', () => {
    const p = parsePlotCall('plot3d(sin(x)*cos(y), x, y, -3, 3, -3, 3)')
    expect(p).toMatchObject({ kind: 'plot3d', vars: ['x', 'y'], ranges: [-3, 3, -3, 3] })
  })

  it('неявный график и линии уровня', () => {
    expect(parsePlotCall('plot-implicit(x^2+y^2-1, x, y, -2, 2, -2, 2)')?.kind).toBe('plot-implicit')
    expect(parsePlotCall('plot-contour(x^2-y^2, x, y, -2, 2, -2, 2)')?.kind).toBe('plot-contour')
  })

  it('мало аргументов — не график', () => {
    expect(parsePlotCall('plot(x)')).toBeNull()
    expect(parsePlotCall('plot(sin(x), x, 0)')).toBeNull()
  })

  it('нечисловые границы — не график', () => {
    expect(parsePlotCall('plot(sin(x), x, a, b)')).toBeNull()
  })

  it('имя переменной проверяется', () => {
    expect(parsePlotCall('plot(sin(x), 2x, 0, 1)')).toBeNull()
  })

  it('не вызов графика — null', () => {
    expect(parsePlotCall('integrate(x*exp(x), x)')).toBeNull()
    expect(parsePlotCall('')).toBeNull()
    expect(parsePlotCall('plot(sin(x), x, 0, 1) extra')).toBeNull()
  })
})

describe('splitTop', () => {
  it('делит только верхний уровень', () => {
    expect(splitTop('a, f(b, c), [1,2]')).toEqual(['a', ' f(b, c)', ' [1,2]'])
  })
})

describe('callSource', () => {
  it('выражение передаётся строкой, переменные — символом', () => {
    const p = parsePlotCall('plot(sin(x)/x, x, -10, 10)')
    expect(p && callSource(p)).toBe('(plot (math-read "sin(x)/x") \'x -10 10)')
  })

  it('у 3D добавляются углы', () => {
    const p = parsePlotCall('plot3d(x*y, x, y, 0, 1, 0, 1)')
    expect(p && callSource(p)).toContain(':azimuth 30 :elevation 25')
  })
})

// WEB.PLOT: решение ОДУ и поле направлений
describe('plot_ode / dsolve', () => {
  it('plot_ode(eq, y(x), [x, a, b], условия) → plot-ode с текстом dsolve', () => {
    const p = parsePlotCall("plot_ode(y'' + y = 0, y(x), [x, -5, 5], y(0) = 1, y'(0) = 0)")
    expect(p).toMatchObject({
      kind: 'plot-ode', vars: ['x'], ranges: [-5, 5],
      expr: "dsolve(y'' + y = 0, y(x), y(0) = 1, y'(0) = 0)",
    })
  })

  it('без условий; переменная t', () => {
    expect(parsePlotCall("plot_ode(y' = y, y(t), [t, 0, 2.5])")).toMatchObject({ vars: ['t'], ranges: [0, 2.5], expr: "dsolve(y' = y, y(t))" })
  })

  it('несовпадающая переменная или не-число в отрезке — не график', () => {
    expect(parsePlotCall("plot_ode(y' = y, y(x), [t, 0, 1])")).toBeNull()
    expect(parsePlotCall("plot_ode(y' = y, y(x), [x, a, 1])")).toBeNull()
    expect(parsePlotCall("plot_ode(y' = y, y(x))")).toBeNull()
  })

  it('callSource решения ОДУ — весь dsolve строкой и границы', () => {
    const p = parsePlotCall("plot_ode(y' = y, y(x), [x, -3, 3], y(0) = 1)")
    expect(p && callSource(p)).toBe('(plot-ode-src "dsolve(y\' = y, y(x), y(0) = 1)" -3 3)')
  })

  it('plot_direction_field → plot-field с двумя переменными и четырьмя границами', () => {
    const p = parsePlotCall('plot_direction_field(x - y, x, y, -3, 3, -2, 2)')
    expect(p).toMatchObject({ kind: 'plot-field', expr: 'x - y', vars: ['x', 'y'], ranges: [-3, 3, -2, 2] })
    expect(p && callSource(p)).toBe('(plot-direction-field (math-read "x - y") \'x \'y -3 3 -2 2)')
  })

  it('parseDsolveCall: переменная из y(v); не dsolve — null', () => {
    expect(parseDsolveCall("dsolve(y' = y, y(x), y(0) = 1)")).toMatchObject({ v: 'x' })
    expect(parseDsolveCall("dsolve(y'' + y = 0, y(t))")).toMatchObject({ v: 't' })
    expect(parseDsolveCall('dsolve(y)')).toBeNull()
    expect(parseDsolveCall('integrate(x, x)')).toBeNull()
  })

  it('isOneDim: y(x) и решение ОДУ — по одной оси; поле — окно', () => {
    expect(isOneDim({ kind: 'plot' })).toBe(true)
    expect(isOneDim({ kind: 'plot-ode' })).toBe(true)
    expect(isOneDim({ kind: 'plot-field' })).toBe(false)
  })

  it('подпись карточки', () => {
    const p = parsePlotCall("plot_ode(y' = y, y(x), [x, 0, 1])")
    expect(p && cardLabel(p)).toBe("решение ОДУ: dsolve(y' = y, y(x))")
  })
})

describe('renameIds', () => {
  const svg = '<svg><clipPath id="plclip"><rect/></clipPath>' +
    '<g clip-path="url(#plclip)"><use href="#plclip"/></g></svg>'

  it('добавляет номер карточки к id и ссылкам', () => {
    const out = renameIds(svg, 3)
    expect(out).toContain('id="plclip-p3"')
    expect(out).toContain('url(#plclip-p3)')
    expect(out).toContain('href="#plclip-p3"')
    expect(out).not.toContain('id="plclip"')
  })

  it('разные номера не конфликтуют', () => {
    expect(renameIds(svg, 1)).not.toBe(renameIds(svg, 2))
  })

  it('SVG без id не меняется', () => {
    const plain = '<svg><rect width="1" height="1"/></svg>'
    expect(renameIds(plain, 5)).toBe(plain)
  })
})

describe('turnRateOf', () => {
  it('прямая линия — 0 точек поворота', () => {
    expect(turnRateOf([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22])).toBe(0)
  })

  it('пила — половина приращений меняет знак', () => {
    const ys = Array.from({ length: 41 }, (_, i) => (i % 2 === 0 ? 1 : 0))
    const rate = turnRateOf(ys)
    expect(rate).not.toBeNull()
    expect(rate as number).toBeGreaterThan(0.9)
  })

  it('пропуски (NaN) не считаются парами; слишком мало точек — null', () => {
    expect(turnRateOf([1, Number.NaN, 2, 3, 4])).toBeNull()
  })
})
