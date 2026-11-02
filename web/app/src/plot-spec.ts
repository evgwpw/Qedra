// WASM.4a: чистые функции графиков — разбор вызова plot(…), переименование id в SVG,
// оценка «пилы» для автоподбора диапазона. Без bso5 и DOM: проверяются в web/tests/plot.test.ts.

export type PlotKind = 'plot' | 'plot-implicit' | 'plot-contour' | 'plot3d'

export interface PlotSpec {
  kind: PlotKind
  expr: string
  vars: string[]
  ranges: number[]
  az: number
  el: number
  /** диапазон задан по умолчанию — подбираем по разрешимости кривой */
  auto?: boolean
  svg?: string
}

interface KindSpec {
  call: string
  vars: number
  ranges: number
}

export const KINDS: Readonly<Record<PlotKind, KindSpec>> = {
  plot: { call: 'plot', vars: 1, ranges: 2 },
  'plot-implicit': { call: 'plot-implicit', vars: 2, ranges: 4 },
  'plot-contour': { call: 'plot-contour', vars: 2, ranges: 4 },
  plot3d: { call: 'plot3d', vars: 2, ranges: 4 },
}

export function lit(s: string): string {
  return '"' + String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"'
}

/** «plot(sin(x)/x, x, -10, 10)» → спецификация графика; не вызов графика — null */
export function parsePlotCall(src: string): PlotSpec | null {
  const m = /^\s*(plot|plot-implicit|plot-contour|plot3d)\s*\(([\s\S]*)\)\s*$/.exec(String(src || ''))
  if (!m) return null
  const kind = m[1] as PlotKind
  const spec = KINDS[kind]
  if (!spec) return null
  const parts = splitTop(m[2] ?? '')
  if (parts.length !== 1 + spec.vars + spec.ranges) return null
  const expr = (parts[0] ?? '').trim()
  const vars = parts.slice(1, 1 + spec.vars).map((s) => s.trim())
  const nums = parts.slice(1 + spec.vars).map((s) => Number(s.trim()))
  if (vars.some((v) => !/^[a-zA-Z][a-zA-Z0-9]*$/.test(v))) return null
  if (nums.some((n) => !Number.isFinite(n))) return null
  return { kind, expr, vars, ranges: nums, az: 30, el: 25 }
}

/** деление строки по запятым верхнего уровня (скобки/квадратные/фигурные) */
export function splitTop(s: string): string[] {
  const out: string[] = []
  let depth = 0
  let cur = ''
  for (const c of s) {
    if (c === '(' || c === '[' || c === '{') depth++
    if (c === ')' || c === ']' || c === '}') depth--
    if (c === ',' && depth === 0) { out.push(cur); cur = ''; continue }
    cur += c
  }
  out.push(cur)
  return out
}

export function fmtNum(v: number): string {
  return String(v)
}

/** диапазон по индексу: в спецификации всегда 2 или 4 числа (см. KINDS) */
export function rng(p: PlotSpec, i: number): number {
  return p.ranges[i] ?? 0
}

export function round1(v: number): number {
  return Math.round(v * 10) / 10
}

export function callSource(p: PlotSpec): string {
  // выражение передаётся строкой: (plot (math-read "sin(x)/x") 'x -10 10)
  const args = ['(math-read ' + lit(p.expr) + ')', ...p.vars.map((v) => "'" + v), ...p.ranges.map(fmtNum)]
  if (p.kind === 'plot3d') args.push(':azimuth', fmtNum(round1(p.az)), ':elevation', fmtNum(round1(p.el)))
  return '(' + KINDS[p.kind].call + ' ' + args.join(' ') + ')'
}

// ---------- автоподбор диапазона ----------
// Берём самый широкий вид, на котором 400 отсчётов ещё разрешают кривую: доля «точек поворота»
// (смен знака приращения) у правильно выбранного диапазона мала, у sin(x^3) на [−10, 10] близка к 0.5.
export const RANGE_CANDIDATES: ReadonlyArray<readonly [number, number]> = [
  [-10, 10], [-5, 5], [-3, 3], [-2, 2], [-1, 1],
]
export const RANGE_SAMPLES = 400
export const MAX_TURN_RATE = 0.15

/** доля смен знака приращения по отсчётам; null — точек слишком мало для суждения */
export function turnRateOf(ys: readonly number[]): number | null {
  let turns = 0
  let pairs = 0
  for (let i = 1; i < ys.length - 1; i++) {
    const d1 = (ys[i] as number) - (ys[i - 1] as number)
    const d2 = (ys[i + 1] as number) - (ys[i] as number)
    if (!Number.isFinite(d1) || !Number.isFinite(d2)) continue
    pairs++
    if (d1 * d2 < 0) turns++
  }
  return pairs > 20 ? turns / pairs : null
}

/** id в SVG фиксированные (plclip): переименовываем при вставке, чтобы графики не конфликтовали */
export function renameIds(svg: string, n: number): string {
  const ids = [...svg.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1] ?? '')
  let out = svg
  for (const id of ids) {
    const to = id + '-p' + n
    out = out.split('id="' + id + '"').join('id="' + to + '"')
    out = out.split('url(#' + id + ')').join('url(#' + to + ')')
    out = out.split('href="#' + id + '"').join('href="#' + to + '"')
    out = out.split('clip-path="#' + id + '"').join('clip-path="#' + to + '"')
  }
  return out
}
