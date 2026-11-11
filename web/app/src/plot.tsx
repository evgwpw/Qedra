// WASM.2e/WASM.4a: графики. Система уже строит SVG (lib/plot.lisp), интерфейс:
// — встраивает SVG в ответ (с переименованием id: в графике фиксированный id="plclip");
// — 2D: колесо/перетаскивание меняют диапазон и ПЕРЕЗАПРАШИВАЮТ plot (200 мс; пока считается — растянутая старая картинка);
// — 3D: поворот мышью — предпросмотр на canvas по сетке plot3d-points (запрошена один раз, проекция в JS),
//   по отпусканию — точный plot3d с новыми :azimuth/:elevation; колесо — масштаб x/y с перезапросом;
// — «Сохранить SVG»/«Сохранить PNG»; двойной щелчок — исходный вид.
// Императивно остаётся только то, что нельзя выразить привязкой: вставка SVG-строки в stage и кадры canvas.
import { signal, computed, $, Show } from 'bso5'

import {
  callSource, cardLabel, fmtNum, isOneDim, lit, renameIds, rng, round1, turnRateOf,
  RANGE_CANDIDATES, RANGE_SAMPLES, MAX_TURN_RATE, type PlotSpec,
} from './plot-spec'

export { parsePlotCall, parseDsolveCall, splitTop, renameIds, turnRateOf } from './plot-spec'
export type { PlotKind, PlotSpec } from './plot-spec'

async function turnRate(expr: string, v: string, a: number, b: number): Promise<number | null> {
  const lisp = `(let ((f (math-read ${lit(expr)})) (n ${RANGE_SAMPLES}) (a ${a}) (b ${b}))
                  (foldl (lambda (acc i)
                           (let* ((x (+ a (* (- b a) (/ i n))))
                                  (y (try (eval-num (subst (list '${v} x) f)) (lambda (e) #f))))
                             (string-append acc (if (number? y) (to-string y) "#") ";")))
                         "" (range (+ n 1))))`
  const text = await evalLisp(lisp)
  const ys = text.split(';').filter((s) => s !== '').map((s) => (s === '#' ? NaN : Number(s)))
  return turnRateOf(ys)
}

/** диапазон по умолчанию; сужаем, только если на широком вид «пилит» (недоразрешённые колебания) */
export async function pickRange(expr: string, v: string): Promise<number[]> {
  try {
    for (const [a, b] of RANGE_CANDIDATES) {
      const rate = await turnRate(expr, v, a, b)
      if (rate === null) return [a, b]
      if (rate <= MAX_TURN_RATE) return [a, b]
    }
  } catch (_) { /* движок не ответил — оставляем обычный диапазон */ }
  return [...(RANGE_CANDIDATES[0] as readonly [number, number])]
}

async function evalLisp(code: string): Promise<string> {
  const res = JSON.parse(await window.lispEval(code, 'lisp')) as LispAnswer
  if (res.error) throw new Error(res.error)
  let text = String(res.result || res.pretty || '')
  // prettyPrint строки — это "…" без экранирования внутри: снимаем только внешние кавычки
  if (text.length >= 2 && text[0] === '"' && text[text.length - 1] === '"') text = text.slice(1, -1)
  return text
}

/** SVG по спецификации сразу (для проверки до создания карточки: ошибка Lisp — исключение с понятным текстом) */
export async function renderPlotSvg(p: PlotSpec): Promise<string> {
  const svg = String(await evalLisp(callSource(p)))
  if (!svg.trimStart().startsWith('<svg')) throw new Error('движок вернул не SVG')
  return svg
}

/** «График» для команды CAS (integrate, diff, …): строка-функция от x из ответа или ошибка с пояснением */
export async function plotAnswerExpr(src: string): Promise<string> {
  return evalLisp('(plot-answer-expr ' + lit(src) + ")")
}

/** отрезок по умолчанию для dsolve(…): точка начального условия ± 5 */
export async function odeWindow(src: string): Promise<[number, number]> {
  try {
    const t = await evalLisp('(let ((w (plot-ode-window ' + lit(src) + '))) (string-append (to-string (car w)) " " (to-string (cadr w))))')
    const [a, b] = t.trim().split(/\s+/).map(Number)
    if (Number.isFinite(a) && Number.isFinite(b)) return [a as number, b as number]
  } catch (_) { /* движок не ответил — обычный отрезок */ }
  return [-5, 5]
}

/** текст ошибки движка без служебного префикса «ОШИБКА:» */
export function plainError(e: unknown): string {
  return String(e instanceof Error ? e.message : e).replace(/^\s*(ОШИБКА|ошибка):\s*/, '')
}


interface Pt3 {
  x: number
  y: number
  z: number
}

interface Proj {
  sx: number
  sy: number
  depth: number
}

interface DragState {
  x: number
  y: number
  ranges: number[]
  az: number
  el: number
  moved: boolean
}

interface CardState {
  reqId: number
  svg: string
  canvas: HTMLCanvasElement | null
  points: (Pt3 | null)[][] | null
  pointsBusy?: boolean
  drag: DragState | null
}

let plotSeq = 0

/** карточка графика; p — из parsePlotCall (или {kind, expr, vars, ranges, az, el, svg}) */
export function createPlotCard(p: PlotSpec): HTMLElement {
  const n = ++plotSeq
  const home = { ranges: [...p.ranges] }
  const state: CardState = { reqId: 0, svg: '', canvas: null, points: null, drag: null }

  // реактивное состояние карточки — сигналы bso5, разметка подписана через $()
  const error = signal('')
  const hint = signal('')
  const rangeText = signal('')
  const noteText = computed(() => (error.value ? 'ошибка: ' + error.value : hint.value))
  const noteClass = computed(() => (error.value ? 'plot-note err' : 'plot-note'))
  // кнопки сохранения активны, когда есть SVG: $() принимает только Signal, поэтому computed через $
  const hasSvg = signal(false)
  const noSvg = computed(() => !hasSvg.value)

  const stage = document.createElement('div')
  stage.className = 'plot-stage'

  const card = (
    <section class="plot-card">
      <div class="row">
        <span class="lbl">График</span>
        <code class="plot-expr">{cardLabel(p)}</code>
        <span class="grow"></span>
        <span class="plot-view">{$(rangeText)}</span>
        <button class="btn small" disabled={$(noSvg)} onClick={saveSvg}>SVG</button>
        <button class="btn small" disabled={$(noSvg)} onClick={savePng}>PNG</button>
        <button class="btn small" onClick={reset}>сброс</button>
      </div>
      {stage}
      <Show when={() => noteText.value !== ''}>
        <div class={$(noteClass)}>{$(noteText)}</div>
      </Show>
    </section>
  ) as HTMLElement

  // ---------- запросы ----------
  let timer = 0
  function schedule(delay = 200): void {
    clearTimeout(timer)
    timer = window.setTimeout(() => { void refresh() }, delay)
  }

  async function refresh(): Promise<void> {
    const id = ++state.reqId
    error.value = ''
    hint.value = 'считается…'
    try {
      const svg = String(await evalLisp(callSource(p)))
      if (id !== state.reqId) return
      if (!svg.trimStart().startsWith('<svg')) throw new Error('движок вернул не SVG')
      state.svg = svg
      stage.innerHTML = renameIds(svg, n)
      stage.style.transform = ''
      hasSvg.value = true
      hint.value = ''
    } catch (e) {
      if (id === state.reqId) error.value = String(e instanceof Error ? e.message : e)
    }
  }

  function updateRangeText(): void {
    rangeText.value = isOneDim(p)
      ? `${p.vars[0] ?? ''} ∈ [${fmtNum(rng(p, 0))}, ${fmtNum(rng(p, 1))}]`
      : `${p.vars[0] ?? ''} ∈ [${fmtNum(rng(p, 0))}, ${fmtNum(rng(p, 1))}], ${p.vars[1] ?? ''} ∈ [${fmtNum(rng(p, 2))}, ${fmtNum(rng(p, 3))}]`
  }

  // ---------- 2D: масштаб и сдвиг ----------
  function approxTransform(oldR: readonly number[], newR: readonly number[], horizontal: 'x' | 'y'): string {
    // растягиваем старую картинку под новый диапазон, пока считается новая
    if (!isOneDim(p)) return ''
    const oa = oldR[0] ?? 0
    const ob = oldR[1] ?? 0
    const na = newR[0] ?? 0
    const nb = newR[1] ?? 0
    const oldSpan = ob - oa
    const newSpan = nb - na
    const k = oldSpan / newSpan
    const dx = ((oa + ob) / 2 - (na + nb) / 2) / newSpan
    return `scale(${horizontal === 'y' ? 1 : k}, 1) translate(${dx * 100}%, 0)`
  }

  function zoom(event: WheelEvent): void {
    if (isOneDim(p)) {
      const rect = stage.getBoundingClientRect()
      const t = Math.min(1, Math.max(0, (event.clientX - rect.left) / rect.width))
      const factor = event.deltaY > 0 ? 1.25 : 0.8
      const a = rng(p, 0)
      const b = rng(p, 1)
      const span = (b - a) * factor
      const at = a + t * (b - a)
      p.ranges = [at - t * span, at + (1 - t) * span]
    } else {
      const factor = event.deltaY > 0 ? 1.25 : 0.8
      const a = rng(p, 0)
      const b = rng(p, 1)
      const c = rng(p, 2)
      const d = rng(p, 3)
      const cx = (a + b) / 2
      const cy = (c + d) / 2
      p.ranges = [cx - ((cx - a) * factor), cx + ((b - cx) * factor), cy - ((cy - c) * factor), cy + ((d - cy) * factor)]
    }
    event.preventDefault()
    stage.style.transform = approxTransform(home.ranges, p.ranges, 'x')
    updateRangeText()
    hint.value = 'считается…'
    schedule()
  }

  function pointerDown(event: PointerEvent): void {
    if (event.button !== 0) return
    stage.setPointerCapture(event.pointerId)
    state.drag = { x: event.clientX, y: event.clientY, ranges: [...p.ranges], az: p.az, el: p.el, moved: false }
    if (p.kind === 'plot3d') void ensurePoints().then(() => { if (state.drag) drawPreview() })
  }

  function pointerMove(event: PointerEvent): void {
    const d = state.drag
    if (!d) return
    const dx = event.clientX - d.x
    const dy = event.clientY - d.y
    if (Math.abs(dx) + Math.abs(dy) < 2) return
    d.moved = true
    if (p.kind === 'plot3d') {
      p.az = d.az + dx * 0.6
      p.el = Math.max(-89, Math.min(89, d.el + dy * 0.5))
      drawPreview()
      hint.value = 'поворот: azimuth ' + round1(p.az) + '°, elevation ' + round1(p.el) + '°'
      return
    }
    const rect = stage.getBoundingClientRect()
    if (isOneDim(p)) {
      const span = (d.ranges[1] ?? 0) - (d.ranges[0] ?? 0)
      const shift = (-dx / rect.width) * span
      p.ranges = [(d.ranges[0] ?? 0) + shift, (d.ranges[1] ?? 0) + shift]
    } else {
      const sx = (((d.ranges[1] ?? 0) - (d.ranges[0] ?? 0)) * -dx) / rect.width
      const sy = (((d.ranges[3] ?? 0) - (d.ranges[2] ?? 0)) * dy) / rect.height
      p.ranges = [(d.ranges[0] ?? 0) + sx, (d.ranges[1] ?? 0) + sx, (d.ranges[2] ?? 0) + sy, (d.ranges[3] ?? 0) + sy]
    }
    stage.style.transform = approxTransform(d.ranges, p.ranges, 'x')
    updateRangeText()
    hint.value = 'считается…'
  }

  function pointerUp(event: PointerEvent): void {
    const d = state.drag
    state.drag = null
    if (!d) return
    try { stage.releasePointerCapture(event.pointerId) } catch (_) { /* уже отпущено */ }
    if (!d.moved) return
    schedule(120)
  }

  function reset(): void {
    p.ranges = [...home.ranges]
    if (p.kind === 'plot3d') { p.az = 30; p.el = 25 }
    updateRangeText()
    stage.innerHTML = ''
    void refresh()
  }

  // ---------- 3D: предпросмотр на canvas ----------
  async function ensurePoints(): Promise<void> {
    if (state.points || state.pointsBusy) return
    state.pointsBusy = true
    try {
      const spec = `(list :surface (math-read ${lit(p.expr)}) '${p.vars[0] ?? ''} '${p.vars[1] ?? ''} ` +
        p.ranges.map(fmtNum).join(' ') + ')'
      // плоский текст «x,y,z;…|строка;строка»: разбирать печать вложенных списков не нужно
      const lisp = `(let ((g (plot3d-points ${spec} :n 40)))
                     (foldl (lambda (acc row)
                              (string-append acc
                                (foldl (lambda (a pt)
                                         (if (pair? pt)
                                             (string-append a (to-string (nth pt 0)) ","
                                                               (to-string (nth pt 1)) ","
                                                               (to-string (nth pt 2)) ";")
                                             (string-append a "#;")))
                                       "" row)
                                "|"))
                            "" g))`
      const text = String(await evalLisp(lisp))
      state.points = text.split('|').filter((r) => r.trim() !== '').map((row) =>
        row.split(';').filter((s) => s !== '').map((s): Pt3 | null => {
          if (s === '#') return null
          const [x, y, z] = s.split(',').map(Number)
          return x !== undefined && y !== undefined && z !== undefined
            && Number.isFinite(x) && Number.isFinite(y) && Number.isFinite(z) ? { x, y, z } : null
        }))
    } catch (_) {
      state.points = null
    } finally {
      state.pointsBusy = false
    }
  }

  /** проекция pl3-projector (lib/plot.lisp), ортогональная */
  function project(x: number, y: number, z: number): Proj {
    const ra = (p.az * Math.PI) / 180
    const re = (p.el * Math.PI) / 180
    const ca = Math.cos(ra), sa = Math.sin(ra), ce = Math.cos(re), se = Math.sin(re)
    const x1 = x * ca - y * sa
    const y1 = x * sa + y * ca
    return { sx: x1, sy: z * ce + y1 * se, depth: y1 * ce - z * se }
  }

  function drawPreview(): void {
    const rows = state.points
    if (!rows || rows.length < 2) return
    if (!state.canvas) {
      const cv = document.createElement('canvas')
      cv.className = 'plot-canvas'
      cv.width = 600
      cv.height = 480
      state.canvas = cv
      stage.replaceChildren(cv)
    }
    const cv = state.canvas
    cv.style.display = 'block'
    const ctx = cv.getContext('2d')
    if (!ctx) return
    ctx.clearRect(0, 0, cv.width, cv.height)
    ctx.fillStyle = '#f7f9fc'
    ctx.fillRect(0, 0, cv.width, cv.height)

    const proj = rows.map((row) => row.map((pt) => (pt ? project(pt.x, pt.y, pt.z) : null)))
    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity
    for (const row of proj) {
      for (const q of row) {
        if (!q) continue
        if (q.sx < minX) minX = q.sx
        if (q.sx > maxX) maxX = q.sx
        if (q.sy < minY) minY = q.sy
        if (q.sy > maxY) maxY = q.sy
      }
    }
    if (!Number.isFinite(minX) || maxX - minX === 0 || maxY - minY === 0) return
    const pad = 40
    const k = Math.min((cv.width - 2 * pad) / (maxX - minX), (cv.height - 2 * pad) / (maxY - minY))
    const toPx = (q: Proj): [number, number] => [(q.sx - minX) * k + pad, cv.height - ((q.sy - minY) * k + pad)]

    const quads: { pts: Proj[]; depth: number; z: number }[] = []
    for (let j = 0; j < proj.length - 1; j++) {
      const rowA = proj[j] as (Proj | null)[]
      const rowB = proj[j + 1] as (Proj | null)[]
      const srcA = rows[j] as (Pt3 | null)[]
      const srcB = rows[j + 1] as (Pt3 | null)[]
      for (let i = 0; i < rowA.length - 1; i++) {
        const a = rowA[i], b = rowA[i + 1], c = rowB[i + 1], d = rowB[i]
        const za = srcA[i], zb = srcB[i + 1]
        if (!a || !b || !c || !d || !za || !zb) continue
        quads.push({
          pts: [a, b, c, d],
          depth: (a.depth + b.depth + c.depth + d.depth) / 4,
          z: (za.z + zb.z) / 2,
        })
      }
    }
    quads.sort((u, v) => v.depth - u.depth)
    let lo = Infinity, hi = -Infinity
    for (const q of quads) { if (q.z < lo) lo = q.z; if (q.z > hi) hi = q.z }
    const span = hi - lo || 1
    for (const q of quads) {
      const t = (q.z - lo) / span
      const r = Math.round(158 + (8 - 158) * t)
      const g = Math.round(202 + (48 - 202) * t)
      const bl = Math.round(225 + (107 - 225) * t)
      ctx.fillStyle = `rgb(${r},${g},${bl})`
      ctx.beginPath()
      const px = q.pts.map(toPx)
      const p0 = px[0] as [number, number]
      ctx.moveTo(p0[0], p0[1])
      for (let i = 1; i < px.length; i++) {
        const pi = px[i] as [number, number]
        ctx.lineTo(pi[0], pi[1])
      }
      ctx.closePath()
      ctx.fill()
    }
  }

  // ---------- сохранение ----------
  function currentSvg(): string {
    const el = stage.querySelector('svg')
    return el ? el.outerHTML : ''
  }

  function download(name: string, blob: Blob): void {
    const a = document.createElement('a')
    a.href = URL.createObjectURL(blob)
    a.download = name
    document.body.appendChild(a)
    a.click()
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove() }, 1000)
  }

  function saveSvg(): void {
    const svg = currentSvg()
    if (!svg) return
    download('plot-' + n + '.svg', new Blob([svg], { type: 'image/svg+xml' }))
  }

  function savePng(): void {
    const svg = currentSvg()
    if (!svg) return
    const img = new Image()
    const blob = new Blob([svg], { type: 'image/svg+xml' })
    const url = URL.createObjectURL(blob)
    img.onload = () => {
      const cv = document.createElement('canvas')
      cv.width = img.width || 600
      cv.height = img.height || 480
      const ctx = cv.getContext('2d')
      if (!ctx) { URL.revokeObjectURL(url); return }
      ctx.fillStyle = '#fff'
      ctx.fillRect(0, 0, cv.width, cv.height)
      ctx.drawImage(img, 0, 0)
      URL.revokeObjectURL(url)
      cv.toBlob((b) => { if (b) download('plot-' + n + '.png', b) }, 'image/png')
    }
    img.onerror = () => { URL.revokeObjectURL(url); error.value = 'не удалось сохранить PNG' }
    img.src = url
  }

  stage.addEventListener('wheel', zoom, { passive: false })
  stage.addEventListener('pointerdown', pointerDown)
  stage.addEventListener('pointermove', pointerMove)
  stage.addEventListener('pointerup', pointerUp)
  stage.addEventListener('pointercancel', pointerUp)
  stage.addEventListener('dblclick', reset)

  updateRangeText()
  if (p.svg) {
    state.svg = p.svg
    stage.innerHTML = renameIds(p.svg, n)
  } else {
    void refresh()
  }
  return card
}
