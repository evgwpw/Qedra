// WASM.2c/WASM.4a: круговой тест ввода формул — latex (наш принтер) → MathLive → ascii-math → входной язык,
// затем движок сверяет исходное и переведённое выражение (структурно после simplify, иначе численно в 3 точках).
import { toSource } from './mathjson'

// Несколько выражений из каталога задач (сам каталог — web/app/examples/*.json, грузится интерфейсом)
const SAMPLE: readonly string[] = [
  'integrate(x^3, x)',
  'integrate(1/(x^2 + 1), x)',
  'integrate(sin(x)^2, x)',
  'limit(sin(x)/x, x, 0)',
  'sum(k^2, k, 1, n)',
  'dsolve(y\'\' + y = 0, y(x))',
  'solve(x^3 - 1, x)',
  'factor(x^4 - 5*x^2 + 4)',
]

// Дополнительные случаи корпуса TEX.1 в записи входного языка (дроби, корни, степени, |x|, n!, множества,
// матрицы, отношения, логика, sin², ln, ∑, ∏, lim, d/dx, определённый интеграл)
const EXTRA: readonly string[] = [
  'x^2/2',
  'sqrt(x+1)',
  'x^(1/3)',
  '(x+1)^2',
  '1/(2*x)',
  'x - (b - c)',
  '2*2',
  'x /= 0',
  'x <= 1',
  'x >= 1',
  'abs(x)',
  'n!',
  '{1, 2, 3}',
  '[[1,2],[3,4]]',
  'sin(x)^2',
  'log(x)',
  'exp(-x^2)',
  'x > 0 and y > 0',
  'x > 0 or x < 0',
  'not (x = 0)',
  'diff(x^3, x)',
  'integrate(x^2, x)',
  'integrate(exp(-x), x, 0, inf)',
  'sum(1/k^2, k, 1, inf)',
  'product(k, k, 1, 4)',
  'limit(sin(x)/x, x, 0)',
  'atan(x)',
  'sinh(x)',
]

interface RoundtripItem {
  n: number
  name: string
  topic: string
  src: string
  latex?: string
  ascii?: string
  translated?: string
  verdict?: string
  error?: string
}

const mf = document.getElementById('mf') as MathFieldElement
const state = document.getElementById('state') as HTMLElement
const rows = document.getElementById('rows') as HTMLElement

function litOf(s: string): string {
  return '"' + String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"'
}

// сверка в движке: Lisp-функция rt-eq определяет исход сравнения
const RT_HELPERS = `
(define (rt-num-eq a b)
  (let loop ((pts (list (list 'x 7/3) (list 'x -5/4) (list 'x 11/7)
                        (list 'y 3/2) (list 'k 5) (list 'n 3))))
    (if (null? pts) #t
        (let* ((p (car pts))
               (va (try (eval-num (subst p a)) (lambda (e) #f)))
               (vb (try (eval-num (subst p b)) (lambda (e) #f))))
          (if (and (number? va) (number? vb) (< (abs (- va vb)) 1e-9))
              (loop (cdr pts))
              #f)))))
(define (rt-eq sa sb)
  (let ((a (try (math-read sa) (lambda (e) 'rt-parse-a)))
        (b (try (math-read sb) (lambda (e) 'rt-parse-b))))
    (cond ((equal? a 'rt-parse-a) 'parse-a)
          ((equal? b 'rt-parse-b) 'parse-b)
          ((equal? (simplify a) (simplify b)) 'eq)
          ((try (rt-num-eq (math-eval sa) (math-eval sb)) (lambda (e) #f)) 'num)
          (else 'neq))))
`

async function evalLisp(code: string): Promise<string> {
  const res = JSON.parse(await window.lispEval(code, 'lisp')) as LispAnswer
  if (res.error) return 'error: ' + res.error
  return res.result || res.pretty || ''
}

async function run(): Promise<void> {
  await evalLisp(RT_HELPERS)
  const corpus = [
    ...SAMPLE.map((src) => ({ name: src, src, topic: 'каталог' })),
    ...EXTRA.map((src) => ({ name: src, src, topic: 'TEX.1' })),
  ]
  const results: RoundtripItem[] = []
  for (const [i, c] of corpus.entries()) {
    const item: RoundtripItem = { n: i + 1, name: c.name, topic: c.topic, src: c.src }
    try {
      const latex = await window.lispLatexOfInput(c.src)
      const lj = JSON.parse(latex) as LispAnswer
      if (lj.status === 'error' || !lj.latex) { item.verdict = 'no-latex'; item.error = lj.error || '' }
      else if (String(lj.latex).startsWith('\\text{')) { item.verdict = 'text-latex' }
      else {
        item.latex = lj.latex
        mf.setValue(lj.latex, { format: 'latex' })
        item.ascii = mf.getValue('ascii-math')
        const tr = toSource(item.ascii)
        if (!tr.ok) { item.verdict = 'unsupported'; item.error = tr.error }
        else {
          item.translated = tr.source
          const verdict = await evalLisp('(rt-eq ' + litOf(c.src) + ' ' + litOf(tr.source) + ')')
          item.verdict = String(verdict).replace(/^["']|["']$/g, '')
        }
      }
    } catch (e) {
      item.verdict = 'exception'
      item.error = String(e instanceof Error ? e.message : e)
    }
    results.push(item)
    const tr = document.createElement('tr')
    const cls = item.verdict === 'eq' || item.verdict === 'num' ? 'ok' : 'bad'
    tr.innerHTML = `<td>${item.n}</td><td>${escHtml(item.src)}</td><td>${escHtml(item.latex || '')}</td>` +
      `<td>${escHtml(item.ascii || '')}</td><td>${escHtml(item.translated || item.error || '')}</td>` +
      `<td class="${cls}">${String(item.verdict)}</td>`
    rows.appendChild(tr)
  }
  const passed = results.filter((r) => r.verdict === 'eq' || r.verdict === 'num').length
  const summary = { total: results.length, passed, percent: Math.round((100 * passed) / results.length) }
  window.rtResults = { summary, results }
  state.textContent = `итого ${passed}/${results.length} (${summary.percent} %)`
  window.rtDone = true
}

function escHtml(s: unknown): string {
  return String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c] ?? c)
}

async function start(): Promise<void> {
  const t0 = Date.now()
  while (!window.lispReady && Date.now() - t0 < 120000) await new Promise((r) => setTimeout(r, 100))
  // MathLive грузится лениво из vendor (в сборку не попадает); каталог считается как в app.tsx
  const dir = new URL('../../vendor/mathlive/', import.meta.url)
  await import(/* @vite-ignore */ new URL('mathlive.min.mjs', dir).href)
  await customElements.whenDefined('math-field')
  await run()
}

void start()
