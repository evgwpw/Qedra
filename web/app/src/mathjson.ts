// WASM.2c: перевод записи MathLive во входной язык запросов.
// ПОЧЕМУ НЕ MathJSON: в MathLive MathJSON-сериализатор живёт только вместе с @cortex-js/compute-engine
// (26 МБ распакованных, ~3.4 МБ ESM-чанков — второй CAS в бандле). Без него getValue('math-json')
// отдаёт "" (0.111.4) или ["Error","compute-engine-not-available"] (0.98.6) — проверено обоими.
// Поэтому вход — собственный линейный экспорт MathLive getValue('ascii-math'): для нужных конструкций
// (дроби, корни, степени, ∫ с пределами, ∑, ∏, lim, d/dx, матрицы, множества, |x|) он однозначен.
// Форма возврата: { ok: true, source } либо { ok: false, error } («не поддерживается: <узел>»).

/** Элементарные функции языка (lib/mathlang/runtime.lisp: m-elem-funs + sqrt) и известные имена */
const FUNCS: ReadonlySet<string> = new Set([
  'sin', 'cos', 'tan', 'cot', 'sec', 'csc',
  'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch',
  'asin', 'acos', 'atan', 'acot', 'asec', 'acsc',
  'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch',
  'exp', 'log', 'ln', 'sqrt', 'abs',
])
/** имена, которые сразу печатаются как вызов (без проверки на '(' — скобки печатает MathLive) */
const CALL_FUNCS: ReadonlySet<string> = new Set([...FUNCS, 'det', 'inverse', 'root', 'Gamma', 'gamma'])

const CONSTS: Readonly<Record<string, string>> = { oo: 'inf', infinity: 'inf', pi: 'pi' }
/** имена AsciiMath → имена входного языка (lib/mathlang/runtime.lisp: m-elem-funs) */
const RENAME: Readonly<Record<string, string>> = {
  arctan: 'atan', arcsin: 'asin', arccos: 'acos', arccot: 'acot',
  arcsec: 'asec', arccsc: 'acsc', ln: 'log',
}
// имена, которые MathLive печатает по буквам (`\operatorname{series}` → «s e r i e s»): склеиваем обратно,
// только если следом идёт «(» — иначе «x y» осталось бы произведением
const OPNAMES: ReadonlySet<string> = new Set([
  'series', 'dsolve', 'solve', 'factor', 'expand', 'simplify', 'taylor', 'subst', 'plot',
  'integrate', 'limit', 'diff', 'sum', 'product', 'det', 'inverse', 'erf',
])

const REL: ReadonlySet<string> = new Set(['=', '/=', '<', '<=', '>', '>='])
/** имена логарифма: log_10(x) и lg/ln с индексом переводятся как ln x / ln b */
const logNames: ReadonlySet<string> = new Set(['log', 'ln', 'lg'])

export type TokenKind = 'num' | 'id' | 'op'

export interface Token {
  t: TokenKind
  v: string
  sp: boolean
}

export type BinOp = '=' | '/=' | '<' | '<=' | '>' | '>=' | '+' | '-' | '*' | '/' | 'and' | 'or' | '->'

export type Node =
  | { t: 'num'; v: string }
  | { t: 'id'; v: string }
  | { t: 'neg'; x: Node }
  | { t: 'fact'; x: Node }
  | { t: 'not'; x: Node }
  | { t: 'pow'; b: Node; e: Node }
  | { t: 'sub'; b: Node; s: Node }
  | { t: 'bin'; op: BinOp; l: Node; r: Node }
  | { t: 'call'; name: string; args: Node[] }
  | { t: 'tuple'; items: Node[] }
  | { t: 'set'; items: Node[] }
  | { t: 'vec'; items: Node[] }
  | { t: 'div'; l: Node; r: Node }

export type TranslateResult = { ok: true; source: string } | { ok: false; error: string }

/** символ по индексу; за границей строки — пустая строка (сравнения с 'x' тогда ложны) */
function at(s: string, i: number): string {
  return i >= 0 && i < s.length ? (s[i] as string) : ''
}

const numRe = /[0-9]/
const letterRe = /[A-Za-z]/

function tokenize(s: string): Token[] {
  const out: Token[] = []
  let i = 0
  let sp = false
  const push = (t: TokenKind, v: string): void => {
    out.push({ t, v, sp })
    sp = false
  }
  while (i < s.length) {
    const c = at(s, i)
    if (/\s/.test(c)) { sp = true; i++; continue }
    if (numRe.test(c) || (c === '.' && numRe.test(at(s, i + 1)))) {
      let j = i
      while (j < s.length && /[0-9.]/.test(at(s, j))) j++
      push('num', s.slice(i, j))
      i = j
      continue
    }
    if (letterRe.test(c)) {
      let j = i
      while (j < s.length && letterRe.test(at(s, j))) j++
      push('id', s.slice(i, j))
      i = j
      continue
    }
    const two = s.slice(i, i + 2)
    if (two === '<=' || two === '>=' || two === '!=' || two === '->') {
      push('op', two === '!=' ? '/=' : two)
      i += 2
      continue
    }
    const map: Readonly<Record<string, string>> = {
      '≠': '/=', '≤': '<=', '≥': '>=', '→': '->', '·': '*', '×': '*', '−': '-', '∂': 'partial',
    }
    const mapped = map[c]
    if (mapped !== undefined) { push('op', mapped); i++; continue }
    if ('+-*/^_=<>!(),[]{}|\\'.includes(c)) {
      // \{ и \} из MathLive — это фигурные скобки множества
      if (c === '\\' && (at(s, i + 1) === '{' || at(s, i + 1) === '}')) {
        push('op', at(s, i + 1))
        i += 2
        continue
      }
      push('op', c)
      i++
      continue
    }
    throw new Error('неизвестный символ: ' + c)
  }
  return mergeOpNames(out)
}

/** «s e r i e s (» → «series (»: склейка имени, напечатанного по буквам (\operatorname{…}) */
function mergeOpNames(toks: readonly Token[]): Token[] {
  const out: Token[] = []
  let i = 0
  while (i < toks.length) {
    let merged = false
    const cur = toks[i] as Token
    if (cur.t === 'id' && cur.v.length === 1) {
      let word = ''
      for (let j = i; j < toks.length; j++) {
        const part = toks[j] as Token
        if (part.t !== 'id' || part.v.length !== 1) break
        word += part.v
        const next = toks[j + 1]
        const followedByCall = !!next && next.t === 'op' && next.v === '('
        if (followedByCall && OPNAMES.has(word)) {
          out.push({ t: 'id', v: word, sp: part.sp })
          i = j + 1
          merged = true
          break
        }
      }
    }
    if (!merged) { out.push(cur); i++ }
  }
  return out
}

class Parser {
  private readonly toks: readonly Token[]
  private i = 0

  constructor(tokens: readonly Token[]) { this.toks = tokens }

  private peek(k = 0): Token | undefined { return this.toks[this.i + k] }
  private next(): Token | undefined { return this.toks[this.i++] }

  private isOp(v: string, k = 0): boolean {
    const t = this.peek(k)
    return !!t && t.t === 'op' && t.v === v
  }

  private isId(v?: string, k = 0): boolean {
    const t = this.peek(k)
    return !!t && t.t === 'id' && (!v || t.v === v)
  }

  private expectOp(v: string): void {
    if (!this.isOp(v)) throw new Error('ожидалось «' + v + '»')
    this.next()
  }

  parse(): Node {
    const node = this.expr(0)
    if (this.i < this.toks.length) throw new Error('лишние символы: ' + JSON.stringify(this.peek()))
    return node
  }

  /** приоритеты: or < and < отношения < +- < * / < степень */
  private prec(): number {
    const t = this.peek()
    if (!t) return -1
    if (t.t === 'op') {
      if (t.v === 'or') return 1
      if (t.v === 'and') return 2
      if (t.v === '->') return 3
      if (REL.has(t.v)) return 3
      if (t.v === '+' || t.v === '-') return 4
      if (t.v === '*' || t.v === '/') return 5
    }
    if (t.t === 'id' && (t.v === 'and' || t.v === 'or')) return t.v === 'or' ? 1 : 2
    return -1
  }

  private expr(minPrec: number): Node {
    let left = this.unary()
    for (;;) {
      const p = this.prec()
      if (p < 0 && minPrec <= 5 && this.startsPrimary()) {
        // соположение множителей: MathLive печатает «2x», «d x» без знака умножения
        const right = this.expr(6)
        left = { t: 'bin', op: '*', l: left, r: right }
        continue
      }
      if (p < minPrec) break
      const t = this.next() as Token
      const op = t.v as BinOp
      const right = this.expr(p + 1)
      left = { t: 'bin', op, l: left, r: right }
    }
    return left
  }

  private startsPrimary(): boolean {
    const t = this.peek()
    if (!t) return false
    if (t.t === 'num') return true
    if (t.t === 'id') return !(t.v === 'and' || t.v === 'or')
    if (t.t === 'op') return t.v === '(' || t.v === '{' || t.v === '['
    return false
  }

  private unary(): Node {
    if (this.isOp('-')) { this.next(); return { t: 'neg', x: this.unary() } }
    if (this.isOp('+')) { this.next(); return this.unary() }
    if (this.isId('not')) { this.next(); return { t: 'not', x: this.unary() } }
    return this.postfix(this.primary())
  }

  /** «тесный» множитель для показателя степени: атом с постфиксами, но без вызова */
  private tight(): Node {
    let node = this.primary()
    for (;;) {
      if (this.isOp('!')) { this.next(); node = { t: 'fact', x: node }; continue }
      break
    }
    return node
  }

  /** постфиксы: ^ (степень), _ (индекс), ! (факториал), ( (вызов) */
  private postfix(start: Node): Node {
    let node = start
    for (;;) {
      if (this.isOp('^')) {
        this.next()
        // 0^+ / 0^- — односторонний предел: MathLive печатает знак сразу после ^
        const p1 = this.peek(1)
        if ((this.isOp('+') || this.isOp('-')) && p1 && p1.t === 'op' && [')', ',', '}'].includes(p1.v)) {
          const sign = (this.next() as Token).v
          node = { t: 'pow', b: node, e: { t: 'num', v: sign } }
          continue
        }
        let e: Node
        if (this.isOp('(')) { this.next(); e = this.expr(0); this.expectOp(')') }
        else e = this.tight()
        // e^{x} — это exp(x): наш принтер печатает exp(x) как e^{x}, обратно собираем степень числа e
        node = node.t === 'id' && node.v === 'e'
          ? { t: 'call', name: 'exp', args: [e] }
          : { t: 'pow', b: node, e }
        continue
      }
      if (this.isOp('_')) {
        this.next()
        let s: Node
        if (this.isOp('(')) { this.next(); s = this.expr(0); this.expectOp(')') }
        else s = this.tight()
        node = { t: 'sub', b: node, s }
        continue
      }
      if (this.isOp('!')) { this.next(); node = { t: 'fact', x: node }; continue }
      if (this.isOp('(')) {
        // пробел перед «(» MathLive ставит у вызова (sin (x), y (x)); «k(k+1)» без пробела — умножение
        const spaced = !!(this.peek() as Token).sp
        const args = this.args()
        node = this.apply(node, args, spaced)
        continue
      }
      break
    }
    return node
  }

  /** вызов уже разобранного узла: sqrt(x), f(x), (d)/(dx)(f), sin^2(x) */
  private apply(node: Node, args: Node[], spaced: boolean): Node {
    if (node.t === 'id') {
      const known = node.v.length > 1 || CALL_FUNCS.has(node.v) || OPNAMES.has(node.v)
      const first = args[0]
      if (!known && !spaced && args.length === 1 && first) return { t: 'bin', op: '*', l: node, r: first }
      return { t: 'call', name: node.v, args }
    }
    if (node.t === 'pow' && node.b.t === 'id') return { t: 'pow', b: { t: 'call', name: node.b.v, args }, e: node.e }
    // log_b(x) = ln x / ln b: в языке логарифм только натуральный (ln и log — одно и то же)
    if (node.t === 'sub' && node.b.t === 'id' && logNames.has(node.b.v)) {
      const arg = args[0]
      if (!arg) throw new Error('log: нет аргумента')
      const ln = (x: Node): Node => ({ t: 'call', name: 'log', args: [x] })
      return { t: 'bin', op: '/', l: ln(arg), r: ln(node.s) }
    }
    const dv = diffVar(node)
    const inner = args[0]
    if (dv && inner) return { t: 'call', name: 'diff', args: [inner, { t: 'id', v: dv }] }
    if (node.t === 'sub' && node.b.t === 'id') throw new Error('функция с индексом не поддерживается: ' + node.b.v)
    throw new Error('вызов у выражения не поддерживается: ' + describe(node))
  }

  private args(): Node[] {
    this.expectOp('(')
    const list: Node[] = []
    if (!this.isOp(')')) {
      list.push(this.expr(0))
      while (this.isOp(',')) { this.next(); list.push(this.expr(0)) }
    }
    this.expectOp(')')
    return list
  }

  private primary(): Node {
    const t = this.peek()
    if (!t) throw new Error('неожиданный конец формулы')
    if (t.t === 'num') { this.next(); return { t: 'num', v: t.v } }
    if (t.t === 'op' && t.v === '(') {
      this.next()
      const inner = this.expr(0)
      const items: Node[] = [inner]
      while (this.isOp(',')) { this.next(); items.push(this.expr(0)) }
      this.expectOp(')')
      // (d)/(dx) — начало записи производной
      if (items.length === 1 && inner.t === 'id' && inner.v === 'd' && this.isOp('/')) {
        this.next()
        const den = this.primary()
        return { t: 'div', l: inner, r: den }
      }
      if (items.length > 1) return { t: 'tuple', items }
      return inner
    }
    if (t.t === 'op' && (t.v === '{' || t.v === '[')) {
      const close = t.v === '{' ? '}' : ']'
      this.next()
      const items: Node[] = []
      if (!this.isOp(close)) {
        items.push(this.expr(0))
        while (this.isOp(',')) { this.next(); items.push(this.expr(0)) }
      }
      this.expectOp(close)
      return { t: t.v === '{' ? 'set' : 'vec', items }
    }
    if (t.t === 'op' && t.v === '|') {
      this.next()
      const x = this.expr(0)
      this.expectOp('|')
      return { t: 'call', name: 'abs', args: [x] }
    }
    if (t.t === 'id') {
      const name = t.v
      if (name === 'int') return this.integral()
      if (name === 'sum' || name === 'prod') return this.bigOp(name)
      if (name === 'lim') return this.limit()
      const konst = CONSTS[name]
      if (konst !== undefined) { this.next(); return { t: 'num', v: konst } }
      if (name === 'Gamma') { this.next(); return { t: 'id', v: 'gamma' } }
      if (name === 'root') {
        this.next()
        const deg = this.args()
        const arg = this.postfix(this.primary())
        const deg0 = deg[0]
        // root(3)(x) → x^(1/3)
        if (deg.length !== 1 || !deg0) throw new Error('root: ожидалась степень')
        return { t: 'pow', b: arg, e: { t: 'bin', op: '/', l: { t: 'num', v: '1' }, r: deg0 } }
      }
      // известное имя функции или переменная: скобки после него обработает postfix
      this.next()
      return { t: 'id', v: RENAME[name] ?? name }
    }
    throw new Error('неожиданный токен: ' + JSON.stringify(t))
  }

  /** int _lo^hi f dx  /  int f dx */
  private integral(): Node {
    this.next()
    let lo: Node | null = null
    let hi: Node | null = null
    if (this.isOp('_')) {
      this.next()
      lo = this.bound()
      if (this.isOp('^')) { this.next(); hi = this.bound() }
    }
    const stop = (tok: Token | undefined): boolean =>
      !!tok && tok.t === 'id' && (tok.v === 'd' || /^d[A-Za-z]$/.test(tok.v))
    const body = this.exprUntil(stop)
    const t = this.peek()
    if (!t || t.t !== 'id') throw new Error('integral: не найден dx')
    let v: Node
    if (t.v === 'd') {
      this.next()
      const u = this.next()
      if (!u || u.t !== 'id' || u.v.length !== 1) throw new Error('integral: после d ожидалась переменная')
      v = { t: 'id', v: u.v }
    } else if (/^d[A-Za-z]$/.test(t.v)) {
      this.next()
      v = { t: 'id', v: at(t.v, 1) }
    } else {
      throw new Error('integral: не найден dx')
    }
    const args: Node[] = [body, v]
    if (lo) args.push(lo)
    if (hi) args.push(hi)
    return { t: 'call', name: 'integrate', args }
  }

  /** sum _(k=1)^(oo) body */
  private bigOp(name: string): Node {
    this.next()
    let lo: Node | null = null
    let hi: Node | null = null
    if (this.isOp('_')) { this.next(); lo = this.bound() }
    if (this.isOp('^')) { this.next(); hi = this.bound() }
    const t = this.peek()
    if (!t) throw new Error(name + ': нет тела суммы')
    const body = this.expr(0)
    if (!lo || lo.t !== 'bin' || lo.op !== '=') throw new Error(name + ': ожидалось «k=1» в нижнем индексе')
    if (!hi) throw new Error(name + ': нет верхней границы')
    return { t: 'call', name: name === 'sum' ? 'sum' : 'product', args: [body, lo.l, lo.r, hi] }
  }

  /** lim _(x->0) body */
  private limit(): Node {
    this.next()
    if (!this.isOp('_')) throw new Error('lim: нет нижнего индекса')
    this.next()
    const inner = this.bound()
    if (inner.t !== 'bin' || inner.op !== '->') throw new Error('lim: ожидалось «x->a»')
    let point: Node = inner.r
    let side: string | null = null
    if (point.t === 'pow' && point.b.t === 'num' && point.e.t === 'num'
      && (point.e.v === '+' || point.e.v === '-')) {
      side = point.e.v === '+' ? 'plus' : 'minus'
      point = point.b
    }
    const body = this.expr(0)
    const args: Node[] = [body, inner.l, point]
    if (side) args.push({ t: 'id', v: side })
    return { t: 'call', name: 'limit', args }
  }

  /**
   * граница интегрирования/суммы: _(oo), _(k=1) или без скобок — одиночный атом (_0).
   * Верхнюю границу (^…) разбирает сам вызывающий, поэтому постфикс ^ здесь не съедаем.
   */
  private bound(): Node {
    if (this.isOp('(')) { this.next(); const x = this.expr(0); this.expectOp(')'); return x }
    return this.primary()
  }

  /** выражение, останавливающееся перед токеном-стопом на нулевой глубине */
  private exprUntil(stop: (tok: Token | undefined) => boolean): Node {
    const saved = this.toks
    let depth = 0
    let j = this.i
    while (j < saved.length) {
      const t = saved[j] as Token
      if (t.t === 'op' && (t.v === '(' || t.v === '{' || t.v === '[')) depth++
      if (t.t === 'op' && (t.v === ')' || t.v === '}' || t.v === ']')) depth--
      if (depth === 0 && stop(t)) break
      j++
    }
    if (j === this.i) throw new Error('пустое тело')
    const sub = saved.slice(this.i, j)
    this.i = j
    return new Parser(sub).parse()
  }
}

function describe(n: Node | undefined): string {
  return n ? n.t : String(n)
}

/** (d)/(dx): MathLive печатает знаменатель как «d x» (два токена → умножение) или «dx» */
function diffVar(node: Node): string | null {
  if (node.t !== 'div') return null
  if (node.l.t !== 'id' || node.l.v !== 'd') return null
  const r = node.r
  if (r.t === 'id' && /^d[A-Za-z]$/.test(r.v)) return at(r.v, 1)
  if (r.t === 'id' && r.v === 'd') return null
  if (r.t === 'bin' && r.op === '*' && r.l.t === 'id' && r.l.v === 'd'
    && r.r.t === 'id' && r.r.v.length === 1) return r.r.v
  return null
}

// ---------- печать во входной язык ----------
const PREC = { or: 1, and: 2, rel: 3, add: 4, mul: 5 } as const

function precOf(n: Node): number {
  if (n.t === 'bin') {
    if (n.op === 'or') return PREC.or
    if (n.op === 'and') return PREC.and
    if (REL.has(n.op) || n.op === '->') return PREC.rel
    if (n.op === '+' || n.op === '-') return PREC.add
    return PREC.mul
  }
  if (n.t === 'neg') return PREC.add
  return 9
}

function print(n: Node, minPrec = 0): string {
  const s = printRaw(n)
  return precOf(n) < minPrec ? '(' + s + ')' : s
}

function printRaw(n: Node): string {
  switch (n.t) {
    case 'num': return n.v
    case 'id': return n.v
    case 'neg': return '-' + print(n.x, PREC.add + 1)
    case 'fact': {
      const x = n.x
      const s = x.t === 'num' || x.t === 'id' || x.t === 'call' ? printRaw(x) : '(' + printRaw(x) + ')'
      return s + '!'
    }
    case 'pow': {
      const b = n.b.t === 'num' || n.b.t === 'id' || n.b.t === 'call' ? printRaw(n.b) : '(' + printRaw(n.b) + ')'
      return b + '^' + print(n.e, 9)
    }
    case 'not': return 'not ' + print(n.x, 9)
    case 'tuple': return '[' + n.items.map((a) => print(a)).join(', ') + ']'
    case 'sub':
      // индекс: у известных имён — часть имени выражения (обрабатывается в call), иначе запрещено
      throw new Error('индекс не поддерживается во входном языке')
    case 'bin': {
      const p = precOf(n)
      if (n.op === '/') return '(' + print(n.l) + ')/(' + print(n.r) + ')'
      if (n.op === '->') throw new Error('стрелка вне предела')
      return print(n.l, p) + ' ' + n.op + ' ' + print(n.r, p + 1)
    }
    case 'call': return n.name + '(' + n.args.map((a) => print(a)).join(', ') + ')'
    case 'set': return '{' + n.items.map((a) => print(a)).join(', ') + '}'
    case 'vec': return '[' + n.items.map((a) => print(a)).join(', ') + ']'
    case 'div': throw new Error('(d)/(dx) без аргумента')
    default: {
      const never: never = n
      throw new Error('неизвестный узел: ' + String(never))
    }
  }
}

/** ascii-math MathLive → выражение входного языка */
export function toSource(ascii: string): TranslateResult {
  try {
    const text = String(ascii || '').trim()
    if (!text) return { ok: false, error: 'пустая формула' }
    const node = new Parser(tokenize(text)).parse()
    return { ok: true, source: print(node) }
  } catch (e) {
    return { ok: false, error: String(e instanceof Error ? e.message : e) }
  }
}

// имя по карточке: перевод MathJSON; пока вход — ascii-math (см. заголовок файла)
export const mathjsonToSource = toSource
