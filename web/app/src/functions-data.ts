// WASM.4a: чистые функции справочника и автодополнения — без bso5 и DOM,
// чтобы их можно было проверять юнит-тестами (web/tests/functions.test.ts).

export const PLACE = '▢'

/** Запись каталога: см. web/tools/gen-functions.ts */
export interface CatalogFunction {
  name: string
  signature: string
  template: string
  summary: string
  topic: string
  example: string
}

let cache: CatalogFunction[] | null = null
let loading: Promise<CatalogFunction[]> | null = null

/** ленивое чтение каталога: один запрос на всю сессию */
export function loadFunctions(): Promise<CatalogFunction[]> {
  if (cache) return Promise.resolve(cache)
  if (!loading) {
    loading = fetch('./functions.json')
      .then((r) => (r.ok ? (r.json() as Promise<CatalogFunction[]>) : []))
      .then((list) => { cache = list; return list })
      .catch(() => { cache = []; return [] })
  }
  return loading
}

// LaTeX-шаблоны для редактора MathLive: у известных функций — обычная запись, у остальных \operatorname
const LATEX_FN: Readonly<Record<string, string>> = {
  sin: '\\sin', cos: '\\cos', tan: '\\tan', cot: '\\cot', sec: '\\sec', csc: '\\csc',
  sinh: '\\sinh', cosh: '\\cosh', tanh: '\\tanh', coth: '\\coth', sech: '\\sech', csch: '\\csch',
  asin: '\\arcsin', acos: '\\arccos', atan: '\\arctan', acot: '\\operatorname{arccot}',
  asec: '\\operatorname{arcsec}', acsc: '\\operatorname{arccsc}',
  asinh: '\\operatorname{arsinh}', acosh: '\\operatorname{arcosh}', atanh: '\\operatorname{artanh}',
  exp: '\\exp', log: '\\ln', ln: '\\ln', sqrt: '\\sqrt', abs: '\\left|\\placeholder{}\\right|',
}

export function latexTemplate(fn: CatalogFunction): string {
  const base = LATEX_FN[fn.name]
  if (base) {
    // sqrt и abs уже содержат место ввода
    return base.includes('\\placeholder') ? base : base + '\\left(\\placeholder{}\\right)'
  }
  return '\\operatorname{' + fn.name + '}\\left(\\placeholder{}\\right)'
}

/** фильтр панели: имя, сигнатура, описание или тема содержат запрос */
export function filterFunctions(list: readonly CatalogFunction[], query: string): CatalogFunction[] {
  const q = query.trim().toLowerCase()
  if (!q) return [...list]
  return list.filter((fn) =>
    fn.name.toLowerCase().includes(q) || fn.signature.toLowerCase().includes(q)
    || (fn.summary || '').toLowerCase().includes(q) || (fn.topic || '').toLowerCase().includes(q))
}

/** ранжирование автодополнения: сначала имена, начинающиеся с набранного, затем прочие вхождения */
export function rankMatches(list: readonly CatalogFunction[], word: string, limit = 8): CatalogFunction[] {
  if (word.length < 2) return []
  const q = word.toLowerCase()
  const starts = list.filter((f) => f.name.toLowerCase().startsWith(q))
  const inside = list.filter((f) => !f.name.toLowerCase().startsWith(q) && f.name.toLowerCase().includes(q))
  return starts.concat(inside).slice(0, limit)
}

/** группы панели по темам в порядке каталога */
export function groupByTopic(list: readonly CatalogFunction[]): { topic: string; list: CatalogFunction[] }[] {
  const m = new Map<string, CatalogFunction[]>()
  for (const fn of list) {
    const t = fn.topic || 'прочее'
    const bucket = m.get(t)
    if (bucket) bucket.push(fn)
    else m.set(t, [fn])
  }
  return [...m.entries()].map(([topic, group]) => ({ topic, list: group }))
}
