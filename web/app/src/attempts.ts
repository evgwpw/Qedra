// WEB.EX2: разбор журнала попыток (вывод explain(...) во входном языке) в дерево.
// Строка: «<отступ><название> — успех|отказ[: причина][ ×N] — <мс> мс», отступ 2 пробела на уровень;
// последней может идти пометка об обрезке «… текст».
export interface AttemptNode {
  label: string
  ok: boolean
  reason: string
  repeats: number   // 1 — без повтора
  ms: number
  children: AttemptNode[]
}

export interface AttemptTree {
  nodes: AttemptNode[]
  note: string      // пометка «… …» (пусто, если нет)
}

const LINE = /^(.*?) — (успех|отказ)(?:: (.*?))?(?: ×(\d+))? — (\d+(?:[.,]\d+)?) мс\s*$/

export function parseAttempts(text: string): AttemptTree {
  const nodes: AttemptNode[] = []
  const stack: { depth: number; node: AttemptNode }[] = []
  let note = ''
  for (const raw of String(text || '').split(/\r?\n/)) {
    if (!raw.trim()) continue
    if (raw.startsWith('…')) { note = raw.replace(/^…\s*/, '').trim(); continue }
    const indentLen = raw.length - raw.trimStart().length
    const m = LINE.exec(raw.trimStart())
    if (!m) continue
    const node: AttemptNode = {
      label: m[1] ?? '',
      ok: m[2] === 'успех',
      reason: m[3] ?? '',
      repeats: m[4] ? Number(m[4]) : 1,
      ms: Number((m[5] ?? '0').replace(',', '.')),
      children: [],
    }
    const depth = Math.floor(indentLen / 2)
    while (stack.length > 0 && (stack[stack.length - 1] as { depth: number }).depth >= depth) stack.pop()
    const parent = stack[stack.length - 1]
    if (parent) parent.node.children.push(node)
    else nodes.push(node)
    stack.push({ depth, node })
  }
  return { nodes, note }
}

/** explain от последнего оператора ввода (операторы разделяются «;» вне скобок и кавычек); '' — пусто */
export function lastStatement(src: string): string {
  let depth = 0
  let quote = false
  let start = 0
  const parts: string[] = []
  for (let i = 0; i < src.length; i++) {
    const c = src[i]
    if (quote) { if (c === '\\') i++; else if (c === '"') quote = false; continue }
    if (c === '"') quote = true
    else if (c === '(' || c === '[' || c === '{') depth++
    else if (c === ')' || c === ']' || c === '}') depth--
    else if (c === ';' && depth <= 0) { parts.push(src.slice(start, i)); start = i + 1 }
  }
  parts.push(src.slice(start))
  const nonEmpty = parts.map((p) => p.trim()).filter((p) => p !== '')
  return nonEmpty[nonEmpty.length - 1] ?? ''
}

/** нужен ли разбор попыток: не вычислилось или шагов нет */
export function needsAttempts(status: string, stepsEmpty: boolean): boolean {
  if (status === 'error') return false
  return status === 'unknown' || status === 'nonelementary' || stepsEmpty
}

export function countAttempts(nodes: readonly AttemptNode[]): number {
  return nodes.reduce((acc, n) => acc + 1 + countAttempts(n.children), 0)
}
