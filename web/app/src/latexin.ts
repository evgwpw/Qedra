// WEB.OPN: LaTeX редактора MathLive → входной язык с сохранением многобуквенных имён.
// ПОЧЕМУ: ascii-math MathLive печатает \operatorname{potential} по буквам («p o t e n t i a l (122)»),
// \operatorname*{…} теряет имя («\operatorname* (122)»), \text{…} даёт строку в кавычках — по такой записи
// имя функции не отличить от произведения букв. Поэтому имена вырезаются из LaTeX до перевода и заменяются
// метками \operatorname{Q9000}, \operatorname{Q9001}, … (MathLive печатает их одним словом «Q9000 (x)»);
// toSource(ascii, names) подставляет настоящие имена обратно.
import { PLACEHOLDER_BASE, toSource, type TranslateResult } from './mathjson'

/** команды, внутри которых записано имя (длинные раньше коротких: \operatorname* до \operatorname, \textrm до \text) */
const NAME_CMDS: readonly string[] = ['\\operatorname*', '\\operatorname', '\\mathrm', '\\textrm', '\\text']
const WRAP_RE = /\\(?:operatorname\*?|mathrm|textrm|text|mathit|mathsf)\{([^{}]*)\}/g
const NAME_RE = /^[A-Za-z][A-Za-z0-9_]*$/

/** тело команды → имя или null: снимает вложенные \mathrm{…}, «\_» и «_{…}» → «_» */
export function cleanName(body: string): string | null {
  let s = body.trim()
  for (let k = 0; k < 8; k++) {
    const t = s.replace(WRAP_RE, '$1')
    if (t === s) break
    s = t
  }
  s = s.replace(/_\{([A-Za-z0-9_]*)\}/g, '_$1').replace(/\\_/g, '_')
  if (!NAME_RE.test(s) || s.length < 2) return null
  // dx, dy — дифференциал в интеграле, не имя
  if (/^d[A-Za-z]$/.test(s)) return null
  return s
}

/** индекс закрывающей «}» для «{» в позиции open (учитывает вложенность и «\{»); -1, если не закрыта */
function closingBrace(s: string, open: number): number {
  let depth = 0
  for (let i = open; i < s.length; i++) {
    const c = s[i]
    if (c === '\\') { i++; continue }
    if (c === '{') depth++
    else if (c === '}') { depth--; if (depth === 0) return i }
  }
  return -1
}

export interface Protected {
  latex: string
  names: string[]
}

/** вырезает многобуквенные имена из LaTeX и ставит метки \operatorname{Q9000+k} */
export function protectNames(latex: string): Protected {
  const names: string[] = []
  let out = ''
  let i = 0
  while (i < latex.length) {
    if (latex[i] === '\\') {
      const cmd = NAME_CMDS.find((c) => latex.startsWith(c, i) && latex[i + c.length] === '{')
      if (cmd !== undefined) {
        const open = i + cmd.length
        const close = closingBrace(latex, open)
        const name = close < 0 ? null : cleanName(latex.slice(open + 1, close))
        if (name !== null) {
          let k = names.indexOf(name)
          if (k < 0) { k = names.length; names.push(name) }
          out += '\\operatorname{Q' + String(PLACEHOLDER_BASE + k) + '}'
          i = close + 1
          continue
        }
      }
      // чужая команда или не имя: копируем «\» и слово, тело разберётся дальше (там могут быть вложенные имена)
      out += latex[i]
      i++
      continue
    }
    out += latex[i]
    i++
  }
  return { latex: out, names }
}

/** LaTeX → входной язык; toAscii — перевод LaTeX в ascii-math (MathLive: convertLatexToAsciiMath или getValue) */
export function latexToSource(latex: string, toAscii: (latex: string) => string): TranslateResult {
  const p = protectNames(latex)
  return toSource(toAscii(p.latex), p.names)
}
