// INT.UX: подсказки к вводу (чистые функции, без DOM).

/** база степени, стоящая слева от позиции i (позиция символа '^'): скобочная группа или слово */
function baseBefore(s: string, i: number): string {
  let j = i
  while (j > 0 && s[j - 1] === ' ') j--
  if (j > 0 && s[j - 1] === ')') {
    let depth = 0
    for (let k = j - 1; k >= 0; k--) {
      if (s[k] === ')') depth++
      else if (s[k] === '(') { depth--; if (depth === 0) return s.slice(k, j) }
    }
    return s.slice(0, j)
  }
  const m = /[A-Za-z0-9_.]+$/.exec(s.slice(0, j))
  return m ? m[0] : ''
}

/**
 * Неоднозначная запись «a^n/m»: степень с целым показателем и сразу деление на целое без скобок.
 * По приоритетам это (a^n)/m, а имеют в виду чаще корень a^(n/m). Не срабатывает на (a^n)/m,
 * a^(n/m), a^n/(m), a^n/m.5, a^2.5/3. Возвращает подсказку или null.
 */
export function ambiguousPowerHint(src: string): string | null {
  const re = /\^\s*(\d+)(?![\d.])\s*\/\s*(\d+)(?![\d.\w(])/g
  for (let m = re.exec(src); m !== null; m = re.exec(src)) {
    const before = src.slice(0, m.index)
    const base = baseBefore(before, before.length) || 'x'
    const n = m[1]
    const d = m[2]
    return base + '^' + n + '/' + d + ' читается как (' + base + '^' + n + ')/' + d
      + '; корень — ' + base + '^(' + n + '/' + d + ')'
  }
  return null
}
