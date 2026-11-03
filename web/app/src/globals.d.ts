// WASM.4a: типы глобальных объектов страницы — рантайма в Worker (web/proto/main.js),
// KaTeX из web/vendor и веб-компонента <math-field> (MathLive грузится лениво, пакета в зависимостях нет).
export {}

declare global {
  /** Ответ хоста: поля совпадают с AgentApi.Answer в src/Lisp.Host */
  interface LispAnswer {
    status: 'answer' | 'error' | 'unknown' | 'nonelementary'
    result: string
    /** вывод explain(...) — дерево попыток текстом (WEB.EX2) */
    output?: string
    conditions?: unknown
    pretty: string
    latex: string
    note: string | null
    ok: boolean
    error: string | null
    stack: string | null
  }

  interface Window {
    lispEval(code: string, mode: 'lisp' | 'math'): Promise<string>
    lispLatexOfInput(code: string): Promise<string>
    lispStop(): Promise<void>
    lispReady: boolean
    lispBusy: boolean
    lispBootMs: number
    lispError: string | null
    appReady?: boolean
    /** итоги кругового теста ввода формул (web/app/roundtrip.html) */
    rtResults?: unknown
    rtDone?: boolean
  }

  /** Минимум из API KaTeX 0.16, который использует интерфейс */
  const katex: {
    renderToString(
      tex: string,
      options?: { displayMode?: boolean; throwOnError?: boolean; strict?: 'ignore' | 'warn' | 'error' },
    ): string
  }

  /** Минимум из API <math-field> (MathLive 0.111) */
  interface MathFieldElement extends HTMLElement {
    getValue(format: 'ascii-math' | 'latex' | 'math-json'): string
    setValue(value: string, options?: { format?: 'latex' | 'ascii-math' }): void
    insert(value: string): void
  }
}
