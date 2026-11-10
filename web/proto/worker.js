// WASM.2a: рантайм .NET в отдельном Web Worker — главная страница не замирает во время вычисления.
// Протокол: страница → {id, op, code?, mode?, file?, test?, from?, count?}, воркер → {id, json}.
// op: eval | latex-of-input | run-test-file | run-named-test | run-test-slice | test-files.
import { dotnet } from './_framework/dotnet.js'

let exports = null
const boot = { t0: performance.now(), ms: 0 }

// Строковый литерал Lisp из JS-строки (кавычки и обратные слэши)
function lispString(s) {
  return '"' + String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"').replace(/\n/g, '\\n').replace(/\r/g, '') + '"'
}

async function init() {
  const { getAssemblyExports, getConfig } = await dotnet.create()
  const config = getConfig()
  const ex = await getAssemblyExports(config.mainAssemblyName)
  const cand =
    (ex.Lisp && ex.Lisp.Wasm && ex.Lisp.Wasm.Exports) ||
    (ex.Exports) ||
    (ex.Lisp && ex.Lisp.Exports) ||
    null
  if (!cand || typeof cand.Eval !== 'function') {
    throw new Error('Eval не найден; exports: ' + JSON.stringify(Object.keys(ex)))
  }
  exports = cand
  boot.ms = performance.now() - boot.t0
  self.postMessage({ ready: true, bootMs: boot.ms })
}

const ready = init().catch((e) => {
  self.postMessage({ bootError: String((e && e.message) || e) })
})

// Печать Lisp-строки снимает кавычки и экранирует \ и " — раскрываем обратно одним проходом,
// чтобы не пострадали «\\» внутри LaTeX (переносы строк в матрицах).
function unquoteLisp(s) {
  let out = ''
  for (let i = 0; i < s.length; i++) {
    const ch = s[i]
    if (ch === '\\' && i + 1 < s.length) {
      const nx = s[i + 1]
      out += nx === 'n' ? '\n' : nx === 't' ? '\t' : nx
      i++
    } else out += ch
  }
  return out
}

// Предпросмотр: разбор входного языка и печать в LaTeX без вычисления.
// math-latex возвращает СТРОКУ LaTeX, а оболочка хоста кладёт её в result (печать Lisp-строки в кавычках) и в
// latex как \text{…}. JSON уже раскрыл экранирование, поэтому остаётся только снять внешние кавычки —
// обратные слэши LaTeX (\lim, \frac) трогать нельзя.
function latexOfInput(code) {
  const env = JSON.parse(exports.Eval('(math-latex (math-read ' + lispString(code) + '))', 'lisp'))
  if (env.status === 'error') return JSON.stringify(env)
  let s = String(env.result || '')
  if (s.length >= 2 && s[0] === '"' && s[s.length - 1] === '"') s = s.slice(1, -1)
  return JSON.stringify({ status: 'answer', latex: s })
}

self.onmessage = async (e) => {
  const m = e.data || {}
  if (!m.id) return
  try {
    await ready
    let json
    switch (m.op) {
      case 'eval': json = exports.Eval(m.code, m.mode); break
      case 'latex-of-input': json = latexOfInput(m.code); break
      case 'run-test-file': json = exports.RunTestFile(m.file); break
      case 'run-named-test': json = exports.RunNamedTest(m.file, m.test); break
      case 'run-test-slice': json = exports.RunTestSlice(m.file, m.from, m.count); break
      case 'test-files': json = exports.TestFiles(); break
      default: throw new Error('неизвестная операция: ' + m.op)
    }
    self.postMessage({ id: m.id, json })
  } catch (err) {
    self.postMessage({
      id: m.id,
      json: JSON.stringify({ status: 'error', ok: false, error: String((err && err.message) || err) }),
    })
  }
}
