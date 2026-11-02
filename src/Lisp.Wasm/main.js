// WASM.2a: страница-клиент рантайма. Сам .NET живёт в worker.js — главный поток не замирает.
// window.lispEval(code, mode) → Promise<json-строка>; window.lispRunTestFile(file) и т. п. — тоже Promise.
// window.lispStop() — terminate + перезапуск рантайма (индикатор загрузки: window.lispReady === false).

// URL воркера — относительно ЭТОГО модуля, а не документа: приложение живёт в /app/index.html,
// и «./worker.js» от документа искало бы /app/worker.js (404, рантайм не поднимался).
const WORKER_URL = new URL('./worker.js', import.meta.url).href

let worker = null
let nextId = 1
const pending = new Map()
let readyWaiter = null

window.lispReady = false
window.lispBusy = false
window.lispBootMs = 0
window.lispError = null

function setReady(v) {
  window.lispReady = v
  if (v && readyWaiter) { readyWaiter(); readyWaiter = null }
}

function rejectAll(why) {
  for (const [, p] of pending) p.reject(new Error(why))
  pending.clear()
  window.lispBusy = false
}

function boot() {
  setReady(false)
  worker = new Worker(WORKER_URL, { type: 'module' })
  worker.onmessage = (e) => {
    const m = e.data || {}
    if (m.ready) {
      window.lispBootMs = m.bootMs
      setReady(true)
      return
    }
    if (m.bootError) {
      window.lispError = m.bootError
      rejectAll(m.bootError)
      return
    }
    const p = pending.get(m.id)
    if (!p) return
    pending.delete(m.id)
    window.lispBusy = pending.size > 0
    p.resolve(m.json)
  }
  worker.onerror = (e) => {
    window.lispError = String((e && e.message) || 'ошибка Worker')
    rejectAll(window.lispError)
  }
}

function call(op, payload) {
  if (!worker) return Promise.reject(new Error('рантайм не запущен'))
  const id = nextId++
  window.lispBusy = true
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject })
    worker.postMessage({ id, op, ...payload })
  })
}

// Ждать готовности рантайма (после старта или после «Стоп»)
window.lispWhenReady = () =>
  window.lispReady ? Promise.resolve() : new Promise((res) => { readyWaiter = res })

window.lispEval = (code, mode) => window.lispWhenReady().then(() => call('eval', { code, mode }))
window.lispLatexOfInput = (code) => window.lispWhenReady().then(() => call('latex-of-input', { code }))
window.lispTestFiles = () => window.lispWhenReady().then(() => call('test-files', {}))
window.lispRunTestFile = (file) => window.lispWhenReady().then(() => call('run-test-file', { file }))
window.lispRunNamedTest = (file, test) => window.lispWhenReady().then(() => call('run-named-test', { file, test }))
window.lispRunTestSlice = (file, from, count) =>
  window.lispWhenReady().then(() => call('run-test-slice', { file, from, count }))

// «Стоп»: убить воркер (вычисление прерывается мгновенно), поднять новый рантайм
window.lispStop = () => {
  try { if (worker) worker.terminate() } catch (_) { /* уже мёртв */ }
  worker = null
  rejectAll('прервано')
  boot()
  return window.lispWhenReady()
}

boot()
