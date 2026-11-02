// WASM.3b/WASM.4a: справочник функций языка и автодополнение. Каталог — web/app/functions.json
// (шаг 3a, генерируется из docs/math-language.md). Разметка — JSX на bso5, состояние — сигналы.
import { signal, computed, effect, $, For, Show } from 'bso5'

import {
  PLACE, filterFunctions, groupByTopic, loadFunctions, rankMatches,
  type CatalogFunction,
} from './functions-data'

export { PLACE, filterFunctions, groupByTopic, latexTemplate, loadFunctions, rankMatches } from './functions-data'
export type { CatalogFunction } from './functions-data'

export interface FunctionsPanelCtx {
  onInsert: (fn: CatalogFunction) => void
  onExample: (fn: CatalogFunction) => void
}

export interface AssistCtx {
  onAccept?: (fn: CatalogFunction) => void
}

/** вставка шаблона в textarea с заменой выделения и постановкой курсора на ▢ (Tab — следующее ▢) */
export function insertTemplate(area: HTMLTextAreaElement, template: string): number {
  const start = area.selectionStart
  const end = area.selectionEnd
  const text = area.value
  const first = template.indexOf(PLACE)
  const clean = first >= 0 ? template.replace(PLACE, '') : template
  const next = text.slice(0, start) + clean + text.slice(end)
  area.value = next
  const caret = start + (first >= 0 ? first : clean.length)
  area.setSelectionRange(caret, caret)
  area.dispatchEvent(new Event('input', { bubbles: true }))
  return caret
}

/** Tab внутри поля ввода: переход к следующему месту ввода ▢ (если оно ещё осталось в тексте) */
export function tabToNextPlace(area: HTMLTextAreaElement): boolean {
  const pos = area.selectionStart
  const idx = area.value.indexOf(PLACE, pos)
  if (idx < 0) return false
  area.setSelectionRange(idx, idx + 1)
  return true
}

// ---------- панель «Функции» ----------
export function createFunctionsPanel(ctx: FunctionsPanelCtx): { node: HTMLElement; open: ReturnType<typeof signal<boolean>>; toggle: () => Promise<void> } {
  const query = signal('')
  const open = signal(false)
  const items = signal<CatalogFunction[]>([])
  const groups = computed(() => groupByTopic(filterFunctions(items.value, query.value)))

  const row = (fn: CatalogFunction): Node => (
    <div class="fn-row">
      <div class="fn-main">
        <code class="fn-sig">{fn.signature}</code>
        <div class="fn-sum">{fn.summary}</div>
      </div>
      <div class="fn-acts">
        <button class="btn small" title="вставить шаблон" onClick={() => ctx.onInsert(fn)}>вставить</button>
        {fn.example
          ? <button class="btn small" title={fn.example} onClick={() => ctx.onExample(fn)}>пример</button>
          : null}
      </div>
    </div>
  )

  const list = <div class="fn-list"></div> as HTMLElement
  // перерисовываем список целиком в effect: For с ключом по теме переиспользовал узлы,
  // и при смене фильтра в списке оставались строки прежнего запроса
  effect(() => {
    const gs = groups.value
    const nodes: Node[] = gs.length === 0
      ? [<div class="note">ничего не найдено</div>]
      : gs.map((g) => (
          <section class="fn-group">
            <div class="fn-topic">{g.topic + ' · ' + g.list.length}</div>
            {g.list.map(row)}
          </section>
        ))
    list.replaceChildren(...nodes)
  })

  const body = (
    <section class="fn-panel">
      <div class="row">
        <input
          class="fn-search"
          type="search"
          placeholder="поиск по функциям"
          value={$(query)}
          onInput={(e: Event) => { query.value = (e.target as HTMLInputElement).value }}
        />
        <span class="chip" id="fn-count">
          {$(computed(() => {
            const n = groups.value.reduce((acc, g) => acc + g.list.length, 0)
            return n + ' функций'
          }))}
        </span>
        <span class="grow"></span>
        <button class="btn small" onClick={() => { open.value = false }}>закрыть</button>
      </div>
      {list}
    </section>
  ) as HTMLElement

  async function toggle(): Promise<void> {
    if (open.value) { open.value = false; return }
    items.value = await loadFunctions()
    open.value = true
    requestAnimationFrame(() => {
      const s = body.querySelector<HTMLInputElement>('.fn-search')
      if (s) s.focus()
    })
  }

  return { node: body, open, toggle }
}

// ---------- автодополнение и подсказка сигнатуры ----------
export interface Assist {
  node: HTMLElement
  update: () => Promise<void>
  keydown: (e: KeyboardEvent) => boolean
  hide: () => void
}

/** состояние подсказок для поля ввода; keydown(e) → true, если событие поглощено */
export function createAssist(area: HTMLTextAreaElement, ctx?: AssistCtx): Assist {
  const matches = signal<CatalogFunction[]>([])
  const active = signal(0)
  const visible = signal(false)
  const hint = signal('')
  let all: CatalogFunction[] = []

  const dropdown = (
    <div class="ac-list" id="ac-list">
      <For each={matches} key={(fn) => fn.name}>
        {(fn: CatalogFunction) => (
          <div class="ac-row" onMousedown={(e: Event) => { e.preventDefault(); accept(fn) }}>
            <code class="ac-name">{fn.name}</code>
            <code class="ac-sig">{fn.signature}</code>
            <span class="ac-sum">{fn.summary}</span>
          </div>
        )}
      </For>
    </div>
  )
  const box = (
    <div class="ac-box">
      <Show when={() => visible.value}>{dropdown}</Show>
      <Show when={() => hint.value !== ''}>
        <div class="sig-hint" id="sig-hint">{$(hint)}</div>
      </Show>
    </div>
  ) as HTMLElement

  /** слово слева от курсора (буквы/цифры/подчёркивание) */
  function wordAt(): string {
    const text = area.value.slice(0, area.selectionStart)
    const m = /([A-Za-z][A-Za-z0-9_]*)$/.exec(text)
    return m && m[1] ? m[1] : ''
  }

  async function update(): Promise<void> {
    all = await loadFunctions()
    const w = wordAt()
    // подсказка сигнатуры: имя уже набрано и сразу за курсором идёт '('
    const after = area.value.slice(area.selectionStart)
    const fn = w ? all.find((f) => f.name === w) : undefined
    hint.value = fn && after.startsWith('(') ? fn.signature + ' — ' + fn.summary : ''
    if (w.length < 2) { visible.value = false; return }
    const found = rankMatches(all, w)
    matches.value = found
    active.value = 0
    visible.value = found.length > 0
    highlight()
  }

  function highlight(): void {
    const rows = box.querySelectorAll<HTMLElement>('.ac-row')
    rows.forEach((r, i) => r.classList.toggle('active', i === active.value))
  }

  function accept(fn: CatalogFunction): void {
    const start = area.selectionStart
    const text = area.value.slice(0, start)
    const m = /([A-Za-z][A-Za-z0-9_]*)$/.exec(text)
    if (!m || !m[1]) return
    const from = start - m[1].length
    const next = area.value.slice(0, from) + fn.template.replace(PLACE, '') + area.value.slice(area.selectionEnd)
    area.value = next
    const caret = from + fn.template.indexOf(PLACE)
    area.setSelectionRange(caret, caret)
    area.dispatchEvent(new Event('input', { bubbles: true }))
    visible.value = false
    area.focus()
    if (ctx && ctx.onAccept) ctx.onAccept(fn)
  }

  /** обработка клавиш; true — событие поглощено (Enter без списка не перехватываем) */
  function keydown(e: KeyboardEvent): boolean {
    const list = matches.value
    if (!visible.value || list.length === 0) return false
    if (e.key === 'ArrowDown') {
      active.value = (active.value + 1) % list.length
      highlight()
      return true
    }
    if (e.key === 'ArrowUp') {
      active.value = (active.value - 1 + list.length) % list.length
      highlight()
      return true
    }
    if (e.key === 'Enter' || e.key === 'Tab') {
      const chosen = list[active.value]
      if (chosen) accept(chosen)
      return true
    }
    if (e.key === 'Escape') { visible.value = false; return true }
    return false
  }

  return { node: box, update, keydown, hide: () => { visible.value = false } }
}
