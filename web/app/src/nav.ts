// WEB.NAV: чистая логика плавающей навигации по разделам страницы и запоминание свёрнутости каталога.
export interface NavSection {
  id: string      // id элемента-якоря в разметке
  label: string
  /** раздел существует в разметке только при условии (ответ) */
  needs?: 'answer'
}

export const NAV_SECTIONS: NavSection[] = [
  { id: 'sec-input', label: 'Ввод' },
  { id: 'formula-box', label: 'Редактор формул' },
  { id: 'sec-functions', label: 'Функции' },
  { id: 'answer', label: 'Результат', needs: 'answer' },
  { id: 'sec-history', label: 'История' },
  { id: 'sec-examples', label: 'Примеры' },
]

/** порог прокрутки (px), после которого панель навигации показывается */
export const NAV_SCROLL_THRESHOLD = 240

export function navVisible(scrollY: number): boolean {
  return scrollY > NAV_SCROLL_THRESHOLD
}

/** какие пункты показывать: «Результат» — только когда ответ есть; остальные раскрываются переходом */
export function visibleNav(answerVisible: boolean): NavSection[] {
  return NAV_SECTIONS.filter((s) => s.needs !== 'answer' || answerVisible)
}

// WEB.EX2: свёрнуты разделы (темы) каталога, а не весь блок; раскрытые темы помнятся в localStorage
export const TOPICS_KEY = 'lisp-example-topics-v1'

export function loadOpenTopics(store: Pick<Storage, 'getItem'> | null): Set<string> {
  try {
    const raw = store?.getItem(TOPICS_KEY)
    const arr: unknown = raw ? JSON.parse(raw) : []
    return new Set(Array.isArray(arr) ? arr.filter((x): x is string => typeof x === 'string') : [])
  } catch { return new Set() }
}

export function saveOpenTopics(store: Pick<Storage, 'setItem'> | null, open: ReadonlySet<string>): void {
  try { store?.setItem(TOPICS_KEY, JSON.stringify([...open])) } catch { /* хранилище недоступно */ }
}

/** строка каталога подходит под поисковый запрос (регистр не важен; пустой запрос — все) */
export function matchesQuery(fields: readonly string[], q: string): boolean {
  const s = q.trim().toLowerCase()
  return s === '' || fields.join(' ').toLowerCase().includes(s)
}
