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

export const EXAMPLES_KEY = 'lisp-examples-open-v1'

export function loadExamplesOpen(store: Pick<Storage, 'getItem'> | null): boolean {
  try { return store?.getItem(EXAMPLES_KEY) === '1' } catch { return false }
}

export function saveExamplesOpen(store: Pick<Storage, 'setItem'> | null, open: boolean): void {
  try { store?.setItem(EXAMPLES_KEY, open ? '1' : '0') } catch { /* хранилище недоступно */ }
}
