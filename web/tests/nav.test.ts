import { describe, it, expect } from 'vitest'
import { NAV_SECTIONS, visibleNav, navVisible, loadExamplesOpen, saveExamplesOpen, EXAMPLES_KEY } from '../app/src/nav'

describe('nav', () => {
  it('«Результат» только при наличии ответа', () => {
    expect(visibleNav(false).map((s) => s.label)).not.toContain('Результат')
    expect(visibleNav(true).map((s) => s.label)).toContain('Результат')
  })
  it('id разделов уникальны', () => {
    const ids = NAV_SECTIONS.map((s) => s.id)
    expect(new Set(ids).size).toBe(ids.length)
  })
  it('панель видна после прокрутки', () => {
    expect(navVisible(0)).toBe(false)
    expect(navVisible(1000)).toBe(true)
  })
  it('каталог по умолчанию свёрнут; значение запоминается; сбой хранилища не падает', () => {
    const mem = new Map<string, string>()
    const store = { getItem: (k: string) => mem.get(k) ?? null, setItem: (k: string, v: string) => { mem.set(k, v) } }
    expect(loadExamplesOpen(store)).toBe(false)
    saveExamplesOpen(store, true)
    expect(mem.get(EXAMPLES_KEY)).toBe('1')
    expect(loadExamplesOpen(store)).toBe(true)
    const bad = { getItem: (): string | null => { throw new Error('x') }, setItem: (): void => { throw new Error('x') } }
    expect(loadExamplesOpen(bad)).toBe(false)
    expect(() => saveExamplesOpen(bad, true)).not.toThrow()
    expect(loadExamplesOpen(null)).toBe(false)
  })
})
