import { describe, it, expect } from 'vitest'
import { NAV_SECTIONS, visibleNav, navVisible, loadOpenTopics, saveOpenTopics, matchesQuery, TOPICS_KEY } from '../app/src/nav'

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
  it('темы каталога по умолчанию свёрнуты; раскрытые запоминаются; сбой хранилища не падает', () => {
    const mem = new Map<string, string>()
    const store = { getItem: (k: string) => mem.get(k) ?? null, setItem: (k: string, v: string) => { mem.set(k, v) } }
    expect(loadOpenTopics(store).size).toBe(0)
    saveOpenTopics(store, new Set(['Алгебра']))
    expect(mem.has(TOPICS_KEY)).toBe(true)
    expect([...loadOpenTopics(store)]).toEqual(['Алгебра'])
    mem.set(TOPICS_KEY, '{мусор')
    expect(loadOpenTopics(store).size).toBe(0)
    const bad = { getItem: (): string | null => { throw new Error('x') }, setItem: (): void => { throw new Error('x') } }
    expect(loadOpenTopics(bad).size).toBe(0)
    expect(() => saveOpenTopics(bad, new Set(['a']))).not.toThrow()
    expect(loadOpenTopics(null).size).toBe(0)
  })
  it('поиск по полям без учёта регистра', () => {
    expect(matchesQuery(['Квадрат суммы', 'expand((x+1)^2)'], 'КВАДРАТ')).toBe(true)
    expect(matchesQuery(['a'], 'zzz')).toBe(false)
    expect(matchesQuery(['a'], '  ')).toBe(true)
  })
})
