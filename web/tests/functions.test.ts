// WASM.4a: юнит-тесты ранжирования автодополнения, фильтра панели, группировки и LaTeX-шаблонов.
import { describe, expect, it } from 'vitest'
import { filterFunctions, groupByTopic, latexTemplate, rankMatches, type CatalogFunction } from '../app/src/functions-data'

function fn(name: string, topic = 'Интегралы', summary = 'описание'): CatalogFunction {
  return { name, signature: name + '(x)', template: name + '(▢)', summary, topic, example: '' }
}

const LIST: CatalogFunction[] = [
  fn('integrate', 'Интегралы', 'неопределённый интеграл'),
  fn('interval', 'Множества, интервалы, логика', 'числовой интервал'),
  fn('intersection', 'Множества, интервалы, логика', 'пересечение множеств'),
  fn('int', 'Служебное', 'целая часть числа'),
  fn('dsolve', 'ОДУ', 'решение дифференциального уравнения'),
  fn('BesselJ', 'Спецфункции', 'функция Бесселя первого рода'),
  fn('sin', 'Арифметика и элементарные функции', 'синус'),
]

describe('rankMatches', () => {
  it('короче двух букв — пустой список', () => {
    expect(rankMatches(LIST, 'i')).toEqual([])
    expect(rankMatches(LIST, '')).toEqual([])
  })

  it('«int» — интегралы впереди, служебное int последним', () => {
    const names = rankMatches(LIST, 'int').map((f) => f.name)
    expect(names.slice(0, 2)).toEqual(['integrate', 'interval', 'intersection'].slice(0, 2))
    expect(names[names.length - 1]).toBe('int')
  })

  it('«dso» находит dsolve', () => {
    expect(rankMatches(LIST, 'dso')[0]?.name).toBe('dsolve')
  })

  it('«bes» находит BesselJ по вхождению', () => {
    expect(rankMatches(LIST, 'bes').map((f) => f.name)).toContain('BesselJ')
  })

  it('регистр не важен', () => {
    expect(rankMatches(LIST, 'BES').map((f) => f.name)).toContain('BesselJ')
  })

  it('лимит соблюдается', () => {
    expect(rankMatches(LIST, 'in', 2)).toHaveLength(2)
  })
})

describe('filterFunctions', () => {
  it('пустой запрос возвращает весь каталог (копию)', () => {
    const out = filterFunctions(LIST, '   ')
    expect(out).toHaveLength(LIST.length)
    expect(out).not.toBe(LIST)
  })

  it('ищет по описанию и по теме', () => {
    expect(filterFunctions(LIST, 'бесселя').map((f) => f.name)).toEqual(['BesselJ'])
    expect(filterFunctions(LIST, 'интегралы').map((f) => f.name)).toEqual(['integrate'])
  })

  it('ищет по сигнатуре', () => {
    expect(filterFunctions(LIST, 'dsolve(x)').map((f) => f.name)).toEqual(['dsolve'])
  })
})

describe('groupByTopic', () => {
  it('группы идут в порядке каталога', () => {
    const groups = groupByTopic(LIST)
    expect(groups[0]?.topic).toBe('Интегралы')
    expect(groups.find((g) => g.topic === 'Множества, интервалы, логика')?.list).toHaveLength(2)
  })

  it('пустая тема попадает в «прочее»', () => {
    const groups = groupByTopic([fn('x2', '')])
    expect(groups[0]?.topic).toBe('прочее')
  })
})

describe('latexTemplate', () => {
  it('известная функция — своя запись с местом ввода', () => {
    expect(latexTemplate(fn('sin'))).toBe('\\sin\\left(\\placeholder{}\\right)')
  })

  it('sqrt получает скобки, abs — свои штрихи без скобок', () => {
    expect(latexTemplate(fn('sqrt'))).toBe('\\sqrt\\left(\\placeholder{}\\right)')
    expect(latexTemplate(fn('abs'))).toBe('\\left|\\placeholder{}\\right|')
  })

  it('неизвестная функция — operatorname', () => {
    expect(latexTemplate(fn('dsolve'))).toBe('\\operatorname{dsolve}\\left(\\placeholder{}\\right)')
  })

  it('ln печатается как \\ln', () => {
    expect(latexTemplate(fn('ln'))).toBe('\\ln\\left(\\placeholder{}\\right)')
  })
})
