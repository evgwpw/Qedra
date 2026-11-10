// WASM.3c/WASM.4a: типы записи шага — формат собирает web/app/steps.lisp (app-step-json),
// поля совпадают с записью шага в lib/steps.lisp: (rule title comment before after level children omitted).
import type { TreeData } from 'bso5-components'

export interface StepRecord {
  rule: string
  title: string
  comment: string
  before_latex: string
  before_text: string
  after_latex: string
  after_text: string
  children?: StepRecord[]
}

export interface StepsJson {
  steps?: StepRecord[]
}

/** узел дерева шагов: TreeData плюс сама запись шага (нужна renderLabel) */
export interface StepNode extends TreeData {
  step?: StepRecord
  children?: StepNode[] | null
}
