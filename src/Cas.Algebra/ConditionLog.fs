// Канал условий применимости ответа (подшаг 22.2): «ответ верен при a ≠ 0», «интеграл — при a > 0».
// В отличие от журнала шагов (StepLog) всегда включён и дёшев: запись — поиск ключа в небольшом списке.
// Список условий — по потокам (ThreadStatic); интерпретатор Lisp однопоточный, алгебра тестируется параллельно.
// Условие — произвольное значение (obj; в Lisp.Core — выражение LispValue, каноническая форма (/= c 0), (> c 0) ...);
// дубликаты определяются ключом (текстом условия), заданным вызывающим кодом; при дубликате остаётся первая причина.
module ConditionLog

open System

type Condition =
    { Key: string
      Condition: obj
      Reason: string }

[<Sealed; AbstractClass>]
type Conditions private () =
    [<ThreadStatic; DefaultValue>]
    static val mutable private items : ResizeArray<Condition>

    // Записать условие; false — такое уже есть
    static member Record(key: string, condition: obj, reason: string) : bool =
        if isNull Conditions.items then Conditions.items <- ResizeArray<Condition>()
        if Conditions.items.Exists(fun c -> c.Key = key) then false
        else
            Conditions.items.Add { Key = key; Condition = condition; Reason = reason }
            true

    // Записанные условия текущего потока по порядку
    static member All : Condition list =
        if isNull Conditions.items then [] else List.ofSeq Conditions.items

    static member Clear() : unit =
        if not (isNull Conditions.items) then Conditions.items.Clear()

    // Выполнить f с чистым каналом; вернуть результат и условия; прежний список восстанавливается
    // (условия внутри захвата во внешний канал не попадают — как у StepLog.Journal.Capture)
    static member Capture(f: unit -> 'a) : 'a * Condition list =
        let saved = Conditions.items
        Conditions.items <- ResizeArray<Condition>()
        try
            let r = f ()
            r, List.ofSeq Conditions.items
        finally
            Conditions.items <- saved
