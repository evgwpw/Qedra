// Тесты Шага 14: объекты, векторы, property list, иерархия типов, методы и диспетчеризация
// Таблицы свойств и методов глобальны (как и globalEnv), поэтому в каждом тесте — свои имена типов
// (параллелизм тестовых коллекций отключён в xunit.runner.json)
module ObjectTests

open Xunit
open Types
open Reader
open Evaluator
open Printer

let ev (s: string) : LispValue = evalAll (readAll s) globalEnv
let simp (v: LispValue) : LispValue = Simplify.simplify v
let sexpr (s: string) : LispValue = readAll s |> List.head
let shows (expected: string) (v: LispValue) = Assert.Equal(expected, prettyPrint v)
let obj (t: string) (fields: LispValue list) = LispObject { Type = t; Fields = Array.ofList fields }
let sym (s: string) = LispSym s
let int' (n: int) = LispInteger (bigint n)
let call (op: string) (args: LispValue list) = LispList (LispSym op :: args)

// Демонстрационный тип modint — вычет по модулю (код на Lisp)
let private setup =
    lazy (
        ev """
(define (mk v m) (make-object 'modint (mod v m) m))
(defmethod + (modint modint) (a b) (mk (+ (object-ref a 0) (object-ref b 0)) (object-ref a 1)))
(defmethod * (modint modint) (a b) (mk (* (object-ref a 0) (object-ref b 0)) (object-ref a 1)))
(defmethod * (integer modint) (k b) (mk (* k (object-ref b 0)) (object-ref b 1)))
(defmethod + (integer modint) (k b) (mk (+ k (object-ref b 0)) (object-ref b 1)))
(defmethod print (modint) (a)
  (string-append (to-string (object-ref a 0)) " (mod " (to-string (object-ref a 1)) ")"))
""" |> ignore)

let private init () = setup.Force()

// --- type-of ---

[<Fact>]
let ``type-of встроенных видов`` () =
    init ()
    shows "integer" (ev "(type-of 1)")
    shows "rational" (ev "(type-of 1/2)")
    shows "float" (ev "(type-of 1.5)")
    shows "symbol" (ev "(type-of 'x)")
    shows "string" (ev "(type-of \"s\")")
    shows "bool" (ev "(type-of #t)")
    shows "nil" (ev "(type-of (quote ()))")
    shows "function" (ev "(type-of (lambda (x) x))")
    shows "function" (ev "(type-of car)")
    shows "expr" (ev "(type-of '(+ x 1))")
    shows "list" (ev "(type-of '(1 2 3))")
    shows "vector" (ev "(type-of (vector 1 2))")
    shows "modint" (ev "(type-of (mk 3 7))")
    shows "algebraic" (ev "(type-of (sqrt 2))")
    Assert.Equal("complex", Objects.typeOf (LispComplex (int' 1, int' 2)))
    Assert.Equal("macro", Objects.typeOf (LispMacro { Name = "lambda"; Params = []; Body = LispNil; Env = globalEnv; Code = null; Captured = null }))

[<Fact>]
let ``иерархия типов и subtype`` () =
    init ()
    Assert.Equal<string list>([ "integer"; "rational"; "real"; "number"; "scalar"; "any" ], Objects.ancestors "integer")
    Assert.Equal<string list>([ "algebraic"; "real"; "number"; "scalar"; "any" ], Objects.ancestors "algebraic")
    Assert.Equal<string list>([ "symbol"; "scalar"; "any" ], Objects.ancestors "symbol")
    Assert.Equal<string list>([ "modint"; "any" ], Objects.ancestors "modint")
    shows "#t" (ev "(subtype? 'integer 'scalar)")
    shows "#t" (ev "(subtype? 'symbol 'scalar)")
    shows "#t" (ev "(subtype? 'modint 'any)")
    shows "#f" (ev "(subtype? 'modint 'scalar)")
    shows "#f" (ev "(subtype? 'float 'integer)")

[<Fact>]
let ``deftype с родителем и защита от циклов`` () =
    ev "(deftype 'tyA 'scalar) (deftype 'tyB 'tyA)" |> ignore
    shows "#t" (ev "(subtype? 'tyB 'scalar)")
    Assert.Equal<string list>([ "tyB"; "tyA"; "scalar"; "any" ], Objects.ancestors "tyB")
    ev "(deftype 'cyc1 'cyc2) (deftype 'cyc2 'cyc1)" |> ignore
    Assert.Equal<string list>([ "cyc1"; "cyc2" ], Objects.ancestors "cyc1")

// --- объекты ---

[<Fact>]
let ``объекты: конструктор и доступ`` () =
    init ()
    ev "(define o1 (make-object 'objT 10 20 30))" |> ignore
    shows "#t" (ev "(object? o1)")
    shows "#f" (ev "(object? 5)")
    shows "objT" (ev "(object-type o1)")
    shows "20" (ev "(object-ref o1 1)")
    shows "3" (ev "(object-count o1)")
    shows "#(10 20 30)" (ev "(object-fields o1)")
    Assert.ThrowsAny<exn>(fun () -> ev "(object-ref o1 3)" |> ignore) |> ignore
    // самовычисляем, печать по умолчанию
    shows "#<objT 10 20 30>" (ev "o1")

[<Fact>]
let ``object-fields возвращает копию`` () =
    ev "(define o2 (make-object 'objT2 1 2))" |> ignore
    ev "(vset! (object-fields o2) 0 99)" |> ignore
    shows "1" (ev "(object-ref o2 0)")

[<Fact>]
let ``structEqual объектов`` () =
    Assert.True(Numeric.structEqual (obj "q" [ int' 1; sym "a" ]) (obj "q" [ int' 1; sym "a" ]))
    Assert.False(Numeric.structEqual (obj "q" [ int' 1 ]) (obj "r" [ int' 1 ]))
    Assert.False(Numeric.structEqual (obj "q" [ int' 1 ]) (obj "q" [ int' 2 ]))
    Assert.False(Numeric.structEqual (obj "q" [ int' 1 ]) (obj "q" [ int' 1; int' 1 ]))
    shows "#t" (ev "(equal? (make-object 'q 1) (make-object 'q 1))")

// --- векторы ---

[<Fact>]
let ``векторы: конструкторы и доступ`` () =
    shows "#(1 2 3)" (ev "(vector 1 2 3)")
    shows "#(0 0 0)" (ev "(make-vector 3 0)")
    shows "#()" (ev "(vector)")
    shows "3" (ev "(vlength (vector 1 2 3))")
    shows "2" (ev "(vref (vector 1 2 3) 1)")
    shows "#t" (ev "(vector? (vector))")
    shows "#f" (ev "(vector? '(1 2))")
    shows "(1 2 3)" (ev "(vector->list (vector 1 2 3))")
    shows "#(1 2 3)" (ev "(list->vector '(1 2 3))")

[<Fact>]
let ``vset! изменяет вектор на месте`` () =
    ev "(define v1 (vector 1 2 3))" |> ignore
    shows "9" (ev "(vset! v1 0 9)")
    shows "#(9 2 3)" (ev "v1")

[<Fact>]
let ``векторы: выход за границы`` () =
    Assert.ThrowsAny<exn>(fun () -> ev "(vref (vector 1 2) 2)" |> ignore) |> ignore
    Assert.ThrowsAny<exn>(fun () -> ev "(vref (vector 1 2) -1)" |> ignore) |> ignore
    Assert.ThrowsAny<exn>(fun () -> ev "(vset! (vector 1 2) 5 0)" |> ignore) |> ignore

[<Fact>]
let ``литерал вектора и round-trip печати`` () =
    let v = readAll "#(1 (a b) #(2 x))" |> List.head
    shows "#(1 (a b) #(2 x))" v
    let back = readAll (prettyPrint v) |> List.head
    Assert.True(Numeric.structEqual v back)
    // элементы не вычисляются, сам литерал самовычисляем
    shows "#(a (+ 1 2))" (ev "#(a (+ 1 2))")
    shows "2" (ev "(vref #(1 2 3) 1)")
    Assert.True(Numeric.structEqual (LispVector [| int' 1; int' 2 |]) (LispVector [| int' 1; int' 2 |]))
    Assert.False(Numeric.structEqual (LispVector [| int' 1 |]) (LispVector [| int' 1; int' 2 |]))

// --- property list ---

[<Fact>]
let ``put и get`` () =
    shows "5" (ev "(put 'plSym 'k 5)")
    shows "5" (ev "(get 'plSym 'k)")
    shows "nil" (ev "(get 'plSym 'other)")
    shows "nil" (ev "(get 'noSuchSym 'k)")
    ev "(put 'plSym 'k 6)" |> ignore
    shows "6" (ev "(get 'plSym 'k)")

// --- prelude ---

[<Fact>]
let ``prelude.lisp загружается`` () =
    shows "#t" (ev "prelude-loaded")
    shows "#(2 4 6)" (ev "(vector-map (lambda (x) (* 2 x)) (vector 1 2 3))")

// --- методы и диспетчеризация ---

[<Fact>]
let ``defmethod: сложение и умножение modint`` () =
    init ()
    shows "5 (mod 7)" (ev "(+ (mk 3 7) (mk 2 7))")
    shows "1 (mod 7)" (ev "(+ (mk 3 7) (mk 5 7))")
    shows "6 (mod 7)" (ev "(* (mk 3 7) (mk 2 7))")
    shows "5 (mod 7)" (ev "(* 3 (mk 4 7))")
    // через simplify
    shows "1 (mod 7)" (ev "(simplify (list '+ (mk 3 7) (mk 5 7)))")
    // n-арная сумма сворачивается попарно
    shows "6 (mod 7)" (ev "(+ (mk 1 7) (mk 2 7) (mk 3 7))")
    // арифметика над числами не затронута
    shows "5" (ev "(+ 2 3)")

[<Fact>]
let ``скаляр + объект через метод`` () =
    init ()
    shows "5 (mod 7)" (ev "(+ 2 (mk 3 7))")
    shows "5 (mod 7)" (ev "(+ (mk 3 7) 2)")

[<Fact>]
let ``наследование методов: scalar применяется к integer и symbol`` () =
    ev "(defmethod + (scalar inhT) (s o) 'ok)" |> ignore
    let o = obj "inhT" [ int' 1 ]
    shows "ok" (simp (call "+" [ int' 5; o ]))
    shows "ok" (simp (call "+" [ sym "x"; o ]))
    shows "ok" (simp (call "+" [ LispFloat 1.5; o ]))

[<Fact>]
let ``более специфичный метод побеждает общий`` () =
    ev "(defmethod + (scalar spT) (a b) 'general) (defmethod + (integer spT) (a b) 'specific)" |> ignore
    let o = obj "spT" []
    shows "specific" (simp (call "+" [ int' 1; o ]))
    shows "general" (simp (call "+" [ sym "x"; o ]))
    shows "general" (simp (call "+" [ LispFloat 1.0; o ]))

[<Fact>]
let ``find-method и add-method`` () =
    ev "(add-method 'frob '(fmT) (lambda (a) 42))" |> ignore
    shows "#<функция frob(fmT)>" (ev "(find-method 'frob '(fmT))")
    shows "nil" (ev "(find-method 'frob '(zzz))")
    Assert.True(Numeric.structEqual (int' 42) (Objects.tryDispatch "frob" [ obj "fmT" [] ] [ obj "fmT" [] ]).Value)

[<Fact>]
let ``прочие операторы: диспетчеризация по всем аргументам`` () =
    ev "(defmethod frob2 (f2T integer) (o n) (+ n 100))" |> ignore
    let o = obj "f2T" []
    Assert.True(Numeric.structEqual (int' 105) (simp (call "frob2" [ o; int' 5 ])))
    // нет метода — символьная форма
    shows "(frob2 #<f2T> x)" (simp (call "frob2" [ o; sym "x" ]))

// --- нет метода: CAS-принцип ---

[<Fact>]
let ``нет метода: символьная форма, идемпотентность`` () =
    let a, b = obj "nmT" [ int' 1 ], obj "nmT" [ int' 2 ]
    let s = simp (call "+" [ a; b; sym "x"; int' 3 ])
    shows "(+ 3 x #<nmT 1> #<nmT 2>)" s
    Assert.True(Numeric.structEqual s (simp s))
    let p = simp (call "*" [ int' 2; a; b ])
    shows "(* 2 #<nmT 1> #<nmT 2>)" p
    Assert.True(Numeric.structEqual p (simp p))
    let w = simp (call "^" [ a; int' 2 ])
    shows "(^ #<nmT 1> 2)" w
    Assert.True(Numeric.structEqual w (simp w))

[<Fact>]
let ``A + (-1)*A = 0 для объекта без методов`` () =
    let a = obj "nm2T" [ sym "q" ]
    Assert.True(Numeric.structEqual (int' 0) (simp (call "+" [ a; call "*" [ int' -1; a ] ])))
    Assert.True(Numeric.structEqual (int' 0) (simp (call "-" [ a; a ])))
    shows "(* 2 #<nm2T q>)" (simp (call "+" [ a; a ]))

// --- некоммутативность ---

[<Fact>]
let ``некоммутативные объекты: порядок сохраняется`` () =
    let a, b = obj "ncT" [ sym "a" ], obj "ncT" [ sym "b" ]
    let ab = simp (call "*" [ a; b ])
    let ba = simp (call "*" [ b; a ])
    Assert.False(Numeric.structEqual ab ba)
    shows "(* #<ncT a> #<ncT b>)" ab
    shows "(* #<ncT b> #<ncT a>)" ba
    // коммутативные множители выносятся вперёд
    shows "(* 2 x #<ncT a> #<ncT b>)" (simp (call "*" [ a; int' 2; b; sym "x" ]))

[<Fact>]
let ``некоммутативные объекты сворачиваются по методу слева направо`` () =
    ev "(defmethod * (catT catT) (a b) (make-object 'catT (object-ref a 0) (object-ref b 0)))" |> ignore
    let c n = obj "catT" [ sym n ]
    shows "#<catT a b>" (simp (call "*" [ c "a"; c "b" ]))
    shows "#<catT b a>" (simp (call "*" [ c "b"; c "a" ]))
    // три множителя: (a b) -> catT с полем a, затем (a c)
    shows "#<catT a c>" (simp (call "*" [ c "a"; c "b"; c "c" ]))
    // соседи через коммутативный множитель
    shows "(* 2 #<catT a b>)" (simp (call "*" [ c "a"; int' 2; c "b" ]))

[<Fact>]
let ``коммутативный тип: множители сортируются`` () =
    ev "(put 'cmT 'commutative #t)" |> ignore
    let a, b = obj "cmT" [ sym "a" ], obj "cmT" [ sym "b" ]
    let ab = simp (call "*" [ a; b ])
    let ba = simp (call "*" [ b; a ])
    Assert.True(Numeric.structEqual ab ba)
    shows "(* #<cmT a> #<cmT b>)" ba
    // и степени собираются
    shows "(^ #<cmT a> 2)" (simp (call "*" [ a; a ]))

[<Fact>]
let ``скаляр * объект через метод scalar`` () =
    ev "(defmethod * (scalar sclT) (k o) (make-object 'sclT (simplify (list '* k (object-ref o 0)))))" |> ignore
    let o = obj "sclT" [ sym "v" ]
    shows "#<sclT (* 2 v)>" (simp (call "*" [ int' 2; o ]))
    shows "#<sclT (* v x)>" (simp (call "*" [ sym "x"; o ]))
    shows "#<sclT (* 6 v x)>" (simp (call "*" [ int' 2; sym "x"; int' 3; o ]))

[<Fact>]
let ``степень объекта: метод или символьно`` () =
    ev "(defmethod ^ (powT integer) (o n) (make-object 'powT n))" |> ignore
    shows "#<powT 3>" (simp (call "^" [ obj "powT" []; int' 3 ]))
    shows "(^ #<powT> x)" (simp (call "^" [ obj "powT" []; sym "x" ]))

[<Fact>]
let ``упорядочение: объекты после составных выражений`` () =
    let o = obj "ordT" [ int' 1 ]
    let comp = sexpr "(sin x)"
    Assert.True(Order.orderp comp o)
    Assert.False(Order.orderp o comp)
    Assert.True(Order.orderp (obj "ordT" [ int' 1 ]) (obj "ordT" [ int' 2 ]))
    Assert.True(Order.orderp (obj "aaT" [ int' 9 ]) (obj "ordT" [ int' 1 ]))
    shows "(+ (sin x) #<ordT 1>)" (simp (call "+" [ o; comp ]))

[<Fact>]
let ``simplify вектора поэлементный, метод simplify объекта`` () =
    let v = LispVector [| sexpr "(+ x x)"; sexpr "(* 1 y)" |]
    shows "#((* 2 x) y)" (simp v)
    ev "(defmethod simplify (smpT) (o) 'simplified)" |> ignore
    shows "simplified" (simp (obj "smpT" []))

// --- печать ---

[<Fact>]
let ``метод print используется prettyPrint и math-print`` () =
    init ()
    shows "3 (mod 7)" (ev "(mk 3 7)")
    Assert.Equal("3 (mod 7)", MathPrinter.mathPrint (ev "(mk 3 7)"))
    shows "(f 3 (mod 7))" (call "f" [ ev "(mk 3 7)" ])
    Assert.Equal("x + 3 (mod 7)", MathPrinter.mathPrint (simp (call "+" [ ev "(mk 3 7)"; sym "x" ])))

[<Fact>]
let ``метод math-print`` () =
    ev "(defmethod math-print (mpT) (o) \"<<mp>>\")" |> ignore
    let o = obj "mpT" [ int' 1 ]
    Assert.Equal("<<mp>>", MathPrinter.mathPrint o)
    Assert.Equal("x + <<mp>>", MathPrinter.mathPrint (simp (call "+" [ o; sym "x" ])))
    shows "#<mpT 1>" o

// --- diff / integrate ---

[<Fact>]
let ``diff по объекту через метод`` () =
    ev "(defmethod diff (dwT) (o x) (make-object 'dwT (diff x (object-ref o 0))))" |> ignore
    shows "#<dwT (* 2 x)>" (ev "(diff 'x (make-object 'dwT '(^ x 2)))")
    // внутри выражения
    shows "(* 3 #<dwT 1>)" (ev "(diff 'x (list '* 3 (make-object 'dwT 'x)))")

[<Fact>]
let ``diff без метода остаётся символьным, вектор - поэлементно`` () =
    let o = obj "dnT" [ int' 1 ]
    shows "(diff #<dnT 1> x)" (Differentiate.diff "x" o)
    shows "#(1 0 (* 2 x))" (Differentiate.diff "x" (LispVector [| sym "x"; sym "y"; sexpr "(^ x 2)" |]))

[<Fact>]
let ``integrate по объекту: метод или ошибка`` () =
    ev "(defmethod integrate (inT) (o x) 'integrated)" |> ignore
    shows "integrated" (IntegrateTests.integrate "x" (obj "inT" []))
    // Шаг 19: нет метода — невычисленная форма (раньше была ошибка «не умею»)
    shows "(integrate #<inNoT> x)" (IntegrateTests.integrate "x" (obj "inNoT" []))
