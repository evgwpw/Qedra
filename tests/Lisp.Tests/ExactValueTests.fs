// Тесты Шага 21c: точные значения функций, exp-степени, вынос корней из рациональных чисел (Simplify.fs)
module ExactValueTests

open Xunit
open Reader
open Numeric
open Simplify
open Order

// входное выражение → упрощённое; ожидаемое задано каноническим S-выражением
let check (input: string) (expected: string) =
    let got = readAll input |> List.head |> simplify
    let exp = readAll expected |> List.head
    Assert.True(structEqual got exp, $"{input}: получено {Printer.prettyPrint got}, ожидалось {expected}")

// --- exp / log ---

[<Fact>]
let ``exp(0) = 1`` () = check "(exp 0)" "1"

[<Fact>]
let ``log(1) = 0`` () = check "(log 1)" "0"

[<Fact>]
let ``log(exp(1)) = 1`` () = check "(log (exp 1))" "1"

[<Fact>]
let ``log(exp(3)) = 3`` () = check "(log (exp 3))" "3"

[<Fact>]
let ``log(0) не трогается`` () = check "(log 0)" "(log 0)"

// --- гиперболические и обратные ---

[<Fact>]
let ``sinh, tanh, asin, atan, asinh, atanh от 0 дают 0`` () =
    for f in [ "sinh"; "tanh"; "asin"; "atan"; "asinh"; "atanh" ] do
        check $"({f} 0)" "0"

[<Fact>]
let ``cosh(0) = 1`` () = check "(cosh 0)" "1"

[<Fact>]
let ``acos(0) = pi/2, acos(1) = 0, acos(-1) = pi`` () =
    check "(acos 0)" "(* 1/2 pi)"
    check "(acos 1)" "0"
    check "(acos -1)" "pi"

[<Fact>]
let ``atan(1) = pi/4, atan(-1) = -pi/4`` () =
    check "(atan 1)" "(* 1/4 pi)"
    check "(atan -1)" "(* -1/4 pi)"

[<Fact>]
let ``asin(1) = pi/2`` () = check "(asin 1)" "(* 1/2 pi)"

[<Fact>]
let ``табличные значения не от нуля и единицы не трогаются`` () =
    check "(asin 2)" "(asin 2)"
    check "(atan 2)" "(atan 2)"

// --- тригонометрия от кратных pi ---

[<Fact>]
let ``sin и cos от pi`` () =
    check "(sin pi)" "0"
    check "(cos pi)" "-1"

[<Fact>]
let ``sin и cos от pi/2, pi/3, pi/6`` () =
    check "(sin (* 1/2 pi))" "1"
    check "(cos (* 1/2 pi))" "0"
    check "(sin (* 1/6 pi))" "1/2"
    check "(cos (* 1/3 pi))" "1/2"
    check "(sin (* 1/3 pi))" "(* 1/2 (^ 3 1/2))"
    check "(cos (* 1/6 pi))" "(* 1/2 (^ 3 1/2))"

[<Fact>]
let ``sin и cos от pi/4`` () =
    check "(sin (* 1/4 pi))" "(* 1/2 (^ 2 1/2))"
    check "(cos (* 1/4 pi))" "(* 1/2 (^ 2 1/2))"

[<Fact>]
let ``приведение по периоду и знаку`` () =
    check "(sin (* 7/6 pi))" "-1/2"
    check "(cos (* 2/3 pi))" "-1/2"
    check "(sin (* 13/6 pi))" "1/2"
    check "(cos (* -1/3 pi))" "1/2"
    check "(sin (* -1/4 pi))" "(* -1/2 (^ 2 1/2))"
    check "(cos (* 7/4 pi))" "(* 1/2 (^ 2 1/2))"
    check "(sin (* 3/2 pi))" "-1"
    check "(cos (* 100 pi))" "1"

[<Fact>]
let ``tan, cot, sec, csc`` () =
    check "(tan (* 1/4 pi))" "1"
    check "(tan (* 1/3 pi))" "(^ 3 1/2)"
    check "(tan (* 1/6 pi))" "(* 1/3 (^ 3 1/2))"
    check "(cot (* 1/4 pi))" "1"
    check "(cot (* 5/6 pi))" "(* -1 (^ 3 1/2))"
    check "(sec (* 1/3 pi))" "2"
    check "(csc (* 1/6 pi))" "2"
    check "(sec (* 1/4 pi))" "(^ 2 1/2)"

[<Fact>]
let ``tan(0) = 0`` () = check "(tan 0)" "0"

[<Fact>]
let ``полюса не вычисляются`` () =
    // tan = sin/cos в каноническом виде; деление на ноль остаётся формой (^ 0 -1), как и раньше
    check "(tan (* 1/2 pi))" "(^ 0 -1)"
    check "(cot 0)" "(^ 0 -1)"

[<Fact>]
let ``нерациональные кратные pi и числа не трогаются`` () =
    check "(sin 1)" "(sin 1)"
    check "(sin (* 1/5 pi))" "(sin (* 1/5 pi))"
    check "(cos (* 1/12 pi))" "(cos (* 1/12 pi))"
    check "(sin (* n pi))" "(sin (* n pi))"

// --- exp-степени ---

[<Fact>]
let ``(exp u)^n = exp(n u)`` () =
    check "(^ (exp x) 2)" "(exp (* 2 x))"
    check "(^ (exp x) 3)" "(exp (* 3 x))"

[<Fact>]
let ``1/exp(u) = exp(-u)`` () =
    check "(/ 1 (exp x))" "(exp (* -1 x))"
    check "(^ (exp x) -1)" "(exp (* -1 x))"

[<Fact>]
let ``exp(a) exp(b) = exp(a+b)`` () =
    check "(* (exp x) (exp y))" "(exp (+ x y))"
    check "(* (exp x) (exp x))" "(exp (* 2 x))"
    check "(* (exp x) (exp (* -1 x)))" "1"

[<Fact>]
let ``нецелая степень exp не сливается`` () =
    check "(^ (exp x) 1/2)" "(^ (exp x) 1/2)"

// --- корни из рациональных чисел ---

[<Fact>]
let ``вынос квадратов`` () =
    check "(^ 8 1/2)" "(* 2 (^ 2 1/2))"
    check "(^ 12 1/2)" "(* 2 (^ 3 1/2))"
    check "(^ 72 1/2)" "(* 6 (^ 2 1/2))"
    check "(sqrt 8)" "(* 2 (^ 2 1/2))"

[<Fact>]
let ``точные корни`` () =
    check "(^ 16 1/4)" "2"
    check "(^ 27 1/3)" "3"
    check "(sqrt 1)" "1"
    check "(sqrt 1/4)" "1/2"

[<Fact>]
let ``знаменатель рационализируется`` () =
    check "(^ 1/2 1/2)" "(* 1/2 (^ 2 1/2))"
    check "(^ 2 -1/2)" "(* 1/2 (^ 2 1/2))"
    check "(^ 1/3 1/2)" "(* 1/3 (^ 3 1/2))"
    check "(^ 1/8 1/2)" "(* 1/4 (^ 2 1/2))"

[<Fact>]
let ``показатель больше 1 и корни высших степеней`` () =
    check "(^ 2 3/2)" "(* 2 (^ 2 1/2))"
    check "(^ 16 1/3)" "(* 2 (^ 2 1/3))"
    check "(^ 4 1/4)" "(^ 2 1/2)"
    check "(^ 8 1/6)" "(^ 2 1/2)"

[<Fact>]
let ``несводимый корень не меняется`` () =
    check "(^ 2 1/2)" "(^ 2 1/2)"
    check "(^ 6 1/3)" "(^ 6 1/3)"

[<Fact>]
let ``отрицательные основания через мнимую единицу`` () =
    check "(sqrt -4)" "(* 2 %i)"
    check "(^ -8 1/2)" "(* 2 (^ 2 1/2) %i)"
    check "(sqrt -2)" "(* (^ 2 1/2) %i)"

[<Fact>]
let ``большие числа под корнем не раскладываются`` () =
    check "(^ 1000000000000000000000007 1/2)" "(^ 1000000000000000000000007 1/2)"
    check "(^ 999999999989 1/2)" "(^ 999999999989 1/2)"

[<Fact>]
let ``нуль в положительной дробной степени`` () =
    check "(^ 0 1/2)" "0"
    check "(sqrt 0)" "0"
    check "(^ 0 -1/2)" "(^ 0 -1/2)"

[<Fact>]
let ``идемпотентность`` () =
    for s in [ "(^ 8 1/2)"; "(^ 2 3/2)"; "(^ 1/2 1/2)"; "(sin (* 1/6 pi))"; "(* (exp x) (exp y))" ] do
        let once = readAll s |> List.head |> simplify
        Assert.True(structEqual once (simplify once), s)
