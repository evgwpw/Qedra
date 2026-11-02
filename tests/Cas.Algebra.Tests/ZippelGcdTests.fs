// Тесты шага 21g: проба одной точкой (взаимная простота, граница степени), разреженный модулярный НОД Зиппеля
module ZippelGcdTests

open System
open System.Numerics
open Xunit
open MPoly
open PolyGcd
open ModGcd
open Zippel

let private vv (i: int) = var i
let private c (n: int) = ofInt (BigInteger n)
let private sum (xs: MPoly list) = List.fold add zero xs
let private prod (xs: MPoly list) = List.fold mul one xs

// Случайный многочлен от переменных 0..nv-1: заданное число термов, степени до maxDeg, коэффициенты до maxCoef
let private randPoly (rnd: Random) (nv: int) (terms: int) (maxDeg: int) (maxCoef: int) : MPoly =
    let mutable r = zero
    for _ in 1 .. terms do
        let mutable t = c (rnd.Next(1, maxCoef + 1) * (if rnd.Next 2 = 0 then 1 else -1))
        for i in 0 .. nv - 1 do
            let d = rnd.Next(0, maxDeg + 1)
            if d > 0 then t <- mul t (pow (vv i) d)
        r <- add r t
    r

// Бенчмарки Фейтмана (эталонные многочлены): n + 1 переменных, y0 — главная (наибольший номер)
let private fateman (n: int) : MPoly[] =
    let y i = vv (n - i)
    let ys = [ for i in 1 .. n -> y i ]
    let y0 = y 0
    let u = add y0 (sum ys)          // u = y_0 + y_1 + … + y_n
    let v = add (pow y0 2) (sum (ys |> List.map (fun q -> pow q 2)))
    let f1 = mul (add u (c 1)) (add u (c 2))
    let g1 = mul (add v (c 1)) (sub (add (mul (c -3) (mul (y 1) (pow y0 2))) (pow (y 1) 2)) (c 1))
    [| f1; g1 |]

let private fateman2 (n: int) : MPoly * MPoly * MPoly =
    let y i = vv (n - i)
    let u = sum [ for i in 1 .. n -> y i ]
    let y0 = y 0
    let h = pow (sum [ y0; u; c 1 ]) 2
    let f = pow (sub (sub y0 u) (c 2)) 2
    let g = pow (sum [ y0; u; c 2 ]) 2
    (mul h f, mul h g, h)

let private fateman3 (n: int) : MPoly * MPoly * MPoly =
    let y i = vv (n - i)
    let u = sum [ for i in 1 .. n -> pow (y i) (n + 1) ]
    let y0 = pow (y 0) (n + 1)
    let h = pow (sum [ y0; u; c 1 ]) 2
    let f = pow (sub (sub y0 u) (c 2)) 2
    let g = pow (sum [ y0; u; c 2 ]) 2
    (mul h f, mul h g, h)

let private primPart (a: MPoly) = divExactExn a (contentMain a)

// ---------- проба одной точкой ----------

[<Fact>]
let ``проба одной точки: Фейтман F_1 (взаимно просты) — доказательство, НОД = 1 без рекурсии`` () =
    for n in 1 .. 4 do
        let fg = fateman n
        Assert.Equal(Some 0, probeGcdDegree (primPart fg.[0]) (primPart fg.[1]) 7UL 3)
    // и через модулярный путь: счётчик доказанных проб растёт, результат 1
    let fg = fateman 3
    // primPart сам вызывает gcd (содержание) и тоже делает пробы — считаем счётчик после него
    let pf, pg = primPart fg.[0], primPart fg.[1]
    let before = (probeStats ()).[1]
    Assert.Equal(Some one, tryModularPrimitiveGcd pf pg)
    Assert.Equal(before + 1, (probeStats ()).[1])

[<Fact>]
let ``проба одной точки: общий множитель — граница степени не ниже истинной (Фейтман F_2, F_3)`` () =
    for n in 1 .. 3 do
        let f, g, h = fateman2 n
        match probeGcdDegree f g 5UL 3 with
        | Some d -> Assert.True(d >= degMain h && d <= degMain h + 0, sprintf "F_2 n=%d: %d" n d)
        | None -> failwith "точка не найдена"
        let f, g, h = fateman3 n
        match probeGcdDegree f g 5UL 3 with
        | Some d -> Assert.Equal(degMain h, d)
        | None -> failwith "точка не найдена"

[<Fact; Trait("Category", "Slow")>]
let ``проба одной точки: случайные пары — граница >= истинной степени, ноль только при взаимной простоте`` () =
    let rnd = Random 2101
    let mutable zeros = 0
    for i in 1 .. 80 do
        let nv = 2 + i % 3
        let g = if i % 2 = 0 then randPoly rnd nv 3 3 9 else one
        let a = mul g (randPoly rnd nv 4 3 9)
        let b = mul g (randPoly rnd nv 4 3 9)
        if mainVar a = nv - 1 && mainVar b = nv - 1 && not (isZero a) && not (isZero b) then
            let pa, pb = primPart a, primPart b
            let truth = degIn (nv - 1) (gcdPrs pa pb)
            match probeGcdDegree pa pb (uint64 i) 3 with
            | Some d ->
                Assert.True(d >= truth, sprintf "пара %d: граница %d < степени НОД %d" i d truth)
                if d = 0 then zeros <- zeros + 1
            | None -> ()
    Assert.True(zeros > 0)

[<Fact>]
let ``проба одной точки: невезучая точка не даёт ложного нуля (x^2-y, x^2-2y+1 — НОД 1)`` () =
    // y = 1 — единственная плохая точка (оба образа x^2-1); при случайной точке проба доказывает НОД 1
    let x, y = vv 1, vv 0
    let f = sub (pow x 2) y
    let g = add (sub (pow x 2) (mul (c 2) y)) (c 1)
    Assert.Equal(Some 0, probeGcdDegree f g 3UL 3)
    Assert.Equal(c 1, gcd f g)

// ---------- LINZIP (de Kleine–Monagan–Wittkopf, ISSAC 2005) ----------

let private P31 = 2147483647L

let rec private modPoly (p: BigInteger) (m: MPoly) : MPoly =
    match m with
    | Const (n, _) -> ofInt (((n % p) + p) % p)
    | Poly (v, cs) -> mk v (Array.map (modPoly p) cs)

// Масштабирование по модулю p так, чтобы старший (лексикографически) коэффициент стал равен target
let private scaleLeadTo (p: int64) (target: int) (m: MPoly) : MPoly =
    let bp = BigInteger p
    let lead = fst (leadConst m)
    let inv = BigInteger.ModPow (lead, bp - 2I, bp)
    modPoly bp (mulConst (BigInteger target * inv, 1I) m)

let private zs () = Array.copy (zippelStats ())

[<Fact>]
let ``Вандермонд (KaLa88): транспонированная система решается, дубли значений отвергаются`` () =
    let p = P31
    let rnd = Random 5
    let mulm (a: int64) (b: int64) = a * b % p
    for n in 1 .. 8 do
        let v = Array.zeroCreate<int64> n
        let mutable k = 0
        while k < n do
            let c0 = int64 (rnd.Next(1, Int32.MaxValue))
            if not (Array.exists (fun q -> q = c0) (Array.sub v 0 k)) then
                v.[k] <- c0
                k <- k + 1
        let cs = Array.init n (fun _ -> int64 (rnd.Next(0, Int32.MaxValue)))
        let w =
            Array.init n (fun j ->
                let mutable s = 0L
                for t in 0 .. n - 1 do
                    let mutable pw = 1L
                    for _ in 0 .. j do pw <- mulm pw v.[t]
                    s <- (s + mulm cs.[t] pw) % p
                s)
        match vandermondeSolve p v w with
        | Some c -> Assert.Equal<int64[]>(cs, c)
        | None -> failwithf "n=%d: система не решена" n
    // совпавшие значения: матрица вырождена
    Assert.True((vandermondeSolve p [| 5L; 5L |] [| 1L; 2L |]).IsNone)

// Example 1: G = (y+50)x³ + 100y, A = (x−y+1)G, B = (x+y+1)G (главная переменная x — номер 1)
let private example1 () =
    let x, y = vv 1, vv 0
    let g = add (mul (add y (c 50)) (pow x 3)) (mul (c 100) y)
    (x, y, g, mul (add (sub x y) (c 1)) g, mul (add (add x y) (c 1)) g)

[<Fact>]
let ``LINZIP Example 1: single scaling, образ по модулю 17 — (8y+9)x³+y из статьи`` () =
    let x, y, g, a, b = example1 ()
    // первый образ по модулю 13: G1 = (y+11)x³ + 9y — форма
    let form13 = add (mul (add y (c 11)) (pow x 3)) (mul (c 9) y)
    Assert.Equal(modPoly 13I g, form13)
    // масштабный терм 9y — одночлен: single scaling, nx = 2 (в блоке x³ два терма)
    Assert.Equal((2, true), zippelFormInfo form13)
    // ровно как в статье (nx образов, без проверочного): образ в нормировке «коэффициент масштабного терма = 1»
    let tag, img = zippelImage 17L a b form13 3 -1 0 11UL
    Assert.Equal("ok", tag)
    Assert.Equal(add (mul (add (mul (c 8) y) (c 9)) (pow x 3)) y, img)
    // с проверочным образом (рабочий режим) — тот же результат
    let tag2, img2 = zippelImage 17L a b form13 3 -1 1 12UL
    Assert.Equal("ok", tag2)
    Assert.Equal(img, img2)
    // после нормировки шага 5.7 (старший коэффициент γ = 1) — второй образ G2 = (y+16)x³ + 15y из статьи
    Assert.Equal(add (mul (add y (c 16)) (pow x 3)) (mul (c 15) y), scaleLeadTo 17L 1 img)

[<Fact>]
let ``LINZIP Example 1: P по модулю 13 даёт G1 из статьи, M — НОД над Z`` () =
    let x, y, g, a, b = example1 ()
    match zippelPrimeGcd 13L a b 3 7UL with
    | Some r -> Assert.Equal(modPoly 13I g, scaleLeadTo 13L 1 r)
    | None -> failwith "P отказал"
    let before = zs ()
    Assert.Equal(Some g, tryZippelGcd a b 3UL)
    let after = zs ()
    Assert.Equal(before.[1] + 1, after.[1])   // успех зафиксирован счётчиком

// Example 2: G = (3y²−90)x³ + 12y + 100 — multiple scaling (нет коэффициента-монома)
let private example2 () =
    let x, y = vv 1, vv 0
    let g = add (mul (sub (mul (c 3) (pow y 2)) (c 90)) (pow x 3)) (add (mul (c 12) y) (c 100))
    (x, y, g, mul (add (add x y) (c 1)) g, mul (add (sub x y) (c 2)) g)

[<Fact>]
let ``LINZIP Example 2: multiple scaling, nx = 3, образ по модулю 17 — 7x³y²+11x³+11y+1 из статьи`` () =
    let x, y, g, a, b = example2 ()
    let form13 = add (add (mul (pow y 2) (pow x 3)) (mul (c 9) (pow x 3))) (add (mul (c 4) y) (c 3))
    Assert.Equal(scaleLeadTo 13L 1 (modPoly 13I g), form13)    // g ≡ x³y² + 9x³ + 4y + 3 (mod 13)
    Assert.Equal((3, false), zippelFormInfo form13)            // «compute three» univariate images
    let before = zs ()
    let tag, img = zippelImage 17L a b form13 3 -1 0 21UL
    Assert.Equal("ok", tag)
    Assert.Equal(before.[12] + 3, (zs ()).[12])
    // масштабы m1 = 1: образ с точностью до константы; в нормировке старшего коэффициента 7 — образ из статьи
    let expected =
        add (add (mul (mul (c 7) (pow y 2)) (pow x 3)) (mul (c 11) (pow x 3))) (add (mul (c 11) y) (c 1))
    Assert.Equal(expected, scaleLeadTo 17L 7 img)
    Assert.Equal(scaleLeadTo 17L 7 (modPoly 17I g), expected)   // и это действительно G mod 17
    let tag2, img2 = zippelImage 17L a b form13 3 -1 1 22UL
    Assert.Equal("ok", tag2)
    Assert.Equal(expected, scaleLeadTo 17L 7 img2)
    Assert.Equal(Some g, tryZippelGcd a b 3UL)

// Example 3: структура системы multiple scaling — форма (a2y²+a1y+a0)x² + (b2y³+b1y+b0)x + (c1y²+c0)
[<Fact>]
let ``LINZIP Example 3: форма из статьи, число образов по Remark 2`` () =
    let x, y = vv 1, vv 0
    let g3 =
        add (add (mul (add (add (pow y 2) (mul (c 2) y)) (c 3)) (pow x 2))
                 (mul (add (add (mul (c 2) (pow y 3)) (mul (c 5) y)) (c 1)) x))
            (add (mul (c 3) (pow y 2)) (c 7))
    // размеры блоков 3, 3, 2: max(3, ⌈(8−1)/(3−1)⌉) = 4
    Assert.Equal((4, false), zippelFormInfo g3)
    let a, b = mul (add (add x y) (c 2)) g3, mul (add (sub x y) (c 3)) g3
    // при 4 образах система определена; образ — G mod p с точностью до константы
    let p = P31
    let before = zs ()
    let tag, img = zippelImage p a b g3 2 -1 0 31UL
    Assert.Equal("ok", tag)
    Assert.Equal(before.[12] + 4, (zs ()).[12])
    Assert.Equal(scaleLeadTo p 1 (modPoly (BigInteger p) g3), scaleLeadTo p 1 img)
    // принудительно 3 образа (число из текста Example 3: «9 уравнений на 10 неизвестных»): система недоопределена,
    // алгоритм (шаг 5.6) добавляет образ — итого те же 4
    let before2 = zs ()
    let tag3, img3 = zippelImage p a b g3 2 3 0 32UL
    Assert.Equal("ok", tag3)
    Assert.Equal(before2.[12] + 4, (zs ()).[12])
    Assert.Equal(scaleLeadTo p 1 img, scaleLeadTo p 1 img3)
    Assert.Equal(Some g3, tryZippelGcd a b 5UL)

// Example 4: у НОД есть содержание по x ((y+2)·(x³+12y)) — система остаётся недоопределённой при любых точках
[<Fact>]
let ``LINZIP Example 4: содержание по x — недоопределённость повторяется, образ отвергается`` () =
    let x, y = vv 1, vv 0
    let g = mul (add y (c 2)) (add (pow x 3) (mul (c 12) y))
    let a, b = mul (add (add x y) (c 1)) g, mul (add (sub x y) (c 2)) g
    let form = add (add (mul (pow x 3) y) (mul (c 2) (pow x 3))) (add (mul (c 12) (pow y 2)) (mul (c 11) y))
    let before = zs ()
    let tag, _ = zippelImage P31 a b form 3 -1 0 41UL
    Assert.Equal("bad", tag)
    let after = zs ()
    Assert.Equal(before.[7] + 1, after.[7])       // недоопределённость с теми же степенями свободы встретилась трижды
    Assert.Equal(before.[12] + 5, after.[12])     // образы 3, 4, 5 (как в статье: добавляют y = 4 и сдаются)

// Проверка результата Зиппеля без сравнения с PRS: r делит a и b, кофакторы взаимно просты (проба одной точкой
// доказывает НОД = 1 за один вызов; если не доказала — эталон считает Браун с отключённым Зиппелем)
let private checkIsGcd (what: string) (a: MPoly) (b: MPoly) (r: MPoly) =
    let qa, qb = divExact a r, divExact b r
    Assert.True(qa.IsSome && qb.IsSome, what + ": результат не делит входные")
    match probeGcdDegree qa.Value qb.Value 77UL 3 with
    | Some 0 -> ()
    | _ ->
        setZippelMode 2
        try Assert.Equal(c 1, gcd qa.Value qb.Value)
        finally setZippelMode 0

[<Fact>]
let ``Зиппель: Фейтман F_1 (взаимно просты), n = 1..3`` () =
    for n in 1 .. 3 do
        let fg = fateman n
        let pf, pg = primPart fg.[0], primPart fg.[1]
        Assert.Equal(Some one, tryZippelGcd pf pg 3UL)

[<Fact>]
let ``Зиппель: Фейтман F_2 и F_3 (общий множитель h), n = 1..3`` () =
    for n in 1 .. 3 do
        for (name, (f, g, h)) in [ "F_2", fateman2 n; "F_3", fateman3 n ] do
            let pf, pg = primPart f, primPart g
            match tryZippelGcd pf pg (uint64 n) with
            | Some r ->
                Assert.Equal(unitNormal h, r)
            | None -> failwithf "%s n=%d: Зиппель отказал" name n

[<Fact>]
let ``Зиппель: немонический НОД — старшие коэффициенты по x зависят от y и z`` () =
    let x, y, z = vv 2, vv 1, vv 0
    // G с lc_x = (y+2)(z−1)² — НЕ константа; множители-кофакторы тоже с нетривиальными lc
    let g = add (mul (mul (add y (c 2)) (pow (sub z (c 1)) 2)) (pow x 3))
                (add (mul (add (mul y z) (c 3)) (pow x 2)) (add (mul (c 5) (mul y x)) (sub (pow z 2) (c 7))))
    let a = mul g (add (mul (add y z) (pow x 2)) (add x (c 4)))
    let b = mul g (add (mul (sub y z) (pow x 2)) (sub (mul y x) (c 3)))
    let pa, pb = primPart a, primPart b
    let r = tryZippelGcd pa pb 9UL
    Assert.Equal(Some (unitNormal g), r)

[<Fact>]
let ``Зиппель: НОД f и f' (бесквадратное разложение), 3 переменных`` () =
    let x, y, z = vv 2, vv 1, vv 0
    // f = (x²+yz+1)²(x+y−z)³(xz+y+2): НОД(f, f') = (x²+yz+1)(x+y−z)²
    let u = add (add (pow x 2) (mul y z)) (c 1)
    let w = sub (add x y) z
    let f = mul (mul (pow u 2) (pow w 3)) (add (add (mul x z) y) (c 2))
    let f' = deriv 2 f
    let pf, pf' = primPart f, primPart f'
    Assert.Equal(Some (unitNormal (mul u (pow w 2))), tryZippelGcd pf pf' 4UL)

// Случайная пара с известным общим множителем: 3..6 переменных, главная — старшая, G нетривиально зависит от неё
let private randomPair (rnd: Random) (nv: int) =
    let x = vv (nv - 1)
    let g = add (mul (randPoly rnd (nv - 1) 3 2 9) (pow x 2)) (add (mul (randPoly rnd nv 2 2 9) x) (randPoly rnd nv 3 3 9))
    let a = mul g (add (randPoly rnd nv 3 2 9) (mul x (randPoly rnd nv 2 1 5)))
    let b = mul g (add (randPoly rnd nv 3 2 9) (mul (pow x 2) (randPoly rnd nv 2 1 5)))
    (g, a, b)

[<Fact>]
let ``Зиппель: 60 случайных пар от 3 до 6 переменных (эталон — построение + точное деление + кофакторы взаимно просты)`` () =
    let rnd = Random 20271014
    let mutable tested = 0
    for i in 1 .. 60 do
        let nv = 3 + i % 4
        let (g, a, b) = randomPair rnd nv
        if mainVar a = nv - 1 && mainVar b = nv - 1 && mainVar g = nv - 1 then
            let pa, pb = primPart a, primPart b
            match tryZippelGcd pa pb (uint64 i) with
            | Some r ->
                checkIsGcd (sprintf "пара %d (%d перем.)" i nv) pa pb r
                tested <- tested + 1
            | None -> failwithf "пара %d (%d перем.): Зиппель отказал" i nv
    Assert.True(tested >= 50, sprintf "проверено только %d пар" tested)

[<Fact>]
let ``эвристика выбора: 3+ переменных — Зиппель; 2 переменных — Браун при степени НОД < 3, иначе Зиппель`` () =
    let x3, y3, z3 = vv 2, vv 1, vv 0
    let g3 = add (add (pow x3 2) (mul y3 z3)) (c 3)
    let a3, b3 = mul g3 (add (add x3 y3) z3), mul g3 (sub (sub x3 y3) (c 1))
    let x2, y2 = vv 1, vv 0
    let gLow = add (add (pow x2 2) y2) (c 1)                       // степень НОД по x равна 2
    let gHigh = add (add (pow x2 4) (mul (c 2) (mul x2 (pow y2 3)))) (add (pow y2 4) (c 7))   // 4
    let pair g = mul g (add (add x2 y2) (c 2)), mul g (sub (mul x2 y2) (c 3))
    let (aL, bL), (aH, bH) = pair gLow, pair gHigh
    let measure (a: MPoly) (b: MPoly) =
        let before = zs ()          // входные данные готовы до чтения счётчиков
        let r = gcd a b
        r, (zs ()).[0] - before.[0]
    let r3, calls3 = measure a3 b3
    Assert.Equal(unitNormal g3, r3)
    Assert.True(calls3 >= 1, "3 переменных: LINZIP не вызывался")
    let rL, callsL = measure aL bL
    Assert.Equal(unitNormal gLow, rL)
    Assert.Equal(0, callsL)
    let rH, callsH = measure aH bH
    Assert.Equal(unitNormal gHigh, rH)
    Assert.True(callsH >= 1, "2 переменных, степень 4: LINZIP не вызывался")

[<Fact>]
let ``Зиппель и Браун совпадают на 20 случайных тройках переменных малого размера (режимы через gcd)`` () =
    // 4 переменных не берём: Браун на случайных немонических парах там не укладывается в минуты (ради этого Зиппель)
    let rnd = Random 4242
    for i in 1 .. 20 do
        let x = vv 2
        let g = add (mul (randPoly rnd 2 2 2 9) (pow x 2)) (randPoly rnd 3 3 2 9)
        let a = mul g (add (randPoly rnd 3 2 2 9) (mul x (randPoly rnd 3 1 1 5)))
        let b = mul g (add (randPoly rnd 3 2 2 9) (mul (pow x 2) (randPoly rnd 3 1 1 5)))
        if mainVar a = 2 && mainVar b = 2 then
            setZippelMode 1
            let viaZ = try gcd a b finally setZippelMode 0
            setZippelMode 2
            let viaB = try gcd a b finally setZippelMode 0
            Assert.True((viaB = viaZ), sprintf "пара %d: Зиппель и Браун дали разные НОД" i)

[<Fact>]
let ``Зиппель: структурные случаи НОД — степень x равна 0, 1, одночлен x^k, блоки одного размера, G = a, общий делитель a | b`` () =
    let rnd = Random 99
    let x, y, z, w = vv 3, vv 2, vv 1, vv 0
    let cof () = add (randPoly rnd 4 3 2 9) (mul x (randPoly rnd 4 2 1 5))
    let cases : (string * MPoly) list =
        [ "x^3", pow x 3
          "линейный по x", add (mul (add (add y z) (c 2)) x) (add (mul y w) (c 5))
          "линейный по x, lc — моном", add (mul (mul y z) x) (add w (c 3))
          "x²: блоки {y,1},{z,1},{w,1}", add (add (mul (add y (c 1)) (pow x 2)) (mul (add z (c 2)) x)) (add w (c 3))
          "x²: три блока по 3 терма", add (add (mul (add (add y z) w) (pow x 2)) (mul (add (add (mul y z) w) (c 1)) x)) (add (add (mul y w) z) (c 7))
          "x²y³ + z (разные степени)", add (mul (pow y 3) (pow x 2)) z
          "1 + x^6 + x^3 y w", add (add (pow x 6) (mul (pow x 3) (mul y w))) one ]
    for (name, g) in cases do
        for round in 1 .. 4 do
            let a, b = mul g (cof ()), mul g (add (cof ()) (pow x 2))
            let pa, pb = primPart a, primPart b
            match tryZippelGcd pa pb (uint64 round) with
            | Some r -> checkIsGcd (sprintf "%s, раунд %d" name round) pa pb r
            | None -> failwithf "%s, раунд %d: отказ" name round
    // G = a (кофактор a равен 1) и a | b
    let g = add (add (mul (add y (c 1)) (pow x 2)) (mul (add z (c 2)) x)) (add w (c 3))
    let b = mul g (add (mul x w) (c 4))
    Assert.Equal(Some (unitNormal g), tryZippelGcd (primPart g) (primPart b) 3UL)
    Assert.Equal(Some (unitNormal g), tryZippelGcd (primPart b) (primPart g) 3UL)
    Assert.Equal(Some (unitNormal g), tryZippelGcd (primPart g) (primPart g) 3UL)

[<Fact>]
let ``счётчики: на невырожденных входах (бенчмарки 21g, Фейтман, случайные пары) откатов нет, каждый вызов успешен`` () =
    let rep (name: string) (f: unit -> unit) =
        let s0 = zs ()
        f ()
        let s1 = zs ()
        let d = Array.map2 (-) s1 s0
        Assert.True(d.[0] > 0, name + ": LINZIP не вызывался")
        Assert.Equal(d.[0], d.[1])                                  // каждый вызов — успех
        Assert.Equal(0, d.[2])                                      // откатов на Брауна нет
        for k in 3 .. 9 do Assert.True(d.[k] = 0, sprintf "%s: счётчик [%d] = %d" name k d.[k])   // и откатов по причинам
        Assert.Equal(0, d.[13])
    // c9
    let x, y, z, w = vv 2, vv 1, vv 0, vv 3
    let lin3 (a: int) (b: int) (cc: int) (d: int) = add (add (add (mul (c a) x) (mul (c b) y)) (mul (c cc) z)) (c d)
    let g9 = pow (lin3 1 2 3 1) 4
    let a9, b9 = mul g9 (pow (lin3 1 1 -1 2) 4), mul g9 (pow (lin3 2 -1 1 3) 4)
    rep "c9 (3 перем., deg 8/4)" (fun () -> gcd a9 b9 |> ignore)
    // c10: x=3,y=2,z=1,w=0
    let X, Y, Z, W = vv 3, vv 2, vv 1, vv 0
    let a10 = pow (add (add (add (pow X 2) (mul Y Z)) W) one) 3
    let b10 = mul (pow (add (add (add (mul X Y) (pow Z 2)) (pow W 2)) (c 2)) 2) (pow (add (add (add (add X Y) Z) W) (c 3)) 2)
    rep "c10 (4 перем., взаимно простые)" (fun () -> gcd a10 b10 |> ignore)
    // c12
    let u = add (add (add (add (mul (pow X 7) (pow Y 2)) (mul (pow Y 6) (pow Z 3))) (mul (pow Z 6) (pow W 3))) (mul (pow W 5) (pow X 2))) one
    let p12 = mul (pow u 2) (add (add (add (pow X 3) (mul Y Z)) (pow W 2)) (c 3))
    let dx, dy = deriv 3 p12, deriv 2 p12
    rep "c12 (НОД(p,p'x), НОД(p,p'y))" (fun () -> gcd p12 dx |> ignore; gcd p12 dy |> ignore)
    // c11: x1..x6 = 5..0
    let v i = vv (6 - i)
    let g11 = add (add (add (add (add (mul (pow (v 1) 3) (v 2)) (mul (pow (v 2) 4) (v 3))) (mul (pow (v 3) 4) (v 4))) (mul (pow (v 4) 4) (v 5))) (mul (pow (v 5) 4) (v 6))) one
    let a11 = mul g11 (add (add (add (mul (v 1) (v 3)) (mul (v 5) (pow (v 6) 2))) (mul (c 2) (v 2))) (c 7))
    let b11 = mul g11 (add (add (add (add (mul (v 2) (v 4)) (mul (v 1) (v 6))) (mul (v 3) (v 5))) (mul (c -3) (v 1))) (c 5))
    rep "c11 (6 перем., разреженный)" (fun () -> gcd a11 b11 |> ignore)
    // F_2, F_3
    for n in 2 .. 3 do
        let f, g, _ = fateman2 n
        let pf, pg = primPart f, primPart g
        rep (sprintf "F_2 n=%d" n) (fun () -> gcd pf pg |> ignore)
        let f, g, _ = fateman3 n
        let pf, pg = primPart f, primPart g
        rep (sprintf "F_3 n=%d" n) (fun () -> gcd pf pg |> ignore)
    // 60 случайных пар
    let rnd = Random 20271014
    let pairs = [ for i in 1 .. 60 do
                    let nv = 3 + i % 4
                    let (g, a, b) = randomPair rnd nv
                    if mainVar a = nv - 1 && mainVar b = nv - 1 && mainVar g = nv - 1 then yield (primPart a, primPart b) ]
    rep "60 случайных пар (tryZippelGcd)" (fun () -> pairs |> List.iteri (fun i (pa, pb) -> tryZippelGcd pa pb (uint64 i) |> ignore))

// ---------- откаты ----------

[<Fact>]
let ``откат: неверная форма — несовместность, терм вне формы, нет масштабного терма`` () =
    let x, y, g, a, b = example1 ()
    let p = P31
    // форма без терма (старая форма пропустила y·x⁰): несовместная система
    let formNoTerm = mul (add y (c 50)) (pow x 3)
    Assert.Equal("form", fst (zippelImage p a b formNoTerm 3 -1 1 1UL))
    // у НОД есть x³-блок, которого нет в форме (форма от x²): образ содержит терм вне формы
    let formOutside = add (mul (add y (c 50)) (pow x 2)) (mul (c 100) y)
    Assert.Equal("form", fst (zippelImage p a b formOutside 3 -1 1 2UL))
    // форма с лишним одночленным блоком x¹ (масштабный терм): в образе НОД его нет — «scaling term absent»
    let formScale = add g (mul (c 7) x)
    Assert.Equal("form", fst (zippelImage p a b formScale 3 -1 1 3UL))

[<Fact>]
let ``откат: падение степени — образ степени ниже dx1 возвращает новую границу`` () =
    let x, y, g, a, b = example1 ()
    // граница 4 (образ первого простого был невезучим: НОД·(x+1)), истинная степень 3
    let form = mul (add y (c 50)) (pow x 4)
    let tag, _ = zippelImage P31 a b (add form (mul (c 100) y)) 4 -1 1 4UL
    Assert.Equal("degdrop:3", tag)

[<Fact>]
let ``откат: невезучая точка — степень НОД выше границы`` () =
    let x, y, g, a, b = example1 ()
    // граница 2 при истинной степени 3: каждый образ выше границы — «невезучее простое» уже на первом образе
    let form = add (mul (add y (c 50)) (pow x 2)) (mul (c 100) y)
    let before = zs ()
    Assert.Equal("bad", fst (zippelImage P31 a b form 2 -1 1 5UL))
    Assert.Equal(before.[6] + 1, (zs ()).[6])

[<Fact>]
let ``откат M: простое обнуляет терм НОД (пропавший терм) — несовместность, новый первый образ`` () =
    let x, y, z = vv 2, vv 1, vv 0
    // коэффициент при y·z делится на первое простое 2^31−1: по нему этого терма в первом образе нет
    let g = add (add (pow x 2) (mul (mul (c (int P31)) y) z)) (add z (c 1))
    let a = mul g (add (add (add x y) z) (c 1))
    let b = mul g (add (sub (mul x y) z) (c 2))
    let before = zs ()
    Assert.Equal(Some g, tryZippelGcd a b 12UL)
    let after = zs ()
    Assert.True(after.[5] > before.[5], "пропавший терм не обнаружен (шаг 5.5)")
    Assert.Equal(before.[1] + 1, after.[1])

[<Fact>]
let ``откат M: невезучее простое — кофакторы не взаимно просты по модулю первого простого`` () =
    let x, y, z = vv 2, vv 1, vv 0
    let g = add (add (pow x 2) y) z
    // по модулю 2^31−1 оба кофактора равны x+1 (и ещё z): НОД первого образа — G·(x+1), степень 3 > 2
    let ca = add (add x (c 1)) (mul (c (int P31)) y)
    let cb = add (add x (c 1)) (mul (c (int P31)) z)
    let a, b = mul g ca, mul g cb
    let before = zs ()
    Assert.Equal(Some g, tryZippelGcd a b 13UL)
    let after = zs ()
    Assert.True(after.[4] > before.[4], "падение степени (невезучий первый образ) не обнаружено")

[<Fact>]
let ``откат P: у НОД есть содержание по x_n — Fail (шаг 0); пример g = x(y+1)+y+14 по модулю 13`` () =
    let x, y = vv 1, vv 0
    let g = add (mul x (add y (c 1))) (add y (c 14))
    let a, b = mul g (add x (c 2)), mul g (add x y)
    let before = zs ()
    // по модулю 13: g = (y+1)(x+1) — содержание y+1 по x
    Assert.True((zippelPrimeGcd 13L a b 1 5UL).IsNone)
    Assert.Equal(before.[3] + 1, (zs ()).[3])
    // по другому простому содержания нет; результат (с точностью до константы) — g mod p
    match zippelPrimeGcd 17L a b 1 5UL with
    | Some r -> Assert.Equal(scaleLeadTo 17L 1 (modPoly 17I g), scaleLeadTo 17L 1 r)
    | None -> failwith "P отказал по модулю 17"
    // над Z (M) — обычный результат: плохое простое здесь не используется
    Assert.Equal(Some g, tryZippelGcd a b 5UL)

[<Fact>]
let ``откат P: невезучие точки x_n при малом простом (принудительные значения через seed) — результат остаётся верным`` () =
    let x, y, z = vv 2, vv 1, vv 0
    let g = add (add (pow x 2) (mul y x)) (add z (c 1))
    // кофакторы x−z и x−1 по модулю p взаимно просты, но в точке z = 1 совпадают: невезучее вычисление
    let a, b = mul g (sub x z), mul g (sub x (c 1))
    let p = 13L
    let expected = scaleLeadTo p 1 (modPoly (BigInteger p) g)
    let before = zs ()
    let mutable some, none = 0, 0
    for dx1 in [ 2; 3 ] do          // точная граница и завышенная
        for seed in 1 .. 60 do
            match zippelPrimeGcd p a b dx1 (uint64 seed) with
            | Some r ->
                some <- some + 1
                Assert.Equal(expected, scaleLeadTo p 1 r)
            | None -> none <- none + 1
    let after = zs ()
    Assert.True(some > 60, sprintf "успешных: %d" some)
    // откаты реально встретились: падение степени (завышенная граница) и невезучая точка (точная граница)
    Assert.True(after.[4] > before.[4], "падение степени не встретилось")
    Assert.True(after.[6] > before.[6], "невезучая точка не встретилась")

[<Fact>]
let ``Зиппель реально сработал в gcd: 4 переменные, без отката на Брауна`` () =
    let x, y, z, w = vv 3, vv 2, vv 1, vv 0
    let g = add (add (mul (add y w) (pow x 2)) (mul (sub z (c 2)) x)) (add (mul y z) (c 3))
    let a = mul g (add (add (mul x y) z) (add w (c 1)))
    let b = mul g (sub (add (pow x 2) (mul z w)) (c 5))
    let before = zs ()          // входные данные готовы до чтения счётчиков
    let r = gcd a b
    let after = zs ()
    Assert.Equal(unitNormal g, r)
    Assert.True(after.[0] > before.[0], "LINZIP M не вызывался")
    Assert.Equal(after.[0] - before.[0], after.[1] - before.[1])   // каждый вызов закончился успехом
    Assert.Equal(before.[2], after.[2])                             // откатов на Брауна нет

[<Fact>]
let ``Зиппель и Браун дают одно и то же (режимы), multiple и single scaling, большие коэффициенты`` () =
    let x, y, z = vv 2, vv 1, vv 0
    let big = BigInteger.Pow (10I, 25)
    // multiple scaling: блоки x²:{y,1}, x:{z,1}, 1:{y,z}; lc по x — не константа
    let gm = add (add (mul (add y (c 1)) (pow x 2)) (mul (add z (c 2)) x)) (add y z)
    // single scaling: x⁰-блок — одночлен 2yz, большие коэффициенты
    let gs = add (add (mul (ofInt big) (pow x 2)) (mul (add (mul (c 3) y) z) x)) (mul (c 2) (mul y z))
    for (name, g) in [ "multiple", gm; "single", gs ] do
        let a = mul g (add (add x y) (c 3))
        let b = mul g (sub (mul x z) (add y (c 4)))
        let pa, pb = primPart a, primPart b
        let before = zs ()
        let viaZ = tryZippelGcd pa pb 7UL
        let after = zs ()
        Assert.Equal(Some (unitNormal g), viaZ)
        if name = "multiple" then Assert.True(after.[11] > before.[11]) else Assert.True(after.[10] > before.[10])
        setZippelMode 2
        let viaB = try gcd pa pb finally setZippelMode 0
        Assert.Equal(unitNormal g, viaB)

[<Fact>]
let ``Зиппель: взаимно простые 3-4 переменные (проба и Зиппель дают 1)`` () =
    let rnd = Random 11
    for nv in 3 .. 4 do
        for _ in 1 .. 3 do
            let a = primPart (add (pow (vv (nv - 1)) 3) (randPoly rnd nv 6 2 9))
            let b = primPart (add (pow (vv (nv - 1)) 2) (randPoly rnd nv 6 2 9))
            match tryZippelGcd a b 6UL with
            | Some r -> Assert.Equal(one, r)
            | None -> failwith "отказ на взаимно простых"
