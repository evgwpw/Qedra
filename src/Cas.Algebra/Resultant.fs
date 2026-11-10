// Результатант и интерполяция (Шаг 12; вынесено из Algebraic.fs в Шаге 15a)
module Resultant

open System.Numerics
open Rational
open Sturm

// --- Результатант (матрица Сильвестра) ---

// Определитель матрицы bigint — алгоритм Барейсса (дробно-свободное исключение Гаусса)
// Точное деление на предыдущий ведущий элемент; O(n³), без факториального роста
let detBigInt (m: bigint[,]) : bigint =
    let n = m.GetLength(0)
    if n = 0 then 1I
    else
        let a = Array2D.copy m
        let mutable sign = 1I
        let mutable prev = 1I
        let mutable singular = false
        let mutable k = 0
        while not singular && k < n - 1 do
            // выбор ведущего элемента (перестановка строк при нуле)
            if a.[k, k] = 0I then
                let mutable r = k + 1
                while r < n && a.[r, k] = 0I do
                    r <- r + 1
                if r = n then
                    singular <- true
                else
                    for j in k .. n - 1 do
                        let t = a.[k, j]
                        a.[k, j] <- a.[r, j]
                        a.[r, j] <- t
                    sign <- -sign
            if not singular then
                for i in k + 1 .. n - 1 do
                    for j in k + 1 .. n - 1 do
                        a.[i, j] <- (a.[i, j] * a.[k, k] - a.[i, k] * a.[k, j]) / prev
                prev <- a.[k, k]
                k <- k + 1
        if singular then 0I else sign * a.[n - 1, n - 1]

// Результатант двух многочленов через матрицу Сильвестра
let resultant (p: bigint list) (q: bigint list) : bigint =
    let p' = normalize p
    let q' = normalize q
    let m = p'.Length - 1
    let n = q'.Length - 1
    if m = 0 && List.head p' = 0I then 0I
    elif n = 0 && List.head q' = 0I then 0I
    else
        let size = m + n
        let syl = Array2D.init size size (fun i j ->
            if i < n then
                // первые n строк — коэффициенты p со сдвигом
                if j >= i && j < i + p'.Length then p'.[j - i] else 0I
            else
                // остальные m строк — коэффициенты q со сдвигом
                let r = i - n
                if j >= r && j < r + q'.Length then q'.[j - r] else 0I)
        detBigInt syl

// --- Bivariate resultant через подстановку и интерполяцию ---

// Подстановка x_i в q(x-y): q_i(y) = Σ q_k (x_i - y)^k — полином от y
let substForAdd (q: bigint list) (xi: bigint) : bigint list =
    let qn = normalize q
    let n = qn.Length - 1
    let result = Array.create (n + 1) 0I
    let qLow = List.rev qn
    List.iteri (fun k c ->
        // (x_i - y)^k: коэффициент при y^j = C(k,j) * x_i^(k-j) * (-1)^j
        for j in 0 .. k do
            let rec bin (a: bigint) (b: bigint) : bigint =
                if b = 0I || b = a then 1I
                else bin (a - 1I) (b - 1I) * a / b
            let bc = bin (bigint k) (bigint j)
            let sign = if j % 2 = 0 then 1I else -1I
            result.[j] <- result.[j] + c * bc * (BigInteger.Pow(xi, k - j)) * sign) qLow
    normalize (List.rev (Array.toList result))

// Подстановка x_i в y^n * q(x/y): коэффициент при y^m равен c_{n-m} * x_i^{n-m}
let substForMul (q: bigint list) (xi: bigint) : bigint list =
    let qn = normalize q
    let n = qn.Length - 1
    // разворачиваем к младшей→старшей: коэффициент при y^m = c_m * x^m (позиция = степень)
    qn |> List.rev |> List.mapi (fun m c -> c * BigInteger.Pow(xi, m)) |> normalize

// Лагранжева интерполяция (разделённые разности Ньютона)
// Узлы — последовательные целые, значения — целые ⇒ коэффициенты целые (деление точное)
let lagrangeInterp (points: (bigint * bigint) list) : bigint list =
    let n = points.Length
    if n = 0 then [0I]
    else
        let xs = points |> List.map fst |> Array.ofList
        let ys = points |> List.map snd |> Array.ofList
        let table = ys |> Array.copy
        let coeffs = Array.create n 0I
        for j in 0 .. n - 1 do
            coeffs.[j] <- table.[j]
            for i in n - 1 .. -1 .. j + 1 do
                // знаменатель разделённой разности: x_i - x_{i-j-1}
                table.[i] <- (table.[i] - table.[i - 1]) / (xs.[i] - xs.[i - j - 1])
        // Полином Ньютона: Σ c_j Π_{i<j} (x - x_i)
        // Схема Горнера для формы Ньютона: r = c_{n-1}; r = r*(x - x_j) + c_j для j = n-2 .. 0
        // (умножение на (x - a): коэффициенты [r_k] → [r_k] @ [0] минус a * ([0] @ [r_k]))
        let mulLinear (r: bigint list) (a: bigint) : bigint list =
            let hi = r @ [0I]
            let lo = 0I :: (r |> List.map (fun t -> t * a))
            List.map2 (-) hi lo
        let mutable result = [coeffs.[n - 1]]
        for j in n - 2 .. -1 .. 0 do
            let m = mulLinear result xs.[j]
            // прибавить c_j к свободному члену (последний элемент списка)
            result <- (List.take (m.Length - 1) m) @ [List.last m + coeffs.[j]]
        normalize result

// R(x) = Res_y(p(y), s(x,y)) — вычисляем результатант в целых точках x_i и интерполируем
let bivariateResultant (p: bigint list) (q: bigint list)
                       (substFn: bigint list -> bigint -> bigint list) : bigint list =
    let n = degree q
    // степень R ≤ deg(p)*deg(q); берём достаточно точек -k..k (последовательные целые)
    let numPts = degree p * n + 1
    let center = bigint (numPts / 2)
    let points =
        [ for i in 0 .. numPts - 1 ->
            let xi = bigint i - center
            (xi, resultant p (substFn q xi)) ]
    lagrangeInterp points

