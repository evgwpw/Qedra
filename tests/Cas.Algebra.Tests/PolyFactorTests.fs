// Тесты разложения на множители над ℤ (чистая алгебра, Cas.Algebra): factorPoly.
// Шаг 21h': тесты factor/sqfree над выражениями Lisp остались в Lisp.Tests (FactorExprTests.fs); здесь — то, что не
// использует типы Lisp (случайные многомерные произведения); остальные эталоны — WangFactorTests.fs
module PolyFactorTests

open System
open System.Diagnostics
open System.Numerics
open Xunit

[<Fact>]
let ``factor многомерный: случайные произведения 2-3 многочленов`` () =
    let rnd = Random 2027
    let nv = 3
    let v i = MPoly.var i
    let randPoly (maxDeg: int) =
        // x (главная, индекс 2) входит всегда: хотя бы степень 1
        let mutable r = MPoly.zero
        for _ in 1 .. rnd.Next(3, 6) do
            let mutable t = MPoly.ofInt (BigInteger (rnd.Next(1, 5) * (if rnd.Next 2 = 0 then 1 else -1)))
            for i in 0 .. nv - 1 do
                let d = rnd.Next(0, maxDeg + 1)
                if d > 0 then t <- MPoly.mul t (MPoly.pow (v i) d)
            r <- MPoly.add r t
        MPoly.add r (v 2)
    let sw = Stopwatch.StartNew()
    for round in 1 .. 25 do
        let k = if round % 3 = 0 then 3 else 2
        let fs = [ for _ in 1 .. k -> randPoly 2 ]
        let p = fs |> List.fold MPoly.mul MPoly.one
        let (c, parts) = PolyFactor.factorPoly p
        // произведение множителей = исходному
        let back = parts |> List.fold (fun acc (f, e) -> MPoly.mul acc (MPoly.pow f e)) (MPoly.mulConst c MPoly.one)
        Assert.Equal(p, back)
        // число множителей (с кратностями) не меньше числа сомножителей, неконстантных
        let expected = fs |> List.filter (fun f -> not (MPoly.isConst f)) |> List.length
        Assert.True((parts |> List.sumBy snd) >= expected, sprintf "раунд %d: %d < %d" round (parts |> List.sumBy snd) expected)
    Assert.True(sw.ElapsedMilliseconds < 20000L, sprintf "%d мс" sw.ElapsedMilliseconds)
