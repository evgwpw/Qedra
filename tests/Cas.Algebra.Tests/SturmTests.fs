// Тесты изоляции корней по Штурму, рациональных корней и результанта (Sturm.fs, Resultant.fs, Cas.Algebra):
// перенесены из AlgebraicTests (шаг 21h'); многочлены — списки bigint от старшей степени к младшей
module SturmTests

open Xunit
open Sturm
open Resultant

[<Fact>]
let ``roots x^2-2 → 2 корня`` () =
    let r = isolateRoots [1I; 0I; -2I]
    Assert.Equal(2, r.Length)

[<Fact>]
let ``roots x^2-3 → 2 корня`` () =
    let r = isolateRoots [1I; 0I; -3I]
    Assert.Equal(2, r.Length)

[<Fact>]
let ``roots x^2-1 → 2 корня ±1`` () =
    let r = isolateRoots [1I; 0I; -1I]
    Assert.Equal(2, r.Length)

[<Fact>]
let ``roots x^3-1 → 1 действительный корень`` () =
    let r = isolateRoots [1I; 0I; 0I; -1I]
    Assert.Equal(1, r.Length)

[<Fact>]
let ``roots x^2+1 → 0 действительных корней`` () =
    let r = isolateRoots [1I; 0I; 1I]
    Assert.Equal(0, r.Length)

[<Fact>]
let ``roots x^2-3x+1 → 2 корня`` () =
    let r = isolateRoots [1I; -3I; 1I]
    Assert.Equal(2, r.Length)

[<Fact>]
let ``resultant x^2-2 и x-a → (a^2-2)`` () =
    // Res_y(y²-2, y - a) = a² - 2
    let r = resultant [1I; 0I; -2I] [1I; -5I]
    Assert.Equal(23I, r)

[<Fact>]
let ``rationalRoots x^2-1 → ±1`` () =
    let r = rationalRoots [1I; 0I; -1I]
    Assert.Equal(2, r.Length)
