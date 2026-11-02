// Тесты рациональной арифметики на кортежах (Rational.fs, Cas.Algebra): isqrtBigint перенесены из AlgebraicTests (шаг 21h')
module RationalTests

open System.Numerics
open Xunit
open Rational

[<Fact>]
let ``isqrtBigint точный квадрат`` () =
    Assert.Equal(10I, isqrtBigint 100I)
    Assert.Equal(3I, isqrtBigint 9I)

[<Fact>]
let ``isqrtBigint не квадрат — округление вниз`` () =
    Assert.Equal(1I, isqrtBigint 2I)
    Assert.Equal(4I, isqrtBigint 24I)

[<Fact>]
let ``ratNorm: сокращение и положительный знаменатель`` () =
    Assert.Equal((1I, 2I), ratNorm (2I, 4I))
    Assert.Equal((-1I, 3I), ratNorm (1I, -3I))
    Assert.Equal((0I, 1I), ratNorm (0I, -7I))
    Assert.ThrowsAny<exn>(fun () -> ratNorm (1I, 0I) |> ignore) |> ignore

[<Fact>]
let ``арифметика кортежей: + - * / и сравнение`` () =
    Assert.Equal((5I, 6I), ratAdd (1I, 2I) (1I, 3I))
    Assert.Equal((1I, 6I), ratSub (1I, 2I) (1I, 3I))
    Assert.Equal((1I, 6I), ratMul (1I, 2I) (1I, 3I))
    Assert.Equal((3I, 2I), ratDiv (1I, 2I) (1I, 3I))
    Assert.True(ratCompare (1I, 3I) (1I, 2I) < 0)
    Assert.Equal(-1, ratSign (-5I, 7I))
    Assert.True(ratIsZero (0I, 1I))
    Assert.ThrowsAny<exn>(fun () -> ratDiv (1I, 2I) (0I, 1I) |> ignore) |> ignore
