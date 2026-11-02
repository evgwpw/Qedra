module Core

open System.Numerics
open Algebra

// вызов через границу сборок: Algebra.shifted — модульная функция, читающая модульные значения
let run (n: int) : string = shifted (BigInteger n) |> string
