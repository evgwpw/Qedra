module Algebra

open System.Numerics

// модульное значение: именно такие F# кладёт в <StartupCode$Algebra>.$Algebra
let scale = BigInteger 3
let offset = BigInteger 1

let twice (x: BigInteger) = x * scale
let shifted (x: BigInteger) = twice x + offset
