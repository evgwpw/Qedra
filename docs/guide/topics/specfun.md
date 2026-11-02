# Topic: specfun

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=>` after a form is the printed result it must give. Expressions are data: quote them. Heads: `(gamma z)`, `(beta a b)`, `(psi z)` (digamma), `(hyper (a ...) (b ...) z)` = pFq (parameter lists are plain lists, `()` when empty). A pole gives `(complex-infinity)`; `1/Gamma(pole)` is 0. Identities with a side condition write it to the `conditions` channel (reflection for symbolic `z`: `sin(pi z) /= 0`; Gauss: `c-a-b > 0`).

## Functions

* `(sf-gamma z)`: Gamma(z). Integers `(n-1)!`, half-integers `r*sqrt(pi)` (also negative), poles `(complex-infinity)`; other rationals are reduced to the fractional part in (0,1).
* `(sf-beta a b)`: B(a,b) = Gamma(a)Gamma(b)/Gamma(a+b) when it simplifies (both rational, or one a positive integer); otherwise `(beta a b)`.
* `(sf-digamma z)`: psi: `psi(n) = -euler-gamma + H(n-1)`, `psi(1/2) = -euler-gamma - 2 log 2`; a symbolic `z+k` is shifted: `psi(z+1) = psi(z) + 1/z`.
* `(specfun-simplify e)`: `simplify` plus the recurrence `Gamma(z+1) = z Gamma(z)` (all `Gamma(z+k)` of one class reduce to the smallest shift), the reflection `Gamma(z)Gamma(1-z) = pi/sin(pi z)` for pairs with `a+b` an integer, exact Gamma, B, psi.
* `(specfun-duplication e)`, `(specfun-duplication-collapse e)`: Legendre duplication `Gamma(2z) = 2^(2z-1) pi^(-1/2) Gamma(z) Gamma(z+1/2)` and the reverse (pairs in products).
* `(hyper-term h k)`, `(hyper-series h n)`: exact k-th term; exact sum of terms 0..n.
* `(hyper-reduce h)`: `z = 0` gives 1; equal `a` and `b` cancel (except integers <= 0); `a = 0` gives 1; `a = -n` gives a polynomial of degree n (if some `b = -m` with `m <= n` the function is undefined: condition `hyper-undefined`, `h` unchanged).
* `(hyperexpand e)`: every `hyper` inside `e` that has a formula: 0F0, 1F0, 0F1 (`cos`, `sin`, `cosh`, `sinh`), 1F1 (`erf`, `erfi`, `(exp z - 1)/z`), 2F1 `(1,1;2)` (log), `(1/2,1;3/2)` (atanh, atan), `(1/2,1/2;3/2)` (asin, asinh), `(1,1;3/2)`, `(a,a+1/2;1/2)`, `(a,a+1/2;3/2)`; SFn.2b: `0F1(;b;+-u^2/4) = Gamma(b)(u/2)^(1-b) J/I_(b-1)(u)`, `0F1(;2/3;x^3/9)` and `0F1(;4/3;x^3/9)` give `AiryAi`/`AiryBi` combinations, `2F1(-n, n+1; 1; z) = P_n(1-2z)`; at `z = 1`: Chu-Vandermonde for terminating 2F1 and Gauss `Gamma(c)Gamma(c-a-b)/(Gamma(c-a)Gamma(c-b))` when `Re(c-a-b) > 0` (else no formula, condition recorded). No formula: the `hyper` stays.
* `(hyper-diff h)`: `d/dz pFq(a;b;z) = (prod a / prod b) pFq(a+1;b+1;z)`.
* `(hyper-eval h)`: numeric value (numeric parameters) or `#f`. The series is summed with a proven tail bound `rho_N = |z| (N+B)^p / ((N-B)^q (N+1))`; for p = q+1 only `|z| < 1`, otherwise through `hyperexpand`.
* Heads of SFn.2a (not counted as signatures above): `bessel-j`, `bessel-y`, `bessel-i`, `bessel-k` take order `nu` and argument `x` (half-integer `nu` up to 9/2 is elementary, e.g. `J_{1/2}(x) = sqrt(2/(pi x)) sin x`); `airy-ai`, `airy-bi` and their derivatives `airy-ai-prime`, `airy-bi-prime` (`Ai″ = x·Ai`, so `diff` closes the loop); `legendre-p`, `legendre-q` (integer `n >= 0` gives a polynomial for P). Values come from `eval-num`; printing is `BesselJ(nu, x)`, `AiryAi(x)`, `LegendreP(n, x)` and reads back.
* `(specfun-check lhs rhs vars)`: certificate. `#t`: after `hyperexpand` and `specfun-simplify` the difference is 0. `numeric`: three rational points agree (series with tail bound, Gamma through `eval-num`). `#f`: a point disagrees. `unknown`: no admissible point.
* `(specfun-check-numeric lhs rhs vars)`: the same numeric check without expansion (checks a `hyperexpand` formula against the series).

## Examples

```lisp
(sf-gamma 7/2)
;=> (* 15/8 (^ pi 1/2))

(sf-gamma -1/2)
;=> (* -2 (^ pi 1/2))

(sf-beta 2 3)
;=> 1/12

(specfun-simplify '(/ (gamma (+ z 3)) (gamma (+ z 1))))
;=> (* (+ 1 z) (+ 2 z))

(specfun-simplify '(* (gamma 1/3) (gamma 2/3)))
;=> (* 2/3 (^ 3 1/2) pi)

(sf-digamma 1)
;=> (* -1 euler-gamma)

(hyperexpand '(hyper (1 1) (2) z))
;=> (* -1 (^ z -1) (log (+ 1 (* -1 z))))

(hyperexpand '(hyper (1/2 1/2) (2) 1))
;=> (* 4 (^ pi -1))

(hyper-series '(hyper (1 1) (2) z) 3)
;=> (+ 1 (* 1/2 z) (* 1/3 (^ z 2)) (* 1/4 (^ z 3)))

(specfun-check '(hyper (1 1) (2) z) '(* (^ z -1) (log (+ 1 (* -1 z)))) 'z)
;=> #f

(specfun-check-numeric '(hyper (1/2 1) (3/2) (^ z 2)) '(* (^ z -1) (atanh z)) 'z)
;=> numeric
```

## Notes

* `eval-num` lacks `cosh`, `sinh`, `atanh`, `asinh`, `factorial`; `hyper-eval` and the checks rewrite them first. Gamma of a negative non-integer is numeric (sign by reflection).
* Gamma at other rationals (1/3) stays a symbol. 2F1 at `|z| = 1` without a formula is `unknown`; pFq with p > q+1 is not evaluated.
