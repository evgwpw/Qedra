# Topic: integration

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Data is quoted: `'(* x (exp x))`; infinity is `inf` / `-inf` in Lisp (`∞` only in math syntax).

## Functions

* `(integrate e x)`, `(integrate e x a b)`: indefinite integral of `e` by `x`, or definite (bounds may be `inf`, `-inf`). Unevaluated result `(integrate ...)` means: not found (or not elementary).
* `(int-check F e x)`: `#t` if d/dx `F` = `e` (exact via simplify/together, else numeric at sample points), `#f` otherwise.
* `(int-check-how F e x)`: how it was proved: `simplify`, `together` (exact), `numeric` (sample points), `bad` (wrong).
* `(int-check-rubi F e x)`, `(int-check-rubi-how F e x)`: the same for the Rubi engine, cheapest check first (`simplify`, numeric, `together` last), so rejected candidates stay cheap; `integrate` keeps `int-check`.
* `(risch-integrate e x)`: the Risch algorithm only (exp/log/atan towers, algebraic curves of genus 0 and some more): antiderivative, `F + (integrate R x)` with a proved non-elementary rest, or `#f` = "does not know".
* `(risch-nonelementary? e x)`: `#t` only when it is PROVED that no elementary antiderivative exists; `#f` means "not proved", not "elementary".
* `(risch-special e x)`: the antiderivative through a special function (`erf`, `erfi`, `Ei`, `li`, `Si`) for the common non-elementary cases, else `#f`.
* `(int-has-integrate? e)`: `#t` if an answer still contains an unevaluated `(integrate ...)` (a partial answer).
* `(simplify e)`, `(diff x e)`: to rewrite or differentiate answers; in Lisp the VARIABLE comes first in `diff` (the data form of a derivative inside an equation is `(diff (y x) x)`).

## Examples

```lisp
(integrate '(* x (exp x)) 'x)
;=> (+ (* x (exp x)) (* -1 (exp x)))

(integrate '(^ x 2) 'x 0 1)
;=> 1/3

(integrate '(/ 1 (+ (^ x 2) 1)) 'x '-inf 'inf)
;=> pi

(int-check '(* (+ -1 x) (exp x)) '(* x (exp x)) 'x)
;=> #t

(int-check-how '(* x x) '(* x x) 'x)
;=> bad

(risch-nonelementary? '(exp (^ x 2)) 'x)
;=> #t

(integrate '(/ (exp x) (sqrt (+ 1 (exp (* 2 x))))) 'x)
;=> (log (+ (^ (+ 1 (exp (* 2 x))) 1/2) (exp x)))

(risch-special '(exp (* -1 (^ x 2))) 'x)
;=> (* 1/2 (^ pi 1/2) (erf x))
```

## Pitfalls

* In MCP, tool `integrate` returns `status: nonelementary` for a proved non-elementary integrand; in Lisp ask `risch-nonelementary?`. `unknown` / unevaluated `(integrate ...)` without that proof only means "not found": never say "no antiderivative".
* For common cases the tool `note` already names the special function (`exp(-x^2)` gives `(sqrt(pi)/2) erf(x)`, `exp(x^2)` erfi, `exp(x)/x` Ei, `1/log x` li, `sin x/x` Si); in the math tool `risch_special(f, x)` returns it. `integrate` returns no `erf`/`Ei`/`li`; its last fallback, Rubi rules (6 s), may give `hypergeometric-2f1`/`elliptic-f`, never for a proved non-elementary integrand.
* `risch-special` output is for the user; `diff` knows `erf` but not `Ei`, `li`, so do not rely on `int-check` for those.
* A PARTIAL answer such as `x*log(log(x)) - integrate(1/log(x), x)` has `status: answer` plus a warning about the unevaluated integral; the remainder is proved non-elementary and listed in `conditions` as `risch-nonelementary(...)`. Integration steps: `steps: "full"` shows the technique (`int-by-parts`, `int-substitution`, `int-partial-fractions`, `risch`, ...).
* Radical over an exp/log tower (`x*sqrt(e^x+1)`, `e^x*sqrt(x+1)`, `log(x)/sqrt(1+log x)`): a genus-0 curve is rationalized and the transcendental Risch algorithm runs in the parameter. `integrate` gives the answer or a proved `nonelementary`; genus >= 1 with a surviving `x` (`x*e^x*sqrt(e^(3x)+1)`) stays `unknown`. A 10 s budget turns a stalled step into `unknown`.
* The antiderivative is defined up to a constant and may look different from a textbook form: check with `int-check` (or `certificate: true` in the MCP tool), not by comparing text.
* A float (`0.5`) makes the answer inexact; use `1/2`.
* Hidden zero coefficients are removed before the Risch step (`(log 6 - log 2 - log 3) e^(x^2)` integrates to 0). A constant that is probably but not provably zero (`const-zero?` gives `unknown`) makes Risch answer "not known": no answer or "non-elementary" proof rests on a guess.
* Definite integrals with a singularity inside `(a, b)` are not substituted blindly: `(integrate '(^ x -2) 'x -1 1)` stays unevaluated (it diverges). Since DI.3 they go to `definite-integral`: divergence is the condition `(divergent form "reason")`; improper results use certificate kind `definite` (`definite-check`).
* Mixed case (a radical over `exp`/`log`, e.g. `sqrt(exp(x)+1)`, `exp(x)/sqrt(1+exp(2x))`, `1/(x log(x) sqrt(log(x)+2))`): `integrate` substitutes `t = exp(a x)`, `log(a x + b)` or `x^(1/n)` and integrates in `t`; a proved non-elementary verdict in `t` is transferred only when the reduced integrand has no `x` left. `x*sqrt(exp(x)+1)` or `exp(x)*sqrt(x+1)` stay "not found", not "non-elementary".
* Symbols are arbitrary complex numbers unless declared; parameters (`a`) are generic, see `conditions`.
* Parameters (`1/(x^2+a)`, `x^a`, `exp(a x)`): unless `declare` decides the sign/zero, the answer is `(piecewise ((cond ans) ...))`, checked by `(int-piecewise-check pw e x)`; plain data, `diff` ignores it.

## Also (exported helpers)

Elliptic integrals (values, arguments `phi` and modulus `k`): `elliptic-f`, `elliptic-e`, `elliptic-pi`, `elliptic-k`, `elliptic-ec`; the integrator reduces elliptic integrands with `int-elliptic`. Chebyshev binomial integrals `x^m (a + b x^n)^p`: `int-chebyshev`, `int-cheb-form`, `int-cheb-elementary?`. Extension points of the integrator: `int-rule`, `int-add-strategy`, `int-guard`; `int-num` evaluates a limit value to a number or `#f`. Algebraic-curve integration internals (integral bases, Hermite reduction, places, divisors, torsion) are listed in `not-covered.txt`.
