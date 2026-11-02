# Topic: calculus

Derivatives, limits, series. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Math language: `diff(f, x)`, `limit(f, x, a)`, `series(f, x, a, n)`. Integrals: card `integration`; Puiseux series of algebraic functions: card `curves`.

## Functions

* `(diff x e)`: derivative of `e` by `x`; THE VARIABLE COMES FIRST (`(diff e x)` is an error). Unknown functions stay: `(diff 'x '(f x))` is `(diff (f x) x)`.
* `(limit e x a [side])`: `a` is a number, `inf` or `-inf`; `side` is `'plus` or `'minus`. Results: a value, `inf`, `-inf`, `undefined` (sides differ), or the unevaluated `(limit ...)` when not decided. Uses series, L'Hopital and, for exp/log towers, Gruntz.
* `(series e x a n)`: Laurent series in `(x - a)` up to `O((x - a)^n)`, a `series` object (prints `1 + x + ... + O(x^n)`).
* `(taylor e x a n)`: the polynomial part only (terms of degree < n), a plain expression.
* `(series->expr s)`: a series object as an expression without `O`; `(series-coeff s k)`: coefficient of `x^k`; `(series-order s)`: the truncation order.
* `(gruntz-limitinf e x)`: limit at `+inf` by Gruntz's algorithm: value, `inf`, `-inf`, or `#f` (unknown).
* `(gruntz-mrv e x)`: the most rapidly varying subexpressions (list) or `#f`; `(gruntz-sign e x)`: sign at `+inf` (`1`, `-1`, `0`, `#f`); `(gruntz-compare a b x)`: `<`, `=`, `>` or `#f`; `(gruntz-leadterm e x)`: leading term `(c0 e0)` or `#f`.

## Examples

```lisp
(diff 'x '(^ x x))
;=> (* (^ x x) (+ 1 (log x)))

(limit '(^ (+ 1 (/ 1 x)) x) 'x 'inf)
;=> (exp 1)

(limit '(- x (log (+ 1 (exp x)))) 'x 'inf)
;=> 0

(limit '(/ 1 x) 'x 0 'minus)
;=> -inf

(limit '(/ 1 x) 'x 0)
;=> undefined

(taylor '(log (+ 1 x)) 'x 0 4)
;=> (+ x (* -1/2 (^ x 2)) (* 1/3 (^ x 3)))

(series-coeff (series '(exp x) 'x 0 5) 3)
;=> 1/6

(gruntz-sign '(- (exp x) x) 'x)
;=> 1
```

## Pitfalls

* `diff` takes the variable first; `integrate` takes the expression first. Do not mix them.
* An unevaluated `(limit ...)` or `status: unknown` means "not decided", not "does not exist". `undefined` is a proved answer: the one-sided limits differ.
* A limit whose answer depends on the sign of an undeclared parameter (`a^x / x`) stays unevaluated: `declare` the parameter first.
* `series` raises an error for fractional powers (`sqrt(x)` at 0): that needs Puiseux series (card `curves`, `algebraic-series`).
* Limits at `-inf` and non-standard points are reduced by substitution `x -> 1/t`; Gruntz handles only `+ * ^ log exp` of the variable.
* `floor` and a bare `sin x` at infinity are not decided (the result stays unevaluated); `sin x / x` at `inf` works.
* Certificates: `diff`, `limit`, `series` have none (`kind: none`). To check a limit numerically, evaluate near the point with `eval-num`.

## Also

`lim-add`, `ser-*` helpers (`ser-bad?`, `ser-lg`, `ser-var`, `ser-val`, `ser-cs`, `ser-compute`, `ser-precision-err?`, `ser-with-logx`), the series type `series?`.
