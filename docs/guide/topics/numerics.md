# Topic: numerics

Certified numerics: exact rational interval arithmetic, root isolation, integrals and sums with guaranteed enclosures. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. An interval is `(iv lo hi)` with EXACT rational ends; the results below are mathematically guaranteed (unlike `eval-num`, which is a float estimate). Ends of transcendental enclosures print as huge fractions: compare them (`iv-contains?`, `iv-subset?`) instead of reading them.

## Functions

* `(iv lo hi)`: the interval `[lo, hi]`, `lo <= hi` exact; `(iv-lo X)`, `(iv-hi X)`, `(iv-width X)`, `(iv-mid X)`, `(iv-pi)`, `(iv-e)`.
* `(iv+ a b ...)`, `(iv- a b)`, `(iv* a b ...)`, `(iv/ a b)` (the divisor must not contain 0), `(iv^ X n)`, `iv-neg`, `iv-sqrt`, `iv-exp`, `iv-log`, `iv-sin`, `iv-cos`, `iv-atan`: arithmetic and functions with outward rounding of the result.
* `(iv-contains? X q)`: is the exact number `q` inside; `(iv-subset? A B)`: is `A` inside `B`.
* `(iv-eval e x X)`: an enclosure of the values of expression `e` for `x` in `X` (it may be wider than the true range: the dependency problem); `(iv-refine e x X tol)`: subdivides until the width is at most `tol`.
* `(isolate-roots p x)`: disjoint rational intervals, each containing exactly one real root of the polynomial `p`; `(refine-root p x I tol)`: shrinks one interval.
* `(certified-roots f x a b tol)`: roots of a general `f` on `[a, b]`: `(certified unresolved)`, certified intervals each with exactly one root, and sub-intervals that could not be decided.
* `(certified-integral f x a b tol)`: an interval containing `integral_a^b f dx`, width about `tol` or less.
* `(certified-sum term k a tol)`: an interval for `sum_{k=a}^inf term` for positive decreasing terms (tail bound by comparison).

## Examples

```lisp
(iv+ (iv 1 2) (iv 3 4))
;=> (iv 4 6)

(iv* (iv -1 2) (iv -3 1))
;=> (iv -6 3)

(iv-eval '(+ (^ x 2) x) 'x (iv 1 2))
;=> (iv 2 6)

(length (isolate-roots '(- (^ x 2) 2) 'x))
;=> 2

(iv-subset? (certified-integral '(exp (* -1 (^ x 2))) 'x 0 1 1/1000) (iv 7468/10000 7469/10000))
;=> #t

(iv-subset? (certified-integral '(/ 1 x) 'x 1 2 1/100) (iv 693/1000 694/1000))
;=> #t

(iv-contains? (certified-sum '(/ 1 (^ k 2)) 'k 1 1/100) 1644934/1000000)
;=> #t

(iv-subset? (iv-pi) (iv 314159/100000 314160/100000))
;=> #t
```

## Pitfalls

* An enclosure is a proof, but a wide one is useless: a small `tol` costs time; start with `1/100`. The answer states "the value lies in this interval", never "equals the midpoint".
* `iv-eval` of an expression where a variable occurs twice (`x - x`) is wider than the exact range: split the interval with `iv-refine`.
* Functions `iv-sqrt`, `iv-log` need a non-negative resp. positive interval, `iv/` a divisor without zero: otherwise an error, not an infinite interval.
* `certified-integral` needs a bounded integrand on `[a, b]` (interval evaluation over a pole fails or gives a useless width); improper integrals are not handled.
* `certified-sum` is only for positive decreasing terms (partial sum plus a rigorous tail bound by the integral test or a geometric majorant); for exact sums use card `sums`.
* `certified-roots` uses Krawczyk's test: cells it cannot prove (for example a double root) go to the second list "unresolved": report them as undecided, not as "no root".
* `(eval-num e)` is an uncertified float: use it for display, never as a certificate. The same bound with `sum` or `integrate` certificates (`certificate: true`) is symbolic, not interval-based.

## Also

`iv?`, `iv-neg`, `iv-sqrt`, `iv-exp`, `iv-log`, `iv-sin`, `iv-cos`, `iv-atan`, `iv-lo`, `iv-hi`, `iv-mid`, `iv-e`.
