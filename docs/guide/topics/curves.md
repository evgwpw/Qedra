# Topic: curves

Plane algebraic curves `F(x, y) = 0` with `F` a polynomial over ℚ. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Plotting curves: card `plots` (`plot-implicit`). Elliptic integrals and integration on curves: card `integration`.

## Functions

* `(singular-points F x y)`: groups of singular points (affine and at infinity); each group is an association list `((point x y) (multiplicity m) (branches b) (delta d) (ordinary #t|#f) (tangents (...)) (conjugates k) (at affine|infinity))`.
* `(curve-singular? F x y px py)`: is the point singular (certificate `F = F_x = F_y = 0`).
* `(curve-genus F x y)`: `(genus g)`, `(reducible (F1 ...))` or `unknown`; genus = (d-1)(d-2)/2 minus the sum of the deltas.
* `(parametrize-curve F x y t)`: a rational parametrization `(x(t) y(t))` for genus 0, `(not-rational g)` otherwise; `(parametrization-check F x y par t)`: independent check `#t`/`#f` that `F(par) = 0` identically.
* `(parametrize-curve-inverse F x y t par)`: `t` as a function of `(x, y)` for pencil parametrizations, else `unknown`; `(parametrization-inverse-check F x y par inv t)`.
* `(newton-polygon F x y)`: lower edges of the Newton polygon at the origin.
* `(puiseux F x y n)`: Puiseux branches at `x = 0`: a list of `(q (c1 e1) (c2 e2) ...)`, meaning `y = sum ci x^ei`, `q` the ramification index, up to `n` terms.
* `(puiseux-check F x y br n)`: independent check `#t`/`#f` by substituting `x = s^q`; `(puiseux-terms br)`: the `(c e)` list; `(puiseux-rational F x y n)`: Duval groups `((q terms) multiplicity)` with rational coefficients.
* `(algebraic-series F x y a n)`: a Puiseux series object of the branch at `x = a`; `(algebraic-series->expr s)`: it as an expression.

## Examples

```lisp
(curve-genus '(- (^ y 2) (+ (^ x 3) (* -1 x) 1)) 'x 'y)
;=> (genus 1)

(singular-points '(- (^ y 2) (^ x 3)) 'x 'y)
;=> (((point 0 0) (multiplicity 2) (branches 1) (delta 1) (ordinary #f) (tangents (horiz)) (conjugates 1) (at affine)))

(parametrize-curve '(- (^ y 2) (^ x 3)) 'x 'y 't)
;=> ((^ t 2) (^ t 3))

(parametrize-curve '(- (^ y 2) (+ (^ x 3) (* -1 x) 1)) 'x 'y 't)
;=> (not-rational 1)

(puiseux '(- (^ y 2) (+ x (^ x 2))) 'x 'y 3)
;=> ((2 ((1 1/2) (1/2 3/2) (-1/8 5/2))) (2 ((-1 1/2) (-1/2 3/2) (1/8 5/2))))

(puiseux-check '(- (^ y 2) (^ x 3)) 'x 'y (car (puiseux '(- (^ y 2) (^ x 3)) 'x 'y 3)) 3)
;=> #t

(algebraic-series->expr (algebraic-series '(- (^ y 2) (+ 1 x)) 'x 'y 0 3))
;=> (+ 1 (* 1/2 x) (* -1/8 (^ x 2)) (* 1/16 (^ x 3)))
```

## Pitfalls

* `F` must be a polynomial in `x` and `y` over ℚ; `unknown` is returned when the analysis cannot be completed (not "no singular points").
* `singular-points` takes about half a second on a lemniscate and much longer for large degrees: raise `timeout_s`.
* Puiseux with complex embeddings of degree >= 3 uses floating-point (`double`) tails: deep recursion can fail the self-check, and the call then reports an honest error. Always run `puiseux-check`.
* Duval grouping merges conjugate branches only for ramification `q <= 6`.
* `(not-rational g)` for `g >= 1`: there is no rational parametrization; do not search for one.
* Branches are at `x = 0` (shift the curve first); `y` must be the dependent variable of positive degree.

## Also (exported helper)

`puiseux-at` (approximate float value of a branch at a point; a rough estimate only), `algebraic-series?`, `algebraic-series-coeff` (coefficient of the `k`-th term, 1-based, or `#f`).
