# Topic: plots

Two-dimensional plots as SVG text, plus a numeric feature report to check a plot without looking at it. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Use the tool `evaluate`; nothing is written to disk: show the returned string as `.svg` or save it.

## Functions

* `(plot f x a b &rest opts)`: SVG string of the curve `y = f(x)` on `[a, b]`; `f` is a quoted expression, `a`, `b` may be expressions (`'(* 2 pi)`).
* `(plot-svg specs opts)`: several curves in one picture; `specs` is a list of `(f x a b)`, `(:parametric xe ye t a b)` or `(:polar r th a b)`; `opts` is a list of option pairs (may be `'()`).
* `(plot-implicit F x y x0 x1 y0 y1 &rest opts)`: the curve `F(x, y) = 0` in the window `[x0, x1] x [y0, y1]` (marching squares; singular points are marked and the branches meet there).
* `(plot-info f x a b)` or `(plot-info spec)`: features without rendering: `(:segments n :asymptotes (...) :holes (...) :jumps (...) :yrange (lo hi) :one-sided ((c left|right) ...))`; implicit curves add `:singular`.
* `(plot-sample f x a b opts)`: the sampled polylines, each a list of `(x y)` points clipped to the y range.
* `(plot-contour f x y x0 x1 y0 y1 &rest opts)`: contour lines `f(x, y) = c` (levels automatic or `:levels (...)`); spec `(:contour f x y x0 x1 y0 y1 :levels (...))` in `plot-svg`.
* `(plot-certificate f x a b &rest opts)`: rigorous interval enclosure per cell: `(:tol t :cells ((x0 x1 status lo hi) ...))`; `(plot-certificate-check f x a b cert)` re-verifies it (`#t`/`#f`).
* `(plot3d f x y x0 x1 y0 y1 &rest opts)`: 3D surface `z = f(x, y)` as SVG (painter's algorithm, height colors, `:azimuth :elevation :perspective :mesh :floor-contours :n :zmin :zmax`); `(plot3d-svg specs opts)` with `(:surface ...)` / `(:parametric-surface fx fy fz u u0 u1 v v0 v1)` specs; `(plot3d-info f x y x0 x1 y0 y1)` → `(:quads :holes :zrange :clipped ...)`; `(plot3d-points spec &rest opts)` the grid vertices `(X Y Z)` or `#f`.
* `(plot-ode eq yx (x a b) cond ...)`: plot of an ODE solution (language `plot_ode(eq, y(x), [x, a, b], y(x0) = v, ...)`): an exact particular `dsolve` solution is one curve; a general solution (constants `C1`, ...) is a family; with no formula but with conditions, the numeric RK45 curve (checked by the residual; a failed run is drawn up to the break); otherwise an error says what to set. Specs: `(:ode eq yx a b (conds))`, `(:points ((x y) ...))`.
* `(plot-direction-field f x y x0 x1 y0 y1 &rest opts)`: direction field of `y' = f(x, y)`; `:curves ((x y) ...)` adds integral curves. Spec `(:field f x y x0 x1 y0 y1)`.
* Numeric Cauchy problem (module `ode-numeric`): `ode-numeric` solves an ODE of order n, linear in the highest derivative, by Dormand-Prince 5(4) (`eq`, `yx`, `(x a b)`, n conditions); `ode-numeric-status` is `ok` or `failed` (blow-up, singularity: `ode-numeric-reason`), `ode-numeric-points` rows `(x y y' ...)`, `ode-numeric-field` any key; `ode-numeric-check` re-checks a table by the residual (`#f` for a fake); `ode-numeric-rhs-fn` gives the system right-hand side.
* Option `:certified #t` (for `plot`, `plot-svg`, `plot-info`): honest mode; cells where the enclosure stays wide (poles, narrow spikes, unsupported functions) are marked uncertain instead of guessed; `plot-info` then reports `:certified`, `:uncertain`, `:enclosure`.

## Options

Keywords after the required arguments: `:width :height :title :legend :grid :xmin :xmax :ymin :ymax :n` (number of samples; grid size for implicit curves) and `:aspect` (`:equal` is the default for parametric, polar and implicit curves, `:auto` for `y = f(x)`). Poles and jumps are not joined by a line; removable singularities are drawn as hollow circles.

## Examples

```lisp
(substring (plot '(sin x) 'x 0 '(* 2 pi) :title "sin") 0 4)
;=> "<svg"

(nth (plot-info '(/ 1 x) 'x -2 2) 3)
;=> (0.0)

(nth (plot-info '(/ (sin x) x) 'x -3 3) 5)
;=> (0.0)

(nth (plot-info '(exp (/ 1 x)) 'x -1 1) 11)
;=> ((0.0 right))

(string-contains? (plot-svg (list '((^ x 2) x -2 2) '(:parametric (cos t) (sin t) t 0 (* 2 pi))) '()) "<svg")
;=> #t

(string-contains? (plot-implicit '(- (^ x 2) (^ y 2) 1) 'x 'y -3 3 -3 3) "<svg")
;=> #t

(string-contains? (plot-ode '(= (diff (y x) x) (y x)) '(y x) '(x -3 3)) "C1 = 2")
;=> #t

(string-contains? (plot-ode '(= (diff (y x) x) (+ (^ x 2) (sin (y x)))) '(y x) '(x -2 2) '(= (y 0) 1)) "(RK45)")
;=> #t

(nth (plot-info '(:field (- x y) x y -3 3 -3 3)) 1)
;=> 280

(define nr (ode-numeric '(= (diff (y x) x) (y x)) '(y x) '(x 0 1) '(= (y 0) 1)))

(ode-numeric-status nr)
;=> ok

(ode-numeric-check '(= (diff (y x) x) (y x)) '(y x) (map (lambda (p) (list (car p) (car p))) (ode-numeric-points nr)))
;=> #f
```

## Pitfalls

* The values in `plot-info` are numeric (sampled), not proofs: a pole closer than the sampling step (about 1/193 of the window) can be missed; a narrow feature needs a narrower window.
* `floor` and `round` are not evaluated numerically (the plot is empty); tangency points of an implicit curve without a sign change are not found.
* Poles stretch the y range: the range is clipped by a robust rule (Tukey fence), so the picture may not show the full height near an asymptote. Set `:ymin`/`:ymax` to see more.
* Implicit plots are drawn from a 120 x 120 grid by default; use `:n 60` for a fast draft. There are no 3D plots.
* The SVG can be long (several KB): do not print it into the chat; pass it to a viewer or save it as a file.

## Reading plot-info

The result is a property list: the value of a key is the element right after it (`nth` indexes: `:asymptotes` 2, `:holes` 4, `:jumps` 6, `:yrange` 8, `:one-sided` 10; the value is index + 1). `:one-sided` entries `(c right)` mean a pole at `c` seen from one side only (`exp(1/x)` at 0).
