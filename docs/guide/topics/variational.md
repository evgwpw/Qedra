# Topic: variational

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. A functional is the integral of L dx. Write the unknown as `(y x)` and its derivatives as `(diff (y x) x)`; expressions are data, so quote them. Results `var-solution`/`var-classification` are lists `(tag :key value ...)`, read with `(var-field r :key)`; `(var-status r)` is the status.

## Functions

* `(euler-lagrange L yx)`: the Euler-Lagrange equation `(= lhs 0)`. `yx` is `(y x)`. Higher derivatives in `L` give the Euler-Poisson equation. A list `((y x) (z x))` gives a list of equations. Several variables `(u x y)` give the Euler-Ostrogradsky PDE. Radicals are cleared, so the result is a polynomial in the derivatives.
* `(var-first-integrals L yx)`: list of first integrals `(= F C1)`: the energy `L - y' dL/dy'` if L has no x (Beltrami identity; with radicals squared and the constant renamed), the momentum if L has no y.
* `(var-noether L yx)`: `(x-translation H)` the energy, `(shift y p)` the momentum.
* `(var-natural-conditions L yx)`: conditions `(= p_k 0)` of a free end, expressions in x. `(var-transversality L yx phi)`: for an end sliding on `y = phi(x)`.


* `(variational-solve L yx a b conds)`: extremal of the integral over [a, b] through `dsolve`. `conds`: `(= (y p) v)` for fixed ends; an end without a condition is free (natural conditions used). Result: `:status` (`ok`, `family`, `unknown`), `:kind` (`minimum` or `extremal`), `:extremal`, `:equation`, `:check`, `:classification`.
* `(var-check L yx a b conds cand)`: certificate for a candidate `y = f(x)`: it is substituted into the equation and the boundary conditions; `#t`, `numeric`, `#f`. A fake candidate gives `#f`.
* `(var-classify L yx a b extremal fixed?)`, `(var-legendre ...)`, `(var-jacobi ...)`, `(var-convex? L yx)`: `minimum` only when L is convex in (y, y') (Hessian positive semidefinite, global) or the Legendre condition is strict and there is no conjugate point (both ends fixed, weak). Otherwise `extremal`. `var-jacobi`: `none`, `(conjugate c)` or `unknown`.
* `(var-isoperimetric L G yx a b conds ell)`: minimum of the integral of L with the integral of G equal to `ell`: Euler equation for `L + lam G` (symbol `lam`), constants from the ends, `lam` from the constraint. `(var-isoperimetric-check L G yx a b conds ell cand lam)`: certificate of a candidate with its `lam`.
* `(var-check-first-integral F yx xt yt t)`: `(status value)`: `F` is constant along the parametric curve (cycloid, circle).

## Examples

```lisp
(euler-lagrange '(+ (^ (diff (y x) x) 2) (* -1 (^ (y x) 2))) '(y x))
;=> (= (+ (diff (diff (y x) x) x) (y x)) 0)

(euler-lagrange '(+ (^ (diff (u x y) x) 2) (^ (diff (u x y) y) 2)) '(u x y))
;=> (= (+ (diff (diff (u x y) x) x) (diff (diff (u x y) y) y)) 0)

(var-first-integrals '(sqrt (/ (+ 1 (^ (diff (y x) x) 2)) (y x))) '(y x))
;=> ((= (* (+ 1 (^ (diff (y x) x) 2)) (y x)) C1))

(var-field (variational-solve '(sqrt (+ 1 (^ (diff (y x) x) 2))) '(y x) 0 1 '((= (y 0) 0) (= (y 1) 1))) :extremal)
;=> (= (y x) x)

(var-jacobi '(+ (^ (diff (y x) x) 2) (* -1 (^ (y x) 2))) '(y x) 0 (* 2 'pi) '(= (y x) (sin x)))
;=> (conjugate 3.141592653589793)

(var-check '(^ (diff (y x) x) 2) '(y x) 0 1 '((= (y 0) 0) (= (y 1) 1)) '(^ x 2))
;=> #f
```

## Pitfalls

* Write `L` with `(y x)` and `(diff (y x) x)`; a bare `y` is a parameter. The symbol `lam` is reserved in isoperimetric problems.
* The catenary and Dido cannot be solved in closed form (`status` is `family`/`unknown`); check a candidate with `var-check` or `var-isoperimetric-check`.
* Only value conditions `(= (y p) v)`; for order above one the free derivatives at the ends get natural conditions.
