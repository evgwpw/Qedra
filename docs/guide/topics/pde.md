# Topic: pde

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=>` after a form is the printed result it must give. Partial differential equations (step PDE.0, the frame). The unknown is `(u x t)` or `(u x y z)`; derivatives are nested `(diff (diff (u x t) x) x)`, and the subscript notation `u_t`, `u_xx`, `u_xt` is read as derivatives of the declared unknown inside `pdsolve`, `pde-classify`, `pdsolve-check` (elsewhere `u_xx` is an ordinary name). No solving methods yet: `pdsolve` classifies and answers `unknown` with the methods that would fit; the main use is **checking a ready answer** with `pdsolve-check`. In the `math` tool: `pde_check(u_t = u_xx, u(x,t) = exp(-t)*sin(x), u(x,t), u(0,t) = 0)`, `pdsolve(...)`, `pde_classify(...)`, domains as `[x, 0, L]`.

## Functions

* `(pdsolve eq (u x t) cond ... [:domain ((x 0 L) (t 0 inf))] [:coords c] [:method m])`: dispatcher. Result `(pde-solution :type ... :status ok|unknown|inconsistent ... :hint (methods) :comment text)`. Provably inconsistent conditions (two values for the same expression at the same or a nested point) give `inconsistent`; otherwise `unknown` plus `:hint` (`separation`, `characteristics`, `dalembert`, `transform`, `green`, `similarity`). It never says "no solution".
* `(pde-classify eq (u x t) cond ... [:coords c])`: `(pde-class :vars ... :order ... :linear ... :quasilinear ... :homogeneous ... :const-coeff ... :type elliptic|parabolic|hyperbolic|first-order|unknown :pattern heat|wave|laplace|poisson|helmholtz|biharmonic|transport|burgers|... :coords ... :bc-homogeneous ...)`. Second order, two variables: type by `b^2 - ac`; a variable-coefficient sign that `sign-of` cannot decide gives `unknown`; a square is accepted with the condition coefficient `/= 0` in `conditions`.
* `(pde-class-ref class key)`: one field of the classification, for example `:type`, `:order`, `:pattern`.
* `(pdsolve-check eq sol (u x t) cond ... [:domain ...])`: certificate of a given answer `sol = (= (u x t) expr)`: `#t` (the residual after substitution is exactly 0, conditions hold), `numeric` (0 at sample points of the domain), `#f` (a nonzero value found), `unknown` (data `f(x)` in a condition, a series, no verdict). Arbitrary functions `F(x - c t)`: if the residual cancels symbolically the answer holds for any `F` (`#t`); otherwise trial functions (sin, exp, cubic) give `numeric` or `#f`.
* `(pdsolve-check-detail eq sol (u x t) cond ...)`: the same, in detail: `(verdict residual ((condition verdict) ...))`; this is what the `certificate` field of the tools `math`/`evaluate` uses (kind `pde`).
* `(pde-subst e (u x t) rhs)`: substitute `(u x t) -> rhs` and evaluate every derivative (the PDE analogue of `ode-subst`).
* `(pde-status r)`, `(pde-solutions r)`, `(pde-term r)`, `(pde-field r key)`: accessors of the answer object.
* Conditions (arguments after the unknown): `(= (u 0 t) 0)` (point notation), `(= (at (diff (u x t) x) (= x L)) 0)` (Neumann), `(= (u_x 0 t) v)`, `(bounded (u x t) (= x 0))` (the limit at the point is finite).

## Examples

```lisp
(pdsolve-check '(= u_t u_xx) '(= (u x t) (* (exp (* -1 t)) (sin x))) '(u x t))
;=> #t

(pdsolve-check '(= u_tt (* (^ c 2) u_xx)) '(= (u x t) (+ (F (+ x (* -1 c t))) (G (+ x (* c t))))) '(u x t))
;=> #t

(pdsolve-check '(= u_tt (* (^ c 2) u_xx)) '(= (u x t) (+ (F (+ x (* -2 c t))) (G (+ x (* c t))))) '(u x t))
;=> #f

(pdsolve-check '(= u_t u_xx) '(= (u x t) (* (exp (* -4 t)) (sin (* 2 x)))) '(u x t) '(= (u 0 t) 0) '(= (u pi t) 0))
;=> #t

(pde-class-ref (pde-classify '(= u_t (* a u_xx)) '(u x t)) :type)
;=> parabolic

(pde-class-ref (pde-classify '(= u_tt (* (^ c 2) u_xx)) '(u x t)) :pattern)
;=> wave

(pde-status (pdsolve '(= u_t u_xx) '(u x t) '(= (u 0 t) 0) '(= (u 0 t) 1)))
;=> inconsistent
```

## Pitfalls

* `unknown` from `pdsolve` is not "no solution": PDE.0 has no solving methods, only classification and `:hint`.
* `#t` means the residual is exactly zero (any arbitrary `F`, `G`); `numeric` is weaker; `#f` is a proof of a mismatch at a point; `unknown` for a condition with data `f(x)` says the data could not be compared, not that the answer is wrong.
* Series answers `(sum ... n 1 inf)` are not checked yet (`unknown`); boundary conditions are checked pointwise, convergence is not.
* Arbitrary functions of one argument (`F`, `G`, `f`, `phi`) are recognised by name when the name is not a library function (`psi` is the digamma function: use another name).
* The variable `inf` in a domain bound is infinity; the time variable `t` on `(0, inf)` is the normal case and does not count as an infinite space domain.
