# Topic: ode

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Equations are data: quote them. The unknown function is `(y x)`, the derivative is `(diff (y x) x)`, the second one is NESTED: `(diff (diff (y x) x) x)` (not `(diff (y x) x 2)`).

## Functions

* `(dsolve eq yx &rest conds)`: `eq` is an equation `(= lhs rhs)` (an expression alone means `= 0`), `yx` is `(y x)`. Without conditions: the general solution with constants `C1`, `C2`, ...; with conditions: the Cauchy problem. Always returns an `ode-solution` record (never throws on "not solved").
* `(ode-solutions r)`: list of solutions, each `(= (y x) ...)` (or an implicit relation `F(x, y) = C1`); empty list when not solved.
* `(ode-status r)`: `ok`, `unknown`, or a string with the reason (e.g. inconsistent conditions).
* `(dsolve-check eq sol yx)`: independent check, substitutes `sol` into `eq`: `#t` exact, `numeric` (only at sample points), `#f` wrong.
* `(dsolve-conditions-check eq sol yx conds)`: `dsolve-check` plus every initial condition.
* `(ode-order eq y x)`: order = highest derivative of `y`.
* `(ode-linear? eq yx)`, `(ode-const-coeff? eq yx)`, `(ode-autonomous? eq yx)`: classifiers, `#t`/`#f`.
* `(ode-subst e yx rhs)`: substitute `(y x)` by `rhs` and evaluate the derivatives that appear.
* `(dsolve-system eqs funcs t &rest conds)`: linear system `x' = A x + f(t)` with constant `A`. `eqs` is a list of `(= (diff (x t) t) ...)`, `funcs` is `((x t) (y t) ...)`. Returns an `ode-solution` record whose `solutions` are `(= (x t) ...)` per component (real form: `cos`/`sin`, `t^k e^(lt)`); initial conditions as in `dsolve` (`(= (y 0) 1)`) give the Cauchy problem.
* `(dsolve-system-check eqs sol funcs t)`: independent check of a whole system, `#t` / `numeric` / `#f`.
* `(ode->system eq yx)`: an n-th order ODE as a first-order system: `(equations functions)`, functions named `y`, `y1`, `y2`, ...
* `(reduce-order eq yx y1)`: second solution of a linear homogeneous 2nd order ODE from a known one: `y2 = y1 * integral(e^(-integral p)/y1^2)`. `#f` if the result does not pass `dsolve-check`.
* `(dsolve-series eq (y x) [x0] [n] [conds])`: series/Frobenius solution of a linear ODE (order 1-4) with analytic coefficients at `x0` (defaults 0 and 8). Returns a `:type series` record: `:recurrence`, `:series` (general solution `C1*y1 + C2*y2`), `:radius` (distance from `x0` to the nearest other singular point, `inf` if none); at a regular singular point also `:indicial`, `:exponents` (`#f` at an ordinary point); Frobenius branches carry a `log x` term when the indicial roots differ by an integer; `:closed-form` `#t` when the hypergeometric (or elementary) closed form is recognized. Conditions give `:type particular`; an irregular point or a failed certificate gives `status: unknown`; `#f` when not linear. Check a series answer with `(ode-series-check eq sol yx)`.
* Algorithms: `kovacic` (Kovacic for `y'' + a y' + b y = 0`: case 1 (any o(∞)), 2-3 (n=4), Riccati certificate, proved `no-liouvillian`) and `kovacic-check` (independent, rejects fakes).
* Conditions: `(= (y 0) 1)` is `y(0) = 1`; a derivative condition is `(= (at (diff (y x) x) (= x 0)) 0)` i.e. `y'(0) = 0`.

Fallbacks: `ode-drop-y`, `ode-autonomous`.

## Examples

```lisp
(define eq '(= (diff (y x) x) (* 2 (y x))))

(ode-solutions (dsolve eq '(y x)))
;=> ((= (y x) (* C1 (exp (* 2 x)))))

(ode-status (dsolve eq '(y x)))
;=> ok

(ode-solutions (dsolve '(= (diff (y x) x) (y x)) '(y x) '(= (y 0) 2)))
;=> ((= (y x) (* 2 (exp x))))

(ode-solutions (dsolve '(= (+ (diff (diff (y x) x) x) (y x)) 0) '(y x) '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0)))
;=> ((= (y x) (cos x)))

(dsolve-check '(= (diff (y x) x) (y x)) '(= (y x) (* 2 (exp x))) '(y x))
;=> #t

(dsolve-check '(= (diff (y x) x) (y x)) '(= (y x) (* 2 (exp (* 2 x)))) '(y x))
;=> #f

(ode-order '(= (+ (diff (diff (y x) x) x) (y x)) 0) 'y 'x)
;=> 2

(ode-solutions (dsolve-system '((= (diff (x t) t) (y t)) (= (diff (y t) t) (* -1 (x t)))) '(x y) 't))
;=> ((= (x t) (+ (* C1 (cos t)) (* C2 (sin t)))) (= (y t) (+ (* -1 C1 (sin t)) (* C2 (cos t)))))

(dsolve-system-check '((= (diff (x t) t) (y t)) (= (diff (y t) t) (* -1 (x t))))
                     '((= (x t) (cos t)) (= (y t) (sin t))) '(x y) 't)
;=> #f

(ode-solutions (dsolve '(= (* (y x) (diff (diff (y x) x) x)) (^ (diff (y x) x) 2)) '(y x)))
;=> ((= (y x) (* C1 (exp (* C2 x)))))

(ode-solutions (dsolve '(= (+ (diff (diff (y x) x) x) (* 4 (y x))) (sin (* 2 x))) '(y x)))
;=> ((= (y x) (+ (* C1 (cos (* 2 x))) (* C2 (sin (* 2 x))) (* -1/4 x (cos (* 2 x))))))
```

## What is solved, and pitfalls

* Solved: quadratures `y(n) = f(x)`, separable, linear, Bernoulli, homogeneous, exact (with integrating factors), Riccati with a simple particular solution, Clairaut/Lagrange, constant-coefficient linear (order n, resonance with an `x^k` factor and variation of parameters), Euler-Cauchy (n <= 4), linear systems with constant coefficients (`dsolve-system`, real form and Cauchy problem), order reduction with a known solution, equations without `y`, autonomous equations. Singular solutions lost by division are listed in the `singular` field of the record.
* Everything else gives `status: unknown` with an empty solution list: say "not solved", never guess. `unknown` is not "no solution".
* Always run `dsolve-check` before presenting a solution; `numeric` is weaker than `#t`. Never trust a hand-written solution without it.
* A solution may be implicit (`F(x, y) = C1`) or come in several branches (`y = ±...`): iterate over `ode-solutions`.
* Cauchy problem: inconsistent conditions (`y(0) = 1` and `y(0) = 2`) give a status string, not an error; a condition in a non-generic form is not recognised and gives `unknown`.
* In Lisp always write the unknown as `(y x)`: a bare `y` (as in `(= y 1)`) is not an ODE and gives `unknown`.
