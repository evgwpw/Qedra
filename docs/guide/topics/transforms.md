# Topic: transforms

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Expressions are data: quote them. The Heaviside step is `(heaviside u)` = theta(u), the Dirac delta is `(dirac u)`, an unknown function is written `(f t)`. Variable order differs: `(laplace f t s)` (time first), `(inverse-laplace F s t)` (frequency first).

## Functions

* `(laplace f t s)`: the Laplace transform F(s) of f(t). Table (1, t^n, t^a, e^(at), sin, cos, sinh, cosh, theta, delta) plus rules: linearity, frequency shift, time shift `theta(t-a) f(t-a)` gives `e^(-as) F`, multiplication and division by t, derivative, integral `(integrate g u 0 t)`, convolution `(convolve f g t)`; otherwise a direct integral. Not found: the unevaluated `(laplace f t s)` (not an error).
* `(inverse-laplace F s t)`: inverse transform for t > 0. Rational F by `apart` over Q (repeated roots, irreducible quadratics as exp times cos/sin or cosh/sinh, roots in Q(sqrt d), higher-degree factors as `root-sum`); `e^(-as) G` gives `theta(t-a) g(t-a)`; a constant gives `c (dirac t)`; products of non-rational factors give a `convolve`. Not found: the unevaluated `(inverse-laplace F s t)`.
* `(laplace-check f F t s)`: certificate that L[f] = F: `#t` (equal to an independent direct integral, or to the rules for derivatives and convolutions), `numeric` (equal at sample points by quadrature, weaker), `#f` (different: wrong coefficient, shift sign, missing theta, wrong pole), `unknown`. To check an inverse, pass its result as `f`.
* `(convolve f g t)`: the integral from 0 to t of f(tau) g(t-tau); the unevaluated `(convolve f g t)` when the integral fails or theta/delta occur.
* `(laplace-dsolve eq (y t) conds)`: linear ODE with constant coefficients (right side: polynomials, exp, sin, cos, theta, delta) by the Laplace method; `conds` is a list `(= (y 0) 1)`, `(= (at (diff (y t) t) (= t 0)) 0)`. Missing conditions stay as constants C1 = y(0), C2 = y'(0), ... Returns an `ode-solution` (method `laplace`, `:check` `#t`, `numeric`, `#f` or `unknown`; unsolved: status `unknown`). `(laplace-dsolve-system eqs (x y) t conds)`: systems (C numbering runs over function, then derivative order).
* `(laplace-dsolve-check eq (y t) sol conds)`, `(laplace-system-check eqs funcs t sols conds)`: certificate of a given answer: each interval between theta/delta switch points, initial conditions, continuity and the jump of the top derivative at a delta. `#t`, `numeric`, `#f`, `unknown`.
* `(laplace-volterra eq (y t))`: convolution integral equation, second kind `y = f + lambda * integral(k(t-tau) y(tau))` or first kind, integral written `(integrate h tau 0 t)` or `(convolve k (y t) t)`. Checked by exact substitution, else by quadrature (`numeric`); with theta in the answer the check is `unknown`.
* `(transfer-function eq (y t) (u t))`: W(s) = Y/U at zero initial data; `(impulse-response ...)` = L^-1[W], `(step-response ...)` = L^-1[W/s]; `(transfer-poles W s)`: distinct poles; `(stable? W s)`: all poles Re < 0, by Routh-Hurwitz over Q: `#t`, `#f`, `unknown` (symbolic coefficients).
* `(heaviside x)`: a number gives 0, 1 or 1/2 (at 0); otherwise `(heaviside x)`.
* `(dirac x)`: a nonzero number gives 0; otherwise `(dirac x)`.

## Examples

```lisp
(laplace '(* (^ t 2) (exp (* 3 t))) 't 's)
;=> (* 2 (^ (+ -3 s) -3))

(laplace '(heaviside (- t 1)) 't 's)
;=> (* (^ s -1) (exp (* -1 s)))

(laplace '(diff (f t) t) 't 's)
;=> (+ (* s (laplace (f t) t s)) (* -1 (f 0)))

(inverse-laplace '(/ 1 (* s (+ s 1))) 's 't)
;=> (+ 1 (* -1 (exp (* -1 t))))

(inverse-laplace '(/ (+ s 1) (+ (^ s 2) (* 2 s) 5)) 's 't)
;=> (* (cos (* 2 t)) (exp (* -1 t)))

(inverse-laplace '(/ (exp (* -2 s)) (^ s 2)) 's 't)
;=> (* (+ -2 t) (heaviside (+ -2 t)))

(laplace-check '(sin (* 2 t)) '(/ 2 (+ (^ s 2) 4)) 't 's)
;=> #t

(laplace-check '(sin (* 2 t)) '(/ 2 (+ (^ s 2) 9)) 't 's)
;=> #f

(laplace-check '(/ (sin t) t) '(atan (/ 1 s)) 't 's)
;=> numeric
```

```lisp
(ode-solutions (laplace-dsolve '(= (+ (diff (y t) t) (y t)) (heaviside (- t 1))) '(y t) '((= (y 0) 0))))
;=> ((= (y t) (* (+ 1 (* -1 (exp (+ 1 (* -1 t))))) (heaviside (+ -1 t)))))

(ode-solutions (laplace-dsolve-system '((= (diff (x t) t) (y t)) (= (diff (y t) t) (+ (* -1 (x t)) 1))) '(x y) 't '((= (x 0) 0) (= (y 0) 0))))
;=> ((= (x t) (+ 1 (* -1 (cos t)))) (= (y t) (sin t)))

(ode-solutions (laplace-volterra '(= (y t) (+ t (integrate (* (sin (- t tau)) (y tau)) tau 0 t))) '(y t)))
;=> ((= (y t) (+ t (* 1/6 (^ t 3)))))

(transfer-function '(= (+ (diff (diff (y t) t) t) (* 2 (diff (y t) t)) (* 5 (y t))) (u t)) '(y t) '(u t))
;=> (^ (+ 5 (* 2 s) (^ s 2)) -1)

(stable? '(/ 1 (+ (^ s 2) (* 2 s) 5)) 's)
;=> #t

(laplace-dsolve-check '(= (+ (diff (y t) t) (y t)) 0) '(y t) '(* 3 (exp (* -1 t))) '((= (y 0) 2)))
;=> #f
```

## Pitfalls

* Results are valid for Re s > a (the abscissa) and t > 0; both go to the `conditions` channel. Say so to the user.
* `f(0)` in the derivative rule is the symbolic `(f 0)`; higher derivatives give `(at (diff (f t) t) (= t 0))`. Substitute the given initial values by hand.
* Not covered: periodic functions, derivatives of delta (improper F, a polynomial in s), erf and Bessel functions, higher-degree repeated factors. They give the unevaluated form, never a guess.
* Always run `laplace-check` before presenting a result; `numeric` is weaker than `#t`. A hand-made F must pass it too.
* `theta(t-1) sin t` is not `e^(-s) /(s^2+1)`: the shift needs `sin(t-1)`; the check rejects such fakes.
