# Topic: definite

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=>` after a form is the printed result it must give. Expressions are data: quote them. Variable first after the integrand: `(definite-integral f x a b)`. Bounds are numbers, `inf`, `-inf` (quoted symbols) or constants such as `pi`. The result is a value, `(divergent "reason")` (only when divergence is proven) or `unknown`; a parameter such as `a > 0` is written to the `conditions` channel.

## Functions

* `(definite-integral f x a b)`: improper and proper definite integral. Order of attack: rational `f` on the whole line or a half-line by residues (exact for irreducible factors of degree at most 2, so `1/(1+x^4)` also works; on `(0,inf)` the formula `-sum Res(R log z)`, or half of the line integral for even `f`); `integral_0^{2 pi} R(cos, sin)` by `z = e^(i t)` and the residues in the unit disc; `R(x) cos(w x)`, `R(x) sin(w x)` by Jordan's lemma; tables: Gaussian `x^n e^(-a x^2 + b x)`, `x^p e^(-a x)` (Gamma), Beta `(x-a)^p (b-x)^q`, `x^p (x+c)^(-t)` (`pi/sin(pi a)`), Dirichlet `sin(a x)/x`, Fresnel `sin(a x^2)`, `x^n e^(-a x) cos(b x)`; then convergence analysis and Newton-Leibniz through `integrate` (never for trigonometric integrands). Swapped bounds change the sign.
* `(definite-convergence f x a b)`: `convergent`, `conditional` (Dirichlet test: `g(x) sin(w x)` with `g` decreasing to 0), `(divergent "reason")` or `unknown`. Rational `f`: real poles on `[a,b]` and the degree gap at infinity. Other `f`: limits of `x^p f` at infinity and of `(x-c)^p f` at finite singular points, comparison with `1/x^p`.
* `(definite-feynman f x c a b)`: derivative in a parameter c of the closed parametric answer; keyhole `x^s R(x)` and `log x R(x)` on `(0,inf)`, parametric `1/(x^2+a^2)` (a > 0 as a condition) and `integral_0^{2 pi}` with odd powers of `sin` are also covered.
* `(definite-interior f x a b)`: singular points strictly inside a finite interval (zeros of the denominator after tan/cot/sec/csc become sin/cos, log and even-root arguments that change sign). `#f` none, `unknown`, `(divergent ...)`, or the value summed over sub-intervals. Called by `integrate` before the antiderivative path.
* `(definite-check f x a b v)`: certificate for a claimed value `v`. `#t`: `v` lies in a rigorous enclosure (`certified-integral` on a finite part plus a proven tail: rational `f` by `x = 1/u`, `f = r(x) e^(u(x))` with concave `u` by a geometric bound). `numeric`: only quadrature agrees (oscillatory or singular cases, tail estimated). `#f`: `v` is outside, or the integral diverges. `unknown`: parameters in `f`, or no usable quadrature.
* `(integrate f x a b)`: since DI.3 it routes through this module: infinite bounds that are not provably absolutely convergent, a singularity inside `(a, b)` or a failed antiderivative go to `definite-integral`; proved divergence stays `(integrate ...)` with the condition `(divergent form "reason")` (MCP: status `unknown`, note "diverges"). Proper integrals with a continuous antiderivative keep the antiderivative + one-sided limits path (used last by `definite-integral` through the internal call `(integrate f x a b (quote classic))`).
* `(limit f x a)`: limit at a point or `inf`; `definite-convergence` uses `limit` of `x^p f`.
* `(certified-integral f x a b tol)`: rigorous interval `(iv lo hi)` for a finite interval and a regular integrand; slow for wide intervals or many derivatives (about 1 s per call).

## Examples

```lisp
(definite-integral '(/ 1 (+ 1 (^ x 2))) 'x '-inf 'inf)
;=> pi

(definite-integral '(/ 1 (+ 1 (^ x 4))) 'x 0 'inf)
;=> (* 1/4 (^ 2 1/2) pi)

(definite-integral '(/ (cos x) (+ 1 (^ x 2))) 'x '-inf 'inf)
;=> (* pi (exp -1))

(definite-integral '(/ (sin x) x) 'x 0 'inf)
;=> (* 1/2 pi)

(definite-integral '(exp (* -1 (^ x 2))) 'x '-inf 'inf)
;=> (^ pi 1/2)

(definite-integral '(* (^ x 3) (exp (* -2 x))) 'x 0 'inf)
;=> 3/8

(definite-integral '(sqrt (* x (- 1 x))) 'x 0 1)
;=> (* 1/8 pi)

(definite-integral '(/ 1 (+ 2 (cos x))) 'x 0 (* 2 'pi))
;=> (* 2/3 (^ 3 1/2) pi)

(car (definite-integral '(/ 1 x) 'x 1 'inf))
;=> divergent

(definite-integral '(exp (* -1 (* a x))) 'x 0 'inf)
;=> (^ a -1)

(definite-convergence '(/ (sin x) x) 'x 1 'inf)
;=> conditional

(definite-check '(/ 1 (+ 1 (^ x 2))) 'x '-inf 'inf 'pi)
;=> #t

(definite-check '(/ (sin x) x) 'x 0 'inf '(/ pi 3))
;=> #f

(definite-integral '(/ (log x) (^ (+ 1 (^ x 2)) 2)) 'x 0 'inf)
;=> (* -1/4 pi)

(definite-integral '(/ (^ x 1/3) (+ 1 (^ x 2))) 'x 0 'inf)
;=> (* 1/3 (^ 3 1/2) pi)

(definite-integral '(/ 1 (+ (^ x 2) (^ a 2))) 'x '-inf 'inf)
;=> (* (^ a -1) pi)

(definite-integral '(/ 1 (+ 2 (^ (sin x) 2))) 'x 0 (* 2 'pi))
;=> (* 1/3 (^ 6 1/2) pi)
```

## Pitfalls

* `integral_0^inf sin x dx` and `integral_{-1}^{1} dx/x^2` are not numbers: the first gives `(divergent ...)` (the partial integrals oscillate), the second too (a non-integrable pole inside). Never report a principal value as the integral.
* A parameter gives a condition, not a guess: `integral_0^inf e^(-a x) dx = 1/a` holds for `a > 0`; read `(conditions)` and pass the condition on.
* For an irreducible denominator factor of degree 3 or more the sum over its roots is exact: closed radicals (biquadratic formula, normal fields), otherwise `(im (root-sum t g ...))` with `heaviside`; `definite-check` compares such a value only numerically (`numeric`). No float guessing.
* `numeric` from `definite-check` is weaker than `#t`: the Dirichlet integral and singular endpoints are only compared by quadrature.
* Not covered: parametric `1/(x^4+a^4)` (needs degree 4 over Q(a)), principal values, repeated factors of degree 3 or more.
