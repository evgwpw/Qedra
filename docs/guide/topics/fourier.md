# Topic: fourier

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=>` after a form is the printed result it must give. Expressions are data: quote them. Convention: `F(w) = integral of f(t) e^(-i w t) dt` over the whole line, inverse `f(t) = 1/(2 pi) integral of F(w) e^(i w t) dw`. `%i` is the imaginary unit, `(abs t)` is |t|, `(sign t)` is sgn t, `(heaviside u)` is theta(u), `(dirac u)` is delta(u). Variable order: `(fourier f t w)` (time first), `(inverse-fourier F w t)` (frequency first). An unknown function is written `(f t)`, its transform stays `(fourier (f t) t w)`.

## Functions

* `(fourier f t w)`: F(w). Table: `e^(-a|t|)` gives `2a/(a^2+w^2)`, `t^n e^(-at) theta(t)` gives `n!/(a+iw)^(n+1)`, `theta(t)`, a rectangle `theta(t+T) - theta(t-T)` gives `2 sin(wT)/w`, `sin(a t)/t`, Gaussian `e^(-a t^2 + b t)`, `delta(t-t0)` gives `e^(-i w t0)`, `1/(a^2+t^2)` gives `(pi/a) e^(-a|w|)`, constants and `cos`, `sin` as delta pairs. Rules: linearity, shift `f(t-t0)`, modulation `e^(i w0 t) f`, scaling `f(a t)`, derivative `(diff (f t) t)` gives `i w F`, `t^k f` as `(i d/dw)^k`, convolution `(fourier-convolve f g t)` gives `F G`. Not found: the unevaluated `(fourier f t w)` (not an error). Decay conditions (a > 0) go to the `conditions` channel.
* `(inverse-fourier F w t)`: inverse transform. Rational F without poles on the real axis: poles on one side give `theta(t)` or `theta(-t)` parts (through the Laplace inverse with s = i w), complex pole pairs give `e^(-k|t|)` times a phase; a factor `e^(-i w tau)` shifts t; other table entries by duality (the forward table at -t, divided by 2 pi). Not found: the unevaluated `(inverse-fourier F w t)`.
* `(fourier-check f F t w)`: certificate that F is the transform of f: `#t` (exact recomputation through the Laplace transform of the one-sided pieces, independent of the Fourier table), `numeric` (quadrature on a window at w = 1/2, 3/2, 3; tail below 1e-6, weaker; delta terms by sifting), `#f` (different: wrong sign in the exponent, wrong scale, wrong a), `unknown` (f not absolutely integrable, no value). To check an inverse, pass its result as `f`.
* `(heaviside x)`: a number gives 0, 1 or 1/2 (at 0); otherwise `(heaviside x)`.
* `(dirac x)`: a nonzero number gives 0; otherwise `(dirac x)`.

## Examples

```lisp
(fourier '(exp (* -2 (abs t))) 't 'w)
;=> (* 4 (^ (+ 4 (^ w 2)) -1))

(fourier '(* (exp (* -1 t)) (heaviside t)) 't 'w)
;=> (^ (+ 1 (* %i w)) -1)

(fourier '(- (heaviside (+ t 1)) (heaviside (+ t -1))) 't 'w)
;=> (* 2 (^ w -1) (sin w))

(fourier '(exp (* -1 (^ t 2))) 't 'w)
;=> (* (^ pi 1/2) (exp (* -1/4 (^ w 2))))

(fourier '(diff (f t) t) 't 'w)
;=> (* %i w (fourier (f t) t w))

(inverse-fourier '(/ 1 (+ 1 (* %i w))) 'w 't)
;=> (* (exp (* -1 t)) (heaviside t))

(inverse-fourier '(/ 1 (+ 4 (^ w 2))) 'w 't)
;=> (* 1/4 (exp (* -2 (abs t))))

(fourier-check '(exp (* -1 (abs t))) '(/ 2 (+ 1 (^ w 2))) 't 'w)
;=> #t

(fourier-check '(exp (* -1 (^ t 2))) '(* (^ pi 1/2) (exp (* -1/4 (^ w 2)))) 't 'w)
;=> numeric

(fourier-check '(exp (* -1 (abs t))) '(/ 4 (+ 1 (^ w 2))) 't 'w)
;=> #f
```

## Pitfalls

* Other books put 1/(2 pi) or 1/sqrt(2 pi) in front or flip the sign of the exponent: state the convention to the user. Here the forward transform has no factor and the exponent is `-i w t`.
* The transform of a constant or `theta(t)` contains `delta(w)`; `cos` and `sin` give delta pairs: these are distributions, `fourier-check` compares them only by sifting.
* Poles on the real axis (`1/(1-w^2)`, `1/w`) are not inverted; repeated quadratic factors are inverted when F is a rational function of `i w` with rational coefficients (`1/(1+w^2)^2` works); a simple factor with a linear term (`1/(w^2+2w+2)`) gives a phase times `e^(-k|t|)`.
* Run `fourier-check` before presenting a result; `numeric` is weaker than `#t`, `unknown` means no verdict.
* Not covered: periodic functions as series, Bessel and error functions, derivatives of delta, products of two non-matching trigonometric factors with different frequencies inside the exact check (numeric only).
