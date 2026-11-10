# Topic: ztransform

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Expressions are data: quote them. The unilateral Z-transform is `A(z) = sum_{n>=0} a_n z^(-n)`. Variable order: `(ztransform a n z)` (sequence variable first), `(inverse-ztransform F z n)` (z first). The discrete delta is `(kdelta u)` (1 at u = 0), the discrete step `(heaviside (- n k))` means 1 for n >= k. An unknown sequence is written `(a n)`, `(a (+ n 1))`.

## Functions

* `(ztransform a n z)`: A(z). Table: constants, `a^n`, `n^k a^n`, `sin(w n)`, `cos(w n)` (also times `b^n` and `n^k`), `C(n,k)`, `(kdelta (- n k))`. Rules: linearity, `b^n f` gives `F(z/b)`, `n f` gives `-z F'`, shift `a(n+k)` gives `z^k A - sum a_j z^(k-j)` (unknown `(a n)` stays as `(ztransform (a n) n z)`), delay `theta(n-k) f(n-k)` gives `z^(-k) F`, convolution `(sum (* (f k) (g (- n k))) k 0 n)` gives `F G`; else a series closed form by `sum`. Not found: the unevaluated `(ztransform a n z)` (not an error). The radius condition `|z| > R` goes to the `conditions` channel.
* `(inverse-ztransform F z n)`: inverse for rational F (proper at infinity), n >= 0. Partial fractions of F/z over Q: `z/(z-r)^m` gives `C(n,m-1) r^(n-m+1)`, a pole at 0 gives `(kdelta ...)`, irreducible quadratics with complex roots give `r^n (cos, sin)` (angle as a multiple of pi when it is one), real roots in Q(sqrt d) give powers of radicals. Multiplicity above 1 for quadratics and higher degree factors: the unevaluated form.
* `(ztransform-check a F n z)`: certificate that Z[a] = F: `#t` (equal to the rules), `numeric` (partial sums of the series at three points z outside the poles, weaker), `#f` (different), `unknown`. To check an inverse, pass its result as `a`.
* `(ztransform-initial F z)`: initial value a_0 = limit of F at infinity. `(ztransform-final F z)`: limit of a_n = limit of `(z-1) F` at z = 1; `unknown` (with a condition) when a pole of `(z-1) F` lies on or outside the unit circle.
* `(zsolve eq (a n) conds)`: linear recurrence with constant coefficients, right side known to `ztransform`, `eq` is `(= lhs rhs)`, `conds` is a list `(= (a 0) 0)`. Missing initial values stay as constants C1 = a(0), C2 = a(1), ... Returns `(= (a n) closed-form)` valid for n >= 0 (conditions channel); not solved or failed its check: the unevaluated `(zsolve ...)`.
* `(zsolve-check eq (a n) sol conds)`: certificate of an answer `sol` (an equation or an expression): substitution into the recurrence (exact `simplify`, else samples n = 0..5) and the initial values. `#t`, `numeric`, `#f`, `unknown`.
* `(kdelta u)`: a number gives 1 (u = 0) or 0; otherwise `(kdelta u)`.

## Examples

```lisp
(ztransform '(* 3 (^ 2 n)) 'n 'z)
;=> (* 3 z (^ (+ -2 z) -1))

(ztransform '(* n (^ 2 n)) 'n 'z)
;=> (* 2 z (^ (+ 4 (* -4 z) (^ z 2)) -1))

(ztransform '(a (+ n 1)) 'n 'z)
;=> (+ (* -1 z (a 0)) (* z (ztransform (a n) n z)))

(inverse-ztransform '(/ z (* (+ z -1) (+ z -2))) 'z 'n)
;=> (+ -1 (^ 2 n))

(inverse-ztransform '(/ z (+ (^ z 2) 1)) 'z 'n)
;=> (sin (* 1/2 n pi))

(ztransform-check '(* n (^ 2 n)) '(/ (* 2 z) (^ (+ z -2) 2)) 'n 'z)
;=> #t

(ztransform-check '(^ 2 n) '(/ z (+ z -3)) 'n 'z)
;=> #f

(ztransform-final '(/ z (+ z -1/2)) 'z)
;=> 0

(zsolve '(= (+ (a (+ n 2)) (* -3 (a (+ n 1))) (* 2 (a n))) (^ 2 n)) '(a n) '((= (a 0) 0) (= (a 1) 1)))
;=> (= (a n) (* 1/2 (^ 2 n) n))

(zsolve '(= (a (+ n 1)) (+ (* 2 (a n)) 1)) '(a n) '((= (a 0) 1)))
;=> (= (a n) (+ -1 (* 2 (^ 2 n))))

(zsolve-check '(= (a (+ n 1)) (+ (* 2 (a n)) 1)) '(a n) '(= (a n) (^ 2 n)) '((= (a 0) 1)))
;=> #f
```

## Pitfalls

* Resonance (right side `2^n` with root 2) gives `n 2^(n-1)`: that is correct, check it with `zsolve-check`.
* Fibonacci `a(n+2) = a(n+1) + a(n)`, a0 = 0, a1 = 1 gives Binet's formula with `sqrt 5` powers; it agrees with `rsolve` (compare numerically for n = 0, 1, 2, ...).
* Results hold for n >= 0 only; `(kdelta n)` terms appear for poles at 0 (for example `1/(z-2)`).
* Not covered: non-constant coefficients (use `rsolve`), improper F (a polynomial in z), repeated complex poles, nonlinear recurrences: they give the unevaluated form, never a guess.
* The check `numeric` is weaker than `#t`; a hand-made F must pass it too.
