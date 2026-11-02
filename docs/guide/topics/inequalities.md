# Topic: inequalities

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Expressions are data: quote them. This card proves polynomial inequalities `p >= 0` with certificates a reader can check. Coefficients must be exact rationals (a float gives `unknown`). `vars` is a symbol (`'x`) or a list (`'(x y)`).

Result of a proof attempt: `(proved cert)`, or `(counterexample ((x v) ...) value)` (a point where p < 0, `value` = p there), or `unknown` (not decided: it does NOT mean p < 0). `proved` is returned only after `sos-check` accepted the certificate.

Certificates:
* `(sos (c q) ...)`: p = sum of c*q^2 with rational c > 0.
* `(sos-on a b (i j (c q) ...) ...)`: p = sum of (x-a)^i (b-x)^j c q^2 on [a, b].
* `(amgm (c e ((w a) ...)) ...)`: the negative term -c*x^e is covered by weighted AM-GM: weights w > 0 sum to 1, sum of w*a = e, every a has even exponents.

## Functions

* `(prove-nonneg p vars)`: p >= 0 on all of R^n. One variable: exact (factor, real roots, sign on every gap, then p = k A^2 B with B without real roots and a Gram matrix). Several variables: a point grid (counterexample), AM-GM, then a Gram matrix.
* `(prove-nonneg-on p x a b)`: p >= 0 on [a, b] (rational ends, one variable): Lukacs form s0 + (x-a)(b-x) s1 (even degree) or (x-a) s0 + (b-x) s1 (odd degree), roots at the ends peeled off first.
* `(sos-check p vars cert)`: independent check, `#t` or `#f`: `expand` of p minus the sum is 0, every weight is a rational > 0, an AM-GM certificate is recomputed from its weights and the coefficient budget. Fakes are rejected.
* `(sos-decompose p vars)`: Gram-matrix method only (sum of squares over Q). Basis from the half Newton polytope; exact LDL^T of Q.
* `(sos-amgm p vars)`: AM-GM only, found by an exact LP over Q.

## Examples

```lisp
(prove-nonneg '(+ (^ x 2) (* -2 x) 1) 'x)
;=> (proved (sos (1 (+ -1 x))))

(prove-nonneg '(+ (^ x 2) (* -3 x) 2) 'x)
;=> (counterexample ((x 3/2)) -1/4)

(prove-nonneg-on '(* x (+ 1 (* -1 x))) 'x 0 1)
;=> (proved (sos-on 0 1 (1 1 (1 1))))

(prove-nonneg-on '(+ 1 (* -1 (^ x 3))) 'x 0 1)
;=> (proved (sos-on 0 1 (0 1 (1 1) (2 x)) (1 2 (1 1))))

(prove-nonneg '(+ (^ x 4) (^ y 4) (* -2 (^ x 2) (^ y 2))) '(x y))
;=> (proved (amgm (2 (2 2) ((1/2 (4 0)) (1/2 (0 4))))))

(sos-decompose '(^ (+ (^ x 2) (^ y 2) -1) 2) '(x y))
;=> (proved (sos (1 (+ -1 (^ x 2) (^ y 2)))))

(sos-decompose '(+ (* (^ x 4) (^ y 2)) (* (^ x 2) (^ y 4)) (* -3 (^ x 2) (^ y 2)) 1) '(x y))
;=> unknown

(sos-amgm '(+ (* (^ x 4) (^ y 2)) (* (^ x 2) (^ y 4)) (* -3 (^ x 2) (^ y 2)) 1) '(x y))
;=> (proved (amgm (3 (2 2) ((1/3 (4 2)) (1/3 (2 4)) (1/3 (0 0))))))

(sos-check '(+ (^ x 2) (* -2 x) 1) 'x '(sos (1 (+ x -1))))
;=> #t

(sos-check '(+ (^ x 2) (* -2 x) 1) 'x '(sos (2 (+ x -1))))
;=> #f

(prove-nonneg '(+ (^ x 2) (* -1 y)) '(x y))
;=> (counterexample ((x 0) (y 3)) -3)
```

## Pitfalls

* `unknown` is not a disproof: the Motzkin polynomial x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1 is nonnegative but not a sum of squares; `sos-decompose` says `unknown`, and `prove-nonneg` still proves it by AM-GM.
* Counterexamples in several variables come from a small grid only; a polynomial negative elsewhere may stay `unknown`. In one variable the answer is complete.
* The Gram method uses floating point only as a hint; the certificate is exact (rounded, projected onto the linear constraints in Q, LDL^T with all pivots >= 0).
* Strictness is not tracked: a certificate proves `p >= 0`, not `p > 0`.
* Interval proofs take one variable and rational ends with a < b; several variables with constraints are not supported.
