# Topic: solve

Equations and systems. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. The MCP tool `solve` (fields `equations`, `vars`) is the better entry for answers with `conditions` and `certificate`; this card is for Lisp use.

## Functions

* `(solve eq x)`: one equation `(= lhs rhs)` (an expression alone means `= 0`). The answer is a SET printed `{a, b}`; `set->list` gives a list. Unsolvable: `{}`; every number: `ℂ`.
* `(solve (list eq ...) (list x ...))`: a system; the answer is a set of solutions, each a list of `(= x value)`. Linear systems use Gauss-Jordan (parametric families come out in terms of free variables), nonlinear ones Groebner bases.
* `(solve-check eqs x sols)`: independent check by substitution: `(verdict ((solution state (residuals)) ...))`, verdict `exact`, `numeric`, `partial` (some `root-of` not checked), `skip`, `bad` (a residual is non-zero), `empty`. `sols` is a LIST (`set->list` of the answer); `eqs` a list of equations.
* `(real-roots p x)`: isolated real roots of a polynomial as exact algebraic numbers `root(coeffs, lo, hi)` (increasing order).
* `(resultant a b x)`: resultant of two polynomials in `x` (elimination).
* `(eval-num e)`: numeric value of an exact root or answer (float), for reporting.
* `(root-of? v)`: is `v` a `root-of` form? Answers may contain `(root-of poly x)` as DATA: exact roots of an irreducible polynomial of degree >= 3 with no radical form here (no Cardano/Ferrari). Radical clean-up: card `algebra`.
* `(solvable-by-radicals? f x)`: can the roots of the polynomial `f` be written with radicals over Q? `#t` / `#f` / `unknown`. It is the Galois group of every irreducible factor being solvable (degree <= 4: always; degree 5..7: the group is computed with a certificate, see `galois-group`). `#f` only for a proven non-solvable group (S5, A5, PSL(3,2), ...); degree > 7 or symbolic coefficients give `unknown`.
* `(galois-solvability f x)`: the evidence behind it for an irreducible `f`: `(#f :group S5)`, `(#t :group F20)`, `(#t :degree 3)`, `(#t :candidates (F18x2 F36x2))` (group not pinned down but every candidate is solvable), or `(unknown)`.
* `(galois-group f x)`: Galois group of an irreducible `f` of degree 2..7 as `(:group name order :certificate ...)`, or an honest `(:candidates (names ...))`, or `unknown`; `(galois-group-check f x r)` re-verifies it independently (fake groups are rejected). `solve` of an irreducible factor of degree 5..7 keeps its `root-of` answer and records a condition in the `conditions` channel: `not-solvable-by-radicals` ("в радикалах не выражается (группа Галуа S5, сертификат)") or `solvable-by-radicals` ("разрешимо в радикалах (группа Галуа F20, сертификат)"); nothing is recorded when it is not proven.

## Examples

```lisp
(set->list (solve '(= (- (^ x 2) (* 5 x) -6) 0) 'x))
;=> (2 3)

(solve (list '(= (+ x y) 3) '(= (- x y) 1)) (list 'x 'y))
;=> {((= x 2) (= y 1))}

(solve '(= (sin x) 0) 'x)
;=> {(* 2 k1 pi), (+ pi (* 2 k1 pi))}

(solve '(= (sqrt (+ x 1)) x) 'x)
;=> {(+ 1/2 (* 1/2 (^ 5 1/2)))}

(solve-check '((= (^ x 2) 4)) 'x '(2 3))
;=> (bad ((2 exact (0)) (3 bad (5))))

(solve-check '((= (^ x 2) 4)) 'x '(2 -2))
;=> (exact ((2 exact (0)) (-2 exact (0))))

(solvable-by-radicals? '(+ (^ x 5) (* -1 x) -1) 'x)
;=> #f

(solvable-by-radicals? '(+ (^ x 5) -2) 'x)
;=> #t
```

## Pitfalls

* `solve` returns a set, not a list: use `set->list` before `car`/`map`. Trigonometric families use integer parameters `k1`, `k2` (all integers).
* Inequalities (`x > 1`) are NOT solved: status `unknown`. Equations with parameters give a generic answer (`a*x = 1` gives `1/a`); the MCP tool reports the condition `a != 0` in `conditions`, the Lisp function does not. Always pass conditions on.
* Roots that fail substitution are dropped (`sqrt(x+1) = x` keeps only the root with `x >= 0`); `solve-check` with a `bad` verdict means the supplied value is wrong.
* A set `{}` is a proved "no solutions" (MCP status `no-solution`), unlike `unknown`.
* `(root-of ...)` roots are not verified by `solve-check` (verdict `partial`).
* Degree >= 3 with an irrational root: the answer holds both a `root(...)` real root and the symbolic `root-of`; say "root of this polynomial", never invent a closed form.
* Cyclic Groebner systems of six or more variables may time out; use `groebner` (card `polynomials`) and eliminate by hand.

## Also (helpers)

`rational-number?`, `real-numeric?`, `x-free?`, `root-of?`, `numeric-poly?`, `replace-expr`.
