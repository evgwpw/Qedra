# Topic: algebra

Rewriting expressions. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Expressions are data: quote them (`'(+ x 1)`). In the math language the same functions are `simplify(e)`, `factor(e)`, `apart(e, x)`, ...; each has its own MCP tool with `certificate: true`.

## Functions

* `(simplify e)`: canonical form with the rules of the simplifier (trigonometric Pythagoras, powers, logs, radicals). Sound under the declared domains only.
* `(expand e)`: multiply out brackets, `(factor e)`: factor over the integers (product form), `(factor-list e)`: `(content ((factor multiplicity) ...))`.
* `(together e)`: one reduced fraction (numerator times denominator to the power -1); `(numer e)`, `(denom e)`: its parts.
* `(apart e x)`: partial fractions in `x` over ℚ.
* `(poly-gcd a b)`: monic-normalised GCD of polynomials in any variables.
* `(trigsimp e)`: trigonometric simplification by a size criterion (the smallest equivalent form it finds).
* `(combsimp e)`: `factorial`/`gamma` ratios, e.g. `(n+1)!/n!` gives `n + 1`.
* `(sqrt-denest e)`: denest `sqrt(a + b sqrt c)`; `(alg-equal-expr? a b)`: exact equality of expressions with radicals (`#t`/`#f`).
* `(subst rule e)`: the RULE comes first: `(= x 3)`, `(x 3)` or a list of rules; only symbols are substituted.
* `(ac-match pattern e)`: associative-commutative matching, bindings `((?a v) ...)` or `#f`; `(ac-subst pattern binds)` fills a pattern back in.
* `(defrule name pattern replacement)`: a user rewrite rule for `simplify` (`?x` are pattern variables; optional condition, `:ac`).

## Examples

```lisp
(simplify '(+ (^ (sin x) 2) (^ (cos x) 2)))
;=> 1

(factor '(- (^ x 4) 1))
;=> (* (+ -1 x) (+ 1 x) (+ 1 (^ x 2)))

(apart '(/ 1 (* x (+ x 1))) 'x)
;=> (+ (^ x -1) (* -1 (^ (+ 1 x) -1)))

(sqrt-denest '(sqrt (+ 3 (* 2 (sqrt 2)))))
;=> (+ 1 (^ 2 1/2))

(simplify '(sqrt (^ x 2)))
;=> (sqrt (^ x 2))

(begin (declare 'x positive) (simplify '(sqrt (^ x 2))))
;=> x

(undeclare 'x)
;=> x
```

## Pitfalls

* Without a declaration a symbol is an arbitrary complex number: `sqrt(x^2)` stays. `declare` it positive or real (see `domains`); `undeclare` afterwards.
* Compare two expressions with `equivalent` (MCP tool; `true` is a proof) or `alg-equal-expr?` for radicals. `(equal? a b)` is structural: `(+ a 1)` and `(+ 1 a)` differ before `simplify`.
* `factor` works over the integers: `x^2 - 2` stays irreducible. Over ℚ(α) use `factor-over` (card `polynomials`).
* `together` and `apart` do not record `conditions` (removed zeros of denominators).
* Lisp arithmetic simplifies at once: `(+ 'a 'a)` is `(* 2 a)`. To build an expression untouched use `(list '+ 'a 1)`.
* `pi` and `%i` are symbols: quote them.

## Also (exported helpers)

`alg-simplify`, `denest-check?`, `radical-roots`, `ac-match-all`, `ac-match-sub`, `ac-replace-sub`, `ac-pattern-var?`, `ac-segment-var?`, `pattern-from-dag`, `lean-heads` (matching, Lean heads table), `trigsimp-size`, `trigsimp-half-angle`.
