# Topic: polynomials

Polynomials in several variables, algebraic number fields, Groebner bases, generic algebra over a field. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Polynomials are expressions `'(+ (^ x 2) 1)`; in the `fp-*` family they are coefficient lists, LOWEST degree first (`(-1 0 1)` is `x^2 - 1`). MCP tools: `factor`, `groebner` (`order`: `lex`, `grlex`, `grevlex`).

## Functions

* `(coefficients e x)`, `(coefficients->poly cs x)`: expression to list `(c0 c1 ...)` and back; `(poly-divides? a b x)`: does `a` divide `b`.
* `(poly-gcd a b)`: GCD of polynomials in any variables (builtin; also `poly-lcm`, `poly-quotient`, `poly-remainder`, `resultant`, `degree`, `coeff`).
* `(factor-over p x alpha)`: factorization over ℚ(alpha), `alpha` is `(^ 2 1/2)` (any `(^ d 1/n)`), `%i` or `(root-of m t)`. Returns `(lc ((factor multiplicity) ...))`, self-checked.
* `(alg-field m t)`: the number field ℚ(alpha) for an irreducible monic `m` in `t`; `(alg-elt F coeffs)`: element (rational coefficients, lowest first); `(alg-mul F a b)`, `alg-add`, `alg-div`, `alg-inv`, `alg-pow`, `(alg->expr F a)` back to an expression.
* `(groebner fs vars [order])`: reduced Groebner basis (default `lex`, the order for elimination; also `'grlex`, `'grevlex`); `(normal-form f gens vars)`: remainder of `f` modulo the ideal; `(eliminate fs elim rest)`: generators of the elimination ideal.
* `(zero-dim? G vars)`: is the ideal zero-dimensional (finitely many solutions).
* `(field-gf p)`: the field GF(p) as an object; also `(field-Q)`, `(field-algnum F)`, `(field-ratfun x)`, `(field-gfpn F)`. Generic operations: `(field-mul F a b)`, `field-add`, `field-inv`, `field->expr`.
* `(fp-gcd F a b)`: monic GCD of coefficient-list polynomials over the field `F` (also `fp-divmod`, `fp-sqfree`, `fp-egcd`, `fp-eval`, `fp-compose`).
* `(fm-solve F m b)`: linear system over `F`: `(x nullspace-basis)` or `#f` (also `fm-det`, `fm-inverse`, `fm-rank`, `fm-rref`).

## Examples

```lisp
(factor-over '(- (^ x 2) 2) 'x '(^ 2 1/2))
;=> (1 ((+ (^ 2 1/2) x) 1) ((+ (* -1 (^ 2 1/2)) x) 1))

(define F (alg-field '(+ (^ t 2) -2) 't))
;=> F

(alg->expr F (alg-mul F (alg-elt F '(1 1)) (alg-elt F '(1 -1))))
;=> -1

(groebner (list '(+ (^ x 2) (^ y 2) -1) '(- x y)) (list 'x 'y) 'lex)
;=> ((+ x (* -1 y)) (+ -1/2 (^ y 2)))

(eliminate (list '(- x (^ t 2)) '(- y (^ t 3))) (list 't) (list 'x 'y))
;=> ((+ (^ x 3) (* -1 (^ y 2))))

(fp-gcd (field-gf 7) '(-1 0 1) '(-1 1))
;=> (6 1)

(fm-solve (field-Q) '((1 2) (3 4)) '(5 6))
;=> ((-4 9/2) ())
```

## Pitfalls

* `factor` works over ℤ: `x^2 - 2` is irreducible there; give the extension to `factor-over`.
* A Groebner basis depends on the monomial order and variable order: use `lex` to eliminate variables, then `groebner-check` (every input reduces to 0; `certificate` kind `ideal_membership` proves only input ⊆ basis).
* Large systems (cyclic-6 and up) overflow in coefficient growth: expect timeouts, not wrong answers.
* `fp-*`, `alg-elt`, `gf-*` polynomials and elements are coefficient lists lowest degree first (like `coefficients`), never highest first.
* `alg-*` elements are coefficient lists in ℚ(alpha); mix them only with the same field object `F`.
* `(field-gf p)` needs a prime `p`; GF(p^n) is `gf-field` (card `number-theory`).

## Also (exported helpers)

Algebraic numbers: `alg-field-minpoly`, `alg-field-embed`, `alg-sub`, `alg-negate`, `alg-zero?`, `alg-equal?`, `alg-norm`, `alg-minpoly`, `expr->alg`, `alg-poly-div`, `alg-poly-gcd`, `alg-poly-sqfree`, `alg-primitive`, `alg-factor`, `alg-factor-check`. Groebner: `groebner-check`, `groebner-lex`, `fglm`, `normal-form-with-quotients`, `ideal-certificate` (division by a set with quotients: f = sum q_i g_i + r). Fields: `field-name`, `field-char`, `field-zero`, `field-one`, `field-sub`, `field-neg`, `field-div`, `field-zero?`, `field-equal?`, `field-from-rational`, `field-pow`. Polynomials over a field: `fp-trim`, `fp-add`, `fp-sub`, `fp-neg`, `fp-mul`, `fp-scale`, `fp-deg`, `fp-lc`, `fp-monic`, `fp-deriv`, `fp-equal?`, `fp-divmod-check`, `fp-gcd-check`, `fp-egcd-check`, `fp-sqfree-check`, `leading-coefficient`. Matrices over a field: `fm-mul`, `fm-mat-vec`, `fm-identity`, `fm-nullspace`, `fm-nullspace-check`, `fm-solve-check`, `fm-inverse-check`.
