# Topic: forms

Differential forms and vector calculus in ℝ^n. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. A form is an object printed `#(form vars k terms)`; read it with `form->expr` (`(* 2 x y dx)`, `(wedge dx dy)`). Terms are `(coef (indices))` where indices are variable names or 0-based positions. A vector field is a list of components, variables are listed as `'(x y z)`.

## Functions

* `(make-form vars k terms)`: a `k`-form from terms, e.g. `(make-form '(x y) 1 '((1 (x))))` is `dx`; `(form e vars)`: the 0-form `e`; `(form->expr f)`: the readable expression.
* `(form-d f)`: exterior derivative (`d(d f) = 0`); `(wedge a b ...)`: wedge product; `(form-add a b)`, `form-sub`, `form-scale`, `form-neg`, `form-zero?`, `form-equal?`.
* `(form-closed? f)`: `d f = 0`; `(form-exact? omega)`: a potential exists (see pitfalls); `(form-potential omega)`: a `(k-1)`-form `F` with `dF = omega` or `#f`.
* `(form-pullback f phi uvars)`: pull back along `x_i = phi_i(u)`; `(form-interior v f)`: contraction with the vector `v`; `(form-hodge f)`: Hodge star (Euclidean metric).
* `(vf-grad f vars)`, `(vf-div F vars)`, `(vf-curl F vars)`: gradient, divergence, curl (3 variables); `(vf-laplacian f vars)`.
* `(vf-potential F vars)`: a scalar potential of a conservative field or `#f`; `(vf-vector-potential F vars)`: a vector potential `A` with `curl A = F`; both have `...-check` verifiers.
* `(make-chain phi ranges)` and `(integrate-form omega chain)`: integral of a form over a parametrized chain; `(stokes-check omega phi ru rv)`: `(boundary-integral surface-integral status)`.

## Examples

```lisp
(form->expr (form-d (form '(* (^ x 2) y) '(x y))))
;=> (+ (* 2 x y dx) (* (^ x 2) dy))

(form->expr (wedge (make-form '(x y) 1 '((1 (x)))) (make-form '(x y) 1 '((1 (y))))))
;=> (wedge dx dy)

(form->expr (form-potential (make-form '(x y) 1 '((y (x)) (x (y))))))
;=> (* x y)

(vf-curl '((* -1 y) x 0) '(x y z))
;=> (0 0 2)

(vf-potential-check '(y x) '(x y) (vf-potential '(y x) '(x y)))
;=> #t

(integrate-form (make-form '(x y) 1 '((1 (x)))) (make-chain '(u (^ u 2)) '((u 0 1))))
;=> 1

(stokes-check (make-form '(x y) 1 '(((* -1 y) (x)) (x (y)))) '(u v) '(u 0 1) '(v 0 1))
;=> (2 2 exact)

(form->expr (form-pullback (make-form '(x y) 1 '((1 (x)))) '((^ u 2) u) '(u)))
;=> (* 2 u du)
```

## Pitfalls

* `form-d` returns a form object, not an expression: wrap with `form->expr` to read it. The terms of an object print as indices: `((1 (0)))` is `dx`.
* `form-potential` uses the Poincare homotopy from a base point: the potential is valid on a star-shaped domain without singularities (recorded as the condition `star-shaped-domain`) and is verified symbolically. `#f` means "no potential found this way", not a proof of non-exactness: the angle form `(-y dx + x dy)/(x^2 + y^2)` is closed (`#t`) but `form-exact?` gives `#f`.
* `vf-curl` gives a vector for three variables and, for two, the scalar `dQ/dx - dP/dy`.
* `form-hodge` and `vf-*` take no metric argument: they use the standard Euclidean one in Cartesian coordinates (polar or spherical components must be converted first).
* A chain must be given in the parameters `ru`, `rv` as `(u a b)`; Stokes: `stokes-check` compares the boundary integral with the integral of `d omega` and reports `exact`, `numeric` or `mismatch`.

## Also (exported helpers)

`form?`, `form-vars`, `form-degree`, `form-terms`, `form-sub`, `form-neg`, `form-scale`, `form-add`, `form-zero?`, `form-equal?`, `form-potential-check`, `vf-vector-potential-check`, `chain?`, `chain-phi`, `chain-ranges`, `integrate-form-numeric`, `chain-rect-boundary`, `vf-form1`, `vf-form2` (a field as its work 1-form and flux 2-form).
