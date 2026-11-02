# Topic: linear-algebra

Exact matrices (rational, symbolic, algebraic entries). Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. A matrix is a list of rows `'((1 2) (3 4))`; results print either as a list or as `[[..], ..]` (a tensor): both are accepted as input. Linear programming: card `optimization`; any field: card `polynomials` (`fm-*`).

MCP tool `linear-algebra`: matrix as `expr` = `"[[2,1],[0,2]]"` (math language), `fn` selects the operation: `jordan_form` (`[P, J]`, A = P J P^-1), `jordan_blocks`, `mat_exp` (e^{A t}, `var` defaults to `t`; verified by E' = A E, E(0) = I), `mat_power` (A^n, `var` defaults to `n`; nilpotent blocks give zeros with the condition `n >= s` in `conditions`), `mat_fn` (`func` = `"exp"` or a lambda), `diagonalize` (`[P, D]`), `is_diagonalizable`, `eigenvalues` (list of `(lambda multiplicity)`), `eigenvectors`.

## Functions

* `(det m)`, `(inv m)`, `(rank m)`: determinant, inverse, rank (symbolic entries allowed).
* `(mat-mul a b)`: product; `(rref m)`: reduced row echelon form.
* `(nullspace m)`: basis of the kernel (a list of vectors); `(columnspace m)`: basis of the image (columns of the ORIGINAL matrix).
* `(charpoly m lam)`: `det(lam I - A)` as an expression in `lam`.
* `(eigenvalues m)`: list of `(lambda multiplicity)`; complex ones appear as `%i`. `(eigenvectors m)`: `(lambda multiplicity (v1 ...))`, certified by `A v = lambda v`.
* `(jordan-form m)`: `(P J)` with `A = P J P^-1`; `(diagonalize m)`: `(P D)` or an error when not diagonalizable.
* `(mat-exp m [t])`: `e^A` (with a symbol, `e^(A t)`); `(mat-power m n)`: `A^n` with symbolic `n`; `(mat-fn f m)`: `f(A)` for `f` a name such as `'exp` or a lambda.

## Examples

```lisp
(det '((2 1) (0 2)))
;=> 4

(inv '((2 1) (1 1)))
;=> [[1, -1], [-1, 2]]

(nullspace '((1 2) (2 4)))
;=> ((-2 1))

(eigenvalues '((0 1) (-1 0)))
;=> ((%i 1) ((* -1 %i) 1))

(jordan-form '((2 1) (0 2)))
;=> (((1 0) (0 1)) ((2 1) (0 2)))

(mat-exp '((0 1) (0 0)) 's)
;=> ((1 s) (0 1))

(mat-power '((1 1) (0 1)) 'n)
;=> ((1 n) (0 1))
```

## Pitfalls

* `det`, `inv`, `rank`, `dot`, `cross` come from the tensor module; a singular matrix has no inverse (error), check `det` first.
* Without `s`, `(mat-exp m)` is `e^A` (t = 1), not a function of `t`.
* Eigenvalues of high degree are `root(...)`/`root-of` forms; a defective matrix has Jordan blocks (use `jordan-form`, not `diagonalize`).
* In the math language only one-word names are matrices; pass the matrix through `expr` in the tool.
* Vector operations: `(dot a b)`, `(cross a b)` (3-vectors), `(norm v)`; `(mat m)`/`(tensor->list t)` convert between list and tensor.

## Also (tensor and field-matrix helpers)

Tensors: `tensor?`, `tensor-raw`, `tensor-shape-list`, `tensor-data`, `tensor-from-flat`, `as-tensor`, `make-tensor`, `identity-matrix`, `tensor->list`, `shape`, `rank-of`, `strides`, `tref`, `transpose`, `vec+`, `vec-`, `scale`, `dot`, `norm`, `cross`, `mat`, `mat-t`, `outer`, `contract`, `join-strings`, `linalg-pretty`, `diagonalizable?`, `jordan-blocks`.
Matrices over any field (`fm-*`, see `polynomials`): `fm-mul`, `fm-mat-vec`, `fm-identity`, `fm-rref`, `fm-rank`, `fm-nullspace`, `fm-det`, `fm-solve`, `fm-inverse`, `fm-nullspace-check`, `fm-solve-check`, `fm-inverse-check`.
