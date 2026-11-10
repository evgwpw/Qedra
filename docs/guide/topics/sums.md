# Topic: sums

Sums, products, recurrences, C-finite sequences. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. The MCP tool `sum` (fields `expr`, `var`, `from`, `to`, `certificate`) and the math language `sum(f, k, a, b)` call the same code. A recurrence is the record `(recurrence S n (a0 ... aJ) rhs ((n0 v0) ...))`: `a0 S(n) + a1 S(n+1) + ... + aJ S(n+J) = rhs` with initial values.

## Functions

* `(sum-symbolic body k lo hi)`: closed form of the sum, or the unevaluated `(sum body k lo hi)`. Polynomials (Faulhaber), rational terms (Abramov), hypergeometric terms (Gosper), binomial sums (Zeilberger + `rsolve`). `hi` may be `'n` or `'inf`.
* `(sum-check F body k lo hi)`: `numeric` when direct summation at sample points agrees with `F`, else `skip` (not checked).
* `(gosper-sum t k lo hi)`: closed form by Gosper's algorithm or `#f`; `(gosper-term t k)`: the antidifference `g(k)` (`g(k+1) - g(k) = t(k)`), or `unsolvable` / `no-hyper`.
* `(zeilberger F n k)`: the recurrence in `n` that `sum_k F(n,k)` satisfies (creative telescoping), a `recurrence` record; `(wz-certificate F f n k)` gives a WZ certificate (or `#f`).
* `(rsolve r)`: closed form of a homogeneous recurrence with constant coefficients or of first order (hypergeometric), else `#f`.
* `(product-symbolic body k lo hi)`: closed form of a product (factorials, powers) or the unevaluated product.
* `(abramov-sum t k lo hi)`: rational terms: `g(hi+1) - g(lo) + rest`; `(sum-faulhaber m a b)`: power sums `sum k^m`.
* `(cfinite coeffs init)`: a C-finite sequence `a(n) = c1 a(n-1) + ... + cr a(n-r)` with initial terms; `(cf-term s n)` fast n-th term, `(cf-closed-form s n)`: Binet-like formula (order 1 and 2).
* `(cf-of-expr e n)`: C-finite form of an expression like `(fib n)`, or `#f`; `(cf-from-terms list)`: the shortest recurrence for terms (a conjecture, check it).
* `(cf-prove lhs rhs)`: PROVES an identity between C-finite expressions: `(proved R)` or `(disproved n0 lhs rhs)` with the first counterexample.

## Examples

```lisp
(sum-symbolic '(/ 1 (* k (+ k 1))) 'k 1 'n)
;=> (+ 1 (* -1 (^ (+ 1 n) -1)))

(sum-symbolic '(* (binomial n k) (binomial n k)) 'k 0 'n)
;=> (binomial (* 2 n) n)

(zeilberger '(binomial n k) 'n 'k)
;=> (recurrence S n (-2 1) 0 ((0 1)))

(rsolve '(recurrence S n (-2 1) 0 ((0 1))))
;=> (^ 2 n)

(cf-term (cfinite '(1 1) '(0 1)) 100)
;=> 354224848179261915075

(cf-prove '(fib (+ n 2)) '(+ (fib (+ n 1)) (fib n)))
;=> (proved 1)

(cf-prove '(fib (* 2 n)) '(* 2 (^ (fib n) 2)))
;=> (disproved 1 1 2)

(product-symbolic '(/ (+ k 1) (* 2 k)) 'k 1 'n)
;=> (* (^ 1/2 n) (+ 1 n))
```

## Pitfalls

* When no hypergeometric closed form exists (Apery numbers `sum(C(n,k)^2 C(n+k,k))`), the MCP `sum` returns the RECURRENCE with initial values and `note: no closed form`: pass it on, do not invent a formula.
* An unevaluated `(sum ...)` is "not decided", not "diverges". `1/k^2` over `1..inf` and `1/k!` over `0..n` have no closed form here and stay unevaluated.
* `(sum-check ...)` is numeric, not a proof; the recurrence of `zeilberger` is verified separately (`recurrence-check-sum`).
* `rsolve` returns `#f` for order >= 2 with variable coefficients (Petkovsek is not implemented) and for non-homogeneous recurrences.
* `cf-from-terms` guesses from finitely many terms; certify with `cf-prove` against an expression.
* `cf-prove` accepts only C-finite expressions (`fib`, powers `c^n`, polynomials in `n`, sums and products of those); `factorial` raises an error.
* Bounds: the lower bound `lo` defaults to 0 in the tool; terms with a pole or zero at a numeric bound need a manual check.

## Also (exported helpers)

`cf-shift`, `cf-scale`, `cf+`, `cf*`, `cf-partial-sum`, `cf-char-poly`, `cf->gf`, `gf->cf`, `cf-check`, `cf-check-proof`, `cf-coeffs`, `cf-init`, `cf-order`, `cf-terms`, `cf-term-mod`, `cf?`, `recurrence-order`, `recurrence-check`, `recurrence-check-sum`, `rsolve-first-order`, `rsolve-const-coeffs`, `product-check`, `product-check-how`, `sum-check-how`, `sum-unevaluated`, `sum-form`, `sum-strategies`, `sum-add-strategy`, `wz-prove-identity`, `combsimp`, `abramov-decompose` (split a rational term into a summable part and a remainder), `gosper-normal`, `gosper-check-identity`, `poly-shift` (`p(k+h)`), `poly-dispersion`.
