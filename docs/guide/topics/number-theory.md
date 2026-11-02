# Topic: number-theory

Integers, modular arithmetic, certified primality, finite fields GF(p^n). Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. All integers are exact and of any size. Checkers named `...-check` use only multiplications, `powmod` and comparisons.

## Functions

* `(factor-integer n)`: `((p1 k1) ...)` in increasing `p` (a negative `n` starts with `(-1 1)`); `(prime? n [:certificate])`: primality, exact below 3.3e24, a probabilistic test above (the answer carries the condition `probable-prime`); with `:certificate` it returns a Pratt certificate (or `#f` for a composite).
* `(pratt-certificate n)`: `(n a ((q cert) ...))` for a prime `n`; `(pratt-check cert)`: independent check (`#t`/`#f`), a forged certificate gives `#f`.
* `(next-prime n)`: the least prime `> n`; `(primes-up-to n)`: sieve; `(divisors n)`, `(totient n)`.
* `(powmod a e m)`: modular power; `(invmod a m)`: inverse or `#f`; `(egcd a b)`: the list `(g s t)` with `s a + t b = g`.
* `(crt rs ms)`: `(x M)` solving `x = r_i (mod m_i)`; moduli need not be coprime; `#f` when inconsistent.
* `(order a n)`: multiplicative order; `(primitive-root p)`; `(jacobi a n)`; `(sqrtmod a p)`: square root mod prime `p` or `#f`.
* `(solve-linear-diophantine a b c)`: `((x0 y0) (dx dy))` for `a x + b y = c`, solutions `x0 + dx k`.
* `(pell D)`: fundamental solution of `x^2 - D y^2 = 1`; `(pell-negative D)` for `-1` or `#f`; `(pell-solutions D k)`: the first `k` solutions.
* `(sum-of-two-squares n)`: `(a b)` or `#f`; `(pythagorean-triples bound)`: primitive triples with `c <= bound`.
* Diophantine, refusals are `(none reason)`: `(dioph-linear a b c)` (reason: gcd); `(dioph-linear-system A b)`: `(x0 (v1 ...))`, `x = x0 + sum t_i v_i`, or `(none w)` with a rational certificate `w` (`w^T A` integral, `w^T b` not), checked by `(dioph-linear-system-check A b res)`.
* `(dioph-pell-negative D)`: `(x y)` or `(none even-period L)`; `(sqrt-cf-period D)`; `(dioph-pell D N)`: classes of `x^2 - D y^2 = N` (`y >= 0`, any sign of `x`), `(none bound)` when the Nagell bound search is complete, `(unknown bound)` when it is too long.
* `(two-squares n)`: all `(a b)` or `(none p)` with `p = 3 mod 4`; `(three-squares n)`, `(four-squares n)`; `(pythagorean-hypotenuse c)`, `(pythagorean-leg a)`: all triples.
* `(discrete-log g h p)`: `k` with `g^k = h` (Pohlig-Hellman + BSGS) or `(none ...)`; `(multiplicative-order a n)`; `(dioph-check eq vars solution)`: `#t`/`#f` by substitution, `eq` is `(= l r)` or `(congruent l r m)`.
* `(gf-field p m t)`: the field GF(p^n) from an irreducible `m` over GF(p) (coefficients lowest first); `(gf-elt F x)`, `(gf* F a b)`, `(gf-inv F a)`, `(gf-order F a)`.
* `(gf-irreducible? f p)`, `(gf-factor f p)`: irreducibility and factorization over GF(p): `(lc ((f k) ...))`.

## Examples

```lisp
(factor-integer 600851475143)
;=> ((71 1) (839 1) (1471 1) (6857 1))

(pratt-check (pratt-certificate 101))
;=> #t

(pratt-check '(101 3 ((2 (2 1 ())))))
;=> #f

(crt '(2 3) '(3 5))
;=> (8 15)

(pell-solutions 2 3)
;=> ((3 2) (17 12) (99 70))

(solve-linear-diophantine 3 5 1)
;=> ((2 -1) (5 -3))

(dioph-pell 2 7)
;=> ((-3 1) (3 1))

(two-squares 25)
;=> ((5 0) (4 3))

(dioph-linear-system '((1 1) (1 -1)) '(1 0))
;=> (none (-1/2 1/2))

(discrete-log 3 13 17)
;=> 4

(gf-factor '(1 0 0 0 1) 5)
;=> (1 (((2 0 1) 1) ((3 0 1) 1)))

(gf-order (gf-field 2 '(1 1 0 1) 't) (gf-elt (gf-field 2 '(1 1 0 1) 't) '(0 1 0)))
;=> 7
```

## Pitfalls

* `(mod -7 3)` is `-1` (sign of the dividend, like `remainder`); `(modulo -7 3)` is `2`. For residues use `modulo`.
* `prime?` above 3.3e24 is probabilistic unless certified: ask for `:certificate` and verify it with `pratt-check` when the claim matters. Certificates need the factorisation of `n - 1`, slow for hard cases.
* `factor-integer` is trial division plus Pollard's rho, self-checked (product and primality of the factors): a semiprime of two large primes can take very long or end in an error "no divisor found"; neither proves anything about `n`.
* GF elements are coefficient lists, lowest degree first, of length `n`; `(gf-field p m t)` requires `m` irreducible (test with `gf-irreducible?`).
* `egcd` returns `(g s t)`; `invmod` returns `#f` instead of an error when `gcd != 1`.
* Polynomials over GF(p) in `gf-factor`, `gf-poly-gcd` are coefficient lists; for generic field code use `field-gf` (card `polynomials`).

## Also (exported helpers)

`gf->int`, `gf+`, `gf-`, `gf/`, `gf-power`, `gf-random-irreducible`, `gf-primitive?`, `gf-poly-gcd`.
