# Topic: constants

Proved zero tests and relations for closed constants (numbers, `pi`, `e`, `%i`, `+ * ^ - / exp log sin cos tan atan sqrt abs`). Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Every answer is a proof or `unknown`: a numeric near-zero never gives "zero", and "non-zero" needs an interval enclosure that excludes 0 or an exact normal form. The Risch step of `integrate` uses these tests for every "is this coefficient zero" decision.

## Functions

* `(const-zero? c)`: `#t` (proved 0), `#f` (proved non-zero) or `unknown`. Exact layers first (`log 6 = log 2 + log 3`, `exp(2 log 3) = 9`, nested radicals, `sin(pi/6)`, sums of `atan` of rationals), then interval enclosures at 30, 50, 75 digits.
* `(const-enclosure c digits)`: a rigorous `(iv lo hi)` for a closed constant (or `#f`: `%i`, branches, division by 0).
* `(const-clean e x)`: `(e2 unknown?)`: `x`-free groups of `e` proved 0 become 0, hidden rationals become numbers.
* `(const-relations cs)`: PROVED integer relations `sum n_i c_i = 0` (list of vectors). Logs of rationals: exact (prime factorisation); otherwise a PSLQ candidate kept only if `const-zero?` proves it.
* `(const-relation-holds? cs ns)`: `#t`/`#f`/`unknown` for a claimed relation.
* `(const-pslq cs digits)`: PSLQ integer-relation candidate or `#f`; NOT a proof.
* `(log-independent? cs)`: for `(log a)` of rationals: `#t` independent over Q (Baker: then over algebraic numbers), `#f` relation exists, `unknown` for other forms.
* `(exp-independent? as)`: algebraic exponents: `#t` when `e^a_i` are algebraically independent (Lindemann-Weierstrass: the `a_i` are Q-linearly independent).
* `(const-class c)`: `algebraic`, `transcendental` or `unknown` from proved theorems only (Hermite, Lindemann, Gelfond, Gelfond-Schneider).
* `(const-rational-value c)`: the rational `c` equals (proved), `no`, or `unknown`.
* `(const-exp-simplify c)`: `exp(c)` with `log p` terms folded (`exp(log 2 + 2 log 3)` is 18).
* `(iv-set-precision! d)`: working precision `10^-d` of the interval series (default 30); `(iv-precision)` reads it.

## Examples

```lisp
(const-zero? '(+ (log 6) (* -1 (log 2)) (* -1 (log 3))))
;=> #t

(const-zero? '(+ pi -355/113))
;=> #f

(const-zero? '(+ (cos (/ pi 5)) (* -1 (/ (+ 1 (^ 5 1/2)) 4))))
;=> unknown

(const-relations '((log 12) (log 2) (log 3)))
;=> ((-1 2 1))

(const-zero? '(+ (atan 1/2) (atan 1/3) (* -1/4 pi)))
;=> #t

(const-class '(exp pi))
;=> transcendental

(const-rational-value '(/ (log 6) (+ (log 2) (log 3))))
;=> 1
```

## Pitfalls

* `unknown` is truthy in Lisp: test with `(true? ...)`. Never report "zero" or "non-zero" for `unknown`; `cos(pi/5) = (1+sqrt 5)/4` is a true zero this code cannot prove.
* Symbols (parameters) and floats are not closed constants: `unknown`.
* Open problems stay `unknown`: `e + pi`, `e*pi`, `pi^e`, `e^e`, relations between `e` and `pi` (Schanuel). `const-rational-value` says `no` only for denominators up to 10^12 in a 50-digit enclosure.
* The Risch step answers "not known" (no answer, no "non-elementary" claim) when a coefficient is `unknown`.

## Also

Predicates for closed and plain constants are internal helpers (`not-covered.txt`). Certified intervals: card `numerics`.
