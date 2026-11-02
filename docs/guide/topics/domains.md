# Topic: domains

Assumptions on symbols, domains and intervals, finite sets, three-valued logic. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Without a declaration a symbol is an arbitrary complex number: `sqrt(x^2)` stays. The MCP tools `declare` (`symbol`, `domain`), `undeclare`, `declarations` and the math language `x :∈ positive` do the same for the whole session. Domains are values (unquoted): `naturals integers rationals reals complexes` and the sign intervals `positive nonnegative negative nonpositive`.

## Functions

* `(declare 'x domain ...)`: add constraints to a symbol (returns the symbol); `(undeclare 'x)`; `(declarations 'x)`: the list of its constraints (`()` for none).
* `(assuming ((x domain ...) ...) body ...)`: temporary declarations around `body`, restored on any exit.
* `(sign-of e)`: `positive`, `negative`, `zero`, `nonnegative`, `nonpositive` or `unknown`; `(positive? e)`, `negative?`, `nonnegative?`, `nonpositive?`, `real?`, `integer-valued?`: three-valued predicates.
* `(in? x S)`: membership (`#t`/`#f`/`unknown`) for sets, domains and intervals; `(subset? a b)`: inclusion, also three-valued.
* `(make-interval lo hi lo-closed? hi-closed?)`: an interval (infinite ends as `inf`/`-inf`); `interval-has?`, `interval-intersect`, `interval-subset?`, `interval-empty?`, `domain-hull`.
* `(list->set l)`, `(set->list s)`: finite sets (printed `{a, b}`; duplicates merged); `(union a b ...)`, `(set-intersection a b ...)`, `(set-difference a b)`, `(card s)`, `power-set`, `set-map`, `set-filter`.
* `(and3 a b ...)`, `or3`, `not3`: strong Kleene logic where anything that is not `#t` or `#f` is `unknown`; `(true? x)`: `#t` only for `#t`; `known?`.

## Examples

```lisp
(declare 'x positive)
;=> x

(sign-of 'x)
;=> positive

(undeclare 'x)
;=> x

(assuming ((y positive)) (simplify '(sqrt (^ y 2))))
;=> y

(in? 1/2 integers)
;=> #f

(in? 'q integers)
;=> unknown

(interval-intersect (make-interval 0 2 #t #t) (make-interval 1 3 #t #f))
;=> [1, 2]

(set->list (union (list->set '(1 2)) (list->set '(2 3))))
;=> (1 2 3)

(or3 #t 'unknown)
;=> #t
```

## Pitfalls

* `unknown` is TRUE in a Lisp `if`: write `(if (true? (positive? x)) ...)`. `(not 'unknown)` is `#f`; use `not3`.
* `declare` takes one domain per call in the math language (`x :∈ positive`): `declare(a, positive)` is an error there; intersections come from several `declare` calls in Lisp.
* A declaration changes answers (`sqrt(x^2)` becomes `x` for positive `x`, `abs(x)` for real `x`) and is listed in `assumptions`: always mention it. `reset-declarations` removes user declarations (built-in `pi > 0` stays).
* The set operations are for finite sets of the `set` type; `union` of plain lists is wrong. Domains and intervals intersect via `intersect-general` / `interval-intersect`.
* The comparison `(< 'a 1)` is an error for a symbol: use `positive?`, `sign-of`, `in?` for symbolic facts.

## Also (exported helpers)

`domain?`, `make-domain`, `domain-name`, `interval?`, `interval-lo`, `interval-hi`, `interval-lo-closed?`, `interval-hi-closed?`, `empty-interval`, `interval-point?`, `interval-has-integer?`, `disjoint?`, `intersect-general`, `assuming-call`, `reset-declarations`, `negative?`, `nonnegative?`, `nonpositive?`, `op-expr?`, `constraints-of`, `contains-sym?`, `domain-rank`, `set?`, `empty-set?`, `intersection`, `dispatch-method`, `and3-all`, `or3-all`, `false?`.
