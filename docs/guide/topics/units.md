# Topic: units

Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Module `units` (`lib/units.lisp`): exact quantities with units and dimensional analysis. A unit is a symbol or an expression over symbols: `'m`, `'(/ km h)`, `'(* kW h)`; prefixes (`k`, `m`, ...) work on SI units.

## Functions

* `(quantity v u)`: a quantity (value `v`, unit expression `u`); also `quantity-value`, `quantity-unit`, `quantity?`.
* `(convert q target)`: value of `q` in the unit `target` as a new quantity, exact (fractions); an error if the dimensions differ (`m` to `s`).
* `(quantity-add a b)`, `(quantity-mul a b)`: arithmetic; adding different dimensions is an error (also `quantity-div`, `quantity-pow q k`).
* `(unit-factor u)`, `(unit-dimension u)`, `(same-dimension? u1 u2)`: factor to SI, dimension vector, comparison.
* `(dimension->string d)`: readable dimension, e.g. `L M T^-2`.
* `(convert-temperature v from to)`: temperatures (`degC`, `degF`, `K`), affine, so not via `convert`.
* `(dimension-check formula env)`: `env` is an alist `((symbol . unit) ...)`; result `(ok dim)` or `(mismatch ...)`; unknown symbol or operation is an error, not a mismatch.
* `(pi-groups vars env)`, `(pi-groups vars env :repeating (v ...))`: independent dimensionless products (Buckingham pi theorem); the second form is the classical method with repeating variables.
* `(pi-groups-check vars env groups)`: certificate: groups are dimensionless, independent, and their number is n - rank.
* `(dimensional-solve target vars env)`: `target = C * prod(v^a)` if there is exactly one group, else `(= (Phi pi1 ...) 0)`.

## Examples

```lisp
(define env '((T . s) (l . m) (g . (/ m (^ s 2)))))

(convert (quantity 36 '(/ km h)) '(/ m s))
;=> (quantity 10 (/ m s))

(quantity-add (quantity 1 'km) (quantity 500 'm))
;=> (quantity 3/2 km)

(convert-temperature 100 'degC 'K)
;=> 7463/20

(car (dimension-check '(= T (* 2 pi (sqrt (/ l g)))) env))
;=> ok

(car (dimension-check '(= T (* 2 pi l)) env))
;=> mismatch

(pi-groups '(l g T) env)
;=> ((* (^ l 1) (^ g -1) (^ T -2)))

(dimensional-solve 'T '(l g) env)
;=> (= T (* C (^ l 1/2) (^ g -1/2)))
```

## In the math language (`--math`)

Same module, same exact arithmetic; the difference is that everything naming a unit, a formula or a variable is
passed as a **string**, so `m`, `s`, `T` stay ordinary language variables and their values cannot change the parse:

```
math> convert(quantity(36, "km/h"), "m/s")
quantity(10, m/s)
math> convert_temperature(100, "degC", "K")
7463/20
math> dimension_check("T = 2*pi*sqrt(l/g)", ["T = s", "l = m", "g = m/s^2"])
"ok: T"
math> pi_groups(["l", "g", "T"], ["l = m", "g = m/s^2", "T = s"])
[l^1/(g*T^2)]
math> dimensional_solve("T", ["l", "g"], ["l = m", "g = m/s^2", "T = s"])
T = C*l^(1/2)/g^(1/2)
```

Names: `quantity`, `convert`, `convert_temperature`, `dimension_check` (`"ok: <dim>"` or `"mismatch: <where>: <d1>
and <d2>"`), `pi_groups` (optional third argument — repeating variables), `pi_groups_check`, `dimensional_solve`.
Quantity arithmetic (`quantity_add`, …) is still Lisp-only.

## Pitfalls

* Values are exact: `(convert (quantity 1 'mile) 'm)` is a fraction, not a float. Floats in the input make the result inexact.
* `convert` between different dimensions raises an error; use `same-dimension?` first when unsure. Temperatures need `convert-temperature` (`273.15` offset).
* In `dimension-check` the exponent must be a rational number (`(^ x 3/2)` fine; `0.5` or a symbol with a unit gives a `rational-exponent` mismatch), `exp`/`sin` need a dimensionless argument, and `+` needs equal dimensions.
* `dimensional-solve` determines the form only up to the constant `C` (and a function of the groups when there are several): it is a scaling law, not a value.
* A mismatch is a finding about the formula, not a failure of the tool: report it and which two dimensions disagree.

## Also (exported helpers)

`dimension-matrix` (the exponent matrix of variables used by `pi-groups`).
