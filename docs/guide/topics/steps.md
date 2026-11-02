# Topic: steps

Step-by-step solutions: how to ask for them, how to read the tree, how to check a step. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. In the MCP tools pass `steps: "brief"|"full"|"trace"|"attempts"` and `lang: "en"` (the default language of titles is Russian). Steps exist for `integrate`, `diff`, `simplify`, `solve`, `limit`, `series`, `groebner`, linear algebra and LP; `expand`, `factor`, `together`, `apart` write none.

## Functions

* `(steps expr [level [lang]])`: a MACRO, `expr` is evaluated with the step log on; it prints the tree to the output and returns the value. `level` is `'brief` (main steps, default), `'full` or `'trace`; `lang` is `'ru` or `'en`. Write the call inside: `(steps (integrate '(* x (exp x)) 'x) 'full 'en)`.
* `(explain expr [lang])`: macro; prints the tree of ATTEMPTS, including failed strategies with the reason and time (why a Risch or integration chain refused).
* `(steps-call thunk level lang)`, `(explain-call thunk lang)`: the function forms taking a `lambda`.
* `(capture-step-log thunk level lang)`: runs `thunk`, returns `(value steps omitted)` where `steps` is a list of step records, no printing.
* `(step-rule s)`: stable English id of the technique (`solve-factor`, `int-by-parts`, `diff-product`, ...); `(step-title s)`, `(step-comment s)`: text (Russian unless translated by the tool).
* `(step-before s)`, `(step-after s)`: expressions before and after the step; `(step-level s)`: `main` or `detail`; `(step-children s)`: sub-steps.
* `(step-rules steps)`: all rule ids in walk order (parent, then children); `(step-find rule steps)`: the first step with that rule or `#f`.
* `(with-step (rule title before [:comment c] [:level 'detail] [:after f]) body...)`: macro for library authors: records a step around `body`; a failed body (`#f` or an error) drops the frame.

## Examples

```lisp
(steps (integrate '(* x (exp x)) 'x) 'brief 'en)
;=> (+ (* x (exp x)) (* -1 (exp x)))

(step-rules (cadr (capture-step-log (lambda () (solve '(= (- (^ x 2) (* 5 x) -6) 0) 'x)) 'full 'en)))
;=> (solve-equation solve-factor solve-linear solve-linear)

(step-rules (cadr (capture-step-log (lambda () (integrate '(* x (exp x)) 'x)) 'full 'en)))
;=> (integration int-by-parts int-parts-choice int-table int-parts-formula int-table)

(step-rules (cadr (capture-step-log (lambda () (diff 'x '(* x (sin x)))) 'full 'en)))
;=> (differentiation diff-product diff-variable diff-trig simplify-result)

(step-before (car (cadr (capture-step-log (lambda () (solve '(= (- (^ x 2) (* 5 x) -6) 0) 'x)) 'full 'en))))
;=> (= (- (^ x 2) (* 5 x) -6) 0)
```

## Reading the tree (MCP `steps` field)

Each step is `{rule, title, comment, before, before_pretty, after, after_pretty, level, children}`; `omitted: N` means N sub-steps were cut (depth <= 8, <= 200 steps; also in `warnings`). The top step names the operation (`solve-equation`, `integration`, `limit`, `series`); its children are the techniques that produced the answer, in order; failed attempts are not logged (`"attempts"` shows them). A quadratic with rational roots is shown as `solve-factor` (one `solve-linear` per factor), `solve-quadratic` appears only for irreducible quadratics.

`(step-omitted s)`: how many sub-steps were cut by the limits (0 if none).

## Pitfalls

* Every step is an equivalent transformation: to verify one, call `equivalent` on `before_pretty` and `after_pretty`. For `limit` and `series` the `before`/`after` are unevaluated `limit(...)`/`series(...)` forms or series: do not feed them to `equivalent`.
* Titles and comments are Russian by default; `lang: "en"` translates a phrase from the dictionary, the rest stays Russian and is reported in `warnings`. `rule` ids and formulas are language independent: rely on them.
* An unevaluated result (`unknown`, `nonelementary`) has no steps; use `explain`/`"attempts"` to see why.
* `steps` prints into `output` and returns the value: in `evaluate` read both fields; `steps` is a macro and must contain the whole call, not a quoted expression.
* `d/dx(u)` and `integral f dx` written as text are not parsed back into steps.
