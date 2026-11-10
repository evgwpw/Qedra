# Topic: optimization

Critical points and Lagrange multipliers, exact linear and integer programming, dynamic programming with checkable answers. Examples are Lisp forms in `lisp` blocks, run top to bottom in one fresh session; a line `;=> text` after a form is the printed result it must give. Points are lists `((= x a) (= y b))`; the LP rows are `(coefficients rel rhs)` with `rel` one of `<= >= =` (unquoted inside a quoted list).

MCP tool `linear-programming`: `objective` (c as `"[3, 5]"`), `dir` (`max`/`min`), `constraints` (A), `rhs` (b), `relations` (vector of `"<="`/`">="`/`"="`, default all `"<="`), `integer` (vector of `"int"`/`"bin"`/`"free"` per variable; absent means plain LP). Answers: `(optimal x value y)` with dual prices `y` (`c.x = value = b.y`), `(infeasible y)` with a Farkas certificate (`status: no-solution`), `(unbounded x d)` (a feasible point and a ray), `(unknown x value nil)` (branch-and-bound node limit). `certificate: true` re-checks with `lp-check`; `steps` shows simplex iterations.

## Functions

* `(critical-points f vars)`: solutions of `grad f = 0` as a list of points, each verified by substitution; `(hessian f vars)`: matrix of second derivatives.
* `(extrema f vars)`: `(point value min|max|saddle|unknown)` per critical point (a degenerate Hessian gives `unknown`, never a false `min`).
* `(lagrange f constraints vars)`: constrained extrema `(point value lambdas type)`; the type is decided by the bordered Hessian for one constraint in two variables, else `unknown`. `constraints` is a list of expressions equal to 0.
* `(lp-solve dir c rows)`: `dir` is `'max` or `'min`, variables `x >= 0`; answer as above; `(lp-solve-free dir c rows frees)`: `frees` marks sign-free variables with `#t`.
* `(lp-maximize c A b)`, `(lp-minimize c A b)`: shortcuts for `A x <= b`, `x >= 0`.
* `(lp-check ans c rows)`: exact check of an answer to a MAX problem (feasibility, `c.x = b.y`, dual feasibility, Farkas certificate); `lp-check-min` for MIN.
* `(ilp-solve dir c rows intset)`: integer programming by branch and bound; `intset` is a list of `'int`, `'bin`, `'free`; `(ilp-check ans dir c rows intset)`.
* `(knapsack weights values W)`: 0/1 knapsack `(value chosen-indices table)`; `(lcs a b)`: longest common subsequence of two LISTS; `(edit-distance a b)`: Levenshtein with the operations.
* `(coin-change coins amount)`: `(count coins table)` or `(infeasible table)`; `(shortest-paths vertices edges s)`: Bellman-Ford `(distances tree)` or `(negative-cycle cycle)`.
* `(memoize f)`: a memoized function (the key is the argument list); `defmemo` defines one.

## Examples

```lisp
(extrema '(+ (- (^ x 3) (* 3 x)) (^ y 2)) (list 'x 'y))
;=> ((((= x -1) (= y 0)) 2 saddle) (((= x 1) (= y 0)) -2 min))

(lp-solve 'max '(3 5) '(((1 0) <= 4) ((0 2) <= 12) ((3 2) <= 18)))
;=> (optimal (2 6) 36 (0 3/2 1))

(lp-check (lp-solve 'max '(3 5) '(((1 0) <= 4) ((0 2) <= 12) ((3 2) <= 18))) '(3 5) '(((1 0) <= 4) ((0 2) <= 12) ((3 2) <= 18)))
;=> #t

(ilp-solve 'max '(5 4) '(((6 4) <= 24) ((1 2) <= 6)) '(int int))
;=> (optimal (4 0) 20)

(lp-solve 'max '(1 1) '(((1 -1) <= 1)))
;=> (unbounded (1 0) (1 1))

(car (knapsack '(1 3 4 5) '(1 4 5 7) 7))
;=> 9

(car (lcs '(a g g t a b) '(g x t x a y b)))
;=> 4

(car (edit-distance '(k i t t e n) '(s i t t i n g)))
;=> 3
```

## Pitfalls

* LP variables are `x >= 0` unless declared free (`lp-solve-free`, or `"free"` in the tool): a free variable forgotten here makes the problem look infeasible.
* An infeasible LP returns `(infeasible y)` (the evaluate status is `no-solution`): the vector `y` is the proof, check it with `lp-check`.
* `lcs` and `edit-distance` take LISTS of symbols or numbers, not strings (`(string->list s)` converts).
* `lagrange` and the bordered-Hessian type work for one constraint and two variables; with more, the type is `unknown`: classify by hand (do not call it a minimum).
* A branch-and-bound node limit gives `unknown`, not "infeasible".
* `(check-critical f vars point)` rejects a point that is not critical (`#f`): use it on any hand-made candidate.

## Also (exported helpers)

`classify-critical`, `check-critical`, `opt-real-point?`, `opt-lag-terms`, `lp-pretty`, `lp-check-min`, `knapsack-check`, `lcs-check`, `edit-distance-check`, `coin-change-check`, `coin-ways`, `coin-ways-check`, `shortest-paths-check`, `defmemo`.
