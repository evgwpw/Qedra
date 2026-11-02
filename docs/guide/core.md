# CAS guide for LLMs: core

An exact computer algebra system (symbols, integers, fractions, radicals; no floating-point guesses). It is honest: when it cannot decide, it says `unknown`; answers that hold only under conditions list them. Pass both on to the user. This is the short core; details live in topic cards (`guide` with `topic`, see the end).

## Two input languages

* **Math language** (default for `integrate`, `solve`, `simplify`, `math`, ...): `x^2`, `2x` (implicit product only after a number), `x*y` (never `xy`), `sqrt(x)`, `exp(x)`, `log(x)` (natural), `sin cos tan atan`, `pi`, `∞`, equations `a = b`, vectors `[a, b]`, sets `{a, b}`, intervals `(0, ∞)`, `f(x) := x^2` definitions (use the `math` tool, the session is persistent). Decimal `0.5` makes results inexact: write `1/2`.
* **Lisp** (tool `evaluate`, or `syntax: "lisp"`): S-expressions, prefix operators with a quote for data: `(integrate '(* x (exp x)) 'x)`. The topic cards show Lisp forms, because library functions (`dsolve`, `convert`, `pi-groups`, ...) are called from Lisp. In the `math` tool the same functions are written `f(a, b)`.

More math notation: `abs(x)`, `cot asin acos sinh cosh`; `π`, `-∞`; `[a, b]` is a VECTOR (a system of equations, unknowns, a matrix row), a closed interval only where a domain is expected (`x ∈ [0, 1]`, `declare`), elsewhere `interval(a, b)`; `x ∈ ℝ` tests membership (`true/false/unknown`), `x :∈ ℝ` declares; domains `ℕ ℤ ℚ ℝ ℂ`, `positive`, `nonnegative`, `negative`, `nonpositive`. `log10` and `**` do not exist. Systems and unknowns are vectors: `equations: "[x + y = 3, x - y = 1]"`, `vars: "[x, y]"` (arrays of strings are accepted too). Examples: `integrate(x*exp(x), x)` gives `x*exp(x) - exp(x)`; `solve(x^2 - 5x + 6 = 0, x)` gives `{2, 3}`; `limit(sin(x)/x, x, 0)` gives `1`; `f(x) := x^3 - 3x; solve(diff(f(x), x) = 0, x); f(1)` in `math`.

Results come as an S-expression in `result` (for example `(^ x 2)`) and in the math language in `pretty`; read `pretty`. LaTeX (KaTeX) is in `latex` (step entries also carry `before_latex`/`after_latex`).

## Running it

`qedra` (also shipped as `Lisp.exe`) with no arguments starts a REPL; `--math` starts it in the math language, `-e "expr"` runs one expression, `--json` is a line protocol for agents, `--mcp` serves MCP over stdio. `--version` prints the release. `--sandbox [--allow-dir DIR]...` limits `load`/`load-math` to the library directory and the allowed ones in every mode (in `--mcp` the sandbox is on by default; `--unsafe` turns it off): it guards against mistakes, not against an attacker.

## Reading the answer

Look at `status`, not at `ok`.

| status | meaning | do |
|---|---|---|
| `answer` | computed | use `result`/`pretty`; check `conditions`, `warnings`, `note` |
| `unknown` | not decided (the result is the unevaluated form) | say so; never invent an answer; try another route. **unknown is not "no"** |
| `no-solution` | proved: no solutions | an answer, not a failure |
| `nonelementary` | `integrate` only: proved that no elementary antiderivative exists (e.g. `exp(x^2)`, `1/log(x)`) | an answer; stop retrying; `note` may name a special function |
| `error` | bad input | fix the input (`error` has the message) |
| `timeout` | interrupted after `timeout_s` (default 60, max 600) | simplify or raise `timeout_s`; not a proof of anything |

Other fields: `conditions` (when the answer is valid, e.g. `a ≠ 0`: always tell the user), `assumptions` (active declarations such as `x ∈ ℝ`), `note`, `warnings`, `output` (what `print` wrote), `steps` (off by default: `steps: "brief"` or `"full"`, `lang: "en"` for English text).

## Certificates

Pass `certificate: true` (tools `integrate`, `solve`, `simplify`, `expand`, `factor`, `together`, `apart`, `groebner`, `sum`, `equivalent`) when correctness matters. The field `certificate` is `{kind, verified, method, detail}`: `verified: true` is an exact check by an independent route (derivative of an antiderivative, substitution of solutions, ...); `"numeric"` is a check at sample points (convincing, not a proof); `"skipped"` means nothing could be checked; `false` means the answer FAILED its own check: do not present it as correct. `"partial"`: some solutions (those with `root-of`) were not checked; `"timeout"`: the check ran out of time (the answer stays valid). A failed check adds the warning "ответ не прошёл проверку". A certificate never changes `status` and counts against `timeout_s`. In Lisp, checkers are separate functions: `int-check`, `dsolve-check`, `solve-check`, `dimension-check` (see the cards).

| `kind` | what was checked |
|---|---|
| `derivative` | `integrate`: the derivative of the antiderivative minus the integrand is 0 (definite: also `F(b) - F(a)`) |
| `substitution` | `solve`: every solution substituted into every equation (`detail.solutions[].residuals`) |
| `equivalence` | `simplify`, `expand`, `factor`, `together`, `apart`, `equivalent`: input and answer are equal |
| `counterexample` | `equivalent` returned `false`: `detail.point` and the two values prove it |
| `ideal_membership` | `groebner`: every input polynomial reduces to 0 by the basis (input is inside the ideal of the basis only) |
| `sum`, `recurrence` | `sum`: direct summation at integer points agrees (`"numeric"`); a returned recurrence is checked against direct sums (`true`) |
| `nonelementary` | `integrate` with `status: nonelementary`: a proof by Risch/Liouville, not an independent check (`verified: "skipped"`) |
| `none` | no check exists (`diff`, `limit`, `series`, `math`, ...) |

## Which tool

| need | tool |
|---|---|
| one operation with checked arguments | `simplify`, `expand`, `factor`, `together`, `apart`, `diff`, `integrate`, `sum`, `solve`, `limit`, `series`, `groebner`, `equivalent` |
| matrices, Jordan form, `exp(A t)` | `linear-algebra` (fields in card `linear-algebra`); LP and ILP: `linear-programming` (card `optimization`) |
| several statements, definitions, any library function in math syntax | `math` |
| Lisp code, library functions with data (ODE, units, number theory, ...) | `evaluate` |
| properties of symbols (`x` positive, integer, in `[0,1]`) | `declare`, `undeclare`, `declarations`; without a declaration a symbol is an arbitrary complex number (`sqrt(x^2)` stays) |
| find a library function by name or words | `code` with `kind: "search"`, then `sig` (signature) or `def` (source); also `Lisp.exe --query` |
| how a topic works, signatures, examples | `guide` with `topic` |
| forget everything | `reset` |

Prefer a specific tool to `math`: arguments are checked and the answer is classified.

## Habits that avoid wrong answers

* Declare domains first when the answer depends on them (`declare(x, positive)`).
* Use `equivalent` to compare two expressions: `true` is a proof; `unknown` with agreeing samples is NOT a proof.
* In Lisp, unevaluated forms are data: quote them (`'(+ x 1)`); a function of `x` in an equation is written `(y x)`, derivatives `(diff (y x) x)`.
* `log10`, `**`, `x^0.5` are traps: use `log(x)/log(10)`, `^`, `sqrt(x)`. `xy` is ONE symbol: write `x*y` (and `2x`, not `x2`). `ln` is the same as `log`.
* `solve(a*x = b, x)` is `b/a` only for `a ≠ 0`: always pass `conditions` on.
* A name defined earlier in the session may shadow a function: `reset` when something behaves strangely.
* Report `unknown`, `conditions` and failed certificates honestly.

## When the result is `unknown`

Say honestly that the system did not decide. You may suggest or try: simplify the input first (`simplify`, `expand`, `together`), `declare` the domain of the symbols, substitute a variable by hand, compute a `series` for a limit, or give a numerical estimate that you clearly label as an estimate. A `timeout` proves nothing: the same problem may succeed with a larger `timeout_s` or a simpler form. Never present a guess as a result of this tool.

## Session and limits

The session is persistent: variables, functions (`f(x) := ...`) and declarations stay until `reset`; if a name behaves strangely, you may have defined it earlier. `timeout_s` (1 to 600) limits a call; `max_chars` (up to 200000, default 20000) limits `result`/`pretty` (truncation is reported in `warnings`). Files outside the CAS library and `--allow-dir` cannot be read; writing files and starting processes are not available.

## Topics (guide with topic=NAME)

Each card has 5-15 functions with exact signatures, runnable examples and pitfalls. A tool name or a name from another system (`DSolve`, `FactorInteger`, `Eigenvalues`, ...) is accepted as a topic too: see `synonyms`.

* `algebra`: `simplify`, `expand`, `factor`, `together`, `apart`, `trigsimp`, `combsimp`, radicals, pattern matching, user rules.
* `solve`: `solve` for equations and systems, `solve-check`, `root-of`, real roots, resultants.
* `calculus`: `diff`, `limit` (Gruntz), `series`, `taylor`; Lisp argument order.
* `integration`: `integrate`, definite integrals, Risch verdicts (`nonelementary`), special functions, `int-check`.
* `definite`: improper definite integrals (`definite-integral`, `definite-convergence`, `definite-check`): residues, Jordan, tables, proven divergence, certificates.
* `ode`: `dsolve` (general solution and Cauchy problem), `dsolve-check`, solution record accessors.
* `variational`: calculus of variations: Euler-Lagrange, Euler-Poisson and PDE equations, Beltrami and other first integrals, natural boundary conditions, Noether.
* `transforms`: Laplace transform and its inverse (`laplace`, `inverse-laplace`), `laplace-check`, `convolve`, `heaviside`, `dirac`; ODEs, systems and Volterra equations by Laplace (`laplace-dsolve`, `laplace-dsolve-system`, `laplace-volterra`), transfer functions (`transfer-function`, `stable?`).
* `ztransform`: Z-transform and inverse (`ztransform`, `inverse-ztransform`, `ztransform-check`), linear recurrences by Z (`zsolve`, `zsolve-check`).
* `fourier`: Fourier transform and inverse (`fourier`, `inverse-fourier`, `fourier-check`), convention `e^(-i w t)`.
* `sums`: `sum` (Gosper, Zeilberger), recurrences (`rsolve`), products, C-finite sequences and identity proofs.
* `linear-algebra`: matrices, `det`, `inv`, eigen, Jordan form, `mat-exp`, tool `linear-algebra`.
* `polynomials`: GCD, factoring over algebraic fields, Groebner bases, generic fields (`field-*`, `fp-*`).
* `number-theory`: primes and certificates, modular arithmetic, Pell, finite fields GF(p^n).
* `curves`: plane curves: singular points, genus, parametrization, Puiseux series.
* `plots`: SVG plots (explicit, parametric, polar, implicit) and `plot-info`.
* `numerics`: certified intervals, root isolation, certified integrals and sums.
* `constants`: proved zero tests and relations for constants (`const-zero?`, `const-relations`, `const-class`): `log 6 = log 2 + log 3`, `unknown` instead of guesses.
* `optimization`: critical points, Lagrange, linear and integer programming, dynamic programming.
* `inequalities`: polynomial inequalities `p >= 0` with checkable certificates: sums of squares (Gram matrix), AM-GM, intervals, counterexamples (`prove-nonneg`, `sos-check`).
* `specfun`: Gamma, B, psi and hypergeometric pFq: exact values, recurrence and reflection with conditions, `hyperexpand`, Gauss and Chu-Vandermonde sums, numeric certificates (`specfun-simplify`, `hyperexpand`, `specfun-check`).
* `forms`: differential forms, vector calculus, Stokes check.
* `domains`: declarations, intervals, finite sets, three-valued logic.
* `steps`: step-by-step solutions, reading the step tree.
* `units`: quantities with units, `convert`, `dimension-check`, Buckingham pi groups, `dimensional-solve`.
* `synonyms`: names from other systems (Mathematica, Maple) mapped to our functions and topics.

An unknown name returns suggestions and the full list.
