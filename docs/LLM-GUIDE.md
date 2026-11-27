# CAS guide for LLMs: moved

The guide for LLMs is now served on demand in small pieces (step GD.2), not as one long file:

* **Core** (input languages, reading `status` / `conditions` / `certificate`, which tool when, list of topics): `docs/guide/core.md`; MCP tool `guide` without arguments, MCP resource `lisp://guide`, command `Lisp.exe --guide`.
* **Topic cards** (5-15 functions with exact signatures, runnable examples, pitfalls): `docs/guide/topics/NAME.md`; MCP tool `guide` with `topic=NAME`, command `Lisp.exe --guide NAME`.
* **Synonyms** (names from other systems (Maple, Maxima) and from the original Rubi language, plus our tool names mapped to topics, for example `DSolve` gives the card `ode`): `docs/guide/synonyms.md`; `guide` with `topic=DSolve` returns the right card.

Partial differential equations (step PDE.0): card `pde`. `pdsolve(u_t = a*u_xx, u(x,t), u(x,0) = f(x), u(0,t) = 0, [x, 0, L], [t, 0, inf])` classifies the equation and answers `unknown` with the methods that would fit (no solving methods yet); `pde_check(equation, u(x,t) = answer, u(x,t), conditions...)` verifies someone else's answer: `true` (exact), `numeric`, `false`, `unknown`; arbitrary functions `F(x - c*t)` are supported. Subscripts `u_t`, `u_xx` mean derivatives of the declared unknown only inside these calls. With `certificate: true` on `math`/`evaluate` the last `dsolve`/`ode_check`/`pdsolve`/`pde_check` call returns a certificate of kind `ode`/`pde` (residual after substitution and a verdict per condition).

Command line: `qedra --help` lists all modes; `--version` prints the release, `--sandbox [--allow-dir DIR]...` limits `load`/`load-math` in every mode (details in `docs/mcp.md`).

The files are embedded into the assembly; the tests in `tests/Lisp.Tests/GuideTests.fs` check sizes, that every function named in a card exists, that every example runs and prints what the card says, and that every exported function of the library is either mentioned in a card or listed in `docs/guide/not-covered.txt`.
