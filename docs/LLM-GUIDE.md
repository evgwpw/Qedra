# CAS guide for LLMs: moved

The guide for LLMs is now served on demand in small pieces (step GD.2), not as one long file:

* **Core** (input languages, reading `status` / `conditions` / `certificate`, which tool when, list of topics): `docs/guide/core.md`; MCP tool `guide` without arguments, MCP resource `lisp://guide`, command `Lisp.exe --guide`.
* **Topic cards** (5-15 functions with exact signatures, runnable examples, pitfalls): `docs/guide/topics/NAME.md`; MCP tool `guide` with `topic=NAME`, command `Lisp.exe --guide NAME`.
* **Synonyms** (names from other systems such as Mathematica and Maple, and our tool names mapped to topics, for example `DSolve` gives the card `ode`): `docs/guide/synonyms.md`; `guide` with `topic=DSolve` returns the right card.

Command line: `qedra --help` lists all modes; `--version` prints the release, `--sandbox [--allow-dir DIR]...` limits `load`/`load-math` in every mode (details in `docs/mcp.md`).

The files are embedded into the assembly; the tests in `tests/Lisp.Tests/GuideTests.fs` check sizes, that every function named in a card exists, that every example runs and prints what the card says, and that every exported function of the library is either mentioned in a card or listed in `docs/guide/not-covered.txt`.
