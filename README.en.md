# Qedra

Russian version: [README.md](README.md).

**Qedra** is a computer algebra system built on its own Lisp dialect (F# / .NET 10). The point is answers you can trust:
every result is checked independently, what was not solved is reported honestly, and a solution can be read step by
step. A typical problem takes a fraction of a second; hard ones (Risch, Gruntz, Kovacic) take seconds.

## What it is

- **Checked answers.** An antiderivative is verified by differentiation, a solution by substitution into the original
  equation, sums and recurrences by a numeric oracle. In `--json` and MCP this is the `certificate` field.
- **Proved refusals.** If no elementary antiderivative exists, Risch's algorithm proves it: `status: nonelementary` is
  an answer, not a failure. If a problem is not solved, the result is `status: unknown` with a reason, never an
  invented answer.
- **Step-by-step solutions.** `steps` in `--json` and MCP shows the rule and formula of every step (in Russian and in
  English).
- **Two inputs.** The math language (`--math`, `.mth` files) takes formulas as on paper; Lisp gives full access to the
  library.
- **Embedding.** An MCP server for Claude Desktop and other clients, `--json` for agents, and a browser build.

It covers: integration (Risch, rational functions, special functions, definite integrals), limits (Gruntz), series,
symbolic sums and recurrences, ODEs (including Kovacic and solutions in special functions), algebra (factorization,
Gröbner bases, Galois groups, algebraic numbers), linear algebra and Jordan form, LP/ILP, number theory with
certificates, interval arithmetic and plots.

## Install

Prebuilt archives are in [Releases](https://github.com/evgwpw/Qedra/releases): `qedra-1.109.7.11-win-x64.zip`,
`qedra-1.109.7.11-linux-x64.tar.gz`, `qedra-1.109.7.11-osx-x64.tar.gz`, `qedra-1.109.7.11-osx-arm64.tar.gz`.
They are self-contained: no installed .NET is required. Unpack an archive and run `qedra` (`qedra.exe` on Windows);
`Lisp.exe` next to it is the same launcher under its former name.

```
$ qedra --version
Qedra 1.109.7.11
$ qedra --math -e "integrate(x^2, x)"
1/3*x^3
```

From sources you need the .NET 10 SDK:

```
dotnet build Lisp.slnx
dotnet test Lisp.slnx
src/Lisp.Host/bin/Debug/net10.0/Lisp.exe            # REPL: Lisp; --math for the math language
```

## Examples

Every output below was produced by `qedra --math -e "…"` with this version.

An indefinite integral:

```
$ qedra --math -e "integrate(x*exp(x), x)"
x*exp(x) - exp(x)
```

A non-elementary integral: the answer is a proof, not an error (`--json` carries `status: nonelementary` and the
reason in `note`):

```
$ qedra --math -e "integrate(exp(x^2), x)"
integrate(exp(x^2), x)
```

A differential equation:

```
$ qedra --math -e "dsolve(y' + y = x, y(x))"
y(x) = (C1 + x*exp(x) - exp(x))*exp(-x)
```

Equations and polynomial systems:

```
$ qedra --math -e "solve(x^2 - 5*x + 6 = 0, x)"
{2, 3}
$ qedra --math -e "groebner([x^2 - y, y^2 - x], [x, y])"
[x - y^2, -y + y^4]
```

Limits and factorization:

```
$ qedra --math -e "limit(sin(x)/x, x, 0)"
1
$ qedra --math -e "factor(x^4 - 1)"
(-1 + x)(1 + x)(1 + x^2)
```

A machine-readable answer: one JSON line per request (`timing.ms` depends on the machine).

```
$ echo '{"op":"math","code":"diff(x^3 - 3*x, x)"}' | qedra --json
{"status":"answer","result":"(+ -3 (* 3 (^ x 2)))","pretty":"-3 + 3x^2","latex":"-3 + 3x^{2}","note":null,"conditions":null,"assumptions":null,"certificate":null,"steps":null,"warnings":null,"output":"","timing":{"ms":71,"timeout":false},"ok":true,"error":null,"stack":null}
```

More examples with expected answers are in [`examples/`](examples/README.md); they are executed by the test suite.

## MCP

`qedra --mcp` is an MCP server over stdio. To connect it to Claude Desktop (`claude_desktop_config.json`) or any client:

```json
{
  "mcpServers": {
    "qedra": {
      "command": "C:\\path\\to\\qedra.exe",
      "args": ["--mcp"]
    }
  }
}
```

The tools `math`, `simplify`, `integrate`, `sum`, `solve`, `limit`, `series`, `groebner`, `equivalent`, `declare` and
others return one shape: `status` (`answer` / `unknown` / `nonelementary` / `error`), the result, `conditions`, and on
request `steps` and `certificate`. The server can read files through `load`, so the sandbox is on by default (see
below); details are in [`docs/mcp.md`](docs/mcp.md).

### Installing as an MCP server

- **MCPB (Claude Desktop, no .NET):** download `qedra-1.109.7.11.mcpb` from [Releases](https://github.com/evgwpw/Qedra/releases) and open the file — the client offers to install it. The bundle is self-contained: Windows x64, Linux x64, macOS x64/arm64.
- **Docker:** `docker run -i --rm ghcr.io/evgwpw/qedra` — a stdio server; the registry name is `io.github.evgwpw/qedra`.
- **NuGet (.NET tool, requires .NET 10):** `dnx Qedra --mcp` (or `dotnet tool install -g Qedra`, then `qedra --mcp`).

```json
{
  "mcpServers": {
    "qedra": { "command": "docker", "args": ["run", "-i", "--rm", "ghcr.io/evgwpw/qedra"] }
  }
}
```

For NuGet: `"command": "dnx", "args": ["Qedra", "--mcp"]`.

## Sandbox

`qedra --sandbox [--allow-dir <dir>]...` restricts `load`/`load-math` to the library directory and the given
directories in every mode: file, `-e`, `--math`, `--json`, REPL. In `--mcp` the sandbox is on by default and
`--unsafe` turns it off. It guards against LLM mistakes (a stray `load`, reading someone else's file), **not against
an attacker**: the interpreter and the host are one process.

## Browser version

<https://evgwpw.github.io/Qedra/> — the same engine compiled to WebAssembly (AOT), with formula input and an example
catalog. To build locally: `web/build.sh` (or `web/build.cmd`), then run `web/start.sh` / `web/start.cmd`.

## Documentation

- [`docs/math-language.md`](docs/math-language.md) — the input math language: operations, functions, steps, JSON API.
- [`docs/lisp-library-guide.md`](docs/lisp-library-guide.md) — the Lisp library reference (checked against the code by
  a test).
- [`docs/lisp-dialect.md`](docs/lisp-dialect.md), [`docs/lisp-modules.md`](docs/lisp-modules.md) — the dialect and
  modules.
- [`docs/mcp.md`](docs/mcp.md) — the MCP server: tools, safety, protocol.
- [`docs/guide/core.md`](docs/guide/core.md) — the short LLM guide (English), topic cards in `docs/guide/topics/`.

## How it is made

The code was written mostly by LLM agents from the author's task specifications and under the author's review;
architecture, choice of algorithms and acceptance are human. Correctness does not rest on trusting generated code:
every result is checked independently (differentiating the antiderivative, substituting the solution, certificates
for sums and proofs), with a suite of more than 3300 tests.

## License

0BSD — see [`LICENSE`](LICENSE). Licenses of third-party libraries used by the browser build are in
[`THIRD-PARTY-NOTICES.md`](THIRD-PARTY-NOTICES.md).
