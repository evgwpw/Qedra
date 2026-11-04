# Qedra

<!-- mcp-name: io.github.evgwpw/qedra -->

Computer algebra with verifiable answers: symbolic integration (Risch), limits, series, sums,
ODEs, polynomial algebra. Every result is checked independently, and step-by-step solutions are
available.

This package is a .NET tool (framework-dependent, .NET 10):

```
dnx Qedra --mcp
```

The `--mcp` mode is an MCP server over stdio. From a shell:

```
qedra --math -e "integrate(x^2, x)"
qedra --version
```

License: 0BSD. Source and releases: https://github.com/evgwpw/Qedra
