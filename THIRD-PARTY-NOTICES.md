# Third-party notices

Qedra itself is released under the Zero-Clause BSD license (see `LICENSE`).
Qedra and its builds include the third-party works below; their license texts are reproduced here.

## Rubi 4.17.3.0 (Rule-based Integration)

Files: `lib/rubi/rules/` — integration rules translated from the Mathematica sources of Rubi into Lisp data
(commit 61e9c18ea248061cd83c67882f7c91a73cef912d); `lib/rubi/engine.lisp` and `lib/rubi/utils*.lisp` reimplement
the rule engine and utility functions of Rubi following its sources. License text also in `lib/rubi/LICENSE-RUBI.txt`.
License: MIT. Project: https://rulebasedintegration.org/ (https://github.com/RuleBasedIntegration/Rubi)

```
MIT License

Copyright (c) 2018 Rule-Based-Integration Organization

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## symbolica-integrate (Rubi port to Rust; source of ported utility functions)

Files: `lib/rubi/utils.lisp`, `lib/rubi/utils-s.lisp`, `lib/rubi/utils-c.lisp`, `lib/rubi/inert.lisp` — separate
Lisp functions reimplemented after the corresponding functions of `symbolica-integrate` (Ben Ruijl's Rust port of
Rubi, `src/lib.rs`), verified against `IntegrationUtilityFunctions.m` of Rubi 4.17.3.0. Functions whose body was
translated from the Rust source carry a comment naming the function and its location in `src/lib.rs`; everything
else is the Rubi algorithm itself.
License: MIT. Project: https://github.com/symbolica-dev/symbolica-integrate, version 2.0.2,
commit 2759c3464589e24b1b3a746b5d6060c7b2e524a1 (2026-10-15). Only the MIT source of symbolica-integrate was read;
it was never built or run. Its dependency Symbolica (separate Symbolica Source-Available License) was not used,
read or analysed in any form.

```
MIT License

Copyright (c) 2026 Ben Ruijl

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## algebraic_integration (S. Blake, method for pseudo-elliptic integrals)

Files: `lib/integrate/blake.lisp` — a Lisp port of the method of S. Blake, "A Simple Method for Computing Some
Pseudo-Elliptic Integrals in Terms of Elementary Functions" (arXiv:2004.04910), following the algorithm and
the Mathematica implementation of the author (test data from the same repository: `research/intown/`).
License: MIT. Project: https://github.com/stblake/algebraic_integration

```
MIT License

Copyright (c) 2020 stblake

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## parallel_integrate_mixed (S. Blake, parallel Risch-Norman method, strict parts)

Files: `lib/integrate/ansatz-cert.lisp` — Hermite reduction of S(x)·sqrt(q(x)) (exact denominator bound) and the
non-elementarity certificate "non-zero holomorphic remainder with zero residues", after S. Blake, "Parallel Integration
over Simple Radical Extensions" I-III (arXiv 2608.29482, 2609.13643, 2610.04477); an algorithm port, not a line-by-line
translation of the author's Python/Mathematica code.
License: MIT. Project: https://github.com/stblake/parallel_integrate_mixed

```
MIT License

Copyright (c) 2026 Sam Blake

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## KaTeX 0.16.11

Files: `web/vendor/katex/` (`katex.min.js`, `katex.min.css`, `fonts/`).
License: MIT. Project: https://katex.org/

```
The MIT License (MIT)

Copyright (c) 2013-2020 Khan Academy and other contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## MathLive 0.111.4

Files: `web/vendor/mathlive/` (`mathlive.min.mjs`, `fonts/`, `sounds/`).
License: MIT. Project: https://mathlive.io/

```
Copyright (c) 2017 - present Arno Gourdol. All rights reserved.

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
```

## bso5 0.4.0 and bso5-components 0.2.0

Files: `web/vendor/bso5/`, `web/vendor/bso5-components/`.
License: MIT. Project: https://github.com/evgwpw/BSO5

```
MIT License

Copyright (c) 2025 Евгений Веприков

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
