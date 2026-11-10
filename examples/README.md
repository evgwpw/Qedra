# Примеры

Запуск: `src/Lisp.Host/bin/Debug/net10.0/Lisp.exe examples/01-integrals.mth` (или `dotnet run --project src/Lisp.Host -- examples/01-integrals.mth`).
Файл `.mth` — входной математический язык (каждый оператор печатает своё значение); файл `.lisp` — Lisp
(вывод — `(display x) (newline)`, `print` нет; в конце запуск файла печатает значение последней формы, поэтому в эталонах есть строка `nil`).

| Файл | О чём |
|---|---|
| `01-integrals.mth` | интегралы: таблица, подстановка, по частям, рациональные дроби, определённый; неэлементарные остаются невычисленными |
| `02-risch.lisp` | алгоритм Риша: `risch-nonelementary?` (`#t` — доказано, что первообразной нет), найденная первообразная и проверка дифференцированием |
| `03-sums-products.mth` | суммы и произведения с символьной границей (Фаульхабер, Абрамов, Госпер, Цайльбергер + `rsolve`) |
| `04-limits.mth` | пределы (каскад, алгоритм Грунца для башен exp/log) |
| `05-solve.mth` | уравнения и системы (в том числе нелинейные — через базис Грёбнера) |
| `06-groebner.mth` | базисы Грёбнера, `normal_form`, `eliminate` |
| `07-series.mth` | ряды Тейлора и Лорана |
| `08-linear-algebra.lisp` | `rref`, `nullspace`, `eigenvalues`, `eigenvectors`, жорданова форма, `mat-exp`, `mat-power` |
| `09-steps.mth` | пошаговые решения `steps(…, "full")`, английские заголовки |
| `10-explain.lisp` | `explain` — журнал попыток: успешные и отказавшие стратегии с причинами |
| `11-simplify.mth` | упрощение, `expand`, `factor`, `together`, `apart`, производные |
| `12-linear-programming.mth` | линейное и целочисленное программирование: `lp_maximize`, `lp_solve`, `ilp_solve` (с сертификатами) |
| `13-dynamic-programming.lisp` | динамическое программирование: рюкзак, LCS, Левенштейн, размен, способы, Беллман–Форд, `defmemo` (с сертификатами) |
| `14-certified-numerics.mth` | численность с сертификатами: `interval`, `certified_integral`, `certified_roots`, `certified_sum` — гарантированные границы интегралов, корней и сумм |
| `15-c-finite.mth` | C-конечные последовательности: `cfinite`, `cf_term` (F(100)), `cf_terms`, `cf_prove` (тождества Фибоначчи и контрпример), `guess_recurrence`, `cf_gf` |
| `16-optimization.mth` | экстремумы и множители Лагранжа: `critical_points`, `extrema` (min/max/saddle/unknown), `hessian`, `lagrange` |
| `17-algebraic-integrals.mth` | алгебраические и эллиптические интегралы: Чебышёв (ответ и отказ), F/E/K, Π третьего рода, башня ℚ(√2,√3) для `1/(x⁴+4x²+1)` |
| `18-number-theory.mth` | теория чисел: `powmod`, `crt`, `isprime`, `factorint`, `pell`, `pell_solutions`, `sum_of_two_squares`, `pythagorean_triples`, диофантово уравнение, GF(2⁸) (AES) |
| `19-differential-forms.mth` | дифференциальные формы: `extd`, `wedge`, `pullback`, `form_potential` (и отказ для dθ), `grad`/`div`/`curl`/`laplacian`, `potential`, `vector_potential`, `integrate_form` (работа, площадь, поток через сферу) |
| `20-ode.mth` | ОДУ (ODE.0): квадратуры `y′ = f(x)`, `y″ = f(x)`, объект `ode-solution`, сертификат `ode_check`; вне квадратур — `unknown` |
| `demo.mth` | обзор входного языка (шаг 21) |
| `programs.mth` | программирование на входном языке: циклы, `return`, итераторы |

## Эталоны и тест

Рядом с каждым примером лежит `имя.expected` — ожидаемый стандартный вывод. Тест `ExamplesTests`
(`tests/Lisp.Mcp.Tests/ExamplesTests.fs`) запускает каждый `*.lisp`/`*.mth` из этого каталога отдельным процессом
`Lisp.dll файл`, требует код возврата 0 и сравнивает вывод с эталоном (концы строк и пробелы в конце не важны;
время вида `12.3 мс` заменяется на `N мс` — его печатает `explain`). Так примеры не устаревают молча.

- Прогнать только примеры: `dotnet test tests/Lisp.Mcp.Tests --filter "FullyQualifiedName~ExamplesTests"`.
- Новый пример: положить файл, один раз выполнить `UPDATE_EXAMPLES=1 dotnet test tests/Lisp.Mcp.Tests --filter "FullyQualifiedName~ExamplesTests"`
  (перезаписывает `.expected` по текущему выводу), **просмотреть эталон глазами** и закоммитить оба файла.
- Правило: в эталон попадает только то, что реально работает; ответ «не знаю» или невычисленная форма — тоже честный вывод, но комментарием в файле это нужно оговорить.
- Пример должен считаться быстро (< ≈ 1 с); медленный вынести в отдельную теорию с `Trait("Category", "Slow")`.
