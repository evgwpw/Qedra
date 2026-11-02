# MCP-сервер (шаги 22.3–22.5)

`Lisp.exe --mcp` — сервер [Model Context Protocol](https://modelcontextprotocol.io) на stdio: LLM-клиент (Claude Code, Claude Desktop, Cursor, …) запускает процесс сам и вызывает инструменты CAS. Ответ каждого инструмента — тот же `ToolResponse`, что у режима `--json` (поля — `docs/math-language.md`, раздел «Из других программ»).

## Сборка

```
dotnet build src/Lisp.Host -c Release
```

Исполняемый файл — `qedra.exe` из релизного архива (в репозитории — `src\Lisp.Host\bin\Release\net10.0\Lisp.exe`; рядом каталог `lib\` — библиотеки CAS; рабочий каталог процесса не важен). Подойдёт и Debug-сборка (`bin\Debug\net10.0\Lisp.exe`).

## Подключение

**Claude Code** (область `user` — для всех проектов; без `--scope` — только текущий проект):

```
claude mcp add --scope user qedra -- <путь>\qedra.exe --mcp
claude mcp list
```

В сеансе Claude Code команда `/mcp` показывает состояние сервера и список инструментов.

**Claude Desktop** — файл `%APPDATA%\Claude\claude_desktop_config.json` (Settings → Developer → Edit Config), затем перезапуск приложения:

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

Тот же блок `mcpServers` подходит для `.mcp.json` проекта (Claude Code) и для других клиентов с конфигурацией в этом формате.

Параметры командной строки (после `--mcp`, подшаг 22.4):

| Параметр | Что делает |
|---|---|
| `--allow-dir <путь>` | разрешить `load`/`load-math` файлов из каталога (с подкаталогами); можно несколько раз. Например, рабочий каталог с `.mth`/`.lisp` пользователя |
| `--unsafe` | снять песочницу (чтение любых файлов) |
| `--max-memory-mb <N>` | предел управляемой памяти во время вызова (по умолчанию 4096; 0 — без проверки) |

Пример: `claude mcp add qedra -- <путь>\qedra.exe --mcp --allow-dir C:\math` или `"args": ["--mcp", "--allow-dir", "C:\\math"]`.

## Инструменты

| Инструмент | Параметры | Что делает |
|---|---|---|
| `math` | `code`, `steps?` | программа на математическом языке (операторы через `;` или перевод строки); `result`/`pretty` — по строке на оператор, `output` — вывод `print` |
| `evaluate` | `code`, `steps?` | Lisp-код; при ошибке `stack` — стек Lisp |
| `simplify` | `expr`, `syntax?`, `steps?` | каноническая форма |
| `diff` | `expr`, `var`, `order?`, `syntax?`, `steps?` | производная порядка `order` (по умолчанию 1) |
| `integrate` | `expr`, `var`, `from?`, `to?`, `syntax?`, `steps?` | неопределённый интеграл или определённый (обе границы); не найден — `status: unknown`, невычисленная форма; доказано неэлементарен (алгоритм Риша) — `status: nonelementary` |
| `sum` | `expr`, `var`, `from?` (0), `to`, `syntax?`, `steps?` | символьная сумма (шаг 21l.7): Фаульхабер для многочленов, Госпер/Абрамов для гипергеометрических/рациональных термов, Цайльбергер + rsolve для биномиальных; ответ — замкнутая форма (`sum(C(n,k)^2,k,0,n) = C(2n,n)`) или рекуррентность с начальными значениями, если гипергеометрической замкнутой формы нет (Апери): `note` «замкнутой формы нет…», `result` — `(recurrence S n …)`; `to` — верхняя граница (обычно `n`) |
| `solve` | `equations`, `vars`, `syntax?`, `steps?` | множество решений уравнения (`x`) или системы (`[x + y = 3, x - y = 1]`, `[x, y]`; можно массивом строк); `conditions` — условия на параметры |
| `expand` | `expr`, `syntax?`, `steps?` | раскрытие скобок и степеней сумм |
| `factor` | `expr`, `syntax?`, `steps?` | разложение на множители над ℤ |
| `together` | `expr`, `syntax?`, `steps?` | сумма дробей → одна дробь в несократимом виде |
| `apart` | `expr`, `var`, `syntax?`, `steps?` | разложение на простейшие дроби по `var` |
| `limit` | `expr`, `var`, `point`, `side?`, `syntax?`, `steps?` | предел (`point` — число, `∞`, `-∞`; `side` — `plus`/`minus`); не найден — `status: unknown`, невычисленный `limit(...)` |
| `series` | `expr`, `var`, `point?`, `order?`, `syntax?`, `steps?` | ряд Тейлора/Лорана до `O(var^order)` (по умолчанию точка 0, порядок 6) |
| `groebner` | `polys`, `vars`, `order?`, `syntax?`, `steps?` | приведённый базис Грёбнера (вектор многочленов); `order` — `lex` (по умолчанию), `grlex`, `grevlex` |
| `linear-algebra` | `expr`, `fn`, `var?`, `func?`, `steps?` | точная линейная алгебра (шаг LA.4): `expr` — матрица `[[2,1],[0,2]]` (математический язык); `fn`: `jordan_form` (пара `[P, J]`, A = P·J·P⁻¹), `jordan_blocks`, `mat_exp` (e^{A·t}, `var` по умолчанию встроенное `t`; сертификаты d/dt E = A·E и E(0) = I), `mat_power` (Aⁿ, `var` по умолчанию `n`; нильпотентные блоки λ=0 — нули с условием n ≥ s в `conditions`), `mat_fn` (f(A), `func` — например `exp` или лямбда), `diagonalize` (`[P, D]`), `is_diagonalizable`, `eigenvalues`, `eigenvectors`; результат — тензор `[[..], ..]` |
| `linear-programming` | `objective`, `dir`, `constraints`, `rhs`, `relations?`, `integer?`, `steps?` | линейное и целочисленное программирование (шаг LP.3, точная рациональная арифметика): `objective` — коэффициенты c (вектор `"[3, 5]"`), `dir` — `max`/`min`, `constraints` — матрица A, `rhs` — правые части b, `relations` — вектор `"<="`/`">="`/`"="` (по умолчанию все `"<="`), `integer` — вектор классов переменных `"int"`/`"bin"`/`"free"` (при отсутствии — обычное ЛП). Ответы: `(optimal x value y)` — оптимум с двойственными ценами, `(infeasible y)` — несовместность (сертификат Фаркаша, `status: no-solution`), `(unbounded x d)` — неограниченность (луч), `(unknown x value nil)` — лимит узлов ветвления. Сертификат (`certificate: true`): оптимум — lp-check (Ax ∘ b, x ≥ 0, двойственная допустимость, cᵀx = value = bᵀy), несовместность — лемма Фаркаша, неограниченность — луч, целочисленное — повторный счёт дерева ветвления (ilp-check) |
| `declare` | `symbol`, `domain`, `steps?` | декларация домена/интервала символа на сессию (`ℝ ℤ ℚ ℕ ℂ`, `positive`, `nonnegative`, `negative`, `nonpositive`, `(0, ∞)`, `[0, 1]`); декларации одного символа пересекаются; `result` — `x ∈ D` |
| `undeclare` | `symbol`, `steps?` | снять все декларации символа |
| `declarations` | — | список действующих деклараций (по строке `x ∈ D`) |
| `equivalent` | `a`, `b`, `vars?`, `syntax?`, `steps?` | равны ли выражения: `result` — `true` / `false` / `unknown` (`status: answer`), см. ниже |
| `guide` | `topic` (необяз.) | ядро справки и список тем (в `result`; тот же текст — ресурс MCP `lisp://guide`) или карточка темы / синонима (`DSolve` → `ode`) |
| `code` | `kind`, `arg?`, `depth?`, `json?`, `no_body?` | запросы к коду `lib\` (как `Lisp.exe --query`, шаг Q.2): def sig refs callers callees module outline search deps unused; `result` — компактный текст или JSON-текст (`json: true`); неизвестное имя — `status: error` с похожими именами |
| `reset` | — | новая сессия: переменные, функции и декларации доменов забываются |

* `syntax`: `math` (по умолчанию — инфиксная запись языка: `x^2*sin(x)`, `sqrt(x)`, `π`, `∞`, `a = b`) или `lisp` (S-выражения).
* `steps`: `none` (по умолчанию) | `brief` | `full` | `trace` | `attempts` — пошаговое решение в поле `steps` (шаг S.1): дерево шагов `{rule, title, comment, before, before_pretty, after, after_pretty, level, children}` (`+ omitted`, если вложенные шаги скрыты обрезкой). `brief` — только главные (`main`) шаги верхнего уровня, `full` — всё дерево (глубина ≤ 8, ≤ 200 узлов; обрезка — строка в `warnings`), `trace` — плюс шаги упрощателя (`rule` `simplify:имя`, `level: detail`). `rule` — стабильный английский идентификатор приёма, `title`/`comment` — по-русски (с `lang: "en"` — по-английски). Шаги пишут `diff`, `simplify`, `integrate`, `solve`, `limit`, `series` и базисы Грёбнера (шаг S закрыт); у остальных — `[]`.
* `steps: attempts` (шаг D2a) — журнал ПОПЫТОК вместо шагов: то же дерево, но узел — каждая рамка `with-step` (успешная и неудачная): `comment` = «успех: пояснение» | «отказ: причина — N мс» (+ ` ×k` — схлопнутые одинаковые повторы), `level` = `attempt`, `after` пуст (результат неудачной попытки неизвестен), `before` — вход стратегии. Причина отказа: `нет результата (#f)` (тело каскада вернуло `#f`), сообщение ошибки или явная (`attempt-fail`, шаг D2b). Лимиты как у `full` (глубина ≤ 8, ≤ 200 узлов; обрезка — строка в `warnings`). В Lisp/языке то же делает `(explain выражение)` — печатает дерево «стратегия — успех/отказ: причина — мс» и возвращает значение.
* `lang` (шаг S.5): `ru` (по умолчанию) | `en` — язык заголовков и пояснений шагов (у всех инструментов с `steps`): перевод — словарь `src\Cas.Algebra\StepDict.fs` (`rule` → английский заголовок и фразы пояснения; формулы и выражения языконезависимы). По-русски совокупность решений в шагах печатается «x = 2 или x = 3», по-английски — «x = 2 or x = 3». Шаг без перевода остаётся русским, его `rule` перечислен в `warnings` («no English translation for step rules: …»); пометка об обрезке на выбранном языке. Неизвестное значение — ошибка. В языке: `steps(e, "full", "en")`, `step_list(e, "full", "en")`. Длинные выражения шага обрезаются до 2000 символов. Формат и правила — `docs\math-language.md` («Пошаговые решения»).
* `certificate` (boolean, по умолчанию `false`; у `simplify`, `diff`, `integrate`, `solve`, `expand`, `factor`, `together`, `apart`, `limit`, `series`, `groebner`, `equivalent`, `sum`, `linear-programming`) — сертификат (подшаг 22.6): проверка ответа независимым путём, поле `certificate` ответа = `{kind, verified, method, detail}`. Виды: `derivative` (integrate: `d/dx F − f = 0`; определённый — и подстановка пределов), `substitution` (solve: подстановка решений в уравнения; решения `root-of` — `skipped`, при смеси — `partial`), `equivalence` (simplify/expand/factor/together/apart и `equivalent` → `true`), `counterexample` (`equivalent` → `false`: `detail.point`, значения; рациональная точка проверяется подстановкой точно), `ideal_membership` (groebner: остаток каждого исходного многочлена по базису равен 0; доказывает только вложение исходного идеала в идеал базиса, множителей-коэффициентов для Lean нет — шаг 22'), `sum` (шаг 21l.7: замкнутая форма — оракул `sum-check`, прямая сумма в целых точках, `verified: "numeric"`), `recurrence` (шаг 21l.7: ответ-рекуррентность проверяется прямыми суммами через начальные точки, `verified: true`), `none` (diff, limit, series — проверка не предусмотрена). `verified`: `true`/`false`, `"numeric"`, `"partial"`, `"skipped"` (причина — `detail.reason`), `"timeout"` (проверка входит в `timeout_s`; ответ сохраняется, статус не меняется). `verified: false` — тревожный сигнал: в `warnings` добавляется «ответ не прошёл проверку». Подробнее — `docs\math-language.md` («Из других программ»), `docs\LLM-GUIDE.md`.
* `timeout_s` (у всех, кроме `reset`): предел времени вызова в секундах, по умолчанию 60, не больше 600 (см. ниже).
* `max_chars` (у всех, кроме `reset`): предел длины `result`/`pretty`/`error`, по умолчанию 20 000, не больше 200 000.
* Выражение в режиме `math` вычисляется как вызов языка `op(expr, var, …)` — переменные и функции, заданные инструментом `math` (`a := 2`, `f(x) := …`), подставляются.
* Неизвестный аргумент или неверный тип — ответ `status: error` с перечнем допустимых аргументов; неизвестный инструмент — ошибка JSON-RPC `-32602`.
* Результат `tools/call`: `content[0].text` — ToolResponse как JSON-текст, `structuredContent` — тот же объект; `isError` не используется (ошибка вычисления — `status: error`).

## Пример сессии (JSON-RPC, по строке на сообщение)

```
→ {"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"demo","version":"1"}}}
← {"result":{"protocolVersion":"2025-06-18","capabilities":{"logging":{},"tools":{}},"serverInfo":{"name":"qedra","version":"22.4"},"instructions":"Computer algebra system ..."},"id":1,"jsonrpc":"2.0"}
→ {"jsonrpc":"2.0","method":"notifications/initialized"}
→ {"jsonrpc":"2.0","id":2,"method":"tools/list"}
← {"result":{"tools":[{"name":"math","description":"...","inputSchema":{"type":"object","properties":{...},"required":["code"],"additionalProperties":false}}, ...]},"id":2,"jsonrpc":"2.0"}
→ {"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"solve","arguments":{"equations":"a*x^2 = 1","vars":"x"}}}
← {"result":{"content":[{"type":"text","text":"{\"status\":\"answer\",...}"}],
             "structuredContent":{"status":"answer","result":"{(* -1 (sqrt (^ a -1))), (sqrt (^ a -1))}","pretty":"{-sqrt(1/a), sqrt(1/a)}",
               "note":null,"conditions":[{"condition":"a ≠ 0","sexpr":"(/= a 0)","reason":"solve: старший коэффициент квадратного уравнения"}],
               "assumptions":null,"certificate":null,"steps":null,"warnings":null,"output":"","timing":{"ms":63,"timeout":false},
               "ok":true,"error":null,"stack":null}},"id":3,"jsonrpc":"2.0"}
→ {"jsonrpc":"2.0","id":40,"method":"tools/call","params":{"name":"integrate","arguments":{"expr":"x*sin(x)","var":"x","certificate":true}}}
← {... "structuredContent":{"status":"answer","result":"...","pretty":"-x*cos(x) + sin(x)",
       "certificate":{"kind":"derivative","verified":true,"method":"символьно: simplify(d/dx F − f) = 0",
         "detail":{"integrand":"x*sin(x)","antiderivative":"-x*cos(x) + sin(x)","derivative":"x*sin(x)","residual":"0"}}, ...}}
→ {"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"integrate","arguments":{"expr":"sin(x)/x","var":"x"}}}
← {"result":{"content":[...],"structuredContent":{"status":"unknown","result":"(integrate (* (^ x -1) (sin x)) x)","pretty":"integrate(sin(x)/x, x)",
               "note":"integrate: ответ не найден — возвращена невычисленная форма", ...}},"id":4,"jsonrpc":"2.0"}
→ {"jsonrpc":"2.0","id":5,"method":"tools/call","params":{"name":"integrate","arguments":{"expr":"1/log(x)","var":"x","certificate":true}}}
← {... "structuredContent":{"status":"nonelementary","result":"(integrate (^ (log x) -1) x)","pretty":"integrate(1/log(x), x)",
       "note":"интеграл неэлементарен: алгоритм Риша (теорема Лиувилля) доказал, что первообразной в элементарных функциях нет",
       "conditions":[{"condition":"risch-nonelementary(integrate(1/log(x), x))","sexpr":"(risch-nonelementary (integrate (^ (log x) -1) x))","reason":"..."}],
       "certificate":{"kind":"nonelementary","verified":"skipped","method":"алгоритм Риша (теорема Лиувилля): независимой проверки нет",
         "detail":{"integral":"integrate(1/log(x), x)","reason":"..."}}, ...}}
```

**Неэлементарные интегралы (шаг 21k.4).** Алгоритм Риша (последняя стратегия интегратора) доказывает, что первообразной в элементарных функциях нет. Тогда `integrate` возвращает прежнюю невычисленную форму `(integrate f x)`, а ответ получает `status: "nonelementary"` (это ответ, не отказ), `note` — причина, в `conditions` — запись `risch-nonelementary(…)` (канал `record-condition`), сертификат (по запросу) — `kind: "nonelementary"`, `verified: "skipped"` (доказательство алгоритма, независимой проверки нет). Статус `nonelementary` — только когда значение запроса — неопределённый `(integrate f x)` и условие описывает именно его; определённый интеграл с пределами остаётся `unknown`. Частичный ответ `F + c·integrate(r, x)` (r доказанно неэлементарен) — `status: "answer"` с предупреждением в `warnings` о невычисленной форме; остаток перечислен в `conditions`.

(SDK экранирует не-ASCII символы в JSON-RPC как `\uXXXX` — для разборщика JSON это те же строки.)

## Таймаут, отмена, лимиты, песочница (подшаг 22.4)

**Таймаут и отмена.** Каждый вызов выполняется под сторожем: по истечении `timeout_s` (по умолчанию 60 с), по отмене запроса клиентом (`notifications/cancelled`) или при превышении предела памяти поднимается флаг отмены, интерпретатор прерывается на ближайшей проверке, ответ — `status: "timeout"`, `timing.timeout: true`, `note` с причиной («таймаут 60 с», «запрос отменён клиентом», «превышен предел памяти 4096 МБ»). Сессия остаётся рабочей: `unwind-protect`/`assuming` при прерывании восстанавливают состояние (временные декларации снимаются), перехват `print` закрывается; Lisp-форма `try` прерывание не перехватывает. После отмены запроса клиентом интерпретатор освобождается за доли секунды — следующий вызов выполняется сразу (ответ на сам отменённый запрос клиенту по протоколу не нужен).

```
→ {"jsonrpc":"2.0","id":5,"method":"tools/call","params":{"name":"math","arguments":{"code":"g(n) := g(n + 1); g(0)","timeout_s":2}}}
← {... "structuredContent":{"status":"timeout","note":"вычисление прервано: таймаут 2 с; сессия сохранена и готова к следующему вызову",
       "timing":{"ms":2041,"timeout":true},"ok":false,"error":"Прервано: таймаут 2 с", ...}}
```

Где проверяется флаг (стоимость — одно чтение поля, на бенчмарках не измеряется): каждый нехвостовой вызов Lisp-функции и уровень рекурсии упрощателя (`checkStack`), каждый хвостовой вызов (трамплин), внешняя итерация и шаг редукции Бухбергера (Грёбнер на F#), перебор комбинаций и попытки подстановок факторизации. Длинная операция F# без проверок (одно умножение огромных многочленов, НОД) флаг не видит: если вычисление не остановилось за 5 с после таймаута, сервер отвечает `timeout` с предупреждением и **завершает процесс** — клиент перезапускает сервер, состояние сессии теряется (в Claude Code — `/mcp` → reconnect).

**Лимиты ответа.** `result`, `pretty`, `error` — до `max_chars` символов (по умолчанию 20 000); `output` (`print`/`display`) — до 10 000 (сверх того вывод не хранится, только считается); `steps` — до 200 шагов, выражения шага — до 2 000 символов. Обрезка — с « …» в конце строки и пометкой в `warnings` (`"output обрезан: показаны первые 10000 из 50000 символов"`). Глубина рекурсии — прежний логический лимит (`set-max-depth`, по умолчанию 100 000) и защита системного стека. Память — управляемая куча проверяется сторожем раз в 50 мс: больше `--max-memory-mb` (4096) → прерывание с причиной.

**Песочница** (по умолчанию; снимает `--unsafe`; все ограничения — `src\Lisp.Core\Sandbox.fs`). Это защита от ошибок LLM, а не от злоумышленника:
* чтение файлов — `(load "файл")`, `(load-math "файл.mth")` (builtin `read-text-file`) — только из каталога `lib\` рядом с `Lisp.exe` и каталогов `--allow-dir` (с подкаталогами; пути сравниваются после нормализации, `..` не помогает); нарушение → `status: "error"`, `error`: «load: чтение файла «…» запрещено (песочница: чтение файлов (load, load-math) — только из …; запись файлов и запуск процессов недоступны; снять ограничения — запуск без --sandbox (в режиме --mcp — --unsafe), добавить каталог — --allow-dir <путь>)»;
* записи файлов и запуска процессов в языке нет (будущие такие builtins обязаны вызывать `Sandbox.checkWrite`/`checkProcess`).

**Та же песочница вне MCP.** `lisp --sandbox [--allow-dir <путь>]... <режим>` включает её в режимах `файл.lisp`, `-e`, `--math` (файл и `-e`), `--json` и REPL; `--allow-dir` можно повторять (несуществующий каталог — ошибка, код 2). Без флага поведение прежнее. Файл, указанный в командной строке, читается всегда (его выбрал человек), ограничение действует на `load`/`load-math` из него. `lisp --version` печатает версию продукта (`Qedra 1.109.7.11` — из `<Version>` в `Directory.Build.props`, в коде не дублируется).

REPL, `lisp файл.lisp/.mth` и `--json` без `--sandbox` работают без песочницы и сторожа, как раньше.

**Декларации по сессиям.** Декларации доменов (`x :∈ ℝ`, `declare`, `assuming`) — состояние сессии (окружения), а не символа: разные сессии `AgentApi`/`--json` в одном процессе не видят деклараций друг друга, `reset` снимает декларации сессии; системная `pi > 0` действует везде.

## Устройство и ограничения

* Протокол — официальный C# SDK `ModelContextProtocol.Core` 1.4.1 (без Hosting/DI); код — `src\Lisp.Host\McpServer.fs`: таблица инструментов (`McpHost.tools`, новый инструмент — одна строка, если операция есть в `AgentApi.handleRequest`), схемы входа строятся по таблице.
* Сессия одна на процесс (методы `defmethod`, правила `defrule` и типы `deftype` — общие для процесса таблицы; переопределять их через `evaluate` не стоит); библиотеки грузятся при старте, первым в очереди идёт прогревочный интеграл (JIT). Вызовы выполняются по одному в потоке интерпретатора (стек 256 МБ); одновременные вызовы клиента ждут в очереди, порядок их выполнения не гарантирован — зависимые вызовы клиент делает после ответа на предыдущий.
* stdout — только протокол: `print`/`display`/трассы попадают в поле `output` ответа, вывод вне вызовов и сообщения сервера — в stderr.
* Закрытие stdin завершает сервер; ответы на ещё не выполненные запросы при этом теряются.
* Пока нет (подшаг 22.6): сертификатов.

## equivalent, guide (подшаг 22.5)

**`equivalent(a, b)`** проверяет равенство выражений; `status` всегда `answer`, вердикт — в `result`/`pretty`: `true`, `false` или `unknown`, пояснение — в `note`.
1. Символьно: разность `a - b` упрощается до 0 одним из способов `simplify`, `expand`, `together`, `cancel`, `together + expand` → `true` («верно там, где оба выражения определены»).
2. Иначе численно: до 8 допустимых проб (до 60 попыток, фиксированное зерно — ответ воспроизводим). Значение каждого символа — случайное рациональное внутри его деклараций (ℕ ℤ ℚ ℝ, интервалы; границы и 0 не берутся); необъявленный символ пробуется вещественным числом. Выражения считаются числом (`SolveNum.numEvalEnv`, комплексная арифметика, главные ветви); пробы, где выражение не вычисляется или даёт ∞/NaN, пропускаются. Значения различаются (относительно 1e-8) → `false`, в `note` — контрпример: точка и оба значения («x = -27/7: первое выражение = 3.857…, второе = -3.857…»).
3. Все пробы совпали, но символьно не доказано → `unknown` («численно совпадают в N случайных точках — это не доказательство»). `true` по численной проверке никогда не выдаётся. Нет ни одной допустимой пробы → `unknown`.

Ограничения: `false` — по вещественным пробам с учётом деклараций (необъявленный `x`: `sqrt(x^2) = x` даёт `false` с `x < 0`; объявите `x` положительным); равенство в точках неопределённости не проверяется; `vars` — необязательный список дополнительных символов для проб (по умолчанию — все свободные символы обоих выражений); `sin(2x) = 2 sin(x) cos(x)` — `unknown` (упрощатель кратные углы не раскрывает).

**`guide`** (шаги GD.1–GD.2) — справка по запросу, по-английски, встроена в сборку (`EmbeddedResource`). Без аргумента — короткое ядро `docs\guide\core.md` (синтаксис, формат ответа, сертификаты, выбор инструмента) и список тем; с `topic` (17 карточек: `algebra`, `solve`, `calculus`, `integration`, `ode`, `sums`, `linear-algebra`, `polynomials`, `number-theory`, `curves`, `plots`, `numerics`, `optimization`, `forms`, `domains`, `steps`, `units`) — карточка `docs\guide\topics\<тема>.md` (функции с сигнатурами, проверяемые примеры, ловушки); имя из других систем (Mathematica, Maple) или имя инструмента (`DSolve`, `FactorInteger`, `Eigenvalues`, `integrate`) возвращает нужную карточку по таблице `docs\guide\synonyms.md` (тема `synonyms` — вся таблица); неизвестная тема — ошибка с подсказкой «Did you mean» (расстояние редактирования) и списком тем. В командной строке то же: `Lisp.exe --guide [тема]`. Ресурс `lisp://guide` (`resources/list`, `resources/read`, MIME `text/markdown`) — тот же текст, что у `guide` без темы (ядро и список тем); прежний длинный `docs\LLM-GUIDE.md` теперь короткая ссылка на эти файлы. Тест `GuideTests` проверяет размеры, существование функций и выполнение примеров карточек, а также что каждый экспорт модулей библиотеки назван в карточке или в `docs\guide\not-covered.txt`. Рекомендуется один раз прочитать перед первым вычислением; сервер также передаёт краткую инструкцию в `initialize`.

**Параметры `declare`:** `domain` — одно выражение на вызов (не вектор: `[0, 1]` здесь отрезок); несколько ограничений — несколько вызовов. `symbol` — только имя (буквы, цифры, `_`). Декларации действуют на всю сессию до `undeclare`/`reset`, видны в `assumptions` каждого ответа.
