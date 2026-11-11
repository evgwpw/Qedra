# Qedra

Английская версия: [README.en.md](README.en.md). Проект не связан с одноимённым приложением для iOS.

**Qedra** — система компьютерной алгебры на собственном диалекте Lisp (F# / .NET 10). Главное — ответы, которым можно
доверять: каждый результат проверяется независимо, нерешённое честно помечается, а решения можно разобрать по шагам.
Обычная задача считается за доли секунды, трудная (Риш, Грунц, Ковачич) — за секунды.

## Что это

- **Проверяемые ответы.** Первообразная проверяется дифференцированием, решение уравнения — подстановкой в исходное
  уравнение, суммы и рекуррентности — численным оракулом. В `--json` и MCP это поле `certificate`.
- **Сертификат Lean 4.** Для первообразной можно получить файл `.lean` с утверждением `HasDerivAt F f x`
  (`--lean`, в JSON `"certificate":"lean"`); проверка — Lean 4 + mathlib вне Qedra.
- **Правила Rubi.** В интегратор встроены правила интегрирования Rubi 4.17.3 (≈ 8 500 правил, перенесены в Lisp):
  каскад методов Qedra отвечает первым, Rubi — когда каскад не справился или его ответ громоздок; ответы Rubi тоже
  проверяются дифференцированием.
- **Доказанные отказы.** Если элементарной первообразной нет, алгоритм Риша это доказывает: `status: nonelementary` —
  это ответ, а не сбой. Если задача не решена, возвращается `status: unknown` с причиной, а не выдуманный результат.
- **Пошаговые решения.** `steps` в `--json` и MCP показывает правило и формулу на каждом шаге (по-русски и по-английски).
- **Два входа.** Математический язык (`--math`, файлы `.mth`) — формулы как на бумаге; Lisp — полный доступ к библиотеке.
- **Встраивание.** MCP-сервер для Claude Desktop и других клиентов, `--json` для агентов, браузерная версия.

Умеет: интегрирование (Риш, правила Rubi, рациональные функции, специальные функции — в том числе ₂F₁, функция Аппеля,
эллиптические, — определённые интегралы), пределы (Грунц), ряды,
символьные суммы и рекуррентности, ОДУ (включая Ковачича и решения через специальные функции), алгебру (факторизация,
Грёбнер, группы Галуа, алгебраические числа), линейную алгебру и жорданову форму, LP/ILP, теорию чисел с сертификатами,
интервальную арифметику и графики.

## Установка

Готовые сборки — в [Releases](https://github.com/evgwpw/Qedra/releases): `qedra-1.109.7.11-win-x64.zip`,
`qedra-1.109.7.11-linux-x64.tar.gz`, `qedra-1.109.7.11-osx-x64.tar.gz`, `qedra-1.109.7.11-osx-arm64.tar.gz`.
Они самодостаточны: установленный .NET не нужен. Распакуйте архив и запустите `qedra` (`qedra.exe` в Windows);
рядом лежит `Lisp.exe` — тот же запускатель под прежним именем.

```
$ qedra --version
Qedra 1.109.7.11
$ qedra --math -e "integrate(x^2, x)"
1/3*x^3
```

Из исходников нужен .NET 10 SDK:

```
dotnet build Lisp.slnx
dotnet test Lisp.slnx
src/Lisp.Host/bin/Debug/net10.0/Lisp.exe            # REPL: Lisp; --math — математический режим
```

## Примеры

Каждый вывод ниже получен запуском `qedra --math -e "…"` на этой версии.

Неопределённый интеграл:

```
$ qedra --math -e "integrate(x*exp(x), x)"
x*exp(x) - exp(x)
```

Неэлементарный интеграл: ответ — доказательство, а не ошибка (в `--json` видно `status: nonelementary` и причину в `note`):

```
$ qedra --math -e "integrate(exp(x^2), x)"
integrate(exp(x^2), x)
```

Дифференциальное уравнение:

```
$ qedra --math -e "dsolve(y' + y = x, y(x))"
y(x) = (C1 + x*exp(x) - exp(x))*exp(-x)
```

Уравнение и система многочленов:

```
$ qedra --math -e "solve(x^2 - 5*x + 6 = 0, x)"
{2, 3}
$ qedra --math -e "groebner([x^2 - y, y^2 - x], [x, y])"
[x - y^2, -y + y^4]
```

Предел и разложение на множители:

```
$ qedra --math -e "limit(sin(x)/x, x, 0)"
1
$ qedra --math -e "factor(x^4 - 1)"
(-1 + x)(1 + x)(1 + x^2)
```

Машиночитаемый ответ: одна строка JSON на запрос (поле `timing.ms` зависит от машины).

```
$ echo '{"op":"math","code":"diff(x^3 - 3*x, x)"}' | qedra --json
{"status":"answer","result":"(+ -3 (* 3 (^ x 2)))","pretty":"-3 + 3x^2","latex":"-3 + 3x^{2}","note":null,"conditions":null,"assumptions":null,"certificate":null,"steps":null,"warnings":null,"output":"","timing":{"ms":71,"timeout":false},"ok":true,"error":null,"stack":null}
```

Больше примеров с эталонами — в [`examples/`](examples/README.md); они выполняются тестами.

## MCP

`qedra --mcp` — MCP-сервер на stdio. Подключение в Claude Desktop (`claude_desktop_config.json`) или любом клиенте:

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

Инструменты `math`, `simplify`, `integrate`, `sum`, `solve`, `limit`, `series`, `groebner`, `equivalent`, `declare`
и другие возвращают единый ответ: `status` (`answer` / `unknown` / `nonelementary` / `error`), результат, `conditions`,
по запросу — `steps` и `certificate`. Однако серверу доступно чтение файлов через `load`, поэтому по умолчанию
включена песочница (см. ниже); параметры — [`docs/mcp.md`](docs/mcp.md).

### Установка как MCP-сервер

- **MCPB (Claude Desktop, без .NET):** скачайте `qedra-1.109.7.11.mcpb` из [Releases](https://github.com/evgwpw/Qedra/releases) и откройте файл — клиент предложит установку. Бандл самодостаточен: Windows x64, Linux x64, macOS x64/arm64.
- **Docker:** `docker run -i --rm ghcr.io/evgwpw/qedra` — сервер на stdio; имя в реестре MCP — `io.github.evgwpw/qedra`.
- **NuGet (.NET tool, нужен .NET 10):** `dnx Qedra --mcp` (или `dotnet tool install -g Qedra`, затем `qedra --mcp`).

```json
{
  "mcpServers": {
    "qedra": { "command": "docker", "args": ["run", "-i", "--rm", "ghcr.io/evgwpw/qedra"] }
  }
}
```

Для NuGet: `"command": "dnx", "args": ["Qedra", "--mcp"]`.

## Песочница

`qedra --sandbox [--allow-dir <путь>]...` ограничивает `load`/`load-math` каталогом библиотеки и указанными каталогами
во всех режимах: файл, `-e`, `--math`, `--json`, REPL. В режиме `--mcp` песочница включена по умолчанию, снимает её
`--unsafe`. Это защита от ошибок LLM (лишний `load`, чтение чужого файла), **а не изоляция ОС**: интерпретатор и хост —
один процесс, от злоумышленника песочница не защищает.

## Браузерная версия

<https://evgwpw.github.io/Qedra/> — тот же вычислитель, собранный в WebAssembly (AOT), с вводом формул и каталогом
примеров. Локальная сборка: `web/build.sh` (или `web/build.cmd`), запуск — `web/start.sh` / `web/start.cmd`.

## Документация

- [`docs/math-language.md`](docs/math-language.md) — входной математический язык: операции, функции, шаги, JSON-API.
- [`docs/lisp-library-guide.md`](docs/lisp-library-guide.md) — справочник библиотеки Lisp (сверяется тестом с кодом).
- [`docs/lisp-dialect.md`](docs/lisp-dialect.md), [`docs/lisp-modules.md`](docs/lisp-modules.md) — диалект и модули.
- [`docs/mcp.md`](docs/mcp.md) — MCP-сервер: инструменты, безопасность, протокол.
- [`docs/guide/core.md`](docs/guide/core.md) — короткая справка для LLM (по-английски), карточки тем — в `docs/guide/topics/`.

## Как сделано

Код написан в основном LLM-агентами по заданиям и под ревью автора: архитектура, выбор алгоритмов, приёмка — человек.
Корректность не основана на доверии к генерации: каждый результат проверяется независимо (производная от
первообразной, подстановка решения, сертификаты сумм и доказательств), набор — более 3300 тестов.

## Лицензия

0BSD — см. [`LICENSE`](LICENSE). Сторонние работы (правила Rubi — MIT, библиотеки браузерной версии) и тексты их
лицензий — [`THIRD-PARTY-NOTICES.md`](THIRD-PARTY-NOTICES.md).
