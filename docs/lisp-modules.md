# Модули библиотеки Lisp

Шаг 21h' (бывший шаг 23). Файлы `lib\*.lisp` — модули: у каждого свой набор экспортированных (публичных) имён и приватные
вспомогательные. До шага 21h' все определения библиотеки были глобальными, и вспомогательное имя в одном файле молча
перекрывало одноимённое в другом (в шаге 18 `solve.lisp` перезаписал `find-pivot` из `tensor.lisp`).

## Как написать модуль

Файл начинается с формы `module` (комментарии перед ней допустимы; **первой формой** файла она должна быть всегда):

```lisp
(module tensor
  (export tensor? tensor shape tref transpose det inv))

(define (find-pivot ...) ...)   ; приватное: не в списке экспорта
(define (det m) ...)            ; публичное
```

* `(module имя (export имя ...))` — имя модуля и список экспорта. `(module имя)` без `export` — файл без новых экспортируемых имён.
* Определения файла — `define` и `defmacro` верхнего уровня — принадлежат модулю.
* Модуль может состоять из нескольких файлов (так устроены `lib\integrate\*.lisp` и `lib\mathlang\*.lisp`): в каждом файле
  пишется `(module то-же-имя ...)`; списки экспорта складываются, приватные имена файлов модуля общие. Экспортированное
  файлом имя должно быть определено к концу **этого** файла.
* Порядок загрузки задаёт `lib\prelude.lisp` (он сам — модуль `prelude`).

## Правила видимости

| Имя | Как хранится | Кто видит |
|---|---|---|
| экспортированное | обычное глобальное, как до шага 21h' | все модули, REPL, математический язык, тесты, F# |
| приватное (определено в модуле, не в `export`) | глобальная привязка с именем `модуль::имя` | внутри модуля — по короткому имени; снаружи — только `модуль::имя` |

* Ссылку на имя внутри модуля компилятор разрешает так: локальная переменная → приватное имя модуля (`модуль::имя`) →
  глобальное имя. **Позднее связывание сохранено**: экспортированные имена по-прежнему ищутся в глобальной ячейке при
  каждом вызове, поэтому пользователь, переопределивший `f` в REPL, влияет и на вызовы `f` из библиотеки.
* Тело функции компилируется лениво, в области имён модуля, где функция определена (запоминается в шаблоне лямбды);
  условия правил `defrule` — в области имён модуля правила; макрос раскрывается в области имён **вызывающего** кода
  (поэтому имена, на которые раскрывается экспортируемый макрос, тоже должны быть экспортированы: `deftest` → `register-test`).
* Код вне модуля (REPL, пользовательский файл без `module`, `eval`, математический язык, `--json`) видит только
  глобальные имена и может переопределять что угодно. Приватное имя доступно как обычный символ `модуль::имя`
  (чтение, `define`, `set!`, `trace`), что удобно для тестов и отладки: `(integrate::int-size '(+ x 1))`.
* Двоеточие в середине имени (`модуль::имя`) — обычный символ; символ с двоеточием **первым** знаком (`:where`) — самовычисляющееся ключевое слово, `define`/`set!` его — ошибка.
* Имена в стеке ошибок, `#<функция ...>`, `describe`, `trace` — `модуль::имя` для приватных функций.
* Математический язык вызывает Lisp-функцию по имени как глобальную. Всё, что он вызывает (список в
  `docs\math-language.md`), и всё, на что раскрывается сгенерированный им код (`m-...` в `lib\mathlang`, он вычисляется через
  `eval` в глобальной области), должно быть **экспортировано**.

## Что принадлежит модулю, а что глобально

| Определение | Принадлежность |
|---|---|
| `define`, `defmacro` | модуль: экспортированное — глобальное, прочее — приватное (`модуль::имя`) |
| `defmethod` | запись в глобальной таблице методов (методы действуют на все модули); тело компилируется в области имён модуля. Тот же метод (операция + типы) из **двух разных модулей** — ошибка загрузки |
| `defrule` | запись в глобальной таблице правил; условие — в области имён модуля. Правило с тем же именем из другого модуля — ошибка загрузки |
| `deftype` | типы глобальны (типы нужны диспетчеризации и печати объектов `#<tensor ...>`); конфликтов типов загрузчик не проверяет |
| `put` / `get`, `declare` | глобальное состояние процесса/сессии, к модулям не относятся |

Код вне модуля (пользователь) переопределяет и методы, и правила свободно (и снимает «владение» модуля).

## Конфликты — ошибка при загрузке

* два модуля экспортируют одно имя: «модуль B экспортирует имя f, которое уже экспортирует модуль A»;
* модуль определяет (приватно) имя, которое экспортирует другой модуль: «модуль B определяет имя f, которое экспортирует
  модуль A (переименуйте приватное имя; переопределять чужой экспорт нельзя)»;
* экспорт или приватное определение с именем встроенной функции (builtin) — ошибка;
* экспорт неопределённого имени: «модуль M экспортирует имя f, но не определяет его»;
* `(module ...)` не первой формой файла, либо вычисленная вне загрузчика: «module: объявление модуля допустимо только
  первой формой загружаемого файла».

## Как выбирать экспорт

Экспортируйте минимум — то, что реально используется извне: документированный API, имена, которыми пользуются другие
модули/F#/математический язык/тесты. Остальное — приватное; тест, которому нужен внутренний помощник, обращается к нему как
`модуль::имя`.

Проверка достаточности экспорта — `Evaluator.checkModules env` (тест `ModuleTests`): компилирует все тела всех лямбд всех
модулей и перечисляет глобальные имена, на которые они ссылаются, но которых нигде нет (обычно — обращение к
неэкспортированному имени другого модуля либо опечатка). `Evaluator.duplicateDefinitions env` — имена, определённые в нескольких
модулях (раньше такие определения молча перезаписывали друг друга).

## Экспорт библиотеки (шаг 21h')

| Модуль (файлы) | Экспорт |
|---|---|
| `prelude` (`prelude.lisp`) | `prelude-loaded reverse map map2 filter foldl range every? any? take drop last butlast member? append-map vector-map vector-map2` |
| `tensor` | `tensor? tensor tensor-raw tensor-shape-list tensor-data tensor-from-flat as-tensor make-tensor identity-matrix tensor->list shape rank-of strides tref transpose vec+ vec- scale dot norm cross mat mat-t mat-mul det inv rank outer contract join-strings` |
| `logic` | `unknown true? false? known? not3 and3 or3 and3-all or3-all` |
| `set` | `set? set->list list->set set card empty-set? union set-intersection intersection set-difference set-map set-filter power-set in? subset? dispatch-method` |
| `domain` | домены и интервалы, `declare undeclare declarations reset-declarations assuming assuming-call`, предикаты знака (`real? positive? ...`), `op-expr? constraints-of contains-sym? domain-rank` |
| `rules` | — (только правила) |
| `match` (шаг AC.1) | `ac-match ac-match-all ac-subst ac-pattern-var? ac-segment-var? ac-match-sub ac-replace-sub pattern-from-dag lean-heads` — AC-сопоставление, поиск в подвыражениях (AC.5), см. справочник § «match» |
| `poly` | `coefficients leading-coefficient coefficients->poly poly-divides?` |
| `puiseux` (шаги A2.1–A2.2) | `newton-polygon puiseux puiseux-check puiseux-terms puiseux-at puiseux-rational algebraic-series algebraic-series->expr algebraic-series-coeff algebraic-series?` — ряды Ньютона–Пюизё: многоугольник Ньютона, рёбра/φ, расширения полей (все вложения; квадратичные комплексные — точные радикалы), регулярный случай рядом Ньютона, ветви с самопроверкой; группы Дюваля (puiseux-rational), ряд ветви как объект (algebraic-series) |
| `curves` (шаги A3.1–A3′.2) | `singular-points curve-genus curve-singular? parametrize-curve parametrization-check parametrize-curve-inverse parametrization-inverse-check` — особые точки плоской алгебраической кривой (аффинные и на бесконечности, сопряжённые группы с полем ℚ(α)), δ по ветвям Пюизё, род по формуле Нётера; приводимость → reducible; рациональная параметризация рода 0, её сертификат и обратное отображение для пучка |

| `algnum` (шаги A1.1–A1.3) | `alg-field alg-elt alg-field-minpoly alg-field-embed alg-add alg-sub alg-mul alg-div alg-inv alg-negate alg-pow alg-zero? alg-equal? alg-norm alg-minpoly alg->expr expr->alg alg-poly-div alg-poly-gcd alg-poly-sqfree alg-primitive alg-factor alg-factor-check factor-over` — поле ℚ(α) = ℚ[t]/(m): арифметика по модулю m, норма, минимальный многочлен, НОД/бесквадратность в ℚ(α)[x], примитивный элемент, факторизация нормой Трагера |
| `numtheory` (шаги NT.1–NT.4) | `powmod invmod egcd jacobi sqrtmod crt totient divisors order primitive-root prime? next-prime primes-up-to factor-integer pratt-certificate pratt-check solve-linear-diophantine pell pell-negative pell-solutions sum-of-two-squares pythagorean-triples` — теория чисел на целых числах с сертификатами: модулярная арифметика, Тонелли–Шенкс, КТО с несовместными модулями, φ и делители, порядок и первообразный корень, Миллер–Рабин (детерминированные базы до 3.3·10^24, выше — `probable-prime` в канале условий), решето, факторизация (пробное деление + ρ Полларда с сертификатом), сертификаты Пратта, линейное диофантово уравнение, Пелль (цепная дробь √D, положительный и отрицательный), сумма двух квадратов (Корнаккия), примитивные пифагоровы тройки |
| `gf` (шаг NT.3) | `gf-field gf-elt gf->int gf+ gf- gf* gf/ gf-inv gf-power gf-order gf-irreducible? gf-random-irreducible gf-primitive? gf-poly-gcd gf-factor` — конечные поля GF(pⁿ): элементы — списки коэффициентов, арифметика с сертификатами (`a·a⁻¹ = 1`, `r·b = a`), неприводимость по Рабину, разложение Кантора–Цассенхауса над GF(p) (бесквадратная часть через цепочку НОД), генератор `gf-random-irreducible` |
| `ode` (шаги ODE.0–ODE.3) | `dsolve dsolve-check ode-solution ode-solutions ode-status ode-subst ode-order ode-linear? ode-const-coeff? ode-autonomous?` — каркас ОДУ: струйная форма `(y x)`, классификатор, объект `ode-solution`, сертификат подстановкой (`simplify`/`together`, затем численно); квадратуры `y⁽ⁿ⁾ = f(x)`, первый порядок (разделяющиеся, линейные, Бернулли, однородные), линейные с постоянными коэффициентами (кратности, комплексные корни, вариация постоянных, вронскиан); неявные ответы и особые решения; вне методов — `unknown` |
| `field` (шаг FLD.1) | `field-Q field-algnum field-gf field-gfpn field-ratfun field-name field-char field-zero field-one field-add field-sub field-neg field-mul field-div field-inv field-zero? field-equal? field-from-rational field->expr field-pow fp-trim fp-add fp-sub fp-neg fp-mul fp-scale fp-deg fp-lc fp-monic fp-divmod fp-gcd fp-egcd fp-deriv fp-sqfree fp-eval fp-compose fp-equal? fp-divmod-check fp-gcd-check fp-egcd-check fp-sqfree-check fm-mul fm-mat-vec fm-identity fm-rref fm-rank fm-nullspace fm-det fm-solve fm-inverse fm-nullspace-check fm-solve-check fm-inverse-check` — алгоритмы один раз для любого поля (ℚ, ℚ(α), GF(p), GF(pⁿ), ℚ(x)): многочлены и матрицы над полем-записью, ответы с сертификатами |
| `forms` (шаг DF.1) | `make-form form form? form-vars form-degree form-terms form->expr form-zero? form-equal? form-add form-sub form-neg form-scale wedge form-d form-pullback form-interior form-hodge form-closed? form-exact? form-potential form-potential-check vf-grad vf-div vf-curl vf-laplacian vf-potential vf-potential-check vf-vector-potential vf-vector-potential-check make-chain chain? chain-phi chain-ranges integrate-form integrate-form-numeric chain-rect-boundary stokes-check vf-form1 vf-form2` — внешнее исчисление в ℝⁿ: формы, ∧, d, φ\*, ι, ∗, потенциал по Пуанкаре; векторный анализ через формы с сертификатами; интегралы форм по цепям, Грин/Стокс (шаги DF.1–DF.2) |
| `multiint` (шаг MINT.a) | `integrate-multi integrate-change jacobian-det line-integral arc-length surface-integral surface-area integrate-region region-swap green-check stokes-surface-check gauss-check` (MINT.b: области, смена порядка, проверки Грина / Стокса / Гаусса) — кратные интегралы одной записью, замена переменных с модулем якобиана (знак по пределам), интегралы первого рода (длина кривой, площадь поверхности) |
| `prob` (шаг PROB) | `bernoulli-dist binomial-dist poisson-dist geometric-dist uniform-discrete hypergeometric-dist uniform-dist normal-dist exponential-dist gamma-dist beta-dist chi2-dist student-dist f-dist table-dist density-dist dist? dist-support dist-pdf dist-cdf dist-prob dist-mean dist-variance dist-stddev dist-moment dist-expectation dist-mgf dist-quantile dist-mass dist-check sample-mean sample-variance sample-stddev sample-median quantile-sample sample-covariance sample-correlation linear-regression frequencies bayes-posterior total-probability` — вероятность и статистика: распределения как данные, pdf/cdf/моменты/mgf общим движком sum/integrate, выборка, Байес |
| `stats` (шаг PROB.b) | `dist-cdf-cert dist-cdf-num dist-sf-num dist-quantile-bounds dist-quantile-num quantile-dist mle mle-check mle-score moments-estimate confint-mean confint-mean-sigma confint-variance confint-proportion confint-wilson t-test t-test-two t-test-pooled t-test-paired chi2-gof chi2-independence f-test-variances stat-get` — математическая статистика: cdf нормального/Стьюдента/χ²/Фишера и квантили с заявленной точностью, оценки, интервалы, критерии |
| `diffgeom` (шаг DG) | `curve-speed curve-tangent curve-normal curve-binormal frenet-frame curvature torsion curvature-radius first-form second-form gauss-curvature mean-curvature principal-curvatures surface-normal graph-surface gauss-bonnet-check` — кривые (Френе, κ, τ) и поверхности (формы, K, H, главные кривизны), Гаусс–Бонне как сертификат; знак корней — только доказанный |
| `homology` (шаг HOM) | `smith-form smith-invariants smith-check simplicial-complex complex-from-simplices complex? complex-closed? complex-dimension complex-faces boundary-matrix homology homology-text betti euler-characteristic homology-check sphere-complex circle-complex disk-complex torus-complex projective-plane-complex klein-bottle-complex` — нормальная форма Смита над Z и гомологии симплициальных комплексов (H_k = Z^b + кручение), готовые триангуляции, сертификат ∂∂ = 0 и U·A·V = D |
| `fourier` (шаг FS) | `fourier-coefficients fourier-series fourier-sine-series fourier-cosine-series fourier-complex-coefficients fourier-value-at fourier-coefficients-check parseval-check` — ряды Фурье на отрезке: коэффициенты символьно по n (piecewise и abs по кускам), синус- и косинус-ряды, значение в разрыве (Дирихле), Парсеваль как сертификат |
| `complex-analysis` (шаг CA) | `residue laurent singularity-type singularities contour-integral residue-check contour-integral-check integral-by-residues` — ТФКП: вычеты (в том числе на ∞ и в существенной особенности), ряд Лорана, тип особой точки, интеграл по окружности, ∫R(x)dx по ℝ; сертификаты — численный круг |
| `solve` | `solve rational-number? real-numeric? x-free? root-of? numeric-poly? replace-expr` |
| `linalg` (шаги LA.1–LA.3) | `rref nullspace columnspace charpoly eigenvalues eigenvectors diagonalizable? diagonalize jordan-form jordan-blocks mat-exp mat-power mat-fn` — линейная алгебра: RREF, ядро, образ, характеристический многочлен, собственные значения/векторы, диагонализация, жорданова форма, экспонента, символьная степень, функции от матриц |
| `dp` (шаг DP.1) | `memoize defmemo knapsack knapsack-check lcs lcs-check edit-distance edit-distance-check coin-change coin-change-check coin-ways coin-ways-check shortest-paths shortest-paths-check` — динамическое программирование с сертификатами (уравнения Беллмана, потенциалы, отрицательный цикл) |
| `interval` (шаги CN.1–CN.3) | `iv? iv iv-lo iv-hi iv-width iv-mid iv-contains? iv-subset? iv+ iv- iv* iv/ iv-neg iv^ iv-sqrt iv-exp iv-log iv-sin iv-cos iv-atan iv-pi iv-e iv-eval iv-refine isolate-roots refine-root certified-roots certified-integral certified-sum` — интервальная арифметика на точных рациональных концах (ряды Тейлора с оценкой остатка, π по формуле Мэчина), изоляция корней Штурма, сертификация корней оператором Кравчика, гарантированные границы интегралов и сумм |
| `cfinite` (шаги RE.1–RE.3) | `cf? cfinite cf-coeffs cf-init cf-order cf-check cf-term cf-term-mod cf-terms cf-shift cf-from-terms cf+ cf* cf-scale cf-partial-sum cf-char-poly cf-of-expr cf-prove cf-check-proof cf->gf gf->cf cf-closed-form` — C-конечные последовательности: быстрое n-е значение (x^n mod χ), Берлекэмп–Мэсси, доказательство тождеств, производящие функции и замкнутая форма |
| `denest` (шаг A1.5–A1.6) | `sqrt-denest denest-check? alg-simplify alg-equal-expr? radical-roots` — денестинг радикалов глубины 2 (критерий BFHT) с сертификатом, нормальная форма выражений в ℚ(α), точные корни биквадратных уравнений |
| `integrate` (`integrate/*.lisp`) | `integrate int-check int-rule int-add-strategy int-num int-guard` |
| `risch` (`risch/*.lisp`, шаги 21k) | `risch-integrate risch-nonelementary? risch-special` |
| `summation` (`summation/*.lisp`, шаги 21l) | `sum-symbolic sum-strategies sum-add-strategy sum-guard sum-check sum-check-how sum-unevaluated sum-faulhaber sum-form` (core), `hyper-ratio hyper-termp poly-shift poly-int-roots poly-int-roots-param poly-dispersion hyper-lin hyper-frac-mul hyper-poly-mul` (hyper/gosper), `gosper-degree-bound` (gosper), `abramov-decompose abramov-sum` (abramov), `recurrence-check recurrence-order wz-prove-identity wz-certificate zeilberger zb-par-gosper zb-shift-ratio zb-shift-ratios zb-par-numer` (zeilberger), `rsolve rsolve-first-order rsolve-const-coeffs` (hyper-solve) |
| `series` | `series series? taylor series->expr series-coeff series-order` и `ser-bad? ser-lg ser-var ser-val ser-cs ser-compute ser-precision-err?` (для `limit`), `ser-with-logx` (для `gruntz`) |
| `gruntz` (шаг 21j.1) | `gruntz-limitinf gruntz-mrv gruntz-compare gruntz-sign gruntz-leadterm` — пределы exp-log-функций при x → +∞ по Грунцу (MRV) |
| `limit` | `limit lim-add` |
| `test` | `deftest register-test run-test run-tests assert-equal assert-true assert-error assert-error-fn` |
| `mathlang` (`mathlang/*.lisp`) | точки входа (`math-eval math-eval-tree load-math math-reset factorial m-capture-start m-capture-end`), времена выполнения сгенерированного кода и цели `m-aliases` (`m-gslow m-arith m-diff m-solve ...`) |
