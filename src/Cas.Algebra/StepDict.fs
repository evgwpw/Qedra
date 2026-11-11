// Шаг S.5: английский словарь шагов. Шаг записывается по-русски (title/comment), rule — стабильный английский
// идентификатор; здесь — таблица rule → перевод заголовка и пояснения на английский.
//
// Перевод — подстановка подстрок (ординальная, по порядку записи) отдельно для заголовка и для пояснения; формулы и
// подставленные выражения в пояснениях языконезависимы и остаются как есть, переводятся только русские фразы между ними.
// Сначала применяются пары правила (rule), затем общие пары (common: «или», «не существует»).
// Если после перевода в тексте остались кириллические буквы (фраза не покрыта словарём) или для rule нет записи — поле
// остаётся русским, а rule попадает в список «нет перевода» (warnings ответа и пометка в печати). Новый шаг в коде =
// новая запись здесь; тест StepDictTests сверяет словарь с rule, встречающимися в lib\*.lisp и Differentiate.fs.
module StepDict

open System
open System.Text.RegularExpressions

// Запись словаря: пары (русская фраза, английская) для заголовка и для пояснения
type Entry =
    { Title: (string * string) list
      Comment: (string * string) list }

let private e (title: (string * string) list) (comment: (string * string) list) : Entry = { Title = title; Comment = comment }
let private t (ru: string) (en: string) : (string * string) list = [ ru, en ]

// Общие пары для пояснений (после пар правила)
let private common : (string * string) list =
    [ " или ", " or "
      "не существует", "does not exist"
      "не определён", "undefined"
      // D2b: причины отказов стратегий (attempt-fail) — чтобы английские попытки не оставались русскими
      "условия табличной формулы не выполнены", "the conditions of the table formula are not met"
      "одно из слагаемых не интегрируется", "one of the terms cannot be integrated"
      "оставшийся множитель не интегрируется", "the remaining factor cannot be integrated"
      "не удалось проинтегрировать выражение через u", "could not integrate the expression in u"
      "интеграл неэлементарен: доказано алгоритмом Риша", "the integral is not elementary: proved by the Risch algorithm"
      "нет подходящего приёма интегрирования", "no suitable integration method"
      "интеграл v·du не берётся (по частям не сходится)", "the integral of v·du cannot be taken (integration by parts does not close)"
      "раскрытая сумма не интегрируется", "the expanded sum cannot be integrated"
      "знаменатель не разложен на линейные и квадратные множители", "the denominator is not factored into linear and quadratic factors"
      "слагаемое простейшей дроби не интегрируется", "a partial fraction term cannot be integrated"
      "ответ не прошёл проверку дифференцированием", "the answer failed the differentiation check"
      "степени sin и cos не сводятся к табличным", "powers of sin and cos do not reduce to table integrals"
      "корень не приводится к табличному (r = 0 или K < 0)", "the root does not reduce to a table integral (r = 0 or K < 0)"
      "преобразованная сумма не интегрируется", "the transformed sum cannot be integrated"
      "доказано: интеграл неэлементарен", "proved: the integral is not elementary"
      "Риш не решил: не знаю", "Risch did not decide: unknown"
      "пределы частей не определены (неопределённость)", "the limits of the parts are not determined (indeterminate form)"
      "предел производных не вычислен", "the limit of the derivatives was not computed"
      "алгоритм Грунца не определил предел", "the Gruntz algorithm did not determine the limit"
      "ведущий член ряда не даёт предела", "the leading series term does not give a limit"
      "предел не вычислен: приёмы каскада не дали значения", "the limit was not computed: no cascade method produced a value" ]

// Пояснения шагов AC-правил (Rules.acComment): «множитель c = z», «остальные слагаемые: 3 + y», «остаток r = …»;
// порядок: «множители » раньше «множитель » не нужен (разные окончания), «остальные слагаемые » — до общих
let private ruleComment : (string * string) list =
    [ "остальные слагаемые ", "remaining terms "
      "остальные слагаемые: ", "remaining terms: "
      "множители ", "factors "
      "множитель ", "factor "
      "остаток ", "remainder " ]

// R5.3b: фразы шага «Кантор» (порядок δ по модулю p, проверка по q и над ℚ, таблица kδ парами Мамфорда) —
// в alg-principal (главность/кручение) и alg-refusal (причина отказа «не кручение»)
let private cantorPairs : (string * string) list =
    [ "Кантор: ", "Cantor: "
      "; проверка по модулю q не проводилась (нет хороших q ≤ 200)", "; no check modulo q was made (no good q ≤ 200)"
      ") ⇒ δ не кручение (иначе ", ") ⇒ δ is not torsion (otherwise "
      "·δ = 0 над ℚ и по модулю q)", "·δ = 0 over ℚ and modulo q)"
      "·δ = 0 над ℚ)", "·δ = 0 over ℚ)"
      "; над ℚ проверка опущена (порядок велик)", "; the check over ℚ is omitted (the order is large)"
      "; над ℚ: ", "; over ℚ: "
      "·δ ≠ 0 ⇒ δ не кручение (иначе ", "·δ ≠ 0 ⇒ δ is not torsion (otherwise "
      "·δ = 0 ⇒ порядок δ равен ", "·δ = 0 ⇒ the order of δ is "
      "; обоснование: редукция по хорошему p > 2 инъективна на кручении J(ℚ), поэтому порядок кручения n = ord_p(δ)",
      "; justification: reduction modulo a good prime p > 2 is injective on the torsion of J(ℚ), so the torsion order is n = ord_p(δ)"
      "; найдена функция u с div u = ", "; a function u with div u = "
      "; функция u с div u = ", "; the function u with div u = "
      "·δ не найдена (расхождение с Кантором)", "·δ is not found (disagreement with Cantor)"
      "; kδ — пары Мамфорда (u, v): ", "; kδ as Mumford pairs (u, v): "
      "; kδ в модели w² = Q(z) — пары Мамфорда (u, v): ", "; kδ in the model w² = Q(z) as Mumford pairs (u, v): "
      "замена x = ", "substitution x = "
      "; точки δ перенесены: (x₀, y₀) ↦ (1/(x₀ − a), y₀/(x₀ − a)^(g+1)), (a, 0) ↦ ∞, ∞± ↦ (0, ±√lc);",
      "; the points of δ are transferred: (x₀, y₀) ↦ (1/(x₀ − a), y₀/(x₀ − a)^(g+1)), (a, 0) ↦ ∞, ∞± ↦ (0, ±√lc);"
      " порядок и главность δ сохраняются при бирациональном изоморфизме; ", " the order and principality of δ are preserved by a birational isomorphism; "
      " — по Трагеру ∫ неэлементарен", " — by Trager's theorem the integral is not elementary"
      // R5.3c2: Кантор над K = ℚ(√d) (расщеплённое p, √d ↦ s mod p)
      "; обоснование: p расщепляется в K, простой 𝔭 | p имеет степень 1 и поле вычетов 𝔽_p; редукция по 𝔭 (p > 2, неразветвлённо) инъективна на кручении J(K), поэтому порядок кручения n = ord_𝔭(δ)",
      "; justification: p splits in K, a prime 𝔭 | p has degree 1 and residue field 𝔽_p; reduction modulo 𝔭 (p > 2, unramified) is injective on the torsion of J(K), so the torsion order is n = ord_𝔭(δ)"
      "Кантор над ℚ(√", "Cantor over ℚ(√"
      ") ⇒ δ не кручение (порядок кручения делит B)", ") ⇒ δ is not torsion (the torsion order divides B)"
      "·δ = 0 над K и по модулю q)", "·δ = 0 over K and modulo q)"
      "·δ = 0 над K)", "·δ = 0 over K)"
      "; над K проверка опущена (порядок велик)", "; the check over K is omitted (the order is large)"
      "; над K: ", "; over K: "
      "; проверка по модулю q не проводилась (нет хороших q ≤ 300)", "; no check modulo q was made (no good q ≤ 300)"
      "): k·δ ≠ 0 по модулю 𝔭 при всех k ≤ ", "): k·δ ≠ 0 modulo 𝔭 for all k ≤ "
      "); кручение порядка ≤ ", "); torsion of order ≤ "
      " исключено, порядок не определён (граница кручения B неизвестна) — не знаю", " is excluded, the order is not determined (the torsion bound B is unknown) — unknown" ]

// R1-хвост: места над ℚ(α) степени ≥ 3 (placesnf.lisp): вычеты ρ ∈ ℚ(α), режимы B/C, Кантор по модулям p (α ≡ a), функция u над ℚ(α)
let private nfPairs : (string * string) list =
    [ "скручивание η = √c₀·y, c₀ = ", "twisting η = √c₀·y, c₀ = "
      ": кривая η² = Q, Q = ", ": the curve η² = Q, Q = "
      "места над ℚ(α), α — корень g = ", "places over ℚ(α), α is a root of g = "
      "): на кривой y² = ", "): on the curve y² = "
      " имеем y(α) = s = ", " we have y(α) = s = "
      "; вычет в месте (α, +s) равен ρ = ", "; the residue at the place (α, +s) is ρ = "
      "Tr ρ ≠ 0 — сопряжённые вычеты ℚ-независимы, дивизор E = [(α, s) − (α, −s)] над ℚ(α)",
      "Tr ρ ≠ 0 — the conjugate residues are ℚ-independent, the divisor E = [(α, s) − (α, −s)] over ℚ(α)"
      "Tr ρ = 0 — единственное соотношение между сопряжёнными вычетами, дивизоры E_a − E_b",
      "Tr ρ = 0 — the only relation between the conjugate residues, the divisors E_a − E_b"
      "Кантор по модулю p, ", "Cantor modulo p, "
      "корень α ≡ a (простой 𝔓 | p), порядок ord(E mod 𝔓): ", "root α ≡ a (prime 𝔓 | p), order ord(E mod 𝔓): "
      "корни α ≡ a, b согласованы (G = S₃), порядок ord((E_a − E_b) mod 𝔓): ", "roots α ≡ a, b are consistent (G = S₃), order ord((E_a − E_b) mod 𝔓): "
      "; все порядки равны n = ", "; all orders equal n = "
      " — кандидат в кручение порядка n (обоснование: образ кручения порядка n в J(𝔽_p) имеет порядок ровно n; p > 2, 𝔓 | p неразветвлено)",
      " — a torsion candidate of order n (justification: the image of torsion of order n in J(𝔽_p) has order exactly n; p > 2, 𝔓 | p unramified)"
      "; порядки различны ⇒ дивизор не кручение (иначе все порядки равны n)", "; the orders differ ⇒ the divisor is not torsion (otherwise all orders equal n)"
      "; функция u над замыканием поля не строится — не знаю", "; the function u over the splitting field is not constructed — unknown"
      "найдена функция u(t) = (a(x) + b(x)·y)/(x − t)^", "found the function u(t) = (a(x) + b(x)·y)/(x − t)^"
      " (a, b ∈ ℚ(α)[x]) с div u = ", " (a, b ∈ ℚ(α)[x]) with div u = "
      "·E; точная проверка H = Σ (ρ/n)·u′/u в K[y]/(y² − P(x₀)) в рациональных точках: совпадает",
      "·E; exact check of H = Σ (ρ/n)·u′/u in K[y]/(y² − P(x₀)) at rational points: it agrees"
      "вычеты над ℚ(α), g — кубика: порядки образов дивизора в J(𝔽_p) различны (p = ",
      "residues over ℚ(α), g is a cubic: the orders of the divisor images in J(𝔽_p) differ (p = "
      " и p = ", " and p = "
      ") — не кручение, интеграл неэлементарен", ") — not torsion, the integral is not elementary"
      "дивизор вычетов над ℚ(α) — кручение (n = ", "the residue divisor over ℚ(α) is torsion (n = "
      "), но остаток H − Σ (ρ/n)·u′/u — ненулевой дифференциал 1-го рода — первообразной нет",
      "), but the remainder H − Σ (ρ/n)·u′/u is a nonzero differential of the first kind — there is no antiderivative" ]

let private ec (title: (string * string) list) (comment: (string * string) list) : Entry = e title (comment @ cantorPairs @ nfPairs)

// Словарь: rule → запись. Ключи с «*» на конце — шаблоны для семейств (simplify:rule:имя и т. п.)
let private table : (string * Entry) list =
    [
      // --- Базисы Грёбнера и системы (S.1) ---
      "groebner-basis", e (t "Базис Грёбнера" "Groebner basis")
                          [ "алгоритм Бухбергера, порядок ", "Buchberger's algorithm, order "
                            ", переменные ", ", variables "
                            "; элементов базиса: ", "; basis elements: " ]
      "normal-form", e (t "Нормальная форма" "Normal form")
                       (t "остаток от деления на приведённый базис Грёбнера" "remainder of division by the reduced Groebner basis")
      "fglm", e (t "Смена порядка мономов (FGLM)" "Change of monomial order (FGLM)")
                [ "перевод базиса нульмерного идеала из порядка ", "conversion of a zero-dimensional ideal basis from order "
                  " в ", " to "
                  " (размерность факторкольца ", " (quotient ring dimension " ]
      "elimination", e (t "Исключение переменных" "Variable elimination")
                       (t "базис Грёбнера в блочном порядке, исключаются " "Groebner basis in a block order; eliminated: ")
      "polynomial-system", e (t "Нелинейная система: метод базисов Грёбнера" "Nonlinear system: Groebner basis method")
                             (t "система многочленов приводится к треугольному виду, затем решается обратной подстановкой"
                                "the polynomial system is brought to triangular form and then solved by back substitution")
      "triangular-system", e (t "Приведение к треугольному виду (lex-базис Грёбнера)" "Reduction to triangular form (lex Groebner basis)")
                             (t "лексикографический базис Грёбнера: последний многочлен — от одной переменной"
                                "lexicographic Groebner basis: the last polynomial has a single variable")
      "parametric-basis", e (t "Базис Грёбнера с параметрами" "Groebner basis with parameters")
                            (t "параметры рассматриваются как переменные младшего блока: базис над ℚ(параметры), если старшие коэффициенты ненулевые"
                               "parameters are treated as variables of the lowest block: a basis over ℚ(parameters) if the leading coefficients are nonzero")
      "generic-parameters", e (t "Ответ для общих значений параметров" "Answer for generic parameter values")
                              [ "решения верны при общих значениях параметров ", "the solutions hold for generic parameter values "
                                "; при обращении в нуль старших коэффициентов и знаменателей (условия ниже) система может вести себя иначе",
                                "; if leading coefficients or denominators vanish (conditions below), the system may behave differently" ]

      // --- diff (S.2) ---
      "differentiation", e (t "Дифференцирование по " "Differentiation with respect to ") []
      "simplify-result", e (t "Упрощение результата" "Simplifying the result") []
      "diff-sum", e [ "Производная суммы", "Derivative of a sum"; "Производная разности", "Derivative of a difference" ] []
      "diff-constant-multiple", e (t "Вынесение постоянного множителя" "Taking out a constant factor") []
      "diff-product", e (t "Правило произведения" "Product rule") []
      "diff-quotient", e (t "Правило частного" "Quotient rule") []
      "diff-power", e (t "Производная степенной функции" "Derivative of a power function") []
      "diff-power-general", e (t "Производная показательно-степенной функции" "Derivative of a general power u^v") []
      "diff-exp", e [ "Производная показательной функции", "Derivative of an exponential function"
                      "Производная экспоненты", "Derivative of the exponential" ] []
      "diff-log", e (t "Производная логарифма" "Derivative of a logarithm") []
      "diff-sqrt", e (t "Производная квадратного корня" "Derivative of a square root") []
      "diff-abs", e (t "Производная модуля" "Derivative of the absolute value") []
      "diff-special", e (t "Производная специальной функции" "Derivative of a special function") []
      "diff-trig", e (t "Производная тригонометрической функции" "Derivative of a trigonometric function") []
      "diff-hyperbolic", e (t "Производная гиперболической функции" "Derivative of a hyperbolic function") []
      "diff-inverse-trig", e (t "Производная обратной тригонометрической функции" "Derivative of an inverse trigonometric function") []
      "diff-inverse-hyperbolic", e (t "Производная обратной гиперболической функции" "Derivative of an inverse hyperbolic function") []
      "diff-chain", e (t "Цепное правило (сложная функция)" "Chain rule (composite function)") []
      "diff-variable", e (t "Производная переменной" "Derivative of the variable") []
      "diff-constant", e (t "Производная постоянной" "Derivative of a constant") []

      // --- simplify (S.2) ---
      "simplification", e (t "Упрощение" "Simplification") []
      "simplify:collect-terms", e (t "приведение подобных" "collecting like terms") []
      "simplify:merge-powers", e (t "объединение степеней" "merging powers") []
      "simplify:exact-value", e (t "точное значение функции" "exact value of the function") []
      "simplify:exact-root", e (t "точное значение корня" "exact value of the root") []
      "simplify:extract-root", e (t "вынесение множителя из-под корня" "extracting a factor from under the root") []
      "simplify:exp-merge", e (t "произведение экспонент" "product of exponentials") []
      "simplify:exp-power", e (t "степень экспоненты" "power of an exponential") []
      "simplify:power-of-product", e (t "степень произведения" "power of a product") []
      "simplify:power-of-power", e (t "степень степени" "power of a power") []
      "simplify:imaginary-power", e (t "степень мнимой единицы" "power of the imaginary unit") []
      "simplify:distribute-minus", e (t "раскрытие минуса" "distributing the minus sign") []
      "simplify:pythagorean", e (t "основное тригонометрическое тождество" "Pythagorean trigonometric identity") []
      "simplify:trig-rules", e (t "тригонометрическое тождество" "trigonometric identity") []
      "simplify:sqrt-rational", e (t "корень из рационального числа" "square root of a rational number") []
      "simplify:sqrt-negative", e (t "корень из отрицательного числа" "square root of a negative number") []
      "simplify:ln-to-log", e (t "ln как log" "ln as log") []
      "simplify:rule:*", e (t "правило " "rule ") ruleComment
      // заголовки правил lib\rules.lisp (:title у defrule); пояснение — привязки AC-правил (Rules.acComment)
      "simplify:rule:abs-nonnegative", e (t "Модуль неотрицательного числа" "Absolute value of a nonnegative number") ruleComment
      "simplify:rule:abs-nonpositive", e (t "Модуль неположительного числа" "Absolute value of a nonpositive number") ruleComment
      "simplify:rule:abs-abs", e (t "Модуль модуля" "Absolute value of an absolute value") ruleComment
      "simplify:rule:abs-square", e (t "Модуль квадрата вещественного числа" "Absolute value of a real square") ruleComment
      "simplify:rule:sqrt-square-nonnegative", e (t "Корень из квадрата неотрицательного числа" "Square root of the square of a nonnegative number") ruleComment
      "simplify:rule:sqrt-square-real", e (t "Корень из квадрата вещественного числа" "Square root of the square of a real number") ruleComment
      "simplify:rule:pow-half-square-nonnegative", e (t "Степень 1/2 от квадрата неотрицательного числа" "Power 1/2 of the square of a nonnegative number") ruleComment
      "simplify:rule:pow-half-square-real", e (t "Степень 1/2 от квадрата вещественного числа" "Power 1/2 of the square of a real number") ruleComment
      "simplify:rule:pow-pow", e (t "Степень степени (x ≥ 0)" "Power of a power (x ≥ 0)") ruleComment
      "simplify:rule:pow-product", e (t "Степень произведения неотрицательных множителей" "Power of a product of nonnegative factors") ruleComment
      "simplify:rule:log-exp", e (t "Логарифм экспоненты" "Logarithm of an exponential") ruleComment
      "simplify:rule:log-pow-positive", e (t "Логарифм степени положительного числа" "Logarithm of a power of a positive number") ruleComment
      "simplify:rule:log-pow-negative-even", e (t "Логарифм чётной степени отрицательного числа" "Logarithm of an even power of a negative number") ruleComment
      "simplify:rule:log-pow-negative-twok", e (t "Логарифм степени 2k отрицательного числа (k целое)" "Logarithm of the power 2k of a negative number (k integer)") ruleComment
      "simplify:rule:log-product-positive", e (t "Логарифм произведения с положительным множителем" "Logarithm of a product with a positive factor") ruleComment
      "simplify:rule:sqrt-product-nonnegative", e (t "Корень произведения с неотрицательным множителем" "Square root of a product with a nonnegative factor") ruleComment
      "simplify:rule:exp-log", e (t "Экспонента логарифма" "Exponential of a logarithm") ruleComment
      "simplify:rule:sin-integer-pi", e (t "Синус целого кратного π" "Sine of an integer multiple of π") ruleComment
      "simplify:rule:cos-even-multiple-pi", e (t "Косинус чётного кратного π" "Cosine of an even multiple of π") ruleComment
      "simplify:rule:cos-integer-pi", e (t "Косинус целого кратного π" "Cosine of an integer multiple of π") ruleComment
      "simplify:rule:pythagorean-common-factor", e (t "Основное тригонометрическое тождество (общий множитель)"
                                                      "Pythagorean trigonometric identity (common factor)") ruleComment
      // Шаг PL: полилогарифм и функция Ламберта
      "simplify:rule:polylog-zero", e (t "Значение Li_s в нуле" "Value of Li_s at zero") ruleComment
      "simplify:rule:polylog-order-one", e (t "Li₁(x) = −log(1−x)" "Li₁(x) = −log(1−x)") ruleComment
      "simplify:rule:polylog-order-zero", e (t "Li₀(x) = x/(1−x)" "Li₀(x) = x/(1−x)") ruleComment
      "simplify:rule:polylog-order-minus-one", e (t "Li₋₁(x) = x/(1−x)²" "Li₋₁(x) = x/(1−x)²") ruleComment
      "simplify:rule:polylog-order-minus-two", e (t "Li₋₂(x) = x(1+x)/(1−x)³" "Li₋₂(x) = x(1+x)/(1−x)³") ruleComment
      "simplify:rule:polylog-2-one", e (t "Li₂(1) = π²/6" "Li₂(1) = π²/6") ruleComment
      "simplify:rule:polylog-4-one", e (t "Li₄(1) = π⁴/90" "Li₄(1) = π⁴/90") ruleComment
      "simplify:rule:polylog-6-one", e (t "Li₆(1) = π⁶/945" "Li₆(1) = π⁶/945") ruleComment
      "simplify:rule:polylog-2-minus-one", e (t "Li₂(−1) = −π²/12" "Li₂(−1) = −π²/12") ruleComment
      "simplify:rule:polylog-4-minus-one", e (t "Li₄(−1) = −7π⁴/720" "Li₄(−1) = −7π⁴/720") ruleComment
      "simplify:rule:polylog-6-minus-one", e (t "Li₆(−1) = −31π⁶/30240" "Li₆(−1) = −31π⁶/30240") ruleComment
      "simplify:rule:polylog-2-half", e (t "Li₂(1/2) = π²/12 − log²2/2" "Li₂(1/2) = π²/12 − log²2/2") ruleComment
      "simplify:rule:polylog-deriv", e (t "Производная полилогарифма: Li_s′ = Li_{s−1}/x" "Derivative of the polylogarithm: Li_s′ = Li_{s−1}/x") ruleComment
      "simplify:rule:polylog-deriv-one", e (t "Производная Li₁: 1/(1−x)" "Derivative of Li₁: 1/(1−x)") ruleComment
      "simplify:rule:lambert-zero", e (t "W(0) = 0" "W(0) = 0") ruleComment
      "simplify:rule:lambert-e", e (t "W(e) = 1" "W(e) = 1") ruleComment
      "simplify:rule:lambert-minus-inverse-e", e (t "W(−1/e) = −1" "W(−1/e) = −1") ruleComment
      "simplify:rule:lambert-inverse", e (t "W(x·eˣ) = x при x ≥ −1" "W(x·eˣ) = x for x ≥ −1") ruleComment
      "simplify:rule:lambert-times-exp", e (t "W(x)·e^W(x) = x" "W(x)·e^W(x) = x") ruleComment
      "simplify:rule:lambert-deriv", e (t "Производная функции Ламберта: W′ = W/(x(1+W))" "Derivative of the Lambert function: W′ = W/(x(1+W))") ruleComment
      "simplify:rule:lambert-deriv-var", e (t "Производная функции Ламберта: W′ = W/(x(1+W))" "Derivative of the Lambert function: W′ = W/(x(1+W))") ruleComment
      // Шаг SF: специальные функции — значения в нуле и нечётность
      "simplify:rule:erf-zero", e (t "Значение erf в нуле" "Value of erf at zero") ruleComment
      "simplify:rule:erfi-zero", e (t "Значение erfi в нуле" "Value of erfi at zero") ruleComment
      "simplify:rule:si-zero", e (t "Значение Si в нуле" "Value of Si at zero") ruleComment
      "simplify:rule:shi-zero", e (t "Значение Shi в нуле" "Value of Shi at zero") ruleComment
      "simplify:rule:erfc-zero", e (t "Значение erfc в нуле" "Value of erfc at zero") ruleComment
      "simplify:rule:erf-odd", e (t "Нечётность erf" "Oddness of erf") ruleComment
      "simplify:rule:erfi-odd", e (t "Нечётность erfi" "Oddness of erfi") ruleComment
      "simplify:rule:si-odd", e (t "Нечётность Si" "Oddness of Si") ruleComment
      "simplify:rule:shi-odd", e (t "Нечётность Shi" "Oddness of Shi") ruleComment
      "simplify:rule:erf-odd-number", e (t "Нечётность erf (отрицательное число)" "Oddness of erf (negative number)") ruleComment
      "simplify:rule:erfi-odd-number", e (t "Нечётность erfi (отрицательное число)" "Oddness of erfi (negative number)") ruleComment
      "simplify:rule:si-odd-number", e (t "Нечётность Si (отрицательное число)" "Oddness of Si (negative number)") ruleComment
      "simplify:rule:shi-odd-number", e (t "Нечётность Shi (отрицательное число)" "Oddness of Shi (negative number)") ruleComment
      // Шаг 21l.0: комбинаторные головы
      "simplify:combinatorial-value", e (t "значение комбинаторной функции" "value of a combinatorial function") ruleComment
      "simplify:rule:gamma-factorial", e (t "Γ(n+1) = n! для целых n" "Γ(n+1) = n! for integer n") ruleComment
      "simplify:rule:gamma-recurrence", e (t "Функциональное уравнение Γ(z+1) = z·Γ(z)" "Functional equation Γ(z+1) = z·Γ(z)") ruleComment
      "simplify:rule:factorial-gamma", e (t "Факториал через гамма-функцию" "Factorial via the gamma function") ruleComment
      "simplify:rule:binomial-zero-k", e (t "C(n, 0) = 1" "C(n, 0) = 1") ruleComment
      "simplify:rule:binomial-n-k", e (t "C(n, n) = 1" "C(n, n) = 1") ruleComment
      "simplify:rule:binomial-one-k", e (t "C(n, 1) = n" "C(n, 1) = n") ruleComment
      "simplify:rule:rf-one", e (t "(x)_1 = x" "(x)_1 = x") ruleComment
      "simplify:rule:ff-one", e (t "(x)‾1 = x" "(x)‾1 = x") ruleComment
      "simplify:rule:rf-zero", e (t "(x)_0 = 1" "(x)_0 = 1") ruleComment
      "simplify:rule:ff-zero", e (t "(x)‾0 = 1" "(x)‾0 = 1") ruleComment
      "simplify:rule:psi-half", e (t "ψ(1/2) = −γ − 2·ln 2" "ψ(1/2) = −γ − 2·ln 2") ruleComment
      "simplify:method:*", e (t "метод " "method ") []
      "simplify:*", e (t "упрощение: " "simplification: ") []

      // --- integrate (S.3, S.4) ---
      "rubi-step", e (t "Правило Rubi" "Rubi rule") []
      "rubi", e (t "Правила Rubi" "Rubi rules")
                (t "запасная стратегия: поиск правила интегрирования по таблице Rubi, ответ проверен дифференцированием"
                   "fallback strategy: searching the Rubi integration rule table, the answer is checked by differentiation")
      "integration", e (t "Интегрирование по " "Integration with respect to ") []
      "simplify-integrand", e (t "Упрощение подынтегральной функции" "Simplifying the integrand") []
      "int-table", e [ "Табличный интеграл", "Table integral"; "Интеграл постоянной", "Integral of a constant" ]
                      [ "; здесь u = ", "; here u = "
                        ", поэтому результат делится на ", ", so the result is divided by " ]
      "int-linearity", e [ "Интеграл суммы: интегрируем почленно", "Integral of a sum: integrate term by term"
                           "Вынесение постоянного множителя", "Taking out a constant factor" ]
                         (t ", где c = " ", where c = ")
      "int-substitution", e (t "Метод подстановки" "Substitution method") []
      "int-substitution-change", e (t "Замена переменной" "Change of variable")
                                   (t "подынтегральное выражение через u: " "the integrand in terms of u: ")
      "int-back-substitution", e (t "Обратная замена" "Back substitution") []
      "int-by-parts", e [ "Интегрирование по частям (циклический случай)", "Integration by parts (cyclic case)"
                          "Интегрирование по частям", "Integration by parts" ]
                        [ "по частям дважды: исходный интеграл возвращается с множителем c, получаем уравнение",
                          "by parts twice: the original integral returns with the factor c, which gives an equation"
                          "; u выбирается по правилу LIATE (логарифм, обратная тригонометрия, алгебраическая, тригонометрия, показательная)",
                          "; u is chosen by the LIATE rule (logarithm, inverse trigonometric, algebraic, trigonometric, exponential)" ]
      "int-parts-choice", e (t "Выбор u и dv" "Choice of u and dv")
                            [ "по правилу LIATE; du = ", "by the LIATE rule; du = "
                              " (вложенный шаг ниже)", " (nested step below)" ]
      "int-parts-formula", e (t "Формула интегрирования по частям" "Integration by parts formula")
                             (t "; здесь u = " "; here u = ")
      "int-parts-cycle", e (t "Циклический случай: решаем уравнение относительно интеграла" "Cyclic case: solving the equation for the integral")
                           (t "после двух шагов " "after two steps ")
      "int-trig-powers", e (t "Степени синуса и косинуса" "Powers of sine and cosine")
                           [ "формула понижения степени: ", "reduction formula: "
                             "нечётная степень синуса: ", "odd power of sine: "
                             "нечётная степень косинуса: ", "odd power of cosine: "
                             "обе степени чётные: понижаем степень, ", "both powers are even: reducing the power, "
                             "чётная степень при отрицательной другой: sin² = 1 − cos² (или cos² = 1 − sin²) сводит к степеням одной функции",
                             "an even power with a negative other one: sin² = 1 − cos² (or cos² = 1 − sin²) reduces to powers of one function"
                             "подстановка ", "substitution "
                             "; аргумент линейный: u = ", "; the argument is linear: u = " ]
      "int-trig-product", e (t "Произведение синусов и косинусов" "Product of sines and cosines") []
      "risch-precheck", e (t "Предпроверка Риша: элементарна ли первообразная" "Risch pre-check: is the antiderivative elementary")
                         [ "не уложилась в бюджет времени ", "did not fit into the time budget of " ]
      "int-tan-pow", e (t "Дробная степень tan x" "Fractional power of tan x")
                      (t "подстановка t = tan x, dx = dt/(1 + t²), затем u = t^(1/"
                         "substitution t = tan x, dx = dt/(1 + t²), then u = t^(1/")
      "int-polylog", e (t "Интеграл через полилогарифм или функцию Ламберта" "Integral via the polylogarithm or the Lambert W function")
                      (t "подстановка u = k·xⁿ, dx/x = du/(n·u): " "substitution u = k·xⁿ, dx/x = du/(n·u): ")
      "int-product-to-sum", e (t "Преобразование произведения в сумму" "Converting a product to a sum") []
      "int-sqrt-quad", e (t "Интеграл с корнем из квадратного трёхчлена" "Integral with the square root of a quadratic")
                         [ "выделяем полный квадрат Q = a·U² + r; ", "complete the square Q = a·U² + r; "
                           " при a > 0, ", " for a > 0, "
                           " при a < 0 (K = r/|a|); ", " for a < 0 (K = r/|a|); "
                           " и ∫ (B·x + C)/√Q dx сводятся к ней", " and ∫ (B·x + C)/√Q dx reduce to it" ]
      "int-expand", e (t "Раскрытие скобок в подынтегральной функции" "Expanding brackets in the integrand")
                     (t "раскрываем скобки и интегрируем получившуюся сумму" "expand the brackets and integrate the resulting sum")
      "int-expand-brackets", e (t "Раскрытие скобок" "Expanding brackets") []
      "int-partial-fractions", e (t "Разложение на простые дроби" "Partial fraction decomposition")
                                 (t "раскладываем дробь на простейшие и интегрируем каждое слагаемое отдельно"
                                    "decompose the fraction into partial fractions and integrate each term separately")
      "apart", e (t "Разложение на простейшие дроби" "Partial fraction expansion") []
      "int-partial-fraction-term", e (t "Интеграл слагаемого" "Integral of the term")
                                     [ " почленно", " term by term"
                                       "многочлен: ", "polynomial: "
                                       "знаменатель линейный: ", "the denominator is linear: "
                                       ", здесь a·x + b = ", ", here a·x + b = "
                                       "знаменатель — степень линейного: ", "the denominator is a power of a linear: "
                                       "знаменатель — неприводимый квадратный трёхчлен ", "the denominator is an irreducible quadratic "
                                       ": выделяем полный квадрат, ", ": completing the square, "
                                       "; степень k = ", "; power k = "
                                       " — рекуррентная формула понижения", " — reduction recurrence formula" ]
      "int-rational-function", e (t "Рациональная функция: метод Эрмита и Лазара–Риобу–Трагера" "Rational function: Hermite and Lazard–Rioboo–Trager methods")
                                 (t "рациональная часть выделяется редукцией Эрмита, остаток интегрируется как сумма логарифмов (ЛРТ)"
                                    "the rational part is extracted by Hermite reduction, the remainder is integrated as a sum of logarithms (LRT)")
      "int-rational-hermite", e (t "Метод Эрмита: рациональная часть" "Hermite method: rational part")
                                [ "редукция Эрмита: ", "Hermite reduction: "
                                  ", у D нет кратных множителей; A/B — рациональная часть ответа", ", D has no repeated factors; A/B is the rational part of the answer" ]
      "int-rational-lrt", e (t "Метод Лазара–Риобу–Трагера: логарифмическая часть" "Lazard–Rioboo–Trager method: logarithmic part")
                           [ "метод Лазара–Риобу–Трагера: логарифмическая часть — сумма t·log S(t, x) по корням t резольвенты",
                             "Lazard–Rioboo–Trager method: the logarithmic part is the sum of t·log S(t, x) over the roots t of the resultant"
                             "; корни не выражаются в радикалах — остаётся сумма по корням rootsum",
                             "; the roots are not expressible in radicals, so a sum over the roots (rootsum) remains" ]
      "int-definite", e (t "Определённый интеграл" "Definite integral")
                        (t ", где F — первообразная f" ", where F is an antiderivative of f")
      "int-scan", e (t "Особые точки внутри отрезка" "Singular points inside the interval")
                    (t "нули знаменателя, ветви log и степеней; интегрируемые — разбиение отрезка"
                       "zeros of the denominator, branches of log and powers; integrable ones — splitting the interval")
      "int-limits", e (t "Подстановка пределов: F(b) − F(a)" "Substituting the limits: F(b) − F(a)")
                      (t "формула Ньютона–Лейбница: " "Newton–Leibniz formula: ")
      "int-improper", e (t "Несобственный интеграл: пределы первообразной" "Improper integral: limits of the antiderivative")
                        (t " при x → b − lim F(x) при x → a (с односторонними пределами у особых точек)"
                           " as x → b − lim F(x) as x → a (with one-sided limits at singular points)")

      // --- алгоритм Риша (21k.4) ---
      "risch", e (t "Алгоритм Риша" "Risch algorithm")
                 (t "подынтегральная функция переписывается в башне exp-log, затем редукция Эрмита, логарифмическая и многочленная части"
                    "the integrand is rewritten in an exp-log tower, then Hermite reduction, the logarithmic part and the polynomial part")
      "risch-tower", e (t "Алгоритм Риша: башня exp-log" "Risch algorithm: exp-log tower") []
      "risch-hermite", e (t "Алгоритм Риша: редукция Эрмита" "Risch algorithm: Hermite reduction")
                         (t "∫ f = g + ∫ h + ∫ r: g — рациональная часть, у h знаменатель без кратных множителей, r — многочлен по θ"
                            "∫ f = g + ∫ h + ∫ r: g is the rational part, h has a squarefree denominator, r is a polynomial in θ")
      "risch-lrt", e (t "Алгоритм Риша: логарифмическая часть (резольвента)" "Risch algorithm: logarithmic part (resolvent)") []
      "risch-check", e (t "Алгоритм Риша: проверка первообразной" "Risch algorithm: antiderivative check") []
      "risch-poly", e (t "Алгоритм Риша: многочленная часть" "Risch algorithm: polynomial part") []
      "risch-prde", e (t "Алгоритм Риша: параметрическое уравнение" "Risch algorithm: parametric Risch equation") []
      "risch-tan", e (t "Алгоритм Риша: тангенс-уровень" "Risch algorithm: tangent level") []
      "kovacic-normal", e (t "Ковачич: нормальная форма" "Kovacic: normal form") []
      "kovacic-poles", e (t "Ковачич: полюса r и порядок на ∞" "Kovacic: poles of r and order at infinity") []
      "kovacic-cases", e (t "Ковачич: какие случаи возможны" "Kovacic: which cases are possible") []
      "kovacic-case1", e (t "Ковачич: случай 1" "Kovacic: case 1") []
      "kovacic-case2", e (t "Ковачич: случай 2" "Kovacic: case 2") []
      "kovacic-case3", e (t "Ковачич: случай 3" "Kovacic: case 3") []
      "kovacic-solution", e (t "Ковачич: решение" "Kovacic: solution") []
      "kovacic-none", e (t "Ковачич: лиувиллевых решений нет" "Kovacic: no Liouvillian solutions") []
      "risch-log-part", e (t "Алгоритм Риша: логарифмическая и многочленная части" "Risch algorithm: logarithmic and polynomial parts")
                           [ "вычеты постоянны (метод Лазара–Риобу–Трагера), многочлен по θ интегрируется сверху вниз",
                             "the residues are constant (Lazard–Rioboo–Trager method), the polynomial in θ is integrated from the top degree down"
                             "найден неконстантный вычет или нет подходящего q + c·log u: остаток неэлементарен",
                             "a non-constant residue was found or there is no suitable q + c·log u: the remainder is not elementary" ]
      "risch-nonelementary", e [ "Алгоритм Риша: интеграл неэлементарен", "Risch algorithm: the integral is not elementary"
                                 "Алгоритм Риша: остаток неэлементарен", "Risch algorithm: the remainder is not elementary" ]
                                (t "интеграл неэлементарен: алгоритм Риша (теорема Лиувилля) доказал, что первообразной в элементарных функциях нет"
                                   "the integral is not elementary: the Risch algorithm (Liouville's theorem) proved that there is no antiderivative in elementary functions")
      // --- алгоритм Риша, exp-случай (21k.5) ---
      "risch-rde", e (t "Алгоритм Риша: уравнение Риша" "Risch algorithm: Risch differential equation")
                     [ "Dy + i·Dη·y = aᵢ: найдено решение y в поле ниже, ∫ aᵢθⁱ = y·θⁱ",
                       "Dy + i·Dη·y = aᵢ: a solution y was found in the field below, ∫ aᵢθⁱ = y·θⁱ"
                       "Dy + i·Dη·y = aᵢ: решения в поле ниже нет — слагаемое неэлементарно",
                       "Dy + i·Dη·y = aᵢ: there is no solution in the field below, so the term is not elementary"
                       "Dy + i·Dη·y = aᵢ: решения нет; частичное решение y: aᵢ = Dy + i·Dη·y + r, ∫ aᵢθⁱ = y·θⁱ + ∫ r·θⁱ, остаток неэлементарен",
                       "Dy + i·Dη·y = aᵢ: there is no solution; partial solution y: aᵢ = Dy + i·Dη·y + r, ∫ aᵢθⁱ = y·θⁱ + ∫ r·θⁱ, the remainder is not elementary"
                       "Dy + i·Dη·y = aᵢ: уравнение не решено", "Dy + i·Dη·y = aᵢ: the equation was not solved" ]
      "risch-exp-part", e (t "Алгоритм Риша: экспоненциальная часть" "Risch algorithm: exponential part")
                          [ "вычеты постоянны, для каждого aᵢθⁱ решено уравнение Риша, a₀ проинтегрировано уровнем ниже",
                            "the residues are constant, the Risch equation is solved for every aᵢθⁱ, a₀ is integrated one level down"
                            "для каждого aᵢθⁱ решено уравнение Риша, a₀ проинтегрировано уровнем ниже",
                            "the Risch equation is solved for every aᵢθⁱ, a₀ is integrated one level down"
                            "неконстантный вычет или уравнение Риша без решения: остаток неэлементарен",
                            "a non-constant residue or a Risch equation without a solution: the remainder is not elementary"
                            "уравнение Риша без решения: остаток неэлементарен",
                            "a Risch equation without a solution: the remainder is not elementary" ]
      // --- алгоритм Риша, ограниченное интегрирование (21k.7a) ---
      "risch-limited", e [ "Алгоритм Риша: ограниченное интегрирование", "Risch algorithm: limited integration"
                           "Алгоритм Риша: система над константами", "Risch algorithm: linear system over the constants" ]
                         [ "старший коэффициент aₘ = Dv + c·Dθ: найдены v в поле ниже и константа c",
                           "the leading coefficient aₘ = Dv + c·Dθ: v in the field below and a constant c were found"
                           "aₘ ≠ Dv + c·Dθ ни при каких v и c — многочлен по θ неэлементарен",
                           "aₘ ≠ Dv + c·Dθ for any v and c, so the polynomial in θ is not elementary"
                           "aₘ = Dv + c·Dθ: задача не решена", "aₘ = Dv + c·Dθ: the problem was not solved"
                           "проверка подстановкой не прошла: частное решение", "the substitution check failed: particular solution"
                           "проверка подстановкой не прошла: базисный вектор", "the substitution check failed: basis vector" ]

      // --- алгебраический Риш, род 0, смешанный и параметрический пути интегрирования (ключевые шаги, brief) ---
      "alg-integration", e (t "Алгебраическое интегрирование: редукция Эрмита и метод Трагера"
                              "Algebraic integration: Hermite reduction and Trager's method") []
      "alg-curve", e (t "Кривая подынтегрального выражения" "Curve of the integrand")
                     [ "радикал заменён на y: кривая y^", "the radical is replaced by y: curve y^"
                       "; род кривой g = ", "; genus of the curve g = "
                       "y = √a + √b заменяет оба радикала: кривая F(x, y) = 0, F = (y² − a − b)² − 4ab",
                       "y = √a + √b replaces both radicals: the curve F(x, y) = 0, F = (y² − a − b)² − 4ab" ]
      "alg-hermite", e (t "Редукция Эрмита" "Hermite reduction")
                       [ "∫A = G, остаток H = 0: у подынтегральной функции только алгебраическая часть",
                         "∫A = G, the remainder H = 0: the integrand has only an algebraic part"
                         "∫A = G + ∫H: G — алгебраическая часть, у остатка H знаменатель без кратных множителей",
                         "∫A = G + ∫H: G is the algebraic part, the remainder H has a squarefree denominator"
                         "в общем целом базисе поля K(x, y): остаток H = 0, ответ — алгебраическая часть G",
                         "in the general integral basis of the field K(x, y): the remainder H = 0, the answer is the algebraic part G" ]
      "alg-infinity", e (t "Полюсы на бесконечности" "Poles at infinity")
                        [ "замена x = a + 1/z переводит ∞ в z = 0; полюсы дифференциала сняты поправкой G∞, остаток равен 0",
                          "the substitution x = a + 1/z moves ∞ to z = 0; the poles of the differential are removed by the correction G∞, the remainder is 0"
                          "замена x = a + 1/z переводит ∞ в z = 0; снята точная часть G∞, остаток H′ идёт в логарифмическую часть",
                          "the substitution x = a + 1/z moves ∞ to z = 0; the exact part G∞ is removed, the remainder H′ goes to the logarithmic part" ]
      "alg-residues", ec (t "Вычеты H dx и дивизор вычетов δ" "Residues of H dx and the residue divisor δ")
                        [ "вычеты: ", "residues: "
                          ", ветвление)", ", ramified)"
                          " в (", " at ("
                          ". Проверки: сумма вычетов = 0; R(t) = ", ". Checks: the sum of the residues = 0; R(t) = "
                          " с корнями — вычетами (с кратностями). δ = Σ m·res·P, m = ",
                          " has as roots the residues (with multiplicities). δ = Σ m·res·P, m = "
                          " (наименьшее натуральное, при котором все m·res целые)", " (the least positive integer making all m·res integers)"
                          "; степень δ = 0", "; degree of δ = 0" ]
      "alg-torsion-bound", e (t "Граница кручения B (число точек по модулю p)" "Torsion bound B (point counts modulo p)")
                             [ "граница не найдена среди хороших p ≤ 50: перебираются n = 1…12",
                               "no bound was found among good primes p ≤ 50: n = 1…12 are tried"
                               "хорошие p (p ∤ disc P): ", "good primes (p ∤ disc P): "
                               "хорошие p (p ∤ disc P·d): ", "good primes (p ∤ disc P·d): "
                               " (расщеплено, поле вычетов F_p): #J(F_p) = L_p(1) = ", " (split, residue field F_p): #J(F_p) = L_p(1) = "
                               " (инертно, поле вычетов F_(p²)): #J(F_(p²)) = L_p(1)·L_p(−1) = ",
                               " (inert, residue field F_(p²)): #J(F_(p²)) = L_p(1)·L_p(−1) = "
                               " (аффинных ", " (affine points "
                               "; на ∞: ", "; at ∞: "
                               "; B = НОД = ", "; B = gcd = " ]
      "alg-principal", ec (t "Проверка главности n·δ" "Principal-divisor test for n·δ")
                         [ "n·δ главный при n = ", "n·δ is principal for n = "
                           ": найдена функция u с div u = ", ": a function u with div u = "
                           "·δ (перебор n ∈ {", "·δ was found (tried n ∈ {"
                           "n·δ не главный ни при одном n ∈ {", "n·δ is not principal for any n ∈ {"
                           "; n | B = ", "; n | B = "
                           ": порядок δ в J(ℚ) делит #J(F_p) для хороших p (редукция инъективна на кручении)",
                           ": the order of δ in J(ℚ) divides #J(F_p) for good p (reduction is injective on torsion)"
                           "; при отвергнутых n ∈ {", "; for the rejected n ∈ {"
                           "} пространство L(−n·δ) = {u : div u ≥ n·δ} нулевое, функции u нет",
                           "} the space L(−n·δ) = {u : div u ≥ n·δ} is zero, there is no function u"
                           "; для каждого n пространство L(−n·δ) = {u : div u ≥ n·δ} нулевое, функции u нет",
                           "; for every n the space L(−n·δ) = {u : div u ≥ n·δ} is zero, there is no function u"
                           "поиск функции u не завершён", "the search for the function u did not finish"
                           "сертификат (закон сложения на E): ", "certificate (group law on E): "
                           " — порядок δ равен ", " — the order of δ is "
                           "; kT ≠ O для всех k | B = ", "; kT ≠ O for all k | B = "
                           " — δ не кручение", " — δ is not torsion"
                           "расхождение сертификата: L(D) даёт порядок δ, равный ", "certificate mismatch: L(D) gives the order of δ equal to "
                           "расхождение сертификата: L(D) не находит порядка (n·δ не главный при n ∈ {",
                           "certificate mismatch: L(D) finds no order (n·δ is not principal for n ∈ {"
                           "}), а закон сложения на E — ", "}), while the group law on E gives "
                           ", а закон сложения на E — ", ", while the group law on E gives "
                           "kT = O уже при k = ", "kT = O already at k = " ]
      "alg-log-part", e (t "Логарифмическая часть" "Logarithmic part")
                        (t "H dx = Σ (q/(m·n))·d(log u): найдены функции u, проверка H − Σ (q/(m·n))·u′/u = 0 точная"
                           "H dx = Σ (q/(m·n))·d(log u): the functions u are found, the check H − Σ (q/(m·n))·u′/u = 0 is exact")
      "alg-certificate", e (t "Сертификат ответа" "Certificate of the answer")
                            [ "точная проверка в поле K(x, y): H = Σ (q/(m·n))·u′/u (hyp-log-check); численная проверка неустойчива из-за сокращения",
                              "exact check in the field K(x, y): H = Σ (q/(m·n))·u′/u (hyp-log-check); the numeric check is unstable because of cancellation"
                              "производная ответа совпадает с подынтегральной функцией (int-check)",
                              "the derivative of the answer equals the integrand (int-check)" ]
      "alg-refusal", ec (t "Неэлементарность доказана" "Non-elementarity proved")
                       [ "остаток H голоморфен во всех точках и H ≠ 0 — интеграл 1-го рода неэлементарен (Лиувилль, Трагер гл. 5)",
                         "the remainder H is holomorphic at all points and H ≠ 0 — the integral of the first kind is not elementary (Liouville, Trager ch. 5)"
                         "вычеты и граница кручения Трагера отвергают все n, либо остаток голоморфен и не 0, либо у него неснимаемый полюс порядка ≥ 2 (2-й род)",
                         "the residues and Trager's torsion bound reject every n, or the remainder is holomorphic and nonzero, or it has an irremovable pole of order ≥ 2 (second kind)"
                         "полюсы над неприводимыми множителями знаменателя: ни при каком n функция u не найдена (B — граница кручения)",
                         "poles over irreducible factors of the denominator: no function u is found for any n (B is the torsion bound)"
                         "вычетов нет, остаток H голоморфен и H ≠ 0 — интеграл 1-го рода неэлементарен (Лиувилль, Трагер гл. 5)",
                         "there are no residues, the remainder H is holomorphic and H ≠ 0 — the integral of the first kind is not elementary (Liouville, Trager ch. 5)"
                         "вычетов нет, у H неснимаемый полюс порядка ≥ 2 на ∞ (ненулевой класс 2-го рода) — интеграл неэлементарен",
                         "there are no residues, H has an irremovable pole of order ≥ 2 at ∞ (nonzero class of the second kind) — the integral is not elementary"
                         "вычеты в ℚ(√d): дивизор δ не кручение (граница кручения известна, n·δ не главный) — интеграл неэлементарен",
                         "residues in ℚ(√d): the divisor δ is not torsion (the torsion bound is known, n·δ is not principal) — the integral is not elementary"
                         "δ не кручение: B = ", "δ is not torsion: B = "
                         ", перебраны n ∈ {", ", tried n ∈ {"
                         "}, n·δ не главный ни при одном — по Трагеру ∫ неэлементарен",
                         "}, n·δ is not principal for any of them — by Trager's theorem the integral is not elementary"
                         "дивизор вычетов — кручение (n = ", "the residue divisor is torsion (n = "
                         "), но остаток H − (1/", "), but the remainder H − (1/"
                         ")·u′/u = (", ")·u′/u = ("
                         ")·dx/y — дифференциал 1-го рода (голоморфный во всех точках, ненулевой) — первообразной нет (Лиувилль, Трагер гл. 5)",
                         ")·dx/y — a differential of the first kind (holomorphic at all points, nonzero) — there is no antiderivative (Liouville, Trager ch. 5)"
                         ")·u′/u голоморфен и не равен 0 — первообразной нет (1-й род, Лиувилль, Трагер гл. 5)",
                         ")·u′/u is holomorphic and nonzero — there is no antiderivative (first kind, Liouville, Trager ch. 5)"
                         "), но у остатка H − (1/", "), but the remainder H − (1/"
                         ")·u′/u неснимаемый полюс порядка ≥ 2 на ∞ (ненулевой класс 2-го рода) — первообразной нет",
                         ")·u′/u has an irremovable pole of order ≥ 2 at ∞ (nonzero class of the second kind) — there is no antiderivative"
                         "теорема Чебышёва: интеграл ∫ x^m (a + b·x^n)^p dx элементарен только если p, (m+1)/n или (m+1)/n + p целое; здесь p = ",
                         "Chebyshev's theorem: the integral ∫ x^m (a + b·x^n)^p dx is elementary only if p, (m+1)/n or (m+1)/n + p is an integer; here p = " ]
      "gn-integration", e (t "Кривая рода 0: параметризация и интеграл по параметру"
                             "Genus 0 curve: parametrization and the integral in the parameter") []
      "gn-parametrization", e (t "Параметризация кривой рода 0" "Parametrization of the genus 0 curve")
                               (t "; обратно t = " "; inverse t = ")
      "gn-rational-integral", e (t "Интеграл по параметру t" "The integral in the parameter t")
                                (t "подынтегральная функция рациональна по t: интегрируем (Эрмит, ЛРТ), затем обратная подстановка t = t(x, y)"
                                   "the integrand is rational in t: integrate (Hermite, LRT), then the back substitution t = t(x, y)")
      "mx-integration", e (t "Смешанный случай: радикал над башней exp/log" "Mixed case: a radical over an exp/log tower") []
      "mx-substitution", e (t "Подстановка t = θ(x)" "Substitution t = θ(x)")
                             [ ": g не содержит x, exp, log — алгебраический случай по t",
                               ": g contains no x, exp, log — an algebraic case in t"
                               ": в g остаются x, exp или log — после рационализации Риш по параметру",
                               ": g still contains x, exp or log — after rationalization, Risch in the parameter" ]
      "mx-transformed", e (t "Интеграл по t" "The integral in t")
                           [ "g(t) — алгебраическая функция от t без x: интегрируем алгебраическим путём (кривая рода 0 или Эрмит–Трагер)",
                             "g(t) is an algebraic function of t without x: integrated by the algebraic path (genus 0 curve or Hermite–Trager)"
                             "g(t) — функция башни exp/log от t без радикалов: алгоритм Риша по t",
                             "g(t) is a function of an exp/log tower in t without radicals: the Risch algorithm in t" ]
      "mx-back-substitution", e (t "Обратная подстановка и проверка" "Back substitution and check")
                                (t "; производная ответа совпадает с подынтегральной функцией"
                                   "; the derivative of the answer equals the integrand")
      "mx-rationalization", e (t "Рационализация кривой рода 0" "Rationalization of the genus 0 curve")
                               [ "параметр w = ", "parameter w = "
                                 ": радикал исчезает, log t и eᵗ остаются башней над ℚ(w) — Риш по w",
                                 ": the radical disappears, log t and eᵗ remain a tower over ℚ(w) — Risch in w" ]
      "mx-transfer", e (t "Перенос отказа на исходный интеграл" "Transferring the refusal to the original integral")
                       [ "флаги: g без x, константы в ℚ, внутренний вердикт доказан, отображение проверено численно; ",
                         "flags: g without x, constants in ℚ, the inner verdict is proved, the map is checked numerically; "
                         "интеграл по t (t = ", "the integral in t (t = "
                         ") неэлементарен (внутренний вердикт: ", ") is not elementary (inner verdict: "
                         "алгебраический Трагер", "algebraic Trager"
                         "алгоритм Риша", "the Risch algorithm"
                         "), по лемме Розенлихта исходной первообразной тоже нет",
                         "), by Rosenlicht's lemma the original integral has no antiderivative either" ]
      "pc-integration", e (t "Интеграл с параметрами: разбор случаев" "Integral with parameters: case analysis")
                           (t "вид первообразной зависит от знака или нуля выражения от параметров: ответ — piecewise по ветвям"
                              "the form of the antiderivative depends on the sign or zero of an expression in the parameters: the answer is a piecewise over the branches")
      "pc-family", e (t "Решающее выражение" "Deciding expression")
                     [ "знак или нуль выражения E = ", "the sign or zero of the expression E = "
                       " определяет вид первообразной; без деклараций параметры вещественны",
                       " determines the form of the antiderivative; without declarations the parameters are real" ]
      "pc-branch", e (t "Случай по знаку или нулю параметра" "Case by the sign or zero of the parameter")
                     (t "первообразная при выполнении условия" "the antiderivative when the condition holds")
      "pc-certificate", e (t "Сертификат ветвей" "Certificate of the branches")
                          (t "условия ветвей покрывают все значения параметров; каждая ветвь проверена дифференцированием в 1–3 допустимых рациональных точках"
                             "the branch conditions cover all parameter values; each branch is checked by differentiation at 1–3 admissible rational points")

      // --- линейная алгебра (LA.4) ---
      "charpoly", e (t "характеристический многочлен" "characteristic polynomial") []
      "eigen-roots", e (t "корни характеристического многочлена (кратности)" "roots of the characteristic polynomial (with multiplicities)") []
      "kernel", e (t "ядро A − λI (собственные векторы)" "kernel of A − λI (eigenvectors)") []
      "jordan-chains", e (t "жордановы цепочки (обобщённые собственные векторы)" "Jordan chains (generalized eigenvectors)") []
      "exp-blocks", e (t "e^{Jt} по жордановым блокам" "e^{Jt} over the Jordan blocks") []
      "pfjp", e (t "P·e^J·P⁻¹" "P·e^J·P⁻¹") []

      // --- линейное программирование (LP.3) ---
      "lp-canon", e (t "каноническая форма: неравенства → равенства со slack/surplus"
                         "canonical form: inequalities → equalities with slack/surplus") []
      "lp-phase1", e (t "фаза 1: искусственные переменные (max −Σ art)"
                          "phase 1: artificial variables (max −Σ art)") []
      "lp-phase2", e (t "фаза 2: симплекс на целевой функции"
                          "phase 2: the simplex method on the objective function") []
      "lp-pivot", e [ "симплекс-итерация ", "simplex iteration "
                      ": входит переменная ", ": the entering variable is "
                      ", выходит переменная ", ", the leaving variable is "
                      " (строка ", " (row "
                      "), отношение rhs/a = ", "), the ratio rhs/a = " ] []
      "lp-optimal", e (t "оптимум: value = " "the optimum: value = ")
                        [ ", финальная симплекс-таблица", ", the final simplex tableau"
                          "двойственные цены: y = ", "the dual prices: y = " ]
      "lp-farkas", e (t "несовместность: сертификат леммы Фаркаша (цены строк)"
                        "infeasibility: a Farkas lemma certificate (row prices)") []
      "lp-unbounded", e (t "неограниченность: луч d (cᵀd > 0, Ad ∘ 0)"
                            "unboundedness: the ray d (cᵀd > 0, Ad ∘ 0)") []
      "ilp-bnb", e (t "ветви и границы: целочисленное ЛП"
                       "branch and bound: integer linear programming") []
      "ilp-branch", e [ "ветвь: x", "branch: x" ] []

      // --- solve (S.4) ---
      "solve-equation", e (t "Решение уравнения относительно " "Solving the equation for ") []
      "solve-move-terms", e (t "Перенос слагаемых в левую часть" "Moving the terms to the left-hand side")
                            (t "уравнение a = b равносильно a − b = 0" "the equation a = b is equivalent to a − b = 0")
      "solve-clear-denominator", e (t "Умножение на знаменатель" "Multiplying by the denominator")
                                   (t "дробь равна нулю, когда числитель равен нулю, а знаменатель не равен нулю"
                                      "a fraction is zero when the numerator is zero and the denominator is not")
      "solve-exclude-denominator-roots", e (t "Исключение корней знаменателя" "Excluding the roots of the denominator")
                                           [ "знаменатель ", "the denominator "
                                             " обращается в нуль при отброшенных значениях", " vanishes at the discarded values" ]
      "solve-linear", e (t "Линейное уравнение" "Linear equation")
                        [ "; здесь a = ", "; here a = "
                          "; условие a ≠ 0 записано в conditions", "; the condition a ≠ 0 is recorded in conditions" ]
      "solve-quadratic", e (t "Квадратное уравнение" "Quadratic equation")
                           [ "; дискриминант D = b² − 4ac = ", "; discriminant D = b² − 4ac = "
                             "; корни x = (−b ± √D)/(2a)", "; roots x = (−b ± √D)/(2a)"
                             " > 0: два корня x", " > 0: two roots x"
                             ": один корень x = −b/(2a)", ": one root x = −b/(2a)"
                             " < 0: два комплексных корня x", " < 0: two complex roots x"
                             " < 0: вещественных корней нет", " < 0: no real roots" ]
      "solve-polynomial", e (t "Уравнение высокой степени" "Higher-degree equation")
                            [ "многочлен степени ", "polynomial of degree "
                              " без рациональных корней: вещественные корни — алгебраические числа (изоляция корней по Штурму)",
                              " without rational roots: the real roots are algebraic numbers (root isolation by Sturm)"
                              "; остальные (невещественные) корни записаны как root-of", "; the remaining (non-real) roots are written as root-of"
                              " с параметрами: корни записаны как root-of", " with parameters: the roots are written as root-of" ]
      "solve-factor", e (t "Разложение на множители" "Factoring")
                       (t "произведение равно нулю, когда хотя бы один множитель равен нулю: "
                          "a product is zero when at least one factor is zero: ")
      "solve-substitution", e (t "Замена переменной" "Change of variable")
                              [ ": уравнение становится многочленом от ", ": the equation becomes a polynomial in "
                                "; найдя его корни, возвращаемся к x", "; after finding its roots we return to x" ]
      "solve-inverse-function", e [ "Обращение функции", "Inverting the function"; "Обращение", "Inversion" ]
                                  [ "(для v ≠ 0; в ℝ нужно v > 0)", "(for v ≠ 0; in ℝ we need v > 0)"
                                    ", k — целое", ", k is an integer"
                                    "степенное уравнение: ", "power equation: "
                                    " ⇒ корни n-й степени из v (чётная степень — оба знака); ", " ⇒ n-th roots of v (an even power gives both signs); " ]
      "solve-isolate", e [ "Перенос слагаемых без неизвестной", "Moving the terms without the unknown"
                           "Деление на множитель без неизвестной", "Dividing by a factor without the unknown" ]
                         [ "слагаемые, не содержащие неизвестную, переносятся в правую часть",
                           "the terms not containing the unknown are moved to the right-hand side"
                           "обе части делятся на множитель без неизвестной (он считается ненулевым)",
                           "both sides are divided by the factor without the unknown (assumed nonzero)" ]
      "solve-square", e (t "Возведение в квадрат" "Squaring")
                        (t "; возведение в квадрат может дать посторонние корни — они отсеиваются проверкой подстановкой"
                           "; squaring may introduce extraneous roots, which are removed by checking by substitution")
      "solve-trig-ratio", e (t "Деление на косинус: уравнение для тангенса" "Dividing by cosine: an equation for the tangent")
                            (t " (cos w = 0 не даёт корней: тогда и sin w = 0)" " (cos w = 0 gives no roots: then sin w = 0 as well)")
      "solve-check-roots", e (t "Проверка корней подстановкой" "Checking the roots by substitution")
                             (t "посторонние корни (например, после возведения в квадрат) отбрасываются"
                                "extraneous roots (for example, after squaring) are discarded")
      "solve-domain-filter", e (t "Отбор корней по области значений" "Selecting the roots by the domain")
                               [ "решения, не принадлежащие объявленной области значений ", "solutions outside the declared domain of "
                                 ", отбрасываются", " are discarded" ]
      "solve-linear-system", e (t "Линейная система: метод Гаусса–Жордана" "Linear system: Gauss–Jordan method")
                               [ "система несовместна: после приведения матрицы получена строка 0 = c, c ≠ 0",
                                 "the system is inconsistent: reducing the matrix gives a row 0 = c with c ≠ 0"
                                 "система недоопределена: свободные переменные остаются параметрами, остальные выражены через них",
                                 "the system is underdetermined: the free variables remain parameters, the others are expressed through them"
                                 "расширенная матрица приводится к ступенчатому виду (ведущие элементы нормируются и исключаются из остальных строк): единственное решение",
                                 "the augmented matrix is reduced to echelon form (pivots are normalized and eliminated from the other rows): a unique solution" ]

      // --- limit (S.4) ---
      "limit", e [ "Предел при ", "Limit as "; " справа", " from the right"; " слева", " from the left" ] []
      "limit-substitution", e (t "Прямая подстановка" "Direct substitution")
                              [ "функция непрерывна в точке ", "the function is continuous at the point "
                                ", предел равен значению: ", ", the limit equals the value: " ]
      "limit-combine", e (t "Предел через пределы частей" "Limit via the limits of the parts")
                         [ "предел суммы равен сумме пределов", "the limit of a sum is the sum of the limits"
                           "предел произведения равен произведению пределов", "the limit of a product is the product of the limits"
                           "предел степени вычисляется по пределам основания и показателя",
                           "the limit of a power is computed from the limits of the base and the exponent"
                           "функция непрерывна: предел аргумента подставляется в функцию",
                           "the function is continuous: the limit of the argument is substituted into the function" ]
      "limit-series", e (t "Разложение в ряд: ведущий член" "Series expansion: leading term")
                       [ "в переменной ", "in the variable "
                         "ведущий член ряда ", "leading term of the series "
                         " (степень ", " (degree "
                         "коэффициент содержит log: предел коэффициента берётся по L = log t → −∞",
                         "the coefficient contains log: the limit of the coefficient is taken in L = log t → −∞"
                         "степень положительна, поэтому предел равен 0", "the degree is positive, so the limit is 0"
                         "степень равна нулю, поэтому предел равен коэффициенту", "the degree is zero, so the limit equals the coefficient"
                         "степень отрицательна: предел бесконечен, знак определяется знаком коэффициента и стороной",
                         "the degree is negative: the limit is infinite, its sign is determined by the sign of the coefficient and the side"
                         "; ряд: ", "; series: " ]
      "limit-infinity", e (t "Замена " "Substitution ")
                         (t "предел при x → ∞ сводится к пределу при t → 0+ от выражения, в котором x заменено на ±1/t"
                            "the limit as x → ∞ reduces to the limit as t → 0+ of the expression with x replaced by ±1/t")
      "limit-power", e (t "Степень с переменным показателем" "Power with a variable exponent") (t ", поэтому " ", so ")
      "limit-power-exponent", e (t "Предел показателя g·log f" "Limit of the exponent g·log f") []
      "limit-lhopital", e (t "Правило Лопиталя" "L'Hôpital's rule")
                          [ "неопределённость ", "indeterminate form "
                            ": числитель ", ": numerator "
                            ", знаменатель ", ", denominator " ]
      "limit-derivatives", e (t "Производные числителя и знаменателя" "Derivatives of the numerator and the denominator") []
      "limit-factor-leading", e (t "Вынесение слагаемого за скобку" "Factoring out a term")
                                [ "(остальные)", "(others)"
                                  ", где T = ", ", where T = "
                                  ": предел сводится к ", ": the limit reduces to " ]
      "limit-gruntz", e (t "Сравнение скоростей роста (алгоритм Грунца)" "Comparing growth rates (Gruntz's algorithm)")
                        (t "выделяется множество самых быстро меняющихся подвыражений (MRV), через него выражается малая величина ω → 0+, предел определяется ведущим членом c·ω^e"
                           "the set of the fastest varying subexpressions (MRV) is found, a small quantity ω → 0+ is expressed through it, and the limit is determined by the leading term c·ω^e")
      "limit-gruntz-substitution", e (t "Замена " "Substitution ")
                                     [ "предел при ", "the limit as "
                                       " сводится к пределу при ", " reduces to the limit as "
                                       " (замена ", " (substitution " ]
      "limit-gruntz-mrv", e (t "Самые быстрые подвыражения (MRV)" "The fastest subexpressions (MRV)")
                            [ "множество MRV: ", "the MRV set: "
                              "; в него входят подвыражения, растущие быстрее всех остальных (одного класса роста)",
                              "; it consists of the subexpressions that grow fastest (of one growth class)" ]
      "limit-gruntz-lead", e (t "Ведущий член ω^e" "Leading term ω^e")
                             [ "ω — быстрая величина, стремящаяся к 0+; ведущий член c·ω^e: c = ",
                               "ω is the fast quantity tending to 0+; the leading term c·ω^e: c = "
                               "; при e > 0 предел 0, при e < 0 — ±∞ по знаку c, при e = 0 — предел c",
                               "; for e > 0 the limit is 0, for e < 0 it is ±∞ by the sign of c, for e = 0 it equals c" ]
      "limit-abs", e (t "Раскрытие модуля" "Removing the absolute value")
                     [ "знак аргумента модуля определяется вблизи точки; ", "the sign of the argument of the absolute value is determined near the point; "
                       " заменяется на ", " is replaced by "
                       ", двусторонний предел — сравнение односторонних", ", a two-sided limit compares the one-sided ones" ]
      "limit-step", e (t "Ступенька Хевисайда и дельта" "Heaviside step and Dirac delta")
                     [ "θ(u) заменяется на 1 или 0 по знаку u вблизи точки, δ(u) — на 0 (u не стремится к 0); двусторонний предел — сравнение односторонних",
                       "θ(u) is replaced by 1 or 0 by the sign of u near the point, δ(u) by 0 (u does not tend to 0); a two-sided limit compares the one-sided ones" ]

      // --- series (S.4) ---
      "series", e [ "Разложение в ряд Тейлора (Лорана) в точке ", "Taylor (Laurent) series expansion at the point "
                    " до порядка ", " up to order " ]
                  [ "ряд Лорана: есть члены с отрицательными степенями", "Laurent series: there are terms with negative powers"
                    "ряд Тейлора", "Taylor series"
                    "; внутри — использованные стандартные разложения и операции над рядами",
                    "; inside: the standard expansions and series operations used" ]
      "series-known", e [ "Стандартное разложение", "Standard expansion"; "Биномиальный ряд", "Binomial series" ]
                       [ ": ряд синуса делится на ряд косинуса", ": the sine series is divided by the cosine series"
                         ": ряд косинуса делится на ряд синуса", ": the cosine series is divided by the sine series"
                         " (биномиальный ряд)", " (binomial series)"
                         "стандартное разложение функции по степеням аргумента", "standard expansion of the function in powers of the argument"
                         "; здесь u = ", "; here u = "
                         " выносится за степень", " is taken out of the power" ]
      "series-compose", e [ "Подстановка ряда аргумента", "Substituting the argument series"
                            "Степень с переменным показателем", "Power with a variable exponent" ]
                         [ ": ряд g·log f подставляется в разложение экспоненты", ": the series of g·log f is substituted into the expansion of the exponential"
                           "ряд аргумента ", "the series of the argument "
                           " подставляется в разложение функции ", " is substituted into the expansion of the function " ]
      "series-arith", e [ "Сумма рядов", "Sum of series"
                          "Разность рядов", "Difference of series"
                          "Произведение рядов", "Product of series"
                          "Частное рядов", "Quotient of series"
                          "Отрицательная степень ряда", "Negative power of a series"
                          "Степень ряда", "Power of a series" ]
                        [ "ряды слагаемых складываются почленно", "the series of the terms are added term by term"
                          "ряды перемножаются (свёртка коэффициентов), результат усекается до нужного порядка",
                          "the series are multiplied (convolution of coefficients), the result is truncated to the required order"
                          "ряд делителя заменяется обратным рядом и умножается на ряд делимого",
                          "the divisor series is replaced by its reciprocal series and multiplied by the dividend series"
                          "степень — повторное умножение ряда на себя; отрицательная — через обратный ряд",
                          "a power is repeated multiplication of the series by itself; a negative one goes through the reciprocal series" ]
      "series-derivatives", e (t "Ряд Тейлора через производные" "Taylor series via derivatives")
                              [ "коэффициенты ", "the coefficients "
                                " вычисляются последовательным дифференцированием", " are computed by successive differentiation" ]

      // --- diophantine / sums of squares / SOS (ST.3г-2) ---
      "dio-bezout", e (t "Расширенный Евклид" "Extended Euclid") []
      "dio-none", e (t "Решений нет" "No solutions") []
      "dio-particular", e (t "Частное решение" "Particular solution") []
      "dio-general", e (t "Общее решение" "General solution") []
      "pell-cf", e (t "Цепная дробь √D" "Continued fraction of √D") []
      "pell-solution", e (t "Фундаментальное решение" "Fundamental solution") []
      "pell-check", e (t "Проверка решения" "Checking the solution") []
      "pell-negative", e (t "Отрицательное уравнение Пелля" "Negative Pell equation") []
      "sq-none", e (t "Представления нет" "No representation") []
      "sq-representation", e (t "Найденное представление" "Representation found") []
      "sq-check", e (t "Проверка суммы квадратов" "Checking the sum of squares") []
      "sos-method", e (t "Метод доказательства" "Proof method") []
      "sos-decomposition", e (t "Разложение в сумму квадратов" "Sum-of-squares decomposition") []
      "sos-check", e (t "Проверка разложения" "Checking the decomposition") []
      "sos-refuse", e (t "Доказательство не найдено" "No proof found") []

      // --- galois / denest (ST.3г-1) ---
      "gal-irreducible", e (t "Неприводимость над Q" "Irreducibility over Q") []
      "gal-discriminant", e (t "Дискриминант" "Discriminant") []
      "gal-cycles", e (t "Типы циклов по простым (Дедекинд)" "Cycle types modulo primes (Dedekind)") []
      "gal-resolvents", e (t "Резольвенты" "Resolvents") []
      "gal-candidates", e (t "Отсев кандидатов" "Filtering candidates") []
      "gal-conclusion", e (t "Группа Галуа" "Galois group") []
      "gal-check", e (t "Проверка сертификата" "Certificate check") []
      "gal-solvability", e (t "Разрешимость в радикалах" "Solvability by radicals") []
      "gal-radicals", e (t "Выражение корней радикалами" "Roots in radicals") []
      "dn-formula", e (t "Денестинг квадратного радикала" "Denesting a square radical") []
      "dn-refuse", e (t "Денестинг невозможен" "Denesting impossible") []

      // --- definite integrals (ST.3в-2) ---
      "di-definite", e (t "Определённый интеграл" "Definite integral") []
      "di-method", e (t "Выбор метода" "Choosing the method") []
      "di-divergent", e (t "Интеграл расходится" "Integral diverges") []
      "di-newton", e (t "Формула Ньютона — Лейбница" "Newton–Leibniz formula") []
      "di-singular", e (t "Особые точки внутри отрезка" "Singular points inside the interval") []
      "di-residues", e (t "Полюса в верхней полуплоскости и вычеты" "Poles in the upper half-plane and residues") []
      "di-keyhole", e (t "Замочная скважина" "Keyhole contour") []

      // --- transforms (ST.3в-1): Лаплас, Z, Фурье ---
      "lt-forward", e (t "Прямое преобразование Лапласа" "Direct Laplace transform") []
      "lt-inverse", e (t "Обратное преобразование Лапласа" "Inverse Laplace transform") []
      "lt-exp", e (t "Прямое преобразование: правило" "Direct transform: rule") []
      "lt-heaviside", e (t "Прямое преобразование: правило" "Direct transform: rule") []
      "lt-dirac", e (t "Прямое преобразование: правило" "Direct transform: rule") []
      "lt-tpow", e (t "Прямое преобразование: правило" "Direct transform: rule") []
      "lt-table", e (t "Прямое преобразование: правило" "Direct transform: rule") []
      "lt-linearity", e (t "Линейность преобразования" "Linearity") []
      "lt-inv-partial", e (t "Разложение на простейшие дроби" "Partial fractions") []
      "lt-inv-term", e (t "Обратное преобразование слагаемого" "Inverse transform of a term") []
      "lt-inv-check", e (t "Проверка обратного преобразования" "Checking the inverse transform") []
      "ld-solve", e (t "Решение ОДУ преобразованием Лапласа" "Solving an ODE by Laplace transform") []
      "ld-transform", e (t "Преобразованное уравнение" "Transformed equation") []
      "ld-initial", e (t "Начальные условия" "Initial conditions") []
      "ld-ys", e (t "Изображение Y(s)" "Image Y(s)") []
      "ld-inverse", e (t "Обратное преобразование" "Inverse transform") []
      "ld-check", e (t "Проверка подстановкой" "Check by substitution") []
      "tz-forward", e (t "Z-преобразование" "Z-transform") []
      "tz-inverse", e (t "Обратное Z-преобразование" "Inverse Z-transform") []
      "tz-rule", e (t "Применённое правило" "Applied rule") []
      "tz-inv-partial", e (t "Разложение F(z)/z на простейшие дроби" "Partial fractions of F(z)/z") []
      "tz-inv-term", e (t "Обратное Z-преобразование слагаемого" "Inverse Z-transform of a term") []
      "tz-inv-check", e (t "Проверка обратного Z-преобразования" "Checking the inverse Z-transform") []
      "tz-transform", e (t "Преобразованное уравнение" "Transformed equation") []
      "tz-initial", e (t "Начальные условия" "Initial conditions") []
      "tz-az", e (t "Изображение A(z)" "Image A(z)") []
      "tz-solution", e (t "Решение разностного уравнения" "Solving the difference equation") []
      "tz-check", e (t "Проверка подстановкой" "Check by substitution") []
      "tf-forward", e (t "Преобразование Фурье" "Fourier transform") []
      "tf-inverse", e (t "Обратное преобразование Фурье" "Inverse Fourier transform") []
      "tf-rule", e (t "Применённое правило" "Applied rule") []
      "tf-inv-partial", e (t "Обратное преобразование: разложение" "Inverse transform: decomposition") []
      "tf-inv-check", e (t "Проверка обратного преобразования" "Checking the inverse transform") []

      // --- ODE steps (ST.3а-1): первый порядок ---
      "ode-classify", e (t "Классификация уравнения" "Classifying the equation") []
      "ode-check", e (t "Проверка решения" "Checking the solution") []
      "ode-refuse", e (t "Решение не найдено" "No solution found") []
      "ode-fo-separable", e (t "Разделение переменных" "Separation of variables") []
      "ode-fo-linear", e (t "Линейное уравнение 1-го порядка" "First-order linear equation") []
      "ode-fo-bernoulli", e (t "Уравнение Бернулли" "Bernoulli equation") []
      "ode-fo-homogeneous", e (t "Однородное уравнение (y = v·x)" "Homogeneous equation (y = v·x)") []
      "ode-fo-singular", e (t "Особые решения" "Singular solutions") []
      "ode-ex-exact", e (t "Точное уравнение" "Exact equation") []
      "ode-ex-mu", e (t "Интегрирующий множитель" "Integrating factor") []
      "ode-ex-riccati", e (t "Уравнение Риккати" "Riccati equation") []
      "ode-ex-clairaut", e (t "Уравнение Клеро" "Clairaut equation") []
      "ode-ex-lagrange", e (t "Уравнение Лагранжа" "Lagrange equation") []

      // --- ODE steps (ST.3а-2): линейные высших порядков, Эйлер, понижение ---
      "ode-lo-hom", e (t "Однородное уравнение с постоянными коэффициентами" "Homogeneous constant-coefficient equation") []
      "ode-lo-undet", e (t "Метод неопределённых коэффициентов" "Method of undetermined coefficients") []
      "ode-lo-var", e (t "Вариация постоянных" "Variation of parameters") []
      "ode-eu-subst", e (t "Уравнение Эйлера–Коши: замена x = e^t" "Euler–Cauchy equation: substitution x = e^t") []
      "ode-re-known", e (t "Понижение порядка (известное y₁)" "Order reduction (known y₁)") []
      "ode-re-drop-y", e (t "Уравнение без y (p = y′)" "Equation without y (p = y′)") []
      "ode-re-autonomous", e (t "Автономное уравнение (замена p = y′)" "Autonomous equation (substitution p = y′)") []

      // --- ODE steps (ST.3а-3): Коши, системы, ряды ---
      "ode-ca-consts", e (t "Константы из начальных условий" "Constants from the initial conditions") []
      "ode-ca-check", e (t "Проверка начальных условий" "Checking the initial conditions") []
      "ode-sy-matrix", e (t "Матрица системы" "System matrix") []
      "ode-sy-basis", e (t "Собственные значения и ФСР" "Eigenvalues and fundamental set") []
      "ode-sy-solution", e (t "Решение системы" "Solving the system") []
      "ode-sy-cauchy", e (t "Начальные условия системы" "Initial conditions of the system") []
      "ode-sy-check", e (t "Проверка решения системы" "Checking the system solution") []
      "ode-se-point", e (t "Точка разложения" "Expansion point") []
      "ode-se-indicial", e (t "Определяющее уравнение" "Indicial equation") []
      "ode-se-recurrence", e (t "Рекуррентность коэффициентов" "Coefficient recurrence") []
      "ode-se-series", e (t "Ряд и сертификат остатка" "Series and remainder certificate") []

      // --- summation (21l.1): символьное суммирование, L0–L2 ---
      "sum-symbolic", e (t "Символьное суммирование" "Symbolic summation") []
      "sum-empty", e (t "Пустой диапазон" "Empty range") []
      "sum-check", e (t "Проверка ответа" "Checking the answer") []
      "gosper", e (t "Алгоритм Госпера" "Gosper's algorithm") []
      "sum-path", e (t "Выбор пути суммирования" "Choosing the summation path") []
      "sum-no-path", e (t "Путь не найден" "No summation path found") []
      "gosper-ratio", e (t "Отношение соседних членов" "Ratio of consecutive terms") []
      "gosper-normal", e (t "Разложение Госпера–Петковшека" "Gosper–Petkovšek decomposition") []
      "gosper-degree", e (t "Граница степени x(k)" "Degree bound for x(k)") []
      "gosper-ansatz", e (t "Уравнение для многочлена x(k)" "Polynomial equation for x(k)") []
      "gosper-cert", e (t "Сертификат R(k)" "Certificate R(k)") []
      "gosper-check", e (t "Проверка телескопирования" "Telescoping check") []
      "gosper-refuse", e (t "Неопределённая сумма не гипергеометрическая (Госпер)" "Indefinite sum is not hypergeometric (Gosper)") []
      "abramov", e (t "Рациональное суммирование (Абрамов)" "Rational summation (Abramov)") []
      "abramov-type", e (t "Тип: рациональная функция" "Type: rational function") []
      "abramov-decompose", e (t "Разложение f = Δg + h" "Decomposition f = Δg + h") []
      "abramov-check", e (t "Проверка Δg + h = f" "Checking Δg + h = f") []
      "zeilb-order", e (t "Порядок рекуррентности" "Recurrence order") []
      "zeilb-cert", e (t "Сертификат R(n,k)" "Certificate R(n,k)") []
      "zeilb-check", e (t "Проверка сертификата" "Certificate check") []
      "zeilb-recurrence", e (t "Найденная рекуррентность" "Recurrence found") []
      "rsolve-solution", e (t "Решение рекуррентности" "Solving the recurrence") []
      "cf-charpoly", e (t "Характеристический многочлен" "Characteristic polynomial") []
      "cf-roots", e (t "Корни характеристического многочлена" "Roots of the characteristic polynomial") []
      "cf-general", e (t "Общий вид решения" "General form of the solution") []
      "cf-constants", e (t "Константы из начальных значений" "Constants from initial values") []
      "cf-check", e (t "Проверка первых членов" "Checking the first terms") []
      // --- summation (21l.5–21l.6): Цайльбергер, rsolve ---
      "sum-zeilberger", e (t "Символьное суммирование: Цайльбергер + rsolve" "Symbolic summation: Zeilberger + rsolve") []
      "sum-recurrence", e (t "Символьное суммирование: Цайльбергер (рекуррентность)" "Symbolic summation: Zeilberger (recurrence)") []
    ]

let private byRule : Collections.Generic.Dictionary<string, Entry> =
    let d = Collections.Generic.Dictionary<string, Entry>()
    for (k, v) in table do d.[k] <- v
    d

// Все rule словаря (без шаблонов семейств)
let knownRules : string list = table |> List.map fst |> List.filter (fun k -> not (k.EndsWith "*"))

// Запись для rule: точное совпадение, иначе шаблон семейства (simplify:rule:*, simplify:method:*, simplify:*)
let tryFind (rule: string) : Entry option =
    match byRule.TryGetValue rule with
    | true, v -> Some v
    | _ ->
        if rule.StartsWith "simplify:rule:" then Some byRule.["simplify:rule:*"]
        elif rule.StartsWith "simplify:method:" then Some byRule.["simplify:method:*"]
        elif rule.StartsWith "simplify:" then Some byRule.["simplify:*"]
        else None

let private cyrillic = Regex("[Ѐ-ӿ]", RegexOptions.Compiled)
let hasCyrillic (s: string) : bool = cyrillic.IsMatch s

let private apply (pairs: (string * string) list) (text: string) : string =
    pairs |> List.fold (fun (acc: string) (ru, en) -> acc.Replace(ru, en, StringComparison.Ordinal)) text

// Допустимые языки шагов
let isLang (s: string) : bool = s = "ru" || s = "en"

// Перевод одного поля; None — не удалось (остались русские буквы или нет записи)
let private translateField (pairs: (string * string) list) (withCommon: bool) (text: string) : string option =
    if text = "" || not (hasCyrillic text) then Some text
    else
        let r = apply pairs text
        let r = if withCommon then apply common r else r
        if hasCyrillic r then None else Some r

// Перевести шаги на английский; русский текст поля, не покрытого словарём, остаётся, rule → в список «нет перевода»
let localize (lang: string) (steps: StepLog.Step list) : StepLog.Step list * string list =
    if lang <> "en" then steps, []
    else
        let missing = Collections.Generic.SortedSet<string>(StringComparer.Ordinal)
        let rec conv (s: StepLog.Step) : StepLog.Step =
            let entry = tryFind s.Rule
            let title, comment =
                match entry with
                | Some en ->
                    let tt = translateField en.Title false s.Title
                    let cc = translateField en.Comment true s.Comment
                    if tt.IsNone || cc.IsNone then missing.Add s.Rule |> ignore
                    defaultArg tt s.Title, defaultArg cc s.Comment
                | None ->
                    if hasCyrillic s.Title || hasCyrillic s.Comment then missing.Add s.Rule |> ignore
                    s.Title, s.Comment
            { s with Title = title; Comment = comment; Children = List.map conv s.Children }
        let r = List.map conv steps
        r, List.ofSeq missing

// Предупреждение о правилах без перевода (None — все переведены)
let missingWarning (rules: string list) : string option =
    if rules.IsEmpty then None
    else Some ("no English translation for step rules: " + String.concat ", " rules + " (Russian text kept)")

// Служебные строки печати дерева
let noStepsText (lang: string) : string = if lang = "en" then "(no steps recorded)" else "(шаги не записаны)"
let omittedText (lang: string) (n: int) : string =
    if lang = "en" then sprintf "… %d nested steps hidden" n else sprintf "… скрыто вложенных шагов: %d" n

// Пометка об обрезке на выбранном языке (None — ничего не обрезано)
let truncationNote (lang: string) (sel: StepLog.Selection) : string option =
    if lang <> "en" then StepLog.truncationNote sel
    elif not (StepLog.isTruncated sel) then None
    else
        let why =
            [ if sel.Shown >= StepLog.MaxNodes && sel.Total > StepLog.MaxNodes then sprintf "at most %d steps" StepLog.MaxNodes
              if sel.DepthCut then sprintf "depth up to %d" StepLog.MaxDepth ]
        Some (sprintf "steps truncated: showing %d of %d (%s)" sel.Shown sel.Total
                (if why.IsEmpty then "limit" else String.concat ", " why))
