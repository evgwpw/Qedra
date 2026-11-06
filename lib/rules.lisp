; rules.lisp — условные правила упрощения (Шаг 16), написаны на Lisp поверх defrule (ядро F#).
;
; (defrule имя образец замена условие): правило срабатывает, только если условие вернуло ровно #t.
; Шаг AC.3: флаг :ac — AC-сопоставление (+ и * — мультимножества, ?r... — остаток, см. match.lisp).
; Опция :title "заголовок" — человеческий заголовок шага правила в steps (без неё — «правило имя»); английский
; перевод заголовка — в src\Cas.Algebra\StepDict.fs (ключ simplify:rule:имя). Опции :ac и :title — после условия.
; Условия — трёхзначные предикаты из domain.lisp, поэтому БЕЗ деклараций (unknown) выражение остаётся как есть;
; декларации включают правила: (assuming ((x reals)) (simplify '(^ (^ x 2) 1/2))) → (abs x).
; Образцы канонизируются при регистрации: слагаемые/множители сортируются, поэтому для двухсомножителей
; (* ?a ?b) порядок не фиксирован — условие само проверяет, какой из множителей pi.
; Квадратный корень в канонической форме остаётся (sqrt x), а возведение в 1/2 — (^ x 1/2):
; правила для sqrt(x^2) написаны для обеих форм.
; Список правил оператора — (rules 'abs); отключить — (remove-rule 'имя); трассировка — (trace-rules).

; Шаг 21h': модуль rules ничего не экспортирует: правила — записи глобальной таблицы правил; условия компилируются
; в области имён модуля (приватный pi-times-integer? виден им)
(module rules (export))

; --- abs ---
; числа сворачиваются через знак: (abs -3) → 3
(defrule abs-nonnegative (abs ?x) ?x (nonnegative? ?x) :title "Модуль неотрицательного числа")
(defrule abs-nonpositive (abs ?x) (* -1 ?x) (nonpositive? ?x) :title "Модуль неположительного числа")
(defrule abs-abs (abs (abs ?x)) (abs ?x) :title "Модуль модуля")
(defrule abs-square (abs (^ ?x 2)) (^ ?x 2) (real? ?x) :title "Модуль квадрата вещественного числа")

; --- корень из квадрата ---
(defrule sqrt-square-nonnegative (sqrt (^ ?x 2)) ?x (nonnegative? ?x)
  :title "Корень из квадрата неотрицательного числа")
(defrule sqrt-square-real (sqrt (^ ?x 2)) (abs ?x) (real? ?x)
  :title "Корень из квадрата вещественного числа")
(defrule pow-half-square-nonnegative (^ (^ ?x 2) 1/2) ?x (nonnegative? ?x)
  :title "Степень 1/2 от квадрата неотрицательного числа")
(defrule pow-half-square-real (^ (^ ?x 2) 1/2) (abs ?x) (real? ?x)
  :title "Степень 1/2 от квадрата вещественного числа")

; --- степени ---
; (x^a)^b = x^(a b) для нецелого b при x >= 0 (и вещественном a; целое b Simplify сворачивает сам)
(defrule pow-pow (^ (^ ?x ?a) ?b) (^ ?x (* ?a ?b))
  (and3 (nonnegative? ?x) (real? ?a) (not (integer? ?b)))
  :title "Степень степени (x ≥ 0)")
; (a b r)^c = a^c b^c r^c для нецелого c при a, b >= 0 (на r — любом остатке произведения — условий нет: (a b)^c ≥ 0).
; Шаг AC.3: правило :ac — множителей может быть сколько угодно, порядок не важен; условие проверяется на каждой паре a, b
(defrule pow-product (^ (* ?a ?b ?r...) ?c) (* (^ ?a ?c) (^ ?b ?c) (^ ?r... ?c))
  (and3 (nonnegative? ?a) (nonnegative? ?b) (not (integer? ?c))) :ac
  :title "Степень произведения неотрицательных множителей")

; --- log / exp ---
(defrule log-exp (log (exp ?x)) ?x (real? ?x) :title "Логарифм экспоненты")
(defrule exp-log (exp (log ?x)) ?x :title "Экспонента логарифма")           ; безусловно: допущение x != 0

; Шаг AS: ветви log и sqrt при ЯВНЫХ допущениях (главная ветвь, arg ∈ (−π, π]; docs/math-language.md «Ветви и допущения»).
; Правила срабатывают, только если в множителе/основании есть символ с декларацией (asm-dep?): чисто числовые знаки
; (log(2x), pi) без допущений не трогаются — старые ответы не меняются.
(define (asm-dep? e)
  (cond ((equal? e 'pi) #f)
        ((symbol? e) (not (null? (declarations e))))
        ((pair? e) (not (null? (filter asm-dep? (cdr e)))))
        (else #f)))
(define (neg-even-pow? x n)
  (and (integer? n) (= (mod n 2) 0) (equal? (negative? x) #t)))
; log(x^n) = n log x при x > 0, n вещественное
(defrule log-pow-positive (log (^ ?x ?n)) (* ?n (log ?x)) (and3 (positive? ?x) (asm-dep? ?x) (real? ?n))
  :title "Логарифм степени (x > 0)")
; log(x^(2k)) = 2k log(-x) при x < 0
(defrule log-pow-negative-even (log (^ ?x ?n)) (* ?n (log (* -1 ?x))) (and3 (asm-dep? ?x) (neg-even-pow? ?x ?n))
  :title "Логарифм чётной степени (x < 0)")
(defrule log-pow-negative-twok (log (^ ?x (* 2 ?k...))) (* 2 ?k... (log (* -1 ?x)))
  (and3 (negative? ?x) (asm-dep? ?x) (integer-valued? ?k...)) :ac
  :title "Логарифм чётной степени 2k (x < 0)")
; log(a b) = log a + log b при a > 0 (b любое ненулевое: arg(ab) = arg b)
(defrule log-product-positive (log (* ?a ?b ?r...)) (+ (log ?a) (log (* ?b ?r...)))
  (and3 (positive? ?a) (asm-dep? ?a)) :ac
  :title "Логарифм произведения с положительным множителем")
; sqrt(a b) = sqrt a * sqrt b при a >= 0
(defrule sqrt-product-nonnegative (sqrt (* ?a ?b ?r...)) (* (sqrt ?a) (sqrt (* ?b ?r...)))
  (and3 (nonnegative? ?a) (asm-dep? ?a)) :ac
  :title "Корень из произведения с неотрицательным множителем")

; --- sin / cos кратных pi ---
; Числовые значения (sin(π) = 0, cos(2π/3) = -1/2, ...) считает ядро simplify (Шаг 21c);
; здесь — только параметрические: n целое по декларации.
; (n pi) для целого n. Шаг AC.3: правила :ac — pi и остаток ?r... произведения в любом порядке и любом числе
; множителей ((* 2 n pi): ?r... = (* 2 n)); раньше было три правила на пары (* ?a ?b) в обоих порядках.
(defrule sin-integer-pi (sin (* pi ?r...)) 0 (integer-valued? ?r...) :ac
  :title "Синус целого кратного π")
; cos(2 n pi) = 1 (раньше (^ -1 (* 2 n)) не сворачивалось): чётное кратное — отдельным правилом, до общего
(defrule cos-even-multiple-pi (cos (* 2 pi ?r...)) 1 (integer-valued? ?r...) :ac
  :title "Косинус чётного кратного π")
(defrule cos-integer-pi (cos (* pi ?r...)) (^ -1 ?r...) (integer-valued? ?r...) :ac
  :title "Косинус целого кратного π")

; --- специальные функции (Шаг SF) ---
; Тождества над ℂ: значения в нуле и нечётность erf/erfi/Si/Shi. erfc НЕ переписываем в 1 − erf
; (по решению Шага SF — оставляем как есть); Ei, li, Ci, Chi значений/чётности не имеют — правил нет.
; Нечётность: канонический минус — числовой множитель произведения, условие (negative? ?c) — трёхзначный
; предикат, поэтому с символьным множителем (знак неизвестен) правило не срабатывает; чисто числовой
; отрицательный аргумент (erf -3) остаётся атомом — отдельное правило. Обе замены → (* -1 (f |?c|·…)).
(defrule erf-zero (erf 0) 0 :title "Значение erf в нуле")
(defrule erfi-zero (erfi 0) 0 :title "Значение erfi в нуле")
(defrule si-zero (Si 0) 0 :title "Значение Si в нуле")
(defrule shi-zero (Shi 0) 0 :title "Значение Shi в нуле")
(defrule erfc-zero (erfc 0) 1 :title "Значение erfc в нуле")
(defrule erf-odd (erf (* ?c ?r...)) (* -1 (erf (* -1 ?c ?r...))) (negative? ?c) :title "Нечётность erf")
(defrule erfi-odd (erfi (* ?c ?r...)) (* -1 (erfi (* -1 ?c ?r...))) (negative? ?c) :title "Нечётность erfi")
(defrule si-odd (Si (* ?c ?r...)) (* -1 (Si (* -1 ?c ?r...))) (negative? ?c) :title "Нечётность Si")
(defrule shi-odd (Shi (* ?c ?r...)) (* -1 (Shi (* -1 ?c ?r...))) (negative? ?c) :title "Нечётность Shi")
(defrule erf-odd-number (erf ?n) (* -1 (erf (* -1 ?n))) (negative? ?n) :title "Нечётность erf (отрицательное число)")
(defrule erfi-odd-number (erfi ?n) (* -1 (erfi (* -1 ?n))) (negative? ?n) :title "Нечётность erfi (отрицательное число)")
(defrule si-odd-number (Si ?n) (* -1 (Si (* -1 ?n))) (negative? ?n) :title "Нечётность Si (отрицательное число)")
(defrule shi-odd-number (Shi ?n) (* -1 (Shi (* -1 ?n))) (negative? ?n) :title "Нечётность Shi (отрицательное число)")

; --- комбинаторные головы (Шаг 21l.0) ---
; Тождества Γ/Pochhammer/бинома; числовые значения считаются в F# (Simplify.combinatorValue),
; здесь — только структурные правила. Порядок важен: Γ(n+1) с целым n — сначала в n!,
; Γ(x+1) с вещественным x — функциональное уравнение.
(defrule gamma-factorial (gamma (+ ?n 1)) (factorial ?n) (integer-valued? ?n)
  :title "Γ(n+1) = n! для целых n")
(defrule gamma-recurrence (gamma (+ ?x 1)) (* ?x (gamma ?x))
  :title "Функциональное уравнение Γ(z+1) = z·Γ(z)")
; n! = Γ(n+1): только когда факториал не вычислим числом (отрицательный/нецелый аргумент)
(defrule factorial-gamma (factorial ?n) (gamma (+ ?n 1)) (and (not (and (integer? ?n) (>= ?n 0))) (integer-valued? ?n))
  :title "Факториал через гамма-функцию")
; биномиальные тождества (символьные)
(defrule binomial-zero-k (binomial ?n 0) 1 :title "C(n, 0) = 1")
(defrule binomial-n-k (binomial ?n ?n) 1 :title "C(n, n) = 1")
(defrule binomial-one-k (binomial ?n 1) ?n :title "C(n, 1) = n")
; Похгаммер: базовые значения
(defrule rf-one (rf ?x 1) ?x :title "(x)_1 = x")
(defrule ff-one (ff ?x 1) ?x :title "(x)‾1 = x")
(defrule rf-zero (rf ?x 0) 1 :title "(x)_0 = 1")
(defrule ff-zero (ff ?x 0) 1 :title "(x)‾0 = 1")
; гармонические: H_0 = 0, H_1 = 1 — считаются в F# (combinatorValue); defrule с константным
; образцом (harmonic 0) нельзя — упрощатель сворачивает образец в 0 при регистрации
; ψ: спецзначения (γ — символ euler-gamma; паттерн с 1/2 не сворачивается — psi не имеет точных значений)
(defrule psi-half (psi 1/2) (+ (* -1 euler-gamma) (* -2 (log 2))) :title "ψ(1/2) = −γ − 2·ln 2")

; --- Пифагор с общим множителем (Шаг AC.3) ---
; F#-упрощатель (pythag) сворачивает c sin²u + c cos²u только при числовом c; здесь c — любой общий множитель
; (?c... — остаток произведения, пустой = 1), слагаемые суммы — в любом порядке и числе: z sin²x + z cos²x + y → z + y
(defrule pythagorean-common-factor
  (+ (* ?c... (^ (sin ?u) 2)) (* ?c... (^ (cos ?u) 2)) ?r...)
  (+ ?c... ?r...) :ac
  :title "Основное тригонометрическое тождество (общий множитель)")
