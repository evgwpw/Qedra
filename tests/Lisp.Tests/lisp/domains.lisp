; Lisp-тесты доменов, интервалов, деклараций, вывода принадлежности и знака (lib\domain.lisp), Шаг 16

; --- Домены ---

(deftest "печать доменов и интервалов"
  (assert-equal (to-string naturals) "ℕ")
  (assert-equal (to-string integers) "ℤ")
  (assert-equal (to-string rationals) "ℚ")
  (assert-equal (to-string reals) "ℝ")
  (assert-equal (to-string complexes) "ℂ")
  (assert-equal (to-string (interval 0 1)) "[0, 1]")
  (assert-equal (to-string (interval 0 1 'open 'closed)) "(0, 1]")
  (assert-equal (to-string positive) "(0, inf)")
  (assert-equal (to-string nonnegative) "[0, inf)")
  (assert-equal (to-string (interval '-inf 0)) "(-inf, 0]")   ; бесконечная граница всегда открыта
  (assert-equal (to-string (interval 1 0)) "∅"))

(deftest "решётка доменов: subset?"
  (assert-equal (subset? naturals integers) #t)
  (assert-equal (subset? integers rationals) #t)
  (assert-equal (subset? rationals reals) #t)
  (assert-equal (subset? reals complexes) #t)
  (assert-equal (subset? naturals complexes) #t)
  (assert-equal (subset? integers integers) #t)
  (assert-equal (subset? integers naturals) #f)
  (assert-equal (subset? reals rationals) #f)
  (assert-equal (subset? complexes reals) #f))

(deftest "членство чисел в доменах"
  (assert-equal (in? 3 naturals) #t)
  (assert-equal (in? 0 naturals) #t)          ; ℕ содержит 0
  (assert-equal (in? -3 naturals) #f)
  (assert-equal (in? -3 integers) #t)
  (assert-equal (in? 1/2 integers) #f)
  (assert-equal (in? 1/2 rationals) #t)
  (assert-equal (in? 1.5 rationals) #f)       ; float — вещественное число
  (assert-equal (in? 1.5 reals) #t)
  (assert-equal (in? (sqrt 2) rationals) #f)  ; алгебраическое иррациональное
  (assert-equal (in? (sqrt 2) reals) #t)
  (assert-equal (in? 7 complexes) #t))

(deftest "in? с неподдерживаемым вторым аргументом — ошибка"
  (assert-error (in? 1 5))
  (assert-error (in? 1 '(1 2))))

; --- Интервалы ---

(deftest "членство чисел в интервалах"
  (assert-equal (in? 1/2 (interval 0 1)) #t)
  (assert-equal (in? 0 (interval 0 1)) #t)
  (assert-equal (in? 0 (interval 0 1 'open 'closed)) #f)
  (assert-equal (in? 1 (interval 0 1 'open 'closed)) #t)
  (assert-equal (in? 1 (interval 0 1 'open 'open)) #f)
  (assert-equal (in? 100 positive) #t)
  (assert-equal (in? 0 positive) #f)
  (assert-equal (in? 0 nonnegative) #t)
  (assert-equal (in? -5 negative) #t)
  (assert-equal (in? 1.5 (interval 1 2)) #t)
  (assert-equal (in? 3 (interval '-inf 'inf)) #t)
  (assert-equal (in? (sqrt 2) (interval 1 2)) #t)
  (assert-equal (in? 5 (interval 1 2)) #f))

(deftest "subset? для интервалов"
  (assert-equal (subset? (interval 1 2) (interval 0 3)) #t)
  (assert-equal (subset? (interval 0 1 'open 'open) (interval 0 1)) #t)
  (assert-equal (subset? (interval 0 1) (interval 0 1 'open 'open)) #f)
  (assert-equal (subset? positive nonnegative) #t)
  (assert-equal (subset? nonnegative positive) #f)
  (assert-equal (subset? (interval 0 5) (interval 1 6)) #f)
  (assert-equal (subset? (interval 3 2) positive) #t))       ; пустой — подмножество всего

(deftest "subset? между интервалами и доменами"
  (assert-equal (subset? (interval 0 1) reals) #t)
  (assert-equal (subset? (interval 0 1) complexes) #t)
  (assert-equal (subset? (interval 0 1) rationals) #f)        ; содержит иррациональные
  (assert-equal (subset? (interval 2 2) integers) #t)         ; вырожденный интервал {2}
  (assert-equal (subset? (interval 1/2 1/2) integers) #f)
  (assert-equal (subset? naturals nonnegative) #t)
  (assert-equal (subset? naturals (interval -1/2 'inf)) #t)
  (assert-equal (subset? integers nonnegative) #f)
  (assert-equal (subset? integers (interval '-inf 'inf)) #t)
  (assert-equal (subset? complexes (interval '-inf 'inf)) #f)
  (assert-equal (subset? naturals (set 1 2)) #f))

(deftest "пересечение интервалов"
  (assert-equal (intersection (interval 0 2) (interval 1 3)) (interval 1 2))
  (assert-equal (intersection (interval 0 1 'open 'open) (interval 1 2)) (interval 1 0))   ; пусто
  (assert-equal (intersection (interval 0 1) (interval 1 2)) (interval 1 1))
  (assert-equal (intersection positive negative) (interval 1 0))
  (assert-equal (intersection positive nonnegative) positive)
  (assert-equal (intersection (interval 0 5) (interval 1 'inf 'open 'open)) (interval 1 5 'open 'closed))
  (assert-equal (intersection (interval 0 5) reals) (interval 0 5))
  (assert-equal (intersection naturals integers) naturals)
  (assert-equal (equal? (interval 1 0) (interval 5 2)) #t))   ; все пустые интервалы равны

(deftest "disjoint?: интервалы с числовыми границами"
  (assert-equal (disjoint? (interval 0 1) (interval 2 3)) #t)
  (assert-equal (disjoint? (interval 0 1) (interval 1 2)) #f)
  (assert-equal (disjoint? (interval 0 1 'open 'open) (interval 1 2)) #t)
  (assert-equal (disjoint? positive negative) #t)
  (assert-equal (disjoint? positive (interval -1 'inf)) #f))

(deftest "disjoint?: домены и интервалы"
  (assert-equal (disjoint? integers (interval 1/3 2/3)) #t)   ; между 1/3 и 2/3 нет целых
  (assert-equal (disjoint? integers (interval 0 1)) #f)
  (assert-equal (disjoint? naturals negative) #t)
  (assert-equal (disjoint? naturals (interval -3 -1/2)) #t)
  (assert-equal (disjoint? naturals (interval -1/2 1/2)) #f)   ; 0 ∈ ℕ
  (assert-equal (disjoint? reals positive) #f)
  (assert-equal (disjoint? rationals (interval 2 2)) #f)
  (assert-equal (disjoint? rationals (interval 1/3 1/3 'open 'closed)) #t)   ; пустой интервал
  (assert-equal (disjoint? complexes positive) #f)
  (assert-equal (disjoint? integers naturals) #f)
  (assert-error (disjoint? 1 2)))

(deftest "конструктор интервала: ошибки"
  (assert-error (interval 'a 1))
  (assert-error (interval 0 1 'open))
  (assert-error (interval 0 1 'foo 'bar))
  (assert-error (interval (+ 'x 1) 2)))

; --- Декларации ---

(deftest "declare / declarations / undeclare"
  (assert-equal (declarations 'dt-x) '())
  (declare 'dt-x integers)
  (assert-equal (declarations 'dt-x) (list integers))
  (declare 'dt-x positive integers)             ; добавляет; дубли не повторяются
  (assert-equal (declarations 'dt-x) (list integers positive))
  (undeclare 'dt-x)
  (assert-equal (declarations 'dt-x) '()))

(deftest "declare: ошибки в аргументах"
  (assert-error (declare 5 integers))
  (assert-error (declare 'dt-y 5))
  (assert-equal (declarations 'dt-y) '()))

(deftest "assuming: временные декларации, значение тела"
  (assert-equal (declarations 'dt-a) '())
  (assert-equal (assuming ((dt-a integers)) (declarations 'dt-a)) (list integers))
  (assert-equal (declarations 'dt-a) '())          ; восстановлено
  (assert-equal (assuming ((dt-a integers) (dt-b reals positive)) (list (in? 'dt-a reals) (sign-of 'dt-b)))
                '(#t positive)))

(deftest "assuming не протекает: вложенность и повторное вхождение"
  (assuming ((dt-a integers))
    (assert-equal (declarations 'dt-a) (list integers))
    (assuming ((dt-a positive))
      (assert-equal (declarations 'dt-a) (list integers positive)))
    (assert-equal (declarations 'dt-a) (list integers)))   ; внутренний блок снят
  (assert-equal (declarations 'dt-a) '()))

(deftest "assuming не протекает после ошибки внутри блока"
  (assert-equal (try (assuming ((dt-a integers)) (error "сбой")) (lambda (e) 'caught)) 'caught)
  (assert-equal (declarations 'dt-a) '())
  ; ошибка во внутреннем блоке: внешний продолжает с прежними декларациями
  (assuming ((dt-a integers))
    (try (assuming ((dt-a positive)) (error "сбой")) (lambda (e) 'ok))
    (assert-equal (declarations 'dt-a) (list integers)))
  (assert-equal (declarations 'dt-a) '()))

(deftest "assuming: неверная декларация — ошибка, ничего не остаётся"
  (assert-error (assuming ((dt-a integers) (dt-b 5)) 1))
  (assert-equal (declarations 'dt-a) '())
  (assert-equal (declarations 'dt-b) '()))

(deftest "assuming: декларации ранее объявленного символа восстанавливаются"
  (declare 'dt-c reals)
  (assuming ((dt-c positive)) (assert-equal (declarations 'dt-c) (list reals positive)))
  (assert-equal (declarations 'dt-c) (list reals))
  (undeclare 'dt-c))

; --- Принадлежность символов и выражений ---

(deftest "символ: необъявленный — ℂ, остальное unknown"
  (assert-equal (in? 'dt-u complexes) #t)
  (assert-equal (in? 'dt-u reals) unknown)
  (assert-equal (in? 'dt-u integers) unknown)
  (assert-equal (in? 'dt-u positive) unknown))

(deftest "символ: вывод по декларациям (#t / #f / unknown)"
  (assuming ((dt-x integers))
    (assert-equal (in? 'dt-x integers) #t)
    (assert-equal (in? 'dt-x rationals) #t)
    (assert-equal (in? 'dt-x reals) #t)
    (assert-equal (in? 'dt-x complexes) #t)
    (assert-equal (in? 'dt-x naturals) unknown)
    (assert-equal (in? 'dt-x (interval 1/3 2/3)) #f)     ; между 1/3 и 2/3 целых нет
    (assert-equal (in? 'dt-x (interval 0 10)) unknown)))

(deftest "символ: натуральный и интервальные декларации"
  (assuming ((dt-n naturals))
    (assert-equal (in? 'dt-n nonnegative) #t)
    (assert-equal (in? 'dt-n negative) #f)
    (assert-equal (in? 'dt-n positive) unknown)
    (assert-equal (in? 'dt-n integers) #t))
  (assuming ((dt-r (interval 0 1)))
    (assert-equal (in? 'dt-r reals) #t)
    (assert-equal (in? 'dt-r rationals) unknown)
    (assert-equal (in? 'dt-r (interval -1 2)) #t)
    (assert-equal (in? 'dt-r (interval 2 3)) #f)
    (assert-equal (in? 'dt-r (interval 1/2 3)) unknown)))

(deftest "символ: несколько деклараций — пересечение"
  (assuming ((dt-p integers positive))
    (assert-equal (in? 'dt-p naturals) #t)              ; целое и > 0
    (assert-equal (in? 'dt-p negative) #f)
    (assert-equal (sign-of 'dt-p) 'positive)))

(deftest "сумма и произведение: замкнутость"
  (assert-equal (in? '(+ dt-x dt-y) integers) unknown)    ; без деклараций
  (assuming ((dt-x integers) (dt-y integers))
    (assert-equal (in? '(+ dt-x dt-y) integers) #t)
    (assert-equal (in? '(* 2 dt-x dt-y) integers) #t)
    (assert-equal (in? '(* dt-x 1/2) integers) unknown)
    (assert-equal (in? '(* dt-x 1/2) rationals) #t)
    (assert-equal (in? '(- dt-x dt-y) integers) #t))       ; не упрощённая запись тоже понимается
  (assuming ((dt-x naturals) (dt-y naturals))
    (assert-equal (in? '(+ dt-x dt-y 1) naturals) #t)
    (assert-equal (in? '(* -1 dt-x) naturals) unknown)    ; ℕ не замкнут по коэффициенту -1
    (assert-equal (in? '(* -1 dt-x) integers) #t)))

(deftest "степень: целая, отрицательная, дробная"
  (assuming ((dt-x integers))
    (assert-equal (in? '(^ dt-x 3) integers) #t)
    (assert-equal (in? '(^ dt-x -1) integers) unknown)    ; 1/x — не целое
    (assert-equal (in? '(^ dt-x -1) rationals) #t))       ; допущение: x != 0
  (assuming ((dt-x positive))
    (assert-equal (in? '(^ dt-x 1/2) reals) #t))
  (assert-equal (in? '(^ dt-x 1/2) reals) unknown)
  (assuming ((dt-x reals))
    (assert-equal (in? '(^ dt-x 1/2) reals) unknown)))    ; корень из отрицательного — не вещественный

(deftest "функции: sin cos exp atan log sqrt abs"
  (assuming ((dt-x reals))
    (assert-equal (in? '(sin dt-x) reals) #t)
    (assert-equal (in? '(cos dt-x) reals) #t)
    (assert-equal (in? '(exp dt-x) reals) #t)
    (assert-equal (in? '(atan dt-x) reals) #t)
    (assert-equal (in? '(log dt-x) reals) unknown)
    (assert-equal (in? '(sqrt dt-x) reals) unknown))
  (assert-equal (in? '(sin dt-x) reals) unknown)
  (assuming ((dt-x positive))
    (assert-equal (in? '(log dt-x) reals) #t)
    (assert-equal (in? '(sqrt dt-x) reals) #t))
  (assuming ((dt-x nonnegative))
    (assert-equal (in? '(sqrt dt-x) reals) #t)
    (assert-equal (in? '(log dt-x) reals) unknown))      ; log 0 не определён
  (assert-equal (in? '(abs dt-x) reals) #t)               ; |u| вещественно при любом u
  (assuming ((dt-x integers))
    (assert-equal (in? '(abs dt-x) naturals) #t)))

(deftest "прочее: unknown, а для complexes — #t"
  (assert-equal (in? '(foo dt-x) reals) unknown)
  (assert-equal (in? '(foo dt-x) complexes) #t)
  (assert-equal (in? '(+ dt-x (foo dt-y)) complexes) #t))

(deftest "выражение в интервале: через знак"
  (assuming ((dt-x reals))
    (assert-equal (in? '(^ dt-x 2) nonnegative) #t)
    (assert-equal (in? '(^ dt-x 2) negative) #f)
    (assert-equal (in? '(^ dt-x 2) positive) unknown))
  (assert-equal (in? '(^ dt-x 2) nonnegative) unknown)
  (assert-equal (in? '(exp dt-x) positive) unknown))

(deftest "pi — положительное вещественное"
  (assert-equal (in? 'pi reals) #t)
  (assert-equal (sign-of 'pi) 'positive)
  (assert-equal (sign-of '(* 2 pi)) 'positive))

; --- Знак ---

(deftest "sign-of: числа и символы"
  (assert-equal (sign-of 5) 'positive)
  (assert-equal (sign-of -1/2) 'negative)
  (assert-equal (sign-of 0) 'zero)
  (assert-equal (sign-of 2.5) 'positive)
  (assert-equal (sign-of (sqrt 2)) 'positive)
  (assert-equal (sign-of 'dt-s) 'unknown)
  (assuming ((dt-s positive)) (assert-equal (sign-of 'dt-s) 'positive))
  (assuming ((dt-s negative)) (assert-equal (sign-of 'dt-s) 'negative))
  (assuming ((dt-s naturals)) (assert-equal (sign-of 'dt-s) 'nonnegative))
  (assuming ((dt-s nonpositive)) (assert-equal (sign-of 'dt-s) 'nonpositive))
  (assuming ((dt-s (interval 0 0))) (assert-equal (sign-of 'dt-s) 'zero))
  (assuming ((dt-s (interval -1 1))) (assert-equal (sign-of 'dt-s) 'unknown))
  (assuming ((dt-s integers)) (assert-equal (sign-of 'dt-s) 'unknown)))

(deftest "sign-of: сумма"
  (assuming ((dt-x positive) (dt-y positive) (dt-z nonnegative) (dt-w negative))
    (assert-equal (sign-of '(+ dt-x dt-y)) 'positive)
    (assert-equal (sign-of '(+ dt-x dt-z)) 'positive)
    (assert-equal (sign-of '(+ dt-z dt-z)) 'nonnegative)
    (assert-equal (sign-of '(+ dt-w dt-w)) 'negative)
    (assert-equal (sign-of '(+ dt-x dt-w)) 'unknown)
    (assert-equal (sign-of '(+ dt-x dt-u)) 'unknown)))     ; dt-u не объявлен

(deftest "sign-of: произведение по правилу знаков"
  (assuming ((dt-x positive) (dt-y negative) (dt-z nonnegative))
    (assert-equal (sign-of '(* dt-x dt-x)) 'positive)
    (assert-equal (sign-of '(* dt-x dt-y)) 'negative)
    (assert-equal (sign-of '(* dt-y dt-y)) 'positive)
    (assert-equal (sign-of '(* -1 dt-x)) 'negative)
    (assert-equal (sign-of '(* dt-x dt-z)) 'nonnegative)
    (assert-equal (sign-of '(* dt-y dt-z)) 'nonpositive)
    (assert-equal (sign-of '(* dt-x dt-u)) 'unknown)))

(deftest "sign-of: степень"
  (assert-equal (sign-of '(^ dt-x 2)) 'unknown)            ; x может быть комплексным
  (assuming ((dt-x reals))
    (assert-equal (sign-of '(^ dt-x 2)) 'nonnegative)
    (assert-equal (sign-of '(^ dt-x 4)) 'nonnegative)
    (assert-equal (sign-of '(^ dt-x 3)) 'unknown))
  (assuming ((dt-x positive))
    (assert-equal (sign-of '(^ dt-x 2)) 'positive)
    (assert-equal (sign-of '(^ dt-x 3)) 'positive)
    (assert-equal (sign-of '(^ dt-x -1)) 'positive)
    (assert-equal (sign-of '(^ dt-x 1/2)) 'positive))
  (assuming ((dt-x negative))
    (assert-equal (sign-of '(^ dt-x 3)) 'negative)
    (assert-equal (sign-of '(^ dt-x 2)) 'positive)
    (assert-equal (sign-of '(^ dt-x 1/2)) 'unknown)))

(deftest "sign-of: exp, abs, sqrt"
  (assuming ((dt-x reals))
    (assert-equal (sign-of '(exp dt-x)) 'positive))
  (assert-equal (sign-of '(exp dt-x)) 'unknown)
  (assert-equal (sign-of '(abs dt-x)) 'nonnegative)
  (assuming ((dt-x positive))
    (assert-equal (sign-of '(abs dt-x)) 'positive)
    (assert-equal (sign-of '(sqrt dt-x)) 'positive))
  (assuming ((dt-x nonnegative))
    (assert-equal (sign-of '(sqrt dt-x)) 'nonnegative))
  (assert-equal (sign-of '(sqrt dt-x)) 'unknown)
  (assert-equal (sign-of '(foo dt-x)) 'unknown))

(deftest "предикаты positive? nonnegative? negative? nonpositive? (трёхзначные)"
  (assert-equal (positive? 3) #t)
  (assert-equal (positive? -3) #f)
  (assert-equal (positive? 0) #f)
  (assert-equal (positive? 'dt-u) unknown)
  (assert-equal (nonnegative? 0) #t)
  (assert-equal (nonnegative? -1) #f)
  (assert-equal (negative? -1) #t)
  (assert-equal (negative? 1) #f)
  (assert-equal (nonpositive? 0) #t)
  (assert-equal (nonpositive? 1) #f)
  (assuming ((dt-n naturals))
    (assert-equal (nonnegative? 'dt-n) #t)
    (assert-equal (positive? 'dt-n) unknown)     ; ноль возможен
    (assert-equal (negative? 'dt-n) #f)))

(deftest "предикаты real? и integer-valued?"
  (assert-equal (real? 2) #t)
  (assert-equal (real? 'dt-u) unknown)
  (assert-equal (integer-valued? 3) #t)
  (assert-equal (integer-valued? 1/2) #f)
  (assert-equal (integer-valued? 'dt-u) unknown)
  (assuming ((dt-k integers))
    (assert-equal (integer-valued? 'dt-k) #t)
    (assert-equal (real? '(* 2 dt-k)) #t)
    (assert-equal (integer-valued? '(+ dt-k 1)) #t))
  (assert-equal (if (true? (real? 'dt-u)) 'yes 'no) 'no))
