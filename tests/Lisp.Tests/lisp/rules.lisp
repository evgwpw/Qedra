; Lisp-тесты условных правил упрощения (lib\rules.lisp), Шаг 16.
; Без деклараций (unknown) правила не срабатывают — выражение остаётся как было.

; --- abs ---

(deftest "abs: числа сворачиваются"
  (assert-equal (simplify '(abs -3)) 3)
  (assert-equal (simplify '(abs 5)) 5)
  (assert-equal (simplify '(abs 0)) 0)
  (assert-equal (simplify '(abs -1/2)) 1/2)
  (assert-equal (simplify '(abs 2.5)) 2.5)
  (assert-equal (simplify '(+ 1 (abs -3))) 4))

(deftest "abs без деклараций не меняется"
  (assert-equal (simplify '(abs x)) '(abs x))
  (assert-equal (simplify '(abs (+ x 1))) '(abs (+ 1 x))))

(deftest "abs: неотрицательный и неположительный аргумент"
  (assert-equal (assuming ((rl-x nonnegative)) (simplify '(abs rl-x))) 'rl-x)
  (assert-equal (assuming ((rl-x positive)) (simplify '(abs rl-x))) 'rl-x)
  (assert-equal (assuming ((rl-x naturals)) (simplify '(abs rl-x))) 'rl-x)
  (assert-equal (assuming ((rl-x negative)) (simplify '(abs rl-x))) '(* -1 rl-x))
  (assert-equal (assuming ((rl-x nonpositive)) (simplify '(abs rl-x))) '(* -1 rl-x))
  ; вещественный без знака — abs остаётся
  (assert-equal (assuming ((rl-x reals)) (simplify '(abs rl-x))) '(abs rl-x))
  ; после блока декларации сняты
  (assert-equal (simplify '(abs rl-x)) '(abs rl-x)))

(deftest "abs: составной аргумент"
  (assert-equal (assuming ((rl-x positive) (rl-y positive)) (simplify '(abs (+ rl-x rl-y)))) '(+ rl-x rl-y))
  (assert-equal (assuming ((rl-x positive) (rl-y negative)) (simplify '(abs (* rl-x rl-y)))) '(* -1 rl-x rl-y))
  (assert-equal (assuming ((rl-x positive)) (simplify '(abs (+ rl-x rl-y)))) '(abs (+ rl-x rl-y))))

(deftest "abs от abs — безусловно"
  (assert-equal (simplify '(abs (abs x))) '(abs x))
  (assert-equal (simplify '(abs (abs (abs x)))) '(abs x)))

(deftest "abs от квадрата — при вещественном x"
  (assert-equal (simplify '(abs (^ x 2))) '(abs (^ x 2)))
  (assert-equal (assuming ((rl-x reals)) (simplify '(abs (^ rl-x 2)))) '(^ rl-x 2))
  (assert-equal (assuming ((rl-x integers)) (simplify '(abs (^ rl-x 2)))) '(^ rl-x 2)))

; --- sqrt(x^2) ---

(deftest "sqrt(x^2) без деклараций остаётся (обе формы)"
  (assert-equal (simplify '(sqrt (^ x 2))) '(sqrt (^ x 2)))
  (assert-equal (simplify '(^ (^ x 2) 1/2)) '(^ (^ x 2) 1/2)))

(deftest "sqrt(x^2): вещественный x → abs, неотрицательный → x"
  (assert-equal (assuming ((rl-x reals)) (simplify '(^ (^ rl-x 2) 1/2))) '(abs rl-x))
  (assert-equal (assuming ((rl-x reals)) (simplify '(sqrt (^ rl-x 2)))) '(abs rl-x))
  (assert-equal (assuming ((rl-x nonnegative)) (simplify '(^ (^ rl-x 2) 1/2))) 'rl-x)
  (assert-equal (assuming ((rl-x nonnegative)) (simplify '(sqrt (^ rl-x 2)))) 'rl-x)
  (assert-equal (assuming ((rl-x naturals)) (simplify '(sqrt (^ rl-x 2)))) 'rl-x)
  ; отрицательный: |x| → -x
  (assert-equal (assuming ((rl-x negative)) (simplify '(sqrt (^ rl-x 2)))) '(* -1 rl-x))
  ; комплексный (по умолчанию) — не трогаем
  (assert-equal (assuming ((rl-x complexes)) (simplify '(sqrt (^ rl-x 2)))) '(sqrt (^ rl-x 2))))

; --- степени ---

(deftest "(x^a)^b при x >= 0 и нецелом b"
  (assert-equal (assuming ((rl-x nonnegative)) (simplify '(^ (^ rl-x 4) 1/2))) '(^ rl-x 2))
  (assert-equal (assuming ((rl-x nonnegative) (rl-a reals)) (simplify '(^ (^ rl-x rl-a) 1/3)))
                '(^ rl-x (* 1/3 rl-a)))
  (assert-equal (assuming ((rl-x positive)) (simplify '(^ (^ rl-x 2) 1/3))) '(^ rl-x 2/3)))

(deftest "(x^a)^b: без деклараций, при неизвестном знаке и при неизвестном a — не меняется"
  (assert-equal (simplify '(^ (^ x 4) 1/2)) '(^ (^ x 4) 1/2))
  (assert-equal (assuming ((rl-x reals)) (simplify '(^ (^ rl-x 4) 1/2))) '(^ (^ rl-x 4) 1/2))
  (assert-equal (assuming ((rl-x nonnegative)) (simplify '(^ (^ rl-x rl-a) 1/2))) '(^ (^ rl-x rl-a) 1/2)))

(deftest "(x^a)^n для целого n сворачивается самим Simplify"
  (assert-equal (simplify '(^ (^ x 2) 3)) '(^ x 6)))

(deftest "(a b)^c при a, b >= 0 и нецелом c"
  (assert-equal (assuming ((rl-a nonnegative) (rl-b nonnegative)) (simplify '(^ (* rl-a rl-b) 1/2)))
                '(* (^ rl-a 1/2) (^ rl-b 1/2)))
  (assert-equal (assuming ((rl-x nonnegative)) (simplify '(^ (* 2 rl-x) 1/2)))
                '(* (^ 2 1/2) (^ rl-x 1/2))))

(deftest "(a b)^c: не меняется при неизвестном знаке одного из множителей или без деклараций"
  (assert-equal (simplify '(^ (* a b) 1/2)) '(^ (* a b) 1/2))
  (assert-equal (assuming ((rl-a nonnegative)) (simplify '(^ (* rl-a rl-b) 1/2))) '(^ (* rl-a rl-b) 1/2))
  (assert-equal (assuming ((rl-a nonnegative) (rl-b reals)) (simplify '(^ (* rl-a rl-b) 1/2)))
                '(^ (* rl-a rl-b) 1/2))
  ; целая степень — по правилу Simplify, без деклараций
  (assert-equal (simplify '(^ (* a b) 2)) '(* (^ a 2) (^ b 2))))

; --- log / exp ---

(deftest "exp(log x) → x безусловно"
  (assert-equal (simplify '(exp (log x))) 'x)
  (assert-equal (simplify '(exp (ln (+ x 1)))) '(+ 1 x)))

(deftest "log(exp x) → x при вещественном x"
  (assert-equal (simplify '(log (exp x))) '(log (exp x)))
  (assert-equal (assuming ((rl-x reals)) (simplify '(log (exp rl-x)))) 'rl-x)
  (assert-equal (assuming ((rl-x positive)) (simplify '(log (exp rl-x)))) 'rl-x)
  (assert-equal (assuming ((rl-x complexes)) (simplify '(log (exp rl-x)))) '(log (exp rl-x)))
  (assert-equal (simplify '(log (exp 2))) 2))

; --- sin / cos кратных pi ---

(deftest "sin pi, cos pi"
  (assert-equal (simplify '(sin pi)) 0)
  (assert-equal (simplify '(cos pi)) -1))

(deftest "sin/cos от числового кратного pi"
  (assert-equal (simplify '(sin (* 2 pi))) 0)
  (assert-equal (simplify '(sin (* -1 pi))) 0)
  (assert-equal (simplify '(cos (* 2 pi))) 1)
  (assert-equal (simplify '(cos (* 3 pi))) -1)
  (assert-equal (simplify '(cos (* -1 pi))) -1)
  (assert-equal (simplify '(+ 1 (sin (* 5 pi)))) 1))

(deftest "sin/cos (n pi) без деклараций не меняются; нецелые — тоже"
  (assert-equal (simplify '(sin (* n pi))) '(sin (* n pi)))
  (assert-equal (simplify '(cos (* n pi))) '(cos (* n pi)))
  ; Шаг 21c: кратные pi со знаменателем 1, 2, 3, 4, 6 — точные значения; прочие — без изменений
  (assert-equal (simplify '(sin (* 1/2 pi))) 1)
  (assert-equal (simplify '(cos (* 1/3 pi))) 1/2)
  (assert-equal (simplify '(sin (* 1/5 pi))) '(sin (* 1/5 pi)))
  (assert-equal (simplify '(cos (* 2/7 pi))) '(cos (* 2/7 pi)))
  (assert-equal (assuming ((rl-n reals)) (simplify '(sin (* rl-n pi)))) '(sin (* pi rl-n)))
  (assert-equal (simplify '(sin (* 2 x))) '(sin (* 2 x)))
  (assert-equal (simplify '(sin x)) '(sin x)))

(deftest "sin/cos (n pi) при целом n"
  (assert-equal (assuming ((rl-n integers)) (simplify '(sin (* rl-n pi)))) 0)
  (assert-equal (assuming ((rl-n integers)) (simplify '(cos (* rl-n pi)))) '(^ -1 rl-n))
  (assert-equal (assuming ((rl-n naturals)) (simplify '(cos (* rl-n pi)))) '(^ -1 rl-n))
  ; символ, стоящий в каноническом порядке после pi: (* pi z)
  (assert-equal (assuming ((rl-z integers)) (simplify '(sin (* rl-z pi)))) 0)
  (assert-equal (assuming ((rl-z integers)) (simplify '(cos (* rl-z pi)))) '(^ -1 rl-z))
  (assert-equal (assuming ((rl-n integers)) (simplify '(+ 1 (sin (* rl-n pi))))) 1))

; --- управление правилами ---

(deftest "rules: имена правил оператора"
  (assert-equal (rules 'abs) '(abs-nonnegative abs-nonpositive abs-abs abs-square))
  (assert-equal (rules 'sin) '(sin-integer-pi))      ; Шаг 21c: sin-pi, cos-pi перенесены в ядро
  (assert-equal (rules 'cos) '(cos-even-multiple-pi cos-integer-pi))    ; Шаг AC.3: три правила пар -> :ac
  (assert-equal (rules '+) '(pythagorean-common-factor))
  (assert-equal (rules 'no-such-operator) '()))

; --- Шаг AC.3: правила :ac и переведённые правила ---

(deftest "AC.3: sin/cos кратных pi — три и более множителей, любой порядок"
  (assert-equal (assuming ((rl-n integers)) (simplify '(sin (* 2 rl-n pi)))) 0)
  (assert-equal (assuming ((rl-n integers) (rl-m integers)) (simplify '(sin (* rl-m rl-n pi)))) 0)
  (assert-equal (assuming ((rl-n integers)) (simplify '(sin (* pi 3 rl-n)))) 0)
  (assert-equal (assuming ((rl-n integers) (rl-m integers)) (simplify '(cos (* rl-m rl-n pi)))) '(^ -1 (* rl-m rl-n)))
  (assert-equal (assuming ((rl-n integers)) (simplify '(cos (* 2 rl-n pi)))) 1)
  (assert-equal (assuming ((rl-n integers)) (simplify '(cos (* 3 rl-n pi)))) '(^ -1 (* 3 rl-n)))
  ; нецелый или неизвестный остаток — без изменений
  (assert-equal (assuming ((rl-n integers)) (simplify '(sin (* 1/2 rl-n pi)))) '(sin (* 1/2 pi rl-n)))
  (assert-equal (simplify '(sin (* 2 rl-n pi))) '(sin (* 2 pi rl-n)))
  (assert-equal (assuming ((rl-n integers)) (simplify '(sin (* rl-n rl-q pi)))) '(sin (* pi rl-n rl-q))))

(deftest "AC.3: pow-product — три и более множителей, условие на каждой паре"
  (assert-equal (assuming ((rl-x positive) (rl-y positive) (rl-z positive)) (simplify '(^ (* rl-x rl-y rl-z) 1/2)))
                '(* (^ rl-x 1/2) (^ rl-y 1/2) (^ rl-z 1/2)))
  ; двое неотрицательных — их можно вынести, остаток под корнем остаётся
  (assert-equal (assuming ((rl-x positive) (rl-y positive)) (simplify '(^ (* rl-x rl-y rl-w) 1/2)))
                '(* (^ rl-w 1/2) (^ rl-x 1/2) (^ rl-y 1/2)))
  ; без деклараций и при целой степени — как раньше
  (assert-equal (simplify '(^ (* rl-x rl-y rl-z) 1/2)) '(^ (* rl-x rl-y rl-z) 1/2))
  (assert-equal (simplify '(^ (* a b c) 2)) '(* (^ a 2) (^ b 2) (^ c 2)))
  (assert-equal (assuming ((rl-x positive) (rl-y positive)) (simplify '(^ (* rl-x rl-y) 1/2)))
                '(* (^ rl-x 1/2) (^ rl-y 1/2))))

(deftest "AC.3: sin^2 + cos^2 с общим множителем в сумме"
  (assert-equal (simplify '(+ (* z (^ (sin x) 2)) (* z (^ (cos x) 2)) y)) '(+ y z))
  (assert-equal (simplify '(+ 3 (* z w (^ (sin x) 2)) (* w z (^ (cos x) 2)) y)) '(+ 3 y (* w z)))
  (assert-equal (simplify '(+ (* -1 z (^ (sin x) 2)) (* -1 z (^ (cos x) 2)) y)) '(+ y (* -1 z)))
  ; числовой коэффициент и пример проекта — pythag упрощателя, правило не мешает (нет двойного срабатывания)
  (assert-equal (simplify '(+ 3 (* 2 (^ (sin x) 2)) (* 2 (^ (cos x) 2)) y)) '(+ 5 y))
  (assert-equal (simplify '(+ (^ (sin x) 2) (^ (cos x) 2))) 1)
  ; разные аргументы и разные множители — не сворачивается
  (assert-equal (simplify '(+ (* z (^ (sin x) 2)) (* w (^ (cos x) 2)))) '(+ (* w (^ (cos x) 2)) (* z (^ (sin x) 2))))
  (assert-equal (simplify '(+ (^ (sin x) 2) (^ (cos y) 2))) '(+ (^ (cos y) 2) (^ (sin x) 2))))

(deftest "AC.3: defrule :ac — перестановки, >= 3 множителей, остаток ?r..."
  (defrule rl-ac-sum (rl-g (+ (^ ?y 2) (sin ?x) ?r...)) (rl-h ?x ?y (+ ?r...)) :ac)
  (defrule rl-ac-prod (rl-k (* 2 ?x (cos ?y) ?r...)) (rl-h2 ?x ?y ?r...) :ac)
  (unwind-protect
    (begin
      (assert-equal (simplify '(rl-g (+ (sin a) (^ b 2)))) '(rl-h a b 0))
      (assert-equal (simplify '(rl-g (+ (^ b 2) 7 (sin a)))) '(rl-h a b 7))
      (assert-equal (simplify '(rl-g (+ c (^ b 2) 7 (sin a)))) '(rl-h a b (+ 7 c)))
      (assert-equal (simplify '(rl-g (+ (sin a) 7))) '(rl-g (+ 7 (sin a))))
      (assert-equal (simplify '(rl-k (* 2 p (cos q)))) '(rl-h2 p q 1))
      (assert-equal (simplify '(rl-k (* (cos q) m 2 p))) '(rl-h2 m q p))
      (assert-equal (simplify '(rl-k (* 3 p (cos q)))) '(rl-k (* 3 p (cos q))))
      (assert-equal (rules 'rl-g) '(rl-ac-sum)))
    (begin (remove-rule 'rl-ac-sum) (remove-rule 'rl-ac-prod))))

(deftest "AC.3: defrule :ac — условие проверяется на каждом кандидате"
  (defrule rl-ac-cond (rl-g3 (+ ?x ?y)) (rl-h3 ?x ?y) (integer-valued? ?x) :ac)
  (defrule rl-ac-cond2 (rl-g4 (* ?x ?r...)) (rl-h4 ?x) (and3 (integer-valued? ?x) (nonnegative? ?x)) :ac)
  (unwind-protect
    (begin
      ; без деклараций: условие unknown — правило не срабатывает
      (assert-equal (simplify '(rl-g3 (+ rl-p rl-q))) '(rl-g3 (+ rl-p rl-q)))
      ; rl-p целое, rl-q неизвестно: первый кандидат (x = rl-p или rl-q) в порядке выражения — подходит тот, где условие #t
      (assert-equal (assuming ((rl-p integers)) (simplify '(rl-g3 (+ rl-p rl-q)))) '(rl-h3 rl-p rl-q))
      (assert-equal (assuming ((rl-q integers)) (simplify '(rl-g3 (+ rl-p rl-q)))) '(rl-h3 rl-q rl-p))
      ; условие, не определённое на части кандидатов
      (assert-equal (assuming ((rl-p naturals) (rl-q reals)) (simplify '(rl-g4 (* rl-p rl-q)))) '(rl-h4 rl-p))
      (assert-equal (assuming ((rl-q naturals)) (simplify '(rl-g4 (* rl-p rl-q)))) '(rl-h4 rl-q))
      (assert-equal (assuming ((rl-p reals)) (simplify '(rl-g4 (* rl-p rl-q)))) '(rl-g4 (* rl-p rl-q))))
    (begin (remove-rule 'rl-ac-cond) (remove-rule 'rl-ac-cond2))))

(deftest "AC.3: defrule :ac — без :ac правило структурное, как раньше"
  (defrule rl-nonac (rl-g5 (+ ?x ?y)) (rl-h5 ?x ?y))
  (unwind-protect
    (begin
      (assert-equal (simplify '(rl-g5 (+ a b))) '(rl-h5 a b))
      (assert-equal (simplify '(rl-g5 (+ a b c))) '(rl-g5 (+ a b c))))
    (remove-rule 'rl-nonac))
  (defrule rl-ac-yes (rl-g5 (+ ?x ?y)) (rl-h5 ?x ?y) :ac)      ; и флаг без условия
  (unwind-protect
    (begin
      (assert-equal (simplify '(rl-g5 (+ a b))) '(rl-h5 a b))
      (assert-equal (simplify '(rl-g5 (+ a b c))) '(rl-g5 (+ a b c))))   ; без ?r... число аргументов должно совпасть
    (remove-rule 'rl-ac-yes)))

(deftest "AC.3: defrule :ac — защита от зацикливания и завершение"
  (defrule rl-ac-loop (rl-g6 (+ ?x ?r...)) (rl-g6 (+ ?r... ?x)) :ac)     ; всегда срабатывает: a -> a
  (defrule rl-ac-drop (rl-g7 (+ ?x ?y ?r...)) (rl-g7 (+ ?y ?r...)) :ac)  ; каждый раз короче — завершается
  (unwind-protect
    (begin
      (assert-error (simplify '(rl-g6 (+ a b c))))
      (assert-equal (length (rules 'rl-g6)) 1)
      (assert-equal (simplify '(rl-g7 (+ a b c))) '(rl-g7 c))
      ; после ошибки цепочка переписываний сброшена: обычные правила работают
      (assert-equal (assuming ((rl-n integers)) (simplify '(sin (* 2 rl-n pi)))) 0))
    (begin (remove-rule 'rl-ac-loop) (remove-rule 'rl-ac-drop))))

(deftest "AC.3: defrule :ac — ошибки синтаксиса"
  (assert-error (eval '(defrule rl-bad (rl-g8 ?x) ?x #t :ac :ac)))
  (assert-error (eval '(defrule rl-bad (rl-g8 ?x) ?x 1 2 :ac))))

(deftest "defrule из Lisp: условное правило с декларациями, remove-rule"
  (defrule rl-tmp-double (rl-double ?x) (* 2 ?x) (real? ?x))
  (unwind-protect
    (begin
      (assert-equal (simplify '(rl-double y)) '(rl-double y))
      (assert-equal (assuming ((y reals)) (simplify '(rl-double y))) '(* 2 y))
      (assert-equal (simplify '(rl-double 3)) 6)
      (assert-equal (remove-rule 'rl-tmp-double) #t)
      (assert-equal (simplify '(rl-double 3)) '(rl-double 3)))
    (remove-rule 'rl-tmp-double)))

(deftest "правила не меняют обычное упрощение"
  (assert-equal (simplify '(+ x x)) '(* 2 x))
  (assert-equal (simplify '(^ (* a b) 2)) '(* (^ a 2) (^ b 2)))
  (assert-equal (simplify '(sin x)) '(sin x))
  (assert-equal (simplify '(exp 0)) 1))
