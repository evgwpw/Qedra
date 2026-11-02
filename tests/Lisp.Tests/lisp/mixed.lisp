; Шаг R3.1: гладкие коники рода 0 и смешанный случай Риша — подстановка θ → t с переносом вердикта.
; Ответы проверяются дифференцированием (int-check); «неэлементарен» — условие risch-nonelementary ровно для формы ответа.

(define (mxt-ne? r)
  (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary)
                         (equal? (cadr (car c)) r)))
        (conditions)))

; ответ: без невычисленного интеграла и с производной, равной подынтегральному
(define (mxt-ans? f x)
  (let ((r (integrate f x)))
    (and (not (contains-sym? r 'integrate)) (int-check r f x))))

; доказанный отказ: невычисленная форма и условие risch-nonelementary для неё
(define (mxt-ne-int? f x)
  (conditions-clear)
  (let ((r (integrate f x)))
    (and (pair? r) (equal? (car r) 'integrate) (mxt-ne? r))))

(define (mxt-any-ne?)
  (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary))) (conditions)))

; ---------- род 0: гладкие коники ----------

(deftest "mixed: gn-conic? — бесквадратный deg P ∈ {1, 2} при q = 2"
  (assert-true (integrate::gn-conic? '(+ u 1) 2 'u))
  (assert-true (integrate::gn-conic? '(+ (^ u 2) u 1) 2 'u))
  (assert-equal #f (integrate::gn-conic? '(+ (^ u 3) 1) 2 'u))
  (assert-equal #f (integrate::gn-conic? '(+ u 1) 3 'u)))

(deftest "mixed: ∫√(u+1)/u и ∫du/((u−2)√(u+1)) — коника y² = u+1 (подстановка Эйлера)"
  (assert-true (mxt-ans? '(/ (sqrt (+ u 1)) u) 'u))
  (assert-true (mxt-ans? '(/ 1 (* (+ u -2) (sqrt (+ u 1)))) 'u)))

(deftest "mixed: ∫du/(u√(u²+u+1)) и ∫√(2u+3)/(u+1) — гладкие коники"
  (assert-true (mxt-ans? '(/ 1 (* u (sqrt (+ (^ u 2) u 1)))) 'u))
  (assert-true (mxt-ans? '(/ (sqrt (+ (* 2 u) 3)) (+ u 1)) 'u)))

; ---------- θ = eˣ, log x: x-free g — алгебраический случай в t ----------

(deftest "mixed: ∫√(eˣ+1), ∫1/√(eˣ+1), ∫√(eˣ−1) — подстановка t = eˣ"
  (assert-true (mxt-ans? '(sqrt (+ (exp x) 1)) 'x))
  (assert-true (mxt-ans? '(/ 1 (sqrt (+ (exp x) 1))) 'x))
  (assert-true (mxt-ans? '(sqrt (+ (exp x) -1)) 'x)))

(deftest "mixed: ∫eˣ/√(1+e²ˣ) = log(eˣ + √(1+e²ˣ)) — быстро (было 13–18 с)"
  (let ((r (integrate '(/ (exp x) (sqrt (+ 1 (exp (* 2 x))))) 'x)))
    (assert-equal r '(log (+ (^ (+ 1 (exp (* 2 x))) 1/2) (exp x))))
    (assert-true (int-check r '(/ (exp x) (sqrt (+ 1 (exp (* 2 x))))) 'x))))

(deftest "mixed: ∫dx/(x·log x·√(log x+2)) — θ = log x, константа √2 из внутреннего ответа"
  (assert-true (mxt-ans? '(/ 1 (* x (log x) (sqrt (+ (log x) 2)))) 'x)))

(deftest "mixed: sinh/cosh под радикалом — переписка в exp"
  (assert-true (mxt-ans? '(* (exp x) (sqrt (+ (exp x) 1)) (cosh x)) 'x)))

(deftest "mixed: перенос вердикта — eˣ/((eˣ−3)√(e³ˣ−2)) и 1/(x(log x−3)√(log³x−2)) неэлементарны (A5 в t)"
  (assert-true (mxt-ne-int? '(/ (exp x) (* (+ (exp x) -3) (sqrt (+ (exp (* 3 x)) -2)))) 'x))
  (assert-true (mxt-ne-int? '(/ 1 (* x (+ (log x) -3) (sqrt (+ (^ (log x) 3) -2)))) 'x)))

(deftest "mixed: перенос вердикта — eˣ/((eˣ−2)√(e³ˣ+1)) (остаток 1-го рода) и e⁻ˣ/√(e³ˣ+1) (Чебышёв)"
  (assert-true (mxt-ne-int? '(/ (exp x) (* (+ (exp x) -2) (sqrt (+ (exp (* 3 x)) 1)))) 'x))
  (assert-true (mxt-ne-int? '(/ 1 (* (exp x) (sqrt (+ (exp (* 3 x)) 1)))) 'x)))

(deftest "mixed: e^{x+1} — постоянный множитель e выносится, вердикт переносится"
  (assert-true (mxt-ne-int? '(/ 1 (* (exp (+ x 1)) (sqrt (+ (exp (* 3 x)) 1)))) 'x)))

; ---------- θ = x^{1/n}: Риш по t ----------

(deftest "mixed: ∫e^{√x} = 2(√x−1)e^{√x}; ∫√x·e^{√x}; ∫eˣ/√x — неэлементарен"
  (assert-true (mxt-ans? '(exp (sqrt x)) 'x))
  (assert-true (mxt-ans? '(* (sqrt x) (exp (sqrt x))) 'x))
  (assert-true (mxt-ne-int? '(/ (exp x) (sqrt x)) 'x)))

; ---------- честные отказы и подделки ----------

(deftest "mixed: √(eˣ+x), x·eˣ√(e³ˣ+1) (род 1, x остаётся), e^{√2x} — int-mixed не отвечает и вердикта не пишет"
  (conditions-clear)
  (assert-equal #f (integrate::int-mixed (integrate::int-norm '(* x (exp x) (sqrt (+ (exp (* 3 x)) 1)))) 'x 0))
  (assert-equal #f (integrate::int-mixed (integrate::int-norm '(sqrt (+ (exp x) x))) 'x 0))
  (assert-equal #f (integrate::int-mixed (integrate::int-norm '(* (sqrt (+ (exp x) 1)) (exp (* (sqrt 2) x)))) 'x 0))
  (assert-true (not (mxt-any-ne?))))

(deftest "mixed: план — θ и обратная функция; e^{bᵢ} — множитель, символьный параметр — отказ"
  (let ((p (integrate::mx-plan '(sqrt (+ 1 (exp (* 2 x)))) 'x)))
    (assert-equal (car p) 'theta)
    (assert-equal (cadr (caddr p)) '(exp (* 2 x))))
  (assert-equal (caddr (caddr (integrate::mx-plan '(* (exp x) (sqrt (+ 1 (exp (* 2 x))))) 'x)))
                '(log %t))
  (assert-equal #f (integrate::mx-plan '(sqrt (+ (exp x) a)) 'x)))

(define mxt-e '(* (^ (+ -3 (exp x)) -1) (^ (+ -2 (exp (* 3 x))) -1/2) (exp x)))
(define mxt-g '(* (^ (+ -3 %t) -1) (^ (+ -2 (^ %t 3)) -1/2)))
(define (mxt-proof)
  (cadr (capture-conditions (lambda () (integrate::int-go (subst '(%t x) mxt-g) 'x 0)))))

(deftest "mixed: чекер mx-transfer-ne! — честный перенос и подделки"
  (let ((cs (mxt-proof)))
    ; честно: x-free, константы ℚ, доказательство для g, отображение eˣ
    (assert-equal #t (car (capture-conditions
                           (lambda () (integrate::mx-transfer-ne! mxt-e 'x 1 mxt-g '%t '(exp x) 'alg 'x cs)))))
    (begin
      ; без внутреннего доказательства
      (assert-equal #f (car (capture-conditions
                             (lambda () (integrate::mx-transfer-ne! mxt-e 'x 1 mxt-g '%t '(exp x) 'alg 'x '())))))
      ; x спрятан в g (не x-free)
      (assert-equal #f (car (capture-conditions
                             (lambda () (integrate::mx-transfer-ne! mxt-e 'x 1 (list '* 'x mxt-g) '%t '(exp x) 'alg 'x cs)))))
      ; подменённая подстановка t = e^{2x}
      (assert-equal #f (car (capture-conditions
                             (lambda () (integrate::mx-transfer-ne! mxt-e 'x 1 mxt-g '%t '(exp (* 2 x)) 'alg 'x cs)))))
      ; постоянный множитель 0 и символьный параметр
      (assert-equal #f (car (capture-conditions
                             (lambda () (integrate::mx-transfer-ne! mxt-e 'x 0 mxt-g '%t '(exp x) 'alg 'x cs)))))
      (assert-equal #f (car (capture-conditions
                             (lambda () (integrate::mx-transfer-ne! mxt-e 'x 'a mxt-g '%t '(exp x) 'alg 'x cs))))))))

; ---------- R3.2: рационализация рода 0 и Риш по параметру ----------

(deftest "mixed R3.2: x·√(eˣ+1) и x/√(eˣ+1) неэлементарны (дилогарифм); производная x√(eˣ+1) даёт x√(eˣ+1)"
  (assert-true (mxt-ne-int? '(* x (sqrt (+ (exp x) 1))) 'x))
  (assert-true (mxt-ne-int? '(/ x (sqrt (+ (exp x) 1))) 'x))
  (let ((r (integrate (diff 'x '(* x (sqrt (+ (exp x) 1)))) 'x)))
    (assert-equal r '(* x (^ (+ 1 (exp x)) 1/2)))))

(deftest "mixed R3.2: log x/√(1+log x) неэлементарен (erfi); производная (log x)√(1+log x) — ответ"
  (assert-true (mxt-ne-int? '(/ (log x) (sqrt (+ 1 (log x)))) 'x))
  (assert-true (mxt-ans? (diff 'x '(* (log x) (sqrt (+ 1 (log x))))) 'x)))

(deftest "mixed R3.2: радикал от x под башней — eˣ√(x+1), eˣ/√(x+2) неэлементарны; производная eˣ√(x+1) — ответ"
  (assert-true (mxt-ne-int? '(* (exp x) (sqrt (+ x 1))) 'x))
  (assert-true (mxt-ne-int? '(/ (exp x) (sqrt (+ x 2))) 'x))
  (assert-equal (integrate (diff 'x '(* (exp x) (sqrt (+ x 1)))) 'x) '(* (^ (+ 1 x) 1/2) (exp x)))
  (assert-true (mxt-ans? (diff 'x '(/ (exp x) (sqrt (+ x 2)))) 'x)))

(deftest "mixed R3.2: ответы с логарифмом — x·eˣ/√(eˣ+1), (log x)√(x+1) (радикал от x, башня log)"
  (assert-true (mxt-ans? '(/ (* x (exp x)) (sqrt (+ (exp x) 1))) 'x))
  (assert-true (mxt-ans? '(* (log x) (sqrt (+ x 1))) 'x)))

(deftest "mixed R3.2: log(−1) — x√(1−eˣ), x/√(1−eˣ) неэлементарны; производная x√(1−eˣ) — ответ"
  (assert-true (mxt-ne-int? '(* x (sqrt (- 1 (exp x)))) 'x))
  (assert-true (mxt-ne-int? '(/ x (sqrt (- 1 (exp x)))) 'x))
  (assert-true (mxt-ans? (diff 'x '(* x (sqrt (- 1 (exp x))))) 'x)))

(deftest "mixed R3.2: разбор знака логарифмов — g = g0 + L·h"
  ; log(1−s²)/(s²−1) = log(s²−1)/(s²−1) + L/(s²−1)
  (let ((sp (integrate::mx-log-sign-split '(* (log (+ 1 (* -1 (^ s 2)))) (^ (+ (^ s 2) -1) -1)) 's)))
    (assert-equal (cadr sp) '(^ (+ -1 (^ s 2)) -1))
    (assert-true (not (contains-sym? (car sp) '%L))))
  ; две отрицательные константы сокращаются: h = 0
  (assert-equal (cadr (integrate::mx-log-sign-split
                       '(+ (log (+ 1 (* -1 s))) (* -1 (log (+ 1 (* -2 s))))) 's))
                0)
  ; положительные аргументы не меняются
  (assert-equal (cadr (integrate::mx-log-sign-split '(log (+ 1 s)) 's)) 0))

(deftest "mixed R3.2: линейная параметризация y^q = a·v + b"
  (let ((p (integrate::mx-linear-param '(+ 1 (* -1 %t)) 2 '%t)))
    (assert-equal (cadr p) 't)
    (assert-equal (simplify (subst '(t 2) (car p))) -3))
  (assert-equal #f (integrate::mx-linear-param '(+ 1 (^ %t 2)) 2 '%t))
  (assert-equal #f (integrate::mx-linear-param '(+ 1 (* a %t)) 2 '%t)))

(deftest "mixed R3.2: не род 0 с x — x·eˣ√(e³ˣ+1) остаётся без ответа и без вердикта"
  (conditions-clear)
  (let ((r (integrate '(* x (exp x) (sqrt (+ (exp (* 3 x)) 1))) 'x)))
    (assert-true (contains-sym? r 'integrate))
    (assert-true (not (mxt-ne? r)))))

(deftest "mixed R3.2: бюджет времени — исчерпан: ни ответа, ни вердикта, условие timeout"
  (let ((old integrate::mx-time-limit))
    (unwind-protect
        (begin
          (set! integrate::mx-time-limit 0.001)
          (conditions-clear)
          (let ((r (integrate::int-mixed (integrate::int-norm '(* x (sqrt (+ (exp x) 1)))) 'x 0)))
            (assert-equal r #f)
            (assert-true (not (mxt-any-ne?)))
            (assert-true (any? (lambda (c) (equal? (car (car c)) 'timeout)) (conditions)))))
      (set! integrate::mx-time-limit old))))

; фальсификации чекера для не x-free формы: e = x√(eˣ+1), g — его образ в параметре 't (s = √(eˣ+1))
(define mxt-e2 '(* x (^ (+ 1 (exp x)) 1/2)))
(define mxt-s2 '(^ (+ 1 (exp x)) 1/2))

(define (mxt-tr e g c sx)
  (car (capture-conditions (lambda () (integrate::mx-transfer-ne! e 'x c g 't sx 'risch 't '())))))

(deftest "mixed R3.2: чекер — честный перенос по Ришу и подделки"
  (let* ((e1 (integrate::mx-norm mxt-e2)) (th (caddr (integrate::mx-plan e1 'x)))
         (gx (integrate::mx-substitute e1 'x th))
         (cg (integrate::mx-const-split (car gx) '%t))
         (rz (integrate::mx-rationalize (cdr cg) '%t (integrate::mx-th-theta th)))
         (g (car rz)) (sx (caddr rz)))
    ; без прогона Риша доказательства нет (g ≠ ничего из таблицы)
    (assert-equal #f (mxt-tr mxt-e2 '(* t (^ (+ t -1) -1)) 1 mxt-s2))
    (assert-true (mxt-ne? (integrate mxt-e2 'x)))
    ; честно: x-free, константы ℚ, доказательство, отображение
    (assert-equal #t (mxt-tr mxt-e2 g (car cg) sx))
    ; x в g; постоянный множитель 0; подменённое отображение s = √(e²ˣ+1)
    (assert-equal #f (mxt-tr mxt-e2 (list '* 'x g) (car cg) sx))
    (assert-equal #f (mxt-tr mxt-e2 g 0 sx))
    (assert-equal #f (mxt-tr mxt-e2 g (car cg) '(^ (+ 1 (exp (* 2 x))) 1/2))))
  ; элементарные внутренние интегралы — флаг «доказано» не выставляется
  (assert-equal #f (integrate::mx-risch-proved? '(* 2 t) 't))
  (assert-equal #f (integrate::mx-risch-proved? '(^ (+ -1 (^ t 2)) -1) 't)))

(deftest "mixed R3.2: ложный ответ отвергается проверкой по исходному f"
  (assert-equal #f (integrate::mx-ok '(+ (* x (^ (+ 1 (exp x)) 1/2)) x) (diff 'x mxt-e2) 'x))
  (assert-true (integrate::mx-ok mxt-e2 (diff 'x mxt-e2) 'x)))

(deftest "mixed: подменённая обратная функция — ответ отвергается проверкой"
  ; G(t) = ∫√(t+1)/t, но обратная подстановка t = e^{2x} вместо eˣ: gn-ok? по исходному f — #f
  (let* ((G (integrate '(/ (sqrt (+ x 1)) x) 'x))
         (bad (simplify (subst '(x (exp (* 2 x))) G))))
    (assert-equal #f (integrate::mx-ok bad '(sqrt (+ (exp x) 1)) 'x))
    (assert-true (integrate::mx-ok (simplify (subst '(x (exp x)) G)) '(sqrt (+ (exp x) 1)) 'x))))
