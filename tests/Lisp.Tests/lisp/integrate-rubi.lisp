; Rubi как запасная ступень integrate: интегралы, которые прежний каскад не брал, теперь берутся правилами Rubi;
; ответ проверен дифференцированием, шаги содержат рамку «Правила Rubi» и цепочку правил; доказанная
; неэлементарность в Rubi не уходит; прежние ответы каскада не меняются.

; другие файлы тестов подменяют правила Rubi игрушечными наборами - возвращаем настоящие
(define (ir-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (ir-unevaluated? r) (and (pair? r) (equal? (car r) 'integrate)))

(define (ir-solved src)
  (ir-fresh)
  (let* ((e (math-read src))
         (r (integrate e 'x)))
    (assert-true (not (ir-unevaluated? r)))
    (assert-true (rubi::rubi-int-check r e 'x))
    r))

(deftest "integrate/rubi: (a+bx)^n/(c+dx) с символьным n - ответ с 2F1, проверен дифференцированием"
  (let ((r (ir-solved "(a + b*x)^n/(c + d*x)")))
    (assert-true (rubi::rubi-has-head? r 'hypergeometric-2f1))))

(deftest "integrate/rubi: интегралы, которые каскад не брал, берутся запасной ступенью"
  (for-each ir-solved
            '("1/(x^(4/3)*(a + b*x))"
              "(c*x^2)^(5/2)*(a + b*x)^n"
              "(1 - 2*x)^(3/2)*(3*x + 2)^(3/2)*sqrt(5*x + 3)"
              "1/(x*(1 - x)^(1/3)*(2 - x)^(1/3))"
              "(x - 1)^(1/3)/(x + 1)^(1/3)"
              "(a + b*x)^n*(c + d*x)^(-n - 3)")))

(deftest "integrate/rubi: запасная ступень выключается флагом - прежний отказ"
  (ir-fresh)
  (set! integrate::int-rubi-enabled #f)
  (let ((r (integrate (math-read "(c*x^2)^(5/2)*(a + b*x)^n") 'x)))
    (set! integrate::int-rubi-enabled #t)
    (assert-true (ir-unevaluated? r))))

(deftest "integrate/rubi: шаги - рамка стратегии rubi и цепочка правил Rubi"
  (ir-fresh)
  (let* ((cap (capture-step-log (lambda () (integrate (math-read "1/(x^(4/3)*(a + b*x))") 'x)) 'full 'ru))
         (txt (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-true (not (ir-unevaluated? (car cap))))
    (assert-true (string-contains? txt "Правила Rubi"))
    (assert-true (string-contains? txt "Rubi 1.1.1.2 #"))
    (assert-true (>= (length (step-rules (cadr cap))) 3))))

(define (ir-has-ne-condition?)
  (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary))) (conditions)))

; RUBI.6.5: Rubi зовётся и после доказанной неэлементарности
(deftest "integrate/rubi: после доказанной неэлементарности (Чебышёв) Rubi отвечает эллиптической функцией, условия risch-nonelementary нет"
  (ir-fresh)
  (conditions-clear)
  ; x^(1/6)(1+x)^(-1/2): Чебышёв доказал отказ; Rubi даёт EllipticF
  (let* ((e (math-read "x^(1/6)/(1 + x)^(1/2)")) (r (integrate e 'x)))
    (assert-true (not (ir-unevaluated? r)))
    (assert-true (integrate::int-has-special? r))
    (assert-true (rubi::rubi-int-check r e 'x))
    (assert-true (not (ir-has-ne-condition?)))
    (assert-true (not (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-rubi-conflict))) (conditions))))))

(deftest "integrate/rubi: корень из x^3+1 и x^(1/3)(1+x)^(1/2) - ответ со спецфункциями после отказа Риша"
  (ir-fresh)
  (conditions-clear)
  (for-each (lambda (src)
              (let* ((e (math-read src)) (r (integrate e 'x)))
                (assert-true (not (ir-unevaluated? r)))
                (assert-true (integrate::int-has-special? r))
                (assert-true (rubi::rubi-int-check r e 'x))))
            '("x^2/(1 + x^5)^(1/3)" "x^(1/3)*(1 + x)^(1/2)" "sqrt(1 + x^3)"))
  (assert-true (not (ir-has-ne-condition?))))

(deftest "integrate/rubi: шаги - элементарной первообразной нет (Риш) → ответ через спецфункции (Rubi)"
  (ir-fresh)
  (conditions-clear)
  (let* ((cap (capture-step-log (lambda () (integrate (math-read "x^2/(1 + x^5)^(1/3)") 'x)) 'full 'ru))
         (txt (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-true (not (ir-unevaluated? (car cap))))
    (assert-true (string-contains? txt "Правила Rubi"))
    (assert-true (string-contains? txt "ответ через спецфункции (Rubi)"))))

(deftest "integrate/rubi: честная неэлементарность без ответа Rubi остаётся - условие risch-nonelementary, значение невычислено"
  (ir-fresh)
  (for-each (lambda (src)
              (conditions-clear)
              (let ((r (integrate (math-read src) 'x)))
                (assert-true (ir-unevaluated? r))
                (assert-true (ir-has-ne-condition?))))
            '("exp(x^2)" "sin(x)/x" "1/log(x)" "exp(x)/x")))

(deftest "integrate/rubi: флаг int-rubi-on-nonelementary выключает Rubi после доказанной неэлементарности"
  (ir-fresh)
  (conditions-clear)
  (set! integrate::int-rubi-on-nonelementary #f)
  (let ((r (integrate (math-read "x^(1/6)/(1 + x)^(1/2)") 'x)))
    (set! integrate::int-rubi-on-nonelementary #t)
    (assert-true (ir-unevaluated? r))
    (assert-true (ir-has-ne-condition?))))

(deftest "integrate/rubi: условие-дефект risch-rubi-conflict - Rubi нашёл элементарное при доказанной неэлементарности"
  (ir-fresh)
  (conditions-clear)
  ; ответ Rubi без спецфункций после доказательства: условие-дефект; со спецфункцией — нет
  (integrate::int-rubi-after-proof (math-read "exp(x^2)") 'x '(* 2 (exp x)))
  (assert-true (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-rubi-conflict))) (conditions)))
  (conditions-clear)
  (integrate::int-rubi-after-proof (math-read "exp(x^2)") 'x '(* 2 (erfi x)))
  (assert-true (not (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-rubi-conflict))) (conditions)))))

(deftest "integrate/rubi: ответы каскада не меняются"
  (ir-fresh)
  (assert-equal (simplify (integrate (math-read "x^2") 'x)) (simplify '(* 1/3 (^ x 3))))
  (assert-equal (simplify (integrate (math-read "1/(1 + x^2)") 'x)) '(atan x))
  ; каскад ответил - Rubi не загружался
  (assert-equal #f rubi::*rubi-loaded*))
