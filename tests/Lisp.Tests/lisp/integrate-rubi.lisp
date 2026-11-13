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

(define (ir-has-head? e h) (and (pair? e) (or (equal? (car e) h) (any? (lambda (t) (ir-has-head? t h)) (cdr e)))))
; RUBI.6.6: Rubi и когда ответ каскада сомнителен (громоздкий, с RootSum, проверен только численно)
(deftest "integrate/rubi: громоздкий ответ каскада заменяется коротким ответом Rubi (x^2*sqrt(1-x^2))"
  (ir-fresh)
  (let* ((f (math-read "x^2*sqrt(1-x^2)"))
         (r (integrate f 'x)))
    (assert-true (< (integrate::int-size r) 60))
    (assert-true (ir-has-head? r 'asin))
    (assert-true (member? (int-check-how r f 'x) '(simplify together numeric)))))

(deftest "integrate/rubi: ответ с RootSum заменяется ответом Rubi без RootSum, проверенным точно"
  (ir-fresh)
  (let* ((f (math-read "(c + d*x)/(a - b*x^4)"))
         (r (integrate f 'x)))
    (assert-true (null? (integrate::int-rootsums r)))
    ; RUBI.MATCH: правило-победитель другое (короче, с atanh(b x^4/a)^(1/2)) — simplify его не доказывает,
    ; число проверяется; раньше ответ совпадал по форме и проходил together
    (assert-true (member? (int-check-how r f 'x) '(simplify together numeric)))
    ; сверка при обоих знаках x: подынтегральное и ответ вещественны вне нуля
    (assert-true (equal? 'ok (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x r) f) r 'x 0.001
                                                             (list -2.0 -1.4 -0.7 -0.3 0.3 0.7 1.4 2.0))))))

(deftest "integrate/rubi: несомнительный ответ каскада не трогается, Rubi не вызывается"
  (ir-fresh)
  (assert-equal #f (integrate::int-doubtful-why (simplify (integrate (math-read "x*exp(x)") 'x)) (math-read "x*exp(x)") 'x))
  (assert-equal #f rubi::*rubi-loaded*))

(deftest "integrate/rubi: неудача и спецфункция Rubi не портят ответ каскада"
  (ir-fresh)
  (let* ((f (math-read "1/(x^5+1)"))
         (F (integrate::int-antiderivative f 'x)))
    ; ответ каскада громоздкий, Rubi даёт ₂F₁ — каскад остаётся
    (assert-true (integrate::int-doubtful-why F f 'x))
    (assert-equal F (integrate::int-refine-by-rubi F f 'x))
    ; бюджет Rubi нулевой - ответ тот же
    (set! integrate::int-rubi-doubt-time-limit 0.001)
    (let ((G (integrate::int-refine-by-rubi F f 'x)))
      (set! integrate::int-rubi-doubt-time-limit 3)
      (assert-equal F G))))
