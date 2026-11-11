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

(deftest "integrate/rubi: доказанная неэлементарность в Rubi не уходит"
  (ir-fresh)
  ; Чебышёв: x^(1/6)(1+x)^(-1/2) - Rubi дал бы EllipticF, но Риш/Чебышёв доказали отказ
  (let ((r (integrate (math-read "x^(1/6)/(1 + x)^(1/2)") 'x)))
    (assert-true (ir-unevaluated? r))
    (assert-true (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary))) (conditions))))
  ; Лиувилль: exp(x^2)
  (assert-true (ir-unevaluated? (integrate (math-read "exp(x^2)") 'x)))
  ; Rubi не загружался для этих отказов
  (assert-equal #f rubi::*rubi-loaded*))

(deftest "integrate/rubi: ответы каскада не меняются"
  (ir-fresh)
  (assert-equal (simplify (integrate (math-read "x^2") 'x)) (simplify '(* 1/3 (^ x 3))))
  (assert-equal (simplify (integrate (math-read "1/(1 + x^2)") 'x)) '(atan x))
  ; каскад ответил - Rubi не загружался
  (assert-equal #f rubi::*rubi-loaded*))
