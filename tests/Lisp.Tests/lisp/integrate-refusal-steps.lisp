; integrate-refusal-steps.lisp — Q.1: шаги отказа Риша видны при вызове через integrate.

; шаги отказа Риша — без ответа Rubi через спецфункцию после доказательства (решение пользователя 2026-11-15:
; с Rubi ∫1/ln x получает ответ −Γ(0, −ln x), и отказа в журнале уже нет)
(define (irs-log ex)
  (capture-step-log (lambda () (without-rubi-after-proof (lambda () (integrate ex 'x)))) 'brief 'ru))

(define (irs-lines s)
  (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))

(deftest "Q.1: доказанный отказ Риша попадает в brief через integrate (7 примеров П1)"
  (for-each
    (lambda (ex)
      (let* ((r (irs-log ex))
             (val (car r))
             (rules (step-rules (cadr r)))
             (s (steps-text (cadr r) (caddr r) 'ru)))
        ; ответ не изменился по сравнению с вызовом без журнала
        (assert-equal val (without-rubi-after-proof (lambda () (integrate ex 'x))))
        ; условие отказа сохранено
        (assert-true (risch-nonelementary? ex 'x))
        ; в журнале есть и рамка risch, и шаг risch-nonelementary с причиной
        (assert-true (member? 'risch rules))
        (assert-true (member? 'risch-nonelementary rules))
        (assert-true (string-contains? s "неэлементар"))
        (assert-true (<= (irs-lines s) 15))))
    '((exp (^ x 2))
      (* (^ x 2) (exp (- (^ x 2))))
      (/ (exp x) x)
      (/ (sin x) x)
      ; (/ 1 (log x)) убран: после RUBI.CH2/INT.SFREAL integrate отвечает li(x) (Rubi), отказа нет
      (* x (exp x) (log x))
      (* (log x) (sin x)))))

(deftest "Q.1: частичный ответ Риша — шаги прежние, ответ и условие не меняются"
  (let* ((ex '(* (^ x 2) (exp (- (^ x 2)))))
         (r (irs-log ex))
         (s (steps-text (cadr r) (caddr r) 'ru))
         (rules (step-rules (cadr r))))
    (assert-equal (car r) (integrate ex 'x))
    (assert-true (string-contains? (to-string (car r)) "integrate"))
    (assert-true (member? 'risch-tower rules))
    (assert-true (member? 'risch-nonelementary rules))
    (assert-true (string-contains? s "остаток неэлементарен"))
    (assert-true (<= (irs-lines s) 15))))

(deftest "Q.1: без журнала ответ тот же и шагов нет"
  (assert-equal (integrate '(exp (^ x 2)) 'x) '(integrate (exp (^ x 2)) x))
  ; INT.SF2: sin x/x → Si(x) (Rubi); отказ остаётся у sin x/(x+1)
  (assert-equal (integrate '(/ (sin x) (+ x 1)) 'x) '(integrate (* (^ (+ 1 x) -1) (sin x)) x)))
