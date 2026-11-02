; integrate-refusal-steps.lisp — Q.1: шаги отказа Риша видны при вызове через integrate.

(define (irs-log ex)
  (capture-step-log (lambda () (integrate ex 'x)) 'brief 'ru))

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
        (assert-equal val (integrate ex 'x))
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
      (/ 1 (log x))
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
  (assert-equal (integrate '(/ (sin x) x) 'x) '(integrate (* (^ x -1) (sin x)) x)))
