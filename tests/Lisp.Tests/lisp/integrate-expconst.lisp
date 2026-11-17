; INT.EXPCONST (RUBI.CH8, часть B): hebisch 6110, 1679, 9582 — постоянные exp(k) в рациональной функции.
; Для rat-integrate-log/Эрмита/«по частям» (exp 5) и (exp 10) — независимые параметры, хотя exp 10 = (exp 5)²:
; ответ, верный для независимых параметров, вырождался при подстановке (слагаемое log(x + e^5) терялось, «по частям» давала
; ряд-подделку), а у 9582 слагаемые ∫−25/(25 − 30x²e^14 + 9x⁴e^28) уходили в 0, потому что допуск проверки
; tol·(1 + |e|) при |e| ≈ 1e-11 абсолютный. Теперь постоянные exp(k) заменяются степенями одного положительного символа
; (int-go-exp-consts), а ЛРТ не принимает ответ, не зависящий от x, для ненулевой функции. (Относительный допуск при малом
; |e| пробовали и отвергли: у верных ответов Rubi с коэффициентами 1e12 шум float сравним с |e| — потеря на срезе.)

(define (iec-at e x0) (eval-num (replace-expr e 'x x0)))
(define (iec-near? a b tol) (and (number? a) (number? b) (<= (abs (- a b)) (* tol (+ 1 (abs b))))))
; F' ≈ f центральной разностью с Ричардсоном (h = 1e-3·(1+|x|)) — шум численных значений не мешает
(define (iec-antiderivative? f F x0)
  (let* ((h (* 0.001 (+ 1 (abs x0))))
         (d1 (/ (- (iec-at F (+ x0 h)) (iec-at F (- x0 h))) (* 2 h)))
         (d2 (/ (- (iec-at F (+ x0 (/ h 2))) (iec-at F (- x0 (/ h 2)))) h))
         (dr (/ (- (* 4 d2) d1) 3)))
    (iec-near? dr (iec-at f x0) 1e-7)))

(deftest "integrate-expconst/1: hebisch 6110 — рациональная с exp(5), exp(10): ответ верен (раньше ряд-подделка)"
  (let* ((f (math-read "((-12*x**3-2)*exp(5)**2+(-24*x**4-18*x**2-4*x)*exp(5)-12*x**5-2*x**2)/(x**2*exp(5)**2+2*x**3*exp(5)+x**4)"))
         (F (integrate f 'x)))
    (assert-true (not (contains-sym? F 'integrate)))
    (for-each (lambda (x0) (assert-true (iec-antiderivative? f F x0))) '(0.3 1.5 10.0 -2.0 -10.0))))

(deftest "integrate-expconst/2: hebisch 1679 — рациональная с exp(4), exp(8), exp(12)"
  (let* ((f (math-read "(3*x**3*exp(4)**3+(-9*x**4-27*x**3)*exp(4)**2+(9*x**5+54*x**4+81*x**3+144)*exp(4)-3*x**6-27*x**5-81*x**4-81*x**3-288*x-432)/(x**3*exp(4)**3+(-3*x**4-9*x**3)*exp(4)**2+(3*x**5+18*x**4+27*x**3)*exp(4)-x**6-9*x**5-27*x**4-27*x**3)"))
         (F (integrate f 'x)))
    (assert-true (not (contains-sym? F 'integrate)))
    (for-each (lambda (x0) (assert-true (iec-antiderivative? f F x0))) '(0.3 1.5 10.0 -2.0))))

(deftest "integrate-expconst/3: hebisch 9582 — слагаемое −25/D не теряется (раньше → 0, ответ −x)"
  (let* ((D '(+ 25 (* -30 (^ x 2) (exp 14)) (* 9 (^ x 4) (exp 28))))
         (f (list '* -25 (list '^ D -1)))
         (F (integrate f 'x)))
    (assert-true (not (equal? F 0)))
    (assert-true (not (contains-sym? F 'integrate)))
    ; |f| ≈ 1e-11: сравнение относительное (абсолютный допуск пропустил бы и ноль)
    (for-each (lambda (x0)
                (let* ((h 0.001)
                       (d (/ (- (iec-at F (+ x0 h)) (iec-at F (- x0 h))) (* 2 h)))
                       (fx (iec-at f x0)))
                  (assert-true (<= (abs (- d fx)) (* 0.001 (abs fx))))))
              '(0.3 1.5 -2.0))))
