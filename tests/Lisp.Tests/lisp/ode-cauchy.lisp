; ode-cauchy.lisp — тесты шага ODE.4a: задача Коши и уравнение Эйлера–Коши.

; уравнение решено с условиями; сертификат точный
(define (ca-t-particular eq conds)
  (let ((r (apply dsolve (cons eq (cons '(y x) conds)))))
    (and (equal? (ode-status r) 'ok)
         (equal? (ode::ode-field r :type) 'particular)
         (equal? (ode::ode-field r :check) #t)
         (pair? (ode-solutions r)))))

(deftest "ODE.4a: y' = y, y(0) = 2 → 2e^x"
  (assert-true (ca-t-particular '(= (diff (y x) x) (y x)) '((= (y 0) 2))))
  (let ((r (dsolve '(= (diff (y x) x) (y x)) '(y x) '(= (y 0) 2))))
    (assert-equal (car (ode-solutions r)) '(= (y x) (* 2 (exp x))))))

(deftest "ODE.4a: y'' + y = 0, y(0) = 1, y'(0) = 0 → cos x"
  (assert-true (ca-t-particular
                '(= (+ (diff (diff (y x) x) x) (y x)) 0)
                '((= (y 0) 1) (= (at (diff (y x) x) (= x 0)) 0))))
  (let ((r (dsolve '(= (+ (diff (diff (y x) x) x) (y x)) 0) '(y x)
                   '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0))))
    (assert-equal (car (ode-solutions r)) '(= (y x) (cos x)))))

(deftest "ODE.4a: y'' − 3y' + 2y = 0 с двумя условиями"
  (assert-true (ca-t-particular
                '(= (+ (- (diff (diff (y x) x) x) (* 3 (diff (y x) x))) (* 2 (y x))) 0)
                '((= (y 0) 0) (= (at (diff (y x) x) (= x 0)) 1)))))

(deftest "ODE.4a: условие в нецелой точке — y' = y, y(1) = e"
  (assert-true (ca-t-particular
                '(= (diff (y x) x) (y x))
                '((= (y 1) (exp 1))))))

(deftest "ODE.4a: несовместные условия — unknown с причиной"
  (let ((r (dsolve '(= (diff (y x) x) 0) '(y x) '(= (y 0) 1) '(= (y 0) 2))))
    (assert-equal (ode-status r) "условия несовместны: система на C1…Cn не имеет решения")
    (assert-equal (ode-solutions r) '())))

(deftest "ODE.4a: условие порядка 2 (y''(0))"
  ; y'' + y = 0, y(0) = −1, y''(0) = 1 → y = −cos x
  (assert-true (ca-t-particular
                '(= (+ (diff (diff (y x) x) x) (y x)) 0)
                '((= (y 0) -1) (= (at (diff (diff (y x) x) x) (= x 0)) 1)))))

(deftest "ODE.4a: неявное решение с условием y(0) = 0"
  (let ((r (dsolve '(= (diff (y x) x) (exp (* -1 (^ (y x) 2)))) '(y x) '(= (y 0) 0))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)))

(deftest "ODE.4a: подделка — верное для уравнения, неверная константа"
  ; y = 3e^x удовлетворяет y' = y, но условию y(0) = 2 — нет
  (assert-equal #f (dsolve-conditions-check '(= (diff (y x) x) (y x))
                                            '(= (y x) (* 3 (exp x))) '(y x)
                                            (list (ode::ca-condition '(= (y 0) 2) 'y 'x)))))

(deftest "ODE.4a: подделка — решение верно для уравнения, но не для условия"
  ; y = cos x удовлетворяет y'' + y = 0, но y(0) = 1/2 — нет
  (assert-equal #f (dsolve-conditions-check
                    '(= (+ (diff (diff (y x) x) x) (y x)) 0)
                    '(= (y x) (cos x)) '(y x)
                    (list (ode::ca-condition '(= (y 0) 1/2) 'y 'x)))))

(deftest "ODE.4a: dsolve-conditions-check принимает настоящее частное"
  (assert-equal #t (dsolve-conditions-check
                    '(= (diff (y x) x) (y x)) '(= (y x) (* 2 (exp x))) '(y x)
                    (list (ode::ca-condition '(= (y 0) 2) 'y 'x)))))

; ---------- уравнение Эйлера–Коши ----------

(deftest "ODE.4a: x²y'' − 2xy' + 2y = 0 → C1·x + C2·x²"
  (let ((r (dsolve '(= (+ (- (* x x (diff (diff (y x) x) x)) (* 2 x (diff (y x) x)))
                          (* 2 (y x))) 0) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'euler)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r)) '(= (y x) (+ (* C1 x) (* C2 (^ x 2)))))))

(deftest "ODE.4a: x²y'' + xy' + y = 0 → cos(log x), sin(log x)"
  (let ((r (dsolve '(= (+ (+ (* x x (diff (diff (y x) x) x)) (* x (diff (y x) x)))
                          (y x)) 0) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'euler)
    (assert-equal (ode::ode-field r :check) #t)))

(deftest "ODE.4a: x²y'' − xy' + y = 0 → кратный корень: x, x·log x"
  (let ((r (dsolve '(= (+ (- (* x x (diff (diff (y x) x) x)) (* x (diff (y x) x)))
                          (y x)) 0) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'euler)
    (assert-equal (car (ode-solutions r)) '(= (y x) (+ (* C1 x) (* C2 x (log x)))))))

(deftest "ODE.4a: Эйлер с условием Коши — x²y'' − 2xy' + 2y = 0, y(1) = 3, y'(1) = 5"
  (let ((r (dsolve '(= (+ (- (* x x (diff (diff (y x) x) x)) (* 2 x (diff (y x) x)))
                          (* 2 (y x))) 0) '(y x)
                   '(= (y 1) 3) '(= (at (diff (y x) x) (= x 1)) 5))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-equal (ode::ode-field r :check) #t)))

(deftest "ODE.4a: подделка Эйлера — решение не того уравнения отвергается check"
  ; y = 3x + C2·x² не решение x²y'' − 3xy' + 4y = 0 (коэффициент при y испорчен)
  (assert-equal #f (dsolve-check
                    '(= (+ (- (* x x (diff (diff (y x) x) x)) (* 3 x (diff (y x) x)))
                           (* 4 (y x))) 0)
                    '(= (y x) (+ (* 3 x) (* C2 (^ x 2)))) '(y x))))

(deftest "ODE.4a: dsolve-conditions-check — условия в исходной форме; проверяются все условия; неявное решение без сертификата"
  (define eq2 '(= (+ (diff (diff (y x) x) x) (y x)) 0))
  (assert-equal #t (dsolve-conditions-check eq2 '(= (y x) (cos x)) '(y x)
                                            (list '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0))))
  (assert-equal #f (dsolve-conditions-check eq2 '(= (y x) (cos x)) '(y x)
                                            (list '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 1))))
  (assert-equal #f (dsolve-conditions-check eq2 '(= (y x) (cos x)) '(y x) (list '(= (z 0) 1))))
  (assert-equal #f (dsolve-conditions-check '(= (diff (y x) x) (/ x (y x))) '(= (- (^ (y x) 2) (^ x 2)) 7) '(y x)
                                            (list '(= (y 0) 1)))))

; ---------- ODE.4b: потерянная ветвь, неявное частное, допуск условий ----------

(deftest "ODE.4b: y' = x/y — обе ветви ±√(2C1 + x²)"
  (let ((r (dsolve '(= (diff (y x) x) (/ x (y x))) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (length (ode-solutions r)) 2)
    (assert-true (any? (lambda (s) (equal? s '(= (y x) (sqrt (+ (* 2 C1) (^ x 2))))))
                       (ode-solutions r)))
    (assert-true (any? (lambda (s) (equal? s '(= (y x) (* -1 (sqrt (+ (* 2 C1) (^ x 2)))))))
                       (ode-solutions r)))))

(deftest "ODE.4b: y' = x/y, y(0) = 1 → √(x² + 1)"
  (let ((r (dsolve '(= (diff (y x) x) (/ x (y x))) '(y x) '(= (y 0) 1))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r)) '(= (y x) (sqrt (+ 1 (^ x 2)))))))

(deftest "ODE.4b: y' = x/y, y(0) = −1 → −√(x² + 1) (ветвь по условию)"
  (let ((r (dsolve '(= (diff (y x) x) (/ x (y x))) '(y x) '(= (y 0) -1))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r)) '(= (y x) (* -1 (sqrt (+ 1 (^ x 2))))))))

(deftest "ODE.4b: y' = 1/y, y(0) = −2 → −√(4 + 2x)"
  (let ((r (dsolve '(= (diff (y x) x) (/ 1 (y x))) '(y x) '(= (y 0) -2))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)))

(deftest "ODE.4b: неявное частное y' = e^(−y²), y(0) = 0 → ∫₀^y e^(s²)ds − x = 0 с сертификатом"
  (let ((r (dsolve '(= (diff (y x) x) (exp (* -1 (^ (y x) 2)))) '(y x) '(= (y 0) 0))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r))
                  '(= (+ (* -1 x) (integrate (exp (^ ode-s 2)) ode-s 0 y)) 0))))

(deftest "ODE.4b: неявное частное с другим условием — y(0) = 1"
  (let ((r (dsolve '(= (diff (y x) x) (exp (* -1 (^ (y x) 2)))) '(y x) '(= (y 0) 1))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)))

(deftest "ODE.4b: допуск условий — подделка 10⁻⁹ отбрасывается (#f), точное решение #t"
  ; y = cos x·(1 + 10⁻⁹(π − 3)) удовлетворяет уравнению численно, но условию y(0) = 1 — нет
  (assert-equal #f (ode::ca-check-condition
                    '(* (cos x) (+ 1 (* (^ 10 -9) (- %pi 3)))) 0 'x 0 1))
  (assert-equal #t (ode::ca-check-condition '(cos x) 0 'x 0 1)))

(deftest "ODE.4b: подделка ветви — y(0) = 1, а решение −√(x² + 1)"
  (assert-equal #f (ode::ca-check-condition '(* -1 (sqrt (+ 1 (^ x 2)))) 0 'x 0 1))
  (assert-equal #t (ode::ca-check-condition '(* -1 (sqrt (+ 1 (^ x 2)))) 0 'x 0 -1)))
