; ode-linear.lisp — тесты шага ODE.3: постоянные коэффициенты.

(deftest "ODE.3: однородное y″ + y = 0 — комплексные корни в вещественной форме"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (y x)) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'const-coeff)
    (assert-equal (length (ode-solutions r)) 1)
    (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.3: кратный корень y″ − 2y′ + y = 0"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* -2 (diff (y x) x)) (y x)) 0))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-true (dsolve-check eq sol '(y x)))
    ; в ответе обязаны быть e^x и x·e^x
    (assert-true (ode::ode-has-head? sol 'exp))
    (assert-true (ode::ode-has-head? sol '*))))

(deftest "ODE.3: резонанс y″ + y = sin x (метод неопределённых коэффициентов с множителем x)"
  ; после ODE.5b резонанс берут неопределённые коэффициенты (не вариация постоянных)
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (y x)) (sin x)))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'undetermined)
    (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.3: вариация постоянных y″ − 2y′ + y = e^x/x"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* -2 (diff (y x) x)) (y x)) (/ (exp x) x)))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'variation)
    (assert-true (dsolve-check eq sol '(y x)))
    (assert-true (ode::ode-has-head? sol 'log))))

(deftest "ODE.3: y⁽⁴⁾ − y = 0 — четыре независимых решения"
  (let* ((eq '(= (- (diff (diff (diff (diff (y x) x) x) x) x) (y x)) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (length (ode::ode-field r :constants)) 4)
    (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.3: характеристический x⁵ + x + 1 — честный unknown"
  ; root-of-решения не проходят символьный/численный сертификат — не выдаём непроверенное
  (let* ((eq '(= (+ (diff (diff (diff (diff (diff (y x) x) x) x) x) x)
                    (diff (y x) x) (y x)) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'unknown)
    (assert-equal (ode-solutions r) '())))

(deftest "ODE.3: подделка отвергается"
  (assert-equal (dsolve-check '(= (+ (diff (diff (y x) x) x) (y x)) 0)
                              '(= (y x) (+ C1 (cos x) (* C2 (sinh x))))
                              '(y x))
                #f))
; ---------- ODE.5b: резонанс (пробел ODE.3) ----------

(deftest "ODE.5b: резонанс y″ + 4y = sin 2x → −x·cos 2x/4"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* 4 (y x))) (sin (* 2 x))))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (dsolve-check eq sol '(y x)))
    ; частное содержит множитель x (резонанс): C1 cos 2x + C2 sin 2x − x·cos 2x/4
    (assert-equal sol '(= (y x) (+ (* C1 (cos (* 2 x))) (* C2 (sin (* 2 x)))
                                   (* -1/4 x (cos (* 2 x))))))))

(deftest "ODE.5b: резонанс y″ + 4y = cos 2x (тригонометрический, второй вид)"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* 4 (y x))) (cos (* 2 x))))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (dsolve-check eq sol '(y x)))))

(deftest "ODE.5b: резонанс с e^{ax}·xⁿ — y″ − 2y′ + y = x²e^x даёт x⁴e^x/12"
  (let* ((eq '(= (+ (- (diff (diff (y x) x) x) (* 2 (diff (y x) x))) (y x))
                 (* (exp x) (^ x 2))))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal sol '(= (y x) (+ (* C1 (exp x)) (* C2 x (exp x)) (* 1/12 (^ x 4) (exp x)))))))

(deftest "ODE.5b: резонанс y″ + y = sin x — вариация постоянных, множитель x"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (y x)) (sin x)))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (dsolve-check eq sol '(y x)))))

(deftest "ODE.5b: подделка резонанса отвергается (нет множителя x)"
  ; без x·cos 2x/4 не удовлетворяет y″ + 4y = sin 2x
  (assert-equal (dsolve-check '(= (+ (diff (diff (y x) x) x) (* 4 (y x))) (sin (* 2 x)))
                              '(= (y x) (+ (* C1 (cos (* 2 x))) (* C2 (sin (* 2 x)))))
                              '(y x))
                #f))

