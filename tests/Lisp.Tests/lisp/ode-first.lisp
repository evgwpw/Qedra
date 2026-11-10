; ode-first.lisp — тесты шага ODE.1: первый порядок.

(deftest "ODE.1: линейное уравнение и интегрирующий множитель"
  (let ((r (dsolve '(= (+ (diff (y x) x) (y x)) x) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'linear)
    (assert-true (dsolve-check '(= (+ (diff (y x) x) (y x)) x) (car (ode-solutions r)) '(y x))))
  (let ((r (dsolve '(= (diff (y x) x) (+ (* 2 x (y x)) x)) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-true (dsolve-check '(= (diff (y x) x) (+ (* 2 x (y x)) x)) (car (ode-solutions r)) '(y x)))))

(deftest "ODE.1: разделяющиеся переменные"
  (let ((r (dsolve '(= (diff (y x) x) (/ x (y x))) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'separable)
    (assert-true (dsolve-check '(= (diff (y x) x) (/ x (y x))) (car (ode-solutions r)) '(y x))))
  ; неявный ответ: atan y − x = C1
  (let ((r (dsolve '(= (diff (y x) x) (+ 1 (^ (y x) 2))) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'implicit)
    (assert-equal (ode::ode-field r :check) #t)))

(deftest "ODE.1: Бернулли и потерянные решения"
  (let ((r (dsolve '(= (diff (y x) x) (^ (y x) 2)) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'bernoulli)
    (assert-true (dsolve-check '(= (diff (y x) x) (^ (y x) 2)) (car (ode-solutions r)) '(y x)))
    (assert-true (pair? (ode::ode-field r :singular))))
  ; y = 0 и y = 1 — потерянные постоянные решения
  (let* ((eq '(= (diff (y x) x) (* (y x) (- (y x) 1))))
         (r (dsolve eq '(y x)))
         (sing (map (lambda (s) (caddr s)) (ode::ode-field r :singular))))
    (assert-true (any? (lambda (s) (equal? s 0)) sing))
    (assert-true (any? (lambda (s) (equal? s 1)) sing))
    (assert-true (every? (lambda (s) (dsolve-check eq s '(y x))) (ode::ode-field r :singular)))))

(deftest "ODE.1: однородное уравнение y = ux"
  (let ((r (dsolve '(= (diff (y x) x) (/ (+ x (y x)) (- x (y x)))) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'homogeneous)
    (assert-equal (ode::ode-field r :type) 'implicit)
    (assert-true (any? (lambda (v) (equal? v (ode::ode-field r :check))) '(#t numeric)))))

(deftest "ODE.1: квадратура с неэлементарным интегралом"
  (let ((r (dsolve '(= (diff (y x) x) (exp (^ x 2))) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'quadrature)
    (assert-true (dsolve-check '(= (diff (y x) x) (exp (^ x 2))) (car (ode-solutions r)) '(y x))))
  (let ((r (dsolve '(= (diff (diff (diff (y x) x) x) x) (/ (sin x) x)) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'quadrature)))

(deftest "ODE.1: вне методов — unknown, подделка отвергается"
  (assert-equal (ode-status (dsolve '(= (diff (y x) x) (+ (^ x 2) (^ (y x) 2))) '(y x))) 'unknown)
  (assert-equal (dsolve-check '(= (+ (diff (y x) x) (y x)) x)
                              '(= (y x) (+ C1 (* -1 (exp (* -1 x))) x))
                              '(y x))
                #f))
