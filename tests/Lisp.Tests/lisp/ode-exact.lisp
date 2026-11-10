; ode-exact.lisp — тесты шага ODE.2: точные уравнения, интегрирующий множитель, Риккати, Клеро/Лагранж.

(deftest "ODE.2: точное уравнение (2xy+3)dx + (x²+4y)dy = 0"
  (let ((eq '(= (+ (+ (* 2 x (y x)) 3) (* (+ (^ x 2) (* 4 (y x))) (diff (y x) x))) 0)))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'exact)
      (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x))))))

(deftest "ODE.2: точное уравнение (y+e^x)dx + x dy = 0"
  (let ((eq '(= (+ (+ (y x) (exp x)) (* x (diff (y x) x))) 0)))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'exact)
      (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x))))))

(deftest "ODE.2: точное с cos: (y cos x)dx + sin x dy = 0"
  (let ((eq '(= (+ (* (y x) (cos x)) (* (sin x) (diff (y x) x))) 0)))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-true (if (equal? (ode::ode-field r :method) 'exact)
                       (dsolve-check eq (car (ode-solutions r)) '(y x))
                       (equal? (ode::ode-field r :check) #t))))))

(deftest "ODE.2: интегрирующий множитель μ(x): (x+y²)dx − 2xy dy = 0"
  (let ((eq '(= (+ (+ x (^ (y x) 2)) (* -2 x (y x) (diff (y x) x))) 0)))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'integrating-factor)
      (assert-true (if (equal? (ode::ode-field r :type) 'implicit)
                       (ode::ode-field r :check)
                       (dsolve-check eq (car (ode-solutions r)) '(y x)))))))

(deftest "ODE.2: интегрирующий множитель μ(y): y dx + (2x − y e^y) dy = 0"
  (let ((eq '(= (+ (y x) (* (+ (* 2 x) (* -1 (y x) (exp (y x)))) (diff (y x) x))) 0)))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'integrating-factor)
      (assert-true (if (equal? (ode::ode-field r :type) 'implicit)
                       (ode::ode-field r :check)
                       (dsolve-check eq (car (ode-solutions r)) '(y x)))))))

(deftest "ODE.2: интегрирующий множитель μ(xy): y(1+xy)dx + x(1−xy)dy = 0"
  (let ((eq '(= (+ (* (y x) (+ 1 (* x (y x)))) (* x (- 1 (* x (y x))) (diff (y x) x))) 0)))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'integrating-factor)
      (assert-true (ode::ode-field r :check)))))

(deftest "ODE.2: Риккати y′ = y² − 2/x² (частное y₁ = −2/x или 1/x)"
  (let ((eq '(= (diff (y x) x) (- (^ (y x) 2) (/ 2 (^ x 2))))))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'riccati)
      (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x))))))

(deftest "ODE.2: Риккати y′ = y² + 1 − x² (частное y₁ = x)"
  (let ((eq '(= (diff (y x) x) (- (+ (^ (y x) 2) 1) (^ x 2)))))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'riccati)
      (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x))))))

(deftest "ODE.2: Риккати без рационального частного — unknown (не «нет решения»)"
  (let ((r (dsolve '(= (diff (y x) x) (+ (^ (y x) 2) (exp x))) '(y x))))
    (assert-equal (ode-status r) 'unknown)))

(deftest "ODE.2: косметика — exp(k·log x) в ответе Риккати свёрнут в x^k (ревью ODE.2)"
  ; y′ = y² − 2/x² → y = −2/x + 1/(x⁴·(C1 + x^{−3}/3)), без exp(log x)
  (let* ((eq '(= (diff (y x) x) (- (^ (y x) 2) (/ 2 (^ x 2)))))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (not (ode::ode-has-head? sol 'log)))
    (assert-true (dsolve-check eq sol '(y x)))))

(deftest "ODE.2: Клеро y = xy′ + (y′)²; особое y = −x²/4"
  (let ((eq '(= (y x) (+ (* x (diff (y x) x)) (^ (diff (y x) x) 2)))))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'clairaut)
      (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x)))
      (let ((sing (ode::ode-field r :singular)))
        (assert-true (any? (lambda (s) (equal? (caddr s) (list '* -1/4 (^ 'x 2)))) sing))
        (assert-true (every? (lambda (s) (dsolve-check eq s '(y x))) sing))))))

(deftest "ODE.2: Клеро y = xy′ − ln y′; особое y = 1 + ln x"
  (let ((eq '(= (y x) (- (* x (diff (y x) x)) (log (diff (y x) x))))))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'clairaut)
      (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x))))))

(deftest "ODE.2: Лагранж y = 2xy′ + (y′)²"
  (let ((eq '(= (y x) (+ (* 2 x (diff (y x) x)) (^ (diff (y x) x) 2)))))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (assert-equal (ode::ode-field r :method) 'lagrange)
      (assert-true (ode::ode-field r :check)))))

(deftest "ODE.2: потерянное решение y = 0 при делении на y"
  (let ((eq '(= (diff (y x) x) (* x (^ (y x) 2)))))
    (let ((r (dsolve eq '(y x))))
      (assert-equal (ode-status r) 'ok)
      (let ((sing (ode::ode-field r :singular)))
        (assert-true (any? (lambda (s) (equal? (caddr s) 0)) sing))
        (assert-true (every? (lambda (s) (dsolve-check eq s '(y x))) sing))))))

(deftest "ODE.2: подделки отвергаются — неверный потенциал (лишнее слагаемое)"
  (assert-equal (ode::fo-implicit-check
                 '(= (+ (+ (* 2 x (y x)) 3) (* (+ (^ x 2) (* 4 (y x))) (diff (y x) x))) 0)
                 '(+ (* 3 x) (* 2 (^ y 2)) (* (^ x 2) y) (* -1 x))
                 '(/ (* -1 (+ 3 (* 2 x y))) (+ (^ x 2) (* 4 y)))
                 'y 'x)
                #f))

(deftest "ODE.2: подделка — неверный μ (не делает форму точной)"
  (assert-equal (ode::ex-exact-after-mu?
                 '(* -1 y (+ 1 (* x y)))
                 '(* x (- 1 (* x y)))
                 '(^ x -1) 'x 'y)
                #f))

(deftest "ODE.2: подделка — неверное частное решение Риккати"
  (assert-equal (dsolve-check '(= (diff (y x) x) (- (^ (y x) 2) (/ 2 (^ x 2))))
                              '(= (y x) (* 2 (^ x -1)))
                              '(y x))
                #f))

(deftest "ODE.2: подделка — неверная огибающая Клеро"
  (assert-equal (dsolve-check '(= (y x) (+ (* x (diff (y x) x)) (^ (diff (y x) x) 2)))
                              '(= (y x) (* -1/2 (^ x 2)))
                              '(y x))
                #f))
