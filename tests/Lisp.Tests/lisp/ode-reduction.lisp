; ode-reduction.lisp — тесты шага ODE.5b: понижение порядка и автономные уравнения.

; ---------- известное решение: формула Абеля ----------

(deftest "ODE.5b: x²y'' − 3xy' + 4y = 0 при y₁ = x² → y₂ = x²·log x"
  (let* ((eq '(= (+ (- (* x x (diff (diff (y x) x) x)) (* 3 x (diff (y x) x)))
                   (* 4 (y x))) 0))
         (r (reduce-order eq '(y x) '(^ x 2))))
    (assert-true (pair? r))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'reduction)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r))
                  '(= (y x) (+ (* C1 (^ x 2)) (* C2 (^ x 2) (log x)))))))

(deftest "ODE.5b: (1 − x²)y'' − 2xy' + 2y = 0 при y₁ = x — решение сертифицируется"
  (let* ((eq '(= (+ (- (diff (diff (y x) x) x) (* (^ x 2) (diff (diff (y x) x) x)))
                   (* -2 x (diff (y x) x))
                   (* 2 (y x)))
                0))
         (r (reduce-order eq '(y x) 'x))
         (sol (if r (car (ode-solutions r)) #f)))
    (assert-true (pair? r))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    ; второе решение содержит log
    (assert-true (ode::ode-has-head? sol 'log))))

(deftest "ODE.5b: reduce-order — неверное y₁ даёт #f (решение не сертифицируется)"
  ; y₁ = e^x не решение y'' − y = 0? — решение; берём заведомо неверное y₁ = x
  (assert-equal (reduce-order '(= (- (diff (diff (y x) x) x) (* 4 (y x))) 0) '(y x) 'x) #f))

(deftest "ODE.5b: reduce-order — порядок не 2 → #f"
  (assert-equal (reduce-order '(= (diff (y x) x) (y x)) '(y x) 'x) #f))

; ---------- нет y: F(x, y′, y″) = 0 ----------

(deftest "ODE.5b: y'' = (y')² (без y) — y = −log(C1 − x) + C2"
  (let* ((eq '(= (diff (diff (y x) x) x) (^ (diff (y x) x) 2)))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'drop-y)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (length (ode::ode-field r :constants)) 2)
    (assert-true (dsolve-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.5b: y'' + y' = x (без y) — линейное по y′"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (diff (y x) x)) x))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    ; y = C1 + C2·e^{−x} + x²/2 − x
    (assert-equal (car (ode-solutions r))
                  '(= (y x) (+ C1 (* -1 x) (* 1/2 (^ x 2)) (* C2 (exp (* -1 x))))))))

(deftest "ODE.5b: ode-drop-y не срабатывает, когда y есть в уравнении"
  (assert-equal (ode-drop-y '(= (+ (diff (diff (y x) x) x) (y x)) 0) '(y x)) #f))

; ---------- автономные: F(y, y′, y″) = 0 ----------

(deftest "ODE.5b: y·y'' = (y')² (автономное) — y = C1·e^{C2 x}"
  (let* ((eq '(= (* (y x) (diff (diff (y x) x) x)) (^ (diff (y x) x) 2)))
         (r (dsolve eq '(y x)))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'autonomous)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (length (ode::ode-field r :constants)) 2)
    (assert-equal sol '(= (y x) (* C1 (exp (* C2 x)))))
    (assert-true (dsolve-check eq sol '(y x)))))

(deftest "ODE.5b: y'' = (y')² (автономное тоже) — решение сертифицируется"
  (let* ((eq '(= (diff (diff (y x) x) x) (^ (diff (y x) x) 2)))
         (r (ode-autonomous eq '(y x))))
    (assert-true (pair? r))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (length (ode::ode-field r :constants)) 2)))

(deftest "ODE.5b: ode-autonomous не срабатывает при явной зависимости от x"
  (assert-equal (ode-autonomous '(= (+ (diff (diff (y x) x) x) (* x (y x))) 0) '(y x)) #f))

(deftest "ODE.5b: автономное с нерешаемым p-уравнением — #f, а dsolve даёт unknown"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (^ (diff (y x) x) 3) (y x)) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'unknown)
    (assert-equal (ode-solutions r) '())))
