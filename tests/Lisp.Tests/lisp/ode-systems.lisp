; ode-systems.lisp — тесты шага ODE.5a: системы линейных ОДУ с постоянными коэффициентами.

; ---------- однородные системы ----------

(deftest "ODE.5a: x' = y, y' = −x — cos/sin"
  (let* ((eqs '((= (diff (x t) t) (y t)) (= (diff (y t) t) (* -1 (x t)))))
         (r (dsolve-system eqs '(x y) 't)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'system)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (length (ode-solutions r)) 2)
    (assert-true (dsolve-system-check eqs (ode-solutions r) '(x y) 't))))

(deftest "ODE.5a: x' = y, y' = −x — ответ в вещественной форме (cos, sin), вид (x t)"
  (let* ((r (dsolve-system '((= (diff (x t) t) (y t)) (= (diff (y t) t) (* -1 (x t))))
                            '(x y) 't))
         (sols (ode-solutions r)))
    (assert-equal (car sols) '(= (x t) (+ (* C1 (cos t)) (* C2 (sin t)))))
    (assert-equal (cadr sols) '(= (y t) (+ (* -1 C1 (sin t)) (* C2 (cos t)))))))

(deftest "ODE.5a: x' = 3x + y, y' = x + 3y — собственные 2 и 4"
  (let* ((eqs '((= (diff (x t) t) (+ (* 3 (x t)) (y t)))
                (= (diff (y t) t) (+ (x t) (* 3 (y t))))))
         (r (dsolve-system eqs '(x y) 't)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    ; собственные: λ=2 с вектором (1, −1), λ=4 с (1, 1)
    (assert-true (dsolve-system-check eqs
                                      '((= (x t) (+ (* A (exp (* 2 t))) (* B (exp (* 4 t)))))
                                        (= (y t) (+ (* -1 A (exp (* 2 t))) (* B (exp (* 4 t))))))
                                      '(x y) 't))))

(deftest "ODE.5a: жорданова клетка x' = x + y, y' = y — t·e^t"
  (let* ((eqs '((= (diff (x t) t) (+ (x t) (y t))) (= (diff (y t) t) (y t))))
         (r (dsolve-system eqs '(x y) 't))
         (sols (ode-solutions r)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car sols) '(= (x t) (+ (* C1 (exp t)) (* C2 t (exp t)))))
    (assert-equal (cadr sols) '(= (y t) (* C2 (exp t))))))

(deftest "ODE.5a: комплексные собственные значения (1 −1; 1 1) — e^t·cos, e^t·sin"
  (let* ((eqs '((= (diff (y t) t) (* -1 (y1 t))) (= (diff (y1 t) t) (y t))))
         (r (dsolve-system eqs '(y y1) 't)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (dsolve-system-check eqs (ode-solutions r) '(y y1) 't))))

; ---------- неоднородные ----------

(deftest "ODE.5a: неоднородная x' = y, y' = −x + 1 — частное x = 1"
  (let* ((eqs '((= (diff (x t) t) (y t)) (= (diff (y t) t) (+ (* -1 (x t)) 1))))
         (r (dsolve-system eqs '(x y) 't)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r)) '(= (x t) (+ 1 (* C1 (cos t)) (* C2 (sin t)))))))

(deftest "ODE.5a: резонанс y' = y1, y1' = −4y + sin 2t — множитель t"
  (let* ((eqs '((= (diff (y t) t) (y1 t))
                (= (diff (y1 t) t) (+ (* -4 (y t)) (sin (* 2 t))))))
         (r (dsolve-system eqs '(y y1) 't))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (ode::ode-has-head? sol 'cos))
    ; частное содержит t·cos 2t (резонанс)
    (assert-equal sol '(= (y t) (+ (* C1 (cos (* 2 t))) (* 1/2 C2 (sin (* 2 t)))
                                   (* -1/4 t (cos (* 2 t))) (* 1/8 (sin (* 2 t))))))))

(deftest "ODE.5a: система с переменной матрицей не решается — unknown"
  (let ((r (dsolve-system '((= (diff (x t) t) (* t (y t))) (= (diff (y t) t) (x t))) '(x y) 't)))
    (assert-true (not (equal? (ode-status r) 'ok)))
    (assert-equal (ode-solutions r) '())))
; ---------- задача Коши для системы ----------

(deftest "ODE.5a: Коши y' = y, y(0) = 2 → 2e^t"
  (let ((r (dsolve-system '((= (diff (y t) t) (y t))) '(y) 't '(= (y 0) 2))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r)) '(= (y t) (* 2 (exp t))))))

(deftest "ODE.5a: Коши для 2×2, условия в точке t = 1"
  (let* ((eqs '((= (diff (y t) t) (y1 t)) (= (diff (y1 t) t) (* -1 (y1 t)))))
         (r (dsolve-system eqs '(y y1) 't '(= (y 1) 1) '(= (y1 1) 2))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (dsolve-system-check eqs (ode-solutions r) '(y y1) 't))))

(deftest "ODE.5a: Коши — нераспознанное условие даёт unknown с причиной"
  (let ((r (dsolve-system '((= (diff (y t) t) (y t))) '(y) 't '(= (z 0) 2))))
    (assert-true (not (equal? (ode-status r) 'ok)))
    (assert-equal (ode-solutions r) '())))

; ---------- сертификат и подделки ----------

(deftest "ODE.5a: сертификат — подделки отвергаются"
  (let ((eqs '((= (diff (x t) t) (y t)) (= (diff (y t) t) (* -1 (x t))))))
    (assert-equal (dsolve-system-check
                   eqs
                   '((= (x t) (+ (* C1 (cos t)) (* C2 (sin t))))
                     (= (y t) (+ (* -1 C1 (sin t)) (* C2 (cos t)))))
                   '(x y) 't)
                  #t)
    ; неверная компонента: y = 3·sin t
    (assert-equal (dsolve-system-check eqs
                                       '((= (x t) (cos t)) (= (y t) (* 3 (sin t))))
                                       '(x y) 't)
                  #f)
    ; неверный знак в y
    (assert-equal (dsolve-system-check eqs
                                       '((= (x t) (cos t)) (= (y t) (sin t)))
                                       '(x y) 't)
                  #f)))

(deftest "ODE.5a: сертификат принимает 3×3 с кратным корнем"
  (let* ((eqs '((= (diff (x t) t) (x t))
                (= (diff (y t) t) (+ (x t) (y t)))
                (= (diff (z t) t) (+ (y t) (z t)))))
         (r (dsolve-system eqs '(x y z) 't)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (car (ode-solutions r)) '(= (x t) (* C1 (exp t))))
    (assert-equal (length (ode-solutions r)) 3)))

; ---------- ОДУ → система ----------

(deftest "ODE.5a: ode->system — y'' + 3y' = y → два уравнения, имена y, y1"
  (let ((af (ode->system '(= (+ (diff (diff (y x) x) x) (* 3 (diff (y x) x))) (y x)) '(y x))))
    (assert-equal (cadr af) '((y x) (y1 x)))
    (assert-equal (car af) '((= (diff (y x) x) (y1 x))
                             (= (diff (y1 x) x) (+ (* -3 (y1 x)) (y x)))))))

(deftest "ODE.5a: система из ode->system решается и сертифицируется"
  (let* ((af (ode->system '(= (+ (diff (diff (y x) x) x) (y x)) 0) '(y x)))
         (r (dsolve-system (car af) (cadr af) 'x)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-true (dsolve-system-check (car af)
                                      '((= (y x) (cos x)) (= (y1 x) (* -1 (sin x))))
                                      (cadr af) 'x))))

