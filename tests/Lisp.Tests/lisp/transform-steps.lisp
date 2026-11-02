; ST.3в-1: шаги преобразований Лапласа, Z и Фурье — правило/свойство, разложение,
; обратное и проверка; ответы не меняются от включения журнала, brief ≤ 15 строк.

(define (tst-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (tst-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (tst-has? s sub) (string-contains? s sub))
(define (tst-rules thunk) (step-rules (cadr (capture-step-log thunk))))

(deftest "преобразования/шаги: L{t·e^t} — таблица, умножение на t, сдвиг по частоте"
  (let* ((off (laplace '(* t (exp t)) 't 's))
         (s (tst-text (lambda () (laplace '(* t (exp t)) 't 's)) 'brief))
         (rs (tst-rules (lambda () (laplace '(* t (exp t)) 't 's)))))
    ; L[t e^t] = 1/(s−1)^2; в точке s = 3 это 1/4
    (assert-true (< (abs (- (eval-num (subst (list '= 's 3) off)) 1/4)) 1e-9))
    (assert-true (member? 'lt-forward rs))
    (assert-true (member? 'lt-tpow rs))
    (assert-true (member? 'lt-exp rs))
    (assert-true (tst-has? s "Прямое преобразование Лапласа"))
    (assert-true (tst-has? s "умножение на t^n"))
    (assert-true (tst-has? s "сдвиг по частоте"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: L⁻¹{1/(s²+1)} = sin t — разложение и проверка"
  (let* ((off (inverse-laplace '(/ 1 (+ (^ s 2) 1)) 's 't))
         (s (tst-text (lambda () (inverse-laplace '(/ 1 (+ (^ s 2) 1)) 's 't)) 'brief))
         (rs (tst-rules (lambda () (inverse-laplace '(/ 1 (+ (^ s 2) 1)) 's 't)))))
    (assert-true (equal? (simplify off) (simplify '(sin t))))
    (assert-true (member? 'lt-inv-partial rs))
    (assert-true (member? 'lt-inv-check rs))
    (assert-true (tst-has? s "Разложение на простейшие дроби"))
    (assert-true (tst-has? s "Проверка обратного преобразования"))
    (assert-true (tst-has? s "проверено"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: L⁻¹{(s+3)/((s+1)(s+2))} — полюса и коэффициенты"
  (let* ((off (inverse-laplace '(/ (+ s 3) (* (+ s 1) (+ s 2))) 's 't))
         (s (tst-text (lambda () (inverse-laplace '(/ (+ s 3) (* (+ s 1) (+ s 2))) 's 't)) 'brief)))
    ; 2e^{−t} − e^{−2t} при t = 1
    (assert-true (< (abs (- (eval-num (subst (list '= 't 1) off))
                            (eval-num (subst (list '= 't 1) '(- (* 2 (exp (- t))) (exp (* -2 t))))))) 1e-9))
    (assert-true (tst-has? s "{-2, -1}"))
    (assert-true (tst-has? s "проверено"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: laplace-dsolve y''+y=θ(t−1) — уравнение, Y(s), условия, обратное, проверка"
  (let* ((eq '(= (+ (diff (diff (y t) t) t) (y t)) (heaviside (- t 1))))
         (ic '((= (y 0) 0) (= (at (diff (y t) t) (= t 0)) 0)))
         (r (capture-step-log (lambda () (laplace-dsolve eq '(y t) ic)) 'brief 'ru))
         (off (car r)) (s (steps-text (cadr r) 'brief 'ru))
         (rs (step-rules (cadr r))))
    (assert-true (equal? (ode-status off) 'ok))
    (assert-true (member? 'ld-transform rs))
    (assert-true (member? 'ld-ys rs))
    (assert-true (member? 'ld-inverse rs))
    (assert-true (member? 'ld-check rs))
    (assert-true (tst-has? s "Преобразованное уравнение"))
    (assert-true (tst-has? s "Изображение Y(s)"))
    (assert-true (tst-has? s "Начальные условия"))
    (assert-true (tst-has? s "Обратное преобразование"))
    (assert-true (tst-has? s "Проверка подстановкой"))
    (assert-true (tst-has? s "тождество проверено"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: Z{n} — умножение на n^k"
  (let* ((off (ztransform 'n 'n 'z))
         (s (tst-text (lambda () (ztransform 'n 'n 'z)) 'brief))
         (rs (tst-rules (lambda () (ztransform 'n 'n 'z)))))
    ; Z{n} = z/(z−1)^2; в точке z = 3 это 3/4
    (assert-true (< (abs (- (eval-num (subst (list '= 'z 3) off)) 3/4)) 1e-9))
    (assert-true (member? 'tz-forward rs))
    (assert-true (member? 'tz-rule rs))
    (assert-true (tst-has? s "умножение на n^k"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: обратное Z рациональное — разложение и проверка"
  (let* ((off (inverse-ztransform '(/ (* z (+ z 3)) (* (- z 1) (- z 2))) 'z 'n))
         (s (tst-text (lambda () (inverse-ztransform '(/ (* z (+ z 3)) (* (- z 1) (- z 2))) 'z 'n)) 'brief))
         (rs (tst-rules (lambda () (inverse-ztransform '(/ (* z (+ z 3)) (* (- z 1) (- z 2))) 'z 'n)))))
    (assert-true (equal? (simplify off) (simplify '(+ -4 (* 5 (^ 2 n))))))
    (assert-true (member? 'tz-inv-partial rs))
    (assert-true (member? 'tz-inv-check rs))
    (assert-true (tst-has? s "Разложение F(z)/z"))
    (assert-true (tst-has? s "проверено"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: zsolve a(n+1)−2a(n)=0, a(0)=1 — уравнение A(z) и проверка"
  (let* ((eq '(= (+ (a (+ n 1)) (* -2 (a n))) 0))
         (r (capture-step-log (lambda () (zsolve eq '(a n) (list '(= (a 0) 1)))) 'brief 'ru))
         (off (car r)) (s (steps-text (cadr r) 'brief 'ru))
         (rs (step-rules (cadr r))))
    (assert-true (equal? (simplify (caddr off)) (simplify '(^ 2 n))))
    (assert-true (member? 'tz-transform rs))
    (assert-true (member? 'tz-az rs))
    (assert-true (member? 'tz-check rs))
    (assert-true (tst-has? s "Преобразованное уравнение"))
    (assert-true (tst-has? s "Изображение A(z)"))
    (assert-true (tst-has? s "тождество проверено"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: Фурье e^{−|t|} — табличное правило"
  (let* ((off (fourier '(exp (- (abs t))) 't 'w))
         (s (tst-text (lambda () (fourier '(exp (- (abs t))) 't 'w)) 'brief))
         (rs (tst-rules (lambda () (fourier '(exp (- (abs t))) 't 'w)))))
    ; F = 2/(1+w²); при w = 1 это 1
    (assert-true (< (abs (- (eval-num (subst (list '= 'w 1) off)) 1)) 1e-9))
    (assert-true (member? 'tf-forward rs))
    (assert-true (member? 'tf-rule rs))
    (assert-true (tst-has? s "табличное значение"))
    (assert-true (<= (tst-lines s) 15))))

(deftest "преобразования/шаги: обратное Фурье 1/(1+w²) — разложение и проверка"
  (let* ((off (inverse-fourier '(/ 1 (+ 1 (^ w 2))) 'w 't))
         (s (tst-text (lambda () (inverse-fourier '(/ 1 (+ 1 (^ w 2))) 'w 't)) 'brief))
         (rs (tst-rules (lambda () (inverse-fourier '(/ 1 (+ 1 (^ w 2))) 'w 't)))))
    ; 1/2·e^{−|t|}; при t = 1 это 1/(2e)
    (assert-true (< (abs (- (eval-num (subst (list '= 't 1) off))
                            (eval-num (list '/ 1 (list '* 2 (list 'exp 1)))))) 1e-9))
    (assert-true (member? 'tf-inv-partial rs))
    (assert-true (member? 'tf-inv-check rs))
    (assert-true (tst-has? s "Обратное преобразование: разложение"))
    (assert-true (tst-has? s "проверено"))
    (assert-true (<= (tst-lines s) 15))))
