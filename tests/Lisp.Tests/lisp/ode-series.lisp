; ode-series.lisp — тесты шага ODE.7: решения линейных ОДУ степенными рядами и метод Фробениуса.

; ---------- обыкновенная точка ----------

(deftest "ODE.7a: y'' + y = 0 — ряд и замкнутый вид cos/sin"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (y x)) 0))
         (r (dsolve-series eq '(y x) 0 8)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'series)
    (assert-equal (ode::ode-field r :closed-form) #t)
    (assert-equal (ode::ode-field r :radius) 'inf)
    (assert-equal (car (ode-solutions r))
                  '(= (y x) (+ (* C1 (cos x)) (* C2 (sin x)))))))

(deftest "ODE.7a: y'' + y = 0 — первые члены и рекуррентность в :series и :recurrence"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (y x)) 0))
         (r (dsolve-series eq '(y x) 0 6))
         (ser (ode::ode-field r :series))
         (rec (ode::ode-field r :recurrence)))
    ; a₂ = −a₀/2, a₃ = −a₁/6, a₄ = a₀/24
    ; ODE.7c: в обыкновенной точке определяющего уравнения нет — :indicial/:exponents не выдаются
    (assert-equal (ode::ode-field r :indicial) #f)
    (assert-equal (ode::ode-field r :exponents) #f)
    (assert-true (pair? rec))
    (assert-true (pair? ser))
    ; :series — общее решение C1·y₁ + C2·y₂, а не их сумма
    (assert-true (ode::ode-has-head? ser 'C1))
    (assert-true (ode::ode-has-head? ser 'C2))))

(deftest "ODE.7a: y' = y (порядок 1) — e^x"
  (let* ((eq '(= (diff (y x) x) (y x)))
         (r (dsolve-series eq '(y x) 0 8)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (car (ode-solutions r)) '(= (y x) (* C1 (exp x))))))

(deftest "ODE.7a: Эйри y'' − xy = 0 — рекуррентность a_{k+2} = a_{k−1}/((k+2)(k+1)), радиус ∞"
  (let* ((eq '(= (- (diff (diff (y x) x) x) (* x (y x))) 0))
         (r (dsolve-series eq '(y x) 0 10))
         (ser (ode::ode-field r :series)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :radius) 'inf)
    ; y = C1(1 + x³/6 + …) + C2(x + x⁴/12 + …)
    (assert-true (ode::ode-has-head? ser '^))
    (assert-true (ode-series-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.7a: Эрмит y'' − 2xy' + 6y = 0 при n = 3 — полином"
  (let* ((eq '(= (+ (- (diff (diff (y x) x) x) (* 2 x (diff (y x) x))) (* 6 (y x))) 0))
         (r (dsolve-series eq '(y x) 0 10))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    ; чётная ветвь обрывается: C1(1 − 3x²) — полином степени 2 (P₃ через y = z·e^{x²/2})
    (assert-true (ode::ode-has-head? sol 'C1))
    (assert-true (ode-series-check eq sol '(y x)))))

(deftest "ODE.7a: Лежандр (1−x²)y'' − 2xy' + 6y = 0 — радиус 1"
  (let* ((eq '(= (+ (- (* (- 1 (^ x 2)) (diff (diff (y x) x) x)) (* 2 x (diff (y x) x)))
                    (* 6 (y x)))
                 0))
         (r (dsolve-series eq '(y x) 0 10)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :radius) 1)
    (assert-true (ode-series-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.7a: y' = y в точке x0 = 1 — ряд по (x − 1)"
  (let* ((eq '(= (diff (y x) x) (y x)))
         (r (dsolve-series eq '(y x) 1 6))
         (ser (ode::ode-field r :series)))
    (assert-equal (ode-status r) 'ok)
    ; переменная сдвинута: замкнутый вид e^{x−1}, ряд по (x − 1)
    (assert-true (ode::ode-has-head? (car (ode-solutions r)) 'exp))
    (assert-true (ode::ode-has-head? ser '^))))

(deftest "ODE.7a: задача Коши y(0)=1, y'(0)=0 для Эйри — частное решение"
  (let* ((eq '(= (- (diff (diff (y x) x) x) (* x (y x))) 0))
         (r (dsolve-series eq '(y x) 0 10 '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-equal (ode::ode-field r :constants) '())
    ; a₀ = 1, a₁ = 0 → только ветвь C1
    (assert-true (ode-series-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.7a: ряд без условий Коши — две свободные константы"
  (let* ((r (dsolve-series '(= (- (diff (diff (y x) x) x) (* x (y x))) 0) '(y x))))
    (assert-equal (ode::ode-field r :constants) '(C1 C2))))

(deftest "ODE.7a: нелинейное уравнение — #f (честно вне метода)"
  (assert-equal (dsolve-series '(= (diff (y x) x) (^ (y x) 2)) '(y x)) #f)
  (assert-equal (dsolve-series '(= (diff (y x) x) (+ x (sin x))) '(y x)) #f))

(deftest "ODE.7a: подделка не проходит сертификат"
  ; верное решение y = cos x, но подставлен неверный коэффициент ряда
  (assert-equal (ode-series-check '(= (+ (diff (diff (y x) x) x) (y x)) 0)
                                  '(= (y x) (+ 1 (* -1 (^ x 2)) (* 1/24 (^ x 4))))
                                  '(y x))
                #f))


; ---------- регулярная особая точка: Фробениус ----------

(deftest "ODE.7b: Бессель ν = 1/2 — sin x/√x и cos x/√x (разность корней 1, лога нет)"
  (let* ((eq '(= (+ (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x)))
                    (* (- (^ x 2) 1/4) (y x)))
                 0))
         (r (dsolve-series eq '(y x) 0 12))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :exponents) '(1/2 -1/2))
    (assert-equal (ode::ode-field r :closed-form) #t)
    (assert-equal sol '(= (y x) (+ (* C1 (^ x -1/2) (sin x)) (* C2 (^ x -1/2) (cos x)))))
    (assert-true (ode-series-check eq sol '(y x)))))

(deftest "ODE.7b: Бессель ν = 0 — равные корни, вторая ветвь с log x"
  (let* ((eq '(= (+ (* x x (diff (diff (y x) x) x)) (* x (diff (y x) x)) (* (^ x 2) (y x))) 0))
         (r (dsolve-series eq '(y x) 0 10))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :exponents) '(0 0))
    (assert-equal (ode::ode-field r :method) 'frobenius)
    (assert-true (ode::ode-has-head? sol 'log))
    ; SFn.2b: первая ветвь замкнулась в J_0 (прежде — hyper); сертификат тот же
    (assert-true (ode::ode-has-head? sol 'bessel-j))
    (assert-true (ode-series-check eq sol '(y x)))))

(deftest "ODE.7b: Бессель ν = 1 — разность корней 2, лог-член есть"
  (let* ((eq '(= (+ (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x)))
                    (* (- (^ x 2) 1) (y x)))
                 0))
         (r (dsolve-series eq '(y x) 0 10))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :exponents) '(1 -1))
    (assert-true (ode::ode-has-head? sol 'log))
    (assert-true (ode-series-check eq sol '(y x)))))

(deftest "ODE.7b: x·y'' + y = 0 — Фробениус, определяющее уравнение r(r−1) = 0"
  (let* ((eq '(= (+ (* x (diff (diff (y x) x) x)) (y x)) 0))
         (r (dsolve-series eq '(y x) 0 10)))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :exponents) '(1 0))
    (assert-equal (ode::ode-field r :indicial) '(* rr (+ -1 rr)))
    (assert-true (ode::ode-has-head? (car (ode-solutions r)) 'log))
    (assert-true (ode-series-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.7b: гипергеометрическое x(1−x)y'' + (2−3x)y' − y = 0 → −log(1−x)/x"
  (let* ((eq '(= (+ (+ (* x (- 1 x) (diff (diff (y x) x) x)) (* (- 2 (* 3 x)) (diff (y x) x)))
                    (* -1 (y x)))
                 0))
         (r (dsolve-series eq '(y x) 0 12))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :exponents) '(0 -1))
    ; ₂F₁(1,1;2;x)/x = −log(1−x)/x
    (assert-true (ode::ode-has-head? sol 'log))
    (assert-true (ode-series-check eq sol '(y x)))))

(deftest "ODE.7b: Эйлер–Коши как частный случай — x²y'' − 2xy' + 2y = 0 → C1x + C2x²"
  (let* ((eq '(= (+ (- (* (^ x 2) (diff (diff (y x) x) x)) (* 2 x (diff (y x) x))) (* 2 (y x))) 0))
         (r (dsolve-series eq '(y x) 0 10))
         (sol (car (ode-solutions r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :exponents) '(2 1))
    (assert-equal sol '(= (y x) (+ (* C1 (^ x 2)) (* C2 x))))))

(deftest "ODE.7b: иррегулярная особая точка x³y'' + y = 0 — unknown"
  (let ((r (dsolve-series '(= (+ (* (^ x 3) (diff (diff (y x) x) x)) (y x)) 0) '(y x) 0 8)))
    ; honest failure: no series answer, status — причина отказа
    (assert-true (not (equal? (ode-status r) 'ok)))
    (assert-equal (ode-solutions r) '())))

(deftest "ODE.7b: подделка второй ветви Бесселя отвергается"
  ; неверный показатель степени: x^{1/2}·cos x вместо x^{−1/2}·cos x
  (assert-equal (ode-series-check '(= (+ (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x)))
                                         (* (- (^ x 2) 1/4) (y x)))
                                      0)
                                  '(= (y x) (+ (* C1 (^ x -1/2) (sin x)) (* C2 (^ x 1/2) (cos x))))
                                  '(y x))
                #f))

; ---------- подключение к dsolve ----------

(deftest "ODE.7: dsolve для линейного уравнения без элементарного решения — ряд"
  ; ODE.9: x²y″ + xy′ + x²y = 0 — уравнение Бесселя ν = 0, теперь замкнутый ответ через bessel-j
  (let* ((eq '(= (+ (* x (diff (diff (y x) x) x)) (diff (y x) x) (* x (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :method) 'specfun)
    (assert-true (string-contains? (to-string (ode-solutions r)) "(bessel-j 0")))
  ; вне классов ODE.9 ряд остаётся
  (let* ((eq2 '(= (+ (diff (diff (y x) x) x) (* (+ x (^ x 2)) (y x))) 0))
         (r2 (dsolve eq2 '(y x))))
    (assert-equal (ode-status r2) 'ok)
    (assert-equal (ode::ode-field r2 :method) 'series)
    (assert-true (ode-series-check eq2 (car (ode-solutions r2)) '(y x)))))

(deftest "ODE.7: dsolve с условиями Коши в обыкновенной точке — частное решение"
  (let* ((eq '(= (- (diff (diff (y x) x) x) (* x (y x))) 0))
         (r (dsolve eq '(y x) '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-true (ode-series-check eq (car (ode-solutions r)) '(y x)))))

(deftest "ODE.7: постоянные коэффициенты по-прежнему решаются точно (не рядом)"
  (let* ((r (dsolve '(= (+ (diff (diff (y x) x) x) (y x)) 0) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-true (not (member? (ode::ode-field r :method) '(series frobenius))))))

; ---------- ODE.7c: доработка по ревью ----------

(define *bessel0*
  '(= (+ (* x x (diff (diff (y x) x) x)) (* x (diff (y x) x)) (* (^ x 2) (y x))) 0))

(deftest "ODE.7c: Бессель ν=0 — верный y₂ с log x проходит сертификат"
  ; y₂ = x²/4 − 3x⁴/128 + (1 − x²/4 + x⁴/64)·log x
  (assert-true (ode-series-check *bessel0*
                                 '(= (y x) (+ (- (* (^ x 2) 1/4) (* 3 (^ x 4) 1/128))
                                              (* (- 1 (* (^ x 2) 1/4) (* -1 (^ x 4) 1/64)) (log x))))
                                 '(y x))))

(deftest "ODE.7c: log-случай — подделка коэффициента при x⁴ отвергается"
  ; −1/32 вместо −3/128 в многочленной части (A-часть остатка ненулевая в члене x⁴)
  (assert-equal (ode-series-check *bessel0*
                                  '(= (y x) (+ (- (* (^ x 2) 1/4) (* (^ x 4) 1/32))
                                               (* (- 1 (* (^ x 2) 1/4) (* (^ x 4) 1/64)) (log x))))
                                  '(y x))
                #f))

(deftest "ODE.7c: log-случай — подделка многочленной части отвергается"
  ; x²/3 вместо x²/4 и коэффициент при log без членов x⁴
  (assert-equal (ode-series-check *bessel0*
                                  '(= (y x) (+ (* (^ x 2) 1/3) (* (- 1 (* (^ x 2) 1/4)) (log x))))
                                  '(y x))
                #f))

(deftest "ODE.7c: log-случай — «₀F₁(;1;−x²/4)·log x» (не решение) отвергается"
  (assert-equal (ode-series-check *bessel0*
                                  '(= (y x) (* (hyper nil (1) (* -1/4 (^ x 2))) (log x)))
                                  '(y x))
                #f))

(deftest "ODE.7c: log-случай — y₂ + 2·₀F₁(;1;−x²/4) — это решение, не #f"
  ; верный y₂ плюс 2·y₁ — законное решение однородного уравнения
  (assert-true (not (equal? (ode-series-check *bessel0*
                                              '(= (y x) (+ (+ (- (* (^ x 2) 1/4) (* 3 (^ x 4) 1/128))
                                                              (* (- 1 (* (^ x 2) 1/4) (* -1 (^ x 4) 1/64)) (log x)))
                                                           (* 2 (hyper nil (1) (* -1/4 (^ x 2))))))
                                              '(y x))
                        #f))))

(deftest "ODE.7c: радиус в особой точке — расстояние до ДРУГОЙ особой точки"
  ; Бессель ν=0 в 0: особая точка одна (сама 0) → inf
  (let ((r (dsolve-series *bessel0* '(y x) 0 10)))
    (assert-equal (ode::ode-field r :radius) 'inf))
  ; x·y'' + y = 0 в 0 → inf
  (let ((r (dsolve-series '(= (+ (* x (diff (diff (y x) x) x)) (y x)) 0) '(y x) 0 10)))
    (assert-equal (ode::ode-field r :radius) 'inf))
  ; Лежандр (1−x²)y'' − 2xy' + 6y = 0 в 0: другая особая точка ±1 → 1
  (let ((r (dsolve-series '(= (+ (- (* (- 1 (^ x 2)) (diff (diff (y x) x) x))
                                    (* 2 x (diff (y x) x)))
                                 (* 6 (y x)))
                               0)
                          '(y x) 0 10)))
    (assert-equal (ode::ode-field r :radius) 1)))

(deftest "ODE.7c: :series в Фробениусе — общее решение с C1 и C2"
  (let* ((r (dsolve-series *bessel0* '(y x) 0 10))
         (ser (ode::ode-field r :series)))
    (assert-true (ode::ode-has-head? ser 'C1))
    (assert-true (ode::ode-has-head? ser 'C2))
    ; константы входят множителями, а не потеряны в сумме ветвей
    (assert-true (contains-sym? ser 'C1))
    (assert-true (contains-sym? ser 'C2))))

