; pde.lisp — каркас УрЧП (PDE.0): классификатор, диспетчер, pdsolve-check, входной язык.

(define (pdt-class eq uv) (pde-classify eq uv))
(define (pdt-ref c k) (pde-class-ref c k))

; строка таблицы: (имя уравнение (u …) тип порядок линейное квазилинейное образец)
(define *pdt-table*
  '(("тепло" (= u_t (* a u_xx)) (u x t) parabolic 2 #t #t heat)
    ("волна" (= u_tt (* (^ c 2) u_xx)) (u x t) hyperbolic 2 #t #t wave)
    ("Лаплас 2D" (+ u_xx u_yy) (u x y) elliptic 2 #t #t laplace)
    ("Пуассон" (= (+ u_xx u_yy) (f x y)) (u x y) elliptic 2 #t #t poisson)
    ("Гельмгольц" (+ u_xx u_yy (* (^ k 2) u)) (u x y) elliptic 2 #t #t helmholtz)
    ("тепло 2D" (= u_t (+ u_xx u_yy)) (u x y t) parabolic 2 #t #t heat)
    ("волна 2D" (= u_tt (+ u_xx u_yy)) (u x y t) hyperbolic 2 #t #t wave)
    ("Лаплас 3D" (+ u_xx u_yy u_zz) (u x y z) elliptic 2 #t #t laplace)
    ("бигармоническое" (+ u_xxxx (* 2 u_xxyy) u_yyyy) (u x y) elliptic 4 #t #t biharmonic)
    ("перенос" (+ u_t (* c u_x)) (u x t) first-order 1 #t #t transport)
    ("Бюргерс" (+ u_t (* u u_x)) (u x t) first-order 1 #f #t burgers)
    ("Трикоми" (+ u_xx (* x u_yy)) (u x y) unknown 2 #t #t none)
    ("параболическое смешанное" (+ u_xx (* 2 u_xy) u_yy) (u x y) parabolic 2 #t #t none)
    ("гиперболическое смешанное" (+ u_xx (* 4 u_xy) u_yy) (u x y) hyperbolic 2 #t #t none)
    ("полулинейное" (= u_t (+ u_xx (^ u 2))) (u x t) parabolic 2 #f #t none)
    ("телеграфное" (= u_tt (+ u_xx (* -2 u_t))) (u x t) hyperbolic 2 #t #t telegraph)
    ("нелинейное u_t = u_x²" (= u_t (^ u_x 2)) (u x t) first-order 1 #f #f none)))

(deftest "PDE.0: таблица классификации — тип, порядок, линейность, образец (17 уравнений)"
  (for-each
   (lambda (row)
     (let ((c (pdt-class (nth row 1) (nth row 2))) (nm (car row)))
       (assert-equal (list nm (pdt-ref c :type)) (list nm (nth row 3)))
       (assert-equal (list nm (pdt-ref c :order)) (list nm (nth row 4)))
       (assert-equal (list nm (pdt-ref c :linear)) (list nm (nth row 5)))
       (assert-equal (list nm (pdt-ref c :quasilinear)) (list nm (nth row 6)))
       (assert-equal (list nm (pdt-ref c :pattern)) (list nm (nth row 7)))))
   *pdt-table*))

(deftest "PDE.0: однородность, постоянные коэффициенты, условия, система координат"
  (let ((h (pdt-class '(= u_t (* a u_xx)) '(u x t)))
        (inh (pdt-class '(= u_t (+ u_xx (sin x))) '(u x t)))
        (var (pdt-class '(= u_t (* x u_xx)) '(u x t)))
        (cond0 (pde-classify '(= u_t u_xx) '(u x t) '(= (u 0 t) 0) '(= (at (diff (u x t) x) (= x L)) 0)))
        (cond1 (pde-classify '(= u_t u_xx) '(u x t) '(= (u x 0) (f x)) '(= (u 0 t) 0))))
    (assert-equal (pdt-ref h :homogeneous) #t)
    (assert-equal (pdt-ref h :const-coeff) #t)
    (assert-equal (pdt-ref h :bc-homogeneous) 'none)
    (assert-equal (pdt-ref inh :homogeneous) #f)
    (assert-equal (pdt-ref inh :linear) #t)
    (assert-equal (pdt-ref var :const-coeff) #f)
    (assert-equal (pdt-ref var :pattern) 'none)
    (assert-equal (pdt-ref cond0 :bc-homogeneous) #t)
    (assert-equal (pdt-ref cond1 :bc-homogeneous) #f)
    (assert-equal (pdt-ref h :coords) 'cartesian)
    (assert-equal (pdt-ref (pde-classify '(= u_t (* a u_xx)) '(u r phi)) :coords) 'polar)
    (assert-equal (pdt-ref (pde-classify '(= u_t (* a u_xx)) '(u r phi z)) :coords) 'cylindrical)
    (assert-equal (pdt-ref (pde-classify '(= u_t (* a u_xx)) '(u r theta phi)) :coords) 'spherical)
    (assert-equal (pdt-ref (pde-classify '(= u_t (* a u_xx)) '(u x t) :coords 'cylindrical) :coords) 'cylindrical)))

(deftest "PDE.0: тип с переменными коэффициентами — знак по sign-of, иначе unknown"
  ; x u_xx + u_yy: знак x неизвестен
  (assert-equal (pdt-ref (pdt-class '(+ (* x u_xx) u_yy) '(u x y)) :type) 'unknown)
  ; x² u_xx + u_yy: b² − ac = −x², «≠ 0» записывается условием
  (assert-equal (pdt-ref (pdt-class '(+ (* (^ x 2) u_xx) u_yy) '(u x y)) :type) 'elliptic)
  ; 4 u_xx + u_yy
  (assert-equal (pdt-ref (pdt-class '(+ (* 4 u_xx) u_yy) '(u x y)) :type) 'elliptic)
  (assert-equal (pdt-ref (pdt-class '(+ u_xx (* -4 u_yy)) '(u x y)) :type) 'hyperbolic))

(deftest "PDE.0: u_t, u_xx и diff — одна и та же классификация"
  (assert-equal (pde-classify '(= u_t (* a u_xx)) '(u x t))
                (pde-classify '(= (diff (u x t) t) (* a (diff (diff (u x t) x) x))) '(u x t)))
  (assert-equal (pde-diff-form 'u_xt 'u '(x t)) '(diff (diff (u x t) x) t))
  (assert-equal (pde-diff-form 'u_xx 'u '(x t)) '(diff (diff (u x t) x) x))
  ; вне объявленной неизвестной u_xx — обычный идентификатор
  (assert-equal (pde-diff-form 'v_xx 'u '(x t)) 'v_xx))

; ---------- сертификат ----------

(define *pdt-heat* '(= (diff (u x t) t) (diff (diff (u x t) x) x)))
(define *pdt-wave* '(= (diff (diff (u x t) t) t) (* (^ c 2) (diff (diff (u x t) x) x))))

(deftest "PDE.0: u = F(x − ct) + G(x + ct) для волнового уравнения → #t"
  (assert-equal (pdsolve-check *pdt-wave* '(= (u x t) (+ (F (+ x (* -1 c t))) (G (+ x (* c t))))) '(u x t)) #t))

(deftest "PDE.0: u = e^(−t) sin x для u_t = u_xx → #t; с u_t, u_xx в записи"
  (assert-equal (pdsolve-check *pdt-heat* '(= (u x t) (* (exp (* -1 t)) (sin x))) '(u x t)) #t)
  (assert-equal (pdsolve-check '(= u_t u_xx) '(= (u x t) (* (exp (* -1 t)) (sin x))) '(u x t)) #t)
  (assert-equal (pdsolve-check '(= u_t (* a u_xx)) '(= (u x t) (* (exp (* -1 a t)) (sin x))) '(u x t)) #t))

(deftest "PDE.0: u = e^(−4t) sin 2x с условиями u(0,t) = u(π,t) = 0 → #t; с начальным условием"
  (let ((sol '(= (u x t) (* (exp (* -4 t)) (sin (* 2 x))))))
    (assert-equal (pdsolve-check *pdt-heat* sol '(u x t) '(= (u 0 t) 0) '(= (u pi t) 0)) #t)
    (assert-equal (pdsolve-check *pdt-heat* sol '(u x t) '(= (u 0 t) 0) '(= (u pi t) 0) '(= (u x 0) (sin (* 2 x)))
                                 :domain '((x 0 pi) (t 0 inf))) #t)
    (assert-equal (pdsolve-check *pdt-heat* sol '(u x t) '(= (at (u x t) (= t 0)) (sin (* 2 x)))) #t)
    ; производная в условии: u_x(0,t) = 2 e^(−4t)
    (assert-equal (pdsolve-check *pdt-heat* sol '(u x t) '(= (u_x 0 t) (* 2 (exp (* -4 t))))) #t)
    (assert-equal (pdsolve-check *pdt-heat* sol '(u x t) '(= (at (diff (u x t) x) (= x 0)) (* 2 (exp (* -4 t))))) #t)
    ; неизвестная функция в данных — «не знаю», не #f
    (assert-equal (pdsolve-check *pdt-heat* sol '(u x t) '(= (u x 0) (f x))) 'unknown)))

(deftest "PDE.0: десять подделок → #f"
  (let ((h *pdt-heat*) (w *pdt-wave*) (uv '(u x t)))
    ; 1 не та скорость
    (assert-equal (pdsolve-check w '(= (u x t) (+ (F (+ x (* -2 c t))) (G (+ x (* c t))))) uv) #f)
    ; 2 знак затухания
    (assert-equal (pdsolve-check h '(= (u x t) (* (exp t) (sin x))) uv) #f)
    ; 3 не тот показатель
    (assert-equal (pdsolve-check h '(= (u x t) (* (exp (* -1 t)) (sin (* 2 x)))) uv) #f)
    ; 4 лишний множитель
    (assert-equal (pdsolve-check h '(= (u x t) (* t (exp (* -1 t)) (sin x))) uv) #f)
    (assert-equal (pdsolve-check h '(= (u x t) (* x (exp (* -1 t)) (sin x))) uv) #f)
    ; 5 нарушено краевое условие
    (assert-equal (pdsolve-check h '(= (u x t) (* (exp (* -1 t)) (cos x))) uv '(= (u 0 t) 0)) #f)
    (assert-equal (pdsolve-check h '(= (u x t) (* (exp (* -4 t)) (sin (* 2 x)))) uv '(= (u pi t) 1)) #f)
    ; 6 нарушено начальное условие
    (assert-equal (pdsolve-check h '(= (u x t) (* (exp (* -1 t)) (sin x))) uv '(= (u x 0) (sin (* 2 x)))) #f)
    ; 7 волновое: sin(x − 2t) при c = 1
    (assert-equal (pdsolve-check '(= (diff (diff (u x t) t) t) (diff (diff (u x t) x) x)) '(= (u x t) (sin (+ x (* -2 t)))) uv) #f)
    ; 8 Лаплас: x² + y²
    (assert-equal (pdsolve-check '(= (+ (diff (diff (u x y) x) x) (diff (diff (u x y) y) y)) 0)
                                 '(= (u x y) (+ (^ x 2) (^ y 2))) '(u x y)) #f)
    ; 9 Бюргерс: x/(1 + 2t)
    (assert-equal (pdsolve-check '(= (+ (diff (u x t) t) (* (u x t) (diff (u x t) x))) 0)
                                 '(= (u x t) (/ x (+ 1 (* 2 t)))) uv) #f)
    ; 10 перенос: F(x − 2ct) для u_t + c u_x = 0
    (assert-equal (pdsolve-check '(= (+ (diff (u x t) t) (* c (diff (u x t) x))) 0) '(= (u x t) (F (+ x (* -2 c t)))) uv) #f)))

(deftest "PDE.0: верные ответы других уравнений"
  (assert-equal (pdsolve-check '(= (+ (diff (diff (u x y) x) x) (diff (diff (u x y) y) y)) 0)
                               '(= (u x y) (+ (^ x 2) (* -1 (^ y 2)))) '(u x y)) #t)
  (assert-equal (pdsolve-check '(= (+ (diff (u x t) t) (* (u x t) (diff (u x t) x))) 0)
                               '(= (u x t) (/ x (+ 1 t))) '(u x t)) #t)
  (assert-equal (pdsolve-check '(= (+ (diff (u x t) t) (* c (diff (u x t) x))) 0) '(= (u x t) (F (+ x (* -1 c t)))) '(u x t)) #t)
  (assert-equal (pdsolve-check '(= u_t (+ u_xx u_yy)) '(= (u x y t) (* (exp (* -2 t)) (sin x) (sin y))) '(u x y t)) #t)
  ; Гельмгольц с голым u
  (assert-equal (pdsolve-check '(= (+ u_xx u_yy (* 2 u)) 0) '(= (u x y) (* (sin x) (sin y))) '(u x y)) #t))

(deftest "PDE.0: bounded — ограниченность в точке (предел)"
  (let ((lap '(= (+ (diff (diff (u x y) x) x) (diff (diff (u x y) y) y)) 0)))
    (assert-equal (pdsolve-check lap '(= (u x y) (+ (^ x 2) (* -1 (^ y 2)))) '(u x y) '(bounded (u x y) (= x 0))) #t)
    (assert-equal (pdsolve-check lap '(= (u x y) (log (+ (^ x 2) (^ y 2)))) '(u x y)
                                 '(bounded (u x y) ((= x 0) (= y 0)))) #f)))

(deftest "PDE.0: произвольные функции данных: d'Alembert-образная проверка условий"
  ; u = (φ(x−ct) + φ(x+ct))/2 : u(x,0) = φ(x) выполняется тождественно
  (let ((sol '(= (u x t) (* 1/2 (+ (phi (+ x (* -1 c t))) (phi (+ x (* c t))))))))
    (assert-equal (pdsolve-check *pdt-wave* sol '(u x t) '(= (u x 0) (phi x))) #t)
    (assert-equal (pdsolve-check *pdt-wave* sol '(u x t) '(= (at (diff (u x t) t) (= t 0)) 0)) #t)))

; ---------- диспетчер ----------

(deftest "PDE.0: pdsolve — unknown с перечнем методов, без ложных «решения нет»"
  (let ((r (pdsolve '(= u_t (* a u_xx)) '(u x t) '(= (u x 0) (f x)) '(= (u 0 t) 0) '(= (u L t) 0)
                    :domain '((x 0 L) (t 0 inf)))))
    (assert-equal (pde-status r) 'unknown)
    (assert-equal (pde-solutions r) '())
    (assert-equal (pde-term r) '())
    (assert-true (member? 'separation (pde-field r :hint)))
    (assert-equal (pde-class-ref (pde-field r :class) :pattern) 'heat))
  (let ((r (pdsolve '(= u_tt u_xx) '(u x t) :domain '((x -inf inf) (t 0 inf)))))
    (assert-true (member? 'dalembert (pde-field r :hint))))
  (assert-equal (pde-field (pdsolve '(= (+ u_t (* c u_x)) 0) '(u x t)) :hint) '(characteristics))
  ; нелинейное: методов нет, но ответ — unknown, не «нет решения»
  (let ((r (pdsolve '(= u_t (+ u_xx (^ u 3))) '(u x t))))
    (assert-equal (pde-status r) 'unknown)
    (assert-equal (pde-field r :hint) '())))

(deftest "PDE.0: pdsolve — доказуемая несовместность условий"
  (assert-equal (pde-status (pdsolve '(= u_t u_xx) '(u x t) '(= (u 0 t) 0) '(= (u 0 t) 1))) 'inconsistent)
  ; значение в вложенной точке: u(x,0) = 1 и u(0,0) = 2
  (assert-equal (pde-status (pdsolve '(= u_t u_xx) '(u x t) '(= (u x 0) 1) '(= (u 0 0) 2))) 'inconsistent)
  ; не противоречие: разные точки
  (assert-equal (pde-status (pdsolve '(= u_t u_xx) '(u x t) '(= (u 0 t) 0) '(= (u 1 t) 1))) 'unknown)
  ; функция в данных несовместность не доказывает
  (assert-equal (pde-status (pdsolve '(= u_t u_xx) '(u x t) '(= (u 0 t) (f t)) '(= (u 0 t) (g t)))) 'unknown))

; ---------- входной язык ----------

(deftest "PDE.0: входной язык — pde_check, u_t, u_xx, условия, область"
  (assert-equal (math-show (math-eval "pde_check(u_t = u_xx, u(x,t) = exp(-t)*sin(x), u(x,t))")) "true")
  (assert-equal (math-show (math-eval "pde_check(u_t = u_xx, u(x,t) = exp(-4*t)*sin(2*x), u(x,t), u(0,t) = 0, u(pi,t) = 0, u(x,0) = sin(2*x), [x, 0, pi], [t, 0, inf])")) "true")
  (assert-equal (math-show (math-eval "pde_check(u_t = u_xx, u(x,t) = exp(-3*t)*sin(2*x), u(x,t))")) "false")
  (assert-equal (math-show (math-eval "pde_check(u_tt = c^2*u_xx, u(x,t) = F(x - c*t) + G(x + c*t), u(x,t))")) "true")
  (assert-equal (math-show (math-eval "pde_check(u_tt = c^2*u_xx, u(x,t) = F(x - 2*c*t) + G(x + c*t), u(x,t))")) "false")
  (assert-equal (math-show (math-eval "pde_check(laplacian(u(x,y), [x,y]) = 0, u(x,y) = x^2 - y^2, u(x,y))")) "true")
  (assert-equal (math-show (math-eval "pde_check(diff(u(x,t), x, 2) = diff(u(x,t), t), u(x,t) = exp(-t)*sin(x), u(x,t))")) "true")
  (assert-equal (math-show (math-eval "pde_check(u_t = u_xx, u(x,t) = exp(-t)*sin(x), u(x,t), u_x(0,t) = 1)")) "false")
  (assert-equal (math-show (math-eval "pde_check(u_t = u_xx, u(x,t) = exp(-t)*sin(x), u(x,t), u(0,t) = 0, bounded(u(x,t), x = 0))")) "true"))

(deftest "PDE.0: входной язык — pdsolve и pde_classify; u_xx вне pdsolve — идентификатор"
  (let ((r (math-eval "pdsolve(u_t = a*u_xx, u(x,t), u(x,0) = f(x), u(0,t) = 0, u(L,t) = 0, [x, 0, L], [t, 0, inf])")))
    (assert-equal (pde-status r) 'unknown)
    (assert-equal (pde-class-ref (pde-field r :class) :type) 'parabolic))
  (assert-equal (pde-class-ref (math-eval "pde_classify(u_tt = c^2*u_xx, u(x,t))") :type) 'hyperbolic)
  (assert-equal (math-eval "u_xx") 'u_xx))

(deftest "PDE.0: шаги pde-classify и pde-check в журнале"
  (let ((rs (step-rules (cadr (capture-step-log
                               (lambda () (begin (pde-classify '(= u_t u_xx) '(u x t))
                                                 (pdsolve-check *pdt-heat* '(= (u x t) (* (exp (* -1 t)) (sin x))) '(u x t)))))))))
    (assert-true (member? 'pde-classify rs))
    (assert-true (member? 'pde-check rs))))

(deftest "PDE.0: ошибки аргументов"
  (assert-error (pdsolve '(= u_t u_xx) '(u x)))
  (assert-error (pdsolve-check '(= u_t u_xx) 0 '(u)))
  (assert-error (pdsolve-check '(= u_t u_xx) '(= (u x t) 0) '(u x t) '(+ 1 2))))
