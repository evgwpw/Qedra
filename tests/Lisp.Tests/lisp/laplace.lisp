; laplace.lisp — тесты шага TR.1: преобразование Лапласа, обратное, сертификат

; равенство выражений по s и t: после together или после expand разность — 0
(define (ltt-same? a b)
  (let ((d (- a b)))
    (or (equal? (simplify (together d)) 0)
        (equal? (simplify (expand d)) 0))))

(define (ltt-L f) (laplace f 't 's))
(define (ltt-inv F) (inverse-laplace F 's 't))

(deftest "LT: таблица"
  (assert-equal (ltt-L 1) (simplify '(^ s -1)))
  (assert-true (ltt-same? (ltt-L '(^ t 3)) '(* 6 (^ s -4))))
  (assert-true (ltt-same? (ltt-L '(exp (* 3 t))) '(^ (+ s -3) -1)))
  (assert-true (ltt-same? (ltt-L '(sin (* 2 t))) '(/ 2 (+ (^ s 2) 4))))
  (assert-true (ltt-same? (ltt-L '(cos (* 2 t))) '(/ s (+ (^ s 2) 4))))
  (assert-true (ltt-same? (ltt-L '(sinh (* 2 t))) '(/ 2 (+ (^ s 2) -4))))
  (assert-true (ltt-same? (ltt-L '(cosh (* 2 t))) '(/ s (+ (^ s 2) -4))))
  (assert-true (ltt-same? (ltt-L '(^ t 1/2)) '(* 1/2 (^ pi 1/2) (^ s -3/2)))))

(deftest "LT: t^2 e^{3t} и сдвиг по частоте"
  (assert-true (ltt-same? (ltt-L '(* (^ t 2) (exp (* 3 t)))) '(* 2 (^ (+ s -3) -3))))
  (assert-true (ltt-same? (ltt-L '(* (exp (* -1 t)) (sin (* 2 t)))) '(/ 2 (+ (^ (+ s 1) 2) 4)))))

(deftest "LT: умножение на t и деление на t"
  (assert-true (ltt-same? (ltt-L '(* t (sin t))) '(/ (* 2 s) (^ (+ (^ s 2) 1) 2))))
  (assert-true (ltt-same? (ltt-L '(/ (sin t) t)) '(+ (* 1/2 pi) (* -1 (atan s))))))

(deftest "LT: Хевисайд, запаздывание, дельта"
  (assert-true (ltt-same? (ltt-L '(heaviside (- t 1))) '(/ (exp (* -1 s)) s)))
  (assert-true (ltt-same? (ltt-L '(dirac (- t 2))) '(exp (* -2 s))))
  (assert-true (ltt-same? (ltt-L '(* (heaviside (- t 1)) (^ (- t 1) 2)))
                          '(* 2 (^ s -3) (exp (* -1 s)))))
  ; просеивание: g(t) δ(t−1) = g(1) δ(t−1)
  (assert-true (ltt-same? (ltt-L '(* (^ t 2) (dirac (- t 1)))) '(exp (* -1 s)))))

(deftest "LT: производная с начальным условием, интеграл"
  (assert-true (ltt-same? (ltt-L '(diff (f t) t))
                          '(+ (* s (laplace (f t) t s)) (* -1 (f 0)))))
  (assert-true (ltt-same? (ltt-L '(diff (diff (f t) t) t))
                          '(+ (* (^ s 2) (laplace (f t) t s)) (* -1 s (f 0))
                              (* -1 (at (diff (f t) t) (= t 0))))))
  (assert-true (ltt-same? (ltt-L '(integrate (f u) u 0 t)) '(/ (laplace (f t) t s) s)))
  ; известная функция: L[(sin t)'] = L[cos t]
  (assert-true (ltt-same? (ltt-L '(diff (sin t) t)) '(/ s (+ (^ s 2) 1)))))

(deftest "LT: свёртка sin * sin"
  (assert-true (ltt-same? (ltt-L '(convolve (sin t) (sin t) t)) '(^ (+ (^ s 2) 1) -2)))
  (assert-true (ltt-same? (convolve '(sin t) '(sin t) 't) '(* 1/2 (+ (sin t) (* -1 t (cos t)))))))

(deftest "LT: sin^2 через произведение в сумму"
  (assert-true (ltt-same? (ltt-L '(* (sin t) (sin t))) '(/ 2 (* s (+ (^ s 2) 4))))))

(deftest "LT: неизвестное — невычисленная форма"
  (assert-equal (laplace '(exp (^ t 2)) 't 's) '(laplace (exp (^ t 2)) t s)))

(deftest "LT: условие сходимости Re s > a"
  (let ((r (capture-conditions (lambda () (ltt-L '(exp (* 3 t)))))))
    (assert-true (member? '(> s 3) (map car (cadr r))))))

(deftest "LT: обратное — простейшие дроби"
  (assert-true (ltt-same? (ltt-inv '(/ 1 (* s (+ s 1)))) '(+ 1 (* -1 (exp (* -1 t))))))
  (assert-true (ltt-same? (ltt-inv '(/ (+ s 1) (+ (^ s 2) (* 2 s) 5))) '(* (exp (* -1 t)) (cos (* 2 t)))))
  (assert-true (ltt-same? (ltt-inv '(/ 1 (^ (- s 1) 3))) '(* 1/2 (^ t 2) (exp t)))))

(deftest "LT: обратное — кратные комплексные корни 1/(s^2+1)^2"
  ; (sin t − t cos t)/2
  (assert-true (ltt-same? (ltt-inv '(/ 1 (^ (+ (^ s 2) 1) 2))) '(* 1/2 (- (sin t) (* t (cos t))))))
  (assert-true (ltt-same? (ltt-inv '(/ s (^ (+ (^ s 2) 1) 2))) '(* 1/2 t (sin t)))))

(deftest "LT: обратное — запаздывание e^{-2s}/s^2"
  (assert-true (ltt-same? (ltt-inv '(/ (exp (* -2 s)) (^ s 2))) '(* (heaviside (- t 2)) (- t 2))))
  (assert-true (ltt-same? (ltt-inv '(exp (* -1 s))) '(dirac (- t 1))))
  (assert-equal (ltt-inv 1) '(dirac t)))

(deftest "LT: обратное — 1/(s^3 - 1): вещественный и комплексные корни"
  (let ((r (ltt-inv '(/ 1 (+ (^ s 3) -1)))))
    (assert-true (ltt-same? (ltt-L r) '(/ 1 (+ (^ s 3) -1))))
    (assert-true (equal? (laplace-check r '(/ 1 (+ (^ s 3) -1)) 't 's) #t))
    (assert-true (contains-sym? r 'sin))))

(deftest "LT: обратное — корни в Q(sqrt 2) и степень s^{-1/2}"
  (assert-true (ltt-same? (ltt-L (ltt-inv '(/ 1 (+ (^ s 2) -2)))) '(/ 1 (+ (^ s 2) -2))))
  (assert-true (ltt-same? (ltt-inv '(^ s -1/2)) '(* (^ pi -1/2) (^ t -1/2)))))

(deftest "LT: обратное — свёртка при непростых дробях"
  (let ((r (ltt-inv '(/ 1 (* (^ s 1/2) (+ s 1))))))
    (assert-true (ltt-or-conv? r))))

(define (ltt-or-conv? r) (or (contains-sym? r 'convolve) (not (contains-sym? r 'inverse-laplace))))

(deftest "LT: круговые проверки inverse(laplace f) = f"
  (define (rt f) (ltt-inv (ltt-L f)))
  (assert-true (ltt-same? (rt '(+ 1 (* 2 t))) '(+ 1 (* 2 t))))
  (assert-true (ltt-same? (rt '(* t (exp (* -1 t)))) '(* t (exp (* -1 t)))))
  (assert-true (ltt-same? (rt '(* (exp (* -2 t)) (sin (* 3 t)))) '(* (exp (* -2 t)) (sin (* 3 t)))))
  (assert-true (ltt-same? (rt '(+ (sin t) (cos (* 2 t)))) '(+ (sin t) (cos (* 2 t)))))
  (assert-true (ltt-same? (rt '(* (heaviside (- t 1)) (exp (* -1 t)))) '(* (heaviside (- t 1)) (exp (* -1 t))))))

(deftest "LT: сертификат принимает верное"
  (assert-equal (laplace-check '(* (^ t 2) (exp (* 3 t))) '(* 2 (^ (+ s -3) -3)) 't 's) #t)
  (assert-equal (laplace-check '(sin (* 2 t)) '(/ 2 (+ (^ s 2) 4)) 't 's) #t)
  (assert-equal (laplace-check '(heaviside (- t 1)) '(/ (exp (* -1 s)) s) 't 's) #t)
  (assert-equal (laplace-check '(dirac (- t 2)) '(exp (* -2 s)) 't 's) #t)
  (assert-equal (laplace-check '(* (exp (* -1 t)) (cos (* 2 t))) '(/ (+ s 1) (+ (^ s 2) (* 2 s) 5)) 't 's) #t))

(deftest "LT: сертификат численный путь"
  ; sin t / t: прямой интеграл не берётся, остаётся квадратура
  (assert-equal (laplace-check '(/ (sin t) t) '(atan (/ 1 s)) 't 's) 'numeric))

(deftest "LT: сертификат отвергает подделки"
  ; неверный коэффициент
  (assert-equal (laplace-check '(* (^ t 2) (exp (* 3 t))) '(* 3 (^ (+ s -3) -3)) 't 's) #f)
  ; неверный знак сдвига
  (assert-equal (laplace-check '(* (^ t 2) (exp (* 3 t))) '(* 2 (^ (+ s 3) -3)) 't 's) #f)
  (assert-equal (laplace-check '(heaviside (- t 1)) '(/ (exp s) s) 't 's) #f)
  ; потеряна θ
  (assert-equal (laplace-check '(heaviside (- t 1)) '(/ 1 s) 't 's) #f)
  (assert-equal (laplace-check '(* (heaviside (- t 1)) (sin t)) '(/ (exp (* -1 s)) (+ (^ s 2) 1)) 't 's) #f)
  ; неверный полюс
  (assert-equal (laplace-check '(sin (* 2 t)) '(/ 2 (+ (^ s 2) 9)) 't 's) #f)
  (assert-equal (laplace-check '(* (exp (* -1 t)) (cos (* 2 t))) '(/ (+ s 2) (+ (^ s 2) (* 2 s) 5)) 't 's) #f)
  ; численный путь тоже отвергает
  (assert-equal (laplace-check '(/ (sin t) t) '(atan (/ 2 s)) 't 's) #f)
  ; неверная дельта
  (assert-equal (laplace-check '(dirac (- t 2)) '(exp (* 2 s)) 't 's) #f))

; ---------- шаг TR.2: ОДУ, системы, интегральные уравнения, передаточные функции ----------

(define ltd-ic0 '(= (y 0) 0))
(define ltd-ic1 '(= (at (diff (y t) t) (= t 0)) 0))
(define (ltd-d2 a b c rhs) (list '= (list '+ '(diff (diff (y t) t) t) (list '* b '(diff (y t) t)) (list '* c '(y t))) rhs))
(define (ltd-sol r) (caddr (car (ode-solutions r))))
(define (ltd-chk r) (last r))
(define (ltd-at e x) (eval-num (subst (list 't x) (laplace::ld-freeze e 't x))))
(define (ltd-near? a b) (< (abs (- a b)) 0.000001))

(deftest "TR.2: y'' + 3y' + 2y = 0, y(0)=1, y'(0)=0"
  (let ((r (laplace-dsolve (ltd-d2 1 3 2 0) '(y t) (list '(= (y 0) 1) ltd-ic1))))
    (assert-true (ltt-same? (ltd-sol r) '(+ (* 2 (exp (* -1 t))) (* -1 (exp (* -2 t))))))
    (assert-equal (ltd-chk r) #t)
    (assert-equal (ode-status r) 'ok)
    (assert-equal (ode::ode-field r :type) 'particular)
    (assert-equal (ode::ode-field r :method) 'laplace)))

(deftest "TR.2: резонанс y'' + y = sin t"
  (let ((r (laplace-dsolve '(= (+ (diff (diff (y t) t) t) (y t)) (sin t)) '(y t) (list ltd-ic0 ltd-ic1))))
    (assert-true (ltt-same? (ltd-sol r) '(* 1/2 (+ (sin t) (* -1 t (cos t))))))
    (assert-equal (ltd-chk r) #t)))

(deftest "TR.2: y' + y = θ(t−1), y(0)=0 — кусочный ответ"
  (let ((r (laplace-dsolve '(= (+ (diff (y t) t) (y t)) (heaviside (- t 1))) '(y t) (list ltd-ic0))))
    (assert-equal (ltd-chk r) #t)
    (assert-true (ltd-near? (ltd-at (ltd-sol r) 1/2) 0))
    (assert-true (ltd-near? (ltd-at (ltd-sol r) 3) (- 1 (laplace::exp-num -2))))))

(deftest "TR.2: y'' + y = δ(t−π): скачок y′ на силу импульса"
  (let ((r (laplace-dsolve '(= (+ (diff (diff (y t) t) t) (y t)) (dirac (- t pi))) '(y t) (list ltd-ic0 ltd-ic1))))
    (assert-equal (ltd-chk r) #t)
    (assert-true (ltd-near? (ltd-at (ltd-sol r) 2) 0))
    (assert-true (ltd-near? (ltd-at (ltd-sol r) 4) (- (eval-num '(sin 4)))))))

(deftest "TR.2: y''' − y = 0 с тремя условиями"
  (let ((r (laplace-dsolve '(= (- (diff (diff (diff (y t) t) t) t) (y t)) 0) '(y t)
                           '((= (y 0) 1) (= (at (diff (y t) t) (= t 0)) 0) (= (at (diff (diff (y t) t) t) (= t 0)) 0)))))
    (assert-equal (ltd-chk r) #t)
    (assert-true (ltd-near? (ltd-at (ltd-sol r) 1)
                            (+ (* 2/3 (eval-num '(* (cos (/ (sqrt 3) 2)) (exp -1/2)))) (/ (eval-num '(exp 1)) 3))))))

(deftest "TR.2: нет условий — константы C1 = y(0), C2 = y'(0)"
  (let ((r (laplace-dsolve '(= (+ (diff (diff (y t) t) t) (y t)) 0) '(y t) '())))
    (assert-equal (ode::ode-field r :type) 'general)
    (assert-equal (ode::ode-field r :constants) '(C1 C2))
    (assert-true (ltt-same? (ltd-sol r) '(+ (* C1 (cos t)) (* C2 (sin t)))))
    (assert-equal (ltd-chk r) #t)))

(deftest "TR.2: частичные условия — одна константа остаётся"
  (let ((r (laplace-dsolve '(= (+ (diff (y t) t) (* 2 (y t))) 1) '(y t) '())))
    (assert-equal (ode::ode-field r :constants) '(C1))
    (assert-true (ltt-same? (ltd-sol r) '(+ 1/2 (* (+ C1 -1/2) (exp (* -2 t))))))
    (assert-equal (ltd-chk r) #t)))

(deftest "TR.2: система x' = y, y' = −x + 1"
  (let ((r (laplace-dsolve-system '((= (diff (x t) t) (y t)) (= (diff (y t) t) (+ (* -1 (x t)) 1)))
                                  '(x y) 't '((= (x 0) 0) (= (y 0) 0)))))
    (assert-true (ltt-same? (caddr (car (ode-solutions r))) '(+ 1 (* -1 (cos t)))))
    (assert-true (ltt-same? (caddr (cadr (ode-solutions r))) '(sin t)))
    (assert-equal (ltd-chk r) #t)
    (assert-equal (laplace-system-check '((= (diff (x t) t) (y t)) (= (diff (y t) t) (+ (* -1 (x t)) 1)))
                                        '(x y) 't '((= (x t) (+ 1 (* -1 (cos t)))) (= (y t) (* 2 (sin t))))
                                        '((= (x 0) 0) (= (y 0) 0)))
                  #f)))

(deftest "TR.2: система без условий — константы"
  (let ((r (laplace-dsolve-system '((= (diff (x t) t) (y t)) (= (diff (y t) t) (* -1 (x t)))) '(x y) 't '())))
    (assert-equal (ode::ode-field r :constants) '(C1 C2))
    (assert-true (ltt-same? (caddr (car (ode-solutions r))) '(+ (* C1 (cos t)) (* C2 (sin t)))))
    (assert-equal (ltd-chk r) #t)))

(deftest "TR.2: Вольтерра второго рода y = t + ∫ sin(t−τ) y dτ"
  (let ((r (laplace-volterra '(= (y t) (+ t (integrate (* (sin (- t tau)) (y tau)) tau 0 t))) '(y t))))
    (assert-true (ltt-same? (ltd-sol r) '(+ t (/ (^ t 3) 6))))
    (assert-equal (ltd-chk r) #t)))

(deftest "TR.2: Вольтерра первого рода ∫ e^{t−τ} y dτ = t → y = 1 − t"
  (let ((r (laplace-volterra '(= (integrate (* (exp (- t tau)) (y tau)) tau 0 t) t) '(y t))))
    (assert-true (ltt-same? (ltd-sol r) '(+ 1 (* -1 t))))
    (assert-equal (ltd-chk r) #t)))

(deftest "TR.2: Вольтерра через convolve; δ-ответ и нелинейное"
  (let ((r (laplace-volterra '(= (y t) (+ 1 (* 2 (convolve (exp (* -1 t)) (y t) t)))) '(y t))))
    (assert-true (ltt-same? (ltd-sol r) '(+ -1 (* 2 (exp t)))))
    (assert-equal (ltd-chk r) #t))
  ; ∫₀ᵗ y dτ = 1: Y = 1, ответ — δ(t), обобщённая функция, не проверяется
  (assert-equal (ode-status (laplace-volterra '(= (integrate (y tau) tau 0 t) 1) '(y t))) 'unchecked)
  ; нелинейное
  (assert-equal (ode-status (laplace-volterra '(= (y t) (integrate (* (y tau) (y tau)) tau 0 t)) '(y t))) 'unknown))

(deftest "TR.2: передаточная функция, импульсная и переходная характеристики"
  (let* ((eq '(= (+ (diff (diff (y t) t) t) (* 2 (diff (y t) t)) (* 5 (y t))) (u t))))
    (assert-true (ltt-same? (transfer-function eq '(y t) '(u t)) '(/ 1 (+ (^ s 2) (* 2 s) 5))))
    (assert-true (ltt-same? (impulse-response eq '(y t) '(u t)) '(* 1/2 (exp (* -1 t)) (sin (* 2 t)))))
    (assert-true (ltt-same? (step-response eq '(y t) '(u t))
                            '(+ 1/5 (* -1/5 (exp (* -1 t)) (cos (* 2 t))) (* -1/10 (exp (* -1 t)) (sin (* 2 t))))))
    (assert-equal (stable? (transfer-function eq '(y t) '(u t)) 's) #t)
    (assert-equal (length (transfer-poles (transfer-function eq '(y t) '(u t)) 's)) 2)))

(deftest "TR.2: неустойчивая система и Раус–Гурвиц"
  (let ((W (transfer-function '(= (- (diff (diff (y t) t) t) (y t)) (+ (u t) (diff (u t) t))) '(y t) '(u t))))
    (assert-true (ltt-same? W '(/ 1 (+ s -1))))
    (assert-equal (stable? W 's) #f)
    (assert-equal (transfer-poles W 's) '(1)))
  (assert-equal (stable? '(/ 1 (+ (^ s 3) (* 2 (^ s 2)) (* 3 s) 1)) 's) #t)
  (assert-equal (stable? '(/ 1 (+ (^ s 3) (^ s 2) (* 2 s) 8)) 's) #f)
  (assert-equal (stable? '(/ 1 (+ (^ s 4) (* 2 (^ s 3)) (* 3 (^ s 2)) (* 2 s) 1)) 's) #t)
  (assert-equal (stable? '(/ 1 (+ (^ s 2) 1)) 's) #f)
  (assert-equal (stable? '(/ 1 (+ (^ s 2) a)) 's) 'unknown))

(deftest "TR.2: подделки не проходят сертификат"
  (let ((eq '(= (+ (diff (y t) t) (y t)) 0)))
    ; неверный коэффициент
    (assert-equal (laplace-dsolve-check eq '(y t) '(* 3 (exp (* -1 t))) '((= (y 0) 2))) #f)
    ; верно для уравнения, неверно для условия
    (assert-equal (laplace-dsolve-check eq '(y t) '(* 2 (exp (* -1 t))) '((= (y 0) 1))) #f)
    (assert-equal (laplace-dsolve-check eq '(y t) '(* 2 (exp (* -1 t))) '((= (y 0) 2))) #t))
  (let ((eq '(= (+ (diff (diff (y t) t) t) (y t)) (dirac (- t pi)))) (cs (list ltd-ic0 ltd-ic1)))
    (assert-equal (laplace-dsolve-check eq '(y t) '(* (heaviside (- t pi)) (sin (- t pi))) cs) #t)
    ; неверный скачок y′ (сила 2 и −1)
    (assert-equal (laplace-dsolve-check eq '(y t) '(* 2 (heaviside (- t pi)) (sin (- t pi))) cs) #f)
    (assert-equal (laplace-dsolve-check eq '(y t) '(* -1 (heaviside (- t pi)) (sin (- t pi))) cs) #f))
  ; уравнение выполнено на каждом куске, но решение разрывно в точке переключения θ
  (assert-equal (laplace-dsolve-check '(= (+ (diff (y t) t) (y t)) (heaviside (- t 1))) '(y t)
                                      '(* (heaviside (- t 1)) (+ 1 (* -2 (exp (- 1 t))))) (list ltd-ic0))
                #f))

(deftest "TR.2: нелинейное и непостоянные коэффициенты — unknown, не ошибка"
  (assert-equal (ode-status (laplace-dsolve '(= (+ (diff (y t) t) (* (y t) (y t))) 0) '(y t) '())) 'unknown)
  (assert-equal (ode-status (laplace-dsolve '(= (+ (diff (y t) t) (* t (y t))) 0) '(y t) '())) 'unknown)
  (assert-equal (ode-status (laplace-dsolve '(= (+ (diff (y t) t) (y t)) (f t)) '(y t) '((= (y 0) 1)))) 'unknown))

(deftest "TR.2: крючок dsolve — :method 'laplace и автоматически при θ/δ"
  (let ((r (dsolve '(= (+ (diff (diff (y t) t) t) (* 3 (diff (y t) t)) (* 2 (y t))) 0) '(y t) :method 'laplace
                   '(= (y 0) 1) '(= (at (diff (y t) t) (= t 0)) 0))))
    (assert-equal 'ok (ode-status r))
    (assert-equal 'laplace (ode::ode-field r :method)))
  (let ((r (dsolve '(= (+ (diff (diff (y x) x) x) (y x)) (heaviside (- x 1))) '(y x)
                   '(= (y 0) 0) '(= (at (diff (y x) x) (= x 0)) 0))))
    (assert-equal 'laplace (ode::ode-field r :method))
    (assert-equal #t (ode::ode-field r :check))))

(deftest "θ: численные сертификаты работают через eval-num"
  (assert-equal (dsolve-check '(= (+ (diff (y t) t) (y t)) (heaviside (- t 1)))
                              '(* (heaviside (- t 1)) (- 1 (exp (- 1 t)))) '(y t))
                'numeric)
  (assert-equal (dsolve-check '(= (+ (diff (y t) t) (y t)) (heaviside (- t 1)))
                              '(* (heaviside (- t 1)) (- 2 (exp (- 1 t)))) '(y t))
                #f)
  (assert-equal (laplace-check '(* (heaviside (- t 1)) (/ (sin (- t 1)) (- t 1))) '(* (exp (* -1 s)) (atan (/ 1 s))) 't 's)
                'numeric))
