; ode-numeric.lisp — тесты шага WEB.PLOT: численная задача Коши (RK45), график решения ОДУ, поле направлений.

(define (ton-dev r f)
  (foldl (lambda (m p) (max m (abs (- (nth p 1) (f (car p)))))) 0.0 (ode-numeric-points r)))
(define (ton-ex name x) (eval-num (list name x)))
(define (ton-sub? s t) (string-contains? s t))
(define (ton-count s sub)
  (let loop ((i 0) (n 0))
    (cond ((> (+ i (string-length sub)) (string-length s)) n)
          ((equal? (substring s i (+ i (string-length sub))) sub) (loop (+ i 1) (+ n 1)))
          (else (loop (+ i 1) n)))))

; ---------- точность на эталонах ----------
(deftest "ode-numeric: y' = y, y(0) = 1 на [0, 2] — отклонение от e^x < 1e-6"
  (let ((r (ode-numeric (math-read "y' = y") '(y x) '(x 0 2) '(= (y 0) 1))))
    (assert-equal (ode-numeric-status r) 'ok)
    (assert-true (< (ton-dev r (lambda (x) (ton-ex 'exp x))) 1e-6))
    (assert-true (> (length (ode-numeric-points r)) 100))))

(deftest "ode-numeric: y'' + y = 0, y(0) = 1, y'(0) = 0 на [-3, 10] (назад и вперёд) — отклонение от cos x < 1e-6"
  (let ((r (ode-numeric (math-read "y'' + y = 0") '(y x) '(x -3 10)
                        '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0))))
    (assert-equal (ode-numeric-status r) 'ok)
    (assert-true (< (ton-dev r (lambda (x) (ton-ex 'cos x))) 1e-6))
    (assert-true (< (car (car (ode-numeric-points r))) -2.99))
    (assert-true (> (car (last (ode-numeric-points r))) 9.99))))

(deftest "ode-numeric: y' = x^2, y(0) = 2 — отклонение от 2 + x^3/3 < 1e-6; порядок 2 хранит y и y'"
  (let ((r (ode-numeric (math-read "y' = x^2") '(y x) '(x 0 3) '(= (y 0) 2))))
    (assert-true (< (ton-dev r (lambda (x) (+ 2 (/ (* x x x) 3.0)))) 1e-6)))
  (let ((r (ode-numeric (math-read "y'' = -y") '(y x) '(x 0 1) '(= (y 0) 0) '(= (at (diff (y x) x) (= x 0)) 1))))
    (assert-equal (length (car (ode-numeric-points r))) 3)
    (assert-true (< (abs (- (nth (last (ode-numeric-points r)) 2) (ton-ex 'cos 1))) 1e-6))))

(deftest "ode-numeric: из языка — [x, a, b] принимается как тензор, результат — ode-numeric-result"
  (let ((r (math-eval "ode_numeric(y' = y, y(x), [x, 0, 1], y(0) = 1)")))
    (assert-equal (car r) 'ode-numeric-result)
    (assert-equal (ode-numeric-status r) 'ok)
    (assert-true (< (abs (- (nth (last (ode-numeric-points r)) 1) (ton-ex 'exp 1))) 1e-6))))

; ---------- честные отказы ----------
(deftest "ode-numeric: взрыв решения y' = y^2, y(0) = 1 — failed с причиной, точки до обрыва, x ≈ 1"
  (let ((r (ode-numeric (math-read "y' = y^2") '(y x) '(x 0 2) '(= (y 0) 1))))
    (assert-equal (ode-numeric-status r) 'failed)
    (assert-true (ton-sub? (ode-numeric-reason r) "бесконечность"))
    (assert-true (> (length (ode-numeric-points r)) 50))
    (assert-true (< (abs (- (car (last (ode-numeric-points r))) 1.0)) 1e-3))))

(deftest "ode-numeric: особенность правой части y' = 1/x через 0 — failed; нет нужных условий — ошибка"
  (let ((r (ode-numeric (math-read "y' = 1/x") '(y x) '(x -1 2) '(= (y 1) 1))))
    (assert-equal (ode-numeric-status r) 'failed)
    (assert-true (string? (ode-numeric-reason r))))
  (assert-error (ode-numeric (math-read "y'' + y = 0") '(y x) '(x 0 1) '(= (y 0) 1)))
  (assert-error (ode-numeric (math-read "y' = y") '(y x) '(t 0 1) '(= (y 0) 1)))
  ; нелинейно по старшей производной — отказ, а не неверная кривая
  (assert-error (ode-numeric (math-read "y'^2 = y") '(y x) '(x 0 1) '(= (y 0) 1))))

; ---------- проверка по невязке ----------
(deftest "ode-numeric-check: принимает решения, отвергает подделки"
  (let* ((eq (math-read "y' = y"))
         (r (ode-numeric eq '(y x) '(x 0 2) '(= (y 0) 1)))
         (pts (ode-numeric-points r)))
    (assert-true (ode-numeric-check eq '(y x) pts))
    ; подделка: y = x
    (assert-true (not (ode-numeric-check eq '(y x) (map (lambda (p) (list (car p) (car p))) pts))))
    ; подделка: e^x + 0.01 x
    (assert-true (not (ode-numeric-check eq '(y x) (map (lambda (p) (list (car p) (+ (cadr p) (* 0.01 (car p))))) pts))))
    ; подделка: решение другого уравнения (e^(2x))
    (assert-true (not (ode-numeric-check eq '(y x) (map (lambda (p) (list (car p) (ton-ex 'exp (* 2 (car p))))) pts))))
    ; мусор вместо таблицы
    (assert-true (not (ode-numeric-check eq '(y x) '((0 1))))))
  (let* ((eq (math-read "y'' + y = 0"))
         (r (ode-numeric eq '(y x) '(x 0 6) '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0)))
         (pts (ode-numeric-points r)))
    (assert-true (ode-numeric-check eq '(y x) pts))
    ; подделка: подмена y'-колонки
    (assert-true (not (ode-numeric-check eq '(y x) (map (lambda (p) (list (car p) (cadr p) (cadr p))) pts))))))

; ---------- графики ----------
(deftest "plot-svg: (:points …) и (:ode …) — кривая; (:field …) — отрезки; одна ломаная у решения"
  (let ((s (plot-svg (list '(:points ((0 0) (1 1) (2 0)))) '())))
    (assert-true (ton-sub? s "<svg")) (assert-true (ton-sub? s "<path")))
  (let ((i (plot-info '(:ode (= (diff (y x) x) y) (y x) -1 1 ((= (y 0) 1))))))
    (assert-equal (car (cdr i)) 1)
    (assert-true (< (abs (- (car (nth i 9)) (ton-ex 'exp -1))) 1e-3)))
  (let ((i (plot-info '(:field (- x y) x y -3 3 -3 3))))
    (assert-equal (cadr i) 280))
  (assert-error (plot-svg (list '(:ode (= (diff (y x) x) y) (y x) -1 1 ())) '())))

(deftest "plot-ode: частное решение — точная кривая, подпись «точное»; общее — семейство; численное — RK45"
  (let ((s (plot-ode (math-read "y'' + y = 0") '(y x) '(x -5 5) '(= (y 0) 1) '(= (at (diff (y x) x) (= x 0)) 0))))
    (assert-true (ton-sub? s "решение ОДУ (точное)"))
    (assert-true (ton-sub? s "y(x) = cos(x)")))
  (let ((s (plot-ode (math-read "y' = y") '(y x) '(x -3 3))))
    (assert-true (ton-sub? s "общее решение; задайте y(x0)"))
    (assert-true (ton-sub? s "C1 = 2")))
  (let ((s (plot-ode (math-read "y'' + y = 0") '(y x) '(x -5 5))))
    (assert-true (ton-sub? s "C1 = 1, C2 = -1")))
  (let ((s (plot-ode (math-read "y' = x^2 + sin(y)") '(y x) '(x -2 2) '(= (y 0) 1))))
    (assert-true (ton-sub? s "численно (RK45)")))
  (let ((s (plot-ode (math-read "y' = y^2") '(y x) '(x -1 3) '(= (y 0) 1) :title "T")))
    (assert-true (ton-sub? s ">T<"))))

(deftest "plot-ode: отказ численного решения — кривая до обрыва и причина в заголовке; нечего строить — понятная ошибка"
  (let ((s (plot-ode (math-read "y' = x^2 + y^2") '(y x) '(x -1 3) '(= (y 0) 1))))
    (assert-true (ton-sub? s "оборвано"))
    (assert-true (ton-sub? s "бесконечность")))
  (let ((m (try (plot-ode (math-read "y' = sin(x*y)") '(y x) '(x -5 5)) (lambda (e) (error-message e)))))
    (assert-true (ton-sub? m "задайте начальные условия")))
  (assert-error (plot-ode (math-read "y' = y") '(y x) '(t -1 1))))

(deftest "plot_ode / plot_direction_field из языка; plot-ode-src и окно"
  (assert-true (ton-sub? (math-eval "plot_ode(y' = y, y(x), [x, -2, 2], y(0) = 1)") "<svg"))
  (assert-true (ton-sub? (math-eval "plot_direction_field(x - y, x, y, -3, 3, -3, 3)") "поле направлений"))
  (assert-true (ton-sub? (plot-ode-src "dsolve(y'' + y = 0, y(t), y(0) = 1, y'(0) = 0)" -5 5) "y(t) = cos(t)"))
  (assert-equal (plot-ode-window "dsolve(y' = y, y(x), y(3) = 1)") '(-2.0 8.0))
  (assert-equal (plot-ode-window "dsolve(y' = y, y(x))") '(-5.0 5.0))
  (assert-error (plot-ode-src "integrate(x, x)" -1 1)))

(deftest "plot-direction-field: интегральные кривые через точки; пустое окно и неопределённая f — ошибки"
  (let ((s (plot-direction-field '(- x y) 'x 'y -3 3 -3 3 :curves '((0 1) (0 -2)))))
    (assert-true (> (ton-count s "<path") 280)))
  (assert-error (plot-direction-field '(- x y) 'x 'y 3 -3 -3 3))
  (assert-error (plot-direction-field '(/ 1 (- x x)) 'x 'y -3 3 -3 3)))

(deftest "plot-answer-expr: ответ — функция от x; ответ без x, множество, параметр — понятная ошибка"
  (assert-equal (plot-answer-expr "diff(x^3, x)") "3x^2")
  (assert-equal (plot-answer-expr "integrate(2*x, x)") "x^2")
  (assert-true (ton-sub? (try (plot-answer-expr "solve(x^2 - 1, x)") (lambda (e) (error-message e))) "не одна функция"))
  (assert-true (ton-sub? (try (plot-answer-expr "integrate(x, x, 0, 1)") (lambda (e) (error-message e))) "не зависит от x"))
  (assert-true (ton-sub? (try (plot-answer-expr "integrate(a*x, x)") (lambda (e) (error-message e))) "неизвестные a")))
