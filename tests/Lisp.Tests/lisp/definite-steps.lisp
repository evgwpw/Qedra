; ST.3в-2: шаги определённых интегралов — метод и причина, Ньютон — Лейбниц,
; вычеты, замочная скважина, особые точки внутри; brief ≤ 15 строк.

(define (dst-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (dst-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (dst-has? s sub) (string-contains? s sub))
(define (dst-rules thunk) (step-rules (cadr (capture-step-log thunk))))

(deftest "интегралы/шаги: ∫₀¹ x² dx — Ньютон — Лейбниц, первообразная и непрерывность"
  (let* ((off (definite-integral '(^ x 2) 'x 0 1))
         (s (dst-text (lambda () (definite-integral '(^ x 2) 'x 0 1)) 'brief))
         (rs (dst-rules (lambda () (definite-integral '(^ x 2) 'x 0 1)))))
    (assert-equal off 1/3)
    (assert-true (member? 'di-method rs))
    (assert-true (member? 'di-newton rs))
    (assert-true (dst-has? s "Ньютон — Лейбниц"))
    (assert-true (dst-has? s "F(x) = 1/3*x^3"))
    (assert-true (dst-has? s "непрерывность на [a, b]"))
    (assert-true (dst-has? s "F(b) − F(a)"))
    (assert-true (<= (dst-lines s) 15))))

(deftest "интегралы/шаги: ∫ dx/(x²+1) — полюса в верхней полуплоскости и сумма·2πi"
  (let* ((off (definite-integral '(/ 1 (+ (^ x 2) 1)) 'x '-inf 'inf))
         (s (dst-text (lambda () (definite-integral '(/ 1 (+ (^ x 2) 1)) 'x '-inf 'inf)) 'brief))
         (rs (dst-rules (lambda () (definite-integral '(/ 1 (+ (^ x 2) 1)) 'x '-inf 'inf)))))
    (assert-true (< (abs (- (eval-num off) (eval-num 'pi))) 1e-9))
    (assert-true (member? 'di-residues rs))
    (assert-true (member? 'di-method rs))
    (assert-true (dst-has? s "Полюса в верхней полуплоскости и вычеты"))
    (assert-true (dst-has? s "лемма Жордана"))
    (assert-true (dst-has? s "2πi"))
    (assert-true (<= (dst-lines s) 15))))

(deftest "интегралы/шаги: ∫ cos x/(x²+1) — вычеты, полюс i"
  (let* ((off (definite-integral '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 'inf))
         (s (dst-text (lambda () (definite-integral '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 'inf)) 'brief)))
    (assert-true (< (abs (- (eval-num off) (eval-num '(* pi (exp -1))))) 1e-9))
    (assert-true (dst-has? s "вычеты в верхней полуплоскости"))
    (assert-true (dst-has? s "%i"))
    (assert-true (dst-has? s "exp(-1)"))
    (assert-true (<= (dst-lines s) 15))))

(deftest "интегралы/шаги: ∫₀^∞ x^{−1/2}/(x+1) — замочная скважина"
  (let* ((off (definite-integral '(/ (^ x -1/2) (+ x 1)) 'x 0 'inf))
         (s (dst-text (lambda () (definite-integral '(/ (^ x -1/2) (+ x 1)) 'x 0 'inf)) 'brief))
         (rs (dst-rules (lambda () (definite-integral '(/ (^ x -1/2) (+ x 1)) 'x 0 'inf)))))
    (assert-true (< (abs (- (eval-num off) (eval-num 'pi))) 1e-9))
    (assert-true (member? 'di-keyhole rs))
    (assert-true (dst-has? s "Замочная скважина"))
    (assert-true (dst-has? s "s = -1/2"))
    (assert-true (dst-has? s "полюс z = -1"))
    (assert-true (dst-has? s "вычет R(z)·z^s = 1"))
    (assert-true (dst-has? s "−π/sin(πs)·Σ"))
    (assert-true (<= (dst-lines s) 15))))

(deftest "интегралы/шаги: ∫₋₁¹ dx/x² — расходится, полюс на отрезке"
  (let* ((off (definite-integral '(/ 1 (^ x 2)) 'x -1 1))
         (s (dst-text (lambda () (definite-integral '(/ 1 (^ x 2)) 'x -1 1)) 'brief))
         (rs (dst-rules (lambda () (definite-integral '(/ 1 (^ x 2)) 'x -1 1)))))
    (assert-equal (car off) 'divergent)
    (assert-true (member? 'di-divergent rs))
    (assert-true (dst-has? s "Интеграл расходится"))
    (assert-true (dst-has? s "полюс"))
    (assert-true (<= (dst-lines s) 15))))

(deftest "интегралы/шаги: ∫₁⁴ dx/sin²x — расходится, особая точка π внутри"
  (let* ((off (definite-integral '(/ 1 (^ (sin x) 2)) 'x 1 4))
         (s (dst-text (lambda () (definite-integral '(/ 1 (^ (sin x) 2)) 'x 1 4)) 'brief))
         (rs (dst-rules (lambda () (definite-integral '(/ 1 (^ (sin x) 2)) 'x 1 4)))))
    (assert-equal (car off) 'divergent)
    (assert-true (member? 'di-singular rs))
    (assert-true (dst-has? s "Особые точки внутри отрезка"))
    (assert-true (dst-has? s "pi"))
    (assert-true (dst-has? s "интеграл расходится"))
    (assert-true (<= (dst-lines s) 15))))
