; WRONG.1: класс A — ответы, верные только при x > 0 (вынос x из корня без |x|).
; Проверка — производная в точках по обе стороны нулей подкоренного (int-check смотрит только x > 0).
(load (string-append lib-dir "rubi/utils.lisp"))

(define (w1-deriv-ok? f F pts)
  (equal? 'ok
          (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x F) f) f 'x 0.000001 pts)))

(define (w1-check fstr pts)
  (let* ((f (math-read fstr))
         (F (integrate f 'x)))
    (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))
    (assert-true (w1-deriv-ok? f F pts))))

(deftest "wrong1/1: ∫√(4x²−9)/x⁴ — производная верна при x < 0 (было (4−9/x²)^(3/2)/27)"
  (w1-check "sqrt(4*x^2 - 9)/x^4" '(-73/10 -37/10 -22/10 22/10 37/10 73/10)))

(deftest "wrong1/1: ∫√(x²−a²)/x⁴ — производная верна при x < 0 (было (1−a²/x²)^(3/2)/(3a²))"
  (w1-check "sqrt(-49/100 + x^2)/x^4" '(-37/10 -22/10 22/10 37/10)))

(deftest "wrong1/1: ∫dx/√(−b·x²−π) при b < 0 — производная верна при x < 0 (было atan(√(−b−π/x²)/√b)/√b)"
  (let* ((e (math-read "1/sqrt(-b*x^2 - pi)"))
         (f (replace-expr e 'b -7/10))
         (F (replace-expr (integrate e 'x) 'b -7/10)))
    (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))
    (assert-true (w1-deriv-ok? f F '(-73/10 -51/10 -37/10 37/10 51/10 73/10)))))
(deftest "wrong2/1: hebisch/4973 — слагаемое ∫14/x³ = −7/x² не теряется рядом с e^(e⁵)/x²"
  (let* ((f (math-read "((-x-2)*exp(2*log(5)+exp(5)-x-5)+14)/x^3"))
         (F (integrate f 'x)))
    (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))
    (assert-true (int-check F f 'x))
    ; прежний ложный ответ без −7/x² не проходит проверку
    (assert-true (not (int-check '(* (^ x -2) (exp (+ -5 (* -1 x) (exp 5) (* 2 (log 5))))) f 'x)))))

(deftest "wrong2/2: проверка ловит пропажу малого слагаемого рядом с огромным"
  (let* ((f (math-read "exp(200)*x^2 + 5*x^4"))
         (Fwrong (math-read "exp(200)*x^3/3"))
         (Fright (math-read "exp(200)*x^3/3 + x^5"))
         (F (integrate f 'x)))
    ; Fwrong′ = exp(200)·x², малое 5x⁴ потеряно: относительный допуск по |f| ≈ 10⁸⁵ его не видит
    (assert-true (not (int-check Fwrong f 'x)))
    (assert-true (int-check Fright f 'x))
    (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))
    (assert-true (int-check F f 'x))))

