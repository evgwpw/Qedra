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
