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

(deftest "loss-r145/1: Γ-ответ Rubi не отвергается отрицательным набором параметров"
  (let* ((f (math-read "sinh(a + b*x^n)^2/x^2"))
         (F (math-read "1/(2*x) + 1/2*(-(-2*b*x^n)^(1/n)*exp(2*a)*gamma(-1/n, -2*b*x^n)/(2*n*x) - (2*b*x^n)^(1/n)*exp(-2*a)*gamma(-1/n, 2*b*x^n)/(2*n*x))")))
    (assert-true (integrate::int-check-F-final-ok? F f 'x))))

(deftest "loss-r145/2: root-sum с (a-b/x)^(1/3) не отвергается проверкой двух знаков"
  (let* ((f (math-read "1/(a*x^3-b*x^2)^(1/3)/(a*x^4+b)"))
         (F (math-read "-rootsum(t*log((-2048*a*b^3*t^11 + 256a^3*t^8 - 2048*a^4*t^11 + 256b^3*t^8)/(-1 + 32a*t^3 - 384a^2*t^6 + 1536a^3*t^9 - 512*b^3*t^9) + (a - b/x)^(1/3)), t, 1 + 4096*a*b^3*t^12 - 32*a*t^3 + 384*a^2*t^6 - 2048*a^3*t^9 + 4096*a^4*t^12)/(2*b)")))
    (assert-true (integrate::int-check-F-final-ok? F f 'x))))

(deftest "loss-r145/3: blake-ответ с root-sum возвращается, а не «unknown»"
  (let* ((f (math-read "1/(a*x^3-b*x^2)^(1/3)/(a*x^4+b)"))
         (F (integrate f 'x)))
    (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))))

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

