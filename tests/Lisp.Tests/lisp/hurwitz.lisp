; ZETA.HURWITZ: дзета Гурвица ζ(s, a) — голова языка, производная, eval-num, связь с полигаммой, интегралы
; ∫ x^m ζ(σ, a+bx) dx (lib/hurwitz.lisp, lib/integrate/hurwitz.lisp). Ответ каждого интеграла сверяется центральной
; разностью самой первообразной (не через diff) в численных точках.

(define (hzt-num e) (eval-num e))
(define (hzt-near? a b tol) (< (abs (- a b)) (* tol (+ 1.0 (abs b)))))
(define (hzt-open? r) (contains-sym? r 'integrate))

; значение выражения e при x = x0 и параметрах (a b s)
(define (hzt-at e x0 a b s) (hzt-num (subst (list (list 'x x0) (list 'a a) (list 'b b) (list 's s)) e)))

; (F(x+h) − F(x−h))/(2h) против f(x) в трёх точках
(define (hzt-antiderivative? F f)
  (every? (lambda (p)
            (let* ((x0 (car p)) (a (cadr p)) (b (caddr p)) (s (cadddr p)) (h 0.00001)
                   (d (/ (- (hzt-at F (+ x0 h) a b s) (hzt-at F (- x0 h) a b s)) (* 2 h))))
              (hzt-near? d (hzt-at f x0 a b s) 0.000001)))
          '((0.9 1.3 0.7 2.6) (1.7 2.1 0.4 3.3) (0.55 0.8 1.9 4.5))))

(deftest "hurwitz/1: eval-num — известные значения"
  (assert-true (hzt-near? (hzt-num '(zeta 2 1)) 1.6449340668482264 1e-13))
  (assert-true (hzt-near? (hzt-num '(zeta 2 0.5)) 4.934802200544679 1e-13))
  (assert-true (hzt-near? (hzt-num '(zeta 3 0.5)) (* 7 1.2020569031595942) 1e-13))
  (assert-true (hzt-near? (hzt-num '(zeta 12 1)) 1.000246086553308 1e-13))
  (assert-true (hzt-near? (hzt-num '(zeta 2 100.0)) 0.010050166663333573 1e-13))
  ; ζ(−1, 2) = −B₂(2)/2 = −13/12, ζ(0, 2) = 1/2 − 2
  (assert-true (hzt-near? (hzt-num '(zeta -1 2)) -1.0833333333333333 1e-13))
  (assert-true (hzt-near? (hzt-num '(zeta 0 2)) -1.5 1e-13)))

(deftest "hurwitz/2: a < 0 при целом s — сдвиг вверх"
  ; ζ(2, −1/2) = 4 + ζ(2, 1/2), ζ(3, −3/2) = (−3/2)^(−3) + (−1/2)^(−3) + ζ(3, 1/2)
  (assert-true (hzt-near? (hzt-num '(zeta 2 -0.5)) (+ 4.0 4.934802200544679) 1e-13))
  (assert-true (hzt-near? (hzt-num '(zeta 3 -1.5)) (+ (/ 1.0 -3.375) -8.0 (* 7 1.2020569031595942)) 1e-12)))

(deftest "hurwitz/3: связь с полигаммой — hz-psi->zeta, hz-zeta->psi"
  (let ((z (hz-psi->zeta '(psi u 2))) (p (hz-zeta->psi '(zeta 4 u))))
    (assert-equal (hz-psi->zeta '(psi u 1)) '(zeta 2 u))
    (assert-true (hzt-near? (hzt-num (subst '(u 2.5) z)) (hzt-num '(psi 2.5 2)) 1e-12))
    ; ζ(4, u) = −ψ'''(u)/6
    (assert-true (hzt-near? (hzt-num (subst '(u 1.7) p)) (hzt-num '(zeta 4 1.7)) 1e-12))
    (assert-equal (hz-zeta->psi '(zeta s u)) '(zeta s u))
    (assert-equal (hz-psi->zeta '(poly_gamma 1 u)) '(zeta 2 u))))

(deftest "hurwitz/4: производная по аргументу −s·ζ(s+1, a+bx)·b"
  (let ((d (diff 'x '(zeta s (+ a (* b x))))))
    (assert-true (hzt-near? (hzt-at d 0.9 1.3 0.7 2.6)
                            (* -1 2.6 0.7 (hzt-num '(zeta 3.6 1.9300000000000002))) 1e-10))
    (assert-true (hzt-antiderivative? '(zeta s (+ a (* b x))) d))))

(deftest "hurwitz/5: язык — zeta(s, a)"
  (assert-equal (math-eval "zeta(2, 1)") '(zeta 2))
  (assert-equal (math-eval "zeta(2, a + b*x)") '(zeta 2 (+ a (* b x))))
  (assert-true (hzt-near? (math-eval "zeta(2, 2.5)") 0.4903577561002349 1e-12))
  (assert-equal (math-eval "diff(zeta(2, a + b*x), x)") (simplify '(* -2 b (zeta 3 (+ a (* b x))))))
  (assert-error (math-eval "zeta(1, 2, 3)")))

(deftest "hurwitz/6: ∫ζ(s, a+bx), ∫xζ(s, a+bx), ∫x²ζ(s, a+bx) — правила Rubi 8.7"
  (let ((f1 '(zeta s (+ a (* b x))))
        (f2 '(* x (zeta s (+ a (* b x)))))
        (f3 '(* (^ x 2) (zeta s (+ a (* b x))))))
    (for-each (lambda (f)
                (let ((F (integrate f 'x)))
                  (assert-true (not (hzt-open? F)))
                  (assert-true (hzt-antiderivative? F f))))
              (list f1 f2 f3))))

(deftest "hurwitz/7: ∫ζ(2, a+bx) = ψ/b, ∫xζ(2, a+bx) = xψ/b − log Γ/b²"
  (let* ((f1 '(zeta 2 (+ a (* b x))))
         (f2 '(* x (zeta 2 (+ a (* b x)))))
         (F1 (integrate f1 'x))
         (F2 (integrate f2 'x)))
    (assert-true (not (hzt-open? F1)))
    (assert-true (not (hzt-open? F2)))
    (assert-true (contains-sym? F2 'gamma))
    (assert-true (hzt-antiderivative? F1 f1))
    (assert-true (hzt-antiderivative? F2 f2))))

(deftest "hurwitz/8: сумма, где неберущиеся ∫ζ/x сокращаются — по частям по сумме целиком"
  ; b·s·ζ(s+1, u)/x + ζ(s, u)/x² = −d/dx[ζ(s, u)/x]
  (let* ((f '(+ (* b s (zeta (+ s 1) (+ a (* b x))) (^ x -1)) (* (zeta s (+ a (* b x))) (^ x -2))))
         (F (integrate f 'x)))
    (assert-true (not (hzt-open? F)))
    (assert-true (hzt-antiderivative? F f))
    (assert-equal F (simplify '(* -1 (zeta s (+ a (* b x))) (^ x -1)))))
  ; −b ψ''(u)/x + ζ(2, u)/x² = −d/dx[ψ'(u)/x]  (ψ'' = −2ζ(3), ψ' = ζ(2))
  (let* ((f '(+ (* -1 b (psi (+ a (* b x)) 2) (^ x -1)) (* (zeta 2 (+ a (* b x))) (^ x -2))))
         (F (integrate f 'x)))
    (assert-true (not (hzt-open? F)))
    (assert-true (hzt-antiderivative? F f))))

(deftest "hurwitz/9: что не берётся — невычисленная форма (∫ζ(s, u)/x, ∫x²ζ(2, u))"
  (assert-true (hzt-open? (integrate '(* (zeta s (+ a (* b x))) (^ x -1)) 'x)))
  (assert-true (hzt-open? (integrate '(* (zeta 2 (+ a (* b x))) (^ x -2)) 'x)))
  (assert-true (hzt-open? (integrate '(* (^ x 2) (zeta 2 (+ a (* b x)))) 'x))))
