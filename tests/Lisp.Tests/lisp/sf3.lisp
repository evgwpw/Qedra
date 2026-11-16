; INT.SF3: численные значения и производные для функций, на которых int-check-F-status давал 'skip:
; полилогарифм Li_s(z), целое s ≥ 3, комплексный z и вещественный z > 1 (SolveNum.polylogC); интегралы Френеля
; fresnel_s / fresnel_c (нормировка πt²/2); интегральная экспонента exp_integral_e n z (целое n ≥ 0).

(define (sf3-re v) (cond ((number? v) v) ((and (pair? v) (equal? (car v) '+)) (cadr v)) (else 0)))
(define (sf3-im v) (cond ((number? v) 0)
                         ((and (pair? v) (equal? (car v) '+)) (let ((m (caddr v))) (if (pair? m) (cadr m) 0)))
                         ((and (pair? v) (equal? (car v) '*)) (cadr v))
                         (else 0)))
(define (sf3-near? a b tol) (and (number? a) (number? b) (< (abs (- a b)) tol)))
(define (sf3-cx re im) (list '+ re (list '* im '%i)))

; численная производная вдоль вещественной оси: Li_s′(z) = Li_{s−1}(z)/z; сравнение re и im
(define (sf3-deriv-ok? s zr zi tol)
  (let* ((h 1e-5)
         (p (eval-num (list 'polylog s (sf3-cx (+ zr h) zi))))
         (m (eval-num (list 'polylog s (sf3-cx (- zr h) zi))))
         (ref (eval-num (list '/ (list 'polylog (- s 1) (sf3-cx zr zi)) (sf3-cx zr zi)))))
    (and (sf3-near? (/ (- (sf3-re p) (sf3-re m)) (* 2 h)) (sf3-re ref) tol)
         (sf3-near? (/ (- (sf3-im p) (sf3-im m)) (* 2 h)) (sf3-im ref) tol))))

(deftest "sf3/1: Li₃, Li₄ в особых точках (ζ(3), π⁴/90, Li₃(−1) = −3ζ(3)/4, Li₃(1/2))"
  (let ((z3 1.2020569031595942))
    (assert-true (sf3-near? (eval-num '(polylog 3 1)) z3 1e-12))
    (assert-true (sf3-near? (eval-num '(polylog 3 -1)) (* -0.75 z3) 1e-12))
    (assert-true (sf3-near? (eval-num '(polylog 3 0.5))
                            (+ (* 0.875 z3) (* -1 (/ (* 9.869604401089358 0.6931471805599453) 12)) (/ (^ 0.6931471805599453 3) 6)) 1e-12))
    (assert-true (sf3-near? (eval-num '(polylog 4 1)) (/ (^ 3.141592653589793 4) 90) 1e-12))
    (assert-true (sf3-near? (eval-num '(polylog 4 -1)) (* -7/720 (^ 3.141592653589793 4)) 1e-12))))

(deftest "sf3/2: Li₃(2) — вещественный z > 1, значение «снизу» (7ζ(3)/8 + π²ln2/4 − iπ·ln²2/2)"
  (let ((v (eval-num '(polylog 3 2.0)))
        (l2 0.6931471805599453))
    (assert-true (sf3-near? (sf3-re v) (+ (* 0.875 1.2020569031595942) (/ (* 9.869604401089358 l2) 4)) 1e-12))
    (assert-true (sf3-near? (sf3-im v) (* -1 (/ (* 3.141592653589793 l2 l2) 2)) 1e-12))))

(deftest "sf3/3: Li_s вблизи z = 1 (мнимая часть ≈ ε·ζ(s−1)) и инверсия при больших |z|"
  (let ((v (eval-num '(polylog 3 (+ 1.0 (* 1e-9 %i))))))
    (assert-true (sf3-near? (sf3-re v) 1.2020569031595942 1e-8))
    (assert-true (sf3-near? (sf3-im v) 1.6449340660628285e-9 1e-12)))
  ;; Li₃(z) − Li₃(1/z) = −π²/6·ln(−z) − ln³(−z)/6 при z = −10 (DLMF 25.12.? s = 3), ln(−z) = ln 10 вещественный
  (let* ((l (log 10.0))
         (a (eval-num '(polylog 3 -10.0)))
         (b (eval-num '(polylog 3 -0.1))))
    (assert-true (sf3-near? (- a b) (+ (* -1 (/ (* 9.869604401089358 l) 6)) (* -1 (/ (* l l l) 6))) 1e-11))))

(deftest "sf3/4: производная Li_s′ = Li_{s−1}/z численно — на стыках областей |z| = 1/2, |z| = 1, на инверсии"
  (assert-true (sf3-deriv-ok? 3 0.3 0.4 1e-8))     ; |z| = 1/2
  (assert-true (sf3-deriv-ok? 3 0.6 0.8 1e-8))     ; |z| = 1
  (assert-true (sf3-deriv-ok? 4 -0.8 0.6 1e-8))    ; |z| = 1, Re z < 0
  (assert-true (sf3-deriv-ok? 3 -1.5 0.7 1e-8))    ; |z| > 1
  (assert-true (sf3-deriv-ok? 5 3.0 -2.0 1e-8))
  (assert-true (sf3-deriv-ok? 4 2.0 0.0 1e-8))     ; на разрезе (значение снизу)
  (assert-true (sf3-deriv-ok? 6 0.2 -0.9 1e-8)))

(deftest "sf3/5: Френель S, C — значения (Абрамовиц — Стиган 7.3) и стык ряд / дробь при |x| = 1,5"
  (assert-true (sf3-near? (eval-num '(fresnel_s 1.0)) 0.43825914739035476 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_c 1.0)) 0.7798934003768228 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_s 2.0)) 0.3434156783636982 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_c 2.0)) 0.4882534060753408 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_s -3.0)) -0.496312998967375 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_c 10.0)) 0.4998986942055157 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_s 10.0)) 0.4681699785848822 1e-12))
  (assert-true (sf3-near? (eval-num '(fresnel_s 1.4999999)) (eval-num '(fresnel_s 1.5000001)) 1e-6))
  (assert-true (sf3-near? (eval-num '(fresnel_c 1.4999999)) (eval-num '(fresnel_c 1.5000001)) 1e-6)))

(deftest "sf3/6: Френель — производные S′ = sin(πx²/2), C′ = cos(πx²/2) (int-check, численная проверка ответа 'ok)"
  (assert-true (int-check '(fresnel_s x) '(sin (* 1/2 pi (^ x 2))) 'x))
  (assert-true (int-check '(fresnel_c (* 3 x)) '(* 3 (cos (* 9/2 pi (^ x 2)))) 'x))
  (set! integrate::*check-numeric-F* #t)
  (assert-equal 'ok (integrate::int-check-F-status '(fresnel_s x) '(sin (* 1/2 pi x x)) 'x))
  (assert-equal 'ok (integrate::int-check-F-status '(fresnel_c x) '(cos (* 1/2 pi x x)) 'x))
  (assert-equal 'bad (integrate::int-check-F-status '(fresnel_s x) '(cos (* 1/2 pi x x)) 'x))
  (set! integrate::*check-numeric-F* 'risky))

(deftest "sf3/7: E_n(z) — E₁(1), E₂(1), E₃(1), E₁(5), E₀, E₁(−1) = −Ei(1) − iπ"
  (assert-true (sf3-near? (eval-num '(exp_integral_e 1 1.0)) 0.21938393439552029 1e-12))
  (assert-true (sf3-near? (eval-num '(exp_integral_e 1 5.0)) 0.001148295591275326 1e-13))
  (assert-true (sf3-near? (eval-num '(exp_integral_e 2 1.0)) 0.14849550677592205 1e-12))
  (assert-true (sf3-near? (eval-num '(exp_integral_e 3 1.0)) 0.10969196719776026 1e-12))
  (assert-true (sf3-near? (eval-num '(exp_integral_e 0 2.0)) (/ (exp -2.0) 2) 1e-14))
  (let ((v (eval-num '(exp_integral_e 1 -1.0))))
    (assert-true (sf3-near? (sf3-re v) -1.8951178163559368 1e-12))
    (assert-true (sf3-near? (sf3-im v) -3.141592653589793 1e-12))))

(deftest "sf3/8: E_n′ = −E_{n−1} (int-check), в том числе E₀′ и комплексный аргумент"
  (assert-true (int-check '(exp_integral_e 1 x) '(* -1 (/ (exp (* -1 x)) x)) 'x))
  (assert-true (int-check '(exp_integral_e 3 x) '(* -1 (exp_integral_e 2 x)) 'x))
  (assert-true (int-check '(exp_integral_e 0 x) '(* -1 (/ (* (exp (* -1 x)) (+ 1 x)) (^ x 2))) 'x))
  (set! integrate::*check-numeric-F* #t)
  (assert-equal 'ok (integrate::int-check-F-status '(exp_integral_e 2 x) '(* -1 (exp_integral_e 1 x)) 'x))
  (assert-equal 'ok (integrate::int-check-F-status '(polylog 3 x) '(/ (polylog 2 x) x) 'x))
  (assert-equal 'ok (integrate::int-check-F-status '(polylog 4 (* 2 x)) '(/ (polylog 3 (* 2 x)) x) 'x))
  (set! integrate::*check-numeric-F* 'risky)
  ;; E₂′ = −E₁ в комплексной точке (центральная разность)
  (let* ((h 1e-5)
         (p (eval-num (list 'exp_integral_e 2 (sf3-cx (+ 3.0 h) 2.0))))
         (m (eval-num (list 'exp_integral_e 2 (sf3-cx (- 3.0 h) 2.0))))
         (ref (eval-num (list '* -1 (list 'exp_integral_e 1 (sf3-cx 3.0 2.0))))))
    (assert-true (sf3-near? (/ (- (sf3-re p) (sf3-re m)) (* 2 h)) (sf3-re ref) 1e-8))
    (assert-true (sf3-near? (/ (- (sf3-im p) (sf3-im m)) (* 2 h)) (sf3-im ref) 1e-8))))
