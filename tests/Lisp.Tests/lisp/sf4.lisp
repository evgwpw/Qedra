; INT.SF4: численные значения (SolveNum.hyp2f1C / appellF1C, signum, atan2, mods) и их производные (Differentiate.fs) —
; ответы Rubi с hypergeometric-2f1, appell-f1, signum, atan2, mods проверялись как 'skip.

(define (sf4-re v) (cond ((number? v) v) ((and (pair? v) (equal? (car v) '+)) (cadr v)) (else 0)))
(define (sf4-im v) (cond ((number? v) 0)
                         ((and (pair? v) (equal? (car v) '+)) (let ((m (caddr v))) (if (pair? m) (cadr m) 0)))
                         ((and (pair? v) (equal? (car v) '*)) (cadr v))
                         (else 0)))
(define (sf4-near? a b tol)
  (and (number? a) (number? b) (<= (abs (- a b)) (* tol (+ 1 (abs b))))))
(define (sf4-cnear? a b tol)
  (and (sf4-near? (sf4-re a) (sf4-re b) tol) (sf4-near? (sf4-im a) (sf4-im b) tol)))
(define (sf4-cx re im) (list '+ re (list '* im '%i)))
(define (sf4-f21 a b c z) (eval-num (list 'hypergeometric-2f1 a b c z)))
(define (sf4-at e v) (eval-num (replace-expr e 't v)))

(deftest "sf4/1: ₂F₁(1,1;2;z) = −ln(1−z)/z — ряд, связь с 1−z (z → 1), Пфафф (z < 0), до 1e-12"
  (for-each (lambda (z)
              (assert-true (sf4-near? (sf4-f21 1.0 1.0 2.0 z) (/ (- 0 (log (- 1.0 z))) z) 1e-12)))
            '(0.5 0.9 0.95 0.99 0.999 -0.5 -0.95 -7.0 -100.0)))

(deftest "sf4/2: ₂F₁(½,½;3/2;z²) = asin z / z, до 1e-12"
  (for-each (lambda (z)
              (assert-true (sf4-near? (sf4-f21 0.5 0.5 1.5 (* z z)) (/ (asin z) z) 1e-12)))
            '(0.3 0.8 0.95 0.999)))

(deftest "sf4/3: Гаусс ₂F₁(a,b;c;1) = Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b)); при c−a−b ≤ 0 — не число"
  (assert-true (sf4-near? (sf4-f21 1.0 2.0 5.0 1.0) 2.0 1e-12))
  (assert-true (sf4-near? (sf4-f21 0.5 0.5 2.0 1.0) (/ 4.0 3.141592653589793) 1e-12))
  (assert-true (not (number? (sf4-f21 1.0 1.0 2.0 1.0)))))

(deftest "sf4/4: z > 1 — значение «снизу» разреза: ₂F₁(1,1;2;3) = −(ln 2 + iπ)/3; z = 2 (целая разность — возмущение)"
  (let ((v (sf4-f21 1.0 1.0 2.0 3.0)))
    (assert-true (sf4-near? (sf4-re v) (/ (- 0 (log 2.0)) 3) 1e-9))
    (assert-true (sf4-near? (sf4-im v) (/ (- 0 3.141592653589793) 3) 1e-9)))
  (let ((v (sf4-f21 1.0 1.0 2.0 2.0)))        ; −ln(1−z)/z, 1−z = −1 + i0
    (assert-true (sf4-near? (sf4-re v) 0.0 1e-9))
    (assert-true (sf4-near? (sf4-im v) (/ (- 0 3.141592653589793) 2) 1e-9)))
  ; нецелая разность параметров (D-формула без возмущения) — 1e-12: ₂F₁(½,½;3/2;4) = asin(2)/2, asin 2 = π/2 − i·ln(2+√3) снизу
  (let ((v (sf4-f21 0.5 0.5 1.5 4.0)))
    (assert-true (sf4-near? (sf4-re v) (/ 3.141592653589793 4) 1e-9))
    (assert-true (sf4-near? (abs (sf4-im v)) (/ (log (+ 2.0 (sqrt 3.0))) 2) 1e-9))))

(deftest "sf4/5: комплексные z и параметры — преобразование Эйлера F(a,b;c;z) = (1−z)^(c−a−b) F(c−a,c−b;c;z)"
  (for-each (lambda (z)
              (let* ((a 0.3) (b 0.7) (c 1.9)
                     (l (sf4-f21 a b c z))
                     (r (eval-num (list '* (list '^ (list '- 1 z) (- c a b)) (sf4-f21 (- c a) (- c b) c z)))))
                (assert-true (sf4-cnear? l r 1e-10))))
            (list (sf4-cx 0.3 0.4) (sf4-cx 0.5 1.0) (sf4-cx -3.0 2.0) (sf4-cx 0.9 0.3) (sf4-cx 2.0 0.5)))
  ; ₂F₁(1,1;2;z) комплексно
  (let ((z (sf4-cx 0.3 0.4)))
    (assert-true (sf4-cnear? (sf4-f21 1.0 1.0 2.0 z) (eval-num (list '/ (list '* -1 (list 'log (list '- 1 z))) z)) 1e-12))))

(deftest "sf4/6: многочлен (a = −n) при любом z"
  (assert-true (sf4-near? (sf4-f21 -2.0 1.5 3.0 4.0) (+ 1 (* -2 1.5 4.0 (/ 1 3.0)) (* 1 (/ (* -2 -1 1.5 2.5 16.0) (* 3.0 4.0 2.0)))) 1e-12)))

(deftest "sf4/7: F₁(a;b₁,b₂;c;x,0) = ₂F₁(a,b₁;c;x); F₁(…;x,x) = ₂F₁(a,b₁+b₂;c;x) — ряд, строки, интеграл 16.15.1"
  (assert-true (sf4-near? (eval-num '(appell-f1 0.5 1.0 1.3 1.5 0.3 0.0)) (sf4-f21 0.5 1.0 1.5 0.3) 1e-12))
  (for-each (lambda (x)
              (assert-true (sf4-near? (eval-num (list 'appell-f1 0.5 0.7 1.1 1.5 x x)) (sf4-f21 0.5 1.8 1.5 x) 1e-11)))
            '(0.3 0.8 0.95 -3.0 -20.0)))

(deftest "sf4/8: F₁ при x или y на разрезе [1, ∞) — не число (честно); комплексный y"
  (assert-true (not (number? (eval-num '(appell-f1 0.5 1.0 1.0 1.5 1.7 2.3)))))
  (assert-true (number? (sf4-re (eval-num (list 'appell-f1 0.5 1.0 1.0 1.5 0.3 (sf4-cx 0.2 0.5)))))))

(deftest "sf4/9: signum, atan2, mods"
  (assert-true (= (eval-num '(signum -2.5)) -1.0))
  (assert-true (= (eval-num '(signum 0.0)) 0))
  (assert-true (sf4-cnear? (eval-num '(signum (+ 3.0 (* 4.0 %i)))) (sf4-cx 0.6 0.8) 1e-14))
  (assert-true (sf4-near? (eval-num '(atan2 1.0 -2.0)) (- 3.141592653589793 (atan 0.5)) 1e-14))
  (assert-true (sf4-near? (eval-num '(atan2 -1.0 -1.0)) (* -0.75 3.141592653589793) 1e-14))
  (assert-true (sf4-near? (eval-num '(mods 7.0 4.0)) -1.0 1e-14))
  (assert-true (sf4-near? (eval-num '(mods -7.0 4.0)) 1.0 1e-14))
  (assert-true (sf4-near? (eval-num '(mods 5.5 4.0)) 1.5 1e-14)))

(deftest "sf4/10: производные ₂F₁ и F₁ — численно (DLMF 15.5.1; 16.16.1)"
  (let* ((e '(hypergeometric-2f1 0.5 0.7 1.9 (^ t 2)))
         (d (diff 't e)) (h 1e-6))
    (assert-true (sf4-near? (sf4-at d 0.6) (/ (- (sf4-at e (+ 0.6 h)) (sf4-at e (- 0.6 h))) (* 2 h)) 1e-8)))
  (let* ((e '(appell-f1 0.5 0.7 1.3 1.5 (* 0.5 t) (* 0.4 t)))
         (d (diff 't e)) (h 1e-6))
    (assert-true (sf4-near? (sf4-at d 0.8) (/ (- (sf4-at e (+ 0.8 h)) (sf4-at e (- 0.8 h))) (* 2 h)) 1e-8))))

(deftest "sf4/11: производные signum (0), atan2, mods"
  (assert-true (equal? (diff 't '(signum t)) 0))
  (assert-true (sf4-near? (sf4-at (diff 't '(atan2 (+ (sin t) 2) (cos t))) 0.4)
                          (/ (- (* (cos 0.4) (cos 0.4)) (* (+ (sin 0.4) 2) (- 0 (sin 0.4)))) (+ (^ (cos 0.4) 2) (^ (+ (sin 0.4) 2) 2))) 1e-12))
  (assert-true (sf4-near? (sf4-at (diff 't '(mods (* 3 t) 2)) 0.1) 3.0 1e-12)))
