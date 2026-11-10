; specfun-heads.lisp — SFn.2a: головы Бесселя, Эйри, Лежандра (производные, значения, печать).

(define (sfh-close? a b tol)
  (and (number? a) (number? b)
       (<= (abs (- a b)) (* tol (max 1.0 (abs b))))))

(define (sfh-at e x0) (eval-num (subst (list (list 'x x0)) e)))

; пятиточечная центральная разность: ошибка ~h^4, h = 1e-3
(define (sfh-nderiv e x0)
  (let ((h 0.001))
    (/ (+ (* -1 (sfh-at e (+ x0 (* 2 h))))
          (* 8 (sfh-at e (+ x0 h)))
          (* -8 (sfh-at e (- x0 h)))
          (sfh-at e (- x0 (* 2 h))))
       (* 12 h))))

(define (sfh-deriv-ok? e xs)
  (every? (lambda (x0) (sfh-close? (sfh-at (diff 'x e) x0) (sfh-nderiv e x0) 1e-7)) xs))

(deftest "SFn.2a: эталонные значения голов (отн. погрешность < 1e-12)"
  (let ((cases (list (list '(bessel-j 0 1.0) 0.7651976865579666)
                     (list '(bessel-j 1 2.0) 0.5767248077568734)
                     (list '(bessel-y 0 1.0) 0.08825696421567696)
                     (list '(bessel-i 0 1.0) 1.2660658777520082)
                     (list '(bessel-k 0 1.0) 0.42102443824070834)
                     (list '(airy-ai 0.0) 0.3550280538878172)
                     (list '(airy-ai-prime 0.0) -0.2588194037928068)
                     (list '(airy-bi 0.0) 0.6149266274460007)
                     (list '(airy-ai 10.0) 1.1047532552898687e-10)
                     (list '(legendre-p 3 1/2) -0.4375))))
    (for-each (lambda (c) (assert-true (sfh-close? (eval-num (car c)) (cadr c) 1e-12))) cases)))

(deftest "SFn.2a: производные согласны с численной разностью (5 точек)"
  ; аргумент — второй (порядок/степень — параметр)
  (assert-true (sfh-deriv-ok? '(bessel-j 0 x) '(0.3 0.8 1.5 2.5 4.0)))
  (assert-true (sfh-deriv-ok? '(bessel-j 2/3 x) '(0.4 1.0 2.0 3.0 5.0)))
  (assert-true (sfh-deriv-ok? '(bessel-y 0 x) '(0.3 0.8 1.5 2.5 4.0)))
  (assert-true (sfh-deriv-ok? '(bessel-i 0 x) '(0.3 0.8 1.5 2.5 4.0)))
  (assert-true (sfh-deriv-ok? '(bessel-k 0 x) '(0.3 0.8 1.5 2.5 4.0)))
  (assert-true (sfh-deriv-ok? '(airy-ai x) '(-2.0 -0.5 0.5 2.0 4.0)))
  (assert-true (sfh-deriv-ok? '(airy-bi x) '(-2.0 -0.5 0.5 2.0 4.0)))
  (assert-true (sfh-deriv-ok? '(airy-ai-prime x) '(-2.0 -0.5 0.5 2.0 4.0)))
  (assert-true (sfh-deriv-ok? '(legendre-p 3 x) '(-0.8 -0.3 0.2 0.5 0.8)))
  (assert-true (sfh-deriv-ok? '(legendre-q 2 x) '(-0.8 -0.3 0.2 0.5 0.8)))
  ; порядок — параметр: производная по x не должна его трогать
  (assert-true (not (sfh-deriv-ok? '(bessel-j (* 2 x) x) '(1.0)))))

(deftest "SFn.2a: полуцелые ν — элементарные формы"
  (let ((j12 (bessel-j 1/2 'x)) (jm12 (bessel-j -1/2 'x))
        (y12 (bessel-y 1/2 'x)) (i12 (bessel-i 1/2 'x)) (k12 (bessel-k 1/2 'x))
        (refj '(* (^ (* 2 (^ (* pi x) -1)) 1/2) (sin x)))
        (refjm '(* (^ (* 2 (^ (* pi x) -1)) 1/2) (cos x)))
        (refy '(* -1 (^ (* 2 (^ (* pi x) -1)) 1/2) (cos x)))
        (refi '(* (^ (* 2 (^ (* pi x) -1)) 1/2) (sinh x)))
        (refk '(* (^ (* pi (^ (* 2 x) -1)) 1/2) (exp (* -1 x)))))
    (for-each (lambda (e) (assert-true (not (and (pair? e) (equal? (car e) 'bessel-j)))))
              (list j12 jm12))
    (for-each (lambda (x0)
                (assert-true (sfh-close? (sfh-at j12 x0) (sfh-at refj x0) 1e-10))
                (assert-true (sfh-close? (sfh-at jm12 x0) (sfh-at refjm x0) 1e-10))
                (assert-true (sfh-close? (sfh-at y12 x0) (sfh-at refy x0) 1e-10))
                (assert-true (sfh-close? (sfh-at i12 x0) (sfh-at refi x0) 1e-10))
                (assert-true (sfh-close? (sfh-at k12 x0) (sfh-at refk x0) 1e-10)))
              '(0.3 1.0 2.5))))

(deftest "SFn.2a: полиномы Лежандра при целом n ≥ 0"
  (assert-true (equal? (simplify (list '- (legendre-p 2 'x) '(- (* 3/2 (^ x 2)) 1/2))) 0))
  (assert-true (equal? (simplify (list '- (legendre-p 3 'x) '(- (* 5/2 (^ x 3)) (* 3/2 x)))) 0))
  (assert-true (equal? (simplify (list '- (legendre-p 0 'x) 1)) 0))
  (assert-true (equal? (simplify (list '- (legendre-p 1 'x) 'x)) 0))
  ; символический n остаётся головой
  (assert-equal (legendre-p 'n 'x) '(legendre-p n x)))

(deftest "SFn.2a: рекуррентность Бесселя J_{ν−1} + J_{ν+1} = (2ν/x)·J_ν"
  (for-each
   (lambda (nu)
     (for-each
      (lambda (x0)
        (let ((lhs (eval-num (list '+ (list 'bessel-j (- nu 1) x0) (list 'bessel-j (+ nu 1) x0))))
              (rhs (eval-num (list '* (/ (* 2 nu) x0) (list 'bessel-j nu x0)))))
          (assert-true (sfh-close? lhs rhs 1e-10))))
      '(0.5 1.0 2.0 3.0 5.0)))
   '(2/3 1)))

(deftest "SFn.2a: Ai″ = x·Ai символьно; J_ν(0)"
  (assert-equal (simplify (diff 'x (diff 'x '(airy-ai x)))) (simplify '(* x (airy-ai x))))
  (assert-equal (simplify (diff 'x (diff 'x '(airy-bi x)))) (simplify '(* x (airy-bi x))))
  (assert-equal (bessel-j 0 0) 1)
  (assert-equal (bessel-j 1 0) 0)
  (assert-equal (bessel-j 2/3 0) 0)
  (assert-equal (bessel-i 0 0) 1))

(deftest "SFn.2a: печать и чтение входного языка — круговой тест"
  (for-each (lambda (e) (assert-equal (math-read (math-print e)) e))
            '((bessel-j 0 x) (bessel-y 2/3 x) (bessel-i 1 x) (bessel-k 0 x)
              (airy-ai x) (airy-bi x) (airy-ai-prime x) (airy-bi-prime x)
              (legendre-p 3 x) (legendre-q 1 x)))
  (assert-equal (math-print '(bessel-j 0 x)) "BesselJ(0, x)")
  (assert-equal (math-print '(airy-ai-prime x)) "AiryAiPrime(x)"))

(deftest "SFn.2a: вне области — не число, а не подделка"
  (assert-true (not (number? (eval-num '(bessel-y 0 -1.0)))))
  (assert-true (not (number? (eval-num '(bessel-k 0 -1.0)))))
  (assert-true (not (number? (eval-num '(legendre-q 0 1.0)))))
  ; J целая: J_0(−1) = J_0(1) — законное число
  (assert-true (sfh-close? (eval-num '(bessel-j 0 -1.0)) (eval-num '(bessel-j 0 1.0)) 1e-12))
  (assert-true (number? (eval-num '(bessel-k 0 0.5))))
  (assert-true (number? (eval-num '(legendre-q 0 1/2)))))

; ---------- SFn.2b: hyperexpand через головы и замкнутый вид ряда ----------

(define (sfb-has? e h) (or (equal? e h) (and (pair? e) (any? (lambda (z) (sfb-has? z h)) e))))

; сравнение гипергеометрического выражения (числом) с головным в 5 точках
(define (sfb-hy-close5 h e x)
  (every? (lambda (x0)
            (let ((a (hyper-eval (subst (list (list x x0)) h)))
                  (b (eval-num (subst (list (list x x0)) e))))
              (and (number? a) (number? b) (< (abs (- a b)) 1e-10))))
          '(1/5 1/3 1/2 2/3 3/4)))

(deftest "SFn.2b: ₀F₁(;1;∓x²/4) → J₀ / I₀"
  (let* ((hj '(hyper () (1) (* -1/4 (^ x 2))))
         (hi '(hyper () (1) (* 1/4 (^ x 2))))
         (ej (hyperexpand hj)) (ei (hyperexpand hi)))
    (assert-equal ej '(bessel-j 0 x))
    (assert-equal ei '(bessel-i 0 x))
    (assert-true (sfb-hy-close5 hj ej 'x))
    (assert-true (sfb-hy-close5 hi ei 'x))))

(deftest "SFn.2b: ₀F₁(;2/3;x³/9), ₀F₁(;4/3;x³/9) → комбинации Ai, Bi"
  (let* ((h1 '(hyper () (2/3) (* 1/9 (^ x 3))))
         (h2 '(hyper () (4/3) (* 1/9 (^ x 3))))
         (e1 (hyperexpand h1)) (e2 (hyperexpand h2)))
    (assert-true (sfb-has? e1 'airy-ai))
    (assert-true (sfb-has? e1 'airy-bi))
    (assert-true (sfb-has? e2 'airy-ai))
    (assert-true (sfb-has? e2 'airy-bi))
    (assert-true (sfb-hy-close5 h1 e1 'x))
    (assert-true (sfb-hy-close5 h2 e2 'x))))

(deftest "SFn.2b: ₂F₁(−n, n+1; 1; (1−x)/2) = P_n(x)"
  (for-each
   (lambda (n)
     (let* ((h (list 'hyper (list (- 0 n) (+ n 1)) '(1) '(* 1/2 (- 1 x))))
            (e (hyperexpand h)))
       (assert-true (sfb-hy-close5 h e 'x))
       (assert-true (equal? (simplify (list '- e (legendre-p n 'x))) 0))))
   '(2 3 4)))

(deftest "SFn.2b: dsolve-series — Эйри → Ai/Bi, Бессель ν=0 → J₀, Лежандр n=2 → P₂"
  (let* ((eqa '(= (diff (diff (y x) x) x) (* x (y x))))
         (ra (dsolve-series eqa '(y x)))
         (ea (car (ode-solutions ra)))
         (eqb '(= (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x)) (* (^ x 2) (y x))) 0))
         (rb (dsolve-series eqb '(y x)))
         (eb (car (ode-solutions rb)))
         (eql '(= (+ (* (- 1 (^ x 2)) (diff (diff (y x) x) x)) (* -2 x (diff (y x) x)) (* 6 (y x))) 0))
         (rl (dsolve-series eql '(y x)))
         (el (car (ode-solutions rl)))
         (poly (simplify (subst (list (list 'C1 1) (list 'C2 0)) (caddr el)))))
    ; Эйри: обе головы Ai и Bi, сертификат замкнутого вида
    (assert-equal (ode-status ra) 'ok)
    (assert-true (sfb-has? ea 'airy-ai))
    (assert-true (sfb-has? ea 'airy-bi))
    (assert-equal (ode::ode-field ra :closed-form) #t)
    (assert-true (ode-series-check eqa ea '(y x)))
    ; Бессель ν = 0: первая ветвь J₀, вторая — ряд с log
    (assert-equal (ode-status rb) 'ok)
    (assert-true (sfb-has? eb 'bessel-j))
    (assert-true (sfb-has? eb 'log))
    (assert-true (ode-series-check eqb eb '(y x)))
    ; Лежандр n = 2: полиномиальная ветвь кратна P₂ (1 − 3x² = −2P₂)
    (assert-equal (ode-status rl) 'ok)
    (assert-true (equal? (simplify (expand (list '- poly (list '* -2 (legendre-p 2 'x))))) 0))
    (assert-true (ode-series-check eql el '(y x)))))
