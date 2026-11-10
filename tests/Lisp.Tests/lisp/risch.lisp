; Lisp-тесты алгоритма Риша, подшаг 21k.1: lib\risch\field.lisp (башня, rs-deriv, арифметика K[θ], gcdex, ПРС, порядки).
; Внутренние имена модуля risch вызываются как risch::rs-…; θ₁ = %t1, θ₂ = %t2. Многочлен K[θ] — список коэффициентов, старшая степень первой.

(define rt-zero? risch::rs-zero?)
(define rt-poly risch::rs-from-expr)
; равенство выражений из K и многочленов K[θ]
(define (rt-eq? a b) (rt-zero? (list '+ a (list '* -1 b))))
(define (rt-peq? p q) (null? (risch::rs-sub p q)))

(define rt-t1 '%t1)
(define rt-t2 '%t2)
; башни: A = ℚ(x)(log x); B = ℚ(x)(exp x²); C = log x, exp(x·log x) (высота 2, x^x); D = log x, log(log x)
(define rt-A (risch::rs-extend (risch::rs-tower 'x) rt-t1 'log 'x))
(define rt-B (risch::rs-extend (risch::rs-tower 'x) rt-t1 'exp '(^ x 2)))
(define rt-C (risch::rs-extend rt-A rt-t2 'exp '(* x %t1)))
(define rt-D (risch::rs-extend rt-A rt-t2 'log '%t1))

(deftest "риш/башня: Dθ для log и exp, уровни высоты 2"
  (assert-equal (risch::rs-level-dtheta (risch::rs-top rt-A)) '(^ x -1))
  (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top rt-B)) '(* 2 x %t1)))
  ; θ₂ = exp(x·log x): Dθ₂ = (log x + 1)·θ₂
  (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top rt-C)) '(* (+ %t1 1) %t2)))
  ; θ₂ = log(log x): Dθ₂ = 1/(x·log x)
  (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top rt-D)) '(* (^ x -1) (^ %t1 -1))))
  (assert-error (risch::rs-extend rt-A rt-t2 'sin 'x)))

(deftest "риш/rs-case: base, primitive, exp"
  (assert-equal (risch::rs-case (risch::rs-tower 'x)) 'base)
  (assert-equal (risch::rs-case rt-A) 'primitive)
  (assert-equal (risch::rs-case rt-B) 'exp)
  (assert-equal (risch::rs-case rt-C) 'exp)
  (assert-equal (risch::rs-case rt-D) 'primitive)
  (assert-equal (risch::rs-case (risch::rs-lower rt-C)) 'primitive))

(deftest "риш/rs-zero?: нуль распознаётся после приведения к общему знаменателю"
  (assert-true (rt-zero? '(+ (^ x -1) (^ (+ x 1) -1) (* -1 (+ (* 2 x) 1) (^ x -1) (^ (+ x 1) -1)))))
  (assert-true (rt-zero? '(+ (* (+ x 1) %t1 (^ %t2 -2)) (* -1 x %t1 (^ %t2 -2)) (* -1 %t1 (^ %t2 -2)))))
  (assert-true (not (rt-zero? '(+ (^ x -1) (^ (+ x 1) -1)))))
  (assert-true (rt-zero? 0)))

(deftest "риш/rs-deriv: башня log x — производные многочленов и дробей от θ"
  (assert-true (rt-eq? (risch::rs-deriv rt-A '%t1) '(^ x -1)))
  (assert-true (rt-eq? (risch::rs-deriv rt-A '(^ %t1 2)) '(* 2 %t1 (^ x -1))))
  ; D(x·log x) = log x + 1
  (assert-true (rt-eq? (risch::rs-deriv rt-A '(* x %t1)) '(+ %t1 1)))
  ; D(1/θ) = −1/(xθ²)
  (assert-true (rt-eq? (risch::rs-deriv rt-A '(^ %t1 -1)) '(* -1 (^ x -1) (^ %t1 -2)))))

(deftest "риш/rs-deriv: башня exp(x²), D(θ) = 2xθ"
  (assert-true (rt-eq? (risch::rs-deriv rt-B '%t1) '(* 2 x %t1)))
  (assert-true (rt-eq? (risch::rs-deriv rt-B '(* x %t1)) '(* (+ 1 (* 2 (^ x 2))) %t1)))
  ; D(1/(θ+1)) = −2xθ/(θ+1)²
  (assert-true (rt-eq? (risch::rs-deriv rt-B '(^ (+ %t1 1) -1)) '(* -2 x %t1 (^ (+ %t1 1) -2)))))

(deftest "риш/rs-deriv: высота 2 — x^x = exp(x log x) и log log x"
  (assert-true (rt-eq? (risch::rs-deriv rt-C '%t2) '(* (+ %t1 1) %t2)))
  ; D(θ₂²) = 2(θ₁ + 1)θ₂²; ∫ (x^x)(log x + 1) = x^x
  (assert-true (rt-eq? (risch::rs-deriv rt-C '(^ %t2 2)) '(* 2 (+ %t1 1) (^ %t2 2))))
  (assert-true (rt-eq? (risch::rs-deriv rt-C '(* x %t2)) '(+ %t2 (* x (+ %t1 1) %t2))))
  (assert-true (rt-eq? (risch::rs-deriv rt-D '%t2) '(* (^ x -1) (^ %t1 -1))))
  (assert-true (rt-eq? (risch::rs-deriv rt-D '(* %t1 %t2)) '(+ (* %t2 (^ x -1)) (^ x -1)))))

(deftest "риш/rs-deriv: правило Лейбница и линейность на башне высоты 2"
  (let ((f '(+ (* %t1 %t2) (^ (+ x %t2) -1))) (g '(* (^ x -1) (+ (^ %t2 2) %t1))))
    (assert-true (rt-eq? (risch::rs-deriv rt-C (list '* f g))
                         (list '+ (list '* (risch::rs-deriv rt-C f) g) (list '* f (risch::rs-deriv rt-C g)))))
    (assert-true (rt-eq? (risch::rs-deriv rt-C (list '+ f (list '* 3 g)))
                         (list '+ (risch::rs-deriv rt-C f) (list '* 3 (risch::rs-deriv rt-C g)))))))

(deftest "риш/переход выражение ↔ список: коэффициенты — рациональные функции от x"
  (let* ((e '(+ (* (^ x -1) (^ %t1 2)) (* (+ x 1) %t1) (^ (+ x 2) -1)))
         (p (rt-poly e '%t1)))
    (assert-equal (length p) 3)
    (assert-true (rt-eq? (car p) '(^ x -1)))
    (assert-true (rt-eq? (cadr p) '(+ x 1)))
    (assert-true (rt-eq? (risch::rs-to-expr p '%t1) e))
    (assert-equal (rt-poly 0 '%t1) '())
    (assert-error (rt-poly '(^ %t1 -1) '%t1))))

(deftest "риш/деление с остатком в ℚ(x)[θ]"
  (let* ((a (rt-poly '(+ (^ %t1 3) 1) '%t1)) (b (rt-poly '(+ (* x %t1) 1) '%t1))
         (qr (risch::rs-divmod a b)))
    (assert-true (< (risch::rs-deg (cadr qr)) 1))
    (assert-true (rt-peq? a (risch::rs-add (risch::rs-mul (car qr) b) (cadr qr))))
    ; старший коэффициент частного 1/x
    (assert-true (rt-eq? (car (car qr)) '(^ x -1)))
    ; делимость без остатка
    (assert-equal (cadr (risch::rs-divmod (risch::rs-mul a b) b)) '())
    (assert-error (risch::rs-divmod a '()))))

(deftest "риш/НОД в ℚ(x)[θ]: унитарный, коэффициенты из ℚ(x)"
  (let* ((c (rt-poly '(+ %t1 (* -1 (^ x -1))) '%t1))
         (a (risch::rs-mul c (rt-poly '(+ %t1 x) '%t1)))
         (b (risch::rs-mul c (rt-poly '(+ (* x %t1) 2) '%t1)))
         (g (risch::rs-gcd a b)))
    (assert-true (rt-peq? g c))
    (assert-true (rt-peq? (risch::rs-gcd a '()) (risch::rs-monic a)))
    ; взаимно простые: НОД = 1
    (assert-true (rt-peq? (risch::rs-gcd (rt-poly '(+ %t1 x) '%t1) (rt-poly '(+ %t1 (* 2 x)) '%t1)) (list 1)))))

(deftest "риш/rs-gcdex: s·a + t·b = g"
  (let* ((a (rt-poly '(* (+ %t1 x) (+ (^ %t1 2) 1)) '%t1))
         (b (rt-poly '(* (+ %t1 x) (+ %t1 (^ x -1))) '%t1))
         (e (risch::rs-gcdex a b)))
    (assert-true (rt-peq? (caddr e) (rt-poly '(+ %t1 x) '%t1)))
    (assert-true (rt-peq? (risch::rs-add (risch::rs-mul (car e) a) (risch::rs-mul (cadr e) b)) (caddr e)))
    ; взаимно простые: тождество Безу с 1
    (let* ((a2 (rt-poly '(+ (^ %t1 2) x) '%t1)) (b2 (rt-poly '(+ %t1 (^ x -1)) '%t1)) (e2 (risch::rs-gcdex a2 b2)))
      (assert-true (rt-peq? (caddr e2) (list 1)))
      (assert-true (rt-peq? (risch::rs-add (risch::rs-mul (car e2) a2) (risch::rs-mul (cadr e2) b2)) (list 1))))))

(deftest "риш/rs-diophantine: s·a + t·b = c, deg s < deg b; нет решения при НОД ∤ c"
  (let* ((a (rt-poly '(+ (^ %t1 2) x) '%t1)) (b (rt-poly '(+ %t1 (^ x -1)) '%t1))
         (c (rt-poly '(+ (* x (^ %t1 3)) 1) '%t1))
         (st (risch::rs-diophantine a b c)))
    (assert-true st)
    (assert-true (< (risch::rs-deg (car st)) (risch::rs-deg b)))
    (assert-true (rt-peq? (risch::rs-add (risch::rs-mul (car st) a) (risch::rs-mul (cadr st) b)) c)))
  ; общий множитель θ: правая часть θ разрешима, 1 — нет
  (let ((a (rt-poly '(* %t1 (+ %t1 1)) '%t1)) (b (rt-poly '(* %t1 (+ %t1 x)) '%t1)))
    (assert-equal (risch::rs-diophantine a b (list 1)) #f)
    (let ((st (risch::rs-diophantine a b (rt-poly '%t1 '%t1))))
      (assert-true st)
      (assert-true (rt-peq? (risch::rs-add (risch::rs-mul (car st) a) (risch::rs-mul (cadr st) b)) (rt-poly '%t1 '%t1))))))

(deftest "риш/rs-sqfree: бесквадратное разложение по θ"
  (let* ((f1 (rt-poly '(+ %t1 (* -1 (^ x -1))) '%t1)) (f3 (rt-poly '(+ %t1 x) '%t1))
         (p (risch::rs-scale (risch::rs-mul (risch::rs-mul f1 f1) (risch::rs-mul f3 (risch::rs-mul f3 f3))) '(* 2 x)))
         (r (risch::rs-sqfree p)))
    (assert-true (rt-eq? (car r) '(* 2 x)))
    (assert-equal (length (cdr r)) 2)
    (assert-equal (map cadr (cdr r)) '(2 3))
    (assert-true (rt-peq? (car (car (cdr r))) f1))
    (assert-true (rt-peq? (car (cadr (cdr r))) f3))
    ; бесквадратный многочлен — один множитель кратности 1
    (assert-equal (map cadr (cdr (risch::rs-sqfree f3))) '(1))
    (assert-equal (risch::rs-sqfree (list 5)) '(5))))

(deftest "риш/rs-prs: члены по убыванию степени, последний — НОД"
  (let* ((c (rt-poly '(+ %t1 1) '%t1))
         (a (risch::rs-mul c (rt-poly '(+ (^ %t1 2) x) '%t1)))
         (b (risch::rs-mul c (rt-poly '(+ %t1 (^ x -1)) '%t1)))
         (prs (risch::rs-prs a b)) (g (last prs)))
    (assert-equal (risch::rs-deg (car prs)) 3)
    (assert-equal (risch::rs-deg g) 1)
    (assert-true (rt-peq? (risch::rs-monic g) c))
    ; степени строго убывают
    (assert-true (every? (lambda (b) b) (map2 (lambda (p q) (> (risch::rs-deg p) (risch::rs-deg q))) (take prs (- (length prs) 1)) (cdr prs))))
    (assert-true (risch::rs-prs-member prs 1))
    (assert-equal (risch::rs-prs-member prs 0) #f)))

(deftest "риш/rs-prs над K[z]: результант res_θ(d, a − z·Dd) с точностью до множителя (пример туториала, θ = log x)"
  ; f = (2θ² − θ − x²)/(θ³ − x²θ): d = θ³ − x²θ, a = 2θ² − θ − x²
  (let* ((d (rt-poly '(+ (^ %t1 3) (* -1 (^ x 2) %t1)) '%t1))
         (a (rt-poly '(+ (* 2 (^ %t1 2)) (* -1 %t1) (* -1 (^ x 2))) '%t1))
         (b (risch::rs-sub a (risch::rs-scale (risch::rs-deriv-poly rt-A d) 'z)))
         (prs (risch::rs-prs d b))
         (m0 (risch::rs-prs-member prs 0))
         (res (resultant (risch::rs-to-expr d '%t1) (numer (together (risch::rs-to-expr b '%t1))) '%t1)))
    (assert-true m0)
    (assert-true (not (rt-zero? (car m0))))
    ; отношение члена степени 0 к результанту не зависит от z
    (assert-true (not (contains-sym? (together (list '* (car m0) (list '^ res -1))) 'z)))))

(deftest "риш/rs-deriv-poly: производная многочлена по башне"
  ; log x: D(θ²) = 2θ/x;  D(x θ) = θ + 1
  (assert-true (rt-peq? (risch::rs-deriv-poly rt-A (rt-poly '(^ %t1 2) '%t1)) (rt-poly '(* 2 (^ x -1) %t1) '%t1)))
  (assert-true (rt-peq? (risch::rs-deriv-poly rt-A (rt-poly '(* x %t1) '%t1)) (rt-poly '(+ %t1 1) '%t1)))
  ; exp x²: D(x θ²) = (1 + 4x²)θ²
  (assert-true (rt-peq? (risch::rs-deriv-poly rt-B (rt-poly '(* x (^ %t1 2)) '%t1)) (rt-poly '(* (+ 1 (* 4 (^ x 2))) (^ %t1 2)) '%t1)))
  ; высота 2: D(θ₂) = (θ₁ + 1)θ₂ как многочлен по θ₂
  (assert-true (rt-peq? (risch::rs-deriv-poly rt-C (rt-poly '%t2 '%t2)) (rt-poly '(* (+ %t1 1) %t2) '%t2)))
  (assert-equal (risch::rs-deriv-poly rt-A '()) '()))

(deftest "риш/порядки: order_at и order_at_oo"
  (let* ((p (rt-poly '%t1 '%t1)) (q (rt-poly '(+ %t1 x) '%t1))
         (a (risch::rs-mul (risch::rs-mul p p) (risch::rs-mul q (risch::rs-mul q q)))))
    (assert-equal (risch::rs-order-at a p) 2)
    (assert-equal (risch::rs-order-at a q) 3)
    (assert-equal (risch::rs-order-at (list 1 0 0 1) p) 0)
    (assert-equal (risch::rs-order-at '() p) 'inf)
    ; a/d = θ³/θ⁵-ish: порядок в бесконечности = deg d − deg a
    (assert-equal (risch::rs-order-at-oo (rt-poly '(+ (^ %t1 2) x) '%t1) a) 3)
    (assert-equal (risch::rs-order-at-oo a (list 1)) -5)
    (assert-equal (risch::rs-order-at-oo '() a) 'inf)))

; ---------- подшаг 21k.2: lib\risch\tower.lisp — построение башни (эталонные примеры) ----------
; (risch::rs-build-tower e x) → (башня выражение-в-θ таблица) | #f; уровень (θ вид аргумент Dθ)
(define (rt-build e) (risch::rs-build-tower e 'x))
(define (rt-levels r) (cdr (car r)))
(define (rt-kinds r) (map cadr (rt-levels r)))
(define (rt-dth r i) (nth (nth (rt-levels r) i) 3))
(define (rt-arg r i) (nth (nth (rt-levels r) i) 2))
(define (rt-th r i) (car (nth (rt-levels r) i)))
; обратная подстановка возвращает выражение, равное исходному
(define (rt-back-ok? e r) (equal? (simplify (risch::rs-back-subst (cadr r) (caddr r))) (simplify e)))
; «не знаю»: #f и условие (risch-unknown …) в канале
(define (rt-unknown? e)
  (let ((cr (capture-conditions (lambda () (rt-build e)))))
    (and (not (car cr)) (any? (lambda (c) (equal? (car (car c)) 'risch-unknown)) (cadr cr)))))

(deftest "риш/башня: exp x — один уровень, Dθ = θ"
  (let ((r (rt-build '(exp x))))
    (assert-equal (rt-kinds r) '(exp))
    (assert-true (rt-eq? (rt-dth r 0) (rt-th r 0)))
    (assert-equal (cadr r) (rt-th r 0))
    (assert-true (rt-back-ok? '(exp x) r))))

(deftest "риш/башня: exp(x²)·exp(x) — два уровня, произведение θ₁θ₂"
  (let ((r (rt-build '(* (exp (^ x 2)) (exp x)))))
    (assert-equal (rt-kinds r) '(exp exp))
    (assert-equal (rt-arg r 0) 'x)
    (assert-true (rt-eq? (rt-dth r 1) (list '* 2 'x (rt-th r 1))))
    (assert-true (rt-eq? (cadr r) (list '* (rt-th r 0) (rt-th r 1))))))

(deftest "риш/башня: exp(x+x²) при уровнях exp x и exp x² переписывается как θ₁θ₂ (структурная теорема)"
  (let* ((e '(+ (exp x) (exp (^ x 2)) (exp (+ x (^ x 2))))) (r (rt-build e)))
    (assert-equal (length (rt-levels r)) 2)
    (assert-true (rt-eq? (cadr r) (list '+ (rt-th r 0) (rt-th r 1) (list '* (rt-th r 0) (rt-th r 1)))))
    (assert-true (rt-back-ok? e r))))

(deftest "риш/башня integer_powers: exp(2x) + exp x → θ² + θ, θ = exp x"
  (let ((r (rt-build '(+ (exp (* 2 x)) (exp x)))))
    (assert-equal (length (rt-levels r)) 1)
    (assert-equal (rt-arg r 0) 'x)
    (assert-true (rt-eq? (cadr r) (list '+ (rt-th r 0) (list '^ (rt-th r 0) 2))))))

(deftest "риш/башня integer_powers: exp x + exp(x/2) — общая образующая exp(x/2); exp(x/2) + exp(x/3) — exp(x/6)"
  (let ((r (rt-build '(+ (exp x) (exp (* 1/2 x))))))
    (assert-equal (length (rt-levels r)) 1)
    (assert-true (rt-eq? (rt-arg r 0) '(* 1/2 x)))
    (assert-true (rt-eq? (cadr r) (list '+ (rt-th r 0) (list '^ (rt-th r 0) 2))))
    (assert-true (rt-back-ok? '(+ (exp x) (exp (* 1/2 x))) r)))
  (let ((r (rt-build '(+ (exp (* 1/2 x)) (exp (* 1/3 x))))))
    (assert-equal (length (rt-levels r)) 1)
    (assert-true (rt-eq? (rt-arg r 0) '(* 1/6 x)))
    (assert-true (rt-eq? (cadr r) (list '+ (list '^ (rt-th r 0) 2) (list '^ (rt-th r 0) 3))))))

(deftest "риш/башня: x^x = exp(x·log x) — log x, затем exp(xθ₁), Dθ₂ = (θ₁ + 1)θ₂"
  (let ((r (rt-build '(^ x x))))
    (assert-equal (rt-kinds r) '(log exp))
    (assert-true (rt-eq? (rt-dth r 0) '(^ x -1)))
    (assert-true (rt-eq? (rt-dth r 1) (list '* (list '+ (rt-th r 0) 1) (rt-th r 1))))
    (assert-true (rt-back-ok? '(exp (* x (log x))) r))))

(deftest "риш/башня: log(log x) — два log-уровня, Dθ₂ = 1/(x·θ₁)"
  (let ((r (rt-build '(log (log x)))))
    (assert-equal (rt-kinds r) '(log log))
    (assert-equal (rt-arg r 1) (rt-th r 0))
    (assert-true (rt-eq? (rt-dth r 1) (list '* '(^ x -1) (list '^ (rt-th r 0) -1))))
    (assert-true (rt-back-ok? '(log (log x)) r))))

(deftest "риш/башня: log(x²) = 2·log x (factor-list)"
  (let ((r (rt-build '(log (^ x 2)))))
    (assert-equal (rt-kinds r) '(log))
    (assert-equal (rt-arg r 0) 'x)
    (assert-true (rt-eq? (cadr r) (list '* 2 (rt-th r 0))))))

(deftest "риш/башня: log x + log(x+1) и log(x(x+1)) — одна и та же башня из двух уровней"
  (let ((r1 (rt-build '(+ (log x) (log (+ x 1))))) (r2 (rt-build '(log (* x (+ x 1))))))
    (assert-equal (rt-kinds r1) '(log log))
    (assert-true (rt-eq? (rt-dth r1 1) '(^ (+ x 1) -1)))
    (assert-equal (car r1) (car r2))
    (assert-true (rt-eq? (cadr r2) (list '+ (rt-th r2 0) (rt-th r2 1))))))

(deftest "риш/башня: константы ветвей — log(2x) = θ + log 2, log 12 по простым"
  (let ((r (rt-build '(+ (log x) (log (* 2 x))))))
    (assert-equal (length (rt-levels r)) 1)
    (assert-true (rt-eq? (cadr r) (list '+ (list '* 2 (rt-th r 0)) '(log 2)))))
  (let ((r (rt-build '(log (* 12 x)))))
    (assert-true (rt-eq? (cadr r) (list '+ (rt-th r 0) '(* 2 (log 2)) '(log 3))))))

(deftest "риш/башня: exp(x + log x) = x·eˣ, exp(x+1) = e·eˣ, log(exp x) = x; лишние уровни отбрасываются"
  (let ((r (rt-build '(exp (+ x (log x))))))
    (assert-equal (rt-kinds r) '(exp))
    (assert-true (rt-eq? (cadr r) (list '* 'x (rt-th r 0)))))
  (let ((r (rt-build '(exp (+ x 1)))))
    (assert-true (rt-eq? (cadr r) (list '* '(exp 1) (rt-th r 0)))))
  (let ((r (rt-build '(log (exp x)))))
    (assert-equal (rt-levels r) '())
    (assert-equal (cadr r) 'x)))

(deftest "риш/башня: a^x и x^a через exp; параметр — генерическая независимость с условием"
  (let ((r (rt-build '(^ 2 x))))
    (assert-equal (rt-kinds r) '(exp))
    (assert-true (rt-eq? (rt-dth r 0) (list '* '(log 2) (rt-th r 0)))))
  (let* ((cr (capture-conditions (lambda () (rt-build '(+ (exp x) (exp (* a x)))))))
         (r (car cr)))
    (assert-equal (rt-kinds r) '(exp exp))
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-generic)) (cadr cr)))))

(deftest "риш/башня: sinh, tanh — через exp"
  (let ((r (rt-build '(sinh x))))
    (assert-equal (length (rt-levels r)) 1)
    (assert-true (rt-eq? (cadr r) (list '* 1/2 (list '+ (rt-th r 0) (list '* -1 (list '^ (rt-th r 0) -1)))))))
  (let ((r (rt-build '(tanh x))))
    (assert-true (rt-eq? (rt-arg r 0) '(* 2 x)))
    (assert-true (rt-eq? (cadr r) (list '* (list '+ (rt-th r 0) -1) (list '^ (list '+ (rt-th r 0) 1) -1))))))

(deftest "риш/башня: обратная подстановка — exp(exp x), log(1 + eˣ), смешанная башня"
  (let* ((e '(exp (exp x))) (r (rt-build e)))
    (assert-equal (rt-kinds r) '(exp exp))
    (assert-true (rt-eq? (rt-dth r 1) (list '* (rt-th r 0) (rt-th r 1))))
    (assert-true (rt-back-ok? e r)))
  (let* ((e '(* (log (+ 1 (exp x))) (^ (+ x (log x)) -1))) (r (rt-build e)))
    (assert-equal (length (rt-levels r)) 3)
    (assert-true (rt-back-ok? e r))))

(deftest "риш/башня: «не знаю» — sqrt x, x^(1/3), sin(sin x), asin x, exp(log x / 2) = √x (sin x — tan-уровень с 21k″)"
  (assert-true (rt-unknown? '(sqrt x)))
  (assert-true (rt-unknown? '(^ x 1/3)))
  (assert-true (rt-unknown? '(sin (sin x))))
  (assert-true (rt-unknown? '(* (exp x) (asin x))))                   ; atan с 21k.5′ — уровень башни
  (assert-true (rt-unknown? '(exp (* 1/2 (log x)))))
  ; от x не зависит — башня пустая, константы не трогаются
  (assert-equal (car (rt-build '(+ (sin 1) (log 2)))) '(x)))

; ---------- подшаг 21k.3: lib\risch\reduce.lisp (splitfactor, canonical, Эрмит, ЛРТ) ----------
; rh-T — башня tan (Dθ = θ² + 1: специальны только степени θ² + 1), rh-N — башня с параметром ν (Dθ = −θ² − θ/x − (1 − ν²/x²))
(define rh-T (list 'x (list '%t1 'tan 'x '(+ 1 (^ %t1 2)))))
(define rh-N (list 'x (list '%t1 'bessel 'x '(+ (* -1 (^ %t1 2)) (* -1 %t1 (^ x -1)) -1 (* nu nu (^ x -2))))))
(define (rh-P e) (rt-poly e '%t1))
(define (rh-E tw f) (risch::rs-frac-expr tw f))
; тождество a/d = Dg + h + r и свойства h: знаменатель бесквадратный и нормальный
(define (rh-hermite-ok? tw a d)
  (let* ((r (risch::rs-hermite tw (rh-P a) (rh-P d))) (g (car r)) (h (cadr r)) (s (risch::rs-sqfree (cadr h))))
    (and (rt-eq? (list '* a (list '^ d -1))
                 (list '+ (risch::rs-deriv tw (rh-E tw g)) (rh-E tw h) (rh-E tw (caddr r))))
         (every? (lambda (fm) (and (= (cadr fm) 1) (not (risch::rs-special? tw (car fm))))) (cdr s)))))
(define (rh-fe? tw f e) (rt-eq? (rh-E tw f) e))
; S из ЛРТ — список коэффициентов-выражений (от z = %rsz); сравнение с многочленом-образцом
(define (rh-S=? S e) (let ((p (rh-P e))) (and (= (length S) (length p)) (every? (lambda (c) (rt-eq? (car c) (cadr c))) (map2 list S p)))))

(deftest "риш/splitfactor: exp — специальная часть θ^m, log — специальной нет, tan — (θ²+1)^m"
  (let* ((r (risch::rs-splitfactor rt-B (rh-P '(+ (* x (^ %t1 3)) (* x (^ %t1 2)))))))
    (assert-true (rt-peq? (cadr r) (rh-P '(^ %t1 2))))
    (assert-true (rt-peq? (car r) (rh-P '(* x (+ %t1 1))))))
  (let ((r (risch::rs-splitfactor rt-A (rh-P '(* (^ %t1 2) (+ %t1 x))))))
    (assert-true (rt-peq? (cadr r) (rh-P 1)))
    (assert-true (rt-peq? (car r) (rh-P '(* (^ %t1 2) (+ %t1 x))))))
  (let ((r (risch::rs-splitfactor rh-T (rh-P '(* %t1 (^ (+ (^ %t1 2) 1) 2))))))
    (assert-true (rt-peq? (cadr r) (rh-P '(^ (+ (^ %t1 2) 1) 2))))
    (assert-true (rt-peq? (car r) (rh-P '%t1)))))

(deftest "риш/splitfactor_sqf: кратности и старший коэффициент; нуль"
  (let ((r (risch::rs-splitfactor-sqf rt-B (rh-P '(* 3 %t1 (^ (+ %t1 x) 2))))))
    (assert-true (rt-eq? (car r) 3))
    (assert-equal (map cadr (cadr r)) '(2))
    (assert-equal (map cadr (caddr r)) '(1)))
  (assert-equal (risch::rs-splitfactor rt-B '()) (list '() (list 1))))

(deftest "риш/canonical_representation: a/d = P + an/dn + as/ds, tan и exp"
  (let* ((a '(+ (* x (^ %t1 5)) %t1 1)) (d '(* (^ %t1 2) (+ (^ %t1 2) 1)))
         (r (risch::rs-canonical rh-T (rh-P a) (rh-P d))))
    (assert-true (rt-peq? (cadr (cadr r)) (rh-P '(^ %t1 2))))
    (assert-true (rt-peq? (cadr (caddr r)) (rh-P '(+ (^ %t1 2) 1))))
    (assert-true (rt-eq? (list '* a (list '^ d -1))
                         (list '+ (rh-E rh-T (list (car r) (list 1))) (rh-E rh-T (cadr r)) (rh-E rh-T (caddr r)))))
    (assert-true (< (risch::rs-deg (car (cadr r))) 2)))
  (let* ((a '(+ (* x %t1) 2)) (d '(* (^ %t1 3) (^ (+ %t1 1) 2))) (r (risch::rs-canonical rt-B (rh-P a) (rh-P d))))
    (assert-true (rt-peq? (cadr (caddr r)) (rh-P '(^ %t1 3))))
    (assert-true (rt-eq? (list '* a (list '^ d -1))
                         (list '+ (rh-E rt-B (list (car r) (list 1))) (rh-E rt-B (cadr r)) (rh-E rt-B (caddr r)))))))

(deftest "риш/Эрмит: пример 8 туториала (tan), (x − t)/t² = D(−x/t) + (−x)"
  (let ((r (risch::rs-hermite rh-T (rh-P '(- x %t1)) (rh-P '(^ %t1 2)))))
    (assert-true (rh-fe? rh-T (car r) '(* -1 x (^ %t1 -1))))
    (assert-true (rh-fe? rh-T (cadr r) 0))
    (assert-true (rh-fe? rh-T (caddr r) '(* -1 x)))
    (assert-true (rh-hermite-ok? rh-T '(- x %t1) '(^ %t1 2)))))

(deftest "риш/Эрмит (эталонный пример 1): log, кратный знаменатель, h = 0, r = 0"
  (let* ((a '(+ (* (- (* 3 x) 2) (^ %t1 3)) (* (- x 1) (^ %t1 2)) (* (- (* 2 (^ x 2)) (* 4 x)) %t1) (^ x 2)))
         (d '(+ (* x (^ %t1 6)) (* -4 (^ x 2) (^ %t1 5)) (* 6 (^ x 3) (^ %t1 4)) (* -4 (^ x 4) (^ %t1 3)) (* (^ x 5) (^ %t1 2))))
         (r (risch::rs-hermite rt-A (rh-P a) (rh-P d))))
    (assert-true (rh-fe? rt-A (car r) '(* (+ (* 3 (^ %t1 2)) %t1 (* 3 x)) (^ (+ (* 3 (^ %t1 4)) (* -9 x (^ %t1 3)) (* 9 (^ x 2) (^ %t1 2)) (* -3 (^ x 3) %t1)) -1))))
    (assert-true (rh-fe? rt-A (cadr r) 0))
    (assert-true (rh-fe? rt-A (caddr r) 0))
    (assert-true (rh-hermite-ok? rt-A a d))))

(deftest "риш/Эрмит (эталонные примеры 2, 3): log, (t − 1)², (x³t³ − x)"
  (let ((r (risch::rs-hermite rt-A (rh-P '(+ (* -1 (^ %t1 2)) (* 2 %t1) 2)) (rh-P '(* -1 x (^ (- %t1 1) 2))))))
    (assert-true (rh-fe? rt-A (car r) '(* 3 (^ (- %t1 1) -1))))
    (assert-true (rh-fe? rt-A (cadr r) 0))
    (assert-true (rh-fe? rt-A (caddr r) '(^ x -1))))
  (let* ((a '(+ (* (* -1 (^ x 2)) (^ %t1 6)) (* (+ -1 (* -2 (^ x 3)) (^ x 4)) (^ %t1 3)) (* (- -3 (* 3 (^ x 4))) (^ %t1 2)) (* -2 x %t1) (- (- x) (* 3 (^ x 2)))))
         (d '(+ (* (^ x 4) (^ %t1 6)) (* -2 (^ x 2) (^ %t1 3)) 1))
         (r (risch::rs-hermite rt-A (rh-P a) (rh-P d))))
    (assert-true (rh-fe? rt-A (car r) '(* (+ (* (^ x 3) %t1) (^ x 4) 1) (^ (- (* (^ x 3) (^ %t1 3)) x) -1))))
    (assert-true (rh-fe? rt-A (cadr r) 0))
    (assert-true (rh-fe? rt-A (caddr r) '(* -1 (^ x -2))))))

(deftest "риш/Эрмит (эталонный пример 4): башня с параметром ν, Dθ = −θ² − θ/x − (1 − ν²/x²)"
  (let* ((a '(+ (* (^ x 2) (^ %t1 5)) (* x (^ %t1 4)) (* -1 nu nu (^ %t1 3)) (* -1 x (+ (^ x 2) 1) (^ %t1 2))
                (* -1 (- (^ x 2) (* nu nu)) %t1) (* -1/4 (^ x 5))))
         (d '(+ (* (^ x 2) (^ %t1 4)) (* (^ x 2) (+ (^ x 2) 2) (^ %t1 2)) (^ x 2) (^ x 4) (* 1/4 (^ x 6)))))
    (assert-true (rh-hermite-ok? rh-N a d))))

(deftest "риш/Эрмит: exp-башня, специальная часть идёт в остаток r"
  (let* ((a '(+ (* x %t1) 2)) (d '(* (^ %t1 2) (^ (+ %t1 1) 3)))
         (r (risch::rs-hermite rt-B (rh-P a) (rh-P d))))
    (assert-true (rt-peq? (cadr (caddr r)) (rh-P '(^ %t1 2))))
    (assert-true (rh-hermite-ok? rt-B a d))))

(deftest "риш/ЛРТ (эталонный пример 1): (2t² − t − x²)/(t³ − x²t), log x — резольвента z² − ¼, неконстантный корень ⇒ неэлементарно"
  (let ((r (risch::rs-residue-reduce rt-A (rh-P '(- (+ (* 2 (^ %t1 2)) (* -1 %t1)) (^ x 2))) (rh-P '(- (^ %t1 3) (* (^ x 2) %t1))))))
    (assert-equal (cadr r) #f)
    (assert-equal (length (car r)) 1)
    (assert-equal (car (car (car r))) (list 1 0 -1/4))
    (assert-true (rh-S=? (cadr (car (car r))) '(+ %t1 (* 2 x %rsz))))))

(deftest "риш/ЛРТ (эталон 2): −2/x/(t² − 1) ⇒ −log(log x − 1) + log(log x + 1), ответ проверяется дифференцированием"
  (let* ((r (risch::rs-residue-reduce rt-A (rh-P '(* -2 (^ x -1))) (rh-P '(- (^ %t1 2) 1))))
         (F (risch::rs-residue-integral rt-A (rh-P '(* -2 (^ x -1))) (rh-P '(- (^ %t1 2) 1)) 't '((%t1 (log x))))))
    (assert-equal (cadr r) #t)
    (assert-equal (car (car (car r))) (list 1 0 -1))
    (assert-equal (cadr F) #t)
    (assert-true (int-check (car F) '(* -2 (^ x -1) (^ (- (^ (log x) 2) 1) -1)) 'x))
    (assert-true (not (contains-sym? (car F) 'root-sum)))))

(deftest "риш/ЛРТ (эталонный пример 4): tan-башня, z² + ¼ неприводим — root-sum, S = t + x + 2z"
  (let ((r (risch::rs-residue-reduce rh-T (rh-P '(+ (* -2 x %t1) 1 (* -1 (^ x 2)))) (rh-P '(+ (^ %t1 2) (* 2 x %t1) 1 (^ x 2))))))
    (assert-equal (cadr r) #t)
    (assert-equal (car (car (car r))) (list 1 0 1/4))
    (assert-true (rh-S=? (cadr (car (car r))) '(+ %t1 x (* 2 %rsz))))
    ; с 21k.5′ пара корней ±i/2 при S₀ + zS₁ собирается в atan (−2c·atan(c·S₁/S₀)), root-sum остаётся для остальных Q
    (assert-true (contains-sym? (risch::rs-log-part rh-T (car r) 't) 'atan))))

(deftest "риш/ЛРТ: exp-башня, 2xθ/(θ + 2) = 2x − 4x/(θ + 2), лог. часть log(θ + 2) (многочлен отброшен); обратная подстановка θ → exp(x²)"
  (let* ((tw rt-B) (F (risch::rs-residue-integral tw (rh-P '(* 2 x %t1)) (rh-P '(+ %t1 2)) 't '((%t1 (exp (^ x 2)))))))
    (assert-equal (cadr F) #t)
    (assert-true (equal? (car F) '(log (+ 2 (exp (^ x 2))))))))

(deftest "риш/ЛРТ: 1/log x — вычет z = x неконстантен ⇒ флаг «неэлементарно», логарифмов нет"
  (let ((r (risch::rs-residue-reduce rt-A (rh-P 1) (rh-P '%t1))))
    (assert-equal r (list '() #f)))
  ; вычет константа: 1/(x log x) = D(log log x), a = 1/x, d = t
  (let ((r (risch::rs-residue-reduce rt-A (rh-P '(^ x -1)) (rh-P '%t1))))
    (assert-equal (cadr r) #t)
    (assert-equal (car (car (car r))) (list 1 -1))))

(deftest "риш/Эрмит + ЛРТ: пример 11 туториала — f − D(лог. часть) = 1/log x (остаток не вычисляется элементарно)"
  (let* ((a '(- (+ (* 2 (^ %t1 2)) (* -1 %t1)) (^ x 2))) (d '(- (^ %t1 3) (* (^ x 2) %t1)))
         (hr (risch::rs-hermite rt-A (rh-P a) (rh-P d)))
         (h (cadr hr)) (res (risch::rs-residue-reduce rt-A (car h) (cadr h)))
         (L (risch::rs-log-part rt-A (car res) 't)))
    (assert-true (rh-fe? rt-A (car hr) 0))
    (assert-equal (cadr res) #f)
    ; ∫ = 1/2 log(θ + x) − 1/2 log(θ − x) + ∫ 1/θ; остаток на уровень ниже — ровно 1/log x
    (assert-true (rt-eq? (list '+ (list '* a (list '^ d -1)) (list '* -1 (risch::rs-deriv rt-A L))) '(^ %t1 -1)))))

; ---------- 21k.4: драйвер (lib\risch\driver.lisp), log-случай, три исхода, стратегия int-risch ----------
; Полный каскад на неэлементарном интеграле стоит ≈ 0.8 с (до Риша работают все прежние стратегии), поэтому integrate зовётся
; только там, где нужна стратегия; остальное — risch-integrate напрямую; пример 11 считается один раз (шаги и условия).
(define (rd-int-free? e) (not (contains-sym? e 'integrate)))
(define rd-log2 '(log (log x)))
(define rd-inv-log '(^ (log x) -1))
(define rd-e11 '(* (^ (+ (^ (log x) 3) (* -1 (^ x 2) (log x))) -1) (+ (* 2 (^ (log x) 2)) (* -1 (log x)) (* -1 (^ x 2)))))
; ((ответ шаги) условия): ответ — результат integrate, шаги — capture-step-log 'full
(define rd-r11 (capture-conditions (lambda () (capture-step-log (lambda () (integrate rd-e11 'x)) 'full))))

(deftest "риш/драйвер: ∫log x = x log x − x, ∫log²x, ∫x log x, ∫log x / x — элементарные, проверка дифференцированием"
  (let ((F1 (risch-integrate '(log x) 'x)))
    (assert-equal F1 '(+ (* -1 x) (* x (log x))))
    (assert-true (int-check F1 '(log x) 'x)))
  (let ((e '(^ (log x) 2)) (F (risch-integrate '(^ (log x) 2) 'x)))
    (assert-true (and F (rd-int-free? F) (int-check F e 'x))))
  (let ((e '(* x (log x))) (F (risch-integrate '(* x (log x)) 'x)))
    (assert-true (and F (rd-int-free? F) (int-check F e 'x))))
  (let ((e '(* (^ x -1) (log x))) (F (risch-integrate '(* (^ x -1) (log x)) 'x)))
    (assert-equal F '(* 1/2 (^ (log x) 2)))
    (assert-true (int-check F e 'x))))

(deftest "риш/драйвер: ∫log³x/x, ∫x²log²x, ∫x log³x — многочленная часть сверху вниз (c·θ^{m+1} и q·θ^m)"
  (map (lambda (e)
         (let ((F (risch-integrate e 'x)))
           (assert-true (and F (rd-int-free? F) (int-check F e 'x)))))
       '((* (^ (log x) 3) (^ x -1)) (* (^ x 2) (^ (log x) 2)) (* x (^ (log x) 3)))))

(deftest "риш/драйвер: ∫1/(x log x) = log(log x) (ЛРТ: вычет 1), ∫−1/(x log x log²(log x)) = 1/log(log x) (башня высоты 2)"
  (assert-equal (risch-integrate '(^ (* x (log x)) -1) 'x) rd-log2)
  (assert-equal (risch-integrate '(* -1 (^ (* x (log x) (^ (log (log x)) 2)) -1)) 'x) '(^ (log (log x)) -1)))

(deftest "риш/драйвер: ∫log(log x)/x = log x·log(log x) − log x — log x ∈ K распознаётся как θ₁ (высота 2)"
  (let* ((e '(* (^ x -1) (log (log x)))) (F (risch-integrate e 'x)))
    (assert-equal F '(+ (* (log x) (log (log x))) (* -1 (log x))))
    (assert-true (int-check F e 'x))))

(deftest "риш/драйвер: ∫log(log x) — частичный ответ x·log(log x) − ∫1/log x"
  (let ((F (risch-integrate rd-log2 'x)))
    (assert-equal F '(+ (* x (log (log x))) (* -1 (integrate (^ (log x) -1) x))))
    (assert-true (int-check F rd-log2 'x))
    (assert-equal (risch-nonelementary? rd-log2 'x) #t)))

(deftest "риш/драйвер: ∫1/log x — доказано неэлементарно: risch-integrate #f, risch-nonelementary? #t, integrate — невычисленная форма с условием"
  (assert-equal (risch-integrate rd-inv-log 'x) #f)
  (assert-equal (risch-nonelementary? rd-inv-log 'x) #t)
  (assert-equal (risch-nonelementary? '(* 3 (^ (log x) -1)) 'x) #t)
  (conditions-clear)
  (assert-equal (integrate rd-inv-log 'x) '(integrate (^ (log x) -1) x))
  (assert-equal (car (car (conditions))) '(risch-nonelementary (integrate (^ (log x) -1) x))))

(deftest "риш/драйвер: ∫log x / log(1+x), ∫1/log(log x), ∫log x/(1+x²), ∫1/(log x + 1) — неэлементарны (неконстантный вычет / нет q + c·log u)"
  (map (lambda (e) (assert-equal (risch-nonelementary? e 'x) #t))
       '((* (log x) (^ (log (+ 1 x)) -1)) (^ (log (log x)) -1) (* (log x) (^ (+ 1 (^ x 2)) -1)) (^ (+ (log x) 1) -1))))

(deftest "риш/драйвер: пример 11 туториала (2log²x − log x − x²)/(log³x − x²log x) = ½log(log x + x) − ½log(log x − x) + ∫1/log x"
  (let ((F (car (car rd-r11))))
    (assert-true (contains-sym? F 'integrate))
    (assert-true (contains-sym? F 'log))
    (assert-true (int-check F rd-e11 'x))
    (assert-equal (car (car (cadr rd-r11))) '(risch-nonelementary (integrate (^ (log x) -1) x)))))

(deftest "риш/драйвер: ∫log x·log(1+x) и ∫(log x + 1/log x) — частичные ответы проверяются дифференцированием целиком"
  (let* ((e '(* (log x) (log (+ x 1)))) (F (risch-integrate e 'x)))
    (assert-true (contains-sym? F 'integrate))
    (assert-true (int-check F e 'x)))
  (let* ((e '(+ (log x) (^ (log x) -1))) (F (risch-integrate e 'x)))
    (assert-equal F '(+ (* -1 x) (* x (log x)) (integrate (^ (log x) -1) x)))
    (assert-true (int-check F e 'x))))

(deftest "риш/драйвер: алгебраика и тригонометрия — «не знаю» (#f, не неэлементарно), условия отказа башни не остаются"
  ; 21k.5: exp-уровни теперь решаются (exp(x²) — доказано неэлементарно, см. тесты 21k.5)
  (assert-equal (risch-nonelementary? '(^ (log x) -1/2) 'x) 'unknown)
  (assert-equal (risch-nonelementary? '(* (exp x) (asin x)) 'x) 'unknown)
  (conditions-clear)
  ; (log x)^(-1/2): сам Риш не знает, но смешанный случай R3.2 (θ = log x, s² = t) доказывает неэлементарность —
  ; поэтому для «условия отказа не остаются» взят радикал от x + log x (вне R3)
  (assert-equal (integrate '(^ (+ x (log x)) -1/2) 'x) '(integrate (^ (+ x (log x)) -1/2) x))
  (assert-equal (conditions) '()))

(deftest "риш/драйвер: старые ответы не меняются — Риш последним"
  (assert-equal (integrate '(* x (log x)) 'x) '(+ (* -1/4 (^ x 2)) (* 1/2 (^ x 2) (log x))))
  (assert-equal (integrate '(^ (+ 1 (^ x 2)) -1) 'x) '(atan x))
  (assert-equal (integrate '(* x (exp x)) 'x) '(+ (* x (exp x)) (* -1 (exp x))))
  (assert-equal (integrate '(* (^ x -1) (exp x)) 'x) '(integrate (* (^ x -1) (exp x)) x)))

(deftest "риш/драйвер: переключатель (algorithm 'risch): off — прежний каскад (невычисленная форма), on — частичный ответ"
  (unwind-protect
      (begin
        (set-algorithm 'risch 'off)
        (assert-equal (integrate rd-log2 'x) '(integrate (log (log x)) x))
        (set-algorithm 'risch 'on)
        (assert-true (contains-sym? (integrate rd-log2 'x) 'integrate)))
    (set-algorithm 'risch 'on)))

(deftest "риш/драйвер: определённый интеграл — форма с li через risch-special"
  (assert-equal (integrate rd-log2 'x 2 3)
                '(+ (li 2) (* -1 (li 3)) (* -2 (log (log 2))) (* 3 (log (log 3))))))

(deftest "риш/драйвер: журнал шагов — рамка risch, внутри risch-tower, risch-hermite, risch-lrt, risch-log-part, risch-check, risch-nonelementary"
  (assert-equal (step-rules (cadr (car rd-r11))) '(integration risch risch-tower risch-hermite risch-lrt risch-log-part risch-check risch-nonelementary)))

(deftest "риш/драйвер: risch-nonelementary? — #f для элементарного, #t для частичного и доказанного"
  (assert-equal (risch-nonelementary? '(log x) 'x) #f)
  (assert-equal (risch-nonelementary? '(^ (* x (log x)) -1) 'x) #f)
  (assert-equal (risch-nonelementary? '(+ (log x) (^ (log x) -1)) 'x) #t))

; ---------- 21k.5: уравнение Риша (lib\risch\rde.lisp) и exp-случай драйвера ----------
; Башни: r5-B — база ℚ(x); r5-E — θ = exp x (Dθ = θ); r5-L — θ = log x; r5-T — t0 = exp(−1/x) (Dt0 = t0/x²), t = log x (эталонный пример).
(define r5-B (risch::rs-tower 'x))
(define r5-E (risch::rs-extend r5-B '%t1 'exp 'x))
(define r5-L (risch::rs-extend r5-B '%t1 'log 'x))
(define r5-T (risch::rs-extend (risch::rs-extend r5-B '%t1 'exp '(* -1 (^ x -1))) '%t2 'log 'x))
(define (r5-px e) (rt-poly e 'x))
(define (r5-p1 e) (rt-poly e '%t1))
(define (r5-p2 e) (rt-poly e '%t2))
; (ok y) с проверкой Dy + f·y = g
(define (r5-ok? tw f g r)
  (and (equal? (car r) 'ok) (rt-zero? (list '+ (risch::rs-deriv tw (cadr r)) (list '* f (cadr r)) (list '* -1 g)))))
(define (r5-int-ok? e) (let ((F (risch-integrate e 'x))) (and F (rd-int-free? F) (int-check F e 'x) F)))

(deftest "риш/RDE weak_normalizer (эталон): exp-башня, q = ∏ p^m и f − Dq/q"
  (let* ((a (r5-p1 '(+ (* (+ 1 x) (^ %t1 5)) (* 4 (^ %t1 4)) (* (+ -1 (* -3 x)) (^ %t1 3)) (* -4 (^ %t1 2)) (* (+ -2 (* 2 x)) %t1))))
         (d (r5-p1 '(+ (^ %t1 4) (* -3 (^ %t1 2)) 2)))
         (wn (risch::rde-weak r5-E a d)))
    (assert-true (rt-peq? (risch::rs-prod-factors wn) (r5-p1 '(+ (^ %t1 5) (* -1 (^ %t1 4)) (* -4 (^ %t1 3)) (* 4 (^ %t1 2)) (* 4 %t1) -4))))
    (assert-true (rt-eq? (risch::rde-fexpr r5-E (risch::rde-sub-logd r5-E (list a d) wn))
                         '(* (+ (* (+ 1 x) (^ %t1 2)) (* x %t1)) (^ (+ %t1 1) -1))))
    ; повторно — нормализовано: q = 1
    (let ((f1 (risch::rde-sub-logd r5-E (list a d) wn)))
      (assert-equal (risch::rde-weak r5-E (car f1) (cadr f1)) '())))
  ; (1 + t²)/(t² − 1): вычеты 1 в t = ±1. Эталонная реализация берёт корень резольвенты (z − 1)² дважды (real_roots с кратностью) и даёт
  ; q = (t² − 1)², f = (1 − 3t²)/(t² − 1) (вычеты −1); у нас, как у эталонной реализации (различные корни), q = t² − 1, f = −1 (вычеты 0) — тоже слабо нормально
  (let* ((a (r5-p1 '(+ 1 (^ %t1 2)))) (d (r5-p1 '(+ (^ %t1 2) -1))) (wn (risch::rde-weak r5-E a d)))
    (assert-true (rt-peq? (risch::rs-prod-factors wn) (r5-p1 '(+ (^ %t1 2) -1))))
    (assert-true (rt-eq? (risch::rde-fexpr r5-E (risch::rde-sub-logd r5-E (list a d) wn)) -1))))

(deftest "риш/RDE normal_denom: база, Dy + y = 1/x — у y был бы полюс x, решения нет (доказано)"
  (assert-equal (car (risch::rs-rde r5-B 1 '(^ x -1))) 'none)
  ; exp: знаменатель g = θ² — специальный, нормальная часть тривиальна
  (let ((nd (risch::rde-normal-denom r5-E (r5-p1 1) (list 1) (list 1) (r5-p1 '(^ %t1 2)))))
    (assert-true (rt-peq? (car nd) (list 1)))
    (assert-true (rt-peq? (nth nd 3) (list 1)))
    (assert-true (rt-peq? (cadr (caddr nd)) (r5-p1 '(^ %t1 2))))))

(deftest "риш/RDE special_denom (эталон): exp — (1, t², (t²−1)/t) → (1, t²−1, t²−1, t); пример 6.2.1 → h = t, SPDE даёт q = 1"
  (let ((sd (risch::rde-special-denom r5-E (list 1) (list (r5-p1 '(^ %t1 2)) (list 1)) (list (r5-p1 '(+ (^ %t1 2) -1)) (r5-p1 '%t1)))))
    (assert-true (rt-peq? (car sd) (list 1)))
    (assert-true (rt-peq? (cadr sd) (r5-p1 '(+ (^ %t1 2) -1))))
    (assert-true (rt-peq? (caddr sd) (r5-p1 '(+ (^ %t1 2) -1))))
    (assert-true (rt-peq? (nth sd 3) (r5-p1 '%t1))))
  ; пример 6.2.1: a = t² + 2xt + x², b(0) = x² — возможное сокращение, −b(0)/a(0) = −1 = m·Dη ⇒ n = −1
  (let* ((a (r5-p1 '(+ (^ %t1 2) (* 2 x %t1) (^ x 2))))
         (b (r5-p1 '(+ (* (+ 1 (^ x -2)) (^ %t1 2)) (* (+ (* 2 x) -1 (* 2 (^ x -1))) %t1) (^ x 2))))
         (c (r5-p1 '(+ (* (^ x -2) %t1) -1 (* 2 (^ x -1)))))
         (sd (risch::rde-special-denom r5-E a (list b (list 1)) (list c (list 1))))
         (bc (r5-p1 '(+ (* (^ x -2) (^ %t1 2)) (* (+ (* 2 (^ x -1)) -1) %t1)))))
    (assert-true (rt-peq? (car sd) a))
    (assert-true (rt-peq? (cadr sd) bc))
    (assert-true (rt-peq? (caddr sd) bc))
    (assert-true (rt-peq? (nth sd 3) (r5-p1 '%t1)))
    (let ((sp (risch::rde-spde r5-E a bc bc 0 (list 1) '())))
      (assert-equal (car sp) '())
      (assert-equal (cadr sp) '())
      (assert-true (rt-peq? (nth sp 4) (list 1))))))

(deftest "риш/RDE bound_degree (эталон): база (1, −2x, 1) → 0; база с целым −lc b/lc a; primitive (t², −t²/x² − 1/x, …) → 3"
  (assert-equal (risch::rde-bound r5-B (list 1) (r5-px '(* -2 x)) (list 1)) 0)
  (assert-equal (risch::rde-bound r5-B (r5-px 'x) (list -3) (list 1)) 3)
  (assert-equal (risch::rde-bound r5-T (r5-p2 '(^ %t2 2)) (r5-p2 '(+ (* -1 (^ x -2) (^ %t2 2)) (* -1 (^ x -1))))
                                  (r5-p2 '(+ (* (+ (* 2 x) -1) (^ %t2 4)) (* (+ %t1 x) (^ x -1) (^ %t2 3)) (* -1/2 (+ %t1 (* 4 (^ x 2))) (^ x -1) (^ %t2 2)) (* x %t2))))
                3))

(deftest "риш/RDE SPDE (эталонный пример): три базовых примера — (b c n α β)"
  (let ((sp (risch::rde-spde r5-B (r5-px '(+ (^ x 2) x 1)) (r5-px '(+ (* -2 x) -1))
                             (r5-px '(+ (* 1/2 (^ x 5)) (* 3/4 (^ x 4)) (^ x 3) (* -1 (^ x 2)) 1)) 4 (list 1) '())))
    (assert-equal (car sp) '())
    (assert-true (rt-peq? (cadr sp) (r5-px '(+ (* 1/2 x) -1/4))))
    (assert-equal (caddr sp) 2)
    (assert-true (rt-peq? (nth sp 3) (r5-px '(+ (^ x 2) x 1))))
    (assert-true (rt-peq? (nth sp 4) (r5-px '(* 5/4 x)))))
  (let ((sp (risch::rde-spde r5-B (r5-px '(- (^ x 2) x)) (list 1) (r5-px '(+ (* 9 (^ x 4)) (* -10 (^ x 3)) (* 2 (^ x 2)))) 4 (list 1) '())))
    (assert-equal (cadr sp) '())
    (assert-true (rt-peq? (nth sp 4) (r5-px '(+ (* 3 (^ x 3)) (* -2 (^ x 2)))))))
  (let ((sp (risch::rde-spde r5-B (r5-px '(- (^ x 2) x)) (r5-px '(+ (^ x 2) (* -5 x) 3))
                             (r5-px '(+ (^ x 7) (* -1 (^ x 6)) (* -2 (^ x 4)) (* 3 (^ x 3)) (* -1 (^ x 2)))) 5 (list 1) '())))
    (assert-true (rt-peq? (car sp) (list 1)))
    (assert-true (rt-peq? (cadr sp) (r5-px '(+ x 1))))
    (assert-equal (caddr sp) 1)
    (assert-true (rt-peq? (nth sp 3) (r5-px '(- (^ x 4) (^ x 3)))))
    (assert-true (rt-peq? (nth sp 4) (r5-px '(- (^ x 3) (^ x 2)))))))

(deftest "риш/RDE SPDE (эталонный пример): башня t0 = exp(−1/x), t = log x — решение t0·t²/2 + x²t² − x²t"
  (let ((sp (risch::rde-spde r5-T (r5-p2 '(^ %t2 2)) (r5-p2 '(+ (* -1 (^ x -2) (^ %t2 2)) (* -1 (^ x -1))))
                             (r5-p2 '(+ (* (+ (* 2 x) -1) (^ %t2 4)) (* (+ %t1 x) (^ x -1) (^ %t2 3)) (* -1/2 (+ %t1 (* 4 (^ x 2))) (^ x -1) (^ %t2 2)) (* x %t2)))
                             3 (list 1) '())))
    (assert-equal (cadr sp) '())
    (assert-true (rt-peq? (nth sp 4) (r5-p2 '(+ (* 1/2 %t1 (^ %t2 2)) (* (^ x 2) (^ %t2 2)) (* -1 (^ x 2) %t2)))))))

(deftest "риш/RDE SPDE: НОД(a, b) не делит c — нет решения; Dy + 2xy = 1 — граница степени, решения нет"
  (assert-error (risch::rde-spde r5-B (r5-px '(^ x 2)) (r5-px 'x) (list 1) 3 (list 1) '()))
  (assert-equal (car (risch::rs-rde r5-B '(* 2 x) 1)) 'none))

(deftest "риш/RDE solve_poly_rde: b «большой» (старшие члены) и b = 0 (интегрирование многочлена)"
  (assert-true (rt-peq? (risch::rde-poly-solve r5-B '() (r5-px '(+ (* 1/2 x) -1/4))) (r5-px '(+ (* 1/4 (^ x 2)) (* -1/4 x)))))
  (assert-true (rt-peq? (risch::rde-poly-solve r5-B (list 1) (r5-px 'x)) (r5-px '(- x 1))))
  ; primitive: Dq + (t + 1)·q = t + 1 ⇒ q = 1 (x^x(1 + log x)); Dq + (t + 1)·q = 1 — нет (x^x)
  (assert-true (rt-peq? (risch::rde-poly-solve r5-L (r5-p1 '(+ %t1 1)) (r5-p1 '(+ %t1 1))) (list 1)))
  (assert-error (risch::rde-poly-solve r5-L (r5-p1 '(+ %t1 1)) (list 1))))

(deftest "риш/RDE ветки сокращения exp (эталонная схема cancel_exp): Dq + 2x·q = 2x ⇒ 1; Dq + 2x·q = (1 + 2x)t ⇒ t"
  (assert-true (rt-peq? (risch::rde-poly-solve r5-E (r5-p1 '(* 2 x)) (r5-p1 '(* 2 x))) (list 1)))
  (assert-true (rt-peq? (risch::rde-poly-solve r5-E (r5-p1 '(* 2 x)) (r5-p1 '(* (+ 1 (* 2 x)) %t1))) (r5-p1 '%t1))))

(deftest "риш/RDE ветки сокращения primitive (эталонная схема cancel_primitive): (1, t) — нет; (1, t + 1/x) ⇒ t; (4x, 4xt² + 2t/x) ⇒ t²; b = 1/(2x) ⇒ t³"
  (assert-equal (car (risch::rs-rde r5-L 1 '%t1)) 'none)
  (assert-true (rt-peq? (risch::rde-poly-solve r5-L (list 1) (r5-p1 '(+ %t1 (^ x -1)))) (r5-p1 '%t1)))
  (assert-true (rt-peq? (risch::rde-poly-solve r5-L (r5-p1 '(* 4 x)) (r5-p1 '(+ (* 4 x (^ %t1 2)) (* 2 (^ x -1) %t1)))) (r5-p1 '(^ %t1 2))))
  (let ((r (risch::rs-rde r5-L '(* 1/2 (^ x -1)) '(+ (* 3 (^ x -1) (^ %t1 2)) (* 1/2 (^ x -1) (^ %t1 3))))))
    (assert-equal (car r) 'ok)
    (assert-true (rt-eq? (cadr r) '(^ %t1 3)))))

(deftest "риш/rischDE (эталон): Dy − 2xy = 1 − 2x − 2x² ⇒ x + 1; exp: Dy + (1 − t)y = 1 ⇒ −1/t; Dy + y/x = 1 ⇒ x/2 (слабый нормализатор)"
  (let ((r (risch::rs-rde r5-B '(* -2 x) '(+ 1 (* -2 x) (* -2 (^ x 2))))))
    (assert-true (rt-eq? (cadr r) '(+ x 1))))
  (let ((r (risch::rs-rde r5-E '(- 1 %t1) 1)))
    (assert-true (r5-ok? r5-E '(- 1 %t1) 1 r))
    (assert-true (rt-eq? (cadr r) '(* -1 (^ %t1 -1)))))
  (let ((r (risch::rs-rde r5-B '(^ x -1) 1)))
    (assert-true (r5-ok? r5-B '(^ x -1) 1 r))
    (assert-true (rt-eq? (cadr r) '(* 1/2 x)))))

(deftest "риш/rischDE: однородное решение y = x (b = −1/x) — параметрический спуск 21k.7b находит решение степени выше deg c"
  ; Dy − y/x = log x: решение x·log²x/2 (до 21k.7b — unknown: покоэффициентная рекурсия без PRDE его не видела)
  (let ((r (risch::rs-rde r5-L '(* -1 (^ x -1)) '%t1)))
    (assert-true (r5-ok? r5-L '(* -1 (^ x -1)) '%t1 r))
    (assert-equal (risch::rs-from-expr (cadr r) '%t1) '((* 1/2 x) 0 0)))
  (assert-equal (risch::rs-rde r5-B 1 0) '(ok 0)))

(deftest "риш/exp: ∫x eˣ = (x − 1)eˣ, ∫x²eˣ/2, ∫(1 + e⁻ˣ) = x − e⁻ˣ, ∫sinh x"
  (assert-equal (risch-integrate '(* x (exp x)) 'x) '(* (+ -1 x) (exp x)))
  (assert-true (r5-int-ok? '(* 1/2 (^ x 2) (exp x))))
  (assert-equal (risch-integrate '(+ 1 (exp (* -1 x))) 'x) '(+ x (* -1 (exp (* -1 x)))))
  (assert-true (r5-int-ok? '(sinh x))))

(deftest "риш/exp: ∫eˣe^{eˣ} = e^{eˣ}, ∫2eˣe^{2eˣ} = e^{2eˣ}, ∫(e^{x+eˣ} + e^{x−eˣ}) = e^{eˣ} − e^{−eˣ}"
  (assert-equal (risch-integrate '(* (exp x) (exp (exp x))) 'x) '(exp (exp x)))
  (assert-equal (risch-integrate '(* 2 (exp x) (^ (exp (exp x)) 2)) 'x) '(exp (* 2 (exp x))))
  (assert-true (r5-int-ok? '(+ (exp (+ x (exp x))) (exp (+ x (* -1 (exp x))))))))

(deftest "риш/exp: ∫x^x(1 + log x) = x^x (башня log x, exp(x log x); RDE Dy + (θ₁ + 1)y = θ₁ + 1, y = 1)"
  (let ((F (r5-int-ok? '(* (^ x x) (+ 1 (log x))))))
    (assert-true F)
    (assert-equal F '(^ x x))))

(deftest "риш/exp: ∫(1 + 2x²)e^{x²} = x e^{x²} — RDE Dy + 2xy = 1 + 2x² без PRDE"
  (assert-equal (risch-integrate '(* (+ 1 (* 2 (^ x 2))) (exp (^ x 2))) 'x) '(* x (exp (^ x 2)))))

(deftest "риш/exp: пример 6.2.1 — ∫(eˣ − x² + 2x)/((eˣ + x)²x²)·exp((x² − 1)/x + 1/(eˣ + x)) = exp(−1/x + 1/(eˣ + x))"
  (let* ((e '(* (+ (exp x) (* -1 (^ x 2)) (* 2 x)) (^ (* (^ (+ (exp x) x) 2) (^ x 2)) -1) (exp (+ (* (+ (^ x 2) -1) (^ x -1)) (^ (+ (exp x) x) -1)))))
         (F (r5-int-ok? e)))
    (assert-true F)
    (assert-true (int-check '(exp (+ (* -1 (^ x -1)) (^ (+ (exp x) x) -1))) e 'x))))

(deftest "риш/exp: ∫1/(1 + eˣ) = x − log(1 + eˣ), ∫eˣ/(1 + eˣ) = log(1 + eˣ) — поправка ЛРТ к θ⁰"
  (assert-equal (risch-integrate '(^ (+ 1 (exp x)) -1) 'x) '(+ x (* -1 (log (+ 1 (exp x))))))
  (assert-equal (risch-integrate '(* (exp x) (^ (+ (exp x) 1) -1)) 'x) '(log (+ 1 (exp x)))))

(deftest "риш/exp: (25t⁶ − 10t⁵ + 7t⁴ − 8t³ + 13t² + 2t − 1)/(25t⁶ + 35t⁴ + 11t² + 1), t = eˣ (эталон) — Эрмит, ЛРТ с кратным корнем резольвенты"
  (let ((F (r5-int-ok? '(* (+ (* 25 (^ (exp x) 6)) (* -10 (^ (exp x) 5)) (* 7 (^ (exp x) 4)) (* -8 (^ (exp x) 3)) (* 13 (^ (exp x) 2)) (* 2 (exp x)) -1)
                           (^ (+ (* 25 (^ (exp x) 6)) (* 35 (^ (exp x) 4)) (* 11 (^ (exp x) 2)) 1) -1)))))
    (assert-true F)
    (assert-true (contains-sym? F 'log)))
  ; точный результант при deg b = deg a (дефектная ПРС): res(θ² + 1, −2zθ² − 2) = 4(z − 1)²
  (assert-true (rt-eq? (risch::rs-resultant (list 1 0 1) (list '(* -2 %rsz) 0 -2)) '(* 4 (^ (- %rsz 1) 2)))))

(deftest "риш/exp: Лоранов многочлен ∫(e^{2x} + 2 + e^{−2x}) = e^{2x}/2 + 2x − e^{−2x}/2 (θ², θ⁰, θ⁻²)"
  (let ((F (r5-int-ok? '(+ (exp (* 2 x)) 2 (exp (* -2 x))))))
    (assert-true F)
    (assert-true (int-check '(+ (* 1/2 (exp (* 2 x))) (* 2 x) (* -1/2 (exp (* -2 x)))) '(+ (exp (* 2 x)) 2 (exp (* -2 x))) 'x))))

(deftest "риш/exp: ∫x eˣ/(1 + x)² = eˣ/(1 + x) — нормальный знаменатель решения RDE (h = 1 + x)"
  (assert-equal (risch-integrate '(* x (exp x) (^ (+ 1 x) -2)) 'x) '(* (^ (+ 1 x) -1) (exp x))))

(deftest "риш/exp: две экспоненты — ∫e^{x + x²} неэлементарен (RDE уровнем ниже: Dq + (2x + 1)q = 1 — нет), ∫(2x + 1)e^{x}e^{x²} = e^{x + x²}"
  (assert-equal (risch-nonelementary? '(* (exp x) (exp (^ x 2))) 'x) #t)
  (assert-true (r5-int-ok? '(* (+ (* 2 x) 1) (exp x) (exp (^ x 2))))))

(deftest "риш/exp: параметр в показателе — ∫exp(a x²) неэлементарен при генерическом a (условие risch-generic)"
  (let ((cc (capture-conditions (lambda () (risch-nonelementary? '(exp (* a (^ x 2))) 'x)))))
    (assert-equal (car cc) #t)
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-generic)) (cadr cc)))))

(deftest "риш/exp: ∫x/(1 + eˣ) — ответ не ложный: неконстантный вычет, доказано неэлементарно"
  (assert-equal (risch-integrate '(* x (^ (+ 1 (exp x)) -1)) 'x) #f)
  (assert-equal (risch-nonelementary? '(* x (^ (+ 1 (exp x)) -1)) 'x) #t))

(deftest "риш/exp: доказано неэлементарно — exp(x²), eˣ/x, x^x, exp(eˣ), eˣ/x², eˣ log x"
  (map (lambda (e) (assert-equal (risch-nonelementary? e 'x) #t))
       '((exp (^ x 2)) (* (exp x) (^ x -1)) (^ x x) (exp (exp x)) (* (exp x) (^ x -2)) (* (exp x) (log x)))))

(deftest "риш/exp: частичные ответы — e^{x²}/(1 + x²) + ∫e^{−x²}, log(x e^{−x} + 1) — проверка дифференцированием"
  (let* ((e '(* (+ 1 (* 2 (^ x 2)) (^ x 4) (* 2 (^ x 3) (exp (* 2 (^ x 2))))) (^ (* (+ (^ x 4) (* 2 (^ x 2)) 1) (exp (^ x 2))) -1)))
         (F (risch-integrate e 'x)))
    (assert-equal F '(+ (* (^ (+ 1 (^ x 2)) -1) (exp (^ x 2))) (integrate (exp (* -1 (^ x 2))) x)))
    (assert-true (int-check F e 'x)))
  (let* ((e '(log (+ (* x (exp (* -1 x))) 1))) (F (risch-integrate e 'x)))
    (assert-true (contains-sym? F 'integrate))
    (assert-true (int-check F e 'x))))

(deftest "риш/exp: eˣ(log x + 1/x) = eˣ log x (покоэффициентная рекурсия primitive); параметры: ∫e^{ax}, ∫x e^{ax} с условием risch-generic"
  (assert-equal (risch-integrate '(* (exp x) (+ (log x) (^ x -1))) 'x) '(* (exp x) (log x)))
  (let ((cc (capture-conditions (lambda () (risch-integrate '(* x (exp (* a x))) 'x)))))
    (assert-true (int-check (car cc) '(* x (exp (* a x))) 'x))
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-generic)) (cadr cc))))
  (assert-equal (risch-integrate '(exp (* a x)) 'x) '(* (^ a -1) (exp (* a x)))))

(deftest "риш/слепой набор: (x³ − x² + x + 1)eˣ/(x² + 1)² = x eˣ/(x² + 1), (2x⁴ + x² + 1)e^{x²}/(x² + 1)² = x e^{x²}/(x² + 1)"
  (assert-equal (risch-integrate '(* (+ (^ x 3) (* -1 (^ x 2)) x 1) (exp x) (^ (+ (^ x 2) 1) -2)) 'x) '(* x (^ (+ 1 (^ x 2)) -1) (exp x)))
  (assert-equal (risch-integrate '(* (+ (* 2 (^ x 4)) (^ x 2) 1) (exp (^ x 2)) (^ (+ (^ x 2) 1) -2)) 'x)
                '(* x (^ (+ 1 (^ x 2)) -1) (exp (^ x 2)))))

(deftest "риш/слепой набор: (2x² + 2x − x² ln x − (x+1)² ln(x+1))/(x²(x+1)²) = ln(x+1)/x + ln x/(x+1); arctan — в тестах 21k.5′"
  (let* ((e '(* (+ (* 2 (^ x 2)) (* 2 x) (* -1 (^ x 2) (log x)) (* -1 (^ (+ x 1) 2) (log (+ x 1)))) (^ (* (^ x 2) (^ (+ x 1) 2)) -1)))
         (F (r5-int-ok? e)))
    (assert-equal F '(+ (* (^ x -1) (log (+ 1 x))) (* (^ (+ 1 x) -1) (log x))))))

(deftest "риш/exp: integrate — exp(x²) с условием risch-nonelementary; журнал (1 + 2x²)e^{x²}: risch-rde, risch-exp-part, risch-check"
  ; слепой пример (x³ − x² + x + 1)eˣ/(x² + 1)² через integrate тоже берётся Ришем, но прежний каскад до него идёт ≈ 10 с —
  ; здесь пример, на котором каскад сдаётся быстро
  (conditions-clear)
  (assert-equal (integrate '(exp (^ x 2)) 'x) '(integrate (exp (^ x 2)) x))
  (assert-equal (car (car (conditions))) '(risch-nonelementary (integrate (exp (^ x 2)) x)))
  (let* ((e '(* (+ 1 (* 2 (^ x 2))) (exp (^ x 2))))
         (r (capture-step-log (lambda () (integrate e 'x)) 'full)))
    (assert-equal (car r) '(* x (exp (^ x 2))))
    (assert-equal (step-rules (cadr r)) '(integration risch risch-tower risch-rde risch-exp-part risch-check))))


; ---------- подшаг 21k.5′: atan — примитивный уровень башни (Dθ = Du/(1 + u²) ∈ K) ----------
(define (ra-ok? e) (let ((F (risch-integrate e 'x))) (and F (not (contains-sym? F 'integrate)) (int-check F e 'x) F)))

(deftest "риш/atan: башня atan x — вид atan, Dθ = 1/(1 + x²), rs-case = primitive, обратная подстановка"
  (let ((r (rt-build '(atan x))))
    (assert-equal (rt-kinds r) '(atan))
    (assert-true (rt-eq? (rt-dth r 0) '(^ (+ 1 (^ x 2)) -1)))
    (assert-equal (risch::rs-case (car r)) 'primitive)
    (assert-true (rt-back-ok? '(atan x) r))))

(deftest "риш/atan: ∫atan x = x·atan x − ½log(1 + x²); ∫x·atan x"
  (assert-equal (ra-ok? '(atan x)) '(+ (* x (atan x)) (* -1/2 (log (+ 1 (^ x 2))))))
  (assert-true (ra-ok? '(* x (atan x)))))

(deftest "риш/atan: ∫atan(x)/(1 + x²) = ½atan²x (поправка c·θ в многочленной части)"
  (assert-equal (ra-ok? '(* (atan x) (^ (+ 1 (^ x 2)) -1))) '(* 1/2 (^ (atan x) 2)))
  (assert-true (ra-ok? '(* (^ (atan x) 2) (^ (+ 1 (^ x 2)) -1)))))

(deftest "риш/atan: ∫eˣ·atan x неэлементарен (RDE Dy + y = atan x без решения), ∫atan²x частично, ∫1/atan x неэлементарен"
  (assert-equal (risch-nonelementary? '(* (exp x) (atan x)) 'x) #t)
  (assert-equal (risch-nonelementary? '(^ (atan x) -1) 'x) #t)
  (let ((F (risch-integrate '(^ (atan x) 2) 'x)))
    (assert-true (contains-sym? F 'integrate))
    (assert-equal (risch-nonelementary? '(^ (atan x) 2) 'x) #t)))

(deftest "риш/atan: слепой набор №4 — eˣ((x³ + x)·arctan x + x + 1)/((x + 1)²(x² + 1)) = eˣ·arctan x/(x + 1)"
  (let ((e '(* (exp x) (+ (* (+ (^ x 3) x) (atan x)) x 1) (^ (* (^ (+ x 1) 2) (+ (^ x 2) 1)) -1))))
    (assert-equal (ra-ok? e) '(* (^ (+ 1 x) -1) (atan x) (exp x)))
    (assert-equal (risch-nonelementary? e 'x) #f)))

(deftest "риш/atan: atan(1/x) рядом с atan x — зависимость (π/2 − atan x), условие risch-atan-branch, а не второй уровень"
  (let* ((cc (capture-conditions (lambda () (rt-build '(* (atan x) (atan (^ x -1)))))))
         (r (car cc)))
    (assert-equal (rt-kinds r) '(atan))
    (let ((e '(* (atan x) (atan (^ x -1)))))
      (assert-true (< (abs (- (eval-num (replace-expr (risch::rs-back-subst (cadr r) (caddr r)) 'x 3))
                              (eval-num (replace-expr e 'x 3))))
                      0.000000001)))
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-atan-branch)) (cadr cc))))
  (assert-equal (length (rt-levels (rt-build '(+ (atan x) (atan (* 2 x)))))) 2)   ; atan 2x независим от atan x
  (assert-equal (length (rt-levels (rt-build '(+ (atan x) (atan (* -1 x)))))) 0)  ; atan(−x) = −atan x
  (assert-true (ra-ok? '(atan (^ x -1)))))

(deftest "риш/atan: смешанные башни — atan(eˣ)·eˣ/(1 + e^{2x}) = ½atan²(eˣ); e^{atan x}/(1 + x²) = e^{atan x}"
  (let ((r (rt-build '(* (atan (exp x)) (exp x)))))
    (assert-equal (rt-kinds r) '(exp atan)))
  (assert-equal (ra-ok? '(* (atan (exp x)) (exp x) (^ (+ 1 (exp (* 2 x))) -1))) '(* 1/2 (^ (atan (exp x)) 2)))
  (assert-equal (rt-kinds (rt-build '(exp (atan x)))) '(atan exp))
  (assert-equal (ra-ok? '(* (exp (atan x)) (^ (+ 1 (^ x 2)) -1))) '(exp (atan x))))

(deftest "риш/atan: ∫atan(eˣ) — частичный ответ с неэлементарным остатком; атан от константы — константа"
  (let ((F (risch-integrate '(atan (exp x)) 'x)))
    (assert-true (contains-sym? F 'integrate)))
  (assert-equal (risch-nonelementary? '(atan (exp x)) 'x) #t)
  (assert-equal (rt-levels (rt-build '(+ (atan 2) x))) '()))

(deftest "риш/atan: корни z² + c² в ЛРТ дают atan, а не root-sum (∫eˣ/(1 + e^{2x}) = atan eˣ)"
  (let ((F (risch-integrate '(* (exp x) (^ (+ 1 (exp (* 2 x))) -1)) 'x)))
    (assert-true (not (contains-sym? F 'root-sum)))
    (assert-true (int-check F '(* (exp x) (^ (+ 1 (exp (* 2 x))) -1)) 'x))))

(deftest "риш/atan: прежние ответы не меняются — ∫1/(1 + x²) = atan x, integrate(atan x)"
  (assert-equal (integrate '(^ (+ 1 (^ x 2)) -1) 'x) '(atan x))
  (assert-equal (integrate '(atan x) 'x) '(+ (* x (atan x)) (* -1/2 (log (+ 1 (^ x 2)))))))

(deftest "риш/atan: журнал — уровень atan виден в шаге risch-tower; integrate eˣ·atan x — частичный ответ (21k.7b) с условием risch-nonelementary на остатке"
  (let ((r (capture-step-log (lambda () (integrate '(atan (exp x)) 'x)) 'full)))
    (assert-equal (step-rules (cadr r)) '(integration risch risch-tower risch-hermite risch-lrt risch-exp-part risch-poly risch-check risch-nonelementary)))
  (conditions-clear)
  ; до 21k.7b — невычисленная форма целиком; теперь eˣ·atan x − ∫eˣ/(1 + x²) (RDE Dy + y = atan x: частичное y = atan x)
  (assert-equal (integrate '(* (exp x) (atan x)) 'x)
                '(+ (* (atan x) (exp x)) (* -1 (integrate (* (^ (+ 1 (^ x 2)) -1) (exp x)) x))))
  (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions))))

(deftest "риш/atan: степени и произведения — ∫atan³x/(1 + x²) = atan⁴x/4, ∫x²·atan x"
  (assert-equal (ra-ok? '(* (^ (atan x) 3) (^ (+ 1 (^ x 2)) -1))) '(* 1/4 (^ (atan x) 4)))
  (assert-true (ra-ok? '(* (^ x 2) (atan x)))))

(deftest "риш/atan: atan(2x) — независимый уровень, ∫atan 2x; atan на уровне log: ∫log x/(1 + x²) неэлементарен, atan x·log x — «не вычислен» без ложного ответа"
  (assert-true (ra-ok? '(atan (* 2 x))))
  (assert-equal (risch-nonelementary? '(* (log x) (^ (+ 1 (^ x 2)) -1)) 'x) #t)
  (let ((v (risch-nonelementary? '(* (log x) (atan x)) 'x)))
    (assert-true (or (equal? v #t) (equal? v 'unknown)))))

; ---------- 21k.6: финальное упрощение ответов, таблица специальных функций, регрессия по risch-tests.md ----------

(deftest "риш/21k.6: 1/(1 + eˣ) = x − log(1 + eˣ) без log(exp x) (и в Рише, и через integrate)"
  (assert-equal (risch-integrate '(/ 1 (+ 1 (exp x))) 'x) '(+ x (* -1 (log (+ 1 (exp x))))))
  (assert-equal (integrate '(/ 1 (+ 1 (exp x))) 'x) '(+ x (* -1 (log (+ 1 (exp x))))))
  (assert-equal (integrate '(/ 1 (+ (exp x) -1)) 'x) '(+ (* -1 x) (log (+ -1 (exp x))))))

(deftest "риш/21k.6: integrate — log(exp u) → u и exp(u)^k → exp(k·u) в ответе (e^{2x}/(1 + eˣ) = eˣ − log(1 + eˣ))"
  (assert-equal (integrate '(/ (exp (* 2 x)) (+ 1 (exp x))) 'x) '(+ (exp x) (* -1 (log (+ 1 (exp x))))))
  (let ((F (integrate '(/ 1 (+ 1 (exp (* 2 x)))) 'x)))
    (assert-true (int-check F '(/ 1 (+ 1 (exp (* 2 x)))) 'x))
    (assert-true (not (string-contains? (to-string F) "(log (exp")))))

(deftest "риш/21k.6: rs-tidy — log(exp u), exp(k·log u), exp(x + log u)"
  (assert-equal (simplify (risch::rs-tidy '(log (exp (* 2 x))))) '(* 2 x))
  (assert-equal (simplify (risch::rs-tidy '(log (^ (exp x) 3)))) '(* 3 x))
  (assert-equal (simplify (risch::rs-tidy '(exp (* 3 (log (+ x 1)))))) '(^ (+ 1 x) 3))
  (assert-equal (simplify (risch::rs-tidy '(exp (+ x (log (+ x 1)))))) '(* (+ 1 x) (exp x)))
  (assert-equal (simplify (risch::rs-tidy '(+ (log (exp x)) (exp (log x))))) '(* 2 x))
  (assert-equal (simplify (risch::rs-tidy '(exp (* x y)))) '(exp (* x y))))

(deftest "риш/21k.6: таблица спецфункций — erf и erfi (с масштабом)"
  (assert-equal (risch-special '(exp (* -1 (^ x 2))) 'x) '(* 1/2 (^ pi 1/2) (erf x)))
  (assert-equal (risch-special '(exp (^ x 2)) 'x) '(* 1/2 (^ pi 1/2) (erfi x)))
  (assert-equal (risch-special '(exp (* -4 (^ x 2))) 'x) '(* 1/4 (^ pi 1/2) (erf (* 2 x))))
  (assert-equal (risch-special '(* 3 (exp (^ x 2))) 'x) '(* 3/2 (^ pi 1/2) (erfi x))))

(deftest "риш/21k.6: таблица спецфункций — Ei, li, Si, Ci"
  (assert-equal (risch-special '(/ (exp x) x) 'x) '(Ei x))
  (assert-equal (risch-special '(/ (exp (* 2 x)) x) 'x) '(Ei (* 2 x)))
  (assert-equal (risch-special '(/ 1 (log x)) 'x) '(li x))
  (assert-equal (risch-special '(/ (sin x) x) 'x) '(Si x))
  (assert-equal (risch-special '(/ (cos (* 3 x)) x) 'x) '(Ci (* 3 x))))

(deftest "риш/21k.6: risch-special — частичный ответ (log log x = x·log log x − li x), элементарное возвращается как есть, не из таблицы — #f"
  (assert-equal (risch-special '(log (log x)) 'x) '(+ (* x (log (log x))) (* -1 (li x))))
  (assert-equal (risch-special '(exp x) 'x) '(exp x))
  (assert-equal (risch-special '(exp (^ x 3)) 'x) #f)
  ; 21k.7b: x²e^{x²} = ½x·e^{x²} − ½∫e^{x²} (частичное решение RDE) — остаток уже из таблицы (erfi)
  (assert-equal (risch-special '(* (^ x 2) (exp (^ x 2))) 'x) '(+ (* -1/4 (^ pi 1/2) (erfi x)) (* 1/2 x (exp (^ x 2)))))
  (assert-equal (risch-special '(erf x) 'x) #f))

(deftest "риш/21k.6: sp-diff — производные спецфункций по таблице; неверная пара не проходит проверку"
  (assert-true (risch::sp-ok? '(* 1/2 (^ pi 1/2) (erf x)) '(exp (* -1 (^ x 2))) 'x))
  (assert-true (risch::sp-ok? '(Ei (* 2 x)) '(/ (exp (* 2 x)) x) 'x))
  (assert-true (risch::sp-ok? '(+ (* x (log (log x))) (* -1 (li x))) '(log (log x)) 'x))
  (assert-true (not (risch::sp-ok? '(erf x) '(exp (* -1 (^ x 2))) 'x)))
  (assert-true (not (risch::sp-ok? '(Si x) '(/ (cos x) x) 'x))))

(deftest "риш/21k.6: по умолчанию integrate не меняется — невычисленная форма + условие, причина упоминает спецфункцию"
  (conditions-clear)
  (assert-equal (integrate '(exp (* -1 (^ x 2))) 'x) '(integrate (exp (* -1 (^ x 2))) x))
  (let ((cs (filter (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions))))
    (assert-equal (length cs) 1)
    (assert-true (string-contains? (cadr (car cs)) "erf")))
  (conditions-clear)
  ; 21k.7b: eˣ/x² — частичный ответ −eˣ/x + ∫eˣ/x (было: невычисленная форма целиком); причина у остатка — Ei
  (assert-equal (integrate '(/ (exp x) (^ x 2)) 'x) '(+ (* -1 (^ x -1) (exp x)) (integrate (* (^ x -1) (exp x)) x)))
  (let ((cs (filter (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions))))
    (assert-equal (car (car cs)) '(risch-nonelementary (integrate (* (^ x -1) (exp x)) x)))
    (assert-true (string-contains? (cadr (car cs)) "Ei"))))

(deftest "риш/регрессия 21k.6: ложного «неэлементарно» нет — элементарные слепые примеры берутся (log(x e^x + 1), −1/(x eˣ + 1), e^(x²)/(1 + x²), e^x(x − 1)/x²)"
  (assert-equal (risch-nonelementary? '(/ (* (+ x 1) (exp x)) (+ (* x (exp x)) 1)) 'x) #f)
  (assert-equal (risch-nonelementary? '(/ (* (+ x 1) (exp x)) (^ (+ (* x (exp x)) 1) 2)) 'x) #f)
  (assert-equal (risch-nonelementary? '(/ (* 2 (^ x 3) (exp (^ x 2))) (^ (+ 1 (^ x 2)) 2)) 'x) #f)
  (assert-equal (ra-ok? '(/ (* (exp x) (+ x -1)) (^ x 2))) '(* (^ x -1) (exp x)))
  (assert-equal (ra-ok? '(* (^ x -2) (exp (^ x -1)))) '(* -1 (exp (^ x -1)))))

(deftest "риш/регрессия 21k.6: доказанно неэлементарные из набора — e^x/x², e^(1/x), x²e^(x²), e^(x²+x), e^(x³), e^(−x)/x, (e^x − 1)/x, e^x/x³"
  (assert-equal (risch-nonelementary? '(/ (exp x) (^ x 2)) 'x) #t)
  (assert-equal (risch-nonelementary? '(exp (^ x -1)) 'x) #t)
  (assert-equal (risch-nonelementary? '(* (^ x 2) (exp (^ x 2))) 'x) #t)
  (assert-equal (risch-nonelementary? '(exp (+ x (^ x 2))) 'x) #t)
  (assert-equal (risch-nonelementary? '(exp (^ x 3)) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (exp (* -1 x)) x) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (- (exp x) 1) x) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (exp x) (^ x 3)) 'x) #t))

(deftest "риш/регрессия 21k.6: erf и asin — не «неэлементарно» (вне класса); sin(x)/x с 21k″ доказано неэлементарным"
  (assert-equal (risch-nonelementary? '(erf x) 'x) 'unknown)
  (assert-equal (risch-nonelementary? '(asin x) 'x) 'unknown)
  (assert-equal (risch-nonelementary? '(/ (sin x) x) 'x) #t)
  (assert-equal (risch-nonelementary? '(^ (log x) 1/2) 'x) 'unknown))

(deftest "риш/регрессия 21k.6: бесконечная башня высоты 3 — eˣ·e^(eˣ)·e^(e^(eˣ))-типа и x^x(1 + log x) берутся без побочных log(exp)"
  (assert-equal (ra-ok? '(* (exp x) (exp (exp x)))) '(exp (exp x)))
  (assert-equal (ra-ok? '(* (+ (log x) 1) (^ x x))) '(^ x x))
  (let ((F (ra-ok? '(* (exp x) (exp (exp x)) (exp (exp (exp x)))))))
    (assert-equal F '(exp (exp (exp x))))))

(deftest "риш/21k.6: предпроверка — доказанно неэлементарное с параметрами не гоняется по каскаду (log x/(a x² + b x³ + c x⁴)), условие записано"
  (conditions-clear)
  (let ((e '(/ (log x) (+ (* a (^ x 2)) (* b (^ x 3)) (* c (^ x 4))))) (t0 (clock-us)))
    (assert-equal (car (integrate e 'x)) 'integrate)
    (assert-true (< (- (clock-us) t0) 10000000))
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions)))))

(deftest "риш/21k.6: башня высоты 3 — e^{x + eˣ + e^{eˣ}} = e^{e^{eˣ}}·eˣe^{eˣ}: ∫ = e^{e^{eˣ}} (граница RDE через моном нижней башни)"
  (let ((F (ra-ok? '(exp (+ x (exp x) (exp (exp x)))))))
    (assert-equal F '(exp (exp (exp x)))))
  (assert-equal (ra-ok? '(* (exp x) (exp (exp x)) (exp (* 2 (exp (exp x)))))) '(* 1/2 (exp (* 2 (exp (exp x)))))))

(deftest "риш/21k.6′: производные спецфункций (erf, erfc, erfi, Ei, li, Si, Ci, Shi, Chi) — цепное правило"
  (assert-equal (diff 'x '(erf x)) '(* 2 (^ pi -1/2) (exp (* -1 (^ x 2)))))
  (assert-equal (diff 'x '(erfi x)) '(* 2 (^ pi -1/2) (exp (^ x 2))))
  (assert-equal (diff 'x '(Ei (* 2 x))) '(* (^ x -1) (exp (* 2 x))))
  (assert-equal (diff 'x '(li x)) '(^ (log x) -1))
  (assert-equal (diff 'x '(Ci (* 3 x))) '(* (^ x -1) (cos (* 3 x))))
  (assert-true (int-check '(Si x) '(/ (sin x) x) 'x))
  (assert-true (int-check '(Shi x) '(/ (sinh x) x) 'x))
  (assert-true (int-check '(* -1 (erfc x)) '(* 2 (^ pi -1/2) (exp (* -1 (^ x 2)))) 'x)))

(deftest "риш/21k.6′: ответы risch-special проверяются diff"
  (assert-equal (diff 'x (risch-special '(exp (* -1 (^ x 2))) 'x)) '(exp (* -1 (^ x 2))))
  (assert-equal (diff 'x (risch-special '(/ (exp (* 2 x)) x) 'x)) '(* (^ x -1) (exp (* 2 x))))
  (assert-equal (diff 'x (risch-special '(log (log x)) 'x)) '(log (log x))))

(deftest "риш/21k.6′: неизвестная функция от x — производная через deriv (ODE.0); кусочно-постоянные — 0"
  (assert-equal (diff 'x '(foo (^ x 2))) '(* 2 x (deriv foo 1 (^ x 2))))
  (assert-equal (diff 'x '(foo x)) '(diff (foo x) x))
  (assert-equal (diff 'x '(foo y)) 0)
  (assert-equal (diff 'x '(sign x)) 0)
  (assert-equal (diff 'x '(floor x)) 0))

; ---------- 21k.7a: rs-constant-system, параметрическое и ограниченное интегрирование (prde.lisp) ----------
(define r7-cs risch::rs-constant-system)
(define r7-lim risch::rs-limited-integrate)
(define r7-B (risch::rs-tower 'x))
(define r7-A (risch::rs-extend r7-B '%t1 'log 'x))
(define r7-E (risch::rs-extend r7-B '%t1 'exp 'x))
(define r7-T (risch::rs-extend r7-B '%t1 'atan 'x))
; ответ (ok v cs) проверяется заново: f = Dv + Σ cᵢwᵢ
(define (r7-ok? tw f ws r)
  (and (equal? (car r) 'ok)
       (rt-zero? (cons '+ (cons f (cons (list '* -1 (risch::rs-deriv tw (cadr r))) (map2 (lambda (c w) (list '* -1 c w)) (caddr r) ws)))))))

(deftest "риш/21k.7a: rs-constant-system — совместная система над ℚ, коэффициенты при мономах x"
  (assert-equal (r7-cs '((1 1) (1 -1)) '(3 1) '(x)) '((2 1) ()))
  ; c₁x + c₂ = 2x + 3: сравнение коэффициентов при x¹ и x⁰
  (assert-equal (r7-cs '((x 1)) '((+ (* 2 x) 3)) '(x)) '((2 3) ()))
  (assert-equal (r7-cs '((x 1) (1 0)) '((+ (* 2 x) 3) 2) '(x)) '((2 3) ())))

(deftest "риш/21k.7a: rs-constant-system — несовместная система: particular = #f"
  (assert-equal (r7-cs '((x) (1)) '(1 1) '(x)) '(#f ()))
  ; c·x = 1 при константе c невозможно
  (assert-equal (car (r7-cs '((x)) '(1) '(x))) #f))

(deftest "риш/21k.7a: rs-constant-system — параметр a и log 2 — константы поля"
  (assert-equal (r7-cs '(((* a x) 1)) '((+ x 1)) '(x)) '(((^ a -1) 1) ()))
  (assert-equal (r7-cs '(((* (log 2) x))) '((* 3 x)) '(x)) '(((* 3 (^ (log 2) -1))) ())))

(deftest "риш/21k.7a: rs-constant-system — базис однородной части (c₁ + c₂ + c₃x = 0)"
  (let ((r (r7-cs '((1 1 x)) '(0) '(x))))
    (assert-equal (car r) '(0 0 0))
    (assert-equal (cadr r) '((-1 1 0))))
  ; мономы башни: c₁θ + c₂/x = θ + 2/x, без ограничений на c₃
  (let ((r (r7-cs '((%t1 (^ x -1) 0)) '((+ %t1 (* 2 (^ x -1)))) '(x %t1))))
    (assert-equal (car r) '(1 2 0))
    (assert-equal (cadr r) '((0 0 1)))))

(deftest "риш/21k.7a: rs-gauss (структурная теорема) после выделения rs-gauss-elim не изменился"
  (assert-equal (risch::rs-gauss '((1 1 3) (1 -1 1)) 2) '(2 1))
  (assert-equal (risch::rs-gauss '((1 1) (1 2)) 1) #f)
  (assert-equal (risch::rs-gauss '((1 1 2)) 2) '(2 0)))

(deftest "риш/21k.7a: ограниченное интегрирование над ℚ(x) — 1/x = D0 + 1·(1/x); 1/(1 + x²) без w — нет"
  (assert-equal (r7-lim r7-B '(^ x -1) '((^ x -1))) '(ok 0 (1)))
  (assert-equal (car (r7-lim r7-B '(^ (+ 1 (^ x 2)) -1) '())) 'none)
  (assert-equal (r7-lim r7-B '(^ x 2) '()) '(ok (* 1/3 (^ x 3)) ())))

(deftest "риш/21k.7a: ограниченное интегрирование над ℚ(x) — v ≠ 0 и c ≠ 0 (Эрмит + система над константами)"
  (let* ((f '(+ (* 2 x) (^ x -1) (* -1 (^ x -2)))) (w '((^ x -1))) (r (r7-lim r7-B f w)))
    (assert-true (r7-ok? r7-B f w r))
    (assert-equal (caddr r) '(1)))
  ; −2/(x+1)³ + 3/x = D(1/(x+1)²) + 3·(1/x) + 0·1/(x+1)
  (let* ((f '(+ (* -2 (^ (+ x 1) -3)) (* 3 (^ x -1)))) (w '((^ x -1) (^ (+ x 1) -1))) (r (r7-lim r7-B f w)))
    (assert-true (r7-ok? r7-B f w r))
    (assert-equal (caddr r) '(3 0)))
  (assert-equal (r7-lim r7-B '(* a (^ x -1)) '((^ x -1))) '(ok 0 (a))))

(deftest "риш/21k.7a: ограниченное интегрирование на log-уровне — log x ∈ K, ½log²x, 1/log x — нет"
  (assert-equal (r7-lim r7-A '(^ x -1) '()) '(ok %t1 ()))
  (assert-equal (r7-lim r7-A '(* a (^ x -1)) '()) '(ok (* %t1 a) ()))
  (assert-equal (r7-lim r7-A '(* %t1 (^ x -1)) '()) '(ok (* 1/2 (^ %t1 2)) ()))
  (let ((r (r7-lim r7-A '%t1 '((^ (+ x 1) -1)))))          ; log x = D(x log x − x) + 0·1/(x+1)
    (assert-true (r7-ok? r7-A '%t1 '((^ (+ x 1) -1)) r))
    (assert-equal (caddr r) '(0)))
  (assert-equal (car (r7-lim r7-A '(^ %t1 -1) '())) 'none))

(deftest "риш/21k.7a: ограниченное интегрирование — башни высоты 2 (два log; log log x): константа при θ ловится уровнем ниже"
  (let* ((tw (risch::rs-extend r7-A '%t2 'log '(+ x 1))) (f '(+ (* %t1 (^ x -1)) (^ (+ x 1) -1))) (r (r7-lim tw f '())))
    (assert-true (r7-ok? tw f '() r)))
  (let ((tw (risch::rs-extend r7-A '%t2 'log '%t1)))
    (assert-equal (r7-lim tw '(* (^ x -1) (^ %t1 -1)) '()) '(ok %t2 ()))))

(deftest "риш/21k.7a: ограниченное интегрирование на exp-уровне — x eˣ, eˣ/x — нет, x при w = eˣ/(eˣ + 1)"
  (assert-true (r7-ok? r7-E '(* x %t1) '() (r7-lim r7-E '(* x %t1) '())))
  (assert-equal (car (r7-lim r7-E '(* (^ x -1) %t1) '())) 'none)
  (assert-equal (r7-lim r7-E 'x '((* %t1 (^ (+ %t1 1) -1)))) '(ok (* 1/2 (^ x 2)) (0)))
  (assert-equal (r7-lim r7-E '(* %t1 (^ (+ %t1 1) -1)) '((* %t1 (^ (+ %t1 1) -1)))) '(ok 0 (1))))

(deftest "риш/21k.7a: exp-уровень с несколькими кандидатами — найденное решение верно; с PRDE (21k.7b) «нет» доказано"
  (assert-equal (r7-lim r7-E '%t1 '((* x %t1))) '(ok %t1 (0)))
  ; eˣ/x = Dv + c·x eˣ решения нет: до 21k.7b — unknown, теперь параметрическое RDE доказывает none
  (assert-equal (car (r7-lim r7-E '(* (^ x -1) %t1) '((* x %t1)))) 'none))

(deftest "риш/21k.7a: ограниченное интегрирование на atan-уровне — 1/(1+x²) = D atan x; x/(1+x²) — нет; atan x = D(x atan x) − x/(1+x²)"
  (assert-equal (r7-lim r7-T '(^ (+ 1 (^ x 2)) -1) '()) '(ok %t1 ()))
  (assert-equal (car (r7-lim r7-T '(* x (^ (+ 1 (^ x 2)) -1)) '())) 'none)
  (assert-equal (r7-lim r7-T '%t1 '((* x (^ (+ 1 (^ x 2)) -1)))) '(ok (* %t1 x) (-1))))

(deftest "риш/21k.7a: «нестандартные» константы (sin 1) — нет доказательства отсутствия решения: unknown"
  (assert-equal (car (r7-lim r7-B '(* (sin 1) (^ x -1)) '())) 'unknown)
  (assert-equal (car (r7-lim r7-B '(* (log 2) (^ x -1)) '())) 'none)
  (assert-equal (r7-lim r7-B '(* (log 2) (^ x -1)) '((^ x -1))) '(ok 0 ((log 2)))))

(deftest "риш/21k.7a: драйвер — ∫log x·log(1 + x): остаток частичного ответа прежний, неэлементарность подтверждена ограниченным интегрированием"
  (let* ((e '(* (log x) (log (+ x 1)))) (F (risch-integrate e 'x)))
    (assert-equal F '(+ (* (+ (* -1 x) (* x (log x))) (log (+ 1 x)))
                        (integrate (+ (* x (^ (+ 1 x) -1)) (* -1 x (^ (+ 1 x) -1) (log x))) x)))
    (assert-true (int-check F e 'x)))
  (let ((r (capture-step-log (lambda () (integrate '(* (log x) (log (+ x 1))) 'x)) 'full)))
    (assert-equal (step-rules (cadr r)) '(integration risch risch-tower risch-limited risch-poly risch-check risch-nonelementary))))

(deftest "риш/21k.7a: драйвер — log(x e^{−x} + 1) частично (остаток неэлементарен), eˣ·log(eˣ + 1) и log x·(atan x + x/(1+x²)) элементарны"
  (let* ((e '(log (+ (* x (exp (* -1 x))) 1))) (F (risch-integrate e 'x)))
    (assert-true (contains-sym? F 'integrate))
    (assert-true (int-check F e 'x)))
  (assert-equal (ra-ok? '(* (exp x) (log (+ (exp x) 1)))) '(+ (* (exp x) (log (+ 1 (exp x)))) (* -1 (exp x)) (log (+ 1 (exp x)))))
  (assert-true (ra-ok? '(* (log x) (+ (atan x) (* x (^ (+ 1 (^ x 2)) -1))))))
  (assert-equal (risch-nonelementary? '(* (log x) (atan x)) 'x) #t))
(deftest "риш/SF: значения спецфункций в нуле — erf(0)=erfi(0)=Si(0)=Shi(0)=0, erfc(0)=1"
  (assert-equal (simplify '(erf 0)) 0)
  (assert-equal (simplify '(erfi 0)) 0)
  (assert-equal (simplify '(Si 0)) 0)
  (assert-equal (simplify '(Shi 0)) 0)
  (assert-equal (simplify '(erfc 0)) 1))

(deftest "риш/SF: нечётность erf/erfi/Si/Shi — символьный минус и числовой масштаб"
  (assert-equal (simplify '(erf (* -1 x))) '(* -1 (erf x)))
  (assert-equal (simplify '(erfi (* -1 x))) '(* -1 (erfi x)))
  (assert-equal (simplify '(Si (* -1 x))) '(* -1 (Si x)))
  (assert-equal (simplify '(Shi (* -1 x))) '(* -1 (Shi x)))
  (assert-equal (simplify '(Si (* -2 x))) '(* -1 (Si (* 2 x))))
  (assert-equal (simplify '(erf (* -1/2 y))) '(* -1 (erf (* 1/2 y))))
  (assert-equal (simplify '(erf -3)) '(* -1 (erf 3))))

(deftest "риш/SF: правила срабатывают внутри больших выражений (simplify рекурсивен)"
  (assert-equal (simplify '(+ (erf (* -1 x)) (erf x))) 0)
  (assert-equal (simplify '(* (Si 0) (exp x))) 0)
  (assert-equal (simplify '(* 2 (^ (erfi (* -1 x)) 2))) '(* 2 (^ (erfi x) 2))))

(deftest "риш/SF: erfc, Ei, li, Ci, Chi не упрощаются — ни значений, ни чётности/нечётности"
  (assert-equal (simplify '(erfc (* -1 x))) '(erfc (* -1 x)))
  (assert-equal (simplify '(Ci (* -1 x))) '(Ci (* -1 x)))
  (assert-equal (simplify '(Chi (* -1 x))) '(Chi (* -1 x)))
  (assert-equal (simplify '(Ei 0)) '(Ei 0))
  (assert-equal (simplify '(li 1)) '(li 1))
  (assert-equal (simplify '(- (erfc x) 1)) '(+ -1 (erfc x))))

(deftest "риш/SF: значения в нуле и нечётность верны математически — проверка diff"
  (assert-equal (diff 'x '(erf x)) '(* 2 (^ pi -1/2) (exp (* -1 (^ x 2)))))
  (assert-equal (diff 'x '(* -1 (erf (* -1 x)))) '(* 2 (^ pi -1/2) (exp (* -1 (^ x 2)))))
  (assert-true (int-check '(+ (* x (erf 0)) (erfi 0)) 0 'x)))

(deftest "риш/SF: sp-ok? теперь через diff/int-check — те же примеры 21k.6 проходят"
  (assert-true (risch::sp-ok? '(* 1/2 (^ pi 1/2) (erf x)) '(exp (* -1 (^ x 2))) 'x))
  (assert-true (risch::sp-ok? '(Ei (* 2 x)) '(/ (exp (* 2 x)) x) 'x))
  (assert-true (risch::sp-ok? '(+ (* x (log (log x))) (* -1 (li x))) '(log (log x)) 'x))
  (assert-true (not (risch::sp-ok? '(erf x) '(exp (* -1 (^ x 2))) 'x)))
  (assert-true (not (risch::sp-ok? '(Si x) '(/ (cos x) x) 'x))))

(deftest "риш/SF: ответы risch-special проверяются diff — erfc, масштаб, сумма"
  (assert-equal (diff 'x (risch-special '(exp (* -4 (^ x 2))) 'x)) '(exp (* -4 (^ x 2))))
  (assert-equal (diff 'x (risch-special '(/ (sin (* 3 x)) x) 'x)) '(* (^ x -1) (sin (* 3 x))))
  (assert-true (int-check (risch-special '(exp (* -1 (^ x 2))) 'x) '(exp (* -1 (^ x 2))) 'x))
  (assert-true (int-check (risch-special '(log (log x)) 'x) '(log (log x)) 'x))
  (assert-equal (risch-special '(exp (* 2 (^ x 2))) 'x) '(* 1/4 (^ 2 1/2) (^ pi 1/2) (erfi (* (^ 2 1/2) x)))))

(deftest "риш/SF: нечётность консервативна — без декларации знака символьный множитель не трогается, с декларацией (a negative) выносит минус"
  (assert-equal (simplify '(erf (* a x))) '(erf (* a x)))
  (assert-equal (simplify '(Shi (* a y))) '(Shi (* a y)))
  (assert-equal (assuming ((a negative)) (simplify '(erf (* a x)))) '(* -1 (erf (* -1 a x))))
  (assert-equal (assuming ((a negative)) (simplify '(Si (* a x)))) '(* -1 (Si (* -1 a x)))))

; ---------- 21k.7b: параметрическое RDE (prde.lisp: rs-param-rde), частичные решения RDE, однородные решения ----------
(define r8-prde risch::rs-param-rde)
(define r8-part risch::rs-rde-partial)
(define r8-B (risch::rs-tower 'x))
(define r8-E (risch::rs-extend r8-B '%t1 'exp 'x))
(define r8-L (risch::rs-extend r8-B '%t1 'log 'x))
(define r8-L2 (risch::rs-extend r8-L '%t2 'log '(+ x 1)))
; каждый элемент базиса (y κ): Dy + f·y = Σ κᵢgᵢ
(define (r8-basis-ok? tw f gs r)
  (and (equal? (car r) 'ok)
       (every? (lambda (s) (rt-zero? (cons '+ (cons (risch::rs-deriv tw (car s)) (cons (list '* f (car s))
                                                  (map2 (lambda (k g) (list '* -1 k g)) (cadr s) gs))))))
               (cadr r))))
; частичное решение (y r): g = Dy + f·y + r
(define (r8-part-ok? tw f g p) (rt-zero? (list '+ g (list '* -1 (risch::rs-deriv tw (car p))) (list '* -1 f (car p)) (list '* -1 (cadr p)))))
; частичный ответ F + c·∫R: int-check по F против e − (остаток)
(define (r8-partial-ok? e F)
  (and (contains-sym? F 'integrate)
       (let* ((ts (if (equal? (car F) '+) (cdr F) (list F)))
              (rs (filter (lambda (t) (contains-sym? t 'integrate)) ts))
              (fs (filter (lambda (t) (not (contains-sym? t 'integrate))) ts))
              (rem (map (lambda (t) (if (equal? (car t) 'integrate) (cadr t) (list '* (cadr t) (cadr (caddr t))))) rs)))
         (int-check (cons '+ (cons 0 fs)) (simplify (list '+ e (list '* -1 (cons '+ (cons 0 rem))))) 'x))))

(deftest "риш/21k.7b: param_rde над ℚ(x) — базис Dy + y = c₁x + c₂: (x − 1, (1 0)) и (1, (0 1))"
  (let ((r (r8-prde r8-B 1 '(x 1))))
    (assert-true (r8-basis-ok? r8-B 1 '(x 1) r))
    (assert-equal (cadr r) '(((+ -1 x) (1 0)) (1 (0 1))))))

(deftest "риш/21k.7b: param_rde — несовместность: Dy + y = c·(1/x) только c = 0 (пустой базис), Dy + 2xy = c₁ + c₂x — только c₁ = 0"
  (assert-equal (r8-prde r8-B 1 '((^ x -1))) '(ok ()))
  (assert-equal (r8-prde r8-B '(* 2 x) '(1 x)) '(ok ((1/2 (0 1))))))

(deftest "риш/21k.7b: param_rde — однородные решения входят в базис: Dy − y/x = c·x даёт (x, (0)) и (x², (1)); без правых частей — (x, ())"
  (let ((r (r8-prde r8-B '(* -1 (^ x -1)) '(x))))
    (assert-true (r8-basis-ok? r8-B '(* -1 (^ x -1)) '(x) r))
    (assert-equal (cadr r) '((x (0)) ((^ x 2) (1)))))
  (assert-equal (r8-prde r8-B '(* -1 (^ x -1)) '()) '(ok ((x ())))))

(deftest "риш/21k.7b: param_rde на exp-уровне — Dy + y = c₁eˣ + c₂: однородное e⁻ˣ (специальный знаменатель), eˣ/2, 1"
  (let ((r (r8-prde r8-E 1 '(%t1 1))))
    (assert-true (r8-basis-ok? r8-E 1 '(%t1 1) r))
    (assert-equal (cadr r) '(((^ %t1 -1) (0 0)) ((* 1/2 %t1) (1 0)) (1 (0 1)))))
  (let ((r (r8-prde r8-E 2 '((* %t1 (^ x -1)) %t1))))       ; eˣ/x недостижимо: только c₁ = 0
    (assert-true (r8-basis-ok? r8-E 2 '((* %t1 (^ x -1)) %t1) r))
    (assert-equal (map cadr (cadr r)) '((0 0) (0 1)))))

(deftest "риш/21k.7b: param_rde — параметр a и log-уровень: Dy + a·y = c·x; Dy + y/x = c·log x (однородное 1/x)"
  (let ((r (r8-prde r8-B 'a '(x))))
    (assert-true (r8-basis-ok? r8-B 'a '(x) r))
    (assert-equal (length (cadr r)) 1))
  (let ((r (r8-prde r8-L '(^ x -1) '(%t1))))
    (assert-true (r8-basis-ok? r8-L '(^ x -1) '(%t1) r))
    (assert-equal (map cadr (cadr r)) '((0) (1)))))

(deftest "риш/21k.7b: param_rde — «нестандартная» константа sin 1: базис не утверждается полным (incomplete)"
  (assert-equal (car (r8-prde r8-B 1 '((* (sin 1) (^ x -1))))) 'incomplete))

(deftest "риш/21k.7b: ограниченное интегрирование на exp-уровне с несколькими кандидатами — eˣ/x + x eˣ = D((x − 1)eˣ) + 1·eˣ/x"
  (let* ((f '(+ (* %t1 (^ x -1)) (* x %t1))) (w '((* %t1 (^ x -1)))) (r (r7-lim r8-E f w)))
    (assert-true (r7-ok? r8-E f w r))
    (assert-equal (caddr r) '(1)))
  (let* ((f '(* %t1 (^ x -1))) (w '((* x %t1) (* %t1 (^ x -2)))) (r (r7-lim r8-E f w)))   ; eˣ/x = D(eˣ/x) + eˣ/x²
    (assert-true (r7-ok? r8-E f w r))
    (assert-equal (caddr r) '(0 1))))

(deftest "риш/21k.7b: параметрическое интегрирование rs-pi на exp-уровне — базис для (eˣ/x, eˣ/x², x eˣ)"
  (let* ((gs '((* %t1 (^ x -1)) (* %t1 (^ x -2)) (* x %t1))) (b (risch::rs-pi r8-E gs)))
    (assert-equal (length b) 2)
    (assert-true (every? (lambda (s) (rt-zero? (list '+ (risch::rs-deriv r8-E (car s)) (list '* -1 (risch::rs-lin (cadr s) gs))))) b))))

(deftest "риш/21k.7b: RDE primitive — однородное решение вне базы (w = log x уровня ниже): Dy − y/(x log x) = log x/(x + 1) ⇒ y = log x·log(x + 1)"
  (let* ((f '(* -1 (^ (* x %t1) -1))) (g '(* %t1 (^ (+ x 1) -1))) (r (risch::rs-rde r8-L2 f g)))
    (assert-true (r5-ok? r8-L2 f g r))
    (assert-true (rt-eq? (cadr r) '(* %t1 %t2)))))

(deftest "риш/21k.7b: граница RDE primitive при deg b = deg a > 0 (было «не доказано»): Dy + (1 + 1/log x)y = 1 — нет; = log²x + log x + 2log x/x — y = log²x"
  (assert-equal (car (risch::rs-rde r8-L '(+ 1 (^ %t1 -1)) 1)) 'none)
  (assert-equal (risch::rs-rde r8-L '(+ 1 (^ %t1 -1)) '(+ (^ %t1 2) %t1 (* 2 %t1 (^ x -1)))) '(ok (^ %t1 2))))

(deftest "риш/21k.7b: частичное решение RDE — eˣ/x²: y = −1/x, r = 1/x; x²e^{x²}: y = x/2, r = −1/2; eˣ log x: y = log x, r = −1/x"
  (assert-equal (r8-part r8-B 1 '(^ x -2)) '((* -1 (^ x -1)) (^ x -1)))
  (assert-equal (r8-part r8-B '(* 2 x) '(^ x 2)) '((* 1/2 x) -1/2))
  (assert-equal (r8-part r8-L 1 '%t1) '(%t1 (* -1 (^ x -1))))
  (assert-true (r8-part-ok? r8-L 1 '%t1 (r8-part r8-L 1 '%t1))))

(deftest "риш/21k.7b: частичное решение RDE — повторение, пока остаток проще (eˣ/x³ → ½∫eˣ/x); без упрощения y = 0 (eˣ/x)"
  (let ((p (r8-part r8-B 1 '(^ x -3))))
    (assert-true (r8-part-ok? r8-B 1 '(^ x -3) p))
    (assert-equal (cadr p) '(* 1/2 (^ x -1))))
  (assert-equal (r8-part r8-B 1 '(^ x -1)) '(0 (^ x -1)))
  (let ((p (r8-part r8-B 1 '(^ (+ 1 (^ x 2)) -2))))                    ; знаменатель остатка — (1 + x²)¹
    (assert-true (r8-part-ok? r8-B 1 '(^ (+ 1 (^ x 2)) -2) p))
    (assert-equal (degree (denom (together (cadr p))) 'x) 2)))

(deftest "риш/21k.7b: ∫eˣ·log x = eˣ log x − ∫eˣ/x (было: неэлементарно целиком); условие — только на остатке"
  (conditions-clear)
  (let* ((e '(* (exp x) (log x))) (F (integrate e 'x)))
    (assert-equal F '(+ (* (exp x) (log x)) (* -1 (integrate (* (^ x -1) (exp x)) x))))
    (assert-true (r8-partial-ok? e F))
    (assert-equal (map car (filter (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions)))
                  '((risch-nonelementary (integrate (* (^ x -1) (exp x)) x)))))
  (assert-equal (risch-nonelementary? '(* (exp x) (log x)) 'x) #t))

(deftest "риш/21k.7b: ∫x²e^{x²} = ½x·e^{x²} − ½∫e^{x²}; ∫x⁴e^{x²}; ∫e^{x²}/x² = −e^{x²}/x + 2∫e^{x²}"
  (let* ((e '(* (^ x 2) (exp (^ x 2)))) (F (integrate e 'x)))
    (assert-equal F '(+ (* 1/2 x (exp (^ x 2))) (* -1/2 (integrate (exp (^ x 2)) x))))
    (assert-true (r8-partial-ok? e F)))
  (let* ((e '(* (^ x 4) (exp (^ x 2)))) (F (risch-integrate e 'x)))
    (assert-true (r8-partial-ok? e F))
    (assert-true (contains-sym? F 'integrate)))
  (assert-equal (risch-integrate '(/ (exp (^ x 2)) (^ x 2)) 'x)
                '(+ (* -1 (^ x -1) (exp (^ x 2))) (* 2 (integrate (exp (^ x 2)) x)))))

(deftest "риш/21k.7b: ∫eˣ/x³ через integrate — частичный с остатком ½∫eˣ/x; ∫e⁻ˣ/x²"
  (let* ((e '(/ (exp x) (^ x 3))) (F (integrate e 'x)))
    (assert-equal F '(+ (* 1/2 (^ x -2) (+ -1 (* -1 x)) (exp x)) (* 1/2 (integrate (* (^ x -1) (exp x)) x))))
    (assert-true (r8-partial-ok? e F)))
  (let* ((e '(/ (exp (* -1 x)) (^ x 2))) (F (risch-integrate e 'x)))
    (assert-equal F '(+ (* -1 (^ x -1) (exp (* -1 x))) (* -1 (integrate (* (^ x -1) (exp (* -1 x))) x))))
    (assert-true (r8-partial-ok? e F))))

(deftest "риш/21k.7b: башни высоты 2 — ∫x^x·log x = x^x − ∫x^x, ∫x^x·log²x частично; eˣ/(1 + x²)²"
  (assert-equal (integrate '(* (^ x x) (log x)) 'x) '(+ (^ x x) (* -1 (integrate (^ x x) x))))
  (let* ((e '(* (^ x x) (^ (log x) 2))) (F (integrate e 'x)))
    (assert-true (r8-partial-ok? e F)))
  (let* ((e '(/ (exp x) (^ (+ 1 (^ x 2)) 2))) (F (risch-integrate e 'x)))
    (assert-true (r8-partial-ok? e F))))

(deftest "риш/21k.7b: неэлементарные без упрощения остаются невычисленными целиком — eˣ/x, exp(x²), x^x, eˣ/(x + 1), exp(eˣ)"
  (assert-equal (integrate '(/ (exp x) x) 'x) '(integrate (* (^ x -1) (exp x)) x))
  (assert-equal (integrate '(exp (^ x 2)) 'x) '(integrate (exp (^ x 2)) x))
  (assert-equal (integrate '(^ x x) 'x) '(integrate (^ x x) x))
  (assert-equal (integrate '(/ (exp x) (+ x 1)) 'x) '(integrate (* (^ (+ 1 x) -1) (exp x)) x))
  (assert-equal (integrate '(exp (exp x)) 'x) '(integrate (exp (exp x)) x)))

(deftest "риш/21k.7b: журнал — шаг risch-rde с частичным решением; без частичных решений (rs-rde-partials? #f) — прежнее «неэлементарно целиком»"
  (let ((r (capture-step-log (lambda () (integrate '(/ (exp x) (^ x 2)) 'x)) 'full)))
    (assert-equal (step-rules (cadr r)) '(integration risch risch-tower risch-rde risch-exp-part risch-check risch-nonelementary)))
  (assert-equal (risch::rs-run-partials '(* (^ x -2) (exp x)) 'x #f) #f)
  (assert-equal risch::rs-rde-partials? #t))

(deftest "риш/21k.7b: частичный ответ — не полная пометка nonelementary: risch-nonelementary? = #t, но integrate возвращает ответ, а условие — на остатке"
  (conditions-clear)
  (let ((F (integrate '(* (^ x 2) (exp (^ x 2))) 'x)))
    (assert-true (contains-sym? F 'integrate))
    (assert-true (not (any? (lambda (c) (equal? (car c) '(risch-nonelementary (integrate (* (^ x 2) (exp (^ x 2))) x)))) (conditions)))))
  (assert-equal (risch-nonelementary? '(* (^ x 2) (exp (^ x 2))) 'x) #t))

(deftest "риш/21k.7b: прежние элементарные ответы exp-случая не меняются (x eˣ, (1 + 2x²)e^{x²}, eˣ(log x + 1/x), x eˣ/(1 + x)²)"
  (assert-equal (risch-integrate '(* x (exp x)) 'x) '(* (+ -1 x) (exp x)))
  (assert-equal (ra-ok? '(* (+ 1 (* 2 (^ x 2))) (exp (^ x 2)))) '(* x (exp (^ x 2))))
  (assert-equal (ra-ok? '(* (exp x) (+ (log x) (^ x -1)))) '(* (exp x) (log x)))
  (assert-equal (ra-ok? '(/ (* x (exp x)) (^ (+ 1 x) 2))) '(* (^ (+ 1 x) -1) (exp x))))

; ---------- подшаг 21k″: тригонометрия — вещественный tan-моном (Dθ = Du·(1 + θ²)), lib\risch\tan.lisp ----------
(define (rk-num e v) (eval-num (replace-expr e 'x v)))
(define rk-T1 (risch::rs-extend (risch::rs-tower 'x) '%t1 'tan 'x))
(define rk-T2 (risch::rs-extend (risch::rs-tower 'x) '%t1 'tan '(* 1/2 x)))
(define (rk-ok? e) (let ((F (risch-integrate e 'x))) (and F (not (contains-sym? F 'integrate)) (int-check F e 'x) F)))
; f(θ) башни равно исходному выражению в точке (θ = tan w)
(define (rk-tower-ok? e v &rest ref)
  (let ((r (rt-build e)))
    (< (abs (- (rk-num (risch::rs-back-subst (cadr r) (caddr r)) v) (rk-num (if (null? ref) e (car ref)) v))) 0.0000001)))

(deftest "риш/tan: rs-extend — Dθ = Du·(1 + θ²), rs-case = tan, уровень над exp"
  (assert-equal (risch::rs-case rk-T1) 'tan)
  (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top rk-T1)) '(+ 1 (^ %t1 2))))
  (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top rk-T2)) '(* 1/2 (+ 1 (^ %t1 2)))))
  (let ((tw (risch::rs-extend (risch::rs-tower 'x) '%t1 'tan '(^ x 2))))
    (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top tw)) '(* 2 x (+ 1 (^ %t1 2))))))
  (let ((tw (risch::rs-extend (risch::rs-extend (risch::rs-tower 'x) '%t1 'exp 'x) '%t2 'tan '%t1)))
    (assert-equal (risch::rs-case tw) 'tan)
    (assert-true (rt-eq? (risch::rs-level-dtheta (risch::rs-top tw)) '(* %t1 (+ 1 (^ %t2 2)))))
    (assert-equal (risch::rs-case (risch::rs-lower tw)) 'exp)))

(deftest "риш/tan: D(tan x) = 1 + tan²x и D(tan²x) = 2 tan x (1 + tan²x) по башне"
  (assert-true (rt-eq? (risch::rs-deriv rk-T1 '%t1) '(+ 1 (^ %t1 2))))
  (assert-true (rt-eq? (risch::rs-deriv rk-T1 '(^ %t1 2)) '(* 2 %t1 (+ 1 (^ %t1 2)))))
  (assert-true (rt-eq? (risch::rs-deriv rk-T2 '(* x %t1)) '(+ %t1 (* 1/2 x (+ 1 (^ %t1 2)))))))

(deftest "риш/tan: башня из tan x — один уровень tan, аргумент x; sin x — половинный угол tan(x/2)"
  (let ((r (rt-build '(tan x))))
    (assert-equal (rt-kinds r) '(tan))
    (assert-equal (rt-arg r 0) 'x)
    (assert-equal (risch::rs-case (car r)) 'tan))
  (let ((r (rt-build '(sin x))))
    (assert-equal (rt-kinds r) '(tan))
    (assert-equal (rt-arg r 0) '(* 1/2 x))
    (assert-true (rt-eq? (rt-dth r 0) '(* 1/2 (+ 1 (^ %t1 2)))))))

(deftest "риш/tan: sin, cos, tan, cot разных кратных углов — один уровень, значение в точке совпадает"
  (assert-equal (length (rt-levels (rt-build '(+ (sin x) (cos (* 2 x)) (tan x))))) 1)
  (assert-true (rk-tower-ok? '(+ (sin x) (cos (* 2 x)) (tan x)) 7/10))
  (assert-true (rk-tower-ok? '(* (sin (* 3 x)) (cot (* 2 x))) 3/10 '(/ (sin (* 3 x)) (tan (* 2 x)))))
  (assert-true (rk-tower-ok? '(+ (sec x) (csc (* 1/2 x))) 9/10 '(+ (/ 1 (cos x)) (/ 1 (sin (* 1/2 x))))))
  (assert-equal (rt-kinds (rt-build '(+ (tan x) (tan (* 2 x))))) '(tan))
  (assert-true (rk-tower-ok? '(* (sin (+ x 1)) (cos x)) 6/5)))

(deftest "риш/tan: «не знаю» — вложенная тригонометрия, несвязанные углы, tan не сверху, atan рядом"
  (assert-true (rt-unknown? '(sin (sin x))))
  (assert-true (rt-unknown? '(+ (sin x) (sin (^ x 2)))))
  (assert-true (rt-unknown? '(exp (tan x))))
  ; log(cos x): башня теперь строится (log выше tan разрешён в R2.4), но интеграл не берётся
  (assert-true (let ((A (integrate '(log (cos x)) 'x))) (and (pair? A) (equal? (car A) 'integrate))))
  (assert-true (rt-unknown? '(+ (atan x) (tan x))))
  ; от x не зависит — константа, башня пустая
  (assert-equal (car (rt-build '(+ (sin 1) (tan 2)))) '(x)))

(deftest "риш/tan: система (19) над ℚ(x): sin x/x и cos x/x — нет решения; найденное решение c′ − d = a, d′ + c = b"
  (assert-equal (risch::rs-tan-solve rk-T2 1 '(/ 2 x) 0) 'none)
  (assert-equal (risch::rs-tan-solve rk-T2 1 0 '(/ 2 x)) 'none)
  (let ((s (risch::rs-tan-solve rk-T2 1 0 'x)))                       ; c = x, d = 1: a = 1 − 1 = 0, b = x
    (assert-true (rt-eq? (car s) 'x))
    (assert-true (rt-eq? (cadr s) 1)))
  (assert-equal (risch::rs-tan-solve rk-T2 1 0 0) '(0 0)))

(deftest "риш/tan: многочленная часть — θ² + 1 = Dθ, θ² + xθ + 1: остаток xθ неэлементарен, θ = Dlog√(1+θ²)"
  (let ((r (risch::rs-tan-poly rk-T1 '(1 0 1))))
    (assert-true (rt-eq? (car r) '%t1))
    (assert-equal (cadr r) 0))
  (assert-equal (risch::rs-tan-poly rk-T1 (list 1 'x 1)) 'ne)
  (let ((r (risch::rs-tan-poly rk-T1 '(1 0))))                        ; ∫ tan x = ½ log(1 + θ²)
    (assert-equal (cadr r) 0)
    (assert-equal (car r) '(* 1/2 (log (+ 1 (^ %t1 2)))))))

(deftest "риш/tan: неэлементарно (доказано) — sin x/x, cos x/x, sin x², cos x², sin(1/x)"
  (assert-equal (risch-nonelementary? '(/ (sin x) x) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (cos x) x) 'x) #t)
  (assert-equal (risch-nonelementary? '(sin (^ x 2)) 'x) #t)
  (assert-equal (risch-nonelementary? '(cos (^ x 2)) 'x) #t)
  (assert-equal (risch-nonelementary? '(sin (^ x -1)) 'x) #t))

(deftest "риш/tan: неэлементарно — eˣ·tan x и x·tan x (многочленная часть), eˣ/(1 + tan x) (неконстантный вычет)"
  (assert-equal (risch-nonelementary? '(* (exp x) (tan x)) 'x) #t)
  (assert-equal (risch-nonelementary? '(* x (tan x)) 'x) #t)
  (assert-equal (risch-nonelementary? '(+ 1 (* x (tan x)) (^ (tan x) 2)) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (exp x) (+ 1 (tan x))) 'x) #t))

(deftest "риш/tan: неэлементарно — sin x/(x + 1), cos x/x², sin x/(1 + x²), x·cot x"
  (assert-equal (risch-nonelementary? '(/ (sin x) (+ x 1)) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (cos x) (^ x 2)) 'x) #t)
  (assert-equal (risch-nonelementary? '(/ (sin x) (+ 1 (^ x 2))) 'x) #t)
  (assert-equal (risch-nonelementary? '(* x (cot x)) 'x) #t))

(deftest "риш/tan: элементарные ответы, проверенные int-check — 1/(2 + sin x), 1/(3 + cos x), sin²x"
  (assert-true (rk-ok? '(/ 1 (+ 2 (sin x)))))
  (assert-true (rk-ok? '(/ 1 (+ 3 (cos x)))))
  (assert-true (rk-ok? '(^ (sin x) 2))))

(deftest "риш/tan: производные элементарных функций с полюсами берутся — (sin x/x)′, (x/sin x)′, (tan x/x)′"
  (assert-true (rk-ok? (diff 'x '(/ (sin x) x))))
  (assert-true (rk-ok? (diff 'x '(/ x (sin x)))))
  (assert-true (rk-ok? (diff 'x '(/ (tan x) x)))))

(deftest "риш/tan: tan над exp и tan(x²): ∫eˣ·tan(eˣ) = −log cos eˣ, ∫x·tan(x²) = −½ log cos x², x/(1 + x tan x) = (log(cos x + x sin x))′"
  (assert-true (rk-ok? '(* (exp x) (tan (exp x)))))
  (assert-true (rk-ok? '(* x (tan (^ x 2)))))
  (assert-true (rk-ok? '(/ (+ x (* (^ x 2) (tan x))) (^ (+ 1 (* x (tan x))) 2)))))

(deftest "риш/tan: integrate — прежние ответы не меняются (Риш последним), sin x/x остаётся невычисленным с условием nonelementary"
  (assert-equal (integrate '(sin x) 'x) '(* -1 (cos x)))
  (assert-equal (integrate '(tan x) 'x) '(* -1 (log (cos x))))
  (conditions-clear)
  (assert-equal (integrate '(/ (sin x) x) 'x) '(integrate (* (^ x -1) (sin x)) x))
  (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions))))

(deftest "риш/tan: integrate берёт то, что прежний каскад не брал — 1/(2 + cos x), 1/(2 + sin x); условие risch-tan-branch"
  (conditions-clear)
  (let ((F (integrate '(/ 1 (+ 2 (cos x))) 'x)))
    (assert-true (not (contains-sym? F 'integrate)))
    (assert-true (int-check F '(/ 1 (+ 2 (cos x))) 'x)))
  (assert-true (any? (lambda (c) (equal? (car (car c)) 'risch-tan-branch)) (conditions)))
  (assert-true (not (contains-sym? (integrate '(/ 1 (+ 2 (sin x))) 'x) 'integrate))))

(deftest "риш/tan: определённый интеграл через tan(w) не подставляется (разрыв первообразной) — невычисленная форма; прежние определённые на месте"
  ; DI.3: подстановка через разрывную первообразную по-прежнему не делается; значение даёт модуль definite (вычеты на окружности)
  (assert-equal (integrate '(/ 1 (+ 2 (cos x))) 'x 0 (* 2 'pi)) '(* 2/3 (^ 3 1/2) pi))
  (assert-equal (integrate '(* x (sin x)) 'x 0 'pi) 'pi)
  (assert-equal (integrate '(^ (sin x) 2) 'x 0 'pi) '(* 1/2 pi)))

(deftest "риш/tan: eˣ·tan x — предпроверка доказывает неэлементарность за доли секунды, каскад (≈ 4 мин) не гоняется"
  (let ((t0 (clock-us)))
    (assert-equal (integrate '(* (exp x) (tan x)) 'x) '(integrate (* (^ (cos x) -1) (exp x) (sin x)) x))
    (assert-true (< (- (clock-us) t0) 5000000))))

; ---------- R2.1: tan над башней exp/log: guard бюджета ----------

(deftest "risch: R2.1 — tan над exp не виснет (guard бюджета RDE)"
  ; RDE над башней разрешён только для одного уровня и малых a,b;
  ; вне бюджета — быстрый отказ, а не многоминутный rs-rde
  (let ((A (integrate '(* (exp x) (tan x)) 'x)))
    (assert-true (or (equal? A 'unknown)
                     (and (pair? A) (equal? (car A) 'integrate))))))

; ---------- R2.2: logextint — параметрическая лог-производная общего вида ----------

(deftest "risch: R2.2 — α = Dv/v + m·η, v — любая рациональная функция (не только моном)"
  ; 2x/(x²+1) = D(x²+1)/(x²+1), m = 0
  (let ((r (risch::rde-log-deriv-base '(/ (* 2 x) (+ (^ x 2) 1)) 1 'x)))
    (assert-equal (car r) 0)
    (assert-true (rt-eq? (cadr r) '(+ 1 (^ x 2)))))
  ; 1/(x−1) − 1/(x+2) = D((x−1)/(x+2))/((x−1)/(x+2)): v — не моном
  (let ((r (risch::rde-log-deriv-base '(- (/ 1 (- x 1)) (/ 1 (+ x 2))) 1 'x)))
    (assert-equal (car r) 0)
    (assert-true (rt-eq? (cadr r) '(* (+ -1 x) (^ (+ 2 x) -1)))))
  ; полиномиальная часть α кратна η: m = 3
  (let ((r (risch::rde-log-deriv-base '(+ (/ (* 2 x) (+ (^ x 2) 1)) 3) 1 'x)))
    (assert-equal (car r) 3)
    (assert-true (rt-eq? (cadr r) '(+ 1 (^ x 2)))))
  ; 1/x + 1 = D(x)/x + 1
  (let ((r (risch::rde-log-deriv-base '(+ (/ 1 x) 1) 1 'x)))
    (assert-equal (car r) 1)
    (assert-true (rt-eq? (cadr r) 'x)))
  ; граница RDE берёт m из этой функции
  (assert-equal (risch::rde-plogd (risch::rs-tower 'x) '(/ (* 2 x) (+ (^ x 2) 1)) 1) 0))

(deftest "risch: R2.2 — подделки: нерациональный/нецелый вычет, кратный полюс, чужая полиномиальная часть"
  ; 1/(x²+1): вычеты ±i/2 не рациональны — v ∈ ℚ(x) нет
  (assert-equal (risch::rde-log-deriv-base '(/ 1 (+ (^ x 2) 1)) 1 'x) #f)
  ; кратный полюс: у Dv/v полюсы только простые
  (assert-equal (risch::rde-log-deriv-base '(/ 1 (^ (+ x 1) 2)) 1 'x) #f)
  ; полиномиальная часть α не кратна полиномиальной части η
  (assert-equal (risch::rde-log-deriv-base 'x 1 'x) #f)
  ; вычет не целый: 1/(2(x+1)) — кратно, но нецело
  (assert-equal (risch::rde-log-deriv-base '(/ 1 (* 2 (+ x 1))) 1 'x) #f)
  ; полиномиальная часть сходится, а дробная — нет (старый код вернул бы m = 1)
  (assert-equal (risch::rde-log-deriv-base '(+ (/ 1 (+ (^ x 2) 1)) 1) 1 'x) #f))

; ---------- R2.3: тригонометрия поверх башни exp/log ----------

(deftest "risch: R2.3 — tan-RDE над exp-уровнем: c,d из точного разложения по i, строки (19) сходятся"
  ; eˣ·sin²x: tan(x/2)-уровень над exp x, специальная часть k = 2, A = 4eˣθ² → a = 0, b = −4eˣ
  (let* ((lo (risch::rs-extend (risch::rs-tower 'x) '%t1 'exp 'x))
         (tw (risch::rs-extend lo '%t2 'tan '(* 1/2 x)))
         (r (risch::rs-tan-solve tw 2 0 '(* -4 %t1))))
    (assert-true (pair? r))
    ; y = −4i·eˣ/(1+2i) = −8/5·eˣ − 4/5·i·eˣ: c и d — без i
    (assert-true (rt-eq? (car r) '(* -8/5 %t1)))
    (assert-true (rt-eq? (cadr r) '(* -4/5 %t1)))
    ; (19) при f = 2·k·Db = 2: c′ − f·d = 0, d′ + f·c = −4eˣ (производная — башни, не diff)
    (assert-true (risch::rs-zero? (list '+ (risch::rs-deriv lo (car r)) (list '* -2 (cadr r)))))
    (assert-true (risch::rs-zero? (list '+ (risch::rs-deriv lo (cadr r))
                                        (list '* 2 (car r)) '(* 4 %t1))))))

(deftest "risch: R2.3 — повторный вызов через кэш tan-RDE не падает; eˣ·sin²x берётся и проверяется"
  ; кэш хранит (list res), читать надо (car hit): прежнее (cadr hit) давало nth вне границ
  ; на втором вызове (предпроверка + каскад в одном процессе)
  (let* ((H '(* (exp x) (^ (sin x) 2)))
         (R1 (risch::int-risch H 'x 0))
         (R2 (risch::int-risch H 'x 0)))
    (assert-true (and R1 R2))
    (assert-true (int-check R2 H 'x)))
  (let ((A (integrate '(* (exp x) (^ (sin x) 2)) 'x)))
    (assert-true (and (pair? A) (not (equal? (car A) 'integrate))))
    (assert-true (int-check A '(* (exp x) (^ (sin x) 2)) 'x))))

(deftest "risch: R2.3 — ∫log x·sin x доказанно неэлементарен (условие risch-nonelementary, быстро)"
  ; по частям ∫log x·sin x = −log x·cos x + Ci(x): Ci неэлементарен; РИШ доказывает это через tan-уровень
  (let* ((H '(* (log x) (sin x)))
         (cr (capture-conditions (lambda () (integrate H 'x))))
         (A (car cr)))
    (assert-true (and (pair? A) (equal? (car A) 'integrate)))
    (assert-true (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary)))
                       (cadr cr))))
  (let ((t0 (clock-us)))
    (integrate '(* (log x) (sin x)) 'x)
    (assert-true (< (- (clock-us) t0) 2000000))))

; ---------- R2.4: log над tan в башне и полевой сертификат ----------

(deftest "risch: R2.4 — log выше tan разрешён, exp выше tan нет; H2 сертифицируется в башне"
  (let* ((N (integrate::int-norm '(- (* (exp x) (log (cos x))) (* (exp x) (tan x)))))
         (bt (car (capture-conditions (lambda () (risch::rs-build-tower N 'x))))))
    (assert-true (pair? bt))                                        ; башня строится
    (assert-true (any? (lambda (lv) (equal? (risch::rs-level-kind lv) 'log))
                       (risch::rs-levels (car bt)))))               ; log-уровни над tan
  ; exp(tan x) по-прежнему вне башни
  (assert-equal (car (capture-conditions (lambda () (risch::rs-build-tower '(exp (tan x)) 'x)))) #f)
  ; полевой сертификат D(F) = f: int-risch отдаёт ответ для H2 (int-check на полуугловой форме врёт)
  (assert-true (risch::int-risch (integrate::int-norm '(- (* (exp x) (log (cos x))) (* (exp x) (tan x)))) 'x 0)))

(deftest "integrate: бюджет времени — call-with-time-limit и (timeout …) вместо зависания"
  (assert-equal '(timeout) (call-with-time-limit 0.2 (lambda () (letrec ((f (lambda (n) (f (+ n 1))))) (f 0)))))
  (assert-equal '(ok 5) (call-with-time-limit 5 (lambda () 5)))
  ; чужое исключение из thunk снимает бюджет: следующая работа не прерывается «залипшим» дедлайном
  (assert-equal 'caught (try (call-with-time-limit 0.01 (lambda () (error "сбой внутри бюджета")))
                             (lambda (er) 'caught)))
  (assert-equal 'ok (let loop ((i 0)) (if (< i 300000) (loop (+ i 1)) 'ok)))
  ; замечание ревью WASM.1): вложенный длинный бюджет не продлевает внешний короткий; короткий внутри длинного — свой
  (let ((t0 (clock-us))
        (r (call-with-time-limit 0.3 (lambda () (list 'inner (call-with-time-limit 30 (lambda () (letrec ((f (lambda (n) (f (+ n 1))))) (f 0)))))))))
    (assert-equal '(timeout) r)
    (assert-true (< (- (clock-us) t0) 5000000)))
  (assert-equal '(ok (inner (timeout)))
                (call-with-time-limit 30 (lambda () (list 'inner (call-with-time-limit 0.2 (lambda () (letrec ((f (lambda (n) (f (+ n 1))))) (f 0))))))))
  ; крошечный бюджет: невычисленная форма и условие timeout, не неверный ответ
  (let ((old integrate::int-time-limit)
        (E '(* (exp x) (sin x) (^ (cos (* 2 x)) 2))))
    (unwind-protect
        (begin
          (set! integrate::int-time-limit 0.02)
          (let ((A (integrate E 'x)))
            (assert-true (or (equal? (car A) 'integrate) (int-check A E 'x)))
            (if (equal? (car A) 'integrate)
                (assert-true (any? (lambda (c) (equal? (car (car c)) 'timeout)) (conditions))))))
      (set! integrate::int-time-limit old))))

(deftest "integrate: журнал попыток при исчерпании бюджета — причина и рамка предпроверки Риша (INT.UX)"
  (let ((old integrate::int-time-limit))
    (unwind-protect
        (begin
          (set! integrate::int-time-limit 1)
          (let* ((r (capture-attempts (lambda () (integrate '(/ (^ (sin x) 2) (+ (log (* 1/3 x)) (tan x))) 'x))))
                 (txt (attempts-text (cadr r) (caddr r))))
            (assert-true (string-contains? txt "превышен бюджет времени 1 с"))
            (assert-true (string-contains? txt "Предпроверка Риша"))))
      (set! integrate::int-time-limit old))))

(deftest "integrate: тригонометрические произведения со степенью берутся быстро (прежде — минуты по частям)"
  (let ((old integrate::int-time-limit))
    (unwind-protect
        (begin
          (set! integrate::int-time-limit 3)
          (for-each (lambda (E)
                      (let ((A (integrate E 'x)))
                        (assert-true (not (equal? (car A) 'integrate)))
                        (assert-true (int-check A E 'x))))
                    (list '(* (^ (sin x) 2) (cos (* 3 x)))
                          '(* (exp x) (sin x) (cos (* 2 x)))
                          '(* (^ (cos x) 2) (^ (sin (* 2 x)) 2))))
          (let ((A (integrate '(* t (exp (* -1 t)) (cos (* w t))) 't)))
            (assert-true (not (equal? (car A) 'integrate)))))
      (set! integrate::int-time-limit old))))

; ---------- R4.1: нуль констант в Рише ----------
(define rt-hz-denest '(+ (^ (+ 3 (* 2 (^ 2 1/2))) 1/2) -1 (* -1 (^ 2 1/2))))
(define rt-hz-log '(+ (log 6) (* -1 (log 2)) (* -1 (log 3))))

(deftest "r4/риш: rs-zero? — скрытые нули коэффициентов при x и θ"
  (assert-equal (rt-zero? rt-hz-denest) #t)
  (assert-equal (rt-zero? (list '* rt-hz-log 'x)) #t)
  (assert-equal (rt-zero? (list '+ (list '* rt-hz-log '%t1) (list '* rt-hz-denest 'x))) #t)
  (assert-equal (rt-zero? (list '+ (list '* rt-hz-log '%t1) 'x)) #f)
  (assert-equal (rt-zero? '(log 2)) #f)
  (assert-equal risch::rs-zero-unknown #f))

(deftest "r4/риш: rs-zero? — unknown не даёт #t, ставит флаг"
  (set! risch::rs-zero-unknown #f)
  (assert-equal (rt-zero? '(* x (+ (cos (/ pi 5)) (* -1 (/ (+ 1 (^ 5 1/2)) 4))))) #f)
  (assert-equal risch::rs-zero-unknown #t)
  (set! risch::rs-zero-unknown #f))

(deftest "r4/риш: скрытый нуль в подынтегральной функции — ответ 0, а не «неэлементарно»"
  (assert-equal (risch-integrate (list '* rt-hz-log '(exp (^ x 2))) 'x) 0)
  (assert-equal (risch-integrate (list '* rt-hz-denest '(exp (^ x 2))) 'x) 0))

(deftest "r4/риш: ((√(3+2√2) − 1 − √2)·e^{x²} + x) → x²/2"
  (assert-equal (risch-integrate (list '+ (list '* rt-hz-denest '(exp (^ x 2))) 'x) 'x) '(* 1/2 (^ x 2))))

(deftest "r4/риш: ненулевая константа при неэлементарном — остаток остаётся"
  (let ((r (risch-integrate '(+ (* (+ (log 6) 1) (exp (^ x 2))) x) 'x)))
    (assert-true (contains-sym? r 'integrate))
    (assert-true (contains-sym? r 'log))))

(deftest "r4/риш: коэффициент unknown — «не знаю», а не доказательство неэлементарности"
  (let ((E '(* (+ (cos (/ pi 5)) (* -1 (/ (+ 1 (^ 5 1/2)) 4))) (exp (^ x 2)))))
    (assert-equal (risch-integrate E 'x) #f)
    (assert-equal (risch-nonelementary? E 'x) 'unknown)
    (assert-equal risch::rs-zero-unknown #f))
  (assert-equal (risch-nonelementary? '(exp (^ x 2)) 'x) #t))

; ---------- R4.2: башня над константами ----------
(define (r42-levels e) (let ((r (car (capture-conditions (lambda () (risch::rs-build-tower e 'x)))))) (and r (length (risch::rs-levels (car r))))))

(deftest "r4.2/риш: e^(x + log 2) = 2·eˣ — один уровень, множитель 2"
  (assert-equal (r42-levels '(exp (+ x (log 2)))) 1)
  (assert-equal (risch-integrate '(exp (+ x (log 2))) 'x) '(* 2 (exp x)))
  (assert-equal (r42-levels '(+ (exp x) (exp (+ x (log 2))))) 1)
  (assert-equal (cadr (car (capture-conditions (lambda () (risch::rs-build-tower '(exp (+ x (* 2 (log 3)) (log 2))) 'x))))) '(* 18 %t1)))

(deftest "r4.2/риш: log(2x), log(4x) — один уровень (log x), константы log 2 вне башни"
  (assert-equal (r42-levels '(+ (log (* 2 x)) (log (* 4 x)))) 1))

(deftest "r4.2/риш: независимость exp(x) и exp(√2·x) (2 уровня), скрытое рациональное — зависимость"
  (assert-equal (r42-levels '(+ (exp x) (exp (* (^ 2 1/2) x)))) 2)
  (assert-equal (r42-levels '(+ (exp x) (exp (* (log 2) x)))) 2)
  (assert-equal (r42-levels '(+ (exp x) (exp (* (/ (log 6) (+ (log 2) (log 3))) x)))) 1)
  (assert-equal (risch-integrate '(exp (* (/ (log 6) (+ (log 2) (log 3))) x)) 'x) '(exp x)))

; ---------- INT.FIX1: экспонента от спрятанного логарифма и знак в аргументе ----------
(define (rfix1-log-neg-one? e)
  (or (and (pair? e) (equal? (car e) 'log) (equal? (cadr e) -1))
      (and (pair? e) (any? rfix1-log-neg-one? (cdr e)))))

(deftest "INT.FIX1/риш: exp(2i·atan(ax)) — не «неэлементарен» (в atan спрятан логарифм)"
  ; i·atan u = ½·log((1+iu)/(1−iu)): такая экспонента алгебраична, доказательство
  ; неэлементарности для неё недействительно
  (assert-equal (risch-nonelementary? '(* (exp (* 2 %i (atan (* a x))))) 'x) 'unknown)
  (assert-equal (risch-nonelementary? '(* x (exp (* -3 %i (atan (* a x))))) 'x) 'unknown))

(deftest "INT.FIX1/риш: exp(atanh(ax)) — тоже «не знаю», а не «неэлементарен»"
  (assert-equal (risch-nonelementary? '(exp (* 2 (atanh (* a x)))) 'x) 'unknown))

(deftest "INT.FIX1/риш: знак из аргумента логарифма не выносится в log(−1)"
  ; hebisch/44: log(2−x) должен остаться log(2−x); прежний ответ содержал
  ; log(−1)+log(−2+x) и был неверен при x < 2. Свёртка знака — в int-final.
  (let* ((e '(/ (+ (* (+ (* 8 (^ x 2)) (* -10 x) -12) (log (- 2 x))) (* -2 (^ x 3)) (* -6 (^ x 2)))
                 (* (+ (^ x 4) (^ x 3) (* -6 (^ x 2))) (log (- 2 x)))))
         (F (integrate e 'x)))
    (assert-true (pair? F))
    (assert-true (not (rfix1-log-neg-one? F)))
    (assert-true (int-check F e 'x))))

(deftest "INT.FIX1/риш: sech/csch от логарифма — «не знаю», а не «неэлементарен»"
  (assert-equal (risch-nonelementary? '(/ (sech (+ a (* b (log (* c (^ x n)))))) x) 'x) 'unknown)
  (assert-equal (risch-nonelementary? '(/ (csch (+ a (* b (log (* c (^ x n)))))) x) 'x) 'unknown))

; ---------- INT.FIX2.b: дубль уровня башни и ложное «неэлементарен» ----------
(define (rfix2-levels e)
  (let ((r (car (capture-conditions (lambda () (risch::rs-build-tower e 'x))))))
    (and r (cdr (car r)))))

(deftest "INT.FIX2.b/риш: exp(x·c) и exp(x·c+5) — один уровень, дубля нет"
  ; прежний rs-exp-relation при неединственном решении обнулял свободные неизвестные и получал
  ; нерациональные q, после чего уровень exp(x·e⁵) заводился второй раз (%t2 = %t3)
  (let ((L (rfix2-levels '(+ (exp x) (exp (+ 5 (* x (exp 5)))) (exp (* x (exp 5)))))))
    (assert-equal (length L) 2)
    (assert-equal (map (lambda (lv) (risch::rs-level-arg lv))
                       (filter (lambda (lv) (equal? (risch::rs-level-kind lv) 'exp)) L))
                  (list 'x '(* x (exp 5))))))

(deftest "INT.FIX2.b/риш: hebisch/8291 — первообразная логарифма, а не «неэлементарен»"
  (let* ((e '(/ (- (* (exp 5) (exp (* x (exp 5)))) (exp x) 1)
                 (+ (- (exp (* x (exp 5))) (exp x) x) 6)))
         (F (integrate e 'x)))
    (assert-equal (risch-nonelementary? e 'x) #f)
    (assert-true (int-check F e 'x))))

(deftest "INT.FIX2.b/риш: hebisch/6763 — «не знаю» или ответ, но не «неэлементарен»"
  (let ((e '(/ (+ (* (+ (* -2 (^ x 3) (exp 4)) (* 2 (^ x 3) (exp 1)) (^ x 3) (* -1 (^ x 2)))
                     (exp x) (^ (exp (- (* x (exp 4)) (* x (exp 1)))) 2))
                  (* (+ (* 3 x) 3) (exp x)))
               (+ (* (^ x 4) (^ (exp (- (* x (exp 4)) (* x (exp 1)))) 4))
                  (* 6 (^ x 2) (^ (exp (- (* x (exp 4)) (* x (exp 1)))) 2))
                  9))))
    (assert-true (not (equal? (risch-nonelementary? e 'x) #t)))))

(deftest "INT.FIX2.b/риш: производные log(рациональная от exp(c·x)) — не «неэлементарны»"
  ; 10 задач того же вида: c — трансцендентная константа (e, e², e⁴, e⁵), знаменатель логарифма —
  ; рациональная функция от x и exp(c·x); интеграл строится как производная log(D)
  (let ((D '((+ (exp (* x (exp 5))) (* -1 (exp x)) (* -1 x) 6)
             (+ (* 2 (exp (* 2 x (exp 1)))) (* -1 (exp x)) 7)
             (- (+ (exp (* x (exp 3))) (^ x 2)) (* 3 (exp (* 2 x))))
             (+ (* x (exp (* x (exp 2)))) (exp x) 5)
             (- (+ (exp (+ (* x (exp 4)) 1)) (^ x 3)) (exp (* 2 x)))
             (+ (^ (exp (* x (exp 1)))) 2 (* x (^ (exp (* x (exp 1)))) 3))
             (- (exp (* 2 x (exp 4))) (* x (exp x)) 11)
             (+ (* 2 (^ x 2) (exp (* x (exp 5)))) (exp (* 3 x)) 1)
             (+ (exp (* x (- (exp 4) (exp 1)))) (* -1 (exp x)) (* 2 x) 8)
             (+ (* x (exp x)) (exp (* x (exp 3))) (* -1 (^ x 2)) 4))))
    (for-each
     (lambda (d)
       (let* ((G (list 'log d)) (f (simplify (diff 'x G))))
         (assert-true (not (equal? (risch-nonelementary? f 'x) #t)))))
     D)))

(deftest "INT.FIX2.b/риш: производная log(D) интегрируется обратно в log(D)"
  (for-each
   (lambda (d)
     (let* ((G (list 'log d)) (f (simplify (diff 'x G))) (F (integrate f 'x)))
       (assert-true (int-check F f 'x))))
   '((+ (exp (* x (exp 5))) (* -1 (exp x)) (* -1 x) 6)
     (+ (* 2 (exp (* 2 x (exp 1)))) (* -1 (exp x)) 7)
     (+ (^ (exp (* x (exp 1)))) 2 (* x (^ (exp (* x (exp 1)))) 3))
     (- (exp (* 2 x (exp 4))) (* x (exp x)) 11))))



; ---------- INT.FIX2.d: знак аргумента-многочлена у логарифма ----------

(deftest "INT.FIX2.d/риш: log(2−x) — знак остаётся в аргументе, в башне нет log(−1)"
  ; прежний вид: log(−1) + log(−2+x) с коэффициентом от x — такой член свёртка не убирает
  (let ((tw0 (capture-conditions (lambda () (risch::rs-build-tower '(log (- 2 x)) 'x)))))
    (assert-true (not (rfix1-log-neg-one? (car tw0)))))
  (let* ((e '(/ -1 (- 2 x))) (F (integrate e 'x)))
    (assert-true (not (rfix1-log-neg-one? F)))
    (assert-true (int-check F e 'x))))

; ---------- INT.FIX3.c: гейт rs-hyp-log? — только степень −1 (sech/csch) ----------

(deftest "INT.FIX3.c/риш: степени sinh и cosh от логарифма снова интегрируются"
  ; INT.FIX1 исключал из Риша ЛЮБУЮ степень sinh/cosh с логарифмом внутри (гейт ставился для
  ; sech/csch = степень −1), из-за чего 8 задач rubi t_6_1_5/t_6_2_5 отвечали «не знаю»
  (for-each
   (lambda (e)
     (let ((F (integrate e 'x)))
       (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))
       (let* ((sub (lambda (v) (replace-expr (replace-expr (replace-expr (replace-expr v 'a 1) 'b 3) 'c 2) 'n 1)))
              (F1 (sub F)) (f1 (sub e)))
         (assert-true (int-check F1 f1 'x)))))
   '((^ (sinh (+ a (* b (log (* c (^ x n)))))) 2)
     (^ (cosh (+ a (* b (log (* c (^ x n)))))) 4))))

(deftest "INT.FIX3.c/риш: sech/csch от логарифма — не «неэлементарен», ответ есть"
  ; гейт для степени −1 остаётся: ложного доказательства неэлементарности нет, но и ответ даётся
  (for-each
   (lambda (e)
     (assert-true (not (equal? (risch-nonelementary? e 'x) #t)))
     (let ((F (integrate e 'x)))
       (assert-true (not (and (pair? F) (equal? (car F) 'integrate))))))
   '((* (/ 1 x) (^ (cosh (+ a (* b (log (* c (^ x n)))))) -1))
     (* (/ 1 x) (^ (sinh (+ a (* b (log (* c (^ x n)))))) -1)))))
