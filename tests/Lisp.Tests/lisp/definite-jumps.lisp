; definite-jumps.lisp — шаг INT.DEF2: первообразная с разрывом внутри отрезка (скачок atan), односторонние пределы на конце,
; 1/(a·sin x + b·cos x + c) с иррациональным √(a²+b²−c²). Эталон — квадратура Гаусса–Лежандра по частям (панель 0,05, ≥ 10 знаков).

(define (dj-q f lo hi)
  (definite::di-quad (lambda (t) (eval-num (subst (list 'x t) f))) lo hi 0.05))

; квадратура по точкам разбиения (в точках скачка подынтегральной функции)
(define (dj-qs f pts)
  (if (null? (cdr pts)) 0.0 (+ (dj-q f (car pts) (cadr pts)) (dj-qs f (cdr pts)))))

(define (dj-I f a b) (integrate f 'x a b))
(define (dj-ok? v ref) (and (not (contains-sym? v 'integrate)) (< (abs (- (eval-num v) ref)) 1e-9)))
(define (dj-unevaluated? v) (and (pair? v) (equal? (car v) 'integrate)))

; ложное значение (верное число отличается от ответа) — недопустимо; допустимо только неверифицированное «не вычислено»
(define dj-s3 0.5773502691896258)
(define dj-atan3 '(atan (/ (- (* 3 x) (^ x 3)) (- 1 (* 3 (^ x 2))))))

(deftest "скачок первообразной: atan((3x−x³)/(1−3x²)) на [0,1] = π/√3 − π/4 − (3/2)·log 2"
  (let ((v (dj-I dj-atan3 0 1)))
    (assert-true (dj-ok? v (dj-qs dj-atan3 (list 0.0 dj-s3 1.0))))
    (assert-true (dj-ok? v (eval-num '(- (/ pi (sqrt 3)) (+ (/ pi 4) (* 3/2 (log 2)))))))
    ; не ответ без скачка (−π/4 − (3/2) log 2) и не −(3/2) log 4
    (assert-true (not (< (abs (- (eval-num v) (eval-num '(- (- (/ pi 4)) (* 3/2 (log 2)))))) 1e-6)))))

(deftest "скачок первообразной: atan((3x−x³)/(1−3x²)) на [0,2] и [0.7,3]"
  (assert-true (dj-ok? (dj-I dj-atan3 0 2) (dj-qs dj-atan3 (list 0.0 dj-s3 2.0))))
  (assert-true (dj-ok? (dj-I dj-atan3 7/10 3) (dj-qs dj-atan3 (list 0.7 3.0)))))

(deftest "скачок первообразной: нечётная atan((3x−x³)/(1−3x²)) на [−1,1] — два скачка, ответ 0 верен"
  (let ((v (dj-I dj-atan3 -1 1)))
    (assert-true (dj-ok? v (dj-qs dj-atan3 (list -1.0 (- dj-s3) dj-s3 1.0))))))

(deftest "скачок первообразной: atan(2x/(1−x²)) = 2·atan x − π·H(x−1) на [0,3] и [0,1/2]"
  (let ((f '(atan (/ (* 2 x) (- 1 (^ x 2))))))
    (assert-true (dj-ok? (dj-I f 0 3) (dj-qs f (list 0.0 1.0 3.0))))
    (assert-true (dj-ok? (dj-I f 0 1/2) (dj-qs f (list 0.0 0.5))))
    (assert-true (dj-ok? (dj-I f 2 5) (dj-qs f (list 2.0 5.0))))))

(deftest "скачок первообразной: atan(tan 2x) на [0,1] и [0,2] (скачок в π/4)"
  (let ((f '(atan (tan (* 2 x)))) (p4 (/ (eval-num 'pi) 4.0)))
    (assert-true (dj-ok? (dj-I f 0 1) (dj-qs f (list 0.0 p4 1.0))))
    (assert-true (dj-ok? (dj-I f 0 2) (dj-qs f (list 0.0 p4 2.0))))))

(deftest "первообразная atan(…/(1+tan(x/2))) разрывна в π: 1/(2+sin x+cos x) на [0,4]"
  (let ((f '(/ 1 (+ 2 (sin x) (cos x)))))
    (assert-true (dj-ok? (dj-I f 0 4) (dj-q f 0.0 4.0)))
    (assert-true (dj-ok? (dj-I f 1 7) (dj-q f 1.0 7.0)))))

(deftest "односторонний предел на конце: ∫₀¹ √x/(1+x) = 2 − π/2, без деления на нуль"
  (let ((v (dj-I '(/ (sqrt x) (+ 1 x)) 0 1)))
    (assert-true (dj-ok? v (dj-q '(* 2 (/ (^ x 2) (+ 1 (^ x 2)))) 0.0 1.0)))   ; x = u²: 2u²/(1+u²)
    (assert-true (< (abs (- (eval-num v) (- 2.0 (/ (eval-num 'pi) 2.0)))) 1e-12))
    (assert-true (not (contains-sym? v 'integrate)))
    (assert-true (not (contains-sym? v 'atan)))))

(deftest "односторонний предел на конце: √x/(1+x), x^(3/2)/(1+x), √x/(4+x) на отрезках с 0"
  (assert-true (dj-ok? (dj-I '(/ (sqrt x) (+ 1 x)) 0 4) (dj-q '(* 2 (/ (^ x 2) (+ 1 (^ x 2)))) 0.0 2.0)))
  (assert-true (dj-ok? (dj-I '(/ (^ x 3/2) (+ 1 x)) 0 1) (dj-q '(* 2 (/ (^ x 4) (+ 1 (^ x 2)))) 0.0 1.0)))
  (assert-true (dj-ok? (dj-I '(/ (sqrt x) (+ 4 x)) 0 1) (dj-q '(* 2 (/ (^ x 2) (+ 4 (^ x 2)))) 0.0 1.0)))
  (assert-true (dj-ok? (dj-I '(/ 1 (* (sqrt x) (+ 1 x))) 0 1) (dj-q '(/ 2 (+ 1 (^ x 2))) 0.0 1.0))))

(deftest "односторонний предел: atan(x^(−1/2)) при x → 0+ равен π/2"
  (assert-equal (limit '(atan (^ x -1/2)) 'x 0 'plus) '(* 1/2 pi))
  (assert-equal (limit '(^ x -3/2) 'x 0 'plus) 'inf)
  (assert-equal (limit '(^ (* -1 x) -1/2) 'x 0 'minus) 'inf))

; производная найденной первообразной совпадает с подынтегральной в нескольких точках
(define (dj-anti-ok? f pts)
  (let* ((F (integrate f 'x)))
    (and (not (contains-sym? F 'integrate))
         (every? (lambda (p)
                   (let ((d (eval-num (subst (list 'x p) (diff 'x F)))) (g (eval-num (subst (list 'x p) f))))
                     (< (abs (- d g)) 1e-9)))
                 pts))))

(deftest "1/(sin x + cos x) и 1/(a·sin x + b·cos x): первообразная найдена, производная верна"
  (assert-true (dj-anti-ok? '(/ 1 (+ (sin x) (cos x))) '(0.1 0.5 1.0 2.0 4.0)))
  (assert-true (dj-anti-ok? '(/ 1 (+ (sin x) (* 2 (cos x)))) '(0.1 0.5 1.0 2.0 4.0)))
  (assert-true (dj-anti-ok? '(/ 1 (+ (* 2 (sin x)) (* 3 (cos x)))) '(0.1 0.5 1.0 1.5)))
  (assert-true (dj-anti-ok? '(/ 3 (+ (* 3 (sin x)) (* -1 (cos x)))) '(0.5 1.0 1.5 2.0))))

(deftest "1/(a·sin u + b·cos u + c), u линейно, √(a²+b²−c²) иррационален"
  (assert-true (dj-anti-ok? '(/ 1 (+ (sin x) (cos x) 1/2)) '(0.1 0.5 1.0 2.0 4.0)))
  (assert-true (dj-anti-ok? '(/ 1 (+ (* 2 (sin x)) (cos x) 1/3)) '(0.1 0.5 1.0 2.0)))
  (assert-true (dj-anti-ok? '(/ 1 (+ (sin (+ (* 2 x) 1)) (cos (+ (* 2 x) 1)))) '(0.1 0.3 0.6 1.0))))

(deftest "определённый: 1/(sin x + cos x) на [0,1] и 1/(2sin x + 3cos x) на [0,2] — по квадратуре"
  (let ((f1 '(/ 1 (+ (sin x) (cos x)))) (f2 '(/ 1 (+ (* 2 (sin x)) (* 3 (cos x))))))
    (assert-true (dj-ok? (dj-I f1 0 1) (dj-q f1 0.0 1.0)))
    (assert-true (dj-ok? (dj-I f1 1/2 2) (dj-q f1 0.5 2.0)))
    (assert-true (dj-ok? (dj-I f2 0 2) (dj-q f2 0.0 2.0)))))

(deftest "полюс подынтегральной внутри отрезка: 1/(sin x + cos x) на [0,3] — не значение"
  (assert-true (dj-unevaluated? (dj-I '(/ 1 (+ (sin x) (cos x))) 0 3))))

; INT.DEF3: тригонометрические интегралы с разрывами первообразной (atan от tan(x/2)) — верное число либо отказ, не ложь
(define (dj-ok-or-uneval? v ref) (or (dj-unevaluated? v) (dj-ok? v ref)))

(deftest "1/(sin⁴+cos⁴) на [0,2π] = 2√2π (регрессия: был 0)"
  (let ((f '(/ 1 (+ (^ (sin x) 4) (^ (cos x) 4)))))
    (assert-true (dj-ok? (dj-I f 0 '(* 2 pi)) (* 2 (sqrt 2.0) 3.141592653589793)))
    (assert-true (dj-ok? (dj-I f 0 '(* 1/2 pi)) (dj-q f 0.0 1.5707963267948966)))
    (assert-true (dj-ok? (dj-I f '(* -1 pi) 'pi) (* 2 (sqrt 2.0) 3.141592653589793)))
    (assert-true (dj-ok-or-uneval? (dj-I f 0 'pi) (dj-q f 0.0 3.141592653589793)))))

(deftest "1/(1+sin²), 1/(1+cos²), sin²/(1+cos²) на [0,π]: не 0 и не −π (были ложными)"
  (let ((f1 '(/ 1 (+ 1 (^ (sin x) 2)))) (f2 '(/ 1 (+ 1 (^ (cos x) 2)))) (f3 '(/ (^ (sin x) 2) (+ 1 (^ (cos x) 2)))))
    (assert-true (dj-ok-or-uneval? (dj-I f1 0 'pi) (dj-q f1 0.0 3.141592653589793)))
    (assert-true (dj-ok-or-uneval? (dj-I f2 0 'pi) (dj-q f2 0.0 3.141592653589793)))
    (assert-true (dj-ok-or-uneval? (dj-I f3 0 'pi) (dj-q f3 0.0 3.141592653589793)))))

(deftest "1/(sin⁶+cos⁶) на [0,2π], [0,π], [0,π/2]: верно или отказ"
  (let ((f '(/ 1 (+ (^ (sin x) 6) (^ (cos x) 6)))))
    (assert-true (dj-ok-or-uneval? (dj-I f 0 '(* 2 pi)) (dj-q f 0.0 6.283185307179586)))
    (assert-true (dj-ok-or-uneval? (dj-I f 0 'pi) (dj-q f 0.0 3.141592653589793)))
    (assert-true (dj-ok-or-uneval? (dj-I f 0 '(* 1/2 pi)) (dj-q f 0.0 1.5707963267948966)))))
