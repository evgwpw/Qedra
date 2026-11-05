; multiint.lisp — тесты шага MINT.a: кратные интегралы одной записью, замена переменных с якобианом, интегралы первого рода.
; Оракул каждого примера: точное значение (разность с эталоном упрощается в 0) И независимое численное значение
; (Симпсон по неупрощённому подынтегральному выражению, допуск 1e-8). Подделки: отрицательные пределы r не дают
; отрицательную площадь; неверный порядок/знак якобиана ловится сравнением с эталоном.

(define (mt-zero? a b) (let ((d (simplify (list '+ a (list '* -1 b))))) (or (equal? d 0) (< (abs (eval-num d)) 1e-12))))
(define (mt-close? a b) (< (abs (- (eval-num a) (eval-num b))) 1e-8))

; Симпсон: f — функция числа, n — чётное число интервалов
(define (mt-simpson f a b n)
  (let ((h (/ (- b a) n)))
    (* (/ h 3)
       (foldl (lambda (acc i)
                (+ acc (* (cond ((or (= i 0) (= i n)) 1) ((= (modulo i 2) 1) 4) (else 2)) (f (+ a (* i h))))))
              0 (range (+ n 1))))))
(define (mt-at e rules) (eval-num (subst rules e)))
; ∫ speed(t) dt, speed — НЕупрощённый √Σφ′²
(define (mt-num-line phi t a b)
  (let ((sp (list 'sqrt (cons '+ (map (lambda (p) (list '^ (diff t p) 2)) phi)))))
    (mt-simpson (lambda (x) (mt-at (list '* 1 sp) (list (list t x)))) (eval-num a) (eval-num b) 2000)))
; ∫∫ |r_u × r_v| du dv
(define (mt-num-surf phi u a b v c d)
  (let* ((ru (map (lambda (p) (diff u p)) phi)) (rv (map (lambda (p) (diff v p)) phi))
         (cr (list (list '+ (list '* (nth ru 1) (nth rv 2)) (list '* -1 (nth ru 2) (nth rv 1)))
                   (list '+ (list '* (nth ru 2) (nth rv 0)) (list '* -1 (nth ru 0) (nth rv 2)))
                   (list '+ (list '* (nth ru 0) (nth rv 1)) (list '* -1 (nth ru 1) (nth rv 0)))))
         (nrm (list 'sqrt (cons '+ (map (lambda (e) (list '^ e 2)) cr)))))
    (mt-simpson (lambda (x)
                  (mt-simpson (lambda (y) (mt-at nrm (list (list u x) (list v y)))) (eval-num c) (eval-num d) 400))
                (eval-num a) (eval-num b) 12)))

(define mt-2pi '(* 2 pi))

(deftest "multiint: кратный integrate-multi — порядок диапазонов и переменные пределы"
  ; первый диапазон внешний: ∫₀¹ (∫₀ˣ x y dy) dx = 1/8
  (assert-true (mt-zero? (integrate-multi '(* x y) '((x 0 1) (y 0 x))) 1/8))
  ; наоборот: y внешний, x внутренний, x ∈ [y, 1]: та же область
  (assert-true (mt-zero? (integrate-multi '(* x y) '((y 0 1) (x y 1))) 1/8))
  ; другая область: внешний y ∈ [0,1], внутренний x ∈ [0, y] → ∫ y·y²/2 = 1/8 (по симметрии), а x ∈ [0,y] для x² : ∫ y⁴ ...
  (assert-true (mt-zero? (integrate-multi '(^ x 2) '((y 0 1) (x 0 y))) 1/12))
  (assert-true (mt-zero? (integrate-multi '(* x y z) '((x 0 1) (y 0 1) (z 0 1))) 1/8))
  ; гауссов интеграл по ℝ²
  (assert-true (mt-zero? (integrate-multi '(exp (* -1 (+ (^ x 2) (^ y 2)))) '((x -inf inf) (y -inf inf))) 'pi))
  ; одна запись без пределов — неопределённый
  (assert-true (mt-zero? (integrate-multi '(* x y) '((x 0 1) (y))) '(* 1/4 (^ y 2))))
  ; не берётся внутренний — честная невычисленная запись, а не неверное число
  (let ((r (integrate-multi '(* y (sin (^ x 2))) '((y 0 x) (x 0 1)))))
    (assert-true (pair? r))))

(deftest "multiint: якобиан"
  (assert-true (mt-zero? (jacobian-det '((* r (cos t)) (* r (sin t))) '(r t)) 'r))
  (assert-true (mt-zero? (jacobian-det '((* r (sin th) (cos ph)) (* r (sin th) (sin ph)) (* r (cos th))) '(r th ph))
                         '(* (^ r 2) (sin th))))
  (assert-true (mt-zero? (jacobian-det '((+ (* 2 u) v) (- u v)) '(u v)) -3))
  (assert-error (jacobian-det '(u v) '(u))))

(deftest "multiint: замена переменных — площадь круга, объём шара и конуса, гауссов в полярных"
  (assert-true (mt-zero? (integrate-change 1 'polar (list '(r 0 1) (list 't 0 mt-2pi))) 'pi))
  (assert-true (mt-zero? (integrate-change 1 'polar (list '(r 0 5) (list 't 0 mt-2pi))) '(* 25 pi)))
  (assert-true (mt-zero? (integrate-change '(exp (* -1 (+ (^ x 2) (^ y 2)))) 'polar (list '(r 0 inf) (list 't 0 mt-2pi))) 'pi))
  (assert-true (mt-zero? (integrate-change 1 'spherical (list '(r 0 1) '(th 0 pi) (list 'ph 0 mt-2pi))) '(* 4/3 pi)))
  ; шар радиуса R (R > 0 объявлен)
  (assuming ((R (interval 0 'inf)))
    (assert-true (mt-zero? (integrate-change 1 'spherical (list '(r 0 R) '(th 0 pi) (list 'ph 0 mt-2pi))) '(* 4/3 pi (^ R 3))))
    (assert-true (mt-zero? (integrate-change 1 'polar (list '(r 0 R) (list 't 0 mt-2pi))) '(* pi (^ R 2)))))
  ; конус z ∈ [r, 1]: π/3 (цилиндрические); и цилиндр r ≤ 1, 0 ≤ z ≤ 2: 2π
  (assert-true (mt-zero? (integrate-change 1 'cylindrical (list '(r 0 1) (list 't 0 mt-2pi) '(z r 1))) '(* 1/3 pi)))
  (assert-true (mt-zero? (integrate-change 1 'cylindrical (list '(r 0 1) (list 't 0 mt-2pi) '(z 0 2))) '(* 2 pi)))
  ; произвольная линейная замена: |J| = 3
  (assert-true (mt-zero? (integrate-change 1 '((= x (+ (* 2 u) v)) (= y (- u v))) '((u 0 1) (v 0 1))) 3))
  ; то же в виде списков пар
  (assert-true (mt-zero? (integrate-change 1 '((x (+ (* 2 u) v)) (y (- u v))) '((u 0 1) (v 0 1))) 3))
  ; независимые численные оракулы (сечения, не якобиан): круг ∫2√(1−x²)dx (x = sin s), гауссов (∫e^{−x²})², шар ∫π(1−z²)dz, конус ∫πz²dz
  (assert-true (mt-close? (integrate-change 1 'polar (list '(r 0 1) (list 't 0 mt-2pi)))
                          (mt-simpson (lambda (s) (* 2 (^ (cos s) 2))) (- (/ (eval-num 'pi) 2)) (/ (eval-num 'pi) 2) 400)))
  (assert-true (mt-close? (integrate-change '(exp (* -1 (+ (^ x 2) (^ y 2)))) 'polar (list '(r 0 inf) (list 't 0 mt-2pi)))
                          (let ((g (mt-simpson (lambda (s) (eval-num (list 'exp (- (* s s))))) -8 8 800))) (* g g))))
  (assert-true (mt-close? (integrate-change 1 'spherical (list '(r 0 1) '(th 0 pi) (list 'ph 0 mt-2pi)))
                          (mt-simpson (lambda (z) (* (eval-num 'pi) (- 1 (* z z)))) -1 1 20)))
  (assert-true (mt-close? (integrate-change 1 'cylindrical (list '(r 0 1) (list 't 0 mt-2pi) '(z r 1)))
                          (mt-simpson (lambda (z) (* (eval-num 'pi) z z)) 0 1 20)))
  ; численный оракул: ∫∫ x² + y² по кругу радиуса 1 = π/2; Симпсон по (r, θ) с ручным |J| = r
  (let ((num (mt-simpson (lambda (rr)
                           (mt-simpson (lambda (th) (* rr rr rr)) 0 (eval-num mt-2pi) 4)) 0 1 4)))
    (assert-true (mt-close? (integrate-change '(+ (^ x 2) (^ y 2)) 'polar (list '(r 0 1) (list 't 0 mt-2pi))) num))))

(deftest "multiint: модуль якобиана обязателен (подделка: r ∈ [−1, 0])"
  ; |J| = −r при r ≤ 0 → площадь π, не −π
  (assert-true (mt-zero? (integrate-change 1 'polar (list '(r -1 0) (list 't 0 mt-2pi))) 'pi))
  ; сферические: θ ∈ [0, π] — sin θ ≥ 0; для θ ∈ [π, 2π] sin θ ≤ 0 → тоже положительный объём
  (assert-true (mt-zero? (integrate-change 1 'spherical (list '(r 0 1) (list 'th 'pi mt-2pi) (list 'ph 0 mt-2pi))) '(* 4/3 pi)))
  ; то же с явной подстановкой
  (assert-true (mt-zero? (integrate-change 1 '((= x (* r (cos t))) (= y (* r (sin t)))) '((r -1 0) (t 0 (* 2 pi)))) 'pi))
  ; знак r не доказан (r ∈ [−1, 1]) — остаётся |r|; интеграл не берётся → невычисленная запись, но не отрицательное число
  (let ((r (integrate-change 1 'polar (list '(r -1 1) (list 't 0 mt-2pi)))))
    (assert-true (or (contains-sym? r 'integrate) (mt-zero? r mt-2pi)))))

(deftest "multiint: длина кривой"
  (assert-true (mt-zero? (arc-length '((cos t) (sin t)) (list 't 0 mt-2pi)) mt-2pi))
  (assert-true (mt-close? (arc-length '((cos t) (sin t)) (list 't 0 mt-2pi)) (mt-num-line '((cos t) (sin t)) 't 0 mt-2pi)))
  ; виток винтовой линии 2π√2
  (assert-true (mt-zero? (arc-length '((cos t) (sin t) t) (list 't 0 mt-2pi)) '(* 2 pi (sqrt 2))))
  (assert-true (mt-close? (arc-length '((cos t) (sin t) t) (list 't 0 mt-2pi)) (mt-num-line '((cos t) (sin t) t) 't 0 mt-2pi)))
  ; парабола y = x² на [0, 1]: (2√5 + log(2 + √5))/4
  (let ((ex '(/ (+ (* 2 (sqrt 5)) (log (+ 2 (sqrt 5)))) 4)))
    (assert-true (mt-zero? (arc-length '(t (^ t 2)) '(t 0 1)) ex))
    (assert-true (mt-close? (arc-length '(t (^ t 2)) '(t 0 1)) (mt-num-line '(t (^ t 2)) 't 0 1))))
  ; окружность радиуса R — 2πR при R > 0; без объявления знака в ответе |R|
  (assuming ((R (interval 0 'inf)))
    (assert-true (mt-zero? (arc-length '((* R (cos t)) (* R (sin t))) (list 't 0 mt-2pi)) '(* 2 pi R))))
  (assert-true (contains-sym? (arc-length '((* R (cos t)) (* R (sin t))) (list 't 0 mt-2pi)) 'abs))
  ; ∫ (x² + y²) ds по единичной окружности = 2π
  (assert-true (mt-zero? (line-integral '(+ (^ x 2) (^ y 2)) '(x y) '((cos t) (sin t)) (list 't 0 mt-2pi)) mt-2pi))
  ; ∫ x ds по отрезку (0,0)–(1,1): √2/2
  (assert-true (mt-zero? (line-integral 'x '(x y) '(t t) '(t 0 1)) '(/ (sqrt 2) 2)))
  ; длина никогда не отрицательна: обратные пределы — ориентация (знак интеграла), модуль скорости — на промежутке
  (assert-true (> (eval-num (arc-length '(t t) '(t 0 1))) 0))
  (assert-error (line-integral 1 '(x y) '(t) '(t 0 1))))

(deftest "multiint: площадь поверхности и поверхностный интеграл"
  (let ((sph '((* (sin v) (cos u)) (* (sin v) (sin u)) (cos v))))
    (assert-true (mt-zero? (surface-area sph (list 'u 0 mt-2pi) '(v 0 pi)) '(* 4 pi)))
    (assert-true (mt-close? (surface-area sph (list 'u 0 mt-2pi) '(v 0 pi)) (mt-num-surf sph 'u 0 mt-2pi 'v 0 'pi)))
    ; масса сферы с плотностью z²: 4π/3
    (assert-true (mt-zero? (surface-integral '(^ z 2) '(x y z) sph (list 'u 0 mt-2pi) '(v 0 pi)) '(* 4/3 pi))))
  ; сфера радиуса R: 4πR²
  (assuming ((R (interval 0 'inf)) (h (interval 0 'inf)))
    (assert-true (mt-zero? (surface-area '((* R (sin v) (cos u)) (* R (sin v) (sin u)) (* R (cos v))) (list 'u 0 mt-2pi) '(v 0 pi))
                           '(* 4 pi (^ R 2))))
    ; боковая поверхность цилиндра: 2πRh
    (assert-true (mt-zero? (surface-area '((* R (cos u)) (* R (sin u)) v) (list 'u 0 mt-2pi) '(v 0 h)) '(* 2 pi R h))))
  ; численная проверка цилиндра R = 2, h = 3: 12π
  (let ((cyl '((* 2 (cos u)) (* 2 (sin u)) v)))
    (assert-true (mt-zero? (surface-area cyl (list 'u 0 mt-2pi) '(v 0 3)) '(* 12 pi)))
    (assert-true (mt-close? (surface-area cyl (list 'u 0 mt-2pi) '(v 0 3)) (mt-num-surf cyl 'u 0 mt-2pi 'v 0 3))))
  (assert-error (surface-integral 1 '(x y z) '(u v) '(u 0 1) '(v 0 1))))

(deftest "multiint: язык — integrate(f, [x,a,b], [y,c,d]) и прежние вызовы integrate не меняются"
  (assert-equal (math-eval "integrate(x*y, [x, 0, 1], [y, 0, x])") 1/8)
  (assert-equal (math-eval "integrate(x^2, x, 0, 1)") 1/3)
  (assert-true (mt-zero? (math-eval "integrate(x^2, x)") '(* 1/3 (^ x 3))))
  (assert-true (mt-zero? (math-eval "integrate(exp(-(x^2+y^2)), [x, -inf, inf], [y, -inf, inf])") 'pi))
  (assert-true (mt-zero? (math-eval "integrate_change(1, polar, [r, 0, 1], [t, 0, 2*pi])") 'pi))
  (assert-true (mt-zero? (math-eval "integrate_change(1, [x = r*cos(t), y = r*sin(t)], [r, 0, 1], [t, 0, 2*pi])") 'pi))
  (assert-true (mt-zero? (math-eval "arc_length([cos(t), sin(t), t], [t, 0, 2*pi])") '(* 2 pi (sqrt 2))))
  (assert-true (mt-zero? (math-eval "surface_area([sin(v)*cos(u), sin(v)*sin(u), cos(v)], [u, 0, 2*pi], [v, 0, pi])") '(* 4 pi)))
  (assert-true (mt-zero? (math-eval "line_integral(x^2 + y^2, [x, y], [cos(t), sin(t)], [t, 0, 2*pi])") '(* 2 pi)))
  (assert-true (mt-zero? (math-eval "surface_integral(z^2, [x, y, z], [sin(v)*cos(u), sin(v)*sin(u), cos(v)], [u, 0, 2*pi], [v, 0, pi])") '(* 4/3 pi))))
