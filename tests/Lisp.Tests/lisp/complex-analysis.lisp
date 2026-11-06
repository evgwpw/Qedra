; complex-analysis.lisp — тесты шага CA: ТФКП как инструменты (lib/complex-analysis.lisp).
; Оракулы (общеизвестные): Res_{z=i} 1/(z²+1) = −i/2; Res_0 eˣ/z³ = 1/2; sin z / z — устранимая особенность;
; e^{1/z} — существенная, вычет 1; 1/(z(z−1)²): вычеты 1 в 0 и −1 в 1 (сумма с вычетом на ∞ равна 0); cot z в 0 — полюс 1, вычет 1;
; ∮_{|z|=2} 1/(z²+1) = 0; ∮_{|z|=1/2} 1/(z(z−1)) = −2πi; ∫_ℝ 1/(x²+1) dx = π, ∫_ℝ 1/(x²+1)² dx = π/2.
; Независимо: численный круг (residue-check, contour-integral-check), `integrate` для вещественных интегралов,
; сумма всех вычетов (с ∞) рациональной функции равна нулю; подделки — неверный вычет/интеграл даёт mismatch.

(define cat-f1 '(/ 1 (+ (^ z 2) 1)))
(define cat-f2 '(/ 1 (* z (^ (- z 1) 2))))
(define (cat-near? a b tol) (< (abs (- a b)) tol))

; ---------- вычеты ----------

(deftest "ca: вычет 1/(z^2+1) в ±i"
  (assert-equal (residue cat-f1 'z '%i) '(* -1/2 %i))
  (assert-equal (residue cat-f1 'z '(* -1 %i)) '(* 1/2 %i))
  (assert-equal (residue cat-f1 'z 5) 0))

(deftest "ca: вычет e^z/z^3 в 0 равен 1/2"
  (assert-equal (residue '(/ (exp z) (^ z 3)) 'z 0) 1/2))

(deftest "ca: вычет 1/(z(z-1)^2): 1 в нуле, -1 в единице"
  (assert-equal (residue cat-f2 'z 0) 1)
  (assert-equal (residue cat-f2 'z 1) -1)
  (assert-equal (residue cat-f2 'z 'inf) 0))

(deftest "ca: cot z в нуле — полюс 1, вычет 1; вычеты в kπ"
  (assert-equal (singularity-type '(cot z) 'z 0) '(pole 1))
  (assert-equal (residue '(cot z) 'z 0) 1)
  (assert-equal (residue '(cot z) 'z 'pi) 1))

(deftest "ca: полюс высокого порядка и кратная точка в комплексной плоскости"
  (assert-equal (singularity-type '(/ 1 (^ (+ z %i) 3)) 'z '(* -1 %i)) '(pole 3))
  (assert-equal (residue '(/ (exp z) (^ (- z 1) 3)) 'z 1) (simplify '(/ (exp 1) 2)))
  (assert-equal (residue '(/ 1 (+ (^ z 2) (* 2 z) 5)) 'z '(+ -1 (* 2 %i))) '(* -1/4 %i)))

(deftest "ca: сумма вычетов рациональной функции вместе с ∞ равна нулю"
  (let* ((f '(/ (+ z 1) (* (^ z 2) (- z 2))))
         (s (+ (residue f 'z 0) (residue f 'z 2) (residue f 'z 'inf))))
    (assert-equal (simplify s) 0))
  (assert-equal (residue '(/ 1 z) 'z 'inf) -1)
  (assert-equal (residue 'z 'z 'inf) 0)
  ; z²/(z+1) = z − 1 + 1/z − …: c₋₁ = 1, Res_∞ = −1
  (assert-equal (residue '(/ (^ z 2) (+ z 1)) 'z 'inf) -1))

(deftest "ca: вычет в существенной особенности — точные формулы"
  (assert-equal (residue '(exp (/ 1 z)) 'z 0) 1)
  (assert-equal (residue '(* (^ z 2) (exp (/ 1 z))) 'z 0) 1/6)
  (assert-equal (residue '(sin (/ 1 z)) 'z 0) 1)
  (assert-equal (residue '(cos (/ 1 z)) 'z 0) 0)
  (assert-equal (residue '(* (^ z 2) (sin (/ 1 z))) 'z 0) -1/6)
  (assert-equal (residue '(exp (/ 2 (^ z 2))) 'z 0) 0)
  (assert-equal (residue '(* z (exp (/ 2 (^ z 2)))) 'z 0) 2)
  (assert-equal (residue '(exp (/ 1 (- z 1))) 'z 1) 1)
  (assert-equal (residue '(sinh (/ 1 z)) 'z 0) 1))

(deftest "ca: неизвестное — unknown, а не число"
  ; e^z · e^{1/z}: вычет — Σ 1/(k!(k+1)!), ряд Бесселя, замкнутой формулы нет
  (assert-equal (residue '(* (exp z) (exp (/ 1 z))) 'z 0) 'unknown)
  (assert-equal (residue '(sqrt z) 'z 0) 'unknown)
  (assert-equal (residue '(log z) 'z 0) 'unknown)
  (assert-equal (residue '(/ 1 (sin (/ 1 z))) 'z 0) 'unknown))

; ---------- тип особенности ----------

(deftest "ca: устранимая, полюс, существенная"
  (assert-equal (singularity-type '(/ (sin z) z) 'z 0) 'removable)
  (assert-equal (singularity-type '(/ (- (exp z) 1) z) 'z 0) 'removable)
  (assert-equal (singularity-type '(/ (- 1 (cos z)) (^ z 2)) 'z 0) 'removable)
  (assert-equal (singularity-type cat-f2 'z 1) '(pole 2))
  (assert-equal (singularity-type cat-f2 'z 0) '(pole 1))
  (assert-equal (singularity-type cat-f1 'z '%i) '(pole 1))
  (assert-equal (singularity-type '(exp (/ 1 z)) 'z 0) 'essential)
  (assert-equal (singularity-type '(sin (/ 1 z)) 'z 0) 'essential)
  (assert-equal (singularity-type '(* (^ z -5) (exp (/ 1 z))) 'z 0) 'essential))

(deftest "ca: обычная точка — regular, не removable"
  (assert-equal (singularity-type cat-f1 'z 5) 'regular)
  (assert-equal (singularity-type '(exp z) 'z 3) 'regular))

(deftest "ca: бесконечность"
  (assert-equal (singularity-type 'z 'z 'inf) '(pole 1))
  (assert-equal (singularity-type '(^ z 3) 'z 'inf) '(pole 3))
  (assert-equal (singularity-type cat-f1 'z 'inf) 'regular)
  (assert-equal (singularity-type '(exp z) 'z 'inf) 'essential)
  (assert-equal (singularity-type '(sin z) 'z 'inf) 'essential))

(deftest "ca: тип unknown там, где нет доказательства"
  (assert-equal (singularity-type '(sqrt z) 'z 0) 'unknown)
  (assert-equal (singularity-type '(log z) 'z 0) 'unknown)
  ; нули sin(1/z) накапливаются к 0: особенность не изолирована
  (assert-equal (singularity-type '(/ 1 (sin (/ 1 z))) 'z 0) 'unknown)
  (assert-equal (singularity-type '(tan (/ 1 z)) 'z 0) 'unknown)
  ; два существенных слагаемых могли бы сократиться
  (assert-equal (singularity-type '(+ (exp (/ 1 z)) (exp (/ -1 z))) 'z 0) 'unknown))

; ---------- особые точки ----------

(deftest "ca: singularities"
  (assert-equal (singularities cat-f1 'z) (list '%i '(* -1 %i)))
  (assert-equal (sort (singularities cat-f2 'z) <) '(0 1))
  (assert-equal (singularities '(exp (/ 1 z)) 'z) '(0))
  (assert-equal (singularities '(/ (sin z) z) 'z) '(0))
  (assert-equal (singularities '(exp z) 'z) '())
  (assert-equal (length (singularities '(/ 1 (+ (^ z 4) 1)) 'z)) 4)
  (assert-equal (singularities '(/ (exp z) (* z (+ z 1) (- z 2))) 'z) (singularities '(/ 1 (* z (+ z 1) (- z 2))) 'z)))

(deftest "ca: singularities — unknown, если корни не явные или функция не из словаря"
  (assert-equal (singularities '(/ 1 (+ (^ z 3) -2)) 'z) 'unknown)
  (assert-equal (singularities '(tan z) 'z) 'unknown)
  (assert-equal (singularities '(/ 1 (sin z)) 'z) 'unknown)
  (assert-equal (singularities '(sqrt z) 'z) 'unknown))

; ---------- ряд Лорана ----------

(deftest "ca: laurent e^z/z^3 в нуле"
  (let ((l (laurent '(/ (exp z) (^ z 3)) 'z 0 2)))
    (assert-equal (simplify (- l '(+ (^ z -3) (^ z -2) (* 1/2 (^ z -1)) 1/6 (* 1/24 z) (* 1/120 (^ z 2))))) 0)))

(deftest "ca: laurent cot z и 1/(z^2+1) в бесконечности"
  (assert-equal (simplify (- (laurent '(cot z) 'z 0 3) '(+ (^ z -1) (* -1/3 z) (* -1/45 (^ z 3))))) 0)
  (assert-equal (simplify (- (laurent cat-f1 'z 'inf 4) '(+ (^ z -2) (* -1 (^ z -4))))) 0))

(deftest "ca: laurent в комплексной точке"
  ; 1/(z²+1) = −i/2 · 1/(z−i) + 1/4 + i/8 (z−i) + …
  (assert-equal (simplify (- (laurent cat-f1 'z '%i 1)
                             '(+ 1/4 (* -1/2 %i (^ (+ z (* -1 %i)) -1)) (* 1/8 %i (+ z (* -1 %i))))))
                0))

(deftest "ca: laurent существенной особенности — симметричное усечение"
  (let ((l (laurent '(exp (/ 1 z)) 'z 0 2)))
    (assert-equal (simplify (- l '(+ 1 (^ z -1) (* 1/2 (^ z -2))))) 0))
  (assert-equal (simplify (- (laurent '(sin (/ 1 z)) 'z 0 3) '(+ (^ z -1) (* -1/6 (^ z -3))))) 0))

(deftest "ca: laurent — отказ и ошибка порядка"
  (assert-equal (laurent '(sqrt z) 'z 0 3) 'unknown)
  (assert-error (laurent cat-f1 'z '%i -1)))

; ---------- интеграл по окружности ----------

(deftest "ca: контурные интегралы-оракулы"
  (assert-equal (contour-integral cat-f1 'z 0 2) 0)
  (assert-equal (contour-integral '(/ 1 (* z (- z 1))) 'z 0 1/2) '(* -2 %i pi))
  (assert-equal (contour-integral '(/ 1 (* z (- z 1))) 'z 0 2) 0)
  (assert-equal (contour-integral cat-f1 'z '%i 1/2) 'pi)
  (assert-equal (contour-integral '(/ (exp z) (^ z 3)) 'z 0 1) '(* %i pi))
  (assert-equal (contour-integral '(exp (/ 1 z)) 'z 0 3) '(* 2 %i pi))
  (assert-equal (contour-integral cat-f1 'z 5 1) 0))

(deftest "ca: контурный интеграл — unknown на контуре и без мероморфности"
  (assert-equal (contour-integral cat-f1 'z 0 1) 'unknown)
  (assert-equal (contour-integral '(sqrt z) 'z 0 1) 'unknown)
  (assert-equal (contour-integral '(/ 1 (+ (^ z 3) -2)) 'z 0 3) 'unknown)
  (assert-equal (contour-integral '(* (exp z) (exp (/ 1 z))) 'z 0 1) 'unknown))

; ---------- проверки (численный круг) ----------

(deftest "ca: residue-check подтверждает верные вычеты"
  (assert-equal (residue-check cat-f1 'z '%i '(* -1/2 %i)) 'numeric)
  (assert-equal (residue-check '(/ (exp z) (^ z 3)) 'z 0 1/2) 'numeric)
  (assert-equal (residue-check '(exp (/ 1 z)) 'z 0 1) 'numeric)
  (assert-equal (residue-check cat-f2 'z 1 -1) 'numeric)
  (assert-equal (residue-check '(/ 1 z) 'z 'inf -1) 'numeric)
  (assert-equal (residue-check '(cot z) 'z 0 1) 'numeric)
  (assert-equal (residue-check '(* (^ z 2) (sin (/ 1 z))) 'z 0 -1/6) 'numeric))

(deftest "ca: residue-check ловит подставные вычеты"
  (assert-equal (residue-check cat-f1 'z '%i '(* 1/2 %i)) 'mismatch)
  (assert-equal (residue-check '(/ (exp z) (^ z 3)) 'z 0 1/3) 'mismatch)
  (assert-equal (residue-check '(exp (/ 1 z)) 'z 0 2) 'mismatch)
  (assert-equal (residue-check cat-f2 'z 1 1) 'mismatch)
  (assert-equal (residue-check '(/ 1 z) 'z 'inf 1) 'mismatch)
  (assert-equal (residue-check cat-f1 'z 5 1) 'mismatch)
  (assert-equal (residue-check cat-f1 'z '%i 'unknown) 'unknown)
  ; особые точки cot не найдены явно — mismatch не утверждается
  (assert-equal (residue-check '(cot z) 'z 0 2) 'unknown))

(deftest "ca: contour-integral-check"
  (assert-equal (contour-integral-check '(/ 1 (* z (- z 1))) 'z 0 1/2 '(* -2 %i pi)) 'numeric)
  (assert-equal (contour-integral-check '(/ 1 (* z (- z 1))) 'z 0 1/2 '(* 2 %i pi)) 'mismatch)
  (assert-equal (contour-integral-check cat-f1 'z 0 2 0) 'numeric)
  (assert-equal (contour-integral-check cat-f1 'z 0 2 1) 'mismatch)
  (assert-equal (contour-integral-check '(/ (exp z) (^ z 3)) 'z 0 1 '(* %i pi)) 'numeric)
  ; полюсы на контуре: два числа узлов не сходятся — unknown, не ложный ответ
  (assert-equal (contour-integral-check cat-f1 'z 0 1 0) 'unknown))

(deftest "ca: ответ contour-integral всегда проходит численную проверку"
  (for-each (lambda (case)
              (let ((v (contour-integral (car case) 'z (cadr case) (caddr case))))
                (assert-true (not (equal? v 'unknown)))
                (assert-equal (contour-integral-check (car case) 'z (cadr case) (caddr case) v) 'numeric)))
            (list (list cat-f2 0 1/2) (list cat-f2 1 1/2) (list cat-f2 0 2) (list '(/ (exp z) (+ z 1)) 0 2)
                  (list '(/ (cos z) (^ z 4)) 0 1) (list '(* (^ z 2) (exp (/ 1 z))) 0 1)
                  (list '(/ 1 (+ (^ z 2) (* 2 z) 5)) -1 3))))

; ---------- вещественные интегралы ----------

(deftest "ca: ∫ R(x) dx по ℝ через вычеты — оракулы"
  (assert-equal (integral-by-residues '(/ 1 (+ (^ x 2) 1)) 'x) 'pi)
  (assert-equal (integral-by-residues '(/ 1 (^ (+ (^ x 2) 1) 2)) 'x) '(* 1/2 pi))
  (assert-equal (integral-by-residues '(/ 1 (+ (^ x 2) (* 2 x) 5)) 'x) '(* 1/2 pi))
  (assert-equal (integral-by-residues '(/ 1 (+ (^ x 4) (* 5 (^ x 2)) 4)) 'x) '(* 1/6 pi)))

(deftest "ca: ∫ по ℝ совпадает с integrate"
  (for-each (lambda (r)
              (let ((a (integral-by-residues r 'x)) (b (integrate r 'x '-inf 'inf)))
                (assert-true (not (equal? a 'unknown)))
                (assert-true (cat-near? (eval-num a) (eval-num b) 1e-9))))
            (list '(/ 1 (+ (^ x 2) 1)) '(/ 1 (^ (+ (^ x 2) 1) 3)) '(/ (^ x 2) (^ (+ (^ x 2) 1) 2))
                  '(/ (+ x 3) (^ (+ (^ x 2) (* 2 x) 5) 2)))))

; полюса x⁴+1 — алгебраические числа (±1±i)/√2; ∫ = π/√2 (integrate на x⁴+1 берёт ≈ 11 с — в сверку не берём)
(deftest "ca: ∫ по ℝ при комплексных алгебраических полюсах"
  (assert-equal (integral-by-residues '(/ 1 (+ (^ x 4) 1)) 'x) '(* 1/2 (^ 2 1/2) pi))
  (assert-equal (integral-by-residues '(/ (^ x 2) (+ (^ x 4) 1)) 'x) '(* 1/2 (^ 2 1/2) pi)))

(deftest "ca: ∫ по ℝ — unknown вне условий теоремы"
  (assert-equal (integral-by-residues '(/ 1 (- (^ x 2) 1)) 'x) 'unknown)      ; вещественные полюсы
  (assert-equal (integral-by-residues '(/ x (+ (^ x 2) 1)) 'x) 'unknown)      ; убывание 1/x
  (assert-equal (integral-by-residues '(/ (sin x) (+ (^ x 2) 1)) 'x) 'unknown)
  (assert-equal (integral-by-residues '(/ 1 (+ (^ x 3) 2)) 'x) 'unknown))

; ---------- шаг CA.b: Жордан, главное значение, замочная скважина ----------

(deftest "ca.b: лемма Жордана — оракулы (cos, sin, exp, полувычет при устранимой особенности)"
  (assert-equal (integral-fourier '(/ (cos x) (+ (^ x 2) 1)) 'x) '(* pi (exp -1)))
  (assert-equal (integral-fourier '(/ (* x (sin x)) (+ (^ x 2) 1)) 'x) '(* pi (exp -1)))
  (assert-equal (integral-fourier '(/ (cos (* 2 x)) (^ (+ (^ x 2) 1) 2)) 'x) '(* 3/2 pi (exp -2)))
  (assert-equal (integral-fourier '(/ (sin x) x) 'x) 'pi)
  (assert-equal (integral-fourier '(/ (exp (* %i x)) (+ (^ x 2) 1)) 'x) '(* pi (exp -1)))
  (assert-equal (integral-fourier '(/ (cos (* -3 x)) (+ (^ x 2) 4)) 'x) '(* 1/2 pi (exp -6)))
  (assert-equal (integral-fourier '(/ (sin (* -3 x)) (* x (+ (^ x 2) 4))) 'x) '(+ (* -1/4 pi) (* 1/4 pi (exp -6)))))

(deftest "ca.b: Жордан при алгебраических полюсах (x⁴+1) — численно"
  (let ((v (integral-fourier '(/ (cos x) (+ (^ x 4) 1)) 'x)))
    ; π/√2 · e^{−1/√2} (cos(1/√2) + sin(1/√2))
    (assert-true (cat-near? (eval-num v) 1.54428 1e-4))
    (assert-equal (integral-residues-check '(/ (cos x) (+ (^ x 4) 1)) 'x '-inf 'inf v) 'numeric)))

(deftest "ca.b: Жордан — знак параметра из деклараций"
  (assert-equal (assuming ((a positive)) (integral-fourier '(/ (cos (* a x)) (+ (^ x 2) 1)) 'x)) '(* pi (exp (* -1 a))))
  (assert-equal (assuming ((a negative)) (integral-fourier '(/ (cos (* a x)) (+ (^ x 2) 1)) 'x)) '(* pi (exp a)))
  (assert-equal (assuming ((a negative)) (integral-fourier '(/ (sin (* a x)) (+ (^ x 2) 1)) 'x)) 0)
  (assert-equal (assuming ((a positive)) (integral-fourier '(/ (* x (sin (* a x))) (+ (^ x 2) 1)) 'x)) '(* pi (exp (* -1 a))))
  (assert-equal (assuming ((a negative)) (integral-fourier '(/ (* x (sin (* a x))) (+ (^ x 2) 1)) 'x)) '(* -1 pi (exp a)))
  (assert-equal (integral-fourier '(/ (cos (* a x)) (+ (^ x 2) 1)) 'x) 'unknown))     ; знак a неизвестен

(deftest "ca.b: Жордан — unknown вне условий (расходимость, убывание, полюс без устранимости)"
  (assert-equal (integral-fourier '(/ (cos x) x) 'x) 'unknown)                  ; полюс 0, cos 0 ≠ 0
  (assert-equal (integral-fourier '(/ (cos x) (- (^ x 2) 1)) 'x) 'unknown)
  (assert-equal (integral-fourier '(cos x) 'x) 'unknown)
  (assert-equal (integral-fourier '(/ (cos x) (^ x 2)) 'x) 'unknown)             ; двойной полюс
  (assert-equal (integral-fourier '(/ (cos (^ x 2)) (+ (^ x 2) 1)) 'x) 'unknown) ; нелинейный аргумент
  (assert-equal (integral-fourier '(/ (exp x) (+ (^ x 2) 1)) 'x) 'unknown))

; главное значение проверено независимой квадратурой (середины на сетке, симметричной относительно полюсов, L = 300)
(deftest "ca.b: главное значение при простых вещественных полюсах"
  (assert-equal (integral-pv '(/ 1 (* x (- x 1))) 'x) 0)
  (assert-equal (integral-pv '(/ (cos x) (- (^ x 2) 1)) 'x) '(* -1 pi (sin 1)))     ; ≈ −2.64356
  (assert-equal (integral-pv '(/ (sin x) (- x 1)) 'x) '(* pi (cos 1)))              ; ≈ 1.69741
  (assert-equal (integral-pv '(/ (sin x) x) 'x) 'pi))

(deftest "ca.b: integrate не отдаёт главное значение как обычный ответ"
  (for-each (lambda (f)
              (let ((r (integrate f 'x '-inf 'inf)))
                (assert-true (and (pair? r) (equal? (car r) 'integrate)))))
            (list '(/ 1 (* x (- x 1))) '(/ (cos x) (- (^ x 2) 1)) '(/ (sin x) (- x 1)) '(/ (cos x) x))))

(deftest "ca.b: замочная скважина — оракулы"
  (assert-equal (integral-keyhole '(/ (^ x -1/2) (+ x 1)) 'x) 'pi)
  (assert-equal (integral-keyhole '(/ (^ x 1/3) (+ (^ x 2) 1)) 'x) '(* 1/3 (^ 3 1/2) pi))   ; π/(2 sin(2π/3))
  (assert-equal (integral-keyhole '(/ (^ x 1/2) (^ (+ x 1) 2)) 'x) '(* 1/2 pi))          ; двойной полюс
  (assert-equal (integral-keyhole '(/ (log x) (+ (^ x 2) 1)) 'x) 0)
  (assert-equal (integral-keyhole '(/ (log x) (^ (+ x 1) 2)) 'x) 0)
  (assert-equal (integral-keyhole '(/ 1 (+ (^ x 3) 1)) 'x) '(* 2/9 (^ 3 1/2) pi))
  (assert-equal (integral-keyhole '(/ (log x) (+ (^ x 3) 1)) 'x) '(* -2/27 (^ pi 2))))

(deftest "ca.b: замочная скважина — нецелые полюсы и unknown вне сходимости"
  (let ((v (integral-keyhole '(/ (^ x 1/2) (+ (^ x 2) (* 2 x) 2)) 'x)))
    (assert-equal (integral-residues-check '(/ (^ x 1/2) (+ (^ x 2) (* 2 x) 2)) 'x 0 'inf v) 'numeric))
  (assert-equal (integral-keyhole '(/ (^ x 1/2) (+ x 1)) 'x) 'unknown)           ; расходится (α ≥ d − 1)
  (assert-equal (integral-keyhole '(/ (^ x -3/2) (+ x 1)) 'x) 'unknown)          ; расходится в 0
  (assert-equal (integral-keyhole '(/ (^ x 1/2) (- x 1)) 'x) 'unknown)           ; полюс на (0, ∞)
  (assert-equal (integral-keyhole '(/ (log x) (+ x 1)) 'x) 'unknown))

(deftest "ca.b: численная сверка — верные ответы и подделки"
  (assert-equal (integral-residues-check '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 'inf '(* pi (exp -1))) 'numeric)
  (assert-equal (integral-residues-check '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 'inf 'pi) 'mismatch)
  (assert-equal (integral-residues-check '(/ (* x (sin x)) (+ (^ x 2) 1)) 'x '-inf 'inf '(* pi (exp -1))) 'numeric)
  (assert-equal (integral-residues-check '(/ (sin x) x) 'x '-inf 'inf '(* 2 pi)) 'mismatch)
  (assert-equal (integral-residues-check '(/ (^ x -1/2) (+ x 1)) 'x 0 'inf 'pi) 'numeric)
  (assert-equal (integral-residues-check '(/ (^ x -1/2) (+ x 1)) 'x 0 'inf '(* 2 pi)) 'mismatch)
  (assert-equal (integral-residues-check '(/ (log x) (+ (^ x 2) 1)) 'x 0 'inf 1) 'mismatch)
  (assert-equal (assuming ((a positive)) (integral-residues-check '(/ (cos (* a x)) (+ (^ x 2) 1)) 'x '-inf 'inf '(* pi (exp (* -1 a))))) 'numeric)
  (assert-equal (assuming ((a positive)) (integral-residues-check '(/ (cos (* a x)) (+ (^ x 2) 1)) 'x '-inf 'inf '(* pi (exp a)))) 'mismatch))

(deftest "ca.b: запасной путь integrate — только доказанное и сверенное"
  (let ((v (integrate '(/ (cos x) (+ (^ x 4) 1)) 'x '-inf 'inf)))
    (assert-true (cat-near? (eval-num v) 1.54428 1e-4)))
  (assert-equal (integrate '(/ (sin x) (* x (+ (^ x 2) 1))) 'x '-inf 'inf) '(+ pi (* -1 pi (exp -1))))
  (assert-equal (definite-by-residues '(/ (cos x) (+ (^ x 2) 1)) 'x 0 'inf) '(* 1/2 pi (exp -1)))
  (assert-equal (definite-by-residues '(/ 1 (* x (- x 1))) 'x '-inf 'inf) 'unknown)
  (assert-equal (definite-by-residues '(/ (cos x) (+ (^ x 2) 1)) 'x 1 'inf) 'unknown))

; ---------- шаг CA.c: степени тригонометрии, (−inf, 0), период, x^α с параметром ----------

(define pi-num (eval-num 'pi))

(deftest "ca.c: Жордан — степени и произведения тригонометрии (оракулы)"
  (assert-equal (integral-fourier '(/ (^ (sin x) 2) (^ x 2)) 'x) 'pi)
  (assert-equal (integral-fourier '(/ (^ (cos x) 2) (+ (^ x 2) 1)) 'x) '(+ (* 1/2 pi) (* 1/2 pi (exp -2))))
  (assert-equal (integral-fourier '(/ (* (sin x) (cos x)) (* x (+ (^ x 2) 1))) 'x) '(+ (* 1/2 pi) (* -1/2 pi (exp -2))))
  (assert-equal (integral-fourier '(/ (^ (sin x) 3) (^ x 3)) 'x) '(* 3/4 pi))
  (assert-equal (integral-fourier '(/ (+ (cos x) -1) (^ x 2)) 'x) '(* -1 pi))
  (assert-equal (integral-fourier '(/ (* (cos x) (cos (* 2 x))) (+ (^ x 2) 1)) 'x) '(+ (* 1/2 pi (exp -3)) (* 1/2 pi (exp -1)))))

(deftest "ca.c: степени тригонометрии — unknown там, где расходится или не устранимо"
  (assert-equal (integral-fourier '(/ (^ (cos x) 2) (^ x 2)) 'x) 'unknown)     ; полюс 2-го порядка не устраним
  (assert-equal (integral-fourier '(/ (cos x) (^ x 2)) 'x) 'unknown)
  (assert-equal (integral-pv '(/ (^ (sin x) 2) (^ x 2)) 'x) 'unknown)           ; v.p. — только простые полюса
  (assert-equal (integral-fourier '(^ (sin x) 2) 'x) 'unknown)                  ; нет убывания
  (assert-equal (integral-fourier '(/ (^ (sin (^ x 2)) 2) (+ (^ x 2) 1)) 'x) 'unknown))

(deftest "ca.c: сверка степеней тригонометрии — верные ответы и подделки"
  (assert-equal (integral-residues-check '(/ (^ (sin x) 2) (^ x 2)) 'x '-inf 'inf 'pi) 'numeric)
  (assert-equal (integral-residues-check '(/ (^ (sin x) 2) (^ x 2)) 'x '-inf 'inf '(* 2 pi)) 'mismatch)
  (assert-equal (integral-residues-check '(/ (^ (cos x) 2) (+ (^ x 2) 1)) 'x '-inf 'inf '(* 1/2 pi (+ 1 (exp -2)))) 'numeric)
  (assert-equal (integral-residues-check '(/ (^ (cos x) 2) (+ (^ x 2) 1)) 'x '-inf 'inf '(* pi (exp -2))) 'mismatch)
  (assert-equal (integral-residues-check '(/ (^ (sin x) 3) (^ x 3)) 'x '-inf 'inf '(* 3/4 pi)) 'numeric)
  (assert-equal (integral-residues-check '(/ (^ (sin x) 3) (^ x 3)) 'x '-inf 'inf '(* 3/2 pi)) 'mismatch))

(deftest "ca.c: интервал (−inf, 0) — подстановка x → −x"
  (assert-equal (definite-by-residues '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 0) '(* 1/2 pi (exp -1)))
  (assert-equal (definite-by-residues '(/ 1 (+ (^ x 2) (* -2 x) 2)) 'x '-inf 0) '(* 1/4 pi))
  (assert-equal (definite-by-residues '(/ (sin x) (* x (+ (^ x 2) 1))) 'x '-inf 0) '(* 1/2 (+ pi (* -1 pi (exp -1)))))
  (assert-equal (definite-by-residues '(/ 1 (+ (^ x 3) 1)) 'x '-inf 0) 'unknown)   ; полюс −1 на промежутке: расходится
  (assert-equal (definite-by-residues '(/ (^ x 1/2) (+ (^ x 2) 1)) 'x '-inf 0) 'unknown)   ; ветвь на x < 0 не вещественна
  (assert-equal (integral-residues-check '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 0 '(* 1/2 pi (exp -1))) 'numeric)
  (assert-equal (integral-residues-check '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 0 'pi) 'mismatch)
  (assert-equal (integral-residues-check '(/ 1 (+ (^ x 2) (* -2 x) 2)) 'x '-inf 0 '(* 3/4 pi)) 'mismatch)
  (assert-equal (integrate '(/ (cos x) (+ (^ x 2) 1)) 'x '-inf 0) '(* 1/2 pi (exp -1))))

(deftest "ca.c: тригонометрический интеграл по периоду — оракулы"
  (assert-equal (integral-trig '(/ 1 (+ 2 (cos x))) 'x 0 '(* 2 pi)) '(* 2/3 (^ 3 1/2) pi))
  (assert-equal (integral-trig '(/ 1 (+ 5 (* -4 (sin x)))) 'x 0 '(* 2 pi)) '(* 2/3 pi))
  (assert-equal (integral-trig '(/ (^ (cos x) 2) (+ 5 (* 4 (cos x)))) 'x 0 '(* 2 pi)) '(* 5/12 pi))
  (assert-equal (integral-trig '(/ (cos (* 2 x)) (+ 5 (* 4 (cos x)))) 'x 0 '(* 2 pi)) '(* 1/6 pi))
  (assert-equal (integral-trig '(/ 1 (+ 2 (cos x))) 'x '(* -1 pi) 'pi) '(* 2/3 (^ 3 1/2) pi))
  (assert-equal (integral-trig '(/ 1 (+ 2 (cos x))) 'x 0 'pi) '(* 1/3 (^ 3 1/2) pi))    ; чётная: половина
  (assert-equal (integral-trig 1 'x 0 '(* 2 pi)) '(* 2 pi)))

(deftest "ca.c: тригонометрический интеграл — unknown (полюс на окружности, нечётная часть, чужие границы)"
  (assert-equal (integral-trig '(/ 1 (+ 1 (cos x))) 'x 0 '(* 2 pi)) 'unknown)      ; полюс z = −1 на окружности
  (assert-equal (integral-trig '(/ 1 (+ 1 (* 2 (cos x)))) 'x 0 '(* 2 pi)) 'unknown)
  (assert-equal (integral-trig '(/ 1 (+ 2 (sin x))) 'x 0 'pi) 'unknown)           ; не чётная по θ — [0, π] не половина
  (assert-equal (integral-trig '(/ 1 (+ 2 (cos x))) 'x 0 1) 'unknown)
  (assert-equal (integral-trig '(/ (cos (* 1/2 x)) (+ 2 (cos x))) 'x 0 '(* 2 pi)) 'unknown))   ; не целая кратность

(deftest "ca.c: a + b cos θ — неравенство a > |b| из деклараций"
  (let ((f '(/ 1 (+ a (* b (cos x))))))
    (assert-equal (assuming ((a (interval 2 'inf 'open 'open)) (b (interval 0 1 'open 'open))) (integral-trig f 'x 0 '(* 2 pi)))
                  '(* 2 pi (^ (sqrt (+ (^ a 2) (* -1 (^ b 2)))) -1)))
    (assert-equal (assuming ((a positive) (b positive)) (integral-trig f 'x 0 '(* 2 pi))) 'unknown)    ; a > b не следует
    (assert-equal (integral-trig f 'x 0 '(* 2 pi)) 'unknown)
    (assert-equal (assuming ((a (interval 1 3 'open 'open)) (b (interval 0 5 'open 'open))) (integral-trig f 'x 0 '(* 2 pi))) 'unknown)
    (assert-equal (assuming ((a (interval 2 'inf 'open 'open)) (b (interval 0 1 'open 'open)))
                    (integral-residues-check f 'x 0 '(* 2 pi) '(* 2 pi (^ (sqrt (+ (^ a 2) (* -1 (^ b 2)))) -1))))
                  'numeric)
    (assert-equal (assuming ((a (interval 2 'inf 'open 'open)) (b (interval 0 1 'open 'open)))
                    (integral-residues-check f 'x 0 '(* 2 pi) '(* 2 pi (^ a -1))))
                  'mismatch)))

(deftest "ca.c: запасной путь integrate — период тригонометрии"
  (assert-equal (assuming ((a (interval 2 'inf 'open 'open)) (b (interval 0 1 'open 'open)))
                  (integrate '(/ 1 (+ a (* b (cos x)))) 'x 0 '(* 2 pi)))
                '(* 2 pi (^ (sqrt (+ (^ a 2) (* -1 (^ b 2)))) -1)))
  (let ((r (integrate '(/ 1 (+ a (* b (cos x)))) 'x 0 '(* 2 pi))))      ; без деклараций — не значение
    (assert-true (and (pair? r) (equal? (car r) 'integrate))))
  (let ((r (integrate '(/ 1 (+ 1 (* 2 (cos x)))) 'x 0 '(* 2 pi))))      ; полюс на оси
    (assert-true (and (pair? r) (equal? (car r) 'integrate))))
  (assert-equal (integrate '(/ 1 (+ 2 (cos x))) 'x 0 '(* 2 pi)) '(* 2/3 (^ 3 1/2) pi)))

(deftest "ca.c: x^α с параметром — условие сходимости из деклараций"
  (let ((I01 (interval 0 1 'open 'open)) (Im11 (interval -1 1 'open 'open)))
    (assert-equal (assuming ((al I01)) (integral-keyhole '(/ (^ x (+ al -1)) (+ 1 x)) 'x)) '(* pi (^ (sin (* al pi)) -1)))
    (assert-equal (assuming ((al Im11)) (integral-keyhole '(/ (^ x al) (+ (^ x 2) 1)) 'x))
                  '(* pi (sin (* 1/2 al pi)) (^ (sin (* al pi)) -1)))
    ;; π/(2 cos(πα/2)) в точках области сходимости
    (assuming ((al Im11))
      (let ((v (integral-keyhole '(/ (^ x al) (+ (^ x 2) 1)) 'x)))
        (for-each (lambda (a) (assert-true (cat-near? (eval-num (subst (list 'al a) v)) (/ pi-num (* 2 (cos (* 0.5 a pi-num)))) 1e-9)))
                  '(0.3 -0.6 0.8))))
    ;; вне области (α из (3, 4)) — расходится: unknown
    (assert-equal (assuming ((al (interval 3 4 'open 'open))) (integral-keyhole '(/ (^ x (+ al -1)) (+ 1 x)) 'x)) 'unknown)
    (assert-equal (assuming ((al (interval -3 -2 'open 'open))) (integral-keyhole '(/ (^ x al) (+ (^ x 2) 1)) 'x)) 'unknown)
    ;; целозначный показатель: формула вырождена (sin πα = 0)
    (assert-equal (assuming ((n integers)) (integral-keyhole '(/ (^ x n) (+ (^ x 2) 1)) 'x)) 'unknown)))

(deftest "ca.c: x^α без деклараций — ответ с записанным условием"
  (let ((r (capture-conditions (lambda () (integral-keyhole '(/ (^ x (+ al -1)) (+ 1 x)) 'x)))))
    (assert-equal (car r) '(* pi (^ (sin (* al pi)) -1)))
    (assert-true (member? '(> al 0) (map car (cadr r))))
    (assert-true (member? '(< al 1) (map car (cadr r)))))
  (let ((r (capture-conditions (lambda () (integrate '(/ (^ x (+ al -1)) (+ 1 x)) 'x 0 'inf)))))
    (assert-equal (car r) '(* pi (^ (sin (* al pi)) -1)))
    (assert-true (member? '(> al 0) (map car (cadr r)))))
  (assert-equal (integral-keyhole '(/ (^ x (+ (* 2 al) -1)) (+ 1 x)) 'x) 'unknown))     ; показатель не вида «символ + число»

(deftest "ca.c: x^α·log x"
  (assert-equal (integral-keyhole '(/ (* (^ x 1/2) (log x)) (+ (^ x 2) 1)) 'x) '(* 1/4 (^ 2 1/2) (^ pi 2)))
  (assert-equal (integral-residues-check '(/ (* (^ x 1/2) (log x)) (+ (^ x 2) 1)) 'x 0 'inf '(* 1/4 (^ 2 1/2) (^ pi 2))) 'numeric)
  (assert-equal (integral-residues-check '(/ (* (^ x 1/2) (log x)) (+ (^ x 2) 1)) 'x 0 'inf '(* 1/2 (^ 2 1/2) (^ pi 2))) 'mismatch)
  (assert-equal (integral-keyhole '(/ (* (^ x 1/2) (log x)) (+ x 1)) 'x) 'unknown))   ; расходится

(deftest "ca.c: сверка x^α в нескольких точках области — подделка даёт mismatch"
  (let ((I01 (interval 0 1 'open 'open)) (f '(/ (^ x (+ al -1)) (+ 1 x))))
    (assert-equal (assuming ((al I01)) (integral-residues-check f 'x 0 'inf '(* pi (^ (sin (* al pi)) -1)))) 'numeric)
    (assert-equal (assuming ((al I01)) (integral-residues-check f 'x 0 'inf '(* 2 pi (^ (sin (* al pi)) -1)))) 'mismatch)
    ;; верно при α = 1/2 (π), неверно в других точках — одна точка не доказательство
    (assert-equal (assuming ((al I01)) (integral-residues-check f 'x 0 'inf '(* pi (^ (sin (* 1/2 pi)) -1)))) 'mismatch)
    (assert-equal (integrate '(/ (^ x (+ al -1)) (+ 1 x)) 'x 0 'inf) '(* pi (^ (sin (* al pi)) -1)))))

(deftest "ca.c: интервальный знак по декларациям"
  (assuming ((a (interval 2 'inf 'open 'open)) (b (interval 0 1 'open 'open)))
    (assert-true (complex-analysis::cb-ipos? '(+ (^ a 2) (* -1 (^ b 2)))))
    (assert-true (complex-analysis::cb-ipos? '(+ a (* -1 b))))
    (assert-true (complex-analysis::cb-ineg? '(+ b (* -1 a))))
    (assert-true (not (complex-analysis::cb-ipos? '(+ b -1/2)))))
  (assuming ((a positive) (b positive))
    (assert-true (not (complex-analysis::cb-ipos? '(+ a (* -1 b)))))))

; ---------- язык ----------

(deftest "ca: входной язык"
  (assert-equal (math-eval "residue(1/(z^2+1), z, %i)") '(* -1/2 %i))
  (assert-equal (math-eval "integral_by_residues(1/(x^2+1), x)") 'pi)
  (assert-equal (math-eval "integral_fourier(cos(x)/(x^2+1), x)") '(* pi (exp -1)))
  (assert-equal (math-eval "integral_pv(cos(x)/(x^2-1), x)") '(* -1 pi (sin 1)))
  (assert-equal (math-eval "integral_keyhole(x^(-1/2)/(x+1), x)") 'pi)
  (assert-equal (math-eval "integral_residues_check(cos(x)/(x^2+1), x, -inf, inf, pi)") 'mismatch)
  (assert-equal (math-eval "integral_trig(1/(2+cos(x)), x, 0, 2*pi)") '(* 2/3 (^ 3 1/2) pi))
  (assert-equal (math-eval "integral_trig(1/(5-4*sin(x)), x, 0, 2*pi)") '(* 2/3 pi))
  (assert-equal (math-eval "integral_fourier(sin(x)^2/x^2, x)") 'pi)
  (assert-equal (math-eval "assuming(al > 0 and al < 1, integral_keyhole(x^(al-1)/(x+1), x))") '(* pi (^ (sin (* al pi)) -1)))
  (assert-equal (math-eval "contour_integral(1/(z*(z-1)), z, 0, 1/2)") '(* -2 %i pi))
  (assert-equal (math-eval "residue_check(1/(z^2+1), z, %i, 1/2*%i)") 'mismatch))
