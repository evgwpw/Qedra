; transforms.lisp — тесты шага TR.3: Z-преобразование, разностные уравнения, преобразование Фурье

(define (trt-same? a b)
  (let ((d (- a b)))
    (or (equal? (simplify (together d)) 0)
        (equal? (simplify (expand d)) 0)
        (equal? (simplify (expand (numer (together d)))) 0))))

(define (trt-Z a) (ztransform a 'n 'z))
(define (trt-iZ F) (inverse-ztransform F 'z 'n))
(define (trt-F f) (fourier f 't 'w))
(define (trt-iF F) (inverse-fourier F 'w 't))

; значение выражения от n в целых точках (список чисел)
(define (trt-seq e ns) (map (lambda (k) (eval-num (subst (list 'n k) e))) ns))
(define (trt-close-lists? a b)
  (every? (lambda (p) (< (abs (- (car p) (cdr p))) 0.000001)) (map2 cons a b)))

(deftest "Z: таблица a^n, 1, δ"
  (assert-true (trt-same? (trt-Z '(^ a n)) '(/ z (- z a))))
  (assert-true (trt-same? (trt-Z 1) '(/ z (- z 1))))
  (assert-true (trt-same? (trt-Z '(* 3 (^ 2 n))) '(/ (* 3 z) (- z 2))))
  (assert-equal (trt-Z '(kdelta n)) 1)
  (assert-true (trt-same? (trt-Z '(kdelta (- n 2))) '(^ z -2))))

(deftest "Z: n, n², n·2^n, n^k a^n (умножение на n)"
  (assert-true (trt-same? (trt-Z 'n) '(/ z (^ (- z 1) 2))))
  (assert-true (trt-same? (trt-Z '(^ n 2)) '(/ (* z (+ z 1)) (^ (- z 1) 3))))
  (assert-true (trt-same? (trt-Z '(* n (^ 2 n))) '(/ (* 2 z) (^ (- z 2) 2))))
  (assert-true (trt-same? (trt-Z '(* (^ n 2) (^ 3 n))) '(/ (* 3 z (+ z 3)) (^ (- z 3) 3)))))

(deftest "Z: sin(ωn), cos(ωn), a^n cos(ωn), C(n,2)"
  (assert-true (trt-same? (trt-Z '(sin (* w n))) '(/ (* z (sin w)) (+ (^ z 2) (* -2 z (cos w)) 1))))
  (assert-true (trt-same? (trt-Z '(cos (* w n))) '(/ (* z (- z (cos w))) (+ (^ z 2) (* -2 z (cos w)) 1))))
  (assert-true (trt-same? (trt-Z '(* (^ a n) (cos (* w n)))) '(/ (* z (- z (* a (cos w)))) (+ (^ z 2) (* -2 a z (cos w)) (^ a 2)))))
  (assert-true (trt-same? (trt-Z '(binomial n 2)) '(/ z (^ (- z 1) 3)))))

(deftest "Z: сдвиг a_{n+k}, запаздывание θ(n−k), свёртка"
  (assert-true (trt-same? (trt-Z '(a (+ n 1))) '(- (* z (ztransform (a n) n z)) (* z (a 0)))))
  (assert-true (trt-same? (trt-Z '(a (+ n 2)))
                          '(- (* (^ z 2) (ztransform (a n) n z)) (* (^ z 2) (a 0)) (* z (a 1)))))
  (assert-true (trt-same? (trt-Z '(* (heaviside (- n 2)) (^ 2 (- n 2)))) '(/ 1 (* z (- z 2)))))
  (assert-true (trt-same? (trt-Z '(sum (* (^ 2 k) (^ 3 (- n k))) k 0 n)) '(/ (^ z 2) (* (- z 2) (- z 3))))))

(deftest "Z: сертификат ztransform-check и подделки"
  (assert-equal (ztransform-check '(* n (^ 2 n)) '(/ (* 2 z) (^ (- z 2) 2)) 'n 'z) #t)
  (assert-equal (ztransform-check '(^ 2 n) '(/ z (- z 3)) 'n 'z) #f)
  (assert-equal (ztransform-check '(* n (^ 2 n)) '(/ z (^ (- z 2) 2)) 'n 'z) #f)
  (assert-equal (ztransform-check '(+ (^ 2 n) (cos n)) '(+ (/ z (- z 2)) (/ (* z (- z (cos 1))) (+ (^ z 2) (* -2 z (cos 1)) 1))) 'n 'z) #t)
  (assert-true (not (equal? (ztransform-check '(sin (* 2 n)) '(/ (* z (sin 2)) (+ (^ z 2) (* -2 z (cos 2)) 1)) 'n 'z) #f))))

(deftest "Z: обратное z/((z−1)(z−2)) = 2^n − 1, z²/(z−1/2)²"
  (assert-true (trt-same? (trt-iZ '(/ z (* (- z 1) (- z 2)))) '(- (^ 2 n) 1)))
  (assert-equal (ztransform-check (trt-iZ '(/ z (* (- z 1) (- z 2)))) '(/ z (* (- z 1) (- z 2))) 'n 'z) #t)
  (let ((r (trt-iZ '(/ (^ z 2) (^ (- z 1/2) 2)))))
    (assert-true (trt-close-lists? (trt-seq r '(0 1 2 3 4)) '(1 1 0.75 0.5 0.3125)))
    (assert-equal (ztransform-check r '(/ (^ z 2) (^ (- z 1/2) 2)) 'n 'z) #t)))

(deftest "Z: обратное — комплексные полюса и корни в Q(√d)"
  (let ((r (trt-iZ '(/ z (+ (^ z 2) 1)))))
    (assert-true (trt-close-lists? (trt-seq r '(0 1 2 3 4 5)) '(0 1 0 -1 0 1))))
  (let ((r (trt-iZ '(/ z (+ (^ z 2) (* -1 z) -1)))))
    (assert-true (trt-close-lists? (trt-seq r '(0 1 2 3 4 5 6)) '(0 1 1 2 3 5 8))))
  (let ((r (trt-iZ '(/ (* 2 z) (+ (^ z 2) (* -2 z) 2)))))
    (assert-equal (ztransform-check r '(/ (* 2 z) (+ (^ z 2) (* -2 z) 2)) 'n 'z) #t))
  (assert-true (trt-same? (trt-iZ '(/ 1 (- z 2))) '(- (* 1/2 (^ 2 n)) (* 1/2 (kdelta n))))))

(deftest "Z: теоремы о начальном и конечном значении"
  (assert-equal (ztransform-initial '(/ (+ z 1) (- z 2)) 'z) 1)
  (assert-equal (ztransform-final '(/ z (- z 1/2)) 'z) 0)
  (assert-equal (ztransform-final '(/ (* 2 z) (* (- z 1) (+ z 1/2) )) 'z) 4/3)
  (assert-equal (ztransform-final '(/ z (- z 2)) 'z) 'unknown))

(deftest "zsolve: a_{n+2} − 3a_{n+1} + 2a_n = 2^n, a₀ = 0, a₁ = 1 (резонанс)"
  (let* ((eq '(= (+ (a (+ n 2)) (* -3 (a (+ n 1))) (* 2 (a n))) (^ 2 n)))
         (conds '((= (a 0) 0) (= (a 1) 1)))
         (s (zsolve eq '(a n) conds)))
    (assert-true (trt-same? (caddr s) '(* 1/2 n (^ 2 n))))
    (assert-equal (zsolve-check eq '(a n) s conds) #t)
    (assert-equal (zsolve-check eq '(a n) '(= (a n) (^ 2 n)) conds) #f)))

(deftest "zsolve: Фибоначчи — формула Бине, совпадает с rsolve"
  (let* ((eq '(= (a (+ n 2)) (+ (a (+ n 1)) (a n))))
         (conds '((= (a 0) 0) (= (a 1) 1)))
         (s (zsolve eq '(a n) conds))
         (rs (rsolve (list 'recurrence 'S 'n (list -1 -1 1) 0 '((0 0) (1 1))))))
    (assert-true (trt-close-lists? (trt-seq (caddr s) '(0 1 2 3 4 5 6 7 8 9 10)) '(0 1 1 2 3 5 8 13 21 34 55)))
    (assert-true (trt-close-lists? (trt-seq (caddr s) '(0 1 2 3 4 5 6 7 8)) (trt-seq rs '(0 1 2 3 4 5 6 7 8))))
    (assert-true (not (equal? (zsolve-check eq '(a n) s conds) #f)))))

(deftest "zsolve: первого порядка, неоднородное, без условий, комплексные корни"
  (let ((s (zsolve '(= (a (+ n 1)) (+ (* 2 (a n)) 1)) '(a n) '((= (a 0) 1)))))
    (assert-true (trt-same? (caddr s) '(- (* 2 (^ 2 n)) 1))))
  (let ((s (zsolve '(= (a (+ n 1)) (* 3 (a n))) '(a n) '())))
    (assert-true (trt-same? (caddr s) '(* C1 (^ 3 n)))))
  (let ((s (zsolve '(= (a (+ n 2)) (* -1 (a n))) '(a n) '((= (a 0) 1) (= (a 1) 0)))))
    (assert-true (trt-close-lists? (trt-seq (caddr s) '(0 1 2 3 4)) '(1 0 -1 0 1))))
  (let ((s (zsolve '(= (a (+ n 2)) (+ (* 2 (a (+ n 1))) (* -1 (a n)))) '(a n) '((= (a 0) 1) (= (a 1) 3)))))
    (assert-true (trt-same? (caddr s) '(+ 1 (* 2 n))))))

(deftest "zsolve: подделки сертификата и невычисленное"
  (let ((eq '(= (a (+ n 1)) (+ (* 2 (a n)) 1))))
    (assert-equal (zsolve-check eq '(a n) '(= (a n) (- (* 2 (^ 2 n)) 1)) '((= (a 0) 1))) #t)
    (assert-equal (zsolve-check eq '(a n) '(= (a n) (- (* 2 (^ 2 n)) 1)) '((= (a 0) 2))) #f)
    (assert-equal (zsolve-check eq '(a n) '(= (a n) (- (^ 2 n) 1)) '((= (a 0) 0))) #t)
    (assert-equal (zsolve-check eq '(a n) '(= (a n) (^ 2 n)) '((= (a 0) 1))) #f))
  (let ((u (zsolve '(= (a (+ n 1)) (* (a n) (a n))) '(a n) '((= (a 0) 2)))))
    (assert-equal (car u) 'zsolve)))

(deftest "Фурье: e^{−|t|}, e^{−t}θ(t), прямоугольный импульс, гауссиана"
  (assert-true (trt-same? (trt-F '(exp (* -1 (abs t)))) '(/ 2 (+ 1 (^ w 2)))))
  (assert-true (trt-same? (trt-F '(exp (* -3 (abs t)))) '(/ 6 (+ 9 (^ w 2)))))
  (assert-true (trt-same? (trt-F '(* (exp (* -1 t)) (heaviside t))) '(/ 1 (+ 1 (* %i w)))))
  (assert-true (trt-same? (trt-F '(* (exp (* -2 t)) (heaviside t))) '(/ 1 (+ 2 (* %i w)))))
  (assert-true (trt-same? (trt-F '(- (heaviside (+ t 1)) (heaviside (- t 1)))) '(/ (* 2 (sin w)) w)))
  (assert-true (trt-same? (trt-F '(exp (* -1 (^ t 2)))) '(* (^ pi 1/2) (exp (* -1/4 (^ w 2))))))
  (assert-true (trt-same? (trt-F '(exp (* -4 (^ t 2)))) '(* 1/2 (^ pi 1/2) (exp (* -1/16 (^ w 2)))))))

(deftest "Фурье: δ, Лоренциан, cos/sin, константа, θ"
  (assert-true (trt-same? (trt-F '(dirac (- t 2))) '(exp (* -2 %i w))))
  (assert-true (trt-same? (trt-F '(/ 1 (+ 4 (^ t 2)))) '(* 1/2 pi (exp (* -2 (abs w))))))
  (assert-true (trt-same? (trt-F '(cos (* 3 t))) '(+ (* pi (dirac (- w 3))) (* pi (dirac (+ w 3))))))
  (assert-true (trt-same? (trt-F '(sin (* 3 t))) '(+ (* -1 %i pi (dirac (- w 3))) (* %i pi (dirac (+ w 3))))))
  (assert-true (trt-same? (trt-F 1) '(* 2 pi (dirac w))))
  (assert-true (trt-same? (trt-F '(heaviside t)) '(+ (* -1 %i (^ w -1)) (* pi (dirac w))))))

(deftest "Фурье: правила — сдвиг, масштаб, производная, модуляция, t·f, свёртка"
  (assert-true (trt-same? (trt-F '(f (- t 2))) '(* (exp (* -2 %i w)) (fourier (f t) t w))))
  (assert-true (trt-same? (trt-F '(f (* 3 t))) '(* 1/3 (fourier (f t) t (* 1/3 w)))))
  (assert-true (trt-same? (trt-F '(diff (f t) t)) '(* %i w (fourier (f t) t w))))
  (assert-true (trt-same? (trt-F '(* (exp (* -1 (abs t))) (cos (* 3 t))))
                          '(+ (/ 1 (+ 1 (^ (- w 3) 2))) (/ 1 (+ 1 (^ (+ w 3) 2))))))
  (assert-true (trt-same? (trt-F '(* t (exp (* -1 t)) (heaviside t))) '(^ (+ 1 (* %i w)) -2)))
  (assert-true (trt-same? (trt-F '(exp (* -1 (^ (- t 1) 2)))) '(* (^ pi 1/2) (exp (+ (* -1/4 (^ w 2)) (* -1 %i w))))))
  (assert-true (trt-same? (trt-F '(fourier-convolve (exp (* -1 (abs t))) (exp (* -1 (abs t))) t))
                          '(/ 4 (^ (+ 1 (^ w 2)) 2)))))

(deftest "Фурье: сертификат fourier-check"
  (assert-equal (fourier-check '(exp (* -1 (abs t))) '(/ 2 (+ 1 (^ w 2))) 't 'w) #t)
  (assert-equal (fourier-check '(* (exp (* -1 t)) (heaviside t)) '(/ 1 (+ 1 (* %i w))) 't 'w) #t)
  (assert-equal (fourier-check '(exp (* -1 (^ t 2))) '(* (^ pi 1/2) (exp (* -1/4 (^ w 2)))) 't 'w) 'numeric)
  (assert-equal (fourier-check '(- (heaviside (+ t 1)) (heaviside (- t 1))) '(/ (* 2 (sin w)) w) 't 'w) 'numeric)
  (assert-equal (fourier-check '(/ 1 (+ 1 (^ t 2))) '(* pi (exp (* -1 (abs w)))) 't 'w) 'numeric)
  (assert-equal (fourier-check '(dirac (- t 2)) '(exp (* -2 %i w)) 't 'w) 'numeric))

(deftest "Фурье: подделки — знак в экспоненте, масштаб, неверное a"
  (assert-equal (fourier-check '(* (exp (* -1 t)) (heaviside t)) '(/ 1 (- 1 (* %i w))) 't 'w) #f)
  (assert-equal (fourier-check '(exp (* -1 (abs t))) '(/ 4 (+ 1 (^ w 2))) 't 'w) #f)
  (assert-equal (fourier-check '(exp (* -1 (abs t))) '(/ 2 (+ 4 (^ w 2))) 't 'w) #f)
  (assert-equal (fourier-check '(exp (* -1 (^ t 2))) '(* (^ pi 1/2) (exp (* -1/2 (^ w 2)))) 't 'w) #f)
  (assert-equal (fourier-check '(dirac (- t 2)) '(exp (* 2 %i w)) 't 'w) #f)
  (assert-equal (fourier-check '(- (heaviside (+ t 1)) (heaviside (- t 1))) '(/ (* 2 (sin (* 2 w))) w) 't 'w) #f))

(deftest "Фурье: обратное — круг f → F → f для трёх функций"
  (assert-true (trt-same? (trt-iF (trt-F '(exp (* -1 (abs t))))) '(exp (* -1 (abs t)))))
  (assert-true (trt-same? (trt-iF (trt-F '(* (exp (* -1 t)) (heaviside t)))) '(* (exp (* -1 t)) (heaviside t))))
  (assert-true (trt-same? (trt-iF (trt-F '(exp (* -1 (^ t 2))))) '(exp (* -1 (^ t 2)))))
  (assert-true (trt-same? (trt-iF (trt-F '(dirac (- t 2)))) '(dirac (- t 2)))))

(deftest "Фурье: обратное рациональной F — полюса сверху и снизу, комплексные, кратные"
  (assert-true (trt-same? (trt-iF '(/ 1 (+ 4 (^ w 2)))) '(* 1/4 (exp (* -2 (abs t))))))
  (assert-true (trt-same? (trt-iF '(/ 1 (^ (+ 1 (* %i w)) 2))) '(* t (exp (* -1 t)) (heaviside t))))
  (let ((r (trt-iF '(/ 1 (+ 2 (* 2 w) (^ w 2))))))
    (assert-equal (fourier-check r '(/ 1 (+ 2 (* 2 w) (^ w 2))) 't 'w) #t))
  (let ((r (trt-iF '(/ 1 (^ (+ 1 (^ w 2)) 2)))))
    (assert-true (member? (fourier-check r '(/ 1 (^ (+ 1 (^ w 2)) 2)) 't 'w) '(#t numeric))))
  (let ((r (trt-iF '(/ w (+ 1 (^ w 2))))))
    (assert-true (member? (fourier-check r '(/ w (+ 1 (^ w 2))) 't 'w) '(#t numeric)))))

(deftest "Фурье: обратное по таблице (двойственность), сдвиг, невычисленное"
  (assert-true (trt-same? (trt-iF '(exp (* -1 (abs w)))) '(/ 1 (* pi (+ 1 (^ t 2))))))
  (assert-true (trt-same? (trt-iF '(exp (* -2 %i w))) '(dirac (- t 2))))
  (assert-true (trt-same? (trt-iF '(/ (exp (* -1 %i w)) (+ 1 (* %i w)))) '(* (exp (- 1 t)) (heaviside (- t 1)))))
  (assert-equal (car (fourier '(tan (* t t)) 't 'w)) 'fourier)
  (assert-equal (car (inverse-fourier '(tan (* w w)) 'w 't)) 'inverse-fourier))
