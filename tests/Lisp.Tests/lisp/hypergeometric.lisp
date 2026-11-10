; hypergeometric.lisp — SF.HYP: ₂F₁ и F₁ Аппеля (hypergeometric-2f1, appell-f1): значения, производные, частные случаи, int-check.
; Эталоны — элементарные замкнутые формы (DLMF 15.4) и независимый двойной ряд; крючок eval-num — define-numeric.

; загрузка модуля specfun (крючок define-numeric выполняется при загрузке)
(define hg-loaded (hypergeometric-2f1 1 1 2 'z))

(define (hg-close? a b tol) (and (number? a) (number? b) (<= (abs (- a b)) (* tol (max 1.0 (abs b))))))
(define (hg-at e x0) (eval-num (subst (list (list 'x x0)) e)))
(define (hg-h a b c z) (hypergeometric-2f1-num a b c z))

; пятиточечная центральная разность, h = 1e-3
(define (hg-nderiv e x0)
  (let ((h 0.001))
    (/ (+ (* -1 (hg-at e (+ x0 (* 2 h)))) (* 8 (hg-at e (+ x0 h))) (* -8 (hg-at e (- x0 h))) (hg-at e (- x0 (* 2 h))))
       (* 12 h))))
(define (hg-deriv-ok? e xs)
  (every? (lambda (x0) (hg-close? (hg-at (diff 'x e) x0) (hg-nderiv e x0) 1e-7)) xs))

(deftest "SF.HYP: z = 0.5, 0.25, ряд — эталоны 2 ln 2, 2 asin(1/2)"
  (assert-true (hg-close? (hg-h 1.0 1.0 2.0 0.5) (* 2 (log 2.0)) 1e-12))
  (assert-true (hg-close? (hg-h 0.5 0.5 1.5 0.25) (* 2 (eval-num '(asin 0.5))) 1e-12))
  ; через крючок eval-num (голова с точными аргументами)
  (assert-true (hg-close? (eval-num '(hypergeometric-2f1 1 1 2 1/2)) (* 2 (log 2.0)) 1e-12))
  (assert-true (hg-close? (eval-num (hypergeometric-2f1 1/2 1/2 3/2 1/4)) (* 2 (eval-num '(asin 0.5))) 1e-12)))

(deftest "SF.HYP: z = 1 — Гаусс; z у единицы — связь с 1−z (DLMF 15.8.4)"
  (let ((a 0.3) (b 0.4) (c 2.1))
    (assert-true (hg-close? (hg-h a b c 1.0)
                            (/ (* (eval-num (list 'gamma c)) (eval-num (list 'gamma (- c a b))))
                               (* (eval-num (list 'gamma (- c a))) (eval-num (list 'gamma (- c b))))) 1e-12))
    ; около 1: преобразование против прямого ряда (z = 0.92, ряд ещё быстрый) и против Гаусса в пределе
    (assert-true (hg-close? (hg-h a b c 0.92) (specfun::sf-h-series a b c 0.92) 1e-12))
    (assert-true (hg-close? (hg-h a b c 0.999999) (hg-h a b c 1.0) 1e-3)))
  ; asin z / z при z² близком к 1
  (assert-true (hg-close? (hg-h 0.5 0.5 1.5 0.9801) (/ (eval-num '(asin 0.99)) 0.99) 1e-12))
  ; расходимость (c−a−b ≤ 0) и ветвь z > 1 — отказ
  (assert-true (not (hg-h 1.0 1.0 2.0 1.0)))
  (assert-true (not (hg-h 1.0 1.0 2.0 1.5))))

(deftest "SF.HYP: z < −0.9 — Пфафф 15.8.1 и 15.8.2 против элементарных форм"
  (assert-true (hg-close? (hg-h 1.0 1.0 2.0 -2.0) (/ (log 3.0) 2.0) 1e-12))
  (assert-true (hg-close? (hg-h 1.0 1.0 2.0 -10.0) (/ (log 11.0) 10.0) 1e-12))
  (assert-true (hg-close? (hg-h 0.5 0.5 1.5 -50.0) (/ (eval-num '(asinh 7.0710678118654755)) 7.0710678118654755) 1e-12))
  ; нецелое a−b, z = −100, −1000: DLMF 15.8.2 (1/z)
  (assert-true (hg-close? (hg-h 0.5 1.0 1.5 -100.0) (/ (eval-num '(atan 10.0)) 10.0) 1e-12))
  (assert-true (hg-close? (hg-h 0.5 1.0 1.5 -1000.0) (/ (eval-num '(atan 31.622776601683793)) 31.622776601683793) 1e-12))
  ; целое a−b и очень большое |z| — честный отказ
  (assert-true (not (hg-h 1.0 1.0 2.0 -1000.0))))

(deftest "SF.HYP: многочлен (a = −n), (1−z)^(−a) при c = b, комплексный z"
  (let ((ex (eval-num (hyper-series '(hyper (-3 5/2) (3/2) 7) 3))))
    (assert-true (hg-close? (hg-h -3.0 2.5 1.5 7.0) ex 1e-12)))
  (assert-true (hg-close? (hg-h 0.3 1.7 1.7 0.6) (eval-num '(^ 0.4 -0.3)) 1e-12))
  ; ₂F₁(1,1;2;z) = −ln(1−z)/z при z = 0.3 + 0.2i
  (let ((v (eval-num '(hypergeometric-2f1 1 1 2 (+ 3/10 (* 1/5 %i)))))
        (r (eval-num '(* -1 (^ (+ 3/10 (* 1/5 %i)) -1) (log (+ 7/10 (* -1/5 %i)))))))
    (assert-true (< (num-abs (list '- v r)) 1e-13)))
  ; c — целое ≤ 0: не определено
  (assert-true (not (hg-h 1.0 1.0 -1.0 0.5))))

(deftest "SF.HYP: символьные частные значения (DLMF 15.4)"
  (assert-equal (hypergeometric-2f1 'a 'b 'c 0) 1)
  (assert-true (equal? (simplify (list '- (hypergeometric-2f1 1 1 2 'z) '(* -1 (^ z -1) (log (+ 1 (* -1 z)))))) 0))
  (assert-true (equal? (simplify (list '- (hypergeometric-2f1 'a 'b 'b 'z) '(^ (+ 1 (* -1 z)) (* -1 a)))) 0))
  (assert-true (equal? (simplify (list '- (hypergeometric-2f1 -2 'b 1/2 'z)
                                       (hyper-series '(hyper (-2 b) (1/2) z) 2))) 0))
  (let ((r (hypergeometric-2f1 1/2 1/2 3/2 '(^ w 2))))
    (assert-true (contains-sym? r 'asin)))
  ; общий случай — голова остаётся
  (assert-equal (hypergeometric-2f1 1/3 1/2 5/4 'z) '(hypergeometric-2f1 1/3 1/2 5/4 z))
  (assert-equal (math-print '(hypergeometric-2f1 1/3 1/2 5/4 z)) "Hypergeometric2F1(1/3, 1/2, 5/4, z)")
  (assert-equal (math-latex '(hypergeometric-2f1 a b c z)) "{}_2F_1\\left(a, b; c; z\\right)")
  (assert-equal (math-latex '(appell-f1 a p q c x y)) "F_1\\left(a; p, q; c; x, y\\right)"))

(deftest "SF.HYP: производная ₂F₁ — разность (5 точек)"
  (assert-true (hg-deriv-ok? '(hypergeometric-2f1 1/2 1/3 5/4 x) '(-0.8 -0.3 0.2 0.5 0.8)))
  ; цепное правило, отрицательные z (Пфафф), параметры без x
  (assert-true (hg-deriv-ok? '(hypergeometric-2f1 1/2 1/3 5/4 (* 2 x)) '(-0.4 -0.1 0.1 0.3 0.4)))
  (assert-true (hg-deriv-ok? '(hypergeometric-2f1 2/3 3/2 7/3 (* -3 x)) '(0.4 0.9 1.5 2.5 4.0)))
  ; ошибочная формула (без множителя ab/c) ловится
  (assert-true (not (hg-close? (hg-at '(hypergeometric-2f1 3/2 4/3 9/4 x) 0.5) (hg-nderiv '(hypergeometric-2f1 1/2 1/3 5/4 x) 0.5) 1e-7)))
  ; параметр зависит от x — невычисленная производная, не 0
  (assert-true (contains-sym? (diff 'x '(hypergeometric-2f1 x 1/3 5/4 x)) 'diff)))

; независимый двойной ряд: члены по определению через Pochhammer, суммирование по m, n ≤ N
(define (hg-appell-series a b1 b2 c x y n)
  (let outer ((nn 0) (tot 0.0))
    (if (> nn n)
        tot
        (let inner ((mm 0) (acc 0.0))
          (if (> mm n)
              (outer (+ nn 1) (+ tot acc))
              (let ((term (/ (* (hg-poch a (+ mm nn)) (hg-poch b1 mm) (hg-poch b2 nn) (^ x mm) (^ y nn))
                             (* (hg-poch c (+ mm nn)) (hg-fact mm) (hg-fact nn)))))
                (inner (+ mm 1) (+ acc term))))))))
(define (hg-poch a k) (let loop ((i 0) (p 1.0)) (if (>= i k) p (loop (+ i 1) (* p (+ a i))))))
(define (hg-fact k) (let loop ((i 2) (p 1.0)) (if (> i k) p (loop (+ i 1) (* p i)))))

(deftest "SF.HYP: AppellF1 — частные случаи против ₂F₁ и двойной ряд"
  (let ((a 1.2) (b1 0.5) (b2 0.7) (c 2.0))
    (assert-true (hg-close? (appell-f1-num a b1 b2 c 0.3 0.0) (hg-h a b1 c 0.3) 1e-13))
    (assert-true (hg-close? (appell-f1-num a b1 b2 c 0.0 0.4) (hg-h a b2 c 0.4) 1e-13))
    (assert-true (hg-close? (appell-f1-num a b1 b2 c 0.3 0.3) (hg-h a (+ b1 b2) c 0.3) 1e-13))
    (assert-true (hg-close? (appell-f1-num a b1 b2 c 0.3 -0.4) (hg-appell-series a b1 b2 c 0.3 -0.4 45) 1e-12))
    (assert-true (hg-close? (appell-f1-num a b1 b2 c 0.4 0.5) (hg-appell-series a b1 b2 c 0.4 0.5 55) 1e-12))
    ; вне области |x|, |y| ≤ 0.9 — отказ
    (assert-true (not (appell-f1-num a b1 b2 c 0.95 0.1))))
  ; символьные частные случаи
  (assert-equal (appell-f1 1 1/2 1/3 5/4 'x 0) (hypergeometric-2f1 1 1/2 5/4 'x))
  (assert-equal (appell-f1 1 1/2 1/3 5/4 0 'y) (hypergeometric-2f1 1 1/3 5/4 'y))
  (assert-equal (appell-f1 1 1/2 1/3 5/4 'x 'x) (hypergeometric-2f1 1 5/6 5/4 'x))
  (assert-equal (appell-f1 1 1/2 1/3 5/4 'x 'y) '(appell-f1 1 1/2 1/3 5/4 x y))
  (assert-equal (math-print '(appell-f1 1 1/2 1/3 5/4 x y)) "AppellF1(1, 1/2, 1/3, 5/4, x, y)")
  ; eval-num головы с точными аргументами
  (assert-true (hg-close? (eval-num '(appell-f1 1 1/2 1/3 5/4 3/10 2/5))
                          (hg-appell-series 1.0 0.5 (/ 1.0 3.0) 1.25 0.3 0.4 45) 1e-12)))

(deftest "SF.HYP: производные AppellF1 — разность"
  (assert-true (hg-deriv-ok? '(appell-f1 1 1/2 1/3 5/4 x (* x x)) '(0.2 0.5 0.7)))
  (assert-true (hg-deriv-ok? '(appell-f1 1/2 1/2 1/3 7/4 (* 3/2 x) 1/4) '(-0.3 0.2 0.5))))

(deftest "SF.HYP: int-check ∫ x^m (1+x)^n dx = x^(m+1)/(m+1) · ₂F₁(−n, m+1; m+2; −x)"
  (let ((e '(* (^ x m) (^ (+ 1 x) n)))
        (F '(* (^ x (+ m 1)) (^ (+ m 1) -1) (hypergeometric-2f1 (* -1 n) (+ m 1) (+ m 2) (* -1 x)))))
    (assert-true (int-check F e 'x))
    ; подделка (неверный множитель) ловится
    (assert-true (not (int-check '(* (^ x (+ m 1)) (hypergeometric-2f1 (* -1 n) (+ m 1) (+ m 2) (* -1 x))) e 'x)))
    ; дробные показатели: ∫ x^(1/3)/√(1+x)
    (assert-true (int-check '(* (^ x 4/3) 3/4 (hypergeometric-2f1 1/2 4/3 7/3 (* -1 x))) '(* (^ x 1/3) (^ (+ 1 x) -1/2)) 'x))))
