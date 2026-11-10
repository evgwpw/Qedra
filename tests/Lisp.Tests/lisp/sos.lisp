; sos.lisp — тесты шага SOS: неравенства многочленов, суммы квадратов, AM-GM, сертификаты

(define (sost-false x) (assert-true (not x)))
(define (sost-proved? r) (and (pair? r) (equal? (car r) 'proved)))
(define (sost-head r) (and (sost-proved? r) (car (cadr r))))
; доказано и сертификат проверяется независимо
(define (sost-ok? p vars r) (and (sost-proved? r) (sos-check p vars (cadr r))))

(define sost-p1 '(+ (^ x 2) (* -2 x) 1))
(define sost-p2 '(+ (^ x 4) (* -4 x) 3))
(define sost-p3 '(+ (^ x 6) (^ x 4) (* -2 (^ x 3)) 1))
(define sost-mo '(+ (* (^ x 4) (^ y 2)) (* (^ x 2) (^ y 4)) (* -3 (^ x 2) (^ y 2)) 1))
(define sost-q '(+ (^ x 2) (* -3 x) 2))

(deftest "один квадрат: x² − 2x + 1"
  (let ((r (prove-nonneg sost-p1 'x)))
    (assert-true (sost-ok? sost-p1 'x r))
    (assert-equal (sost-head r) 'sos)))

(deftest "x⁴ − 4x + 3 = (x−1)²(x²+2x+3)"
  (assert-true (sost-ok? sost-p2 'x (prove-nonneg sost-p2 'x))))

(deftest "x⁶ + x⁴ − 2x³ + 1 > 0"
  (assert-true (sost-ok? sost-p3 'x (prove-nonneg sost-p3 'x))))

(deftest "отрезок: x(1 − x) ≥ 0 на [0, 1]"
  (let ((r (prove-nonneg-on '(* x (+ 1 (* -1 x))) 'x 0 1)))
    (assert-true (sost-proved? r))
    (assert-equal (sost-head r) 'sos-on)
    (assert-true (sos-check '(* x (+ 1 (* -1 x))) 'x (cadr r)))))

(deftest "отрезок: 1 − x³ ≥ 0 на [0, 1] (нечётная степень)"
  (let ((r (prove-nonneg-on '(+ 1 (* -1 (^ x 3))) 'x 0 1)))
    (assert-true (sost-proved? r))
    (assert-true (sos-check '(+ 1 (* -1 (^ x 3))) 'x (cadr r)))))

(deftest "отрезок [−1, 1]: 1 − x⁴ и (x − 1/2)²(x + 1)"
  (assert-true (sost-proved? (prove-nonneg-on '(+ 1 (* -1 (^ x 4))) 'x -1 1)))
  (let ((p '(* (^ (+ x -1/2) 2) (+ x 1))))
    (assert-true (sost-ok? p 'x (prove-nonneg-on p 'x 0 1)))))

(deftest "отрезок: контрпример x − 1/2 на [0, 1]"
  (let ((r (prove-nonneg-on '(+ x -1/2) 'x 0 1)))
    (assert-equal (car r) 'counterexample)
    (assert-true (< (caddr r) 0))
    (assert-true (< (cadr (car (cadr r))) 1/2))))

(deftest "x² + y² − 2xy"
  (assert-true (sost-ok? '(+ (^ x 2) (^ y 2) (* -2 x y)) '(x y) (prove-nonneg '(+ (^ x 2) (^ y 2) (* -2 x y)) '(x y)))))

(deftest "x⁴ + y⁴ ≥ 2x²y²: AM-GM и Грам"
  (let* ((p '(+ (^ x 4) (^ y 4) (* -2 (^ x 2) (^ y 2))))
         (a (sos-amgm p '(x y)))
         (g (sos-decompose p '(x y))))
    (assert-equal (sost-head a) 'amgm)
    (assert-true (sost-ok? p '(x y) a))
    (assert-equal (sost-head g) 'sos)
    (assert-true (sost-ok? p '(x y) g))))

(deftest "x² + y² + z² ≥ xy + yz + zx: Грам (LDLᵀ) и AM-GM"
  (let ((p '(+ (^ x 2) (^ y 2) (^ z 2) (* -1 x y) (* -1 y z) (* -1 z x))))
    (assert-true (sost-ok? p '(x y z) (sos-decompose p '(x y z))))
    (assert-true (sost-ok? p '(x y z) (sos-amgm p '(x y z))))))

(deftest "Motzkin: не SOS (Грам — unknown), но AM-GM доказывает"
  (assert-equal (sos-decompose sost-mo '(x y)) 'unknown)
  (let ((r (prove-nonneg sost-mo '(x y))))
    (assert-equal (sost-head r) 'amgm)
    (assert-true (sost-ok? sost-mo '(x y) r))))

(deftest "(x² + y² − 1)² — Грам с редукцией грани"
  (let ((p '(^ (+ (^ x 2) (^ y 2) -1) 2)))
    (assert-true (sost-ok? p '(x y) (sos-decompose p '(x y))))))

(deftest "Грам с параметрами: (x² + xy − 1)² + (y² − x)² + 1"
  (let ((p '(+ (^ (+ (^ x 2) (* x y) -1) 2) (^ (+ (^ y 2) (* -1 x)) 2) 1)))
    (assert-true (sost-ok? p '(x y) (sos-decompose p '(x y))))))

(deftest "квадратичная форма x² + 2xy + 3y²"
  (let ((p '(+ (^ x 2) (* 2 x y) (* 3 (^ y 2)))))
    (assert-true (sost-ok? p '(x y) (sos-decompose p '(x y))))))

(deftest "контрпример: x² − 3x + 2 < 0 на (1, 2)"
  (let ((r (prove-nonneg sost-q 'x)))
    (assert-equal (car r) 'counterexample)
    (let ((x0 (cadr (car (cadr r)))))
      (assert-true (< 1 x0)) (assert-true (< x0 2))
      (assert-equal (caddr r) (+ (* x0 x0) (* -3 x0) 2))
      (assert-true (< (caddr r) 0)))))

(deftest "контрпримеры: x³, x² − y, дробные коэффициенты 0.9"
  (assert-equal (car (prove-nonneg '(^ x 3) 'x)) 'counterexample)
  (let ((r (prove-nonneg '(+ (^ x 2) (* -1 y)) '(x y))))
    (assert-equal (car r) 'counterexample)
    (assert-true (< (caddr r) 0)))
  (assert-equal (car (prove-nonneg '(+ (^ x 2) (* -2 x) 9/10) 'x)) 'counterexample))

(deftest "константы и нулевой многочлен"
  (assert-true (sost-ok? 5 'x (prove-nonneg 5 'x)))
  (assert-true (sost-ok? 0 'x (prove-nonneg 0 'x)))
  (assert-equal (car (prove-nonneg -2 'x)) 'counterexample))

(deftest "sos-check: подделки (sos)"
  (let ((good (cadr (prove-nonneg sost-p1 'x))))
    (assert-true (sos-check sost-p1 'x good))
    ; не хватает слагаемого
    (sost-false (sos-check '(+ (^ x 2) (* -2 x) 1 (^ y 2)) '(x y) good))
    (sost-false (sos-check sost-p1 'x '(sos)))
    ; отрицательный и нулевой вес
    (sost-false (sos-check '(+ (* -1 (^ x 2)) (* 2 x) -1) 'x '(sos (-1 (+ x -1)))))
    (sost-false (sos-check sost-p1 'x '(sos (0 (+ x -1)))))
    ; комплексный квадрат и вещественный (float) вес
    (sost-false (sos-check '(+ (^ x 2) 1) 'x '(sos (1 (* %i (+ x 1))))))
    (sost-false (sos-check sost-p1 'x '(sos (1.0 (+ x -1)))))
    ; чужая форма
    (sost-false (sos-check sost-p1 'x 'proved))
    (sost-false (sos-check sost-p1 'x '(foo (1 x))))))

(deftest "sos-check: «доказательство» для знакопеременного многочлена"
  ; x² − 3x + 2 = (x − 3/2)² − 1/4: вес −1/4 запрещён, а положительные веса не сходятся
  (sost-false (sos-check sost-q 'x '(sos (1 (+ x -3/2)) (-1/4 1))))
  (sost-false (sos-check sost-q 'x '(sos (1 (+ x -3/2)) (1/4 1)))))

(deftest "sos-check: подделки (sos-on и amgm)"
  (let ((p '(* x (+ 1 (* -1 x)))))
    (assert-true (sos-check p 'x '(sos-on 0 1 (1 1 (1 1)))))
    ; множитель x(1−x) на всей прямой отрицателен, но на [0,1] допустим только с nat-степенями
    (sost-false (sos-check p 'x '(sos-on 0 1 (-1 1 (1 1)))))
    (sost-false (sos-check p 'x '(sos-on 0 1 (1 1 (-1 1)))))
    (sost-false (sos-check p 'x '(sos-on 0 1 (1 1 (2 1)))))
    ; перепутаны концы
    (sost-false (sos-check p 'x '(sos-on 1 0 (1 1 (1 1))))))
  (let ((p '(+ (^ x 4) (^ y 4) (* -2 (^ x 2) (^ y 2)))))
    (assert-true (sos-check p '(x y) '(amgm (2 (2 2) ((1/2 (4 0)) (1/2 (0 4)))))))
    ; веса не дают 1
    (sost-false (sos-check p '(x y) '(amgm (2 (2 2) ((1/3 (4 0)) (1/3 (0 4)))))))
    ; отрицательный вес
    (sost-false (sos-check p '(x y) '(amgm (2 (2 2) ((3/2 (4 0)) (-1/2 (0 4)))))))
    ; Σ w·a ≠ e
    (sost-false (sos-check p '(x y) '(amgm (2 (2 2) ((1/2 (4 0)) (1/2 (4 0)))))))
    ; нет покрытия отрицательного члена
    (sost-false (sos-check p '(x y) '(amgm)))
    ; нечётный показатель в положительной части
    (sost-false (sos-check '(+ x (* -1 y)) '(x y) '(amgm (1 (0 1) ((1 (1 0)))))))
    ; перерасход коэффициента: -3x²y² покрыт, но x⁴, y⁴ только по 1
    (sost-false (sos-check '(+ (^ x 4) (^ y 4) (* -3 (^ x 2) (^ y 2))) '(x y)
                             '(amgm (3 (2 2) ((1/2 (4 0)) (1/2 (0 4)))))))))

(deftest "prove-nonneg: плохой вход — unknown, не ошибка"
  (assert-equal (prove-nonneg '(sin x) 'x) 'unknown)
  (assert-equal (prove-nonneg '(+ (* 0.5 x) 1) 'x) 'unknown))
