; diophantine.lisp — тесты шага NT.2: диофантовы уравнения с сертификатами.
; Подделки (неверная пара Пелля, неверное представление, неверное k, ложный вектор-сертификат) должны отвергаться.

(define (dtt-sum-sq l) (foldl (lambda (acc x) (+ acc (* x x))) 0 l))

; ---------- линейное уравнение ----------

(deftest "dioph-linear: общее решение при нескольких t"
  (let* ((r (dioph-linear 6 9 12))
         (x0 (car (car r))) (y0 (cadr (car r)))
         (dx (car (cadr r))) (dy (cadr (cadr r))))
    (assert-true (every? (lambda (t) (= (+ (* 6 (+ x0 (* dx t))) (* 9 (+ y0 (* dy t)))) 12))
                         '(-5 -1 0 1 2 17)))
    (assert-equal (gcd (abs dx) (abs dy)) 1)))

(deftest "dioph-linear: нет решений — сертификат НОД"
  (assert-equal (dioph-linear 6 9 7) '(none 3))
  (assert-equal (dioph-linear 0 0 5) '(none 0))
  (assert-equal (dioph-linear 0 0 0) '(all))
  (assert-error (dioph-linear 1/2 3 4)))

; ---------- системы ----------

(deftest "dioph-linear-system: решение и базис решётки"
  (let* ((A '((2 3 1) (4 6 5))) (b '(5 13))
         (r (dioph-linear-system A b)))
    (assert-true (dioph-linear-system-check A b r))
    (assert-equal (length (cadr r)) 1)
    ; сдвиг на базис решётки — снова решение
    (let ((x (map2 + (car r) (map (lambda (v) (* 3 v)) (car (cadr r))))))
      (assert-equal (map (lambda (row) (foldl (lambda (acc p) (+ acc p)) 0 (map2 * row x))) A) b))))

(deftest "dioph-linear-system: одно уравнение, два базисных вектора"
  (let* ((A '((3 5 7))) (r (dioph-linear-system A '(1))))
    (assert-true (dioph-linear-system-check A '(1) r))
    (assert-equal (length (cadr r)) 2)))

(deftest "dioph-linear-system: вырожденная система с решением"
  (let* ((A '((1 2 3) (4 5 6) (7 8 9))) (r (dioph-linear-system A '(6 15 24))))
    (assert-true (dioph-linear-system-check A '(6 15 24) r))
    (assert-equal (length (cadr r)) 1)))

(deftest "dioph-linear-system: нет решений — вектор-сертификат"
  (let* ((A '((2 3 1) (4 6 5))) (r (dioph-linear-system A '(5 11))))
    (assert-equal (car r) 'none)
    (assert-true (dioph-linear-system-check A '(5 11) r))
    ; нечётная сумма: 2x + 4y = 3
    (assert-equal (car (dioph-linear-system '((2 4)) '(3))) 'none)
    ; над ℚ решение есть, над ℤ нет: x + y = 1, x − y = 0
    (assert-equal (car (dioph-linear-system '((1 1) (1 -1)) '(1 0))) 'none)))

(deftest "dioph-linear-system: подделки отвергаются"
  (let ((A '((2 3 1) (4 6 5))))
    (assert-equal (dioph-linear-system-check A '(5 11) '(none (1 0))) #f)         ; wᵀb целое
    (assert-equal (dioph-linear-system-check A '(5 11) '(none (1/2 0))) #f)       ; wᵀA не целое
    (assert-equal (dioph-linear-system-check A '(5 13) '((0 0 0) ())) #f)         ; не решение
    (assert-equal (dioph-linear-system-check A '(5 13) '((-4 4 1) ((1 0 0)))) #f) ; не нулевой вектор решётки
    (assert-true (dioph-linear-system-check A '(5 13) '((-4 4 1) ((3 -2 0)))))))

; ---------- Пелль ----------

(deftest "Пелль: d = 2, 61, 109 (точный bignum)"
  (assert-equal (pell 2) '(3 2))
  (assert-equal (pell 61) '(1766319049 226153980))
  (assert-equal (pell 109) '(158070671986249 15140424455100)))

(deftest "Пелль: отрицательное — период нечётен или отказ с чётным периодом"
  (assert-equal (dioph-pell-negative 13) '(18 5))
  (assert-equal (dioph-pell-negative 61) '(29718 3805))
  (assert-equal (dioph-pell-negative 3) '(none even-period 2))
  (assert-equal (sqrt-cf-period 61) 11)
  (assert-equal (sqrt-cf-period 13) 5))

(deftest "Пелль: обобщённое x² − D·y² = N"
  (assert-equal (dioph-pell 2 7) '((-3 1) (3 1)))
  (assert-equal (dioph-pell 5 4) '((-3 1) (-2 0) (2 0) (3 1)))
  (assert-equal (dioph-pell 3 5) '(none 1))                  ; 5 не норма: перебор завершён
  (assert-equal (dioph-pell 109 -1) '((-8890182 851525) (8890182 851525)))
  (assert-equal (dioph-pell 3 -1) '(none 2))
  (assert-equal (dioph-pell 16 20) '((-6 -1) (-6 1) (6 -1) (6 1)))   ; D — квадрат: конечный список
  (assert-equal (dioph-pell -3 7) '((-2 -1) (-2 1) (2 -1) (2 1)))
  (assert-equal (car (dioph-pell 109 3)) 'unknown))          ; граница выше предела перебора — честное «не знаю»

; ---------- суммы квадратов ----------

(deftest "two-squares: все представления"
  (assert-equal (two-squares 25) '((5 0) (4 3)))
  (assert-equal (two-squares 325) '((18 1) (17 6) (15 10)))
  (assert-equal (two-squares 0) '((0 0)))
  (assert-equal (length (two-squares 5525)) 6)
  (assert-true (every? (lambda (p) (= (dtt-sum-sq p) 5525)) (two-squares 5525))))

(deftest "two-squares: отказ — простое 3 mod 4 в нечётной степени"
  (assert-equal (two-squares 21) '(none 3))
  (assert-equal (two-squares 14) '(none 7))
  (assert-equal (two-squares -4) '(none -1))
  (assert-equal (two-squares 441) '((21 0))))

(deftest "four-squares и three-squares"
  (let ((r (four-squares 7000001)))
    (assert-equal (dtt-sum-sq r) 7000001)
    (assert-equal (length r) 4))
  (assert-equal (four-squares 7) '(2 1 1 1))
  (assert-equal (four-squares 0) '(0 0 0 0))
  (assert-equal (dtt-sum-sq (three-squares 1000001)) 1000001)
  (assert-equal (three-squares 14) '(3 2 1))
  (assert-equal (three-squares 28) '(none legendre 1 7))
  (assert-equal (three-squares 7) '(none legendre 0 7))
  (assert-equal (three-squares 448) '(none legendre 3 7)))

(deftest "пифагоровы тройки с заданной гипотенузой и катетом"
  (assert-equal (pythagorean-hypotenuse 25) '((7 24 25) (15 20 25)))
  (assert-equal (pythagorean-hypotenuse 65) '((16 63 65) (25 60 65) (33 56 65) (39 52 65)))
  (assert-equal (pythagorean-hypotenuse 3) '())
  (assert-equal (pythagorean-leg 12) '((12 5 13) (12 9 15) (12 16 20) (12 35 37)))
  (assert-equal (pythagorean-leg 2) '())
  (assert-true (every? (lambda (t) (= (+ (* (car t) (car t)) (* (cadr t) (cadr t)) ) (* (caddr t) (caddr t))))
                       (pythagorean-leg 60))))

; ---------- дискретный логарифм ----------

(deftest "discrete-log: p = 1000003"
  (let ((k (discrete-log 5 17 1000003)))
    (assert-equal k 983559)
    (assert-equal (powmod 5 k 1000003) 17))
  (assert-equal (discrete-log 2 1 7) 0)
  (assert-equal (powmod 2 (discrete-log 2 5 1009) 1009) 5))

(deftest "discrete-log: гладкий p − 1 и большой модуль, составной модуль, отказ"
  (let ((k (discrete-log 5 12345 1000000007)))
    (assert-equal (powmod 5 k 1000000007) 12345))
  (let ((k (discrete-log 3 13 17))) (assert-equal (powmod 3 k 17) 13))
  (assert-equal (discrete-log 2 3 7) '(none not-in-subgroup))
  (assert-equal (discrete-log 2 3 8) '(none not-unit))
  (let ((k (discrete-log 2 5 (* 3 1009)))) (assert-equal (if (integer? k) (powmod 2 k 3027) 5) 5)))

(deftest "multiplicative-order"
  (assert-equal (multiplicative-order 5 1000003) 1000002)
  (assert-equal (multiplicative-order 2 7) 3))

; ---------- dioph-check ----------

(deftest "dioph-check: верные решения"
  (assert-true (dioph-check '(= (- (^ x 2) (* 61 (^ y 2))) 1) '(x y) '(1766319049 226153980)))
  (assert-true (dioph-check '(= (+ (* 6 x) (* 9 y)) 12) '(x y) '(2 0)))
  (assert-true (dioph-check '(= (+ (^ a 2) (^ b 2)) 325) '(a b) '(18 1)))
  (assert-true (dioph-check '(= (powmod 5 k 1000003) 17) '(k) (list (discrete-log 5 17 1000003))))
  (assert-true (dioph-check '(congruent (^ 2 k) 8 11) '(k) '(3)))
  (assert-true (dioph-check '(- (^ x 2) (* 2 (^ y 2)) 7) '(x y) '(3 1))))

(deftest "dioph-check: подделки отвергаются"
  (assert-equal (dioph-check '(= (- (^ x 2) (* 61 (^ y 2))) 1) '(x y) '(1766319049 226153981)) #f)
  (assert-equal (dioph-check '(= (+ (^ a 2) (^ b 2)) 325) '(a b) '(18 2)) #f)
  (assert-equal (dioph-check '(= (powmod 5 k 1000003) 17) '(k) '(983560)) #f)
  (assert-equal (dioph-check '(= (+ x y) 3) '(x y) '(1/2 5/2)) #f)           ; решение нецелое
  (assert-equal (dioph-check '(= (+ x y) 3) '(x y) '(1)) #f)                  ; не хватает значений
  (assert-equal (dioph-check '(= (+ x z) 3) '(x y) '(1 2)) #f))               ; лишняя переменная
