; intbasis.lisp — тесты шага A4.2: целый базис общей кривой (ван Хуй через Пюизё).

; сравнение элементов по значению
(define (ib-eq? a b) (equal? (simplify (together (list '- a b))) 0))

; кривые ТЗ
(define ib-cusp '(- (^ y 2) (^ x 3)))
(define ib-shift '(- (+ (^ y 2) (^ x 2)) (* 2 x y) (^ x 3)))
(define ib-folium '(- (^ y 3) (* 3 x y) (^ x 3)))
(define ib-quartic '(+ (- (^ y 4) (* (+ (* 4 x) 2) (^ y 2))) 1))
(define ib-char '(- (^ (- (^ y 2) (^ x 3)) 2) (^ x 7)))

; базисы считаем один раз; (y²−x³)²−x⁷ (≈ 1 мин) — bench/intbasis_slow.lisp
(define ib-b1 (integral-basis ib-cusp 'x 'y))
(define ib-b2 (integral-basis ib-shift 'x 'y))
(define ib-b3 (integral-basis ib-folium 'x 'y))
(define ib-b4 (integral-basis ib-quartic 'x 'y))

(deftest "intbasis: y² = x³ — базис {1, y/x}, сверка с A4.1a"
  (assert-equal 2 (length ib-b1))
  (assert-true (ib-eq? (nth ib-b1 0) '(/ y x)))
  (assert-true (ib-eq? (nth ib-b1 1) 1))
  ; A4.1a для y² = x³ даёт те же элементы
  (let ((rb (car (radical-integral-basis '(^ x 3) 2 'x))))
    (assert-true (ib-eq? (nth rb 1) (nth ib-b1 0))))
  (assert-equal #t (integral-basis-check-general ib-cusp 'x 'y ib-b1)))

(deftest "intbasis: сдвинутая каспида (y−x)² = x³"
  ; тот же модуль, что {1, (y−x)/x}: (y−x)/x = y/x − 1
  (assert-equal 2 (length ib-b2))
  (assert-true (ib-eq? (nth ib-b2 0) '(/ y x)))
  (assert-true (ib-eq? (nth ib-b2 1) 1))
  ; после A3.1d singular-points даёт δ = 1 — сертификат максимальности полный
  (assert-equal #t (integral-basis-check-general ib-shift 'x 'y ib-b2)))

(deftest "intbasis: y³ − 3xy + x³ (лист по y)"
  (assert-equal 3 (length ib-b3))
  (assert-true (ib-eq? (nth ib-b3 0) '(/ (^ y 2) x)))
  (assert-true (ib-eq? (nth ib-b3 1) 'y))
  (assert-true (ib-eq? (nth ib-b3 2) 1))
  (assert-equal #t (integral-basis-check-general ib-folium 'x 'y ib-b3)))

(deftest "intbasis: y⁴ − (4x+2)y² + 1 (y = √x + √(x+1)) — стандартный базис"
  (assert-equal 4 (length ib-b4))
  (assert-true (ib-eq? (nth ib-b4 0) '(^ y 3)))
  (assert-true (ib-eq? (nth ib-b4 1) '(^ y 2)))
  (assert-true (ib-eq? (nth ib-b4 3) 1))
  (assert-equal #t (integral-basis-check-general ib-quartic 'x 'y ib-b4)))

(deftest "intbasis: подделки базиса отвергаются"
  ; пропущен знаменатель x: y вместо y/x
  (assert-equal #f (integral-basis-check-general ib-cusp 'x 'y (list 'y 1)))
  ; лишний знаменатель: y/x² вместо y/x
  (assert-equal #f (integral-basis-check-general ib-cusp 'x 'y (list '(/ y (^ x 2)) 1)))
  (assert-true #t))

(deftest "intbasis: (y²−x³)² − x⁷ — базис, сертификат и подделка"
  (let ((b5 (integral-basis ib-char 'x 'y)))
    (assert-equal 4 (length b5))
    (assert-true (ib-eq? (nth b5 0) '(/ (- (^ y 3) (* (^ x 3) y)) (^ x 5))))
    (assert-true (ib-eq? (nth b5 1) '(/ (^ y 2) (^ x 3))))
    (assert-true (ib-eq? (nth b5 2) '(/ y x)))
    (assert-true (ib-eq? (nth b5 3) 1))
    (assert-equal #t (integral-basis-check-general ib-char 'x 'y b5))
    ; y²/x² вместо y²/x³ — знаменатель меньше нужного
    (assert-equal #f (integral-basis-check-general
                      ib-char 'x 'y
                      (list '(/ (- (^ y 3) (* (^ x 3) y)) (^ x 5))
                            '(/ (^ y 2) (^ x 2)) '(/ y x) 1)))))
