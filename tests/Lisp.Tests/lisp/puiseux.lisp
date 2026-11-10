; puiseux.lisp — тесты модуля puiseux (21m A2.1): ряды Ньютона–Пюизё

; ---------- многоугольник Ньютона ----------

(deftest "newton-polygon: y² − x³ — одно ребро (0,2)→(3,0)"
  (assert-equal (newton-polygon '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y)
                '((0 2 3 0 2 3))))

(deftest "newton-polygon: y³ − x²y − x⁵ — два ребра"
  (assert-equal (length (newton-polygon '(+ (^ y 3) (* -1 (* (^ x 2) y)) (* -1 (^ x 5))) 'x 'y)) 2))

(deftest "newton-polygon: F(0,y) ≠ 0 с F(0,0)≠0 — рёбер нет"
  (assert-equal (newton-polygon '(+ (^ y 2) (* -1 x) 1) 'x 'y) '()))

; ---------- puiseux: базовые примеры ----------

(deftest "puiseux: y² − x³ — ветви ±x^{3/2}, q=2"
  (define bs (puiseux '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y 3))
  (assert-true (= (length bs) 2))
  (assert-true (every? (lambda (b) (= (nth b 0) 2)) bs))
  (assert-true (member? (puiseux-terms (nth bs 0)) '(((1 3/2)) (((-1 3/2))))))
  (assert-true (every? (lambda (b) (puiseux-check '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y b 3)) bs)))

(deftest "puiseux: y² − x²(1+x) — гладкие ветви ±(x + x²/2 − x³/8)"
  (define F '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))))
  (define bs (puiseux F 'x 'y 4))
  (assert-true (= (length bs) 2))
  (assert-equal (puiseux-terms (nth bs 0)) '((1 1) (1/2 2) (-1/8 3) (1/16 4)))
  (assert-equal (puiseux-terms (nth bs 1)) '((-1 1) (-1/2 2) (1/8 3) (-1/16 4)))
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 4)) bs)))

(deftest "puiseux: y³ − x — три ветви ωᵏ·x^{1/3}, q=3"
  (define bs (puiseux '(+ (^ y 3) (* -1 x)) 'x 'y 3))
  (assert-true (= (length bs) 3))
  (assert-true (every? (lambda (b) (= (nth b 0) 3)) bs))
  (assert-true (every? (lambda (b) (puiseux-check '(+ (^ y 3) (* -1 x)) 'x 'y b 3)) bs)))

(deftest "puiseux: y² − 2x² — коэффициенты ±√2"
  (define bs (puiseux '(+ (^ y 2) (* -2 (^ x 2))) 'x 'y 3))
  (assert-true (= (length bs) 2))
  (assert-equal (puiseux-terms (nth bs 0)) '(((^ 2 1/2) 1)))
  (assert-equal (puiseux-terms (nth bs 1)) '(((* -1 (^ 2 1/2)) 1))))

(deftest "puiseux: (y − x)² − x³ — ветви x ± x^{3/2}"
  (define F '(+ (* -1 (^ x 3)) (^ (- y x) 2)))
  (define bs (puiseux F 'x 'y 4))
  (assert-true (= (length bs) 2))
  (assert-equal (puiseux-terms (nth bs 0)) '((1 1) (1 3/2)))
  (assert-equal (puiseux-terms (nth bs 1)) '((1 1) (-1 3/2)))
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 4)) bs)))

(deftest "puiseux: y² + x² — комплексные ветви ±ix"
  (define bs (puiseux '(+ (^ y 2) (^ x 2)) 'x 'y 3))
  (assert-true (= (length bs) 2))
  (assert-true (every? (lambda (b) (puiseux-check '(+ (^ y 2) (^ x 2)) 'x 'y b 3)) bs)))

; ДЕФЕКТ A2.1 ИСПРАВЛЕН (A2.2): px-regular-series считал позицию нового члена относительно текущей
; сдвинутой координаты z, а не абсолютную позицию в ряду (shift+k) — показатели хвоста съезжали.
(deftest "puiseux: y³ − x²y − x⁵ — несколько рёбер: все ветви, сумма q = 3, проходят check"
  (define F '(+ (^ y 3) (* -1 (* (^ x 2) y)) (* -1 (^ x 5))))
  (define bs (puiseux F 'x 'y 6))
  (assert-equal (length bs) 3)
  (assert-equal (foldl + 0 (map (lambda (b) (nth b 0)) bs)) 3)
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 6)) bs))
  (define b2 (nth bs 1))
  (assert-equal (puiseux-terms b2) '((1 1) (1/2 3) (-3/8 5)))
  ; подделка с прежним дефектным показателем по-прежнему ловится
  (assert-equal #f (puiseux-check F 'x 'y '(1 ((1 1) (1/2 3) (-3/8 4))) 4)))

; численная сверка: y − ряд ≈ 0 в нескольких точках x (ряд ветви b2 = x + x³/2 − 3/8·x⁵)
(deftest "puiseux: y³ − x²y − x⁵ — численная сверка ветви x + x³/2 − 3/8·x⁵"
  (define F '(+ (^ y 3) (* -1 (* (^ x 2) y)) (* -1 (^ x 5))))
  (define bs (puiseux F 'x 'y 6))
  (define b2 (nth bs 1))
  (define (num-at x)
    (let ((r (eval-num (simplify (subst (list 'x x)
                   (subst (list 'y (cons '+ (map (lambda (tm)
                                                    (list '* (nth tm 0) (list '^ 'x (nth tm 1))))
                                                  (puiseux-terms b2)))) F))))))
      (if (and (number? r) (< (abs r) 1e-6)) r 0)))
  (assert-true (< (abs (num-at 1/20)) 1e-6))
  (assert-true (< (abs (num-at 1/10)) 1e-6))
  (assert-true (< (abs (num-at 1/8)) 1e-6)))

; A2.2: дополнительные кривые с двумя и более шагами Ньютона.
; (y−x)² − x⁵(1+x)²: y = x ± x^{5/2}(1+x) — шаг Ньютона q=2 + регулярный хвост
(deftest "puiseux: (y−x)² − x⁵(1+x)² — два шага Ньютона, точные термы"
  (define F (simplify (expand (list '- (list '^ (list '- 'y 'x) 2)
                                      (list '* (list '^ 'x 5) (list '^ (list '+ 1 'x) 2))))))
  (define bs (puiseux F 'x 'y 4))
  (assert-equal (length bs) 2)
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 4)) bs))
  (assert-equal (puiseux-terms (nth bs 0)) '((1 1) (1 5/2) (1 7/2)))
  (assert-equal (puiseux-terms (nth bs 1)) '((1 1) (-1 5/2) (-1 7/2))))

; y³ − x⁵(1+x): y = x^{5/3}·ζ^k·(1 + …) — шаг Ньютона q=3, комплексные ветви ТОЧНЫЕ (A2.2)
(deftest "puiseux: y³ − x⁵(1+x) — q=3, комплексные ветви с точными радикальными хвостами"
  (define F (simplify (expand (list '- (list '^ 'y 3) (list '* (list '^ 'x 5) (list '+ 1 'x))))))
  (define bs (puiseux F 'x 'y 3))
  (assert-equal (length bs) 3)
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 3)) bs))
  (assert-equal (puiseux-terms (nth bs 0)) '((1 5/3) (1/3 8/3)))
  ; ζ = (−1−√3·%i)/2·x^{5/3} + ζ/3·x^{8/3}
  (assert-equal (puiseux-terms (nth bs 1))
                '(((* 1/2 (+ -1 (* -1 (^ 3 1/2) %i))) 5/3)
                  ((* -1/9 (+ 3/2 (* 3/2 (^ 3 1/2) %i))) 8/3))))

; (y²−x³)² − x⁷: два вложенных шага Ньютона (q=2 и q=2), y = ±x^{3/2}√(1±x^{1/2})
; регрессия бага A2.2: deg-1 факторы немонические (4T−1) — корень был 1 вместо 1/4
(deftest "puiseux: (y²−x³)² − x⁷ — вложенные шаги, y = ±x^{3/2}(1 ± x^{1/2}/2 − x/8 + …)"
  (define F (simplify (expand (list '- (list '^ (list '- (list '^ 'y 2) (list '^ 'x 3)) 2)
                                      (list '^ 'x 7)))))
  (define bs (puiseux F 'x 'y 4))
  (assert-equal (length bs) 4)
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 4)) bs))
  (assert-equal (puiseux-terms (nth bs 0))
                '((1 3/2) (1/2 2) (-1/8 5/2) (1/16 3) (-5/128 7/2) (7/256 4)))
  ; подделка с прежним неверным коэффициентом ловится
  (assert-equal #f (puiseux-check F 'x 'y '(2 ((1 3/2) (1 2))) 4)))

; численная сверка через ньютоновский счёт корня на дробях:
; y_next = y − F/F' от численных значений, старт — значение ряда в точке; сходимость к ряду
(deftest "puiseux: (y²−x³)² − x⁷ — ньютоновский счёт корня сходится к ряду"
  (define F (simplify (expand (list '- (list '^ (list '- (list '^ 'y 2) (list '^ 'x 3)) 2)
                                      (list '^ 'x 7)))))
  (define bs (puiseux F 'x 'y 4))
  (define b0 (nth bs 0))
  (define (series-at x)
    (eval-num (simplify (subst (list 'x x)
      (cons '+ (map (lambda (tm) (list '* (nth tm 0) (list '^ 'x (nth tm 1))))
                    (puiseux-terms b0)))))))
  (define (newton-at x)
    (let ((y0 (series-at x)))
      (let ((fv (eval-num (simplify (subst (list 'x x) (subst (list 'y y0) F)))))
            (dv (eval-num (simplify (subst (list 'x x) (subst (list 'y y0) (diff 'y F)))))))
        (if (and (number? fv) (number? dv) (number? y0) (> (abs dv) 1e-12))
            (- y0 (/ fv dv))
            y0))))
  (assert-true (< (abs (- (newton-at 1/100) (series-at 1/100))) 1e-8))
  (assert-true (< (abs (- (newton-at 1/36) (series-at 1/36))) 1e-6)))

; ---------- вырожденные случаи ----------

(deftest "puiseux: F не содержит y — ветвей нет"
  (assert-equal (puiseux '(+ (* -1 (^ x 2)) 4) 'x 'y 3) '()))

(deftest "puiseux: F приводим (y²−x²) — ветви ±x после бесквадратности"
  (define bs (puiseux '(- (^ y 2) (^ x 2)) 'x 'y 3))
  (assert-true (= (length bs) 2))
  (assert-equal (puiseux-terms (nth bs 0)) '((1 1)))
  (assert-equal (puiseux-terms (nth bs 1)) '((-1 1))))

(deftest "puiseux: точка не особая (y² = 2 + x) — ряд Тейлора вокруг y₀ = ±√2"
  (define F '(+ (* -1 2) (^ y 2) (* -1 x)))
  (define bs (puiseux F 'x 'y 3))
  (assert-true (= (length bs) 2))
  (assert-equal (puiseux-terms (nth bs 0))
                '(((^ 2 1/2) 0) ((* 1/4 (^ 2 1/2)) 1) ((* -1/32 (^ 2 1/2)) 2) ((* 1/128 (^ 2 1/2)) 3)))
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 3)) bs)))

; ---------- подделки ----------

(deftest "puiseux-check: испорченный коэффициент — #f"
  (define F '(+ (^ y 2) (* -1 (^ x 3))))
  (assert-true (puiseux-check F 'x 'y '(2 ((1 3/2))) 3))
  (assert-equal #f (puiseux-check F 'x 'y '(2 ((2 3/2))) 3)))

(deftest "puiseux-check: неверный показатель — #f"
  (define F '(+ (^ y 2) (* -1 (^ x 3))))
  (assert-equal #f (puiseux-check F 'x 'y '(2 ((1 4/3))) 3))
  (assert-equal #f (puiseux-check F 'x 'y '(2 ((1 1))) 3)))

(deftest "puiseux-check: подделка на гладкой ветви — #f"
  (define F '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))))
  (assert-equal #f (puiseux-check F 'x 'y '(1 ((1 1) (1/3 2))) 4))
  (assert-equal #f (puiseux-check F 'x 'y '(1 ((1 1) (1/2 3))) 4)))

(deftest "puiseux-check: подделка с радикальным коэффициентом — #f"
  (define F '(+ (^ y 2) (* -2 (^ x 2))))
  (assert-equal #f (puiseux-check F 'x 'y '(1 (((* 1/2 (^ 2 1/2)) 1))) 3))
  (assert-equal #f (puiseux-check F 'x 'y '(1 (((^ 3 1/2) 1))) 3)))

; ---------- утилиты ----------

(deftest "puiseux-terms: выдать термы ветви"
  (define bs (puiseux '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y 3))
  (assert-equal (puiseux-terms (nth bs 0)) '((1 3/2))))

(deftest "puiseux-at: заглушка — ошибка"
  (assert-error (puiseux-at '(1 ((1 1))) 'x 0.5)))

; ---------- A2.2: puiseux-rational (группы Дюваля) ----------

(deftest "puiseux-rational: y² − x³ — одна группа q=2, кратность 2"
  (define gr (puiseux-rational '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y 3))
  (assert-equal gr '(((2 ((1 3/2))) 2))))

(deftest "puiseux-rational: лист Декарта x³+y³−3xy — две группы (кратности 1 и 2)"
  (define F (simplify (expand (list '+ (+ (^ 'x 3) (^ 'y 3)) (list '* -3 (* 'x 'y))))))
  (define gr (puiseux-rational F 'x 'y 4))
  (assert-equal (length gr) 2)
  (assert-equal (foldl + 0 (map (lambda (g) (nth g 1)) gr)) 3) ; всего ветвей 3
  ; группа 1: y = (1/3)x² + … — одна ветвь
  (assert-equal (puiseux-terms (nth (nth gr 0) 0)) '((1/3 2)))
  ; группа 2: y = √3·x^{1/2} − (1/6)x² − (√3/72)x^{7/2} + … — сопряжённые ±√3
  (assert-equal (puiseux-terms (nth (nth gr 1) 0))
                '(((^ 3 1/2) 1/2) (-1/6 2) ((* -1/72 (^ 3 1/2)) 7/2)))
  ; сверка с puiseux: раскрытые ветви проходят check
  (assert-true (every? (lambda (b) (puiseux-check F 'x 'y b 4)) (puiseux F 'x 'y 4))))

(deftest "puiseux-rational: y³ − x⁵(1+x) — одна группа q=3, кратность 3"
  (define F (simplify (expand (list '- (list '^ 'y 3) (list '* (list '^ 'x 5) (list '+ 1 'x))))))
  (define gr (puiseux-rational F 'x 'y 3))
  (assert-equal gr '(((3 ((1 5/3) (1/3 8/3))) 3))))

(deftest "puiseux-rational: (y²−x³)² − x⁷ — четыре ветви, группы по сопряжённости"
  (define F (simplify (expand (list '- (list '^ (list '- (list '^ 'y 2) (list '^ 'x 3)) 2)
                                      (list '^ 'x 7)))))
  (define gr (puiseux-rational F 'x 'y 4))
  ; 4 ветви разбиты на 2 группы по 2 (±x^{3/2}(1±x^{1/2}/2…): знак при x^{3/2} фиксирован в группе)
  (assert-equal (foldl + 0 (map (lambda (g) (nth g 1)) gr)) 4)
  (assert-equal (length gr) 2))

; ---------- A2.2: algebraic-series ----------

(deftest "algebraic-series: y² − x³, ветвь 1 — объект puiseux-series, x^{3/2}"
  (define s (algebraic-series '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y 0 3))
  (assert-true (algebraic-series? s))
  (assert-equal (algebraic-series-coeff s 1) 1)
  (assert-equal (algebraic-series->expr s) '(^ x 3/2)))

(deftest "algebraic-series: ветвь по номеру 2 — −x^{3/2}"
  (define s (algebraic-series '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y 0 3 2))
  (assert-equal (algebraic-series->expr s) '(* -1 (^ x 3/2))))

(deftest "algebraic-series: вокруг a ≠ 0 — сдвиг, регулярная ветвь y = √(a+x)"
  (define s (algebraic-series '(+ (^ y 2) (* -1 x)) 'x 'y 1 2))
  (assert-true (algebraic-series? s))
  ; первый коэффициент √1 = 1: y = 1 + x/2 − …
  (assert-equal (algebraic-series-coeff s 1) 1)
  (assert-equal (algebraic-series-coeff s 2) 1/2))

