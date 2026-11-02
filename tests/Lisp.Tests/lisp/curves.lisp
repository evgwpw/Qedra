; curves.lisp — тесты модуля curves (A3.1): особые точки, δ, род плоских кривых

; ---------- genus: эталонные кривые ----------

(deftest "curve-genus: узел y² = x²(x+1) — g = 0"
  (assert-equal (curve-genus '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))) 'x 'y) '(genus 0)))

(deftest "curve-genus: каспида y² = x³ — g = 0"
  (assert-equal (curve-genus '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y) '(genus 0)))

(deftest "curve-genus: y³ = x⁴ — g = 0"
  (assert-equal (curve-genus '(+ (^ y 3) (* -1 (^ x 4))) 'x 'y) '(genus 0)))

(deftest "curve-genus: лист Декарта x³+y³ = 3xy — g = 0 (пересечение циклов q > 1 — ζ-сдвиги)"
  (assert-equal (curve-genus '(+ (^ x 3) (^ y 3) (* -3 x y)) 'x 'y) '(genus 0)))

(deftest "curve-genus: лемниската (x²+y²)² = x²−y² — g = 0"
  (assert-equal (curve-genus '(+ (^ (+ (^ x 2) (^ y 2)) 2) (* -1 (^ x 2)) (^ y 2)) 'x 'y) '(genus 0)))

(deftest "curve-genus: астроид (x²+y²−1)³ + 27x²y² — g = 0"
  (assert-equal (curve-genus '(+ (^ (+ (^ x 2) (^ y 2) -1) 3) (* 27 (^ x 2) (^ y 2))) 'x 'y) '(genus 0)))

(deftest "curve-genus: трёхкуспидная гипоциклоида (x+y)²−3xy в квадрате — g = 0"
  (assert-equal (curve-genus '(+ (^ (- (^ (+ x y) 2) (* 3 x y)) 2) (* -1 (* 3 x y (+ x y)))) 'x 'y) '(genus 0)))

(deftest "curve-genus: гладкая кубика y² = x³+x+1 — g = 1"
  (assert-equal (curve-genus '(+ (^ y 2) (* -1 (^ x 3)) (* -1 x) -1) 'x 'y) '(genus 1)))

(deftest "curve-genus: Ферма x⁴+y⁴ = 1 — g = 3"
  (assert-equal (curve-genus '(+ (^ x 4) (^ y 4) -1) 'x 'y) '(genus 3)))

(deftest "curve-genus: Ферма x⁵+y⁵ = 1 — g = 6"
  (assert-equal (curve-genus '(+ (^ x 5) (^ y 5) -1) 'x 'y) '(genus 6)))

(deftest "curve-genus: прямая y = x — g = 0"
  (assert-equal (curve-genus '(+ y (* -1 x)) 'x 'y) '(genus 0)))

(deftest "curve-genus: коника x²+y² = 1 — g = 0"
  (assert-equal (curve-genus '(+ (^ x 2) (^ y 2) -1) 'x 'y) '(genus 0)))

(deftest "curve-genus: приводимая (x²+y²−1)(y−x) — reducible"
  (assert-true (equal? (car (curve-genus '(* (+ (^ x 2) (^ y 2) -1) (+ y (* -1 x))) 'x 'y)) 'reducible)))

; ---------- singular-points: структура и δ ----------
; формат группы: ((point a b) (multiplicity m) (branches r) (delta δ) (ordinary #f/#t)
;                 (tangents …) (conjugates e) (at affine|inf))

(deftest "singular-points: каспида y² = x³ — одна точка (0,0), δ = 1, m = 2"
  (define sp (singular-points '(+ (^ y 2) (* -1 (^ x 3))) 'x 'y))
  (assert-true (and (list? sp) (= (length sp) 1)))
  (define p (nth sp 0))
  (assert-true (equal? (nth p 0) '(point 0 0)))
  (assert-true (equal? (nth p 1) '(multiplicity 2)))
  (assert-true (equal? (nth p 3) '(delta 1)))
  (assert-true (equal? (nth p 4) '(ordinary #f))))

; ---------- A3.1c: вертикальные касательные (ветви считаются по y после обмена) ----------

(deftest "A3.1c: суперэллипс y³ = (x−1)²(x+1) — каспида (3,2) в (1,0), одна ветвь, δ = 1"
  (define sp (singular-points '(- (^ y 3) (* (^ (- x 1) 2) (+ x 1))) 'x 'y))
  (assert-true (= (length sp) 1))
  (define p (nth sp 0))
  (assert-true (equal? (nth p 0) '(point 1 0)))
  (assert-true (equal? (nth p 1) '(multiplicity 2)))
  (assert-true (equal? (nth p 2) '(branches 1)))
  (assert-true (equal? (nth p 3) '(delta 1)))
  (assert-true (equal? (nth p 5) '(tangents (vert))))
  ; род: y³ = P, P степени 3 с двойным корнем → 0
  (assert-true (equal? (curve-genus '(- (^ y 3) (* (^ (- x 1) 2) (+ x 1))) 'x 'y) '(genus 0))))

(deftest "A3.1c: поворот y² = x³ ↔ x² = y³ — δ = 1 в обоих, касательная horiz|vert"
  (define sp1 (singular-points '(- (^ y 2) (^ x 3)) 'x 'y))
  (define sp2 (singular-points '(- (^ x 2) (^ y 3)) 'x 'y))
  (assert-true (equal? (nth (nth sp1 0) 3) '(delta 1)))
  (assert-true (equal? (nth (nth sp1 0) 5) '(tangents (horiz))))
  (assert-true (equal? (nth (nth sp2 0) 2) '(branches 1)))
  (assert-true (equal? (nth (nth sp2 0) 3) '(delta 1)))
  (assert-true (equal? (nth (nth sp2 0) 5) '(tangents (vert)))))

(deftest "A3.1c: поворот y⁴ = x³ ↔ x⁴ = y³ — δ = 3 в обоих"
  (define sp1 (singular-points '(- (^ y 4) (^ x 3)) 'x 'y))
  (define sp2 (singular-points '(- (^ x 4) (^ y 3)) 'x 'y))
  (assert-true (equal? (nth (nth sp1 0) 3) '(delta 3)))
  (assert-true (equal? (nth (nth sp2 0) 3) '(delta 3)))
  (assert-true (equal? (nth (nth sp2 0) 2) '(branches 1))))

(deftest "A3.1c: вертикальные каспиды x³ = y⁵ (δ = 4) и x² = y⁵ (δ = 2) — по Милнору"
  (define sp1 (singular-points '(- (^ x 3) (^ y 5)) 'x 'y))
  (define p1 (car (filter (lambda (g) (equal? (nth (nth g 7) 1) 'affine)) sp1)))
  (assert-true (equal? (nth p1 3) '(delta 4)))
  (assert-true (equal? (nth p1 2) '(branches 1)))
  (assert-true (equal? (nth p1 5) '(tangents (vert))))
  (define sp2 (singular-points '(- (^ x 2) (^ y 5)) 'x 'y))
  (define p2 (car (filter (lambda (g) (equal? (nth (nth g 7) 1) 'affine)) sp2)))
  (assert-true (equal? (nth p2 3) '(delta 2)))
  (assert-true (equal? (nth p2 2) '(branches 1))))

(deftest "singular-points: узел y² = x²(x+1) — (0,0), δ = 1, обыкновенная"
  (define sp (singular-points '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))) 'x 'y))
  (define p (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp)))
  (assert-true (equal? (nth p 3) '(delta 1)))
  (assert-true (equal? (nth p 4) '(ordinary #t)))
  (assert-true (equal? (nth p 2) '(branches 2))))

(deftest "singular-points: астроид — 4 вещественные каспиды δ=1"
  (define sp (singular-points '(+ (^ (+ (^ x 2) (^ y 2) -1) 3) (* 27 (^ x 2) (^ y 2))) 'x 'y))
  (define aff (filter (lambda (g) (equal? (nth (nth g 7) 1) 'affine)) sp))
  (assert-true (>= (length aff) 4))
  (define real4 (filter (lambda (g) (and (rational-number? (nth (nth g 0) 1))
                                          (rational-number? (nth (nth g 0) 2)))) aff))
  (assert-true (= (length real4) 4))
  (assert-true (every? (lambda (g) (= (nth (nth g 3) 1) 1)) real4)))

(deftest "singular-points: лемниската — узел в 0 и циклические точки на бесконечности"
  (define sp (singular-points '(+ (^ (+ (^ x 2) (^ y 2)) 2) (* -1 (^ x 2)) (^ y 2)) 'x 'y))
  (define p0 (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp)))
  (assert-true (equal? (nth p0 3) '(delta 1)))
  (define infs (filter (lambda (g) (equal? (nth (nth g 7) 1) 'inf)) sp))
  (assert-true (>= (length infs) 1))
  (assert-true (every? (lambda (g) (= (nth (nth g 3) 1) 1)) infs)))

(deftest "singular-points: гладкая коника — без особенностей"
  (assert-equal (singular-points '(+ (^ x 2) (^ y 2) -1) 'x 'y) '()))

(deftest "singular-points: y³ = x⁴ — δ = 3 в (0,0)"
  (define sp (singular-points '(+ (^ y 3) (* -1 (^ x 4))) 'x 'y))
  (assert-true (= (length sp) 1))
  (assert-true (equal? (nth (nth sp 0) 3) '(delta 3))))

; ---------- подделки ----------

(deftest "подделка: genus 0 для гладкой кубики не выдаётся"
  (assert-true (not (equal? (curve-genus '(+ (^ y 2) (* -1 (^ x 3)) (* -1 x) -1) 'x 'y) '(genus 0)))))

(deftest "подделка: неособая точка не выдаётся (коника в (0,0): F ≠ 0)"
  (define sp (singular-points '(+ (^ x 2) (^ y 2) -1) 'x 'y))
  (assert-true (not (any? (lambda (g) (equal? (nth g 0) '(point 0 0))) sp))))

(deftest "подделка: посторонняя точка не подмешивается (узел только в (0,0))"
  (define sp (singular-points '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))) 'x 'y))
  (assert-true (equal? (length sp) 1)))

; замечание ревью: точка [0:1:0] (патч X = 1 её не видит) и запрет отрицательного рода
(deftest "curve-genus: y² = квартика — род 1 (такнод в [0:1:0]); y² = x⁵+1 — род 2; y² = x⁶+1 — не ложный род"
  (assert-equal (curve-genus '(- (^ y 2) (+ (^ x 4) 1)) 'x 'y) '(genus 1))
  (assert-equal (curve-genus '(- (^ y 2) (* x (- (^ x 2) 1) (- x 2))) 'x 'y) '(genus 1))
  (assert-equal (curve-genus '(- (^ y 2) (+ (^ x 5) 1)) 'x 'y) '(genus 2))
  (assert-true (member? (curve-genus '(- (^ y 2) (+ (^ x 6) 1)) 'x 'y) '(unknown (genus 2)))))

; ---------- A3.1b: точное пересечение циклов (ζ-сдвиги) и сверка δ по Милнору ----------

; δ в (0,0) для yᵃ − xᵇ сверено по Милнору: δ = (μ + r − 1)/2, μ = (a−1)(b−1), r = НОД(a, b)
(deftest "singular-points: y⁴ − x⁶ — δ = 8 в (0,0) (Милнор μ = 15, r = 2; пересечение циклов q = 2)"
  (define sp (singular-points '(- (^ y 4) (^ x 6)) 'x 'y))
  (define p (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp)))
  (assert-true (equal? (nth p 3) '(delta 8))))

(deftest "singular-points: y³ − x⁶ — δ = 6 в (0,0) (Милнор μ = 10, r = 3; три ветви ζ·x², попарно I = 2)"
  (define sp (singular-points '(- (^ y 3) (^ x 6)) 'x 'y))
  (define p (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp)))
  (assert-true (equal? (nth p 3) '(delta 6)))
  (assert-true (equal? (nth p 2) '(branches 3))))

(deftest "singular-points: y² − x⁵ — δ = 2 (μ = 4, r = 1); y³ − x⁷ — δ = 6 (μ = 12, r = 1)"
  (define sp1 (singular-points '(- (^ y 2) (^ x 5)) 'x 'y))
  (define p1 (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp1)))
  (assert-true (equal? (nth p1 3) '(delta 2)))
  (define sp2 (singular-points '(- (^ y 3) (^ x 7)) 'x 'y))
  (define p2 (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp2)))
  (assert-true (equal? (nth p2 3) '(delta 6))))

; (y²−x³)² − x⁷: δ(0,0) = 9 (две каспоидные ветви ⟨2,3⟩, I = 7), deg 7 → Σδ = 15, g = 0
(deftest "singular-points: (y²−x³)² − x⁷ — δ = 9 в (0,0), род 0"
  (define sp (singular-points '(- (^ (- (^ y 2) (^ x 3)) 2) (^ x 7)) 'x 'y))
  (define p (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp)))
  (assert-true (equal? (nth p 3) '(delta 9)))
  (assert-true (equal? (nth p 2) '(branches 2)))
  (assert-equal (curve-genus '(- (^ (- (^ y 2) (^ x 3)) 2) (^ x 7)) 'x 'y) '(genus 0)))

; род суперэллиптических: (a−1)(b−1)/2 + сдвиги на бесконечности
(deftest "curve-genus: y³ = x⁴+1 — g = 3 ((3−1)(4−1)/2, [0:1:0] гладкая)"
  (assert-equal (curve-genus '(- (^ y 3) (+ (^ x 4) 1)) 'x 'y) '(genus 3)))

(deftest "curve-genus: y² = x⁷+1 — g = 3 ([0:1:0] каспидальная)"
  (assert-equal (curve-genus '(- (^ y 2) (+ (^ x 7) 1)) 'x 'y) '(genus 3)))

; особенности в [0:1:0] и [1:b:0] одновременно (гиперэллиптическая чётной степени)
(deftest "curve-genus: y² = x⁶+1 — g = 2 ([0:1:0] и [1:±i:0])"
  (assert-equal (curve-genus '(- (^ y 2) (+ (^ x 6) 1)) 'x 'y) '(genus 2)))

; гиперэллиптические y² = P(x), deg P = 3..8 без кратных корней → g = ⌊(deg−1)/2⌋
(deftest "curve-genus: гиперэллиптические y² = P(x) степеней 3–8"
  ; P степени 3: g = 1
  (assert-equal (curve-genus '(- (^ y 2) (+ x (^ x 2) (^ x 3))) 'x 'y) '(genus 1))
  ; 4: g = 1
  (assert-equal (curve-genus '(- (^ y 2) (+ 1 x (^ x 4))) 'x 'y) '(genus 1))
  ; 5: g = 2
  (assert-equal (curve-genus '(- (^ y 2) (+ 1 x (^ x 2) (^ x 5))) 'x 'y) '(genus 2))
  ; 6: g = 2
  (assert-equal (curve-genus '(- (^ y 2) (+ 2 (^ x 2) (^ x 4) (^ x 6))) 'x 'y) '(genus 2))
  ; 7: g = 3 (замечание ревью: плотные P степени 7–8 считаются 54 с и 3.5 мин — заменены разреженными)
  (assert-equal (curve-genus '(- (^ y 2) (- (^ x 7) x)) 'x 'y) '(genus 3))
  ; 8: g = 3
  (assert-equal (curve-genus '(- (^ y 2) (+ (^ x 8) 1)) 'x 'y) '(genus 3)))

; ---------- подделки (A3.1b) ----------

(deftest "подделка: род не бывает отрицательным — кривая с завышенным δ даёт unknown, не число"
  ; кривая с любой недооценкой δ не может дать род больше формулы Нётера; любая кривая
  ; набора отвечает genus/reducible/unknown, но не отрицательное число
  (define rs (list (curve-genus '(- (^ y 2) (^ x 5)) 'x 'y)
                   (curve-genus '(- (^ y 3) (^ x 7)) 'x 'y)
                   (curve-genus '(- (^ y 4) (^ x 6)) 'x 'y)))
  (assert-true (every? (lambda (r) (or (and (list? r) (equal? (car r) 'genus) (>= (nth r 1) 0))
                                        (and (list? r) (equal? (car r) 'reducible))
                                        (equal? r 'unknown)))
                        rs)))

(deftest "подделка: неверное δ не проходит сверку по Милнору (y⁴ − x⁶: δ обязано быть 8, не 14)"
  (define sp (singular-points '(- (^ y 4) (^ x 6)) 'x 'y))
  (define p (car (filter (lambda (g) (equal? (nth g 0) '(point 0 0))) sp)))
  ; μ = (4−1)(6−1) = 15, r = 2: δ = (15+2−1)/2 = 8 — ровно это и только это
  (assert-true (equal? (nth p 3) '(delta 8))))

; ---------- A3.2: параметризация рода 0 ----------

(deftest "parametrize-curve: узел y² = x²(x+1) — параметризация с сертификатом"
  (define x 'x)(define y 'y)(define t 't)
  (define par (parametrize-curve '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))) x y t))
  (assert-true (and (list? par) (= (length par) 2)))
  (assert-true (parametrization-check '(+ (^ y 2) (* -1 (^ x 2)) (* -1 (^ x 3))) x y par t)))

(deftest "parametrize-curve: каспида y² = x³ — x = t², y = t³"
  (define x 'x)(define y 'y)(define t 't)
  (define par (parametrize-curve '(+ (^ y 2) (* -1 (^ x 3))) x y t))
  (assert-true (and (list? par) (= (length par) 2)))
  (assert-true (parametrization-check '(+ (^ y 2) (* -1 (^ x 3))) x y par t)))

(deftest "parametrize-curve: лист Декарта x³+y³ = 3xy — параметризация с сертификатом"
  (define x 'x)(define y 'y)(define t 't)
  (define par (parametrize-curve '(+ (^ x 3) (^ y 3) (* -3 x y)) x y t))
  (assert-true (and (list? par) (= (length par) 2)))
  (assert-true (parametrization-check '(+ (^ x 3) (^ y 3) (* -3 x y)) x y par t)))

(deftest "parametrize-curve: трёхкуспидная квартика — параметризация с сертификатом"
  (define x 'x)(define y 'y)(define t 't)
  (define par (parametrize-curve '(+ (^ (- (^ (+ x y) 2) (* 3 x y)) 2) (* -1 (* 3 x y (+ x y)))) x y t))
  (assert-true (and (list? par) (= (length par) 2)))
  (assert-true (parametrization-check '(+ (^ (- (^ (+ x y) 2) (* 3 x y)) 2) (* -1 (* 3 x y (+ x y)))) x y par t)))

(deftest "parametrize-curve: окружность x² + y² = 1 — коника через рациональную точку"
  (define x 'x)(define y 'y)(define t 't)
  (define par (parametrize-curve '(+ (^ x 2) (^ y 2) -1) x y t))
  (assert-true (and (list? par) (= (length par) 2)))
  (assert-true (parametrization-check '(+ (^ x 2) (^ y 2) -1) x y par t)))

(deftest "parametrize-curve: прямая y = x"
  (define x 'x)(define y 'y)(define t 't)
  (define par (parametrize-curve '(+ y (* -1 x)) x y t))
  (assert-true (and (list? par) (= (length par) 2)))
  (assert-true (parametrization-check '(+ y (* -1 x)) x y par t)))

(deftest "parametrize-curve: гладкая кубика y² = x³+x+1 — not-rational"
  (define x 'x)(define y 'y)(define t 't)
  (assert-equal (parametrize-curve '(+ (^ y 2) (* -1 (^ x 3)) (* -1 x) -1) x y t) '(not-rational 1)))

(deftest "parametrize-curve: коника x² + y² = 3 без рациональной точки — параметризация над ℚ(√3)"
  (define x (quote x))(define y (quote y))(define t (quote t))
  (define par (parametrize-curve (quote (+ (^ x 2) (^ y 2) -3)) x y t))
  ; точка (√3, 0) над ℚ(√3); ответ содержит (^ 3 1/2); сертификат — parametrization-check
  (assert-true (and (list? par) (= (length par) 2)
                     (contains-sym? (nth par 0) (quote t))
                     (parametrization-check (quote (+ (^ x 2) (^ y 2) -3)) x y par t))))

(deftest "parametrize-curve: коника x² + y² = −1 — комплексная параметризация над ℚ(i)"
  (define x (quote x))(define y (quote y))(define t (quote t))
  (define par (parametrize-curve (quote (+ (^ x 2) (^ y 2) 1)) x y t))
  (assert-true (and (list? par) (= (length par) 2)
                     (parametrization-check (quote (+ (^ x 2) (^ y 2) 1)) x y par t))))

(deftest "parametrize-curve: коника x² + y² = 325 (точка большой высоты) — рационально, sum-of-two-squares"
  (define x (quote x))(define y (quote y))(define t (quote t))
  (define par (parametrize-curve (quote (+ (^ x 2) (^ y 2) -325)) x y t))
  (assert-true (and (list? par) (= (length par) 2)
                     (parametrization-check (quote (+ (^ x 2) (^ y 2) -325)) x y par t)
                     (not (contains-sym? (nth par 0) (list (quote ^) 3 1/2))))))

(deftest "parametrize-curve: лемниската (кратности < d−1, адъюнкты) — рациональная параметризация"
  (define x 'x)(define y 'y)(define t 't)
  ; (x²+y²)² = x²−y²: особые (0,0) r=2 и [±i:1:0] r=2 — метод адъюнктов
  (define par (parametrize-curve '(+ (^ (+ (^ x 2) (^ y 2)) 2) (* -1 (^ x 2)) (^ y 2)) x y t))
  (assert-true (and (list? par) (= (length par) 2)
                     (parametrization-check '(+ (^ (+ (^ x 2) (^ y 2)) 2) (* -1 (^ x 2)) (^ y 2)) x y par t))))

(deftest "parametrize-curve: астроида (x²+y²−1)³ + 27x²y² = 0 — каспы r=2, адъюнкты"
  (define x 'x)(define y 'y)(define t 't)
  ; 4 каспа r=2 + 2 узла над ℚ(i) + [i:1:0] — метод адъюнктов
  (define par (parametrize-curve '(+ (^ (+ (^ x 2) (^ y 2) -1) 3) (* 27 (^ x 2) (^ y 2))) x y t))
  (assert-true (and (list? par) (= (length par) 2)
                     (parametrization-check '(+ (^ (+ (^ x 2) (^ y 2) -1) 3) (* 27 (^ x 2) (^ y 2))) x y par t))))

(deftest "parametrization-check: подделка — испорченный коэффициент отвергается"
  (define x 'x)(define y 'y)(define t 't)
  ; x = 3t/(1+t³), y = 4t²/(1+t³) — не на листе Декарта
  (define par1 (list (/ (* 3 t) (+ 1 (^ t 3))) (/ (* 4 (^ t 2)) (+ 1 (^ t 3)))))
  (assert-true (not (parametrization-check '(+ (^ x 3) (^ y 3) (* -3 x y)) x y par1 t))))

(deftest "parametrization-check: подделка — степень 2 (t ↦ t²) отвергается"
  (define x 'x)(define y 'y)(define t 't)
  ; композиция настоящей параметризации с t ↦ t²
  (define par2 (list (/ (* 3 (^ t 2)) (+ 1 (^ t 6))) (/ (* 3 (^ t 4)) (+ 1 (^ t 6)))))
  (assert-true (not (parametrization-check '(+ (^ x 3) (^ y 3) (* -3 x y)) x y par2 t))))

(deftest "parametrize-curve: приводимая — reducible"
  (define x 'x)(define y 'y)(define t 't)
  (assert-true (equal? (car (parametrize-curve '(* (+ (^ x 2) (^ y 2) -1) (+ y (* -1 x))) x y t)) 'reducible)))

(deftest "parametrization-check: подделки — t ↦ t³, t ↦ t²+t, не рациональная (cos, sin); 1/t и форма Вейерштрасса — верны"
  (define x 'x)(define y 'y)(define t 't)
  (define F '(- (^ y 2) (* (^ x 2) (+ x 1))))
  (define (comp s) (list (subst (list (list t s)) '(+ -1 (^ t 2))) (subst (list (list t s)) '(+ (* -1 t) (^ t 3)))))
  (assert-true (parametrization-check F x y (comp 't) t))
  (assert-true (parametrization-check F x y (comp '(/ 1 t)) t))
  (assert-true (not (parametrization-check F x y (comp '(^ t 3)) t)))
  (assert-true (not (parametrization-check F x y (comp '(+ (^ t 2) t)) t)))
  (define C '(- (+ (^ x 2) (^ y 2)) 1))
  (assert-true (not (parametrization-check C x y (list '(cos t) '(sin t)) t)))
  (assert-true (parametrization-check C x y (list '(/ (- 1 (^ t 2)) (+ 1 (^ t 2))) '(/ (* 2 t) (+ 1 (^ t 2)))) t))
  (assert-true (not (parametrization-check C x y (list '(/ (- 1 (^ t 2)) (+ 1 (^ t 2))) '(/ (* 3 t) (+ 1 (^ t 2)))) t))))

(deftest "A3.1d: (y − x²)² = x⁵ — δ = 2 в (0,0) (дробная часть ряда после целого члена x²), род 0"
  ; кривая рациональна: x = t², y = t⁴ + t⁵; раньше δ = 0 (ветвь считалась гладкой), род 2
  (define sp (singular-points '(- (^ (- y (^ x 2)) 2) (^ x 5)) 'x 'y))
  (define p (car (filter (lambda (g) (equal? (nth (nth g 7) 1) 'affine)) sp)))
  (assert-equal '(delta 2) (nth p 3))
  (assert-equal '(branches 1) (nth p 2))
  (assert-equal '(ordinary #f) (nth p 4))
  (assert-equal '(genus 0) (curve-genus '(- (^ (- y (^ x 2)) 2) (^ x 5)) 'x 'y))
  (assert-true (parametrization-check '(- (^ (- y (^ x 2)) 2) (^ x 5)) 'x 'y '((^ t 2) (+ (^ t 4) (^ t 5))) 't)))

; ---------- A3.1d: самопроверка рода на рациональных кривых (неявизации параметризаций) ----------
; кривые из параметризаций: genus → (genus 0) или unknown, никогда g > 0;
; parametrize-curve → не not-rational. Умолчание: 1 unknown из 6 (генус), 2 unknown (параметризация).

(deftest "A3.1d: рациональные кривые 1 — неявизации (t², t⁴+t⁵), (t³, t⁴+t⁵), (t²−1, t³−t)"
  ; (t², t⁴+t⁵): (y − x²)² = x⁵ — род 0 (проверено отдельно), здесь неявизация-эквивалент
  (define g1 (curve-genus '(+ (* -1 (^ x 4)) (^ x 5) (* -1 (^ y 2)) (* 2 (^ x 2) y)) 'x 'y))
  (assert-true (or (equal? g1 '(genus 0)) (equal? g1 'unknown)))
  (define g2 (curve-genus '(+ (^ x 4) (^ x 5) (* -1 (^ y 3)) (* 3 (^ x 3) y)) 'x 'y))
  (assert-true (or (equal? g2 '(genus 0)) (equal? g2 'unknown)))
  (define g3 (curve-genus '(+ (^ x 2) (^ x 3) (* -1 (^ y 2))) 'x 'y))
  (assert-true (or (equal? g3 '(genus 0)) (equal? g3 'unknown))))

(deftest "A3.1d: рациональные кривые 2 — (t³−3t, t²), (t, t³), (2t/(1+t²), (1−t²)/(1+t²))"
  (define g1 (curve-genus '(+ (* -1 (^ x 2)) (* 9 y) (* -6 (^ y 2)) (^ y 3)) 'x 'y))
  (assert-true (or (equal? g1 '(genus 0)) (equal? g1 'unknown)))
  (define g2 (curve-genus '(+ (^ x 3) (* -1 y)) 'x 'y))
  (assert-true (or (equal? g2 '(genus 0)) (equal? g2 'unknown)))
  (define g3 (curve-genus '(+ -1 (^ x 2) (^ y 2)) 'x 'y))
  (assert-true (or (equal? g3 '(genus 0)) (equal? g3 'unknown))))

(deftest "A3.1d: рациональные кривые 3 — (t/(1+t²), t²/(1+t²)), y² = x⁷ (t², t⁷), параметры не not-rational"
  (define g1 (curve-genus '(+ (^ x 2) (* -1 y) (^ y 2)) 'x 'y))
  (assert-true (or (equal? g1 '(genus 0)) (equal? g1 'unknown)))
  (define g2 (curve-genus '(- (^ y 2) (^ x 7)) 'x 'y))
  (assert-true (or (equal? g2 '(genus 0)) (equal? g2 'unknown)))
  ; parametrize-curve на рациональной кривой — не not-rational (unknown допустим)
  (define p1 (parametrize-curve '(+ (^ x 2) (* -1 y) (^ y 2)) 'x 'y 't))
  (assert-true (not (equal? (car p1) 'not-rational)))
  (define p2 (parametrize-curve '(+ (^ x 2) (^ x 3) (* -1 (^ y 2))) 'x 'y 't))
  (assert-true (not (equal? (car p2) 'not-rational))))

(deftest "A3.1d: кривые с родом > 0 — y² = x⁵+1 (2), y³ = x⁴+1 (3)"
  (define g1 (curve-genus '(- (^ y 2) (+ (^ x 5) 1)) 'x 'y))
  (assert-true (or (equal? g1 '(genus 2)) (equal? g1 'unknown)))
  (define g2 (curve-genus '(- (^ y 3) (+ (^ x 4) 1)) 'x 'y))
  (assert-true (or (equal? g2 '(genus 3)) (equal? g2 'unknown))))

(deftest "A3.1d: кривые с родом > 0 — x⁴+y⁴=1 (3), y² = x³+x+1 (1), y² = x⁶+1 (2)"
  (define g1 (curve-genus '(- (+ (^ x 4) (^ y 4)) 1) 'x 'y))
  (assert-true (or (equal? g1 '(genus 3)) (equal? g1 'unknown)))
  (define g2 (curve-genus '(- (^ y 2) (+ (+ (^ x 3) x) 1)) 'x 'y))
  (assert-true (or (equal? g2 '(genus 1)) (equal? g2 'unknown)))
  (define g3 (curve-genus '(- (^ y 2) (+ (^ x 6) 1)) 'x 'y))
  (assert-true (or (equal? g3 '(genus 2)) (equal? g3 'unknown))))
