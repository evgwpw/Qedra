; repr.lisp — тесты шага REP: классы сопряжённости, таблица характеров (Диксон — Шнайдер), разложение, сертификат.
; Оракулы: (1) известные таблицы (C_n, S3, S4, D4 и Q8, A4 с ω = e^{2πi/3}, A5 с (1 ± √5)/2); (2) независимые тождества:
; Σ|C| = |G|, Σχ(1)² = |G|, кратность неприводимого в регулярном представлении = степень, ⟨π, π⟩ = число орбит на парах;
; (3) сертификат character_table_check пересчитывает классы и структурные константы сам; (4) подделки таблицы.

(define (rpt-sizes G) (map (lambda (c) (nth c 1)) (conjugacy-classes G)))
(define (rpt-orders G) (map (lambda (c) (nth c 2)) (conjugacy-classes G)))
(define (rpt-rows G) (char-table->exprs (character-table G)))
(define (rpt-degrees G) (char-table-degrees (character-table G)))
(define (rpt-verdict G) (car (character-table-check G (character-table G))))
; инвариант таблицы с точностью до перестановки классов: строки как отсортированные списки численных значений
(define (rpt-num-key x) (let ((v (eval-num x))) (floor (+ (* 1000000 v) 0.5))))
(define (rpt-row-invariant row)
  (sort (map rpt-num-key row) <))
(define (rpt-invariant G)
  (sort (map rpt-row-invariant (rpt-rows G)) rpt-list<))
(define (rpt-list< a b)
  (cond ((null? a) (not (null? b)))
        ((null? b) #f)
        ((< (car a) (car b)) #t)
        ((> (car a) (car b)) #f)
        (else (rpt-list< (cdr a) (cdr b)))))
(define (rpt-abs x) (if (< x 0) (- x) x))
(define (rpt-near? x v) (< (rpt-abs (- (eval-num x) v)) 0.000001))

; ---------- классы сопряжённости ----------

(deftest "repr: классы S3 — размеры, порядки, централизаторы"
  (let ((cl (conjugacy-classes (symmetric-group 3))))
    (assert-equal (map (lambda (c) (nth c 1)) cl) '(1 3 2))
    (assert-equal (map (lambda (c) (nth c 2)) cl) '(1 2 3))
    (assert-equal (map (lambda (c) (nth c 3)) cl) '(6 2 3))))

(deftest "repr: классы S4 — пять классов, размеры 1 3 6 8 6"
  (let ((G (symmetric-group 4)))
    (assert-equal (length (group-elements G)) 24)
    (assert-equal (rpt-sizes G) '(1 3 6 8 6))
    (assert-equal (rpt-orders G) '(1 2 2 3 4))
    (assert-equal (apply + (rpt-sizes G)) 24)))

(deftest "repr: карты степеней классов S4"
  (let ((G (symmetric-group 4)))
    (assert-equal (class-power-map G 2) '(0 0 0 3 1))
    (assert-equal (class-power-map G -1) '(0 1 2 3 4))
    (assert-equal (class-power-map G 3) '(0 1 2 0 4))))

(deftest "repr: C_n — n классов размера 1; тривиальная группа"
  (assert-equal (rpt-sizes (cyclic-group 6)) '(1 1 1 1 1 1))
  (assert-equal (rpt-orders (cyclic-group 6)) '(1 2 3 3 6 6))
  (assert-equal (rpt-rows (list '() 1)) '((1))))

(deftest "repr: классы Q8 и D4 различаются порядками элементов"
  (assert-equal (rpt-orders (quaternion-group)) '(1 2 4 4 4))
  (assert-equal (rpt-orders (dihedral-group 4)) '(1 2 2 2 4))
  (assert-equal (group-order (quaternion-group)) 8))

; ---------- таблицы ----------

(deftest "repr: C5 — пять линейных характеров, значения — корни из единицы"
  (let ((G (cyclic-group 5)))
    (assert-equal (rpt-degrees G) '(1 1 1 1 1))
    (assert-equal (car (rpt-rows G)) '(1 1 1 1 1))
    (assert-equal (rpt-verdict G) 'exact)
    (assert-true (every? (lambda (row) (every? (lambda (x) (and (pair? x) (equal? (car x) 'exp))) (cdr row)))
                         (cdr (rpt-rows G))))))

(deftest "repr: таблица S3"
  (let ((G (symmetric-group 3)))
    (assert-equal (rpt-rows G) '((1 1 1) (1 -1 1) (2 0 -1)))
    (assert-equal (rpt-verdict G) 'exact)))

(deftest "repr: таблица S4 — степени 1 1 2 3 3"
  (let ((G (symmetric-group 4)))
    (assert-equal (rpt-degrees G) '(1 1 2 3 3))
    (assert-equal (rpt-rows G) '((1 1 1 1 1) (1 1 -1 1 -1) (2 2 0 -1 0) (3 -1 1 0 -1) (3 -1 -1 0 1)))
    (assert-equal (rpt-verdict G) 'exact)))

(deftest "repr: D4 и Q8 — одна таблица характеров с точностью до порядка классов"
  (let ((D (dihedral-group 4)) (Q (quaternion-group)))
    (assert-equal (rpt-degrees D) '(1 1 1 1 2))
    (assert-equal (rpt-degrees Q) '(1 1 1 1 2))
    (assert-equal (rpt-invariant D) (rpt-invariant Q))
    (assert-equal (rpt-verdict D) 'exact)
    (assert-equal (rpt-verdict Q) 'exact)))

(deftest "repr: A4 — три линейных характера с ω = e^{2πi/3} и трёхмерный"
  (let* ((G (alternating-group 4)) (T (character-table G)) (rows (char-table-rows T)) (ex (char-table->exprs T)))
    (assert-equal (rpt-degrees G) '(1 1 1 3))
    (assert-equal (rpt-sizes G) '(1 3 4 4))
    (assert-equal (nth ex 0) '(1 1 1 1))
    (assert-equal (nth ex 3) '(3 -1 0 0))
    ; линейные характеры — ω, ω² на двух классах 3-циклов (сопряжены друг другу)
    (assert-true (member? (nth (nth ex 1) 2) (list (simplify '(exp (* 2/3 %i pi))) (simplify '(exp (* 4/3 %i pi))))))
    (assert-equal (char-dual T (nth rows 1)) (nth rows 2))
    (assert-equal (rpt-verdict G) 'exact)
    ; ω² + ω + 1 = 0 точно: ω + ω̄ = −1 как скалярное произведение с тривиальным
    (assert-equal (char-inner T (nth rows 1) (nth rows 0)) 0)))

(deftest "repr: A5 — степени 1 3 3 4 5, золотое сечение в трёхмерных"
  (let* ((G (alternating-group 5)) (ex (rpt-rows G)) (x (nth (nth ex 1) 3)) (y (nth (nth ex 2) 3)))
    (assert-equal (rpt-sizes G) '(1 15 20 12 12))
    (assert-equal (rpt-degrees G) '(1 3 3 4 5))
    (assert-equal (nth ex 3) '(4 0 1 -1 -1))
    (assert-equal (nth ex 4) '(5 1 -1 0 0))
    ; значения на 5-циклах — корни x² − x − 1 = 0: (1 ± √5)/2
    (assert-equal (simplify (- (* x x) x 1)) 0)
    (assert-equal (simplify (- (* y y) y 1)) 0)
    (assert-true (rpt-near? x 1.618033988749895))
    (assert-true (rpt-near? y -0.6180339887498949))
    (assert-equal (rpt-verdict G) 'exact)))

(deftest "repr: D6, A5 и Z12 — сертификат точный"
  (assert-equal (rpt-verdict (dihedral-group 6)) 'exact)
  (assert-equal (rpt-degrees (dihedral-group 6)) '(1 1 1 1 2 2))
  (let ((G (cyclic-group 12)))
    (assert-equal (length (rpt-rows G)) 12)
    (assert-equal (rpt-verdict G) 'exact)))

(deftest "repr: S5 — семь классов, Σ χ(1)² = 120"
  (let ((G (symmetric-group 5)))
    (assert-equal (rpt-degrees G) '(1 1 4 4 5 5 6))
    (assert-equal (apply + (map (lambda (d) (* d d)) (rpt-degrees G))) 120)
    (assert-equal (rpt-verdict G) 'exact)))

; ---------- разложение, тензорные произведения ----------

(deftest "repr: регулярное представление — кратность неприводимого равна степени"
  (for-each (lambda (G)
              (let ((T (character-table G)))
                (assert-equal (char-decompose T (char-regular T)) (char-table-degrees T))))
            (list (symmetric-group 3) (symmetric-group 4) (alternating-group 4) (quaternion-group)
                  (cyclic-group 5) (dihedral-group 5))))

(deftest "repr: S3 — тензорный квадрат стандартного представления"
  (let* ((G (symmetric-group 3)) (T (character-table G)) (std (nth (char-table-rows T) 2)))
    (assert-equal (map car (char-tensor T std std)) '(4 0 1))
    ; 2⊗2 = 1 + sgn + 2
    (assert-equal (char-decompose T (char-tensor T std std)) '(1 1 1))
    ; Sym² = 1 + 2, Λ² = sgn
    (assert-equal (char-decompose T (char-sym2 T std)) '(1 0 1))
    (assert-equal (char-decompose T (char-alt2 T std)) '(0 1 0))))

(deftest "repr: Sym² и Λ² дают в сумме тензорный квадрат"
  (let* ((G (symmetric-group 4)) (T (character-table G)))
    (for-each (lambda (chi)
                (assert-equal (map2 (lambda (a b) (map2 + a b)) (char-sym2 T chi) (char-alt2 T chi))
                              (char-tensor T chi chi)))
              (char-table-rows T))))

(deftest "repr: тензорное произведение S4 — 3 ⊗ 3 = 1 + 2 + 3 + 3'"
  (let* ((G (symmetric-group 4)) (T (character-table G)) (r (char-table-rows T)))
    (assert-equal (char-decompose T (char-tensor T (nth r 3) (nth r 3))) '(1 0 1 1 1))
    (assert-equal (char-decompose T (char-tensor T (nth r 3) (nth r 4))) '(0 1 1 1 1))))

(deftest "repr: сопряжённый характер и скалярное произведение"
  (let* ((G (cyclic-group 5)) (T (character-table G)) (r (char-table-rows T)))
    ; дуальный характер — снова неприводимый; для нетривиального линейного характера C5 он другой
    (for-each (lambda (row) (assert-true (member? (char-dual T row) r))) r)
    (assert-equal (char-dual T (car r)) (car r))
    (assert-true (not (equal? (char-dual T (nth r 1)) (nth r 1))))
    (assert-equal (char-inner T (nth r 1) (nth r 1)) 1)
    (assert-equal (char-inner T (nth r 1) (nth r 2)) 0)
    (assert-equal (char-decompose T (nth r 3)) '(0 0 0 1 0))
    ; ⟨χ, χ̄⟩ = 0 для нетривиального линейного (χ² ≠ 1)
    (assert-equal (char-inner T (nth r 1) (char-dual T (nth r 1))) 0)))

(deftest "repr: перестановочный характер S4 — тривиальный + трёхмерный, ⟨π, π⟩ = 2"
  (let* ((G (symmetric-group 4)) (T (character-table G)) (p (char-permutation T)) (m (char-decompose T p)))
    (assert-equal (map car p) '(4 0 2 1 0))
    (assert-equal (char-inner T p p) 2)
    (assert-equal (car m) 1)
    (assert-equal (apply + (map2 * m (char-table-degrees T))) 4)
    (assert-equal (apply + (map (lambda (x) (* x x)) m)) 2)))

(deftest "repr: не характер — unknown"
  (let* ((G (symmetric-group 3)) (T (character-table G)))
    (assert-equal (char-decompose T '(1 2 3)) 'unknown)
    (assert-equal (char-decompose T '(1 1 3/2)) 'unknown)
    (assert-error (char-decompose T '(1 1)))
    (assert-error (char-decompose T '(1 1 1.5)))))

; ---------- по матрицам образующих ----------

(deftest "repr: матрицы образующих S3 — подстановочное представление = 1 + 2"
  (let* ((G (symmetric-group 3)) (T (character-table G))
         (a '((0 1 0) (1 0 0) (0 0 1))) (b '((0 1 0) (0 0 1) (1 0 0)))
         (chi (char-from-matrices T (list a b))))
    (assert-equal chi (char-permutation T))
    (assert-equal (char-decompose T chi) '(1 0 1))))

(deftest "repr: матрицы с %i — двумерное представление Q8 и характер C3 через exp"
  (let* ((Q (quaternion-group)) (T (character-table Q))
         (chi (char-from-matrices T (list (list (list '%i 0) (list 0 (list '* -1 '%i)))
                                          (list (list 0 1) (list -1 0))))))
    (assert-equal (char-decompose T chi) '(0 0 0 0 1))
    (assert-equal (map car chi) '(2 -2 0 0 0)))
  (let* ((G (cyclic-group 3)) (T (character-table G))
         (w '(exp (* 2/3 %i pi)))
         (chi (char-from-matrices T (list (list (list w))))))
    (assert-equal (char-decompose T chi) '(0 1 0))))

(deftest "repr: матрицы, не задающие представление, — ошибка"
  (let* ((G (symmetric-group 3)) (T (character-table G)) (a '((0 1 0) (1 0 0) (0 0 1))))
    (assert-error (char-from-matrices T (list a a)))
    (assert-error (char-from-matrices T (list a)))
    (assert-error (char-from-matrices T (list a '((1 0) (0 1)))))))

; ---------- сертификат и подделки ----------

(deftest "repr: подделка — одно значение изменено"
  (let* ((G (symmetric-group 3)))
    (assert-equal (car (character-table-check G '((1 1 1) (1 -1 1) (2 0 -2)))) 'mismatch)
    (assert-equal (car (character-table-check G '((1 1 1) (1 -1 1) (2 1 -1)))) 'mismatch)
    (assert-equal (car (character-table-check G '((1 1 1) (1 -1 1) (2 0 -1)))) 'exact)))

(deftest "repr: подделка — перестановка двух значений, знак строки, дубль, не хватает строки"
  (let* ((G (symmetric-group 4)))
    (assert-equal (car (character-table-check G '((1 1 1 1 1) (1 1 -1 1 -1) (2 2 0 -1 0) (3 -1 1 0 -1) (3 -1 -1 0 1)))) 'exact)
    ; значения 1 и -1 переставлены в линейном характере
    (assert-equal (car (character-table-check G '((1 1 1 1 1) (1 -1 1 1 -1) (2 2 0 -1 0) (3 -1 1 0 -1) (3 -1 -1 0 1)))) 'mismatch)
    ; строка с обратным знаком
    (assert-equal (car (character-table-check G '((1 1 1 1 1) (1 1 -1 1 -1) (2 2 0 -1 0) (-3 1 -1 0 1) (3 -1 -1 0 1)))) 'mismatch)
    ; дубль строки вместо одной
    (assert-equal (car (character-table-check G '((1 1 1 1 1) (1 1 -1 1 -1) (2 2 0 -1 0) (3 -1 1 0 -1) (3 -1 1 0 -1)))) 'mismatch)
    ; не хватает строки
    (assert-equal (car (character-table-check G '((1 1 1 1 1) (1 1 -1 1 -1) (2 2 0 -1 0) (3 -1 1 0 -1)))) 'mismatch)
    ; неверная длина строки
    (assert-equal (car (character-table-check G '((1 1 1 1) (1 1 -1 1 -1) (2 2 0 -1 0) (3 -1 1 0 -1) (3 -1 -1 0 1)))) 'mismatch)))

(deftest "repr: подделка таблицы A4 и A5 (комплексные и иррациональные значения)"
  (let* ((G (alternating-group 4)) (T (character-table G)) (rows (char-table-rows T))
         (bad (char-table-with-rows T (list (nth rows 0) (nth rows 1) (nth rows 1) (nth rows 3)))))
    (assert-equal (car (character-table-check G T)) 'exact)
    (assert-equal (car (character-table-check G bad)) 'mismatch)
    (assert-equal (car (character-table-check G (char-table->exprs T))) 'exact))
  (let* ((G (alternating-group 5)) (ex (rpt-rows G))
         (swap (list (nth ex 0) (nth ex 1) (nth ex 1) (nth ex 3) (nth ex 4))))
    (assert-equal (car (character-table-check G ex)) 'exact)
    (assert-equal (car (character-table-check G swap)) 'mismatch)))

(deftest "repr: сертификат — значения не разобраны, unknown"
  (let* ((G (symmetric-group 3)))
    (assert-equal (car (character-table-check G '((1 1 1) (1 -1 1) (2 0 foo)))) 'unknown)
    (assert-equal (car (character-table-check G '((1 1 1) (1 -1 1) (2 0 1.5)))) 'unknown)))

(deftest "repr: сертификат одной группы не принимает таблицу другой"
  (let ((T (character-table (symmetric-group 3))))
    (assert-equal (car (character-table-check (cyclic-group 6) T)) 'mismatch)
    (assert-equal (car (character-table-check (dihedral-group 3) T)) 'exact)))

; ---------- язык ----------

(deftest "repr: язык — классы, таблица, разложение, сертификат"
  (assert-equal (math-eval "character_table(symmetric_group(3))") (math-eval "[[1, 1, 1], [1, -1, 1], [2, 0, -1]]"))
  (assert-equal (math-eval "character_degrees(symmetric_group(4))") (math-eval "[1, 1, 2, 3, 3]"))
  (assert-equal (math-eval "group_order(alternating_group(5))") 60)
  (assert-equal (math-eval "decompose_character(symmetric_group(3), regular_character(symmetric_group(3)))") (math-eval "[1, 1, 2]"))
  (assert-equal (math-eval "decompose_character(symmetric_group(3), character_tensor(symmetric_group(3), [2, 0, -1], [2, 0, -1]))")
                (math-eval "[1, 1, 1]"))
  (assert-equal (math-eval "character_table_check(quaternion_group())") (math-eval "[exact, true, true, true, true, true]"))
  (assert-equal (math-eval "character_table_check(symmetric_group(3), [[1, 1, 1], [1, -1, 1], [2, 0, -2]])")
                (math-eval "[mismatch, false, false, true, true, false]"))
  (assert-equal (math-eval "character_of_representation(symmetric_group(3), [[[0,1,0],[1,0,0],[0,0,1]], [[0,1,0],[0,0,1],[1,0,0]]])")
                (math-eval "[3, 1, 0]"))
  (assert-equal (math-eval "character_symmetric_square(symmetric_group(3), [2, 0, -1])") (math-eval "[3, 1, 0]"))
  (assert-equal (math-eval "character_alternating_square(symmetric_group(3), [2, 0, -1])") (math-eval "[1, -1, 1]"))
  (assert-equal (math-eval "permutation_character(symmetric_group(4))") (math-eval "[4, 0, 2, 1, 0]"))
  (assert-equal (math-eval "character_inner(symmetric_group(3), [2, 0, -1], [2, 0, -1])") 1)
  (assert-equal (math-eval "character_degrees(permutation_group(4, [[1, 2]], [[1, 2, 3, 4]]))") (math-eval "[1, 1, 2, 3, 3]"))
  (assert-error (math-eval "character_table(5)"))
  (assert-error (math-eval "permutation_group(3, [[1, 5]])"))
  (assert-error (math-eval "permutation_group(3, [[1, 2], [2, 3]])")))

(deftest "repr: язык — значения A4 и A5 возвращаются в язык (круговой путь)"
  (assert-equal (math-eval "character_table_check(alternating_group(4), character_table(alternating_group(4)))")
                (math-eval "[exact, true, true, true, true, true]"))
  (assert-equal (math-eval "character_table_check(alternating_group(5), character_table(alternating_group(5)))")
                (math-eval "[exact, true, true, true, true, true]"))
  (assert-equal (math-eval "character_inner(alternating_group(4), character_table(alternating_group(4))[1], character_table(alternating_group(4))[1])") 1))
