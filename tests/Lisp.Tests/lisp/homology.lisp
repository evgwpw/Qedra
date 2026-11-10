; homology.lisp — тесты шага HOM: нормальная форма Смита и гомологии симплициальных комплексов над Z.
; Оракулы: (1) известные группы гомологий (окружность, S², S³, тор, проективная плоскость, бутылка Клейна, диск,
; два несвязных треугольника); (2) Смит: известные примеры, 20 псевдослучайных матриц (фиксированный генератор) с
; независимой проверкой U·A·V = D (своим умножением), det = ±1 (builtin det), делимостью и |det A| = Π dᵢ;
; (3) ∂∂ = 0, числа симплексов, χ двумя путями; (4) подделки: незамкнутый набор граней, нецелая матрица, дубль вершины.

(define (hmt-mul A B)
  (map (lambda (r)
         (map (lambda (j) (apply + (map (lambda (k) (* (nth r k) (nth (nth B k) j))) (range (length B)))))
              (range (length (car B)))))
       A))

; линейный конгруэнтный генератор: следующее состояние и значение в -9..9
(define (hmt-next s) (modulo (+ (* s 1103515245) 12345) 2147483648))
(define (hmt-val s) (- (modulo (quotient s 65536) 19) 9))
(define (hmt-matrix m n seed)
  (let loop ((i 0) (s seed) (rows '()))
    (if (= i m)
        (list (reverse rows) s)
        (let rl ((j 0) (s s) (row '()))
          (if (= j n)
              (loop (+ i 1) s (cons (reverse row) rows))
              (let ((s2 (hmt-next s))) (rl (+ j 1) s2 (cons (hmt-val s2) row))))))))
(define (hmt-matrices count m n seed)
  (let loop ((c 0) (s seed) (acc '()))
    (if (= c count)
        (reverse acc)
        (let ((r (hmt-matrix m n s))) (loop (+ c 1) (cadr r) (cons (car r) acc))))))

(define (hmt-chain-ok? ds)
  (cond ((or (null? ds) (null? (cdr ds))) #t)
        ((= (car ds) 0) (and (= (cadr ds) 0) (hmt-chain-ok? (cdr ds))))
        (else (and (= (remainder (cadr ds) (car ds)) 0) (hmt-chain-ok? (cdr ds))))))

(define (hmt-diag D) (map (lambda (i) (nth (nth D i) i)) (range (min (length D) (length (car D))))))

; независимая проверка одной матрицы: возвращает #t, если все свойства Смита выполнены
(define (hmt-smith-ok? A)
  (let* ((S (smith-form A)) (D (car S)) (U (cadr S)) (V (caddr S)) (dg (hmt-diag D)))
    (and (equal? (hmt-mul (hmt-mul U A) V) D)
         (= (abs (det U)) 1)
         (= (abs (det V)) 1)
         (= (length D) (length A))
         (= (length (car D)) (length (car A)))
         (every? (lambda (i) (every? (lambda (j) (or (= i j) (= (nth (nth D i) j) 0))) (range (length (car D)))))
                 (range (length D)))
         (every? (lambda (x) (>= x 0)) dg)
         (hmt-chain-ok? dg)
         (equal? (smith-invariants A) (filter (lambda (x) (> x 0)) dg)))))

; ---- Смит: известные примеры ----
(deftest "smith: известный пример diag(2, 6, 12)"
  (assert-equal (smith-invariants '((2 4 4) (-6 6 12) (10 -4 -16))) '(2 6 12))
  (assert-equal (car (smith-form '((2 4 4) (-6 6 12) (10 -4 -16)))) '((2 0 0) (0 6 0) (0 0 12)))
  (assert-true (hmt-smith-ok? '((2 4 4) (-6 6 12) (10 -4 -16)))))

(deftest "smith: простые случаи"
  (assert-equal (smith-invariants '((2 0) (0 3))) '(1 6))
  (assert-equal (smith-invariants '((1 2) (2 4))) '(1))
  (assert-equal (smith-invariants '((0 0) (0 0))) '())
  (assert-equal (smith-invariants '((-5))) '(5))
  (assert-equal (smith-invariants '((4 6))) '(2))
  (assert-equal (smith-invariants '((6) (10) (15))) '(1))
  (assert-equal (smith-invariants '((2 0 0) (0 4 0) (0 0 6))) '(2 2 12))
  (assert-equal (smith-invariants '((0 3) (5 0))) '(1 15)))

(deftest "smith: прямоугольные и вырожденные матрицы"
  (assert-true (hmt-smith-ok? '((1 2 3) (4 5 6))))
  (assert-true (hmt-smith-ok? '((1 2) (3 4) (5 6))))
  (assert-true (hmt-smith-ok? '((0 0 0) (0 0 0))))
  (assert-true (hmt-smith-ok? '((0 6 0) (4 0 0) (0 0 0))))
  (assert-true (hmt-smith-ok? '((12 8 4) (9 6 3) (30 20 10))))
  (assert-true (smith-check '((2 4 4) (-6 6 12) (10 -4 -16)))))

(deftest "smith: 20 случайных матриц 3×4 и 4×4"
  (let ((ms (append (hmt-matrices 10 3 4 12345) (hmt-matrices 10 4 4 987))))
    (assert-equal (length ms) 20)
    (assert-true (every? hmt-smith-ok? ms))
    (assert-true (every? smith-check ms))))

(deftest "smith: |det A| = произведение инвариантов у невырожденных 4×4"
  (let ((ms (hmt-matrices 10 4 4 987)))
    (assert-true
      (every? (lambda (A)
                (let ((d (det A)) (iv (smith-invariants A)))
                  (if (= d 0)
                      (< (length iv) 4)
                      (and (= (length iv) 4) (= (abs d) (apply * iv))))))
              ms))))

(deftest "smith: ошибки — нецелые, пустые, неровные"
  (assert-error (smith-form '((1 2.5) (3 4))))
  (assert-error (smith-form '((1 1/2))))
  (assert-error (smith-form '((1 a))))
  (assert-error (smith-form '()))
  (assert-error (smith-form '((1 2) (3))))
  (assert-error (smith-form 5)))

; ---- гомологии: оракул ----
(define (hmt-hom K) (homology K))
(define two-triangles (simplicial-complex '((1 2 3) (4 5 6))))

(deftest "гомологии: окружность"
  (assert-equal (hmt-hom (circle-complex)) '((1 ()) (1 ())))
  (assert-equal (betti (circle-complex)) '(1 1))
  (assert-equal (euler-characteristic (circle-complex)) 0)
  (assert-equal (homology-text (circle-complex)) '("Z" "Z")))

(deftest "гомологии: сфера S² (граница тетраэдра)"
  (assert-equal (hmt-hom (sphere-complex 2)) '((1 ()) (0 ()) (1 ())))
  (assert-equal (betti (sphere-complex 2)) '(1 0 1))
  (assert-equal (euler-characteristic (sphere-complex 2)) 2)
  (assert-equal (map length (cdr (sphere-complex 2))) '(4 6 4)))

(deftest "гомологии: сфера S³ и S⁰"
  (assert-equal (hmt-hom (sphere-complex 3)) '((1 ()) (0 ()) (0 ()) (1 ())))
  (assert-equal (euler-characteristic (sphere-complex 3)) 0)
  (assert-equal (map length (cdr (sphere-complex 3))) '(5 10 10 5))
  (assert-equal (hmt-hom (sphere-complex 0)) '((2 ())))
  (assert-equal (euler-characteristic (sphere-complex 4)) 2))

(deftest "гомологии: тор (7 вершин)"
  (assert-equal (hmt-hom (torus-complex)) '((1 ()) (2 ()) (1 ())))
  (assert-equal (betti (torus-complex)) '(1 2 1))
  (assert-equal (euler-characteristic (torus-complex)) 0)
  (assert-equal (map length (cdr (torus-complex))) '(7 21 14))
  (assert-equal (homology-text (torus-complex)) '("Z" "Z^2" "Z")))

(deftest "гомологии: проективная плоскость (6 вершин)"
  (assert-equal (hmt-hom (projective-plane-complex)) '((1 ()) (0 (2)) (0 ())))
  (assert-equal (betti (projective-plane-complex)) '(1 0 0))
  (assert-equal (euler-characteristic (projective-plane-complex)) 1)
  (assert-equal (map length (cdr (projective-plane-complex))) '(6 15 10))
  (assert-equal (homology-text (projective-plane-complex)) '("Z" "Z/2" "0")))

(deftest "гомологии: бутылка Клейна"
  (assert-equal (hmt-hom (klein-bottle-complex)) '((1 ()) (1 (2)) (0 ())))
  (assert-equal (betti (klein-bottle-complex)) '(1 1 0))
  (assert-equal (euler-characteristic (klein-bottle-complex)) 0)
  (assert-equal (homology-text (klein-bottle-complex)) '("Z" "Z + Z/2" "0"))
  (assert-equal (map length (cdr (klein-bottle-complex))) '(16 48 32)))

(deftest "гомологии: диск и два несвязных треугольника"
  (assert-equal (hmt-hom (disk-complex)) '((1 ()) (0 ()) (0 ())))
  (assert-equal (euler-characteristic (disk-complex)) 1)
  (assert-equal (hmt-hom two-triangles) '((2 ()) (0 ()) (0 ())))
  (assert-equal (betti two-triangles) '(2 0 0))
  (assert-equal (euler-characteristic two-triangles) 2))

(deftest "гомологии: произвольные вершины и несколько кручений"
  ; треугольник из символов — окружность
  (assert-equal (hmt-hom (simplicial-complex '((a b) (b c) (c a)))) '((1 ()) (1 ())))
  ; вершины-строки и числа вперемешку
  (assert-equal (betti (simplicial-complex '((1 "x") ("x" y) (y 1)))) '(1 1))
  ; треугольник с торчащим ребром — стягиваем
  (assert-equal (betti (simplicial-complex '((1 2 3) (3 4)))) '(1 0 0))
  ; букет двух окружностей
  (assert-equal (betti (simplicial-complex '((1 2) (2 3) (3 1) (3 4) (4 5) (5 3)))) '(1 2))
  ; букет двух проективных плоскостей (общая вершина 1): H1 = Z/2 + Z/2
  (let ((K (simplicial-complex
             (append '((1 2 3) (1 3 4) (1 4 5) (1 5 6) (1 6 2) (2 3 5) (3 4 6) (4 5 2) (5 6 3) (6 2 4))
                     '((1 12 13) (1 13 14) (1 14 15) (1 15 16) (1 16 12) (12 13 15) (13 14 16) (14 15 12) (15 16 13) (16 12 14))))))
    (assert-equal (hmt-hom K) '((1 ()) (0 (2 2)) (0 ())))
    (assert-equal (homology-text K) '("Z" "Z/2 + Z/2" "0"))
    (assert-true (car (homology-check K)))))

; ---- границы и ∂∂ = 0 ----
(deftest "∂∂ = 0 для всех готовых комплексов"
  (assert-true
    (every? (lambda (K)
              (every? (lambda (k)
                        (every? (lambda (r) (every? (lambda (x) (= x 0) ) r))
                                (hmt-mul (boundary-matrix K (- k 1)) (boundary-matrix K k))))
                      (filter (lambda (k) (>= k 2)) (range (+ (complex-dimension K) 1)))))
            (list (sphere-complex 2) (sphere-complex 3) (sphere-complex 4) (torus-complex)
                  (projective-plane-complex) (klein-bottle-complex) (disk-complex)))))

(deftest "граница: знаки и порядок"
  (let ((K (simplicial-complex '((1 2 3)))))
    (assert-equal (complex-faces K 1) '((1 2) (1 3) (2 3)))
    (assert-equal (boundary-matrix K 1) '((-1 -1 0) (1 0 -1) (0 1 1)))
    (assert-equal (boundary-matrix K 2) '((1) (-1) (1)))
    (assert-equal (boundary-matrix K 0) '())
    (assert-equal (complex-dimension K) 2)
    (assert-equal (complex-faces K 5) '())))

(deftest "сертификат homology-check"
  (assert-equal (homology-check (torus-complex)) '(#t #t #t #t 0))
  (assert-equal (homology-check (projective-plane-complex)) '(#t #t #t #t 1))
  (assert-true (every? (lambda (K) (car (homology-check K)))
                       (list (circle-complex) (sphere-complex 2) (sphere-complex 3) (klein-bottle-complex)
                             (disk-complex) two-triangles)))
  (assert-equal (cadr (cdr (cdr (homology-check (sphere-complex 2))))) #t))

(deftest "замыкание: явный набор с пропуском грани — ошибка"
  (assert-true (complex-closed? (torus-complex)))
  ; треугольник без ребра (1 2)
  (assert-error (complex-from-simplices '((1) (2) (3) (1 3) (2 3) (1 2 3))))
  ; нет вершины
  (assert-error (complex-from-simplices '((1 2) (1))))
  ; полный набор принимается
  (assert-equal (betti (complex-from-simplices '((1) (2) (3) (1 2) (1 3) (2 3)))) '(1 1))
  ; максимальные симплексы достраиваются сами
  (assert-equal (length (complex-faces (simplicial-complex '((1 2 3))) 1)) 3))

(deftest "ошибки: дубль вершины, пустой симплекс, не комплекс"
  (assert-error (simplicial-complex '((1 1 2))))
  (assert-error (simplicial-complex '(())))
  (assert-error (simplicial-complex '()))
  (assert-error (homology '(1 2 3)))
  (assert-error (boundary-matrix (torus-complex) 3))
  (assert-error (sphere-complex -1)))

(deftest "язык: smith_form и гомологии"
  (assert-equal (math-eval "smith_invariants([[2,4,4],[-6,6,12],[10,-4,-16]])")
                (math-eval "[2, 6, 12]"))
  (assert-equal (math-eval "betti(torus_complex())") (math-eval "[1, 2, 1]"))
  (assert-equal (math-eval "homology_text(klein_bottle_complex())") (math-eval "[\"Z\", \"Z + Z/2\", \"0\"]"))
  (assert-equal (math-eval "euler_characteristic(sphere_complex(2))") 2)
  (assert-error (math-eval "smith_form([[1, 1/2], [3, 4]])")))
