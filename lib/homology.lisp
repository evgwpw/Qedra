; Шаг HOM: гомологии симплициальных комплексов над Z и нормальная форма Смита.
; Матрица — список строк (целые числа). Нормальная форма Смита: U·A·V = D, U, V обратимы над Z (det = ±1),
; D диагональна, d1 | d2 | … (классический алгоритм: элементарные преобразования строк и столбцов с наименьшим по модулю ведущим).
; Комплекс — список (complex S0 S1 … Sd): Sk — отсортированный список k-симплексов, симплекс — список вершин по возрастанию
; (числа по значению, затем остальные атомы по строковой записи). Ориентация симплекса — по возрастанию вершин,
; граница ∂[v0..vk] = Σ (−1)^i [v0..v̂i..vk]. H_k = ker ∂_k / im ∂_{k+1}: ранг b_k = c_k − r_k − r_{k+1}, кручение — инвариантные множители ∂_{k+1}, большие 1.
; Ответ homology — список (b (t1 t2 …)) по размерностям k = 0..d: H_k = Z^b ⊕ Z/t1 ⊕ Z/t2 ⊕ …
(module homology
  (export smith-form smith-invariants smith-check simplicial-complex complex-from-simplices complex? complex-closed?
          complex-dimension complex-faces boundary-matrix homology homology-text betti euler-characteristic homology-check
          sphere-complex circle-complex disk-complex torus-complex projective-plane-complex klein-bottle-complex))

; ---------- матрицы как векторы векторов ----------

(define (hm-for a b f)
  (let loop ((i a)) (if (< i b) (begin (f i) (loop (+ i 1))) '())))

(define (hm-mat l) (list->vector (map list->vector l)))
(define (hm-unmat v) (map vector->list (vector->list v)))
(define (hm-ref m i j) (vref (vref m i) j))
(define (hm-set! m i j x) (vset! (vref m i) j x))
(define (hm-zero-list m n) (map (lambda (i) (map (lambda (j) 0) (range n))) (range m)))
(define (hm-id-list n) (map (lambda (i) (map (lambda (j) (if (= i j) 1 0)) (range n))) (range n)))

(define (hm-row-add! M i k q ncols)
  (hm-for 0 ncols (lambda (j) (hm-set! M i j (+ (hm-ref M i j) (* q (hm-ref M k j)))))))
(define (hm-col-add! M j k q nrows)
  (hm-for 0 nrows (lambda (i) (hm-set! M i j (+ (hm-ref M i j) (* q (hm-ref M i k)))))))
(define (hm-row-swap! M i k) (let ((r (vref M i))) (vset! M i (vref M k)) (vset! M k r)))
(define (hm-col-swap! M j k nrows)
  (hm-for 0 nrows (lambda (i) (let ((x (hm-ref M i j))) (hm-set! M i j (hm-ref M i k)) (hm-set! M i k x)))))
(define (hm-row-neg! M i ncols)
  (hm-for 0 ncols (lambda (j) (hm-set! M i j (- 0 (hm-ref M i j))))))

(define (hm-transpose rows n) (map (lambda (j) (map (lambda (r) (nth r j)) rows)) (range n)))

(define (hm-matmul A B)
  (if (or (null? A) (null? B))
      '()
      (let ((cols (hm-transpose B (length (car B)))))
        (map (lambda (r) (map (lambda (c) (apply + (map2 * r c))) cols)) A))))

; определитель целочисленной матрицы (Бареисс, точное деление)
(define (hm-det rows)
  (let ((n (length rows)) (M (hm-mat rows)) (sign 1) (prev 1) (zero #f))
    (hm-for 0 (- n 1)
      (lambda (k)
        (if (not zero)
            (begin
              (if (= (hm-ref M k k) 0)
                  (let ((r #f))
                    (hm-for (+ k 1) n (lambda (i) (if (and (not r) (not (= (hm-ref M i k) 0))) (set! r i))))
                    (if r
                        (begin (hm-row-swap! M k r) (set! sign (- 0 sign)))
                        (set! zero #t))))
              (if (not zero)
                  (begin
                    (hm-for (+ k 1) n
                      (lambda (i)
                        (hm-for (+ k 1) n
                          (lambda (j)
                            (hm-set! M i j (quotient (- (* (hm-ref M i j) (hm-ref M k k)) (* (hm-ref M i k) (hm-ref M k j))) prev))))))
                    (set! prev (hm-ref M k k))))))))
    (if zero 0 (* sign (hm-ref M (- n 1) (- n 1))))))

; ---------- нормальная форма Смита ----------

; rows — список строк m×n (m, n ≥ 1); результат (D U V)
(define (hm-smith-core rows m n)
  (let ((A (hm-mat rows)) (U (hm-mat (hm-id-list m))) (V (hm-mat (hm-id-list n))))
    (define (radd! i k q) (hm-row-add! A i k q n) (hm-row-add! U i k q m))
    (define (cadd! j k q) (hm-col-add! A j k q m) (hm-col-add! V j k q n))
    (define (rswap! i k) (hm-row-swap! A i k) (hm-row-swap! U i k))
    (define (cswap! j k) (hm-col-swap! A j k m) (hm-col-swap! V j k n))
    ; ненулевой элемент подматрицы [t.., t..] с наименьшим модулем: (i j) или #f
    (define (find-pivot t)
      (let ((best #f) (bv 0))
        (hm-for t m
          (lambda (i)
            (hm-for t n
              (lambda (j)
                (let ((x (abs (hm-ref A i j))))
                  (if (and (> x 0) (or (not best) (< x bv)))
                      (begin (set! best (list i j)) (set! bv x))))))))
        best))
    ; делает ведущий элемент t делителем строки t, столбца t и всей подматрицы
    (define (reduce! t)
      (let loop ()
        (let ((p (hm-ref A t t)))
          (hm-for (+ t 1) m (lambda (i) (radd! i t (- 0 (quotient (hm-ref A i t) p)))))
          (hm-for (+ t 1) n (lambda (j) (cadd! j t (- 0 (quotient (hm-ref A t j) p)))))
          (let ((best #f) (bv 0) (kind #f))
            (hm-for (+ t 1) m
              (lambda (i)
                (let ((x (abs (hm-ref A i t))))
                  (if (and (> x 0) (or (not best) (< x bv))) (begin (set! best i) (set! bv x) (set! kind 'row))))))
            (hm-for (+ t 1) n
              (lambda (j)
                (let ((x (abs (hm-ref A t j))))
                  (if (and (> x 0) (or (not best) (< x bv))) (begin (set! best j) (set! bv x) (set! kind 'col))))))
            (cond ((equal? kind 'row) (rswap! t best) (loop))
                  ((equal? kind 'col) (cswap! t best) (loop))
                  (else
                   (let ((bad #f))
                     (hm-for (+ t 1) m
                       (lambda (i)
                         (hm-for (+ t 1) n
                           (lambda (j)
                             (if (and (not bad) (not (= (remainder (hm-ref A i j) p) 0))) (set! bad i))))))
                     (if bad (begin (radd! t bad 1) (loop)) '()))))))))
    (let outer ((t 0))
      (if (< t (min m n))
          (let ((pv (find-pivot t)))
            (if pv
                (begin
                  (if (not (= (car pv) t)) (rswap! t (car pv)))
                  (if (not (= (cadr pv) t)) (cswap! t (cadr pv)))
                  (reduce! t)
                  (if (< (hm-ref A t t) 0) (begin (hm-row-neg! A t n) (hm-row-neg! U t m)))
                  (outer (+ t 1)))
                '()))
          '()))
    (list (hm-unmat A) (hm-unmat U) (hm-unmat V))))

(define (hm-int? x) (and (integer? x) (equal? (type-of x) 'integer)))

(define (hm-check-matrix name A)
  (if (not (and (list? A) (not (null? A)) (every? (lambda (r) (and (list? r) (not (null? r)))) A)))
      (error (string-append name ": ожидается непустая матрица — список строк")))
  (if (not (every? (lambda (r) (= (length r) (length (car A)))) A))
      (error (string-append name ": строки матрицы разной длины")))
  (if (not (every? (lambda (r) (every? hm-int? r)) A))
      (error (string-append name ": элементы матрицы должны быть целыми числами"))))

; (smith-form A) → (D U V): U·A·V = D
(define (smith-form A)
  (hm-check-matrix "smith-form" A)
  (hm-smith-core A (length A) (length (car A))))

(define (hm-diag D)
  (map (lambda (i) (nth (nth D i) i)) (range (min (length D) (length (car D))))))

; (smith-invariants A) → ненулевые инвариантные множители d1 | d2 | …
(define (smith-invariants A)
  (filter (lambda (x) (not (= x 0))) (hm-diag (car (smith-form A)))))

; (smith-check A) → #t, если U·A·V = D, |det U| = |det V| = 1, D диагональна, d_i ≥ 0 и d_i | d_{i+1}
(define (smith-check A)
  (let* ((S (smith-form A)) (D (car S)) (U (cadr S)) (V (caddr S)) (m (length D)) (n (length (car D))))
    (let ((dg (hm-diag D)))
      (and (equal? (hm-matmul (hm-matmul U A) V) D)
           (= (abs (hm-det U)) 1)
           (= (abs (hm-det V)) 1)
           (every? (lambda (i) (every? (lambda (j) (or (= i j) (= (nth (nth D i) j) 0))) (range n))) (range m))
           (every? (lambda (x) (>= x 0)) dg)
           (let loop ((l dg))
             (cond ((or (null? l) (null? (cdr l))) #t)
                   ((= (car l) 0) (and (= (cadr l) 0) (loop (cdr l))))
                   (else (and (= (remainder (cadr l) (car l)) 0) (loop (cdr l))))))))))

; ---------- комплекс ----------

(define (hm-vertex? v) (or (number? v) (symbol? v) (string? v)))

(define (hm-vless a b)
  (cond ((and (number? a) (number? b)) (< a b))
        ((number? a) #t)
        ((number? b) #f)
        (else (string<? (to-string a) (to-string b)))))

(define (hm-sless a b)
  (cond ((null? a) #f)
        ((hm-vless (car a) (car b)) #t)
        ((hm-vless (car b) (car a)) #f)
        (else (hm-sless (cdr a) (cdr b)))))

(define (hm-sort-simplex s)
  (if (not (and (list? s) (not (null? s)) (every? hm-vertex? s)))
      (error "simplicial-complex: симплекс — непустой список вершин (числа, символы, строки)"))
  (let ((r (sort s hm-vless)))
    (let loop ((l r))
      (cond ((or (null? l) (null? (cdr l))) r)
            ((equal? (car l) (cadr l)) (error "simplicial-complex: повторяющаяся вершина в симплексе" s))
            (else (loop (cdr l)))))))

; все непустые подсписки с сохранением порядка
(define (hm-subsets l)
  (if (null? l)
      '()
      (let ((rest (hm-subsets (cdr l))))
        (append (list (list (car l))) rest (map (lambda (s) (cons (car l) s)) rest)))))

(define (hm-group-by-dim simplices)
  (let ((d (- (foldl (lambda (acc s) (max acc (length s))) 0 simplices) 1)))
    (cons 'complex
          (map (lambda (k) (sort (filter (lambda (f) (= (length f) (+ k 1))) simplices) hm-sless))
               (range (+ d 1))))))

; (simplicial-complex максимальные-симплексы) — замыкание по граням
(define (simplicial-complex maxes)
  (if (not (and (list? maxes) (not (null? maxes))))
      (error "simplicial-complex: ожидается непустой список симплексов"))
  (let ((seen (make-hash)) (all '()))
    (for-each
      (lambda (s0)
        (for-each
          (lambda (f)
            (if (not (hash-has? seen f))
                (begin (hash-set! seen f #t) (set! all (cons f all)))))
          (hm-subsets (hm-sort-simplex s0))))
      maxes)
    (hm-group-by-dim all)))

(define (complex? K)
  (and (pair? K) (equal? (car K) 'complex) (list? K) (not (null? (cdr K)))
       (every? list? (cdr K))))

(define (hm-need-complex name K)
  (if (not (complex? K)) (error (string-append name ": ожидается комплекс (simplicial-complex …)"))))

(define (complex-dimension K) (hm-need-complex "complex-dimension" K) (- (length K) 2))

; (complex-faces K k) — симплексы размерности k (пустой список вне 0..dim)
(define (complex-faces K k)
  (hm-need-complex "complex-faces" K)
  (if (or (< k 0) (> k (- (length K) 2))) '() (nth (cdr K) k)))

(define (hm-index-hash simplices)
  (let ((h (make-hash)))
    (let loop ((l simplices) (i 0))
      (if (null? l) h (begin (hash-set! h (car l) i) (loop (cdr l) (+ i 1)))))))

; замкнут по граням: каждая грань каждого симплекса есть в комплексе
(define (complex-closed? K)
  (hm-need-complex "complex-closed?" K)
  (let ((d (- (length K) 2)))
    (every?
      (lambda (k)
        (or (= k 0)
            (let ((h (hm-index-hash (nth (cdr K) (- k 1)))))
              (every? (lambda (s)
                        (every? (lambda (i) (hash-has? h (append (take s i) (drop s (+ i 1)))))
                                (range (+ k 1))))
                      (nth (cdr K) k)))))
      (range (+ d 1)))))

; (complex-from-simplices все-симплексы) — явное задание: незамкнутый набор — ошибка
(define (complex-from-simplices simplices)
  (if (not (and (list? simplices) (not (null? simplices))))
      (error "complex-from-simplices: ожидается непустой список симплексов"))
  (let ((seen (make-hash)) (all '()))
    (for-each
      (lambda (s0)
        (let ((s (hm-sort-simplex s0)))
          (if (not (hash-has? seen s)) (begin (hash-set! seen s #t) (set! all (cons s all))))))
      simplices)
    (let ((K (hm-group-by-dim all)))
      (if (not (every? (lambda (l) (not (null? l))) (cdr K)))
          (error "complex-from-simplices: нет симплексов некоторой размерности — набор не замкнут по граням"))
      (if (not (complex-closed? K))
          (error "complex-from-simplices: набор не замкнут по граням (у симплекса нет грани)"))
      K)))

; ---------- границы и гомологии ----------

; (boundary-matrix K k): строки — (k−1)-симплексы, столбцы — k-симплексы; знак (−1)^i при удалении i-й вершины; k = 0 — ()
(define (boundary-matrix K k)
  (hm-need-complex "boundary-matrix" K)
  (cond ((or (< k 0) (> k (complex-dimension K))) (error "boundary-matrix: размерность вне 0..dim" k))
        ((= k 0) '())
        (else
         (let* ((rows (complex-faces K (- k 1))) (cols (complex-faces K k))
                (idx (hm-index-hash rows))
                (mat (hm-mat (hm-zero-list (length rows) (length cols)))))
           (let loop ((l cols) (c 0))
             (if (null? l)
                 '()
                 (begin
                   (hm-for 0 (+ k 1)
                     (lambda (i)
                       (let ((r (hash-ref idx (append (take (car l) i) (drop (car l) (+ i 1))) #f)))
                         (if (not r) (error "boundary-matrix: комплекс не замкнут по граням"))
                         (hm-set! mat r c (if (= (modulo i 2) 0) 1 -1)))))
                   (loop (cdr l) (+ c 1)))))
           (hm-unmat mat)))))

; инвариантные множители ∂_k для k = 0..d+1 (индексы 0 и d+1 — пусто)
(define (hm-all-invs K)
  (let ((d (complex-dimension K)))
    (map (lambda (k)
           (if (or (= k 0) (> k d))
               '()
               (let ((A (boundary-matrix K k)))
                 (filter (lambda (x) (not (= x 0)))
                         (hm-diag (car (hm-smith-core A (length A) (length (car A)))))))))
         (range (+ d 2)))))

; (homology K) → ((b0 (t…)) (b1 (t…)) …)
(define (homology K)
  (hm-need-complex "homology" K)
  (let ((invs (hm-all-invs K)) (d (complex-dimension K)))
    (map (lambda (k)
           (let ((c (length (complex-faces K k))) (rk (length (nth invs k))) (rk1 (length (nth invs (+ k 1)))))
             (list (- c rk rk1) (filter (lambda (x) (> x 1)) (nth invs (+ k 1))))))
         (range (+ d 1)))))

(define (betti K) (map car (homology K)))

(define (euler-characteristic K)
  (hm-need-complex "euler-characteristic" K)
  (let loop ((l (cdr K)) (k 0) (s 0))
    (if (null? l) s (loop (cdr l) (+ k 1) (+ s (* (if (= (modulo k 2) 0) 1 -1) (length (car l))))))))

(define (hm-group-text b ts)
  (let ((parts (append (cond ((= b 0) '()) ((= b 1) (list "Z")) (else (list (string-append "Z^" (to-string b)))))
                       (map (lambda (t) (string-append "Z/" (to-string t))) ts))))
    (if (null? parts) "0" (string-join parts " + "))))

; (homology-text K) → ("Z" "Z^2 + Z/2" "0" …)
(define (homology-text K)
  (map (lambda (h) (hm-group-text (car h) (cadr h))) (homology K)))

(define (hm-all-zero? A) (every? (lambda (r) (every? (lambda (x) (= x 0)) r)) A))

; (homology-check K) → (ok ∂∂=0 Смит χ=Σb χ): ∂_{k−1}∂_k = 0, U·A·V = D для всех ∂_k, Σ(−1)^k c_k = Σ(−1)^k b_k
(define (homology-check K)
  (hm-need-complex "homology-check" K)
  (let* ((d (complex-dimension K))
         (dd (every? (lambda (k) (hm-all-zero? (hm-matmul (boundary-matrix K (- k 1)) (boundary-matrix K k))))
                     (filter (lambda (k) (>= k 2)) (range (+ d 1)))))
         (sm (every? (lambda (k) (smith-check (boundary-matrix K k)))
                     (filter (lambda (k) (>= k 1)) (range (+ d 1)))))
         (chi (euler-characteristic K))
         (chib (let loop ((l (betti K)) (k 0) (s 0))
                 (if (null? l) s (loop (cdr l) (+ k 1) (+ s (* (if (= (modulo k 2) 0) 1 -1) (car l)))))))
         (eu (= chi chib)))
    (list (and dd sm eu) dd sm eu chi)))

; ---------- готовые триангуляции ----------

; граница (n+1)-симплекса: все n+1-элементные подмножества {0..n+1}; n = 0 — две точки
(define (sphere-complex n)
  (if (not (and (hm-int? n) (>= n 0))) (error "sphere-complex: ожидается целое n ≥ 0"))
  (simplicial-complex
    (map (lambda (skip) (filter (lambda (v) (not (= v skip))) (range (+ n 2)))) (range (+ n 2)))))

(define (circle-complex) (sphere-complex 1))
(define (disk-complex) (simplicial-complex '((0 1 2))))

; минимальный тор: 7 вершин, 14 треугольников {i, i+1, i+3} и {i, i+2, i+3} по модулю 7
(define (torus-complex)
  (simplicial-complex
    (append-map (lambda (i)
                  (list (list i (modulo (+ i 1) 7) (modulo (+ i 3) 7))
                        (list i (modulo (+ i 2) 7) (modulo (+ i 3) 7))))
                (range 7))))

; минимальная проективная плоскость: 6 вершин, 10 треугольников
(define (projective-plane-complex)
  (simplicial-complex
    '((1 2 3) (1 3 4) (1 4 5) (1 5 6) (1 6 2) (2 3 5) (3 4 6) (4 5 2) (5 6 3) (6 2 4))))

; бутылка Клейна: сетка 4×4, (x, y) ~ (x, y+4), (4, y) ~ (0, −y); вершины 4i + j, 32 треугольника
(define (hm-klein-v i j m n)
  (if (>= i m)
      (hm-klein-v (- i m) (- 0 j) m n)
      (+ (* i n) (modulo j n))))

(define (klein-bottle-complex)
  (let ((m 4) (n 4))
    (simplicial-complex
      (append-map
        (lambda (i)
          (append-map
            (lambda (j)
              (let ((a (hm-klein-v i j m n)) (b (hm-klein-v (+ i 1) j m n))
                    (c (hm-klein-v (+ i 1) (+ j 1) m n)) (d (hm-klein-v i (+ j 1) m n)))
                (list (list a b c) (list a c d))))
            (range n)))
        (range m)))))
