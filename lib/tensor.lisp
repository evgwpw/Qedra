; tensor.lisp — тензор как пользовательский тип на Lisp (Шаг 15)
;
; Представление: (make-object 'tensor shape data)
;   shape — LispVector целых (размерности), ранг >= 1 (скаляр — не тензор);
;   data  — LispVector компонент в порядке row-major; компоненты — любые выражения.
; Тип НЕкоммутативный (умножение двух тензоров — обобщённое скалярное произведение Dot).
; Везде, где аргумент «тензор», принимается и вложенный список (as-tensor).
; Вложенный список: вложенный список — уровень тензора, поэтому '(a b c) — вектор, КРОМЕ списков-выражений:
; список с головой-оператором (+ - * / ^) или символом, связанным с функцией (sin, sqrt, пользовательская),
; — компонента, а не уровень: (tensor (list 'x '(^ x 2))) — вектор из двух компонент.

; Шаг 21h': модуль tensor. Экспорт — API тензоров/матриц/векторов и представление (tensor-raw, tensor-shape-list, tensor-data,
; join-strings: ими пользуются mathlang и set); вспомогательные (find-pivot, rank-loop, det-terms ...) приватны —
; прежде они были глобальными, и в шаге 18 solve.lisp молча перезаписал find-pivot отсюда
(module tensor
  (export tensor? tensor tensor-raw tensor-shape-list tensor-data tensor-from-flat as-tensor make-tensor identity-matrix tensor->list
          shape rank-of strides tref transpose vec+ vec- scale dot norm cross mat mat-t mat-mul det inv rank
          outer contract join-strings))

(deftype 'tensor 'any)

; --- Внутреннее представление ---

(define (tensor-raw shape-list data) (make-object 'tensor (list->vector shape-list) data))
(define (tensor-shape-list a) (vector->list (object-ref a 0)))
(define (tensor-data a) (object-ref a 1))
(define (product l) (foldl * 1 l))

(define (tensor? x) (and (object? x) (equal? (object-type x) 'tensor)))

; --- Что считать уровнем тензора, а что компонентой-выражением (Шаг 15a) ---

; оператор математических выражений
(define (math-op? s) (member? s '(+ - * / ^)))

; список-выражение: голова — математический оператор или символ, связанный с функцией
(define (expr-list? x)
  (and (list? x) (not (null? x)) (symbol? (car x))
       (or (math-op? (car x)) (fbound? (car x)))))

; уровень тензора: список, не являющийся выражением
(define (level? x) (and (list? x) (not (expr-list? x))))

; --- Конструкторы ---

; форма вложенного списка; ошибка при рваной форме
(define (nested-shape x)
  (cond ((null? x) (error "tensor: пустой список не может быть тензором"))
        ((every? level? x)
         (let ((shapes (map nested-shape x)))
           (if (every? (lambda (s) (equal? s (car shapes))) shapes)
               (cons (length x) (car shapes))
               (error "tensor: рваная форма — подсписки разной формы"))))
        ((any? level? x) (error "tensor: рваная форма — смесь списков и скаляров"))
        (else (list (length x)))))

; компоненты вложенного списка в порядке row-major
(define (nested-flatten x)
  (if (every? level? x) (apply append (map nested-flatten x)) x))

; (tensor '((1 2) (3 4))) — из вложенного списка; тензор возвращается как есть
(define (tensor x)
  (cond ((tensor? x) x)
        ((list? x)
         (let ((sh (nested-shape x)))
           (tensor-raw sh (list->vector (nested-flatten x)))))
        (else (error "tensor: ожидается вложенный список или тензор, получено" x))))

(define (as-tensor x) (tensor x))

; (tensor-from-flat '(2 2) '(a b c d)) — из формы и плоского списка компонент (row-major)
(define (tensor-from-flat shape-list flat)
  (if (and (list? shape-list) (not (null? shape-list))
           (every? (lambda (d) (and (integer? d) (> d 0))) shape-list))
      (if (= (product shape-list) (length flat))
          (tensor-raw shape-list (list->vector flat))
          (error "tensor-from-flat: число компонент не соответствует форме" shape-list))
      (error "tensor-from-flat: форма — непустой список положительных целых")))

; все индексы формы (каждый — список) в порядке row-major
(define (all-indices shape)
  (if (null? shape)
      (list '())
      (let ((tails (all-indices (cdr shape))))
        (append-map (lambda (i) (map (lambda (tl) (cons i tl)) tails)) (range (car shape))))))

; (make-tensor '(2 3) (lambda (idx) ...)) — f получает список индексов
(define (make-tensor shape f)
  (if (and (list? shape) (not (null? shape))
           (every? (lambda (d) (and (integer? d) (> d 0))) shape))
      (tensor-raw shape (list->vector (map f (all-indices shape))))
      (error "make-tensor: форма — непустой список положительных целых")))

(define (identity-matrix n)
  (make-tensor (list n n) (lambda (idx) (if (= (car idx) (cadr idx)) 1 0))))

; --- Преобразования и свойства ---

(define (slice-acc v i from acc)
  (if (< i from) acc (slice-acc v (- i 1) from (cons (vref v i) acc))))
; n компонент вектора v начиная с индекса from — списком
(define (slice->list v from n) (slice-acc v (- (+ from n) 1) from '()))

(define (data->nested shape v off)
  (if (null? (cdr shape))
      (slice->list v off (car shape))
      (let ((block (product (cdr shape))))
        (map (lambda (i) (data->nested (cdr shape) v (+ off (* i block)))) (range (car shape))))))

; (tensor->list t) — вложенный список
(define (tensor->list a)
  (let ((tt (as-tensor a)))
    (data->nested (tensor-shape-list tt) (tensor-data tt) 0)))

; (shape t) — список размерностей; для не-тензора и не-списка — () (скаляр)
(define (shape x)
  (cond ((tensor? x) (tensor-shape-list x))
        ((null? x) (list 0))
        ((level? x) (nested-shape x))
        (else '())))

; число осей (не путать с матричным rank)
(define (rank-of x) (length (shape x)))

; шаги row-major: для формы (2 3 4) → (12 4 1)
(define (strides sh)
  (if (null? sh) '() (cons (product (cdr sh)) (strides (cdr sh)))))

(define (tref-walk a shape idx off)
  (cond ((null? idx)
         (if (null? shape)
             (vref (tensor-data a) off)
             (let ((block (product shape)))
               (tensor-raw shape (list->vector (slice->list (tensor-data a) (* off block) block))))))
        ((null? shape) (error "tref: слишком много индексов"))
        ((not (integer? (car idx))) (error "tref: индекс должен быть целым, получено" (car idx)))
        ((or (< (car idx) 0) (not (< (car idx) (car shape))))
         (error "tref: индекс вне границ" (car idx) "при размерности" (car shape)))
        (else (tref-walk a (cdr shape) (cdr idx) (+ (* off (car shape)) (car idx))))))

; (tref t i j ...) — компонента (0-based); индексов меньше ранга — подтензор
(define (tref t &rest idx)
  (let ((a (as-tensor t)))
    (tref-walk a (tensor-shape-list a) idx 0)))

; (transpose t perm) — перестановка осей: ось k результата = ось (nth perm k) исходного
(define (transpose t perm)
  (let* ((a (as-tensor t))
         (sh (tensor-shape-list a))
         (r (length sh)))
    (if (not (and (list? perm) (= (length perm) r) (every? (lambda (k) (member? k perm)) (range r))))
        (error "transpose: perm должна быть перестановкой осей 0..r-1, получено" perm)
        (let* ((old-str (strides sh))
               (new-sh (map (lambda (p) (nth sh p)) perm))
               (perm-str (map (lambda (p) (nth old-str p)) perm))
               (d (tensor-data a)))
          (tensor-raw new-sh
                      (list->vector
                       (map (lambda (idx) (vref d (apply + (map2 * idx perm-str))))
                            (all-indices new-sh))))))))

; --- Арифметика: методы ---

; сумма списка термов; численно, если всё — обычные числа, иначе через упроститель
(define (sum-terms terms)
  (if (any? alg? terms)
      (simplify (cons '+ terms))
      (apply + terms)))

(defmethod + (tensor tensor) (a b)
  (if (equal? (object-ref a 0) (object-ref b 0))
      (tensor-raw (tensor-shape-list a) (vector-map2 + (tensor-data a) (tensor-data b)))
      (error "+: формы тензоров не совпадают" (tensor-shape-list a) (tensor-shape-list b))))

(defmethod * (scalar tensor) (s a)
  (tensor-raw (tensor-shape-list a) (vector-map (lambda (c) (* s c)) (tensor-data a))))

; обобщённое скалярное произведение (Dot): свёртка последнего индекса a с первым индексом b.
; Результат ранга 0 — скаляр.
(define (dot-entry da db i j kk n)
  (sum-terms (map (lambda (k) (* (vref da (+ (* i kk) k)) (vref db (+ (* k n) j)))) (range kk))))

(define (tdot a b)
  (let* ((sa (tensor-shape-list a))
         (sb (tensor-shape-list b))
         (kk (last sa)))
    (if (not (= kk (car sb)))
        (error "dot: несогласованные размерности" sa sb)
        (let* ((m (product (butlast sa)))
               (n (product (cdr sb)))
               (da (tensor-data a))
               (db (tensor-data b))
               (flat (append-map (lambda (i) (map (lambda (j) (dot-entry da db i j kk n)) (range n)))
                                 (range m)))
               (res-shape (append (butlast sa) (cdr sb))))
          (if (null? res-shape)
              (car flat)
              (tensor-raw res-shape (list->vector flat)))))))

(defmethod * (tensor tensor) (a b) (tdot a b))

; квадратная матрица n >= 1 раз повторным умножением (быстрое возведение)
(define (tpow m n)
  (cond ((= n 1) m)
        ((= (mod n 2) 0) (let ((h (tpow m (/ n 2)))) (tdot h h)))
        (else (tdot m (tpow m (- n 1))))))

(define (square-matrix m who)
  (let* ((a (as-tensor m))
         (sh (tensor-shape-list a)))
    (if (and (= (length sh) 2) (= (car sh) (cadr sh)))
        a
        (error who ": ожидается квадратная матрица, форма" sh))))

(defmethod ^ (tensor integer) (a n)
  (let ((m (square-matrix a "^")))
    (cond ((= n 0) (identity-matrix (car (tensor-shape-list m))))
          ((> n 0) (tpow m n))
          (else (tpow (inv m) (- n))))))

(defmethod simplify (tensor) (a)
  (tensor-raw (tensor-shape-list a) (vector-map simplify (tensor-data a))))

(defmethod diff (tensor) (a x)
  (tensor-raw (tensor-shape-list a) (vector-map (lambda (c) (diff x c)) (tensor-data a))))

(defmethod integrate (tensor) (a x)
  (tensor-raw (tensor-shape-list a) (vector-map (lambda (c) (integrate c x)) (tensor-data a))))

; --- Печать: [[1, 2], [3, 4]] ---

(define (join-strings strs sep)
  (cond ((null? strs) "")                    ; Шаг 21a: пустой вектор [] печатается как []
        ((null? (cdr strs)) (car strs))
        (else (string-append (car strs) sep (join-strings (cdr strs) sep)))))

(define (tensor-string-at shape v off conv)
  (if (null? (cdr shape))
      (string-append "[" (join-strings (map (lambda (k) (conv (vref v (+ off k)))) (range (car shape))) ", ") "]")
      (let ((block (product (cdr shape))))
        (string-append "["
                       (join-strings (map (lambda (i) (tensor-string-at (cdr shape) v (+ off (* i block)) conv))
                                          (range (car shape)))
                                     ", ")
                       "]"))))

(defmethod print (tensor) (a)
  (tensor-string-at (tensor-shape-list a) (tensor-data a) 0 to-string))

(defmethod math-print (tensor) (a)
  (tensor-string-at (tensor-shape-list a) (tensor-data a) 0 math-print))

; --- Функции векторной алгебры ---

(define (vec+ a b) (+ (as-tensor a) (as-tensor b)))
(define (vec- a b) (- (as-tensor a) (as-tensor b)))

; (scale s v) — скаляр на каждую компоненту (в том числе при s = 0 — нулевой тензор)
(define (scale s v)
  (let ((a (as-tensor v)))
    (tensor-raw (tensor-shape-list a) (vector-map (lambda (c) (* s c)) (tensor-data a)))))

(define (dot a b) (tdot (as-tensor a) (as-tensor b)))

; евклидова норма: sqrt (v·v); точная при точном квадрате, иначе символьная (sqrt d)
(define (norm v)
  (let* ((d (dot v v))
         (r (sqrt d)))
    (if (alg? r) (list 'sqrt d) r)))

; векторное произведение 3-векторов
(define (cross a b)
  (let ((u (as-tensor a))
        (w (as-tensor b)))
    (if (and (equal? (tensor-shape-list u) '(3)) (equal? (tensor-shape-list w) '(3)))
        (let ((u0 (vref (tensor-data u) 0)) (u1 (vref (tensor-data u) 1)) (u2 (vref (tensor-data u) 2))
              (w0 (vref (tensor-data w) 0)) (w1 (vref (tensor-data w) 1)) (w2 (vref (tensor-data w) 2)))
          (tensor-from-flat '(3)
                            (list (- (* u1 w2) (* u2 w1))
                                  (- (* u2 w0) (* u0 w2))
                                  (- (* u0 w1) (* u1 w0)))))
        (error "cross: ожидаются два 3-вектора"))))

; --- Матрицы ---

(define (matrix-of m who)
  (let ((a (as-tensor m)))
    (if (= (length (tensor-shape-list a)) 2) a (error who ": ожидается матрица (тензор ранга 2)"))))

(define (mat m) (matrix-of m "mat"))
(define (mat-t m) (transpose (matrix-of m "mat-t") '(1 0)))
(define (mat-mul a b) (tdot (matrix-of a "mat-mul") (matrix-of b "mat-mul")))

; определитель: разложение Лапласа по первой строке строится одним выражением, затем simplify
(define (drop-nth l j) (append (take l j) (drop l (+ j 1))))
(define (zero-entry? x) (and (number? x) (= x 0)))

(define (det-expr rows)
  (let ((n (length rows)))
    (cond ((= n 1) (car (car rows)))
          ((= n 2) (list '- (list '* (car (car rows)) (cadr (cadr rows)))
                         (list '* (cadr (car rows)) (car (cadr rows)))))
          (else (cons '+ (det-terms (car rows) (cdr rows) 0))))))

(define (det-terms first-row rest j)
  (cond ((null? first-row) '())
        ((zero-entry? (car first-row)) (det-terms (cdr first-row) rest (+ j 1)))
        (else (cons (list '* (if (= (mod j 2) 0) 1 -1) (car first-row)
                          (det-expr (map (lambda (r) (drop-nth r j)) rest)))
                    (det-terms (cdr first-row) rest (+ j 1))))))

(define (det m)
  (let ((a (square-matrix m "det")))
    (simplify (det-expr (tensor->list a)))))

; обратная матрица: adj(A)/det(A); ошибка при det = 0 (для численной матрицы)
(define (cofactor rows i j)
  (simplify (list '* (if (= (mod (+ i j) 2) 0) 1 -1)
                  (det-expr-or-1 (map (lambda (r) (drop-nth r j)) (drop-nth rows i))))))
(define (det-expr-or-1 rows) (if (null? rows) 1 (det-expr rows)))

(define (inv m)
  (let* ((a (square-matrix m "inv"))
         (rows (tensor->list a))
         (n (length rows))
         (d (det a)))
    (cond ((zero-entry? d) (error "inv: матрица вырождена (det = 0)"))
          ((= n 1) (tensor-from-flat '(1 1) (list (/ 1 (car (car rows))))))
          (else (tensor-from-flat (list n n)
                                  (append-map (lambda (i) (map (lambda (j) (/ (cofactor rows j i) d)) (range n)))
                                              (range n)))))))

; ранг: исключение Гаусса на точных числах (на работе с копией данных)
(define (find-pivot w nr nc r c i)
  (cond ((not (< i nr)) -1)
        ((zero-entry? (vref w (+ (* i nc) c))) (find-pivot w nr nc r c (+ i 1)))
        (else i)))

(define (swap-rows w nc p r)
  (swap-cols w nc p r 0))
(define (swap-cols w nc p r j)
  (if (< j nc)
      (let ((tmp (vref w (+ (* p nc) j))))
        (vset! w (+ (* p nc) j) (vref w (+ (* r nc) j)))
        (vset! w (+ (* r nc) j) tmp)
        (swap-cols w nc p r (+ j 1)))))

(define (eliminate-cols w nc r c i f j)
  (if (< j nc)
      (begin
        (vset! w (+ (* i nc) j) (- (vref w (+ (* i nc) j)) (* f (vref w (+ (* r nc) j)))))
        (eliminate-cols w nc r c i f (+ j 1)))))

(define (eliminate-rows w nr nc r c i)
  (if (< i nr)
      (let ((f (/ (vref w (+ (* i nc) c)) (vref w (+ (* r nc) c)))))
        (eliminate-cols w nc r c i f c)
        (eliminate-rows w nr nc r c (+ i 1)))))

(define (rank-loop w nr nc r c)
  (if (or (not (< r nr)) (not (< c nc)))
      r
      (let ((p (find-pivot w nr nc r c r)))
        (if (< p 0)
            (rank-loop w nr nc r (+ c 1))
            (begin
              (if (not (= p r)) (swap-rows w nc p r))
              (eliminate-rows w nr nc r c (+ r 1))
              (rank-loop w nr nc (+ r 1) (+ c 1)))))))

(define (rank m)
  (let* ((a (matrix-of m "rank"))
         (sh (tensor-shape-list a)))
    (rank-loop (list->vector (vector->list (tensor-data a))) (car sh) (cadr sh) 0 0)))

; --- Тензорные операции ---

; внешнее произведение; скаляры допускаются (скаляр × тензор = scale).
; Скаляр отличаем от тензора через (tensor-like? x): тензор или список-УРОВЕНЬ; список-выражение вроде (+ a b) — скаляр
(define (tensor-like? x) (or (tensor? x) (level? x)))
(define (outer a b)
  (cond ((and (not (tensor-like? a)) (not (tensor-like? b))) (* a b))
        ((not (tensor-like? a)) (scale a b))
        ((not (tensor-like? b)) (scale b a))
        (else
         (let* ((ta (as-tensor a))
                (tb (as-tensor b))
                (bl (vector->list (tensor-data tb))))
           (tensor-raw (append (tensor-shape-list ta) (tensor-shape-list tb))
                       (list->vector
                        (append-map (lambda (x) (map (lambda (y) (* x y)) bl))
                                    (vector->list (tensor-data ta)))))))))

; (contract t i j) — свёртка по паре осей; результат ранга 0 — скаляр
(define (contract-do a sh i j)
  (let* ((str (strides sh))
         (d (nth sh i))
         (step (+ (nth str i) (nth str j)))
         (rem-axes (filter (lambda (ax) (and (not (= ax i)) (not (= ax j)))) (range (length sh))))
         (rem-shape (map (lambda (ax) (nth sh ax)) rem-axes))
         (rem-str (map (lambda (ax) (nth str ax)) rem-axes))
         (data (tensor-data a))
         (sums (map (lambda (idx)
                      (let ((base (apply + (map2 * idx rem-str))))
                        (sum-terms (map (lambda (k) (vref data (+ base (* k step)))) (range d)))))
                    (all-indices rem-shape))))
    (if (null? rem-shape)
        (car sums)
        (tensor-raw rem-shape (list->vector sums)))))

(define (contract t i j)
  (let* ((a (as-tensor t))
         (sh (tensor-shape-list a))
         (r (length sh)))
    (cond ((= i j) (error "contract: индексы i и j должны различаться"))
          ((or (< i 0) (not (< i r)) (< j 0) (not (< j r)))
           (error "contract: индекс вне диапазона, ранг" r))
          ((not (= (nth sh i) (nth sh j)))
           (error "contract: размерности осей не равны" (nth sh i) (nth sh j)))
          (else (contract-do a sh i j)))))
