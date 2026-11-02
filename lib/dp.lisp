; dp.lisp — динамическое программирование с сертификатами (шаг DP.1).
; Принцип оптимальности Беллмана: оптимальное значение подзадачи — через оптимальные значения меньших
; подзадач. Каждая задача возвращает (значение решение таблица) и проверяет себя своим …-check —
; только по таблице и входу, без повторного решения; не прошло — ошибка, не ответ.
; Таблицы — вложенные списки (точная арифметика); недостижимость (∞) — символ 'inf.
; Последовательности для LCS/Левенштейна — списки (строки в этом Lisp не индексируются).

(module dp
  (export memoize defmemo knapsack knapsack-check lcs lcs-check edit-distance edit-distance-check
          coin-change coin-change-check coin-ways coin-ways-check shortest-paths shortest-paths-check))

; ---------- общие помощники ----------

(define dp-inf 'inf)

(define (dp-inf? x) (equal? x 'inf))
(define (dp-zeros k) (map (lambda (i) 0) (range k)))
(define (dp-iota n) (map (lambda (i) (+ i 1)) (range n)))
(define (dp-ref tbl i j) (nth (nth tbl i) j))
(define (dp-last l) (last l))
(define (dp-sum l) (apply + l))
(define (dp-min2 a b) (cond ((dp-inf? a) b) ((dp-inf? b) a) ((<= a b) a) (else b)))
(define (dp-max2 a b) (cond ((dp-inf? a) b) ((dp-inf? b) a) ((>= a b) a) (else b)))

(define (dp-seq x)
  (if (list? x) x (error "dp: последовательность — список" x)))

(define (dp-subseq? s xs)
  (cond ((null? s) #t)
        ((null? xs) #f)
        ((equal? (car s) (car xs)) (dp-subseq? (cdr s) (cdr xs)))
        (else (dp-subseq? s (cdr xs)))))

(define (dp-distinct? l)
  (cond ((null? l) #t)
        ((member? (car l) (cdr l)) #f)
        (else (dp-distinct? (cdr l)))))

(define (dp-assoc-val k al)
  (let ((p (assoc k al)))
    (if p (cdr p) dp-inf)))

(define (dp-alist-set k v al)
  (if (null? al) (list (cons k v))
      (if (equal? (car (car al)) k)
          (cons (cons k v) (cdr al))
          (cons (car al) (dp-alist-set k v (cdr al))))))

; ---------- memoize ----------

; (memoize f) → функция с кэшем: ключ — сам список аргументов (структурный, make-hash —
; LANG.1; раньше ключ был символом из to-string и засорял таблицу символов).
; Повторный вызов с теми же аргументами возвращает сохранённый результат.
(define (memoize f)
  (let ((tbl (make-hash)))
    (lambda (&rest args)
      (let ((v (hash-ref tbl args #f)))
        (if v
            v
            (let ((r (apply f args)))
              (hash-set! tbl args r)
              r))))))

; (defmemo (имя арг…) тело) — макрос: определяет имя как мемоизированную функцию от арг…
; Пример: (defmemo (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(defmacro (defmemo spec &rest body)
  (let ((name (car spec)) (args (cdr spec)))
    `(define ,name (memoize (lambda ,args ,@body)))))

; ========== рюкзак 0/1 ==========

; (knapsack веса ценности W) → (значение выбранные-номера таблица): рюкзак 0/1.
; Веса — целые ≥ 0; dp[i][w] — максимум ценности на первых i предметах при вместимости w;
; выбранные номера — 0-based. Ответ проверяется knapsack-check до возврата.
(define (knapsack weights values W)
  (if (not (and (list? weights) (list? values) (= (length weights) (length values))
                (every? (lambda (w) (and (integer? w) (>= w 0))) weights)
                (every? number? values) (integer? W) (>= W 0)))
      (error "knapsack: веса — целые ≥ 0, W — целое ≥ 0, длины совпадают"))
  (let* ((n (length weights))
         (tbl (dp-knapsack-table weights values W n))
         (sel (dp-knapsack-solution weights values W tbl n))
         (ans (list (dp-ref tbl n W) sel tbl)))
    (if (knapsack-check weights values W ans) ans
        (error "knapsack: сертификат не прошёл" ans))))

(define (dp-knapsack-table weights values W n)
  (if (= n 0)
      (list (dp-zeros (+ W 1)))
      (let* ((prev (dp-knapsack-table weights values W (- n 1)))
             (lastrow (dp-last prev))
             (wi (nth weights (- n 1)))
             (vi (nth values (- n 1)))
             (row (map (lambda (w)
                         (if (< w wi) (nth lastrow w)
                             (dp-max2 (nth lastrow w) (+ (nth lastrow (- w wi)) vi))))
                       (range (+ W 1)))))
        (append prev (list row)))))

(define (dp-knapsack-solution weights values W tbl n)
  (if (= n 0) '()
      (let ((wi (nth weights (- n 1))))
        (if (and (>= W wi) (> (dp-ref tbl n W) (dp-ref tbl (- n 1) W)))
            (append (dp-knapsack-solution weights values (- W wi) tbl (- n 1)) (list (- n 1)))
            (dp-knapsack-solution weights values W tbl (- n 1))))))

; (knapsack-check веса ценности W ans) — независимая проверка ответа (значение решение таблица):
; уравнения Беллмана в каждой клетке + допустимость и стоимость решения; только по таблице и входу.
(define (knapsack-check weights values W ans)
  (and (list? ans) (= (length ans) 3)
       (let ((val (car ans)) (sel (cadr ans)) (tbl (caddr ans)) (n (length weights)))
         (and (= (length tbl) (+ n 1))
              (every? (lambda (row) (= (length row) (+ W 1))) tbl)
              (every? (lambda (v) (= v 0)) (car tbl))
              (dp-knapsack-bellman? weights values W tbl 1 n)
              (dp-distinct? sel)
              (every? (lambda (i) (and (integer? i) (>= i 0) (< i n))) sel)
              (<= (dp-sum (map (lambda (i) (nth weights i)) sel)) W)
              (= (dp-sum (map (lambda (i) (nth values i)) sel)) val)
              (= val (dp-ref tbl n W))))))

(define (dp-knapsack-bellman? weights values W tbl i n)
  (if (> i n) #t
      (let ((wi (nth weights (- i 1))) (vi (nth values (- i 1))))
        (and
         (every? (lambda (w)
                   (= (dp-ref tbl i w)
                      (if (< w wi) (dp-ref tbl (- i 1) w)
                          (dp-max2 (dp-ref tbl (- i 1) w)
                                   (+ (dp-ref tbl (- i 1) (- w wi)) vi)))))
                 (range (+ W 1)))
         (dp-knapsack-bellman? weights values W tbl (+ i 1) n)))))

; ========== наибольшая общая подпоследовательность ==========

; (lcs a b) → (длина подпоследовательность таблица): наибольшая общая подпоследовательность.
; a, b — списки (строки в языке не индексируются). Ответ проверяется lcs-check до возврата.
(define (lcs a b)
  (let ((a (dp-seq a)) (b (dp-seq b)))
    (let* ((m (length a)) (n (length b))
           (tbl (dp-lcs-table a b m n))
           (seq (dp-lcs-solution a b tbl m n))
           (ans (list (dp-ref tbl m n) seq tbl)))
      (if (lcs-check a b ans) ans
          (error "lcs: сертификат не прошёл" ans)))))

(define (dp-lcs-row a b prev m n j acc)
  (if (> j n) (reverse acc)
      (let ((v (if (= j 0) 0
                   (if (equal? (nth a (- m 1)) (nth b (- j 1)))
                       (+ (nth (nth prev (- m 1)) (- j 1)) 1)
                       (max (nth (nth prev (- m 1)) j) (car acc))))))
        (dp-lcs-row a b prev m n (+ j 1) (cons v acc)))))

(define (dp-lcs-table a b m n)
  (if (= m 0)
      (list (dp-zeros (+ n 1)))
      (let ((prev (dp-lcs-table a b (- m 1) n)))
        (append prev (list (dp-lcs-row a b prev m n 0 '()))))))

(define (dp-lcs-solution a b tbl m n)
  (if (or (= m 0) (= n 0)) '()
      (if (equal? (nth a (- m 1)) (nth b (- n 1)))
          (append (dp-lcs-solution a b tbl (- m 1) (- n 1)) (list (nth a (- m 1))))
          (if (>= (dp-ref tbl (- m 1) n) (dp-ref tbl m (- n 1)))
              (dp-lcs-solution a b tbl (- m 1) n)
              (dp-lcs-solution a b tbl m (- n 1))))))

; (lcs-check a b ans) — проверка: уравнения Беллмана по клеткам таблицы; решение — общая
; подпоследовательность a и b длины, равной корню таблицы.
(define (lcs-check a b ans)
  (and (list? ans) (= (length ans) 3)
       (let ((val (car ans)) (seq (cadr ans)) (tbl (caddr ans))
             (m (length a)) (n (length b)))
         (and (= (length tbl) (+ m 1))
              (every? (lambda (row) (= (length row) (+ n 1))) tbl)
              (every? (lambda (v) (= v 0)) (car tbl))
              (every? (lambda (row) (= (nth row 0) 0)) tbl)
              (dp-lcs-bellman? a b tbl 1 m n)
              (dp-subseq? seq a)
              (dp-subseq? seq b)
              (= (length seq) val)
              (= val (dp-ref tbl m n))))))

(define (dp-lcs-bellman? a b tbl i m n)
  (if (> i m) #t
      (and
       (every? (lambda (j)
                 (= (dp-ref tbl i j)
                    (if (equal? (nth a (- i 1)) (nth b (- j 1)))
                        (+ (dp-ref tbl (- i 1) (- j 1)) 1)
                        (max (dp-ref tbl (- i 1) j) (dp-ref tbl i (- j 1))))))
               (dp-iota n))
       (dp-lcs-bellman? a b tbl (+ i 1) m n))))

; ========== редакционное расстояние (Левенштейн) ==========

; (edit-distance a b) → (расстояние операции таблица): расстояние Левенштейна.
; Операции: (keep x), (delete x), (replace x y), (insert y); расстояние — число не-keep операций.
; a, b — списки. Ответ проверяется edit-distance-check до возврата.
(define (edit-distance a b)
  (let ((a (dp-seq a)) (b (dp-seq b)))
    (let* ((m (length a)) (n (length b))
           (tbl (dp-ed-table a b m n))
           (ops (dp-ed-ops a b tbl m n))
           (ans (list (dp-ref tbl m n) ops tbl)))
      (if (edit-distance-check a b ans) ans
          (error "edit-distance: сертификат не прошёл" ans)))))

(define (dp-ed-row a b prev m n j acc)
  (if (> j n) (reverse acc)
      (let ((v (cond ((= j 0) m)
                     ((equal? (nth a (- m 1)) (nth b (- j 1)))
                      (nth (nth prev (- m 1)) (- j 1)))
                     (else (+ 1 (min (nth (nth prev (- m 1)) (- j 1))
                                     (nth (nth prev (- m 1)) j)
                                     (car acc)))))))
        (dp-ed-row a b prev m n (+ j 1) (cons v acc)))))

(define (dp-ed-table a b m n)
  (if (= m 0)
      (list (range (+ n 1)))
      (let ((prev (dp-ed-table a b (- m 1) n)))
        (append prev (list (dp-ed-row a b prev m n 0 '()))))))

(define (dp-ed-ops a b tbl m n)
  (cond ((and (= m 0) (= n 0)) '())
        ((= m 0) (append (dp-ed-ops a b tbl m (- n 1)) (list (list 'insert (nth b (- n 1))))))
        ((= n 0) (append (dp-ed-ops a b tbl (- m 1) n) (list (list 'delete (nth a (- m 1))))))
        ((equal? (nth a (- m 1)) (nth b (- n 1)))
         (append (dp-ed-ops a b tbl (- m 1) (- n 1)) (list (list 'keep (nth a (- m 1))))))
        ((= (dp-ref tbl m n) (+ 1 (dp-ref tbl (- m 1) (- n 1))))
         (append (dp-ed-ops a b tbl (- m 1) (- n 1))
                 (list (list 'replace (nth a (- m 1)) (nth b (- n 1))))))
        ((= (dp-ref tbl m n) (+ 1 (dp-ref tbl (- m 1) n)))
         (append (dp-ed-ops a b tbl (- m 1) n) (list (list 'delete (nth a (- m 1))))))
        (else (append (dp-ed-ops a b tbl m (- n 1)) (list (list 'insert (nth b (- n 1))))))))

(define (dp-ed-sim a ops i out)
  (cond ((null? ops) (list i out))
        ((equal? (car (car ops)) 'insert)
         (dp-ed-sim a (cdr ops) i (append out (list (nth (car ops) 1)))))
        ((equal? (car (car ops)) 'delete)
         (if (or (>= i (length a)) (not (equal? (nth a i) (nth (car ops) 1))))
             (list 'bad out)
             (dp-ed-sim a (cdr ops) (+ i 1) out)))
        ((equal? (car (car ops)) 'keep)
         (if (or (>= i (length a)) (not (equal? (nth a i) (nth (car ops) 1))))
             (list 'bad out)
             (dp-ed-sim a (cdr ops) (+ i 1) (append out (list (nth a i))))))
        ((equal? (car (car ops)) 'replace)
         (if (or (>= i (length a)) (not (equal? (nth a i) (nth (car ops) 1))))
             (list 'bad out)
             (dp-ed-sim a (cdr ops) (+ i 1) (append out (list (nth (car ops) 2))))))
        (else (list 'bad out))))

; (edit-distance-check a b ans) — проверка: уравнения Беллмана по клеткам, число не-keep операций =
; расстоянию, симуляция операций переводит a в b.
(define (edit-distance-check a b ans)
  (and (list? ans) (= (length ans) 3)
       (let ((val (car ans)) (ops (cadr ans)) (tbl (caddr ans))
             (m (length a)) (n (length b)))
         (and (= (length tbl) (+ m 1))
              (every? (lambda (row) (= (length row) (+ n 1))) tbl)
              (equal? (car tbl) (range (+ n 1)))
              (every? (lambda (i) (= (nth (nth tbl i) 0) i)) (range (+ m 1)))
              (dp-ed-bellman? a b tbl 1 m n)
              (= (length (filter (lambda (op) (not (equal? (car op) 'keep))) ops)) val)
              (= val (dp-ref tbl m n))
              (let ((r (dp-ed-sim a ops 0 '())))
                (and (number? (car r))
                     (= (car r) m)
                     (equal? (cadr r) b)))))))

(define (dp-ed-bellman? a b tbl i m n)
  (if (> i m) #t
      (and
       (every? (lambda (j)
                 (= (dp-ref tbl i j)
                    (if (equal? (nth a (- i 1)) (nth b (- j 1)))
                        (dp-ref tbl (- i 1) (- j 1))
                        (+ 1 (min (dp-ref tbl (- i 1) (- j 1))
                                  (dp-ref tbl (- i 1) j)
                                  (dp-ref tbl i (- j 1)))))))
               (dp-iota n))
       (dp-ed-bellman? a b tbl (+ i 1) m n))))

; ========== размен монет ==========

(define (dp-coin-min coins a acc)
  (if (null? coins) dp-inf
      (let ((c (car coins)))
        (cond ((or (<= c 0) (> c a)) (dp-coin-min (cdr coins) a acc))
              (else (let ((d (nth acc (- c 1))))
                      (dp-min2 (if (dp-inf? d) dp-inf (+ 1 d))
                               (dp-coin-min (cdr coins) a acc))))))))

(define (dp-coin-table-loop coins amount a acc)
  (if (> a amount) (reverse acc)
      (let ((v (if (= a 0) 0 (dp-coin-min coins a acc))))
        (dp-coin-table-loop coins amount (+ a 1) (cons v acc)))))

(define (dp-coin-table coins amount) (dp-coin-table-loop coins amount 0 '()))

(define (dp-coin-pick coins tbl a)
  (cond ((null? coins) #f)
        ((and (<= (car coins) a)
              (= (nth tbl a) (+ 1 (nth tbl (- a (car coins))))))
         (car coins))
        (else (dp-coin-pick (cdr coins) tbl a))))

(define (dp-coin-solution coins tbl a)
  (if (= a 0) '()
      (let ((c (dp-coin-pick coins tbl a)))
        (if (not c) '()
            (append (dp-coin-solution coins tbl (- a c)) (list c))))))

; (coin-change монеты сумма) → (число-монет монеты таблица) или (infeasible таблица).
; Минимум монет для суммы; корень таблицы = inf, если размен невозможен.
; Ответ проверяется coin-change-check до возврата.
(define (coin-change coins amount)
  (if (not (and (list? coins) (every? (lambda (c) (and (integer? c) (> c 0))) coins)
                (integer? amount) (>= amount 0)))
      (error "coin-change: монеты — целые > 0, сумма — целое ≥ 0"))
  (let ((tbl (dp-coin-table coins amount)))
    (if (dp-inf? (nth tbl amount))
        (let ((ans (list 'infeasible tbl)))
          (if (coin-change-check coins amount ans) ans
              (error "coin-change: сертификат не прошёл" ans)))
        (let ((ans (list (nth tbl amount) (dp-coin-solution coins tbl amount) tbl)))
          (if (coin-change-check coins amount ans) ans
              (error "coin-change: сертификат не прошёл" ans))))))

(define (dp-coin-acc tbl a)
  (dp-coin-acc-loop tbl (- a 1) '()))
(define (dp-coin-acc-loop tbl k acc)
  (if (< k 0) acc
      (dp-coin-acc-loop tbl (- k 1) (append acc (list (nth tbl k))))))

(define (dp-coin-eq? x y)
  (if (or (dp-inf? x) (dp-inf? y))
      (and (dp-inf? x) (dp-inf? y))
      (= x y)))

(define (dp-coin-bellman? coins tbl a amount)
  (if (> a amount) #t
      (and (dp-coin-eq? (nth tbl a) (dp-coin-min coins a (dp-coin-acc tbl a)))
           (dp-coin-bellman? coins tbl (+ a 1) amount))))

; (coin-change-check монеты сумма ans) — проверка: уравнения Беллмана по таблице min-монет,
; допустимость решения (монеты из набора, сумма = amount, длина = значению) или infeasible при корне inf.
(define (coin-change-check coins amount ans)
  (and (list? ans)
       (let ((kind (car ans)))
         (cond ((equal? kind 'infeasible)
                (and (= (length ans) 2)
                     (let ((tbl (cadr ans)))
                       (and (= (length tbl) (+ amount 1))
                            (= (nth tbl 0) 0)
                            (dp-coin-bellman? coins tbl 1 amount)
                            (dp-inf? (nth tbl amount))))))
               (else
                (and (= (length ans) 3)
                     (let ((val (car ans)) (sol (cadr ans)) (tbl (caddr ans)))
                       (and (= (length tbl) (+ amount 1))
                            (= (nth tbl 0) 0)
                            (dp-coin-bellman? coins tbl 1 amount)
                            (not (dp-inf? (nth tbl amount)))
                            (= (dp-sum sol) amount)
                            (= (length sol) val)
                            (= val (nth tbl amount))
                            (every? (lambda (c) (member? c coins)) sol)))))))))

; ========== число способов размена ==========

(define (dp-ways-base amount)
  (map (lambda (j) (if (= j 0) 1 0)) (range (+ amount 1))))

(define (dp-ways-row prev c amount j acc)
  (if (> j amount) (reverse acc)
      (let ((v (+ (nth prev j)
                  (if (>= j c) (nth acc (- c 1)) 0))))
        (dp-ways-row prev c amount (+ j 1) (cons v acc)))))

(define (dp-ways-table-loop coins amount i n tbl)
  (if (> i n) tbl
      (let ((prev (dp-last tbl)))
        (dp-ways-table-loop coins amount (+ i 1) n
                            (append tbl (list (dp-ways-row prev (nth coins (- i 1)) amount 0 '())))))))

(define (dp-ways-table coins amount)
  (dp-ways-table-loop coins amount 1 (length coins) (list (dp-ways-base amount))))

; (coin-ways монеты сумма) → (число-способов () таблица): число способов размена.
; Таблица T[i][j] — способы первыми i монетами; ответ проверяется coin-ways-check до возврата.
(define (coin-ways coins amount)
  (if (not (and (list? coins) (every? (lambda (c) (and (integer? c) (> c 0))) coins)
                (integer? amount) (>= amount 0)))
      (error "coin-ways: монеты — целые > 0, сумма — целое ≥ 0"))
  (let* ((tbl (dp-ways-table coins amount))
         (n (length coins))
         (ans (list (dp-ref tbl n amount) '() tbl)))
    (if (coin-ways-check coins amount ans) ans
        (error "coin-ways: сертификат не прошёл" ans))))

; (coin-ways-check монеты сумма ans) — проверка: T[i][j] = T[i−1][j] + T[i][j−cᵢ] (при j ≥ cᵢ),
; базовая строка (1, 0, …, 0), корень = значению.
(define (coin-ways-check coins amount ans)
  (and (list? ans) (= (length ans) 3)
       (let ((val (car ans)) (tbl (caddr ans)) (n (length coins)))
         (and (= (length tbl) (+ n 1))
              (every? (lambda (row) (= (length row) (+ amount 1))) tbl)
              (equal? (car tbl) (dp-ways-base amount))
              (dp-ways-bellman? coins amount tbl 1 n)
              (= val (dp-ref tbl n amount))))))

(define (dp-ways-bellman? coins amount tbl i n)
  (if (> i n) #t
      (let ((c (nth coins (- i 1))))
        (and
         (every? (lambda (j)
                   (= (dp-ref tbl i j)
                      (+ (dp-ref tbl (- i 1) j)
                         (if (>= j c) (dp-ref tbl i (- j c)) 0))))
                 (range (+ amount 1)))
         (dp-ways-bellman? coins amount tbl (+ i 1) n)))))

; ========== кратчайшие пути (Беллман–Форд) ==========

; (shortest-paths вершины рёбра s) → (потенциалы дерево) или (negative-cycle цикл).
; Беллман–Форд: веса могут быть отрицательными; потенциалы — alist (вершина . d),
; дерево — alist (вершина . родитель); при отрицательном цикле — список вершин цикла.
; Ответ проверяется shortest-paths-check до возврата.
(define (shortest-paths vertices edges s)
  (if (not (and (list? vertices) (list? edges) (member? s vertices)
                (every? (lambda (e) (and (list? e) (= (length e) 3)
                                         (member? (car e) vertices)
                                         (member? (cadr e) vertices)
                                         (number? (caddr e))))
                        edges)))
      (error "shortest-paths: вершины, рёбра (u v w), источник из vertices"))
  (let* ((n (length vertices))
         (d0 (map (lambda (v) (cons v (if (equal? v s) 0 dp-inf))) vertices))
         (r (dp-bf-rounds edges d0 '() (- n 1)))
         (d (car r))
         (par (cadr r))
         (neg (dp-bf-find-relaxed edges d)))
    (if neg
        (let* ((x (dp-walk-parent par neg n))
               (cyc (cons x (reverse (dp-collect-loop par x (dp-assoc-val x par) '())))))
          (let ((ans (list 'negative-cycle cyc)))
            (if (shortest-paths-check vertices edges s ans) ans
                (error "shortest-paths: сертификат отрицательного цикла не прошёл" ans))))
        (let ((ans (list d par)))
          (if (shortest-paths-check vertices edges s ans) ans
              (error "shortest-paths: сертификат потенциалов не прошёл" ans))))))

(define (dp-bf-round edges d par changed)
  (if (null? edges) (list d par changed)
      (let* ((e (car edges)) (u (car e)) (v (cadr e)) (w (caddr e))
             (du (dp-assoc-val u d)))
        (let ((dv (dp-assoc-val v d)))
          (if (and (not (dp-inf? du)) (or (dp-inf? dv) (< (+ du w) dv)))
              (dp-bf-round (cdr edges) (dp-alist-set v (+ du w) d) (dp-alist-set v u par) #t)
              (dp-bf-round (cdr edges) d par changed))))))

(define (dp-bf-rounds edges d par k)
  (if (= k 0) (list d par)
      (let ((r (dp-bf-round edges d par #f)))
        (dp-bf-rounds edges (car r) (cadr r) (- k 1)))))

(define (dp-bf-find-relaxed edges d)
  (cond ((null? edges) #f)
        (else (let* ((e (car edges)) (du (dp-assoc-val (car e) d)))
                (let ((dv (dp-assoc-val (cadr e) d)))
                  (if (and (not (dp-inf? du)) (or (dp-inf? dv) (< (+ du (caddr e)) dv)))
                      (cadr e)
                      (dp-bf-find-relaxed (cdr edges) d)))))))

(define (dp-walk-parent par x k)
  (if (= k 0) x (dp-walk-parent par (dp-assoc-val x par) (- k 1))))

(define (dp-collect-loop par start cur acc)
  (if (equal? cur start) acc
      (dp-collect-loop par start (dp-assoc-val cur par) (cons cur acc))))

(define (dp-edge-w u v edges)
  (cond ((null? edges) #f)
        ((and (equal? (car (car edges)) u) (equal? (cadr (car edges)) v)) (caddr (car edges)))
        (else (dp-edge-w u v (cdr edges)))))

(define (dp-pairs l)
  (if (or (null? l) (null? (cdr l))) '()
      (cons (list (car l) (cadr l)) (dp-pairs (cdr l)))))

(define (dp-cycle-pairs cyc)
  (append (dp-pairs cyc) (list (list (last cyc) (car cyc)))))

; (shortest-paths-check вершины рёбра s ans) — проверка: d(s) = 0, d(v) ≤ d(u) + w(u,v) для всех
; рёбер, равенство вдоль дерева, родители ведут к s; для (negative-cycle цикл) — каждое ребро цикла
; есть в графе, сумма весов < 0.
(define (shortest-paths-check vertices edges s ans)
  (and (list? ans)
       (cond ((equal? (car ans) 'negative-cycle)
              (let ((cyc (cadr ans)))
                (and (list? cyc) (>= (length cyc) 2)
                     (every? (lambda (p) (not (not (dp-edge-w (car p) (cadr p) edges))))
                             (dp-cycle-pairs cyc))
                     (< (dp-sum (map (lambda (p) (dp-edge-w (car p) (cadr p) edges))
                                     (dp-cycle-pairs cyc)))
                        0))))
             (else
              (let ((d (car ans)) (par (cadr ans)))
                (and (= (length d) (length vertices))
                     (equal? (dp-assoc-val s d) 0)
                     (dp-bf-feasible? edges d)
                     (dp-bf-tree? vertices edges s d par)
                     (every? (lambda (v)
                               (let ((dv (dp-assoc-val v d)))
                                 (or (equal? v s) (dp-inf? dv)
                                     (dp-bf-rooted? v s par (length vertices)))))
                             vertices)))))))

(define (dp-bf-feasible? edges d)
  (every? (lambda (e)
            (let ((du (dp-assoc-val (car e) d))
                  (dv (dp-assoc-val (cadr e) d)))
              (or (dp-inf? du)
                  (and (not (dp-inf? dv)) (<= dv (+ du (caddr e)))))))
          edges))

(define (dp-bf-tree? vertices edges s d par)
  (every? (lambda (v)
            (let ((dv (dp-assoc-val v d)))
              (cond ((equal? v s) #t)
                    ((dp-inf? dv) #t)
                    (else
                     (let ((p (dp-assoc-val v par)))
                       (and (not (dp-inf? p))
                            (member? p vertices)
                            (let ((w (dp-edge-w p v edges)))
                              (and w (= dv (+ (dp-assoc-val p d) w))))))))))
          vertices))

(define (dp-bf-rooted? v s par k)
  (cond ((equal? v s) #t)
        ((= k 0) #f)
        (else (let ((p (dp-assoc-val v par)))
                (if (dp-inf? p) #f (dp-bf-rooted? p s par (- k 1)))))))