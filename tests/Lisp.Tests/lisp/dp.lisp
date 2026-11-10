; dp.lisp — тесты шага DP.1: рюкзак, LCS, Левенштейн, размен, способы, Беллман–Форд, memoize.
; Обязательное требование: каждая …-check отвергает испорченный ответ (таблица/значение/решение/потенциал).

; ---------- помощники ----------

(define (dp-set-cell tbl i j v)
  (map2 (lambda (row ri)
          (if (= ri i)
              (map2 (lambda (x cj) (if (= cj j) v x)) row (range (length row)))
              row))
        tbl (range (length tbl))))

; плоская таблица (размен)
(define (dp-set-1d tbl i v)
  (map2 (lambda (x j) (if (= j i) v x)) tbl (range (length tbl))))

(define (dp-mask-sum l mask acc)
  (if (null? l) acc
      (dp-mask-sum (cdr l) (quotient mask 2)
                   (if (= (remainder mask 2) 1) (+ acc (car l)) acc))))

(define (dp-brute-mask w v W mask limit best)
  (if (= mask limit) best
      (let ((ws (dp-mask-sum w mask 0)) (vs (dp-mask-sum v mask 0)))
        (dp-brute-mask w v W (+ mask 1) limit (if (<= ws W) (max best vs) best)))))

(define (dp-brute-knapsack w v W)
  (dp-brute-mask w v W 0 (^ 2 (length w)) 0))

; ---------- рюкзак ----------

(deftest "dp: рюкзак на 6 предметах совпадает с полным перебором 2^6"
  (let* ((w '(2 3 4 5 9 7)) (v '(3 4 5 8 10 7)) (W 15)
         (ans (knapsack w v W)))
    (assert-equal (car ans) (dp-brute-knapsack w v W))
    (assert-true (knapsack-check w v W ans))))

(deftest "dp: knapsack-check отвергает испорченную таблицу, значение и решение"
  (let* ((w '(1 2 3)) (v '(6 10 12)) (W 5)
         (ans (knapsack w v W)))
    (assert-true (knapsack-check w v W ans))
    ; испорченная клетка таблицы
    (assert-equal (knapsack-check w v W (list (car ans) (cadr ans) (dp-set-cell (caddr ans) 3 5 999))) #f)
    ; испорченное значение
    (assert-equal (knapsack-check w v W (list 999 (cadr ans) (caddr ans))) #f)
    ; недопустимый номер предмета
    (assert-equal (knapsack-check w v W (list (car ans) (list 9) (caddr ans))) #f)))

; ---------- LCS ----------

(deftest "dp: LCS(ABCBDAB, BDCABA) длины 4"
  (let ((ans (lcs '(A B C B D A B) '(B D C A B A))))
    (assert-equal (car ans) 4)
    (assert-equal (length (cadr ans)) 4)
    (assert-true (lcs-check '(A B C B D A B) '(B D C A B A) ans))))

(deftest "dp: lcs-check отвергает испорченную таблицу и решение"
  (let* ((a '(A B C B D A B)) (b '(B D C A B A))
         (ans (lcs a b)))
    (assert-true (lcs-check a b ans))
    (assert-equal (lcs-check a b (list (car ans) (cadr ans) (dp-set-cell (caddr ans) 2 2 99))) #f)
    (assert-equal (lcs-check a b (list (car ans) (cons 'Z (cadr ans)) (caddr ans))) #f)))

; ---------- редакционное расстояние ----------

(deftest "dp: edit-distance(kitten, sitting) = 3"
  (let ((ans (edit-distance '(K I T T E N) '(S I T T I N G))))
    (assert-equal (car ans) 3)
    (assert-true (edit-distance-check '(K I T T E N) '(S I T T I N G) ans))))

(deftest "dp: edit-distance-check отвергает испорченное значение и операцию"
  (let* ((a '(K I T T E N)) (b '(S I T T I N G))
         (ans (edit-distance a b)))
    (assert-true (edit-distance-check a b ans))
    (assert-equal (edit-distance-check a b (list 99 (cadr ans) (caddr ans))) #f)
    ; испорченная операция (replace с неверным исходным символом)
    (assert-equal (edit-distance-check a b (list (car ans) (cons (list 'replace 'Z 'S) (cdr (cadr ans))) (caddr ans))) #f)))

; ---------- размен ----------

(deftest "dp: размен {1,5,10,25} на 63 — 6 монет"
  (let ((ans (coin-change '(1 5 10 25) 63)))
    (assert-equal (car ans) 6)
    (assert-equal (apply + (cadr ans)) 63)
    (assert-true (coin-change-check '(1 5 10 25) 63 ans))))

(deftest "dp: размен {2} на 3 — infeasible"
  (let ((ans (coin-change '(2) 3)))
    (assert-equal (car ans) 'infeasible)
    (assert-true (coin-change-check '(2) 3 ans))))

(deftest "dp: coin-change-check отвергает испорченную таблицу и решение"
  (let* ((coins '(1 5 10 25)) (amount 63)
         (ans (coin-change coins amount)))
    (assert-true (coin-change-check coins amount ans))
    (assert-equal (coin-change-check coins amount (list (car ans) (cadr ans) (dp-set-1d (caddr ans) 10 99))) #f)
    (assert-equal (coin-change-check coins amount (list (car ans) (cons 7 (cadr ans)) (caddr ans))) #f)))

(deftest "dp: coin-ways {1,2,5} на 5 — 4 способа"
  (let ((ans (coin-ways '(1 2 5) 5)))
    (assert-equal (car ans) 4)
    (assert-true (coin-ways-check '(1 2 5) 5 ans))))

(deftest "dp: coin-ways-check отвергает испорченную таблицу"
  (let* ((coins '(1 2 5)) (amount 5)
         (ans (coin-ways coins amount)))
    (assert-true (coin-ways-check coins amount ans))
    (assert-equal (coin-ways-check coins amount (list (car ans) '() (dp-set-cell (caddr ans) 3 5 99))) #f)))

; ---------- кратчайшие пути ----------

(deftest "dp: Беллман–Форд с отрицательным весом без отрицательного цикла"
  (let* ((vs '(a b c d))
         (es '((a b 4) (a c 5) (b c -3) (c d 2)))
         (ans (shortest-paths vs es 'a)))
    (assert-equal (dp::dp-assoc-val 'a (car ans)) 0)
    (assert-equal (dp::dp-assoc-val 'b (car ans)) 4)
    (assert-equal (dp::dp-assoc-val 'c (car ans)) 1)
    (assert-equal (dp::dp-assoc-val 'd (car ans)) 3)
    (assert-true (shortest-paths-check vs es 'a ans))))

(deftest "dp: shortest-paths-check отвергает испорченный потенциал и родителя"
  (let* ((vs '(a b c d))
         (es '((a b 4) (a c 5) (b c -3) (c d 2)))
         (ans (shortest-paths vs es 'a))
         (d (car ans)) (par (cadr ans)))
    (assert-true (shortest-paths-check vs es 'a ans))
    ; испорченный потенциал: b = 99
    (assert-equal (shortest-paths-check vs es 'a (list (dp::dp-alist-set 'b 99 d) par)) #f)
    ; испорченный родитель: d ← a (ребра a→d нет)
    (assert-equal (shortest-paths-check vs es 'a (list d (dp::dp-alist-set 'd 'a par))) #f)))

(deftest "dp: отрицательный цикл распознан и сертифицирован"
  (let* ((vs '(a b c))
         (es '((a b 1) (b c -2) (c b -2)))
         (ans (shortest-paths vs es 'a)))
    (assert-equal (car ans) 'negative-cycle)
    (assert-true (shortest-paths-check vs es 'a ans))
    ; испорченный цикл (заменить вершину) отвергается
    (assert-equal (shortest-paths-check vs es 'a (list 'negative-cycle (cons 'a (cdr (cadr ans))))) #f)))

; ---------- memoize ----------

(defmemo (dp-fib n) (if (< n 2) n (+ (dp-fib (- n 1)) (dp-fib (- n 2)))))

(deftest "dp: defmemo — fib 60 быстро (мемоизация)"
  (assert-equal (dp-fib 60) 1548008755920))

(deftest "dp: memoize кэширует (повторный вызов не пересчитывает)"
  (let ((calls 0))
    (let ((f (memoize (lambda (x) (set! calls (+ calls 1)) (* x x)))))
      (assert-equal (f 5) 25)
      (assert-equal (f 5) 25)
      (assert-equal calls 1))))
