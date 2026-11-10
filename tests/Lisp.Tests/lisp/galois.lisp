; galois.lisp — тесты шага GAL.1: дискриминант, Дедекинд, таблица транзитивных групп

(define (gal-assert-not b) (assert-true (not b)))

(deftest "GAL: степень и дискриминант"
  (define x 'x)
  (assert-equal (galois-poly-degree (+ (^ x 5) (* -1 x) -1) x) 5)
  (assert-equal (galois-disc (+ (^ x 3) -2) x) -108)
  (assert-equal (galois-disc (+ (^ x 4) -2) x) -2048)
  ; x³ − 3x + 1: disc = 81 (квадрат → C₃ ⊆ A₃)
  (assert-equal (galois-disc (+ (^ x 3) (* -3 x) 1) x) 81))

(deftest "GAL: дискриминант — квадрат ⇔ G ⊆ A_n"
  (define x 'x)
  (assert-true (galois-disc-square? (+ (^ x 3) (* -3 x) 1) x))
  (assert-true (galois-disc-square? (+ (^ x 4) 1) x))
  (gal-assert-not (galois-disc-square? (+ (^ x 3) -2) x))
  (gal-assert-not (galois-disc-square? (+ (^ x 5) (* -1 x) -1) x)))

(deftest "GAL: неприводимость"
  (define x 'x)
  (assert-true (galois-irreducible? (+ (^ x 5) (* -1 x) -1) x))
  (assert-true (galois-irreducible? (+ (^ x 3) -2) x))
  (gal-assert-not (galois-irreducible? (+ (^ x 4) -4) x))
  (gal-assert-not (galois-irreducible? (+ (^ x 2) -1) x)))

(deftest "GAL: циклотипы по Дедекинду (x⁵ − x − 1, S₅)"
  (define x 'x)
  (define f (+ (^ x 5) (* -1 x) -1))
  (define ct (galois-cycle-types f x (primes-up-to 100)))
  (assert-true (galois-cycle-types-check f x (primes-up-to 100) ct))
  ; каждый наблюдённый тип — разбиение 5
  (assert-true (galois::gal-all? (lambda (e) (= (apply + (car e)) 5)) ct))
  ; частота 5-циклов > 0 (неприводимость: есть p с одним множителем степени 5)
  (assert-true (> (cdr (assoc '(5) ct)) 0))
  ; наблюдённые типы лежат в S5 и НЕ все в A5 (есть нечётные)
  (define S5 (galois::gal-row->group (gal-group-lookup 5 'S5) 5))
  (define A5 (galois::gal-row->group (gal-group-lookup 5 'A5) 5))
  (assert-true (galois::gal-all? (lambda (e) (gal-cycle-type-member? S5 (car e))) ct))
  (gal-assert-not (galois::gal-all? (lambda (e) (gal-cycle-type-member? A5 (car e))) ct)))

(deftest "GAL: циклотипы x³ − 2 (S₃)"
  (define x 'x)
  (define f (+ (^ x 3) -2))
  (define ct (galois-cycle-types f x (primes-up-to 60)))
  (assert-true (galois-cycle-types-check f x (primes-up-to 60) ct))
  (assert-true (assoc '(3) ct))
  (assert-true (assoc '(2 1) ct)))

(deftest "GAL: таблица транзитивных групп 1–5 сверена построением"
  (assert-true (gal-transitive-table-ok? 1))
  (assert-true (gal-transitive-table-ok? 2))
  (assert-true (gal-transitive-table-ok? 3))
  (assert-true (gal-transitive-table-ok? 4))
  (assert-true (gal-transitive-table-ok? 5)))

(deftest "GAL: таблица транзитивных групп 6 (16 групп) сверена построением"
  (assert-true (gal-transitive-table-ok? 6)))

(deftest "GAL: таблица транзитивных групп 7 (7 групп) сверена построением"
  (assert-true (gal-transitive-table-ok? 7)))

(deftest "GAL: конкретные группы таблицы — порядки"
  (define S5 (galois::gal-row->group (gal-group-lookup 5 'S5) 5))
  (define A5 (galois::gal-row->group (gal-group-lookup 5 'A5) 5))
  (define F20 (galois::gal-row->group (gal-group-lookup 5 'F20) 5))
  (define PSL7 (galois::gal-row->group (gal-group-lookup 7 'PSL32d7) 7))
  (assert-equal (group-order S5) 120)
  (assert-equal (group-order A5) 60)
  (assert-equal (group-order F20) 20)
  (assert-equal (group-order PSL7) 168)
  (assert-equal (length (gal-group-elements PSL7)) 168))

(deftest "GAL: циклотипы групп таблицы"
  (define S5 (galois::gal-row->group (gal-group-lookup 5 'S5) 5))
  (assert-true (gal-cycle-type-member? S5 '(5)))
  (assert-true (gal-cycle-type-member? S5 '(3 2)))
  (assert-true (gal-cycle-type-member? S5 '(4 1)))
  (gal-assert-not (gal-cycle-type-member? S5 '(2 2 1 1 1)))
  (define A5 (galois::gal-row->group (gal-group-lookup 5 'A5) 5))
  (gal-assert-not (gal-cycle-type-member? A5 '(4 1)))
  (assert-true (gal-cycle-type-member? A5 '(3 1 1))))

; ---------- GAL.2b: резольвенты, данные строк, группы многочленов ----------

; произведение многочленов (списки коэффициентов по возрастанию)
(define (gal-t-pmul a b)
  (define r (make-vector (+ (length a) (length b) -1) 0))
  (define i 0)
  (for-each (lambda (x)
              (define j 0)
              (for-each (lambda (y)
                          (vset! r (+ i j) (+ (vref r (+ i j)) (* x y)))
                          (set! j (+ j 1)))
                        b)
              (set! i (+ i 1)))
            a)
  (vector->list r))

; ∏(y − s) по списку значений s
(define (gal-t-from-roots ss)
  (foldl (lambda (acc s) (gal-t-pmul acc (list (- s) 1))) '(1) ss))

(define (gal-pow-int v k) (if (= k 0) 1 (* v (gal-pow-int v (- k 1)))))

; значения сумм по виду: P2 — пары, P3 — тройки, O2 — упорядоченные пары (веса 1, 2)
(define (gal-t-sums kind u)
  (define n (length u))
  (define idx (range n))
  (cond ((equal? kind 'P2)
         (map (lambda (s) (+ (nth u (car s)) (nth u (car (cdr s)))))
              (galois::gal-subsets 2 idx)))
        ((equal? kind 'P3)
         (map (lambda (s) (+ (nth u (car s)) (nth u (car (cdr s))) (nth u (car (cdr (cdr s))))))
              (galois::gal-subsets 3 idx)))
        (else
         (map (lambda (s) (+ (nth u (car s)) (* 2 (nth u (car (cdr s))))))
              (galois::gal-ordered-pairs n)))))

; резольвента движком по унитарным коэффициентам многочлена с целыми корнями r
(define (gal-t-engine kind r tr)
  (define cs (gal-t-from-roots r))
  (define N (galois::gal-resolvent-degree kind (length r)))
  (galois::gal-newton-coeffs
   (galois::gal-resolvent-sums kind (galois::gal-power-sums-u cs tr N) N) N))

; корни u = x + c·x^k
(define (gal-t-u r tr)
  (map (lambda (v) (if (= (car tr) 0) v (+ v (* (car tr) (gal-pow-int v (cdr tr)))))) r))

(deftest "GAL: резольвента по подмножествам (движок = произведение по корням)"
  (define r '(1 2 4 -3 7))
  (assert-equal (gal-t-engine 'P2 r '(0 . 1)) (gal-t-from-roots (gal-t-sums 'P2 r)))
  (assert-equal (gal-t-engine 'P3 r '(0 . 1)) (gal-t-from-roots (gal-t-sums 'P3 r)))
  (assert-equal (gal-t-engine 'O2 r '(0 . 1)) (gal-t-from-roots (gal-t-sums 'O2 r)))
  (assert-equal (gal-t-engine 'O2 r '(1 . 2)) (gal-t-from-roots (gal-t-sums 'O2 (gal-t-u r '(1 . 2)))))
  (assert-equal (gal-t-engine 'P3 r '(-1 . 3)) (gal-t-from-roots (gal-t-sums 'P3 (gal-t-u r '(-1 . 3))))))

(deftest "GAL: резольвента по подмножествам, степень 7 (суммы троек)"
  (define r '(1 2 4 -3 7 -5 6))
  (assert-equal (gal-t-engine 'P3 r '(1 . 2)) (gal-t-from-roots (gal-t-sums 'P3 (gal-t-u r '(1 . 2))))))

; θ = Σ_{g∈F20} ∏ r[σ(g(i))]^e_i, e = (2 1 0 0 1); значения по всем σ ∈ S5
(define (gal-t-theta-values r)
  (define F20 (gal-group-elements (galois::gal-row->group (gal-group-lookup 5 'F20) 5)))
  (define S5 (gal-group-elements (galois::gal-row->group (gal-group-lookup 5 'S5) 5)))
  (define (at g i) (if (< i (vlength g)) (vref g i) i))
  (define e '(2 1 0 0 1))
  (define (theta s)
    (apply + (map (lambda (g)
                    (apply * (map (lambda (i) (gal-pow-int (nth r (at s (at g i))) (nth e i)))
                                  (range 5))))
                  F20)))
  (define vals '())
  (for-each (lambda (s)
              (define v (theta s))
              (if (not (member? v vals)) (set! vals (cons v vals))))
            S5)
  vals)

(deftest "GAL: резольвента Кэли = ∏(y − θ) по 6 значениям F20-инварианта"
  (define r '(1 2 4 -3 -4))
  (define vals (gal-t-theta-values r))
  (assert-equal (length vals) 6)
  (define abcd (galois::gal-depress5 (gal-t-from-roots r)))
  (assert-equal (galois::gal-cayley-coeffs (nth abcd 0) (nth abcd 1) (nth abcd 2) (nth abcd 3))
                (gal-t-from-roots vals)))

(deftest "GAL: резольвента Кэли, недепрессивные корни (сдвиг на −c4/5)"
  (define r '(1 2 4 -3 9))
  (define s (/ (apply + r) 5))
  (define vals (gal-t-theta-values (map (lambda (v) (- v s)) r)))
  (define abcd (galois::gal-depress5 (gal-t-from-roots r)))
  (assert-equal (galois::gal-cayley-coeffs (nth abcd 0) (nth abcd 1) (nth abcd 2) (nth abcd 3))
                (gal-t-from-roots vals)))

(deftest "GAL: данные строк 5 — равны вычисленным по группам"
  (assert-true (galois::gal-row-data-ok? 5 '(C5 D5 F20 A5 S5))))

(deftest "GAL: данные строк 6 (первые 8 групп) — равны вычисленным"
  (assert-true (galois::gal-row-data-ok? 6 '(C6 S3d6 D6 A4d6 F18 2A4d6 S4d6 S4c6))))

(deftest "GAL: данные строк 6 (остальные) — равны вычисленным"
  (assert-true (galois::gal-row-data-ok? 6 '(F18x2 F36 2S4d6 PSL25d6 F36x2 PGL25d6 A6))))

(deftest "GAL: данные строк 7 (кроме A7, S7) — равны вычисленным"
  (assert-true (galois::gal-row-data-ok? 7 '(C7 D7 F21 F42 PSL32d7))))

(deftest "GAL: данные строк S6 и A7 — равны вычисленным"
  (assert-true (galois::gal-row-data-ok? 6 '(S6)))
  (assert-true (galois::gal-row-data-ok? 7 '(A7))))

(deftest "GAL: данные строки S7 равны вычисленным"
  (assert-true (galois::gal-row-data-ok? 7 '(S7))))

; результат galois-group — ожидаемая группа и проходит независимую проверку
(define (gal-t-expect f name order)
  (define x 'x)
  (define r (galois-group f x))
  (assert-equal (nth r 0) :group)
  (assert-equal (nth r 1) name)
  (assert-equal (nth r 2) order)
  (assert-true (galois-group-check f x r)))

(deftest "GAL: x² − 2 → C2" (define x 'x) (gal-t-expect (+ (^ x 2) -2) 'C2 2))
(deftest "GAL: x³ − 2 → S3" (define x 'x) (gal-t-expect (+ (^ x 3) -2) 'S3 6))
(deftest "GAL: x³ − 3x + 1 → C3" (define x 'x) (gal-t-expect (+ (^ x 3) (* -3 x) 1) 'C3 3))
(deftest "GAL: x⁴ − 2 → D4" (define x 'x) (gal-t-expect (+ (^ x 4) -2) 'D4 8))
(deftest "GAL: x⁴ + 1 → V4" (define x 'x) (gal-t-expect (+ (^ x 4) 1) 'V4 4))
(deftest "GAL: x⁴ + x + 1 → S4" (define x 'x) (gal-t-expect (+ (^ x 4) x 1) 'S4 24))
(deftest "GAL: x⁴ − 4x² + 2 → C4" (define x 'x) (gal-t-expect (+ (^ x 4) (* -4 (^ x 2)) 2) 'C4 4))
(deftest "GAL: x⁵ − x − 1 → S5" (define x 'x) (gal-t-expect (+ (^ x 5) (* -1 x) -1) 'S5 120))
(deftest "GAL: x⁵ − 2 → F20 (резольвента Кэли: рациональный корень)"
  (define x 'x)
  (gal-t-expect (+ (^ x 5) -2) 'F20 20))
(deftest "GAL: x⁵ − 5x + 12 → D5"
  (define x 'x)
  (gal-t-expect (+ (^ x 5) (* -5 x) 12) 'D5 10))
(deftest "GAL: x⁵ + 20x + 16 → A5"
  (define x 'x)
  (gal-t-expect (+ (^ x 5) (* 20 x) 16) 'A5 60))
(deftest "GAL: x⁶ − 2 → D6 (суммы на упорядоченных парах и тройках)"
  (define x 'x)
  (gal-t-expect (+ (^ x 6) -2) 'D6 12))
(deftest "GAL: x⁷ − 7x + 3 → PSL(3,2) (суммы на тройках: 7 + 28)"
  (define x 'x)
  (gal-t-expect (+ (^ x 7) (* -7 x) 3) 'PSL32d7 168))
(deftest "GAL: x⁷ − x − 1 → S7" (define x 'x) (gal-t-expect (+ (^ x 7) (* -1 x) -1) 'S7 5040))
(deftest "GAL: x⁷ − 2 → F42" (define x 'x) (gal-t-expect (+ (^ x 7) -2) 'F42 42))

(deftest "GAL: инварианты резольвент"
  (define x 'x)
  (assert-equal (galois::gal-compute-inv (+ (^ x 5) -2) x 'CAY) '(CAY (0 . 1) (1 5)))
  (assert-equal (galois::gal-compute-inv (+ (^ x 5) (* -1 x) -1) x 'CAY) '(CAY (0 . 1) (6)))
  (assert-equal (nth (galois::gal-compute-inv (+ (^ x 6) -2) x 'O2) 2) '(6 12 12))
  (assert-equal (nth (galois::gal-compute-inv (+ (^ x 7) (* -7 x) 3) x 'P3) 2) '(7 28))
  (assert-equal (nth (galois::gal-compute-inv (+ (^ x 7) (* -1 x) -1) x 'P3) 2) '(35)))

(deftest "GAL: подделки с чужим сертификатом / пустым сертификатом отклоняются"
  (define x 'x)
  (define f5 (+ (^ x 5) (* -1 x) -1))
  (define g5 (+ (^ x 5) -2))
  (define rf (galois-group f5 x))
  (define rg (galois-group g5 x))
  (assert-true (galois-group-check f5 x rf))
  (assert-true (galois-group-check g5 x rg))
  (gal-assert-not (galois-group-check f5 x rg))
  (gal-assert-not (galois-group-check g5 x rf))
  (define empty (list :group 'F20 20 :certificate
                      (list :types '() :primes '() :disc 0 :disc-square #f :irreducible #t
                            :lemmas '() :resolvents '())))
  (gal-assert-not (galois-group-check g5 x empty))
  (gal-assert-not (galois-group-check f5 x empty)))

(deftest "GAL: подделка F20 для x⁵ − x − 1 с резольвентой Кэли «с корнем»"
  (define x 'x)
  (define f5 (+ (^ x 5) (* -1 x) -1))
  (define fake (list :group 'F20 20 :certificate
                     (list :types '() :primes '() :disc 0 :disc-square #f :irreducible #t
                           :lemmas '() :resolvents (list (list 'CAY '(0 . 1) '(1 5))))))
  (gal-assert-not (galois-group-check f5 x fake)))

(deftest "GAL: подделка PSL(3,2) для x⁷ − x − 1 и S7 для x⁷ − 7x + 3"
  (define x 'x)
  (define f (+ (^ x 7) (* -1 x) -1))
  (define g (+ (^ x 7) (* -7 x) 3))
  (define rf (galois-group f x))
  (define rg (galois-group g x))
  (gal-assert-not (galois-group-check f x rg))
  (gal-assert-not (galois-group-check g x rf))
  (define fake (list :group 'PSL32d7 168 :certificate
                     (list :types '() :primes '() :disc 0 :disc-square #t :irreducible #t
                           :lemmas '() :resolvents (list (list 'P3 '(0 . 1) '(7 28))))))
  (gal-assert-not (galois-group-check f x fake)))

(deftest "GAL: приводимый и степень > 7 → unknown"
  (define x 'x)
  (assert-equal (galois-group (+ (^ x 4) -4) x) 'unknown)
  (assert-equal (galois-group (+ (^ x 8) x 1) x) 'unknown))

(deftest "GAL: неразличимые группы — честные candidates (x⁶ + 5x³ + 5)"
  (define x 'x)
  (define f (+ (^ x 6) (* 5 (^ x 3)) 5))
  (define r (galois-group f x))
  (assert-equal r '(:candidates (F18x2 F36x2)))
  (assert-true (galois-group-check f x r))
  (gal-assert-not (galois-group-check f x '(:candidates (F18x2))))
  (gal-assert-not (galois-group-check f x '(:group F18x2 36 :certificate ()))))

; ---------- GAL.3: разрешимость в радикалах ----------

(deftest "GAL.3: solvable-by-radicals? — неразрешимые группы → #f"
  (define x 'x)
  (assert-equal (solvable-by-radicals? (+ (^ x 5) (* -1 x) -1) x) #f)     ; S5
  (assert-equal (solvable-by-radicals? (+ (^ x 5) (* 20 x) 16) x) #f)     ; A5
  (assert-equal (solvable-by-radicals? (+ (^ x 7) (* -7 x) 3) x) #f))     ; PSL(3,2)

(deftest "GAL.3: solvable-by-radicals? — разрешимые → #t"
  (define x 'x)
  (assert-equal (solvable-by-radicals? (+ (^ x 5) -2) x) #t)              ; F20
  (assert-equal (solvable-by-radicals? (+ (^ x 5) (* -5 x) 12) x) #t)     ; D5
  (assert-equal (solvable-by-radicals? (+ (^ x 6) -2) x) #t)              ; D6
  (assert-equal (solvable-by-radicals? (+ (^ x 4) x 1) x) #t)             ; S4: степень ≤ 4
  (assert-equal (solvable-by-radicals? (+ (^ x 3) -2) x) #t)
  (assert-equal (solvable-by-radicals? (+ x 3) x) #t))

(deftest "GAL.3: solvable-by-radicals? — приводимые: любой неразрешимый множитель → #f"
  (define x 'x)
  (assert-equal (solvable-by-radicals? (* (+ (^ x 5) -2) (+ (^ x 2) 1)) x) #t)
  (assert-equal (solvable-by-radicals? (* (+ (^ x 5) (* -1 x) -1) (+ x -3)) x) #f)
  (assert-equal (solvable-by-radicals? (^ (+ (^ x 5) (* -1 x) -1) 2) x) #f))

(deftest "GAL.3: solvable-by-radicals? — не доказано → unknown"
  (define x 'x)
  (assert-equal (solvable-by-radicals? (+ (^ x 8) -2) x) 'unknown)         ; степень 8 неприводим: не определяем
  (assert-equal (solvable-by-radicals? (+ (^ x 5) (* 'a x) 1) x) 'unknown) ; параметр
  ; неприводимый дег-8 множитель не мешает доказанному #f другого множителя
  (assert-equal (solvable-by-radicals? (* (+ (^ x 8) -2) (+ (^ x 5) (* -1 x) -1)) x) #f))

(deftest "GAL.3: galois-solvability — вердикт, группа и степень"
  (define x 'x)
  (assert-equal (galois-solvability (+ (^ x 5) (* -1 x) -1) x) '(#f :group S5))
  (assert-equal (galois-solvability (+ (^ x 5) -2) x) '(#t :group F20))
  (assert-equal (galois-solvability (+ (^ x 3) -2) x) '(#t :degree 3))
  (assert-equal (galois-solvability (+ (^ x 4) -4) x) '(unknown)))         ; приводим

(deftest "GAL.3: galois-solvability — candidates одного рода: доказано, что разрешима"
  (define x 'x)
  ; группа среди F18x2/F36x2, обе разрешимы
  (assert-equal (galois-solvability (+ (^ x 6) (* 5 (^ x 3)) 5) x) '(#t :candidates (F18x2 F36x2))))

(deftest "GAL.3: solve — заметка «в радикалах не выражается» для S5, ответ прежний"
  (define x 'x)
  (define r (capture-conditions (lambda () (solve (+ (^ x 5) (* -1 x) -1) x))))
  (define cs (nth r 1))
  (assert-equal (length cs) 1)
  (assert-equal (car (car (car cs))) 'not-solvable-by-radicals)
  (assert-true (string-contains? (nth (car cs) 1) "в радикалах не выражается (группа Галуа S5, сертификат)"))
  ; ответ — как раньше: вещественный корень (алгебраическое число) и root-of
  (assert-true (string-contains? (to-string (car r)) "root-of")))

(deftest "GAL.3: solve — заметка «разрешимо в радикалах» для F20"
  (define x 'x)
  (define r (capture-conditions (lambda () (solve (+ (^ x 5) -2) x))))
  (define cs (nth r 1))
  (assert-equal (length cs) 1)
  (assert-equal (car (car (car cs))) 'solvable-by-radicals)
  (assert-true (string-contains? (nth (car cs) 1) "разрешимо в радикалах (группа Галуа F20, сертификат)")))

(deftest "GAL.3: solve — для степени ≤ 4 и приводимых заметок нет"
  (define x 'x)
  (assert-equal (nth (capture-conditions (lambda () (solve (+ (^ x 3) -2) x))) 1) '())
  (assert-equal (nth (capture-conditions (lambda () (solve (+ (^ x 4) x 1) x))) 1) '())
  ; приводимое: (x − 1)(x² + 1) — множителей степени ≥ 5 нет
  (assert-equal (nth (capture-conditions (lambda () (solve (* (+ x -1) (+ (^ x 2) 1)) x))) 1) '()))
