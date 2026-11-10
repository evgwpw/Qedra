; lp.lisp — шаг LP.1: линейное программирование.
; Точный двухфазный симплекс над рациональными числами, правило Бленда (нет зацикливания).
; Вход: (lp-maximize c A b) — max cᵀx при A·x ≤ b, x ≥ 0; (lp-minimize …) — через −c.
; Общая форма: (lp-solve 'max c rows), строки — (коэффициенты отношение правая-часть), отношение <= >= =.
; Ответы (всегда с сертификатом, проверяемым lp-check независимо — только умножения и сравнения):
;   (optimal x value y)  — Ax ∘ b, x ≥ 0, двойственная допустимость y, cᵀx = value = bᵀy;
;   (infeasible y)       — знаки y по строкам, yᵀA ≤ 0, yᵀb < 0 (лемма Фаркаша);
;   (unbounded x d)      — x допустима, d ≥ 0, Ad ∘ 0 (по отношениям строк), cᵀd > 0.

(module lp
  (export lp-maximize lp-minimize lp-solve lp-solve-free lp-check lp-check-min lp-pretty ilp-solve ilp-check
          math-lp-solve math-ilp-solve math-lp-check math-ilp-check))

; ---------- малые помощники ----------

; все элементы списка — числа (символьные параметры запрещены)
(define (lp-all-nums? xs) (every? (lambda (x) (number? x)) xs))

; скалярное произведение двух списков чисел
(define (lp-dot u v)
  (foldl (lambda (acc p) (+ acc (* (car p) (cadr p)))) 0 (map2 list u v)))

; список из n копий v
(define (lp-make-list n v)
  (if (<= n 0) '() (cons v (lp-make-list (- n 1) v))))

; замена элемента списка по индексу (0-based)
(define (lp-setnth lst i v)
  (cond ((null? lst) '())
        ((= i 0) (cons v (cdr lst)))
        (else (cons (car lst) (lp-setnth (cdr lst) (- i 1) v)))))

; хвост списка с индекса i
(define (lp-tail lst i)
  (if (<= i 0) lst (lp-tail (cdr lst) (- i 1))))

; первые i элементов списка
(define (lp-take lst i)
  (if (or (<= i 0) (null? lst)) '() (cons (car lst) (lp-take (cdr lst) (- i 1)))))

; столбец j матрицы (списка строк-коэффициентов)
(define (lp-col rows j) (map (lambda (r) (nth r j)) rows))

; строка с slack-переменной в позиции j slack-блока (длины ns): (исходные коэф … ±1 …)
(define (lp-embed a ns j v)
  (append a (lp-setnth (lp-make-list ns 0) j v)))

; ---------- симплекс с правилом Бленда ----------
; Таблица tbl: список строк ((коэф…) rhs), все rhs ≥ 0; basis — номера базисных столбцов
; (длина = число строк). Базисные столбцы в таблице — единичные.

; приведённые цены z_j − c_j всех столбцов: z_j = c_Bᵀ·(столбец j таблицы).
; Входящий для max: z_j − c_j < 0 (улучшение); оптимум — все ≥ 0.
(define (lp-reduced-costs tbl obj basis)
  (let* ((cB (map (lambda (j) (nth obj j)) basis))
         (n (length (car (car tbl)))))
    (map (lambda (j)
           (- (lp-dot cB (lp-col (map car tbl) j))
              (if (< j (length obj)) (nth obj j) 0)))
         (range n))))

; входящий столбец (правило Бленда): наименьший индекс с z_j − c_j < 0; #f — оптимум
(define (lp-entering tbl obj basis limit)
  (let* ((costs (lp-reduced-costs tbl obj basis))
         (cand (filter (lambda (j) (and (< j limit) (< (nth costs j) 0)))
                       (range (length costs)))))
    (if (null? cand) #f (car cand))))

; выводящая строка (правило Бленда): минимальное отношение rhs/a при a > 0;
; при равных отношениях — наименьший номер базисной переменной; #f — неограниченность
(define (lp-leaving tbl enter basis)
  (let* ((cand (filter (lambda (p) p)
                        (map (lambda (i)
                               (let* ((row (nth tbl i))
                                      (a (nth (car row) enter))
                                      (rhs (cadr row)))
                                 (if (> a 0) (list (/ rhs a) i) #f)))
                             (range (length tbl))))))
    (if (null? cand) #f
        (foldl (lambda (best p)
                 (if (or (< (car p) (car best))
                         (and (= (car p) (car best))
                              (< (nth basis (cadr p)) (nth basis (cadr best)))))
                     p best))
               (car cand) (cdr cand)))))

; шаг поворота: строку r делим на ведущий элемент, из остальных вычитаем кратные
(define (lp-pivot tbl enter r)
  (let* ((prow (nth tbl r))
         (pv (nth (car prow) enter))
         (prow2 (list (map (lambda (x) (/ x pv)) (car prow)) (/ (cadr prow) pv))))
    (map (lambda (i)
           (let* ((row (nth tbl i)) (f (nth (car row) enter)))
             (if (= i r) prow2
                 (list (map2 (lambda (x y) (- x (* f y))) (car row) (car prow2))
                       (- (cadr row) (* f (cadr prow2)))))))
         (range (length tbl)))))

; симплекс (max objᵀx): (optimal value x tbl basis) | (unbounded d) | (cycled).
; x длины n: базисная переменная строки i = rhs, остальные 0
(define (lp-extract-x tbl n basis)
  (foldl (lambda (x p) (lp-setnth x (car p) (cadr (nth tbl (cadr p)))))
         (lp-make-list n 0)
         (map2 list basis (range (length tbl)))))

; луч неограниченности: d[enter] = 1, d[basis_i] = −a_{i,enter}, остальные 0
(define (lp-ray tbl n basis enter)
  (let ((d (foldl (lambda (acc p)
                    (lp-setnth acc (car p) (- 0 (nth (car (nth tbl (cadr p))) enter))))
                  (lp-make-list n 0)
                  (map2 list basis (range (length tbl))))))
    (lp-setnth d enter 1)))
(define (lp-simplex tbl obj basis limit)
  (lp-simplex-iter tbl obj basis limit 0))

(define (lp-simplex-iter tbl obj basis limit k)
  (let ((enter (lp-entering tbl obj basis limit)))
    (cond ((not enter)
           (let ((x (lp-extract-x tbl (length obj) basis)))
             (list 'optimal (lp-dot obj x) x tbl basis)))
          ((> k 500) (list 'cycled))
          (else
           (let ((leave (lp-leaving tbl enter basis)))
             (if (not leave)
                 (list 'unbounded (lp-ray tbl (length obj) basis enter))
                 (let* ((r (cadr leave))
                        (ntbl (lp-pivot tbl enter r))
                        (nbasis (lp-setnth basis r enter)))
                   ; Шаг LP.3: каждая итерация — рамка (detail): входящая/выходящая переменная,
                   ; отношение rhs/a, «до» — таблица до поворота, значение — рекурсия (итог фазы)
                   (with-step ('lp-pivot
                               (string-append "симплекс-итерация " (to-string (+ k 1))
                                              ": входит переменная " (to-string enter)
                                              ", выходит переменная " (to-string (nth basis r))
                                              " (строка " (to-string r)
                                              "), отношение rhs/a = " (to-string (car leave)))
                               tbl
                               :level 'detail)
                      (lp-simplex-iter ntbl obj nbasis limit (+ k 1))))))))))

; ---------- фаза 1: искусственные переменные ----------
; К таблице (A x = b, b ≥ 0, n столбцов, m строк) добавляем m искусственных столбцов
; (единичная матрица), базис — искусственные; max −Σ art.
(define (lp-phase1 tbl)
  (let* ((m (length tbl))
         (n (length (car (car tbl))))
         (tbl1 (map (lambda (i)
                      (let ((row (nth tbl i)))
                        (list (append (car row) (lp-setnth (lp-make-list m 0) i 1))
                              (cadr row))))
                    (range m)))
         (basis (map (lambda (i) (+ n i)) (range m)))
         (obj (append (lp-make-list n 0) (lp-make-list m -1))))
    (lp-simplex tbl1 obj basis (+ n m))))

; двойственные цены строк по финальной таблице: v_i = c_Bᵀ·B⁻¹·e_i = c_Bᵀ·(искусственный столбец i)
(define (lp-row-prices tbl basis obj n m)
  (let ((cB (map (lambda (j) (nth obj j)) basis)))
    (map (lambda (i) (lp-dot cB (lp-col (map car tbl) (+ n i)))) (range m))))
; вывод искусственных переменных из базиса после фазы 1 (LP.2): строка i с базисным
; искусственным столбцом (>= n) поворачивается на первый структурный столбец k < n
; с ненулевым элементом (значение art = 0, rhs сохраняется); строка без структурных
; элементов — избыточное ограничение, удаляется вместе с позицией базиса.
(define (lp-clean-basis tbl basis n)
  (lp-clean-row tbl basis n 0))

(define (lp-clean-row tbl basis n i)
  (cond ((>= i (length tbl)) (list tbl basis))
        ((< (nth basis i) n) (lp-clean-row tbl basis n (+ i 1)))
        (else
         (let* ((coefs (car (nth tbl i)))
                (ks (filter (lambda (k) (and (< k n) (not (= (nth coefs k) 0)))) (range n))))
           (if (null? ks)
               (lp-clean-row (lp-without tbl i) (lp-without basis i) n i)
               (lp-clean-row (lp-pivot tbl (car ks) i) (lp-setnth basis i (car ks)) n (+ i 1)))))))

; список без элемента с индексом i
(define (lp-without lst i)
  (append (lp-take lst i) (lp-tail lst (+ i 1))))


; ---------- канонизация общей формы ----------

; строки (коэф rel rhs) → строки равенств со slack/surplus:
;   <= : a x + s = rhs;  >= : a x − s = rhs;  = : a x = rhs (s ≥ 0);
; rhs < 0 → строка умножается на −1 (≤ и ≥ меняются местами).
; Возвращает (таблица n0 число-неравенств): таблица строк ((коэф+slack) rhs).
(define (lp-canon rows)
  (let* ((n0 (length (car (car rows))))
         (neq (length (filter (lambda (r) (not (equal? (cadr r) '=))) rows)))
         (rows1 (map (lambda (r)
                       (let* ((a (car r)) (rel (cadr r)) (rhs (caddr r)))
                         (if (< rhs 0)
                             (list (map (lambda (x) (- 0 x)) a)
                                   (cond ((equal? rel '<=) '>=)
                                         ((equal? rel '>=) '<=)
                                         (else '=))
                                   (- 0 rhs))
                             r)))
                     rows))
         (pair (foldl (lambda (acc r)
                        (let* ((tbl (car acc)) (j (cadr acc))
                               (a (car r)) (rel (cadr r)) (rhs (caddr r)))
                          (if (equal? rel '=)
                              (list (append tbl
                                            (list (list (append a (lp-make-list neq 0)) rhs)))
                                    j)
                              (list (append tbl
                                            (list (list (lp-embed a neq j
                                                                    (if (equal? rel '<=) 1 -1))
                                                  rhs)))
                                    (+ j 1)))))
                      '(() 0) rows1)))
    (list (car pair) n0 neq)))

; ---------- главный вход ----------

; (lp-solve 'max|'min c rows): строки (коэф rel rhs), rel ∈ {<= >= =}; все переменные x ≥ 0.
; Ответ (optimal x value y) / (infeasible y) / (unbounded x d); y и луч относятся к исходным строкам:
;   optimal:  yᵢ ≥ 0 (≤-строки) / ≤ 0 (≥-строки) / свободно (=); yᵀA ≥ c (для max), yᵀb = value;
;   infeasible: те же знаки y, yᵀA ≤ 0, yᵀb < 0;
;   unbounded: d ≥ 0, (Ad)ᵢ по rel строк, cᵀd > 0 (для max; для min — cᵀd < 0).
; Ответ проверяется собственным сертификатом (lp-check / lp-check-min) до возврата: ошибка решателя
; (как баг искусственного базиса, найденный в LP.2) даёт ошибку, а не недопустимый «оптимум».
(define (lp-solve dir c rows)
  (let ((r (lp-solve-raw dir c rows)))
    (if (if (equal? dir 'max) (lp-check r c rows) (lp-check-min r c rows))
        r
        (error "lp-solve: внутренняя ошибка — ответ не прошёл проверку сертификата" r))))

(define (lp-solve-raw dir c rows)
  (if (not (and (list? c) (lp-all-nums? c) (list? rows)
                (every? (lambda (r) (and (list? r) (= (length r) 3)
                                         (list? (car r)) (= (length (car r)) (length c))
                                         (lp-all-nums? (car r)) (number? (caddr r))
                                         (member? (cadr r) (list '<= '>= '=))))
                        rows)))
      (error "lp-solve: нужны рациональные числа (символьные параметры запрещены); строки (коэф отношение rhs), отношение <= >= ="))
  (let* ((sgn (if (equal? dir 'max) 1 -1))
         (cc (map (lambda (x) (* sgn x)) c))
         (canon (with-step ('lp-canon "каноническая форма: неравенства → равенства со slack/surplus" rows)
                  (lp-canon rows)))
         (tbl (car canon))
         (n0 (cadr canon))
         (neq (caddr canon))
         (m (length tbl))
         (n (+ n0 neq))
         (p1 (with-step ('lp-phase1 "фаза 1: искусственные переменные (max −Σ art)" tbl)
                (lp-phase1 tbl)))
         (val1 (cadr p1)))
    (if (< val1 0)
        ; фаза 1 не обнулила искусственные: несовместность, сертификат Фаркаша — цены строк фазы 1
        (let* ((v (lp-row-prices (nth p1 3) (nth p1 4)
                                 (append (lp-make-list n 0) (lp-make-list m -1)) n m))
               (y (lp-orig-signs v rows)))
          (with-step ('lp-farkas "несовместность: сертификат леммы Фаркаша (цены строк)" y)
            (list 'infeasible y)))
        ; фаза 2: искусственные столбцы сохраняем (для двойственных цен), entering — только структурные
        (let* ((tbl1 (nth p1 3))
               (basis1 (nth p1 4))
               (clean (lp-clean-basis tbl1 basis1 n))
               (tbl1c (car clean))
               (basis1c (cadr clean))
               (obj2 (append cc (lp-make-list neq 0) (lp-make-list m 0)))
               ; фаза 2 — рамка: «до» — таблица после очистки базиса; итерации симплекса — вложенные
               (res (with-step ('lp-phase2 "фаза 2: симплекс на целевой функции" tbl1c)
                       (lp-simplex tbl1c obj2 basis1c n))))
          (cond ((equal? (car res) 'optimal)
                (let* ((xall (caddr res))
                        (x (lp-take xall n0))
                        (yv (lp-row-prices (nth res 3) (nth res 4) obj2 n m))
                        (y (lp-orig-signs yv rows)))
                   (with-step ('lp-optimal
                               (string-append "оптимум: value = " (to-string (* sgn (cadr res)))
                                              ", финальная симплекс-таблица")
                               (nth res 3)
                               :comment (string-append "двойственные цены: y = "
                                       (to-string (if (> sgn 0) y (map (lambda (v) (- 0 v)) y)))))
                     (list 'optimal x (* sgn (cadr res))
                           (if (> sgn 0) y (map (lambda (v) (- 0 v)) y))))))
                ((equal? (car res) 'unbounded)
                 (let* ((dall (cadr res))
                        (d (lp-take dall n0))
                        (xall (lp-extract-x tbl1c (+ n m) basis1c))
                        (x (lp-take xall n0)))
                   (with-step ('lp-unbounded "неограниченность: луч d (cᵀd > 0, Ad ∘ 0)" d)
                     (list 'unbounded x d))))
                (else (error "lp-solve: симплекс не сошёлся (правило Бленда нарушено?)")))))))

; знаки цен для исходных строк: v относится к каноническим строкам; строки, перевёрнутые
; в lp-canon (исходный rhs < 0), дают для исходной строки цену −v_i
(define (lp-orig-signs v rows)
  (map2 (lambda (vi row) (if (< (caddr row) 0) (- 0 vi) vi)) v rows))


; ---------- удобные входы ----------


; ---------- свободные переменные ----------

; (lp-solve-free dir c rows frees): frees — список #t/#f по переменным (длина = |c|);
; #t — переменная свободна (x = x⁺ − x⁻, оба ≥ 0). Ответ x/d — в исходных координатах.
(define (lp-solve-free dir c rows frees)
  (if (not (and (= (length frees) (length c))
                (every? (lambda (v) (or (equal? v #t) (equal? v #f))) frees)))
      (error "lp-solve-free: frees — список #t/#f по переменным"))
  (let* ((maxp (equal? dir 'max))
         ; замена столбцов: j-я переменная → x⁺_j, x⁻_j (коэф a → a, −a)
         (expand (lambda (xs)
                   (foldl (lambda (acc p)
                            (if (nth frees (car p))
                                (append acc (list (cadr p) (- 0 (cadr p))))
                                (append acc (list (cadr p)))))
                          '() (map2 list (range (length xs)) xs))))
         (c2 (expand c))
         (rows2 (map (lambda (r) (list (expand (car r)) (cadr r) (caddr r))) rows))
         (r (lp-solve dir c2 rows2))
         ; обратная сборка: x_j = x⁺_j − x⁻_j
         (collapse (lambda (xs)
                     (foldl (lambda (acc p)
                              (if (nth frees (car p))
                                  (append acc (list (- (nth xs (cadr p))
                                                       (nth xs (+ 1 (cadr p))))))
                                  (append acc (list (nth xs (cadr p))))))
                            '()
                            (map2 list (range (length frees)) (lp-free-indexes frees))))))
    (cond ((equal? (car r) 'optimal)
           (list 'optimal (collapse (cadr r)) (caddr r) (nth r 3)))
          ((equal? (car r) 'unbounded)
           (list 'unbounded (collapse (cadr r)) (collapse (caddr r))))
          (else r))))

; стартовые индексы расширенных переменных: j-я переменная начинается с индекса
; (сумма по i<j: 1 или 2 столбца)
(define (lp-free-indexes frees)
  (cadr (foldl (lambda (acc f)
                 (list (+ (car acc) (if f 2 1))
                       (append (cadr acc) (list (car acc)))))
               (list 0 '()) frees)))
; (lp-maximize c A b): max cᵀx при A·x ≤ b, x ≥ 0 (A — список строк или tensor из языка)
(define (lp-maximize c A b)
  (lp-solve 'max (lp-mlang-lst c)
            (lp-mlang-rows A b (lp-make-list (if (list? A) (length A) (length (tensor->list (tensor A)))) "<="))))

; (lp-minimize c A b): min cᵀx при A·x ≤ b, x ≥ 0 (сведение к max по −c)
(define (lp-minimize c A b)
  (lp-solve 'min (lp-mlang-lst c)
            (lp-mlang-rows A b (lp-make-list (if (list? A) (length A) (length (tensor->list (tensor A)))) "<="))))

; ---------- lp-check: независимая проверка сертификата ----------

; (lp-check ans c rows) — для ЗАДАЧИ MAX (символы rel берутся как есть).
; Только умножения и сравнения, без обращения к решателю.
; optimal:  Ax ∘ b, x ≥ 0, знаки y по строкам, yᵀA ≥ c, cᵀx = value = bᵀy;
; infeasible: знаки y, yᵀA ≤ 0, yᵀb < 0;
; unbounded: x допустима, d ≥ 0, (Ad)ᵢ по rel строк, cᵀd > 0.
(define (lp-check ans c rows) (lp-check-dir ans c rows 1))

; вариант для задачи MIN: yᵀA ≤ c, неограниченность — cᵀd < 0
(define (lp-check-min ans c rows) (lp-check-dir ans c rows -1))

; проверка optimal-ответа (4 элемента: optimal x value y)
(define (lp-check-opt ans c rows sgn)
  (let ((x (cadr ans)) (val (caddr ans)) (y (nth ans 3)))
    (and (= (length x) (length c)) (= (length y) (length rows))
         (lp-prim-feasible x rows)
         (lp-dual-signs-dir y rows sgn)
         (every? (lambda (j)
                   (if (> sgn 0)
                       (>= (lp-dot (lp-col (map car rows) j) y) (nth c j))
                       (<= (lp-dot (lp-col (map car rows) j) y) (nth c j))))
                 (range (length c)))
         (= (lp-dot c x) val)
         (= (lp-dot (map caddr rows) y) val))))

(define (lp-check-dir ans c rows sgn)
  (let ((kind (car ans)))
    (cond ((equal? kind 'optimal)
           (and (list? ans) (= (length ans) 4)
                (lp-check-opt ans c rows sgn)))
          ((equal? kind 'infeasible)
           (let ((y (cadr ans)))
             (and (= (length y) (length rows))
                  (lp-dual-signs y rows)
                  (every? (lambda (j) (>= (lp-dot (lp-col (map car rows) j) y) 0))   ; Фаркаш: yᵀA ≥ 0 при x ≥ 0 и yᵀb < 0 ⇒ yᵀAx ≥ 0 > yᵀb ≥ yᵀAx
                          (range (length c)))
                  (< (lp-dot (map caddr rows) y) 0))))
          ((equal? kind 'unbounded)
           (let ((x (cadr ans)) (d (caddr ans)))
             (and (= (length x) (length c)) (= (length d) (length c))
                  (lp-prim-feasible x rows)
                  (every? (lambda (v) (>= v 0)) d)
                  (every? (lambda (p)
                            (let ((r (lp-dot (car p) d)))
                              (cond ((equal? (cadr p) '<=) (<= r 0))
                                    ((equal? (cadr p) '>=) (>= r 0))
                                    (else (= r 0)))))
                          rows)
                  (if (> sgn 0) (> (lp-dot c d) 0) (< (lp-dot c d) 0)))))
          (else #f))))

; допустимость x: x ≥ 0 и все строки выполнены
(define (lp-prim-feasible x rows)
  (and (every? (lambda (v) (>= v 0)) x)
       (every? (lambda (p)
                 (let ((r (- (lp-dot (car p) x) (caddr p))))
                   (cond ((equal? (cadr p) '<=) (<= r 0))
                         ((equal? (cadr p) '>=) (>= r 0))
                         (else (= r 0)))))
               rows)))

; знаки двойственных цен (задача MAX): ≤-строки → yᵢ ≥ 0, ≥-строки → yᵢ ≤ 0, = — свободно;
; для MIN — зеркально (lp-check-min)
(define (lp-dual-signs y rows) (lp-dual-signs-dir y rows 1))

(define (lp-dual-signs-dir y rows sgn)
  (every? (lambda (p)
            (cond ((equal? (cadr p) '<=) (if (> sgn 0) (>= (car p) 0) (<= (car p) 0)))
                  ((equal? (cadr p) '>=) (if (> sgn 0) (<= (car p) 0) (>= (car p) 0)))
                  (else #t)))
          (map2 list y rows)))

; ---------- печать ----------

; (lp-pretty ans) — список-описание ответа
(define (lp-pretty ans)
  (cond ((equal? (car ans) 'optimal)
         (list 'optimum 'x (cadr ans) 'value (caddr ans) 'dual-y (nth ans 3)))
        ((equal? (car ans) 'infeasible)
         (list 'infeasible 'farkas-y (cadr ans)))
        ((equal? (car ans) 'unbounded)
         (list 'unbounded 'x (cadr ans) 'ray (caddr ans)))
        (else ans)))



; ---------- LP.2: целочисленное ЛП — ветви и границы ----------

; (ilp-solve dir c rows intset) — целочисленное ЛП поверх lp-solve.
; intset — список по переменным: 'int (целая), 'bin (бинарная 0/1), 'free (без требования целости).
; Ответы:
;   (optimal x value)  — x целая в целых компонентах, допустима, value = cᵀx; оптимальность —
;                        дерево ветвления (ilp-check пересчитывает его заново);
;   (infeasible)       — во всех узлах ветвления LP-релаксация несовместна;
;   (unbounded)        — LP-релаксация неограничена (целочисленного оптимума нет);
;   (unknown best-x best-value bound) — превышен лимит узлов: лучшая найденная целая точка
;                        и LP-граница (может быть #f, если целой точки не нашли).
; Бинарная переменная 'bin — это 'int + граница x_j ≤ 1 (строка добавляется автоматически).

; строка-ограничение x_j ∘ v для матрицы с n столбцами
(define (ilp-var-row n j v rel)
  (list (lp-setnth (lp-make-list n 0) j 1) rel v))

; дополнительные строки для бинарных переменных: x_j ≤ 1
(define (ilp-bin-rows c intset)
  (foldl (lambda (acc p)
           (if (equal? (cadr p) 'bin)
               (append acc (list (ilp-var-row (length c) (car p) 1 '<=)))
               acc))
         '() (map2 list (range (length c)) intset)))

; индексы переменных с требованием целости
(define (ilp-int-indexes intset)
  (filter (lambda (j) (or (equal? (nth intset j) 'int) (equal? (nth intset j) 'bin)))
          (range (length intset))))

; первая дробная целевая переменная в x; #f — все целые
(define (ilp-frac-var x intset)
  (let ((cand (filter (lambda (j) (not (integer? (nth x j)))) (ilp-int-indexes intset))))
    (if (null? cand) #f (car cand))))

; ветви и границы (depth-first, ветвление по первой дробной, отсечение по границе).
; rows — уже с бинарными ограничениями; nodes — лимит узлов.
; Каждый вызов возвращает (статус best-x best-v счёт): статус optimal — лучший найденный
; в поддереве (best-x/best-v — лучшая целая точка; #f, если её нет), infeasible — поддерево пусто,
; unbounded — корневая релаксация неограничена, unknown — исчерпан лимит узлов.
(define (ilp-bnb dir c rows intset nodes)
  (ilp-bnb-go dir c rows intset nodes 0 #f #f))

; лучшая из двух точек по направлению (v = #f — точка не найдена)
(define (ilp-better dir x1 v1 x2 v2)
  (cond ((not v1) (list x2 v2))
        ((not v2) (list x1 v1))
        ((if (equal? dir 'max) (> v1 v2) (< v1 v2)) (list x1 v1))
        (else (list x2 v2))))

; объединение результатов двух ветвей: лучший + статус (unknown побеждает optimal,
; infeasible — только если обе ветви пусты; счётчики складываются минус 1)
(define (ilp-join dir left right)
  (let* ((ls (car left)) (rs (car right))
         (cnt (- (+ (nth left 3) (nth right 3)) 1))
         (best (ilp-better dir (nth left 1) (nth left 2) (nth right 1) (nth right 2)))
         (status (cond ((or (equal? ls 'unknown) (equal? rs 'unknown)) 'unknown)
                       ((equal? ls 'unbounded) 'unbounded)
                       ((equal? rs 'unbounded) 'unbounded)
                       ((and (equal? ls 'infeasible) (equal? rs 'infeasible)) 'infeasible)
                       (else 'optimal))))
    (list status (car best) (cadr best) cnt)))

(define (ilp-bnb-go dir c rows intset nodes count best-x best-v)
  (let* ((r (lp-solve dir c rows))
         (maxp (equal? dir 'max))
         (improve (lambda (v) (if best-v
                                  (if maxp (> v best-v) (< v best-v))
                                  #t))))
    (cond ((equal? (car r) 'infeasible) (list 'infeasible best-x best-v (+ count 1)))
          ((equal? (car r) 'unbounded) (list 'unbounded best-x best-v (+ count 1)))
          ((> (+ count 1) nodes) (list 'unknown best-x best-v (+ count 1)))
          (else
           (let* ((x (cadr r)) (val (caddr r)) (frac (ilp-frac-var x intset)))
             (if (not frac)
                 ; целая точка — кандидат: объединяем с текущим лучшим
                 (let ((best (ilp-better dir x val best-x best-v)))
                   (list 'optimal (car best) (cadr best) (+ count 1)))
                 (if (not (improve val))
                     ; LP-граница не лучше найденного лучшего — отсечение
                     (list 'optimal best-x best-v (+ count 1))
                      ; ветвление: x_frac ≤ floor(v) и x_frac ≥ floor(v)+1
                      (let* ((fv (nth x frac))
                             (lo (floor fv))
                             (rlo (ilp-var-row (length c) frac lo '<=))
                             (rhi (ilp-var-row (length c) frac (+ lo 1) '>=))
                             ; Шаг LP.3: каждый узел ветвления — рамка (detail): добавленная строка
                             (left (with-step ('ilp-branch
                                               (string-append "ветвь: x" (to-string frac) " ≤ "
                                                              (to-string lo))
                                               rlo
                                               :level 'detail)
                                      (ilp-bnb-go dir c (append rows (list rlo))
                                                  intset nodes (+ count 1) best-x best-v)))
                             (lx (if (nth left 2) (nth left 1) best-x))
                             (lv (if (nth left 2) (nth left 2) best-v)))
                        (ilp-join dir left
                                  (with-step ('ilp-branch
                                              (string-append "ветвь: x" (to-string frac) " ≥ "
                                                             (to-string (+ lo 1)))
                                              rhi
                                              :level 'detail)
                                    (ilp-bnb-go dir c (append rows (list rhi))
                                                intset nodes (nth left 3) lx lv)))))))))))
; сборка окончательного ответа
(define (ilp-solve dir c rows intset)
  (if (not (and (list? c) (lp-all-nums? c) (list? rows) (list? intset)
                (= (length intset) (length c))
                (every? (lambda (v) (or (equal? v 'int) (equal? v 'bin) (equal? v 'free)))
                        intset)))
      (error "ilp-solve: intset — список 'int/'bin/'free по переменным; c и rows — как в lp-solve"))
  (let* ((rows2 (append rows (ilp-bin-rows c intset)))
         ; Шаг LP.3: всё дерево ветвления — рамка (main); узлы — вложенные (detail)
         (r (with-step ('ilp-bnb "ветви и границы: целочисленное ЛП" intset)
               (ilp-bnb dir c rows2 intset 2000))))
    (cond ((equal? (car r) 'optimal)
           (if (cadr r) (list 'optimal (cadr r) (caddr r)) (list 'infeasible)))
          ((equal? (car r) 'infeasible) (list 'infeasible))
          ((equal? (car r) 'unbounded) (list 'unbounded))
          (else (list 'unknown (cadr r) (caddr r) #f)))))

; ---------- ilp-check: проверка ответа ----------

; (ilp-check ans dir c rows intset):
;   optimal: x допустима (с бинарными строками), целые компоненты целые, value = cᵀx;
;            оптимальность — повторный счёт дерева ветвления (тот же принцип, лимит узлов велик);
;   infeasible: повторный счёт даёт infeasible;
;   unknown: #t (лучшая точка и граница не обязаны быть окончательными).
(define (ilp-check ans dir c rows intset)
  (let ((kind (car ans)))
    (cond ((equal? kind 'optimal)
           (let ((x (cadr ans)) (val (caddr ans)))
             (and (= (length x) (length c))
                  (lp-prim-feasible x (append rows (ilp-bin-rows c intset)))
                  (every? (lambda (j) (integer? (nth x j))) (ilp-int-indexes intset))
                  (= (lp-dot c x) val)
                  (let ((r (ilp-bnb dir c (append rows (ilp-bin-rows c intset)) intset 100000)))
                    (and (equal? (car r) 'optimal)
                         (= (caddr r) val)
                         (equal? (cadr r) x))))))
          ((equal? kind 'infeasible)
           (equal? (car (ilp-bnb dir c (append rows (ilp-bin-rows c intset)) intset 100000))
                   'infeasible))
          ((equal? kind 'unknown) #t)
          (else #f))))


; ---------- обёртки для математического языка (шаг LP.3) ----------

; строка "<="/">="/"=" или символ → символ отношения
(define (lp-mlang-rel r)
  (cond ((equal? r "<=") '<=)
        ((equal? r ">=") '>=)
        ((equal? r "=") '=)
        ((member? r (list '<= '>= '=)) r)
        (else (error "lp: отношение — строка \"<=\" / \">=\" / \"=\"" ))))

; "max"/"min" или символ → символ
(define (lp-mlang-dir d)
  (cond ((equal? d "max") 'max)
        ((equal? d "min") 'min)
        ((member? d (list 'max 'min)) d)
        (else (error "lp: направление — \"max\" или \"min\"" ))))

; "int"/"bin"/"free" или символ → символ
(define (lp-mlang-class v)
  (cond ((equal? v "int") 'int)
        ((equal? v "bin") 'bin)
        ((equal? v "free") 'free)
        ((member? v (list 'int 'bin 'free)) v)
        (else (error "lp: класс переменной — \"int\" / \"bin\" / \"free\"" ))))

; (math-lp-solve dir c A b rels): dir — "max"/"min"; A — матрица (список строк), b — вектор,
; rels — вектор отношений "<=" / ">=" / "=" по строкам. Ответ — как у lp-solve.
; список или tensor → список (значения из математического языка)
(define (lp-mlang-lst x)
  (if (list? x) x (tensor->list (tensor x))))

; значения из математического языка: список или tensor → список списков чисел
; rels из одного элемента распространяются на все строки (по умолчанию "<=")
(define (lp-mlang-rows A b rels)
  (let* ((A2 (lp-mlang-lst A)) (b2 (lp-mlang-lst b)) (r2 (lp-mlang-lst rels))
         (r3 (if (and (= (length r2) 1) (> (length A2) 1))
                 (lp-make-list (length A2) (car r2))
                 r2)))
    (if (not (and (= (length A2) (length b2)) (= (length A2) (length r3))))
        (error "lp_solve: A, b и relations должны иметь одинаковое число строк"))
    (map (lambda (i)
           (let ((a (nth A2 i)))
             (list (if (list? a) a (tensor->list (tensor a)))
                   (lp-mlang-rel (nth r3 i))
                   (nth b2 i))))
         (range (length A2)))))

(define (math-lp-solve dir c A b rels)
  (lp-solve (lp-mlang-dir dir) (lp-mlang-lst c) (lp-mlang-rows A b rels)))

; проверка сертификата для языка/MCP: ans — ответ решателя, данные — в формате math-lp-solve
(define (math-lp-check ans dir c A b rels)
  (let ((rows (lp-mlang-rows A b rels)) (c2 (lp-mlang-lst c)) (d (lp-mlang-dir dir)))
    (if (equal? d 'max) (lp-check ans c2 rows) (lp-check-min ans c2 rows))))

; (math-ilp-solve dir c A b rels intset): intset — вектор "int"/"bin"/"free" по переменным.
; Ответ — как у ilp-solve.
(define (math-ilp-solve dir c A b rels intset)
  (let ((c2 (lp-mlang-lst c)) (is2 (lp-mlang-lst intset)))
    (ilp-solve (lp-mlang-dir dir) c2 (lp-mlang-rows A b rels)
               (map (lambda (j) (lp-mlang-class (nth is2 j))) (range (length c2))))))

; проверка сертификата ILP для языка/MCP
(define (math-ilp-check ans dir c A b rels intset)
  (let ((c2 (lp-mlang-lst c)) (is2 (lp-mlang-lst intset)))
    (ilp-check ans (lp-mlang-dir dir) c2 (lp-mlang-rows A b rels)
               (map (lambda (j) (lp-mlang-class (nth is2 j))) (range (length c2))))))
