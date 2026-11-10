; lp.lisp — тесты шага LP.1: двухфазный симплекс с правилом Бленда, сертификаты, lp-check.
; Каждый ответ проверяется независимо через lp-check / lp-check-min (только умножения и сравнения).

; ---------- LP.1: учебная 2×2 (оптимум + двойственные цены) ----------

(deftest "lp/LP.1: учебная 2×2 — max 3x+5y, x≤4, 2y≤12, 3x+2y≤18: x=(2,6), value 36"
  (let ((r (lp-maximize '(3 5) '((1 0) (0 2) (3 2)) '(4 12 18))))
    (assert-true (equal? (car r) 'optimal))
    (assert-equal (cadr r) '(2 6))
    (assert-equal (caddr r) 36)
    ; двойственные цены: 0, 3/2, 1
    (assert-equal (nth r 3) '(0 3/2 1))
    ; сертификат независимо
    (assert-true (lp-check r '(3 5)
                            '(((1 0) <= 4) ((0 2) <= 12) ((3 2) <= 18))))))

; ---------- LP.1: пример Била (вырожденность, зацикливание классического правила) ----------

(deftest "lp/LP.1: пример Била — правило Бленда не зацикливается, value −1/20"
  (let ((rows '(((1/4 -60 -1/25 9) <= 0)
                ((1/2 -90 -1/50 3) <= 0)
                ((0 0 1 0) <= 1)))
        (c '(-3/4 150 -1/50 6)))
    (let ((r (lp-solve 'min c rows)))
      (assert-true (equal? (car r) 'optimal))
      (assert-equal (caddr r) -1/20)
      (assert-true (lp-check-min r c rows)))))

; ---------- LP.1: несовместная ----------

(deftest "lp/LP.1: несовместная — x≥2 и x≤1, сертификат Фаркаша"
  (let ((rows '(((1) >= 2) ((1) <= 1)))
        (c '(1)))
    (let ((r (lp-solve 'max c rows)))
      (assert-true (equal? (car r) 'infeasible))
      ; сертификат: y ≥ 0 для ≤-строк, y ≤ 0 для ≥-строк, yᵀA ≥ 0, yᵀb < 0
      (assert-true (lp-check r c rows)))))

; ---------- LP.1: неограниченная ----------

(deftest "lp/LP.1: неограниченная — max x+y при x−y≤2, луч и допустимая точка"
  (let ((rows '(((1 -1) <= 2)))
        (c '(1 1)))
    (let ((r (lp-solve 'max c rows)))
      (assert-true (equal? (car r) 'unbounded))
      (assert-true (lp-check r c rows)))))

; ---------- LP.1: с = и >= ----------

(deftest "lp/LP.1: равенство и неравенство — max x+y, x+y=3, x≤2: (2,1), value 3"
  (let ((rows '(((1 1) = 3) ((1 0) <= 2)))
        (c '(1 1)))
    (let ((r (lp-solve 'max c rows)))
      (assert-true (equal? (car r) 'optimal))
      (assert-equal (cadr r) '(2 1))
      (assert-equal (caddr r) 3)
      (assert-true (lp-check r c rows)))))

(deftest "lp/LP.1: нижняя граница >= — max x при 1≤x≤3: x=3"
  (let ((rows '(((1) >= 1) ((1) <= 3)))
        (c '(1)))
    (let ((r (lp-solve 'max c rows)))
      (assert-true (equal? (car r) 'optimal))
      (assert-equal (cadr r) '(3))
      (assert-true (lp-check r c rows)))))

; ---------- LP.1: транспортная 2×3 ----------

; 2 склада (запасы 30, 20), 3 магазина (спрос 15, 25, 10), стоимости (2 3 1 | 4 1 2).
; Переменные x11..x23; строки: суммы по складам и магазинам — равенства.
(deftest "lp/LP.1: транспортная 2×3 — min, value 75, x=(15,5,10,0,20,0)"
  (let ((c '(2 3 1 4 1 2))
        (rows '(((1 1 1 0 0 0) = 30)
                ((0 0 0 1 1 1) = 20)
                ((1 0 0 1 0 0) = 15)
                ((0 1 0 0 1 0) = 25)
                ((0 0 1 0 0 1) = 10))))
    (let ((r (lp-solve 'min c rows)))
      (assert-true (equal? (car r) 'optimal))
      (assert-equal (cadr r) '(15 5 10 0 20 0))
      (assert-equal (caddr r) 75)
      (assert-true (lp-check-min r c rows)))))

; ---------- LP.1: свободные переменные ----------

(deftest "lp/LP.1: свободная переменная — max x+y, x+y≤4, x+y≥2, x1 свободна"
  (let ((rows '(((1 1) <= 4) ((-1 -1) <= -2)))
        (c '(1 1)))
    (let ((r (lp-solve-free 'max c rows '(#t #f))))
      (assert-true (equal? (car r) 'optimal))
      ; value = 4 (максимум суммы при 2 ≤ x+y ≤ 4)
      (assert-equal (caddr r) 4)
      ; x допустима в исходных координатах (свободная переменная может быть < 0 — здесь ≥ 0)
      (assert-true (equal? (+ (nth (cadr r) 0) (nth (cadr r) 1)) 4)))))

; ---------- LP.1: ошибки входа ----------

(deftest "lp/LP.1: символьные параметры — ошибка"
  (assert-error (lp-solve 'max '(x 1) '(((1 1) <= 4)))))

; ---------- LP.1: печать ----------

(deftest "lp/LP.1: lp-pretty — читаемое описание ответа"
  (let ((r (lp-maximize '(3 5) '((1 0) (0 2) (3 2)) '(4 12 18))))
    (assert-equal (lp-pretty r)
                  '(optimum x (2 6) value 36 dual-y (0 3/2 1)))))

(deftest "lp/LP.1: lp-check отвергает ложный сертификат несовместности"
  ; x ≥ 1 (как −x ≤ −1) совместна; y = 1 даёт yᵀA = −1 < 0 — не сертификат Фаркаша
  (assert-true (not (lp-check '(infeasible (1)) '(1) '(((-1) <= -1)))))
  ; ложный оптимум: x = 0 допустим, но цены y = 0 не дают Aᵀy ≥ c
  (assert-true (not (lp-check '(optimal (0) 0 (0)) '(1) '(((1) <= 3))))))

; ---------- LP.2: рюкзак 0/1 ----------

; полный перебор всех 0/1-наборов (2^n): лучший допустимый по ценности — (набор value)
(define (lp-knapsack-brute c w cap)
  (foldl (lambda (best nb)
           (let* ((wt (lp-kn-dot nb w))
                  (vl (lp-kn-dot nb c)))
             (if (and (<= wt cap) (> vl (cadr best))) (list nb vl) best)))
         '(() -1) (lp-kn-all (length c))))

; скалярное произведение (локальная копия, lp-dot приватен в модуле)
(define (lp-kn-dot u v)
  (foldl (lambda (acc p) (+ acc (* (car p) (cadr p)))) 0 (map2 list u v)))

; все 0/1-наборы длины n
(define (lp-kn-all n)
  (if (<= n 0) '(())
      (let ((rest (lp-kn-all (- n 1))))
        (append (map (lambda (r) (cons 0 r)) rest)
                (map (lambda (r) (cons 1 r)) rest)))))

(deftest "lp/LP.2: рюкзак 0/1 на 5 предметах — сверка с полным перебором"
  (let* ((c '(5 8 13 16 24))
         (rows '(((2 3 5 7 9) <= 18)))
         (intset '(bin bin bin bin bin))
         (r (ilp-solve 'max c rows intset))
         (brute (lp-knapsack-brute c '(2 3 5 7 9) 18)))
    (assert-true (equal? (car r) 'optimal))
    (assert-equal (caddr r) (cadr brute))       ; value совпадает с перебором
    (assert-equal (caddr r) 45)
    (assert-true (ilp-check r 'max c rows intset))))

; ---------- LP.2: дробная LP-релаксация ----------

(deftest "lp/LP.2: LP-релаксация дробная, ILP — целый оптимум (max x, 2x ≤ 3)"
  (let* ((c '(1))
         (rows '(((2) <= 3)))
         (intset '(int))
         (r (ilp-solve 'max c rows intset)))
    ; релаксация даёт 3/2, целый оптимум 1
    (assert-true (equal? (car r) 'optimal))
    (assert-equal (cadr r) '(1))
    (assert-equal (caddr r) 1)
    (assert-true (ilp-check r 'max c rows intset))))

; ---------- LP.2: целочисленно несовместная при совместной LP ----------

(deftest "lp/LP.2: 2x = 3 — LP совместна (x = 3/2), целых решений нет"
  (let* ((c '(1))
         (rows '(((2) = 3)))
         (intset '(int))
         (r (ilp-solve 'max c rows intset)))
    (assert-true (equal? (car r) 'infeasible))
    (assert-true (ilp-check r 'max c rows intset))))

; ---------- LP.2: ilp-check и lp-check отвергают ложные сертификаты ----------

(deftest "lp/LP.2: ilp-check отвергает ложные ответы"
  ; нецелая точка 3/2 — не целочисленное решение (2x ≤ 3, x int)
  (assert-true (not (ilp-check '(optimal (3/2) 3/2) 'max '(1) '(((2) <= 3)) '(int))))
  ; целая, но неоптимальная: x = 0 при оптимуме 1
  (assert-true (not (ilp-check '(optimal (0) 0) 'max '(1) '(((2) <= 3)) '(int))))
  ; целая, но недопустимая: 2x ≤ 3 при x = 2
  (assert-true (not (ilp-check '(optimal (2) 2) 'max '(1) '(((2) <= 3)) '(int))))
  ; value ≠ cᵀx
  (assert-true (not (ilp-check '(optimal (1) 5) 'max '(1) '(((2) <= 3)) '(int))))
  ; ложная несовместность: целые решения есть (x = 1)
  (assert-true (not (ilp-check '(infeasible) 'max '(1) '(((2) <= 3)) '(int)))))

(deftest "lp/LP.2: lp-check (LP.1) отвергает целочисленный сертификат как ложный LP-ответ"
  ; ilp-точка (1) допустима для LP, но y отсутствует — lp-check не примет
  (assert-true (not (lp-check '(optimal (1) 1) '(1) '(((2) <= 3))))))

; ---------- LP.2: смешанные переменные ----------

(deftest "lp/LP.2: int + free — целочисленность требуется только от помеченных"
  (let* ((c '(1 1))
         (rows '(((1 1) <= 5/2) ((1 0) >= 1)))
         (intset '(int free))
         (r (ilp-solve 'max c rows intset)))
    (assert-true (equal? (car r) 'optimal))
    ; x1 целое ≥ 1, x2 = 3/2 — свободная
    (assert-true (integer? (nth (cadr r) 0)))
    (assert-true (ilp-check r 'max c rows intset))))




; ---------- LP.3: шаги симплекса ----------

; все правила дерева шагов (узел: rule title comment before after level children time)
(define (lp-rules-of tree)
  (append-map (lambda (node) (cons (car node) (lp-rules-of (nth node 6)))) tree))

(deftest "lp/LP.3: шаги lp-solve — рамки canon, фаза 1, фаза 2, оптимум"
  (let* ((r (capture-step-log (lambda () (lp-solve 'max '(3 5) '(((1 0) <= 4) ((0 2) <= 12) ((3 2) <= 18)))) 'brief))
         (rules (map car (cadr r))))
    (assert-true (member? 'lp-canon rules))
    (assert-true (member? 'lp-phase1 rules))
    (assert-true (member? 'lp-phase2 rules))
    (assert-true (member? 'lp-optimal rules))))

(deftest "lp/LP.3: шаги full — итерации симплекса lp-pivot (входящая/выходящая, отношение)"
  (let* ((r (capture-step-log (lambda () (lp-solve 'max '(3 5) '(((1 0) <= 4) ((0 2) <= 12) ((3 2) <= 18)))) 'full))
         (rules (lp-rules-of (cadr r))))
    (assert-true (member? 'lp-pivot rules))))

(deftest "lp/LP.3: шаги несовместной — рамка Фаркаша"
  (let* ((r (capture-step-log (lambda () (lp-solve 'max '(1 1) '(((1 1) >= 3) ((1 1) <= 1)))) 'brief))
         (rules (map car (cadr r))))
    (assert-true (member? 'lp-farkas rules))))

(deftest "lp/LP.3: шаги неограниченной — рамка луча"
  (let* ((r (capture-step-log (lambda () (lp-solve 'max '(1 1) '(((1 -1) <= 1)))) 'brief))
         (rules (map car (cadr r))))
    (assert-true (member? 'lp-unbounded rules))))

(deftest "lp/LP.3: шаги ilp-solve — рамки ветвей и границ и ветвления"
  (let* ((r (capture-step-log (lambda () (ilp-solve 'max '(7 9 11) '(((4 4 4) <= 9)) '(int int int))) 'full))
         (rules-main (map car (cadr r)))
         (rules-all (lp-rules-of (cadr r))))
    (assert-true (member? 'ilp-bnb rules-main))
    (assert-true (member? 'ilp-branch rules-all))))

; ---------- LP.3: математический язык ----------

(deftest "lp/LP.3: math-lp-solve — строки-отношения, сертификат math-lp-check"
  (let ((r (math-lp-solve "max" '(3 5) '((1 0) (0 2) (3 2)) '(4 12 18) (list "<=" "<=" "<="))))
    (assert-true (equal? (car r) 'optimal))
    (assert-equal (cadr r) '(2 6))
    (assert-equal (caddr r) 36)
    (assert-true (math-lp-check r "max" '(3 5) '((1 0) (0 2) (3 2)) '(4 12 18) (list "<=" "<=" "<=")))))

(deftest "lp/LP.3: math-ilp-solve — классы переменных строками, проверка"
  (let ((r (math-ilp-solve "max" '(7 9 11) '((4 4 4)) '(9) (list "<=") (list "int" "int" "int"))))
    (assert-true (equal? (car r) 'optimal))
    (assert-true (every? integer? (cadr r)))
    (assert-true (math-ilp-check r "max" '(7 9 11) '((4 4 4)) '(9) (list "<=") (list "int" "int" "int")))))

(deftest "lp/LP.3: math-lp-solve — min и отношения >= ="
  (let ((r (math-lp-solve "min" '(1 1) '((1 1) (1 -1)) '(3 1) (list ">=" "="))))
    (assert-true (equal? (car r) 'optimal))
    (assert-true (math-lp-check r "min" '(1 1) '((1 1) (1 -1)) '(3 1) (list ">=" "=")))))
