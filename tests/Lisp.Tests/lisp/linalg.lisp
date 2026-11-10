; linalg.lisp — тесты шага LA.1: RREF, ядро, образ, charpoly, собственные значения и векторы.
; Каждая проверка собственных векторов — подстановкой A·v = λ·v.

; ---------- помощники ----------

(define (la-dot row v) (simplify (cons '+ (map2 (lambda (a b) (list '* a b)) row v))))

; A·v = λ·v для всех строк (точная проверка; радикалы — linalg::l-zero? с численным запасом)
(define (la-ev-ok? m lam vs)
  (every? (lambda (v)
            (every? (lambda (pair)
                      (linalg::l-zero? (list '- (la-dot (car pair) v)
                                             (list '* lam (nth v (cadr pair))))))
                    (map2 list m (range (length m)))))
          vs))

; ядро: A·v = 0 и число векторов = n − rank
(define (la-null-ok? m vs)
  (let ((n (length (car m))))
    (and (= (length vs) (- n (linalg::l-rank m)))
         (every? (lambda (v) (every? (lambda (row) (linalg::l-zero? (la-dot row v))) m)) vs))))

; столбец — один из столбцов исходной матрицы
(define (la-col-of? c m)
  (any? (lambda (j) (equal? c (map (lambda (r) (nth r j)) m))) (range (length (car m)))))

; ---------- RREF ----------

(deftest "linalg/LA.1: rref приводит к приведённому ступенчатому виду"
  (assert-equal (tensor->list (rref '((1 2) (3 4)))) '((1 0) (0 1))))

(deftest "linalg/LA.1: rref вырожденной 3×3"
  (assert-equal (tensor->list (rref '((1 2 3) (2 4 6) (1 1 1))))
                '((1 0 -1) (0 1 2) (0 0 0))))

; ---------- ядро ----------

(deftest "linalg/LA.1: ядро 3×3 ранга 2 — один вектор"
  (let ((vs (nullspace '((1 2 3) (2 4 6) (1 1 1)))))
    (assert-true (la-null-ok? '((1 2 3) (2 4 6) (1 1 1)) vs))
    (assert-equal (length vs) 1)
    (assert-equal (car vs) '(1 -2 1))))

(deftest "linalg/LA.1: ядро 3×3 ранга 1 — два вектора"
  (let ((m '((1 2 3) (2 4 6) (3 6 9))))
    (let ((vs (nullspace m)))
      (assert-true (la-null-ok? m vs))
      (assert-equal (length vs) 2))))

(deftest "linalg/LA.1: ядро невырожденной матрицы пусто"
  (assert-equal (nullspace '((1 2) (3 4))) '())
  (assert-equal (nullspace '((2 0 0) (0 3 0) (0 0 4))) '()))

; ---------- образ ----------

(deftest "linalg/LA.1: columnspace 3×3 ранга 2 — столбцы исходной при ведущих"
  (let* ((m '((1 2 3) (2 4 6) (1 1 1)))
         (cs (columnspace m)))
    (assert-equal (length cs) (linalg::l-rank m))
    (assert-equal (length cs) 2)
    (assert-true (every? (lambda (c) (la-col-of? c m)) cs))
    (assert-equal cs '((1 2 1) (2 4 1)))))

; ---------- характеристический многочлен ----------

(deftest "linalg/LA.1: charpoly 2×2"
  (assert-equal (simplify (list '- (charpoly '((2 1) (1 2)) 'lam)
                                '(+ 3 (* -4 lam) (^ lam 2)))) 0))

(deftest "linalg/LA.1: charpoly 3×3"
  (assert-equal (simplify (list '- (charpoly '((1 2 0) (0 1 0) (0 0 3)) 'lam)
                                '(+ -3 (* 7 lam) (* -5 (^ lam 2)) (^ lam 3)))) 0))

; ---------- собственные значения ----------

(deftest "linalg/LA.1: собственные значения ((2 1) (1 2)) — 1 и 3"
  (assert-equal (list->set (eigenvalues '((2 1) (1 2)))) (list->set '((1 1) (3 1)))))

(deftest "linalg/LA.1: собственные значения ((1 2) (3 4)) — иррациональные √33"
  (let ((evs (eigenvalues '((1 2) (3 4)))))
    (assert-equal (length evs) 2)
    (assert-true (every? (lambda (ev)
                           (and (= (cadr ev) 1)
                                (linalg::l-zero? (list '- (list '^ (car ev) 2)
                                                       (list '+ (* 5 (car ev)) 2)))))
                         evs))))

(deftest "linalg/LA.1: собственные значения ((0 -1) (1 0)) — комплексные ±i"
  (let ((evs (eigenvalues '((0 -1) (1 0)))))
    (assert-equal (length evs) 2)
    (assert-true (every? (lambda (ev)
                           (and (= (cadr ev) 1)
                                (linalg::l-zero? (list '+ (list '^ (car ev) 2) 1))))
                         evs))))

(deftest "linalg/LA.1: собственные значения 3×3 с кратным значением"
  (assert-equal (list->set (eigenvalues '((2 0 0) (0 2 0) (0 0 3))))
                (list->set '((2 2) (3 1)))))

(deftest "linalg/LA.1: ((1 1) (0 1)) — λ=1 кратности 2, один вектор"
  (assert-equal (list->set (eigenvalues '((1 1) (0 1)))) (list->set '((1 2)))))

; ---------- собственные векторы ----------

(deftest "linalg/LA.1: собственные векторы ((2 1) (1 2)), проверка A·v = λv"
  (let ((evs (eigenvectors '((2 1) (1 2)))))
    (assert-equal (length evs) 2)
    (assert-true (every? (lambda (ev)
                           (let ((lam (car ev)) (mult (cadr ev)) (vs (caddr ev)))
                             (and (= mult 1) (not (null? vs))
                                  (la-ev-ok? '((2 1) (1 2)) lam vs))))
                         evs))))

(deftest "linalg/LA.1: 3×3 с кратным значением — у λ=2 два вектора"
  (let ((evs (eigenvectors '((2 0 0) (0 2 0) (0 0 3)))))
    (let ((e2 (car (filter (lambda (ev) (equal? (car ev) 2)) evs)))
          (e3 (car (filter (lambda (ev) (equal? (car ev) 3)) evs))))
      (assert-equal (cadr e2) 2)
      (assert-equal (length (caddr e2)) 2)
      (assert-equal (length (caddr e3)) 1)
      (assert-true (la-ev-ok? '((2 0 0) (0 2 0) (0 0 3)) 2 (caddr e2)))
      (assert-true (la-ev-ok? '((2 0 0) (0 2 0) (0 0 3)) 3 (caddr e3))))))

(deftest "linalg/LA.1: недиагонализуемая ((1 1) (0 1)) — один вектор при кратности 2"
  (let ((evs (eigenvectors '((1 1) (0 1)))))
    (assert-equal (length evs) 1)
    (let ((ev (car evs)))
      (assert-equal (car ev) 1)
      (assert-equal (cadr ev) 2)
      (assert-equal (length (caddr ev)) 1)
      (assert-true (la-ev-ok? '((1 1) (0 1)) 1 (caddr ev))))))

(deftest "linalg/LA.1: комплексные собственные векторы ((0 -1) (1 0))"
  (let ((evs (eigenvectors '((0 -1) (1 0)))))
    (assert-equal (length evs) 2)
    (assert-true (every? (lambda (ev)
                           (and (not (null? (caddr ev)))
                                (la-ev-ok? '((0 -1) (1 0)) (car ev) (caddr ev))))
                         evs))))

; ---------- LA.2: диагонализация и жорданова форма ----------

; сертификат P·X = A·P и det P ≠ 0
(define (la-pjp-ok? a p x)
  (and (linalg::l-mat-eq? (linalg::l-matmul p x) (linalg::l-matmul a p))
       (not (linalg::l-zero? (det (linalg::l-mat p))))))

(deftest "linalg/LA.2: ((2 1) (1 2)) диагонализуема, D = diag(1,3)"
  (assert-true (diagonalizable? '((2 1) (1 2))))
  (let* ((r (diagonalize '((2 1) (1 2)))) (P (car r)) (D (cadr r)))
    (assert-equal D '((1 0) (0 3)))
    (assert-true (la-pjp-ok? '((2 1) (1 2)) P D))))

(deftest "linalg/LA.2: ((1 1) (0 1)) не диагонализуема, блок ((1 2))"
  (assert-equal (diagonalizable? '((1 1) (0 1))) #f)
  (assert-error (diagonalize '((1 1) (0 1))))
  (assert-equal (jordan-blocks '((1 1) (0 1))) '((1 2)))
  (let ((r (jordan-form '((1 1) (0 1)))))
    (assert-true (la-pjp-ok? '((1 1) (0 1)) (car r) (cadr r)))))

(deftest "linalg/LA.2: 3×3 ((2 1 0) (0 2 0) (0 0 2)) — блоки (2 2) и (2 1)"
  (let* ((m '((2 1 0) (0 2 0) (0 0 2)))
         (r (jordan-form m)))
    (assert-equal (jordan-blocks m) '((2 2) (2 1)))
    (assert-true (la-pjp-ok? m (car r) (cadr r)))))

(deftest "linalg/LA.2: 3×3 ((5 4 2) (0 5 3) (0 0 5)) — один блок размера 3"
  (let* ((m '((5 4 2) (0 5 3) (0 0 5)))
         (r (jordan-form m)))
    (assert-equal (jordan-blocks m) '((5 3)))
    (assert-true (la-pjp-ok? m (car r) (cadr r)))))

(deftest "linalg/LA.2: 4×4 с двумя блоками размера 2 одного λ"
  (let* ((m '((3 1 0 0) (0 3 0 0) (0 0 3 1) (0 0 0 3)))
         (r (jordan-form m)))
    (assert-equal (jordan-blocks m) '((3 2) (3 2)))
    (assert-true (la-pjp-ok? m (car r) (cadr r)))))

(deftest "linalg/LA.2: 4×4, сопряжённая невырожденной целой S"
  (let* ((j '((3 1 0 0) (0 3 0 0) (0 0 3 1) (0 0 0 3)))
         (s '((1 2 0 0) (0 1 0 0) (0 0 1 3) (0 0 0 1)))
         (m (linalg::l-matmul s (linalg::l-matmul j (inv (linalg::l-mat s)))))
         (r (jordan-form m)))
    (assert-equal (jordan-blocks m) '((3 2) (3 2)))
    (assert-true (la-pjp-ok? m (car r) (cadr r)))))

(deftest "linalg/LA.2: ((1 2) (3 4)) диагонализуема с √33"
  (let* ((m '((1 2) (3 4)))
         (r (diagonalize m)))
    (assert-true (diagonalizable? m))
    (assert-true (la-pjp-ok? m (car r) (cadr r)))))

(deftest "linalg/LA.2: жорданова форма диагонализуемой ((1 2) (3 4))"
  (let* ((m '((1 2) (3 4)))
         (r (jordan-form m)))
    (assert-true (la-pjp-ok? m (car r) (cadr r)))))

; ---------- LA.3: матричная экспонента, степень, функции ----------

(define (la-mat-eq? a b) (linalg::l-mat-eq? a b))

(define (la-fib k) (if (< k 2) k (+ (la-fib (- k 1)) (la-fib (- k 2)))))

(deftest "linalg/LA.3: mat-exp ((0 1) (-1 0)) = cos/sin"
  (assert-true (la-mat-eq? (mat-exp '((0 1) (-1 0)) 't)
                           '(((cos t) (sin t)) ((* -1 (sin t)) (cos t))))))

(deftest "linalg/LA.3: mat-exp жордановой ((1 1) (0 1))"
  (assert-true (la-mat-eq? (mat-exp '((1 1) (0 1)) 't)
                           '(((exp t) (* t (exp t))) (0 (exp t))))))

(deftest "linalg/LA.3: mat-exp 3×3 с блоком размера 3"
  (let ((E (mat-exp '((2 1 0) (0 2 1) (0 0 2)) 't)))
    (assert-true (la-mat-eq? E
      '(((exp (* 2 t)) (* t (exp (* 2 t))) (* 1/2 (^ t 2) (exp (* 2 t))))
        (0 (exp (* 2 t)) (* t (exp (* 2 t))))
        (0 0 (exp (* 2 t))))))))

(deftest "linalg/LA.3: mat-exp диагонализуемой ((1 2) (3 4)) — сертификат"
  (let ((E (mat-exp '((1 2) (3 4)) 't)))
    (assert-equal (length E) 2)))

(deftest "linalg/LA.3: mat-power Фибоначчи ((1 1) (1 0)) — элемент (0,1) = F(n)"
  (let ((M (mat-power '((1 1) (1 0)) 'n)))
    (assert-true (every? (lambda (k)
                           (linalg::l-zero? (list '- (nth (nth (linalg::l-subst-mat 'n k M) 0) 1) (la-fib k))))
                         (range 11)))))

(deftest "linalg/LA.3: mat-power ((2 1) (0 2)) = 2ⁿ, n·2^{n−1}"
  (assert-true (la-mat-eq? (mat-power '((2 1) (0 2)) 'n)
                           '(((^ 2 n) (* (^ 2 (+ -1 n)) n)) (0 (^ 2 n))))))

(deftest "linalg/LA.3: mat-power нильпотентной — n ≥ 2, прямые степени при 0 и 1"
  (let ((A '((0 1) (0 0))))
    (assert-true (la-mat-eq? (mat-power A 0) '((1 0) (0 1))))
    (assert-true (la-mat-eq? (mat-power A 1) A))
    (let ((M (mat-power A 'n)))
      (assert-true (la-mat-eq? (linalg::l-subst-mat 'n 2 M) '((0 0) (0 0))))
      (assert-true (la-mat-eq? (linalg::l-subst-mat 'n 3 M) '((0 0) (0 0)))))))

(deftest "linalg/LA.3: mat-fn sqrt diag(4,9) = diag(2,3)"
  (assert-true (la-mat-eq? (mat-fn 'sqrt '((4 0) (0 9))) '((2 0) (0 3)))))

(deftest "linalg/LA.3: mat-fn (lambda (x) (* x x)) на недиагонализуемой = A·A"
  (let ((A '((1 1) (0 1))))
    (assert-true (la-mat-eq? (mat-fn '(lambda (x) (* x x)) A)
                             (linalg::l-matmul A A)))))

; ---------- LA.4: mathlang-обёртки, явная нильпотентная форма, шаги ----------

(deftest "linalg/LA.4: math-mat-exp — тензор для читаемой печати"
  (let ((E (math-mat-exp '((2 1) (0 2)) 't)))
    (assert-true (tensor? E))
    (assert-true (la-mat-eq? (tensor->list E)
                             '(((exp (* 2 t)) (* t (exp (* 2 t)))) (0 (exp (* 2 t))))))))

(deftest "linalg/LA.4: math-jordan-form — (P J) тензорами"
  (let ((r (math-jordan-form '((0 1) (0 0)))))
    (assert-true (and (list? r) (= (length r) 2)))
    (assert-true (tensor? (car r)))
    (assert-true (tensor? (cadr r)))
    ; P·J·P⁻¹ = A
    (assert-true (la-mat-eq? (linalg::l-matmul (linalg::l-matmul (tensor->list (car r)) (tensor->list (cadr r)))
                                                (inv (linalg::l-mat (tensor->list (car r)))))
                             '((0 1) (0 0))))))

(deftest "linalg/LA.4: math-mat-power нильпотентной — явные нули (нет 0^n)"
  (let ((M (math-mat-power '((0 1) (0 0)) 'n)))
    (assert-true (tensor? M))
    (assert-equal '((0 0) (0 0)) (tensor->list M))))

(deftest "linalg/LA.4: math-mat-power нильпотентной — условие n ≥ s (record-condition)"
  (let ((r (capture-conditions (lambda () (math-mat-power '((0 1) (0 0)) 'n)))))
    (assert-true (and (list? (cadr r)) (not (null? (cadr r)))))
    (assert-true (equal? (car (car (cadr r))) '(>= n 2)))))

(deftest "linalg/LA.4: math-diagonalize — (P D) тензорами"
  (let ((r (math-diagonalize '((2 0) (0 3)))))
    (assert-true (and (list? r) (= (length r) 2)))
    (assert-true (tensor? (car r)))
    (assert-true (la-mat-eq? (tensor->list (cadr r)) '((2 0) (0 3))))))

(deftest "linalg/LA.4: math-mat-fn sqrt diag(4,9) = diag(2,3) — тензор"
  (let ((R (math-mat-fn 'sqrt '((4 0) (0 9)))))
    (assert-true (tensor? R))
    (assert-true (la-mat-eq? (tensor->list R) '((2 0) (0 3))))))

(deftest "linalg/LA.4: шаги eigenvalues — рамки charpoly и eigen-roots"
  (let* ((r (capture-step-log (lambda () (eigenvalues '((2 1) (0 2)))) 'brief))
         (rules (map car (cadr r))))
    (assert-true (member? 'charpoly rules))
    (assert-true (member? 'eigen-roots rules))))

(deftest "linalg/LA.4: шаги mat-exp — exp-blocks и pfjp"
  (let* ((r (capture-step-log (lambda () (mat-exp '((2 1) (0 2)) 't)) 'brief))
         (rules (map car (cadr r))))
    (assert-true (member? 'exp-blocks rules))
    (assert-true (member? 'pfjp rules))))

