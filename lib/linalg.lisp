; linalg.lisp — линейная алгебра на Lisp (шаг LA.1): RREF, ядро, образ, характеристический
; многочлен, собственные значения и векторы.
;
; Только точная арифметика. Матрица — тензор (lib/tensor.lisp) или вложенный список; внутри —
; список строк. RREF — через solve::rref-step (Гаусс–Жордан на выражениях, lib/solve.lisp).
; Собственные значения — factor-list(charpoly) + solve по каждому множителю; кратность — из
; factor-list. Каждая функция проверяет результат (сертификат) и при неудаче бросает ошибку,
; а не возвращает ложный ответ.
;
; Ограничение: деление на ведущий элемент, который может быть нулём при параметрах, не
; анализируется — условия на параметры вне шага LA.1.

(module linalg
  (export rref nullspace columnspace charpoly eigenvalues eigenvectors diagonalizable? diagonalize jordan-form jordan-blocks mat-exp mat-power mat-fn
        linalg-pretty math-jordan-form math-jordan-blocks math-mat-exp math-mat-power math-mat-fn math-diagonalize math-diagonalizable?))

; ---------- строки матрицы ----------

(define (l-rows m) (tensor->list (tensor m)))
(define (l-mat rows) (tensor rows))
(define (l-nrows rows) (length rows))
(define (l-ncols rows) (length (car rows)))

; RREF через solve::rref-step → (done . rest): done — ((столбец . строка) …) с единичным ведущим
(define (l-rref-data rows)
  (solve::rref-step '() rows 0 (l-ncols rows)))

(define (l-pivots res) (map car (car res)))
(define (l-rank rows) (length (l-pivots (l-rref-data rows))))

; строка ведущего столбца j или #f
(define (l-pivot-row done j)
  (let ((p (assoc j done)))
    (if p (cdr p) #f)))

; ---------- проверки (сертификаты) ----------

(define (l-dot row v)
  (simplify (cons '+ (map2 (lambda (a b) (list '* a b)) row v))))

(define (l-num e) (try (eval-num e) (lambda (err) #f)))

(define (l-zero-num? e)
  (let ((v (l-num e)))
    (and v (number? v) (< (abs v) 0.000000001))))

; ноль: simplify/together дали 0 либо численно < 1e-9
(define (l-zero? e)
  (or (equal? (together (simplify e)) 0) (l-zero-num? e)))

; относительное совпадение (1e-9) для радикалов, которые simplify не сводит
(define (l-close? a b)
  (let ((x (l-num a)) (y (l-num b)))
    (and x y (number? x) (number? y)
         (let ((d (abs (- x y))) (s (max (max 1.0 (abs x)) (abs y))))
           (< (/ d s) 0.000000001)))))

; ---------- RREF ----------

; (rref m) — приведённый ступенчатый вид (m строк, ведущие единицы, нули над/под ведущими)
(define (rref m)
  (let* ((rows (l-rows m))
         (res (l-rref-data rows))
         (piv (map cdr (car res)))
         (zero (map (lambda (r) (map (lambda (x) 0) r)) (cdr res))))
    (l-mat (append piv zero))))

; ---------- ядро ----------

; (nullspace m) — базис ядра: вектор на каждый свободный столбец; v[f] = 1,
; v[ведущий] = −(rref-строка)[f]; сертификат: A·v = 0 и число векторов = n − rank
(define (nullspace m)
  (let* ((rows (l-rows m))
         (n (l-ncols rows))
         (res (l-rref-data rows))
         (done (car res))
         (pivs (map car done))
         (free (filter (lambda (j) (not (member? j pivs))) (range n)))
         (vecs (map (lambda (f)
                      (map (lambda (j)
                             (cond ((= j f) 1)
                                   ((member? j pivs) (simplify (list '* -1 (nth (l-pivot-row done j) f))))
                                   (else 0)))
                           (range n)))
                    free)))
    (if (not (= (length vecs) (- n (length pivs))))
        (error "linalg/nullspace: сертификат не прошёл: число векторов ≠ n − rank"))
    (if (not (every? (lambda (v) (every? (lambda (row) (l-zero? (l-dot row v))) rows)) vecs))
        (error "linalg/nullspace: сертификат не прошёл: A·v ≠ 0"))
    vecs))

; ---------- образ ----------

; (columnspace m) — базис образа: столбцы ИСХОДНОЙ матрицы при ведущих позициях rref;
; сертификат: выбранные столбцы линейно независимы (их ранг = их число)
(define (columnspace m)
  (let* ((rows (l-rows m))
         (res (l-rref-data rows))
         (pivs (map car (car res)))
         (cols (map (lambda (j) (map (lambda (r) (nth r j)) rows)) pivs)))
    (if (not (= (l-rank cols) (length cols)))
        (error "linalg/columnspace: сертификат не прошёл: столбцы линейно зависимы"))
    cols))

; ---------- характеристический многочлен ----------

; (charpoly m lam) — det(lam·I − A), раскрытый по lam; сертификат: степень n, старший коэффициент 1
(define (charpoly m lam)
  (let* ((rows (l-rows m))
         (n (l-nrows rows))
         (mi (map2 (lambda (row i)
                     (map2 (lambda (a j) (simplify (if (= i j) (list '- lam a) (list '* -1 a))))
                           row (range n)))
                   rows (range n)))
         (cp (expand (det (l-mat mi)))))
    (if (and (= (degree cp lam) n) (equal? (coeff cp lam n) 1))
        cp
        (error "linalg/charpoly: сертификат не прошёл: степень или старший коэффициент" cp))))

; ---------- собственные значения ----------

(define l-eig-var '%lam)           ; зарезервированный символ переменной charpoly для eigenvalues

; корни многочлена f по lam (множество solve → список; иначе — как есть)
(define (l-roots f lam)
  (let ((s (solve (list '= f 0) lam)))
    (cond ((set? s) (set->list s))
          ((list? s) s)
          (else (list s)))))

; (eigenvalues m) — список (λ кратность): множители charpoly, корни каждого через solve,
; кратность — из factor-list (неприводимый множитель степени d с кратностью k даёт d корней
; кратности k; множитель степени ≥ 3 без радикалов остаётся в форме solve — root-of)
; Шаг LA.4: рамки шагов — «характеристический многочлен» и «корни (кратности)»
(define (eigenvalues m)
  (let* ((cp (with-step ('charpoly "характеристический многочлен" m)
               (charpoly m l-eig-var)))
         (fl (factor-list cp))
         (factors (cdr fl)))
    (with-step ('eigen-roots "корни характеристического многочлена (кратности)" cp)
      (append-map (lambda (fm)
                    (let ((f (car fm)) (mult (cadr fm)))
                      (if (= (degree f l-eig-var) 0)
                          '()
                          (map (lambda (r) (list r mult)) (l-roots f l-eig-var)))))
                  factors))))

; ---------- собственные векторы ----------

; (eigenvectors m) — список (λ кратность (v₁ …)): базис nullspace(A − λI); сертификат A·v = λ·v
(define (eigenvectors m)
  (let* ((rows (l-rows m))
         (n (l-ncols rows))
         (evs (eigenvalues m)))
    (map (lambda (ev)
           (let* ((lam (car ev))
                  (mult (cadr ev))
                  (shifted (map2 (lambda (row i)
                                   (map2 (lambda (a j) (simplify (if (= i j) (list '- a lam) a)))
                                         row (range n)))
                                 rows (range n)))
                  (vs (with-step ('kernel "ядро A − λI (собственные векторы)" (l-mat shifted))
                         (nullspace (l-mat shifted)))))
             (if (null? vs)
                 (error "linalg/eigenvectors: не найден собственный вектор для λ" lam))
             (if (not (every? (lambda (v)
                                (every? (lambda (pair)
                                          (let ((lhs (l-dot (car pair) v))
                                                (rhs (simplify (list '* lam (nth v (cadr pair))))))
                                            (or (l-zero? (list '- lhs rhs)) (l-close? lhs rhs))))
                                        (map2 list rows (range n))))
                              vs))
                 (error "linalg/eigenvectors: сертификат A·v = λ·v не прошёл для λ" lam))
             (list lam mult vs)))
         evs)))

; ========== Шаг LA.2: диагонализация и жорданова форма ==========
; λ — собственное значение, k — его алгебраическая кратность. Диагонализация: P из собственных
; векторов, D = diag(λ). Жордан: цепочки обобщённых векторов по ядрам N_j = nullspace((A−λI)^j);
; блок — λ на диагонали, 1 над ней; в P цепочка идёт от собственного вектора к старшему.
; Сертификаты: P·X − A·P = 0 (X = D или J) и det P ≠ 0; не прошло — ошибка, а не ответ.

; A − λI
(define (l-shift rows lam)
  (let ((n (l-nrows rows)))
    (map2 (lambda (row i)
            (map2 (lambda (a j) (simplify (if (= i j) (list '- a lam) a)))
                  row (range n)))
          rows (range n))))

(define (l-matvec rows v) (map (lambda (row) (l-dot row v)) rows))

(define (l-matmul a b) (tensor->list (mat-mul (l-mat a) (l-mat b))))

(define (l-identity n) (tensor->list (identity-matrix n)))

(define (l-matpow m j)
  (cond ((= j 0) (l-identity (l-nrows m)))
        ((= j 1) m)
        (else (l-matmul m (l-matpow m (- j 1))))))

; матрица из вектор-столбцов
(define (l-from-cols cols)
  (if (null? cols)
      '()
      (map (lambda (i) (map (lambda (c) (nth c i)) cols)) (range (length (car cols))))))

(define (l-diag lst)
  (let ((n (length lst)))
    (map (lambda (i) (map (lambda (j) (if (= i j) (nth lst i) 0)) (range n))) (range n))))

; v ∈ span(vecs)?
(define (l-in-span? v vecs)
  (if (null? vecs)
      (every? (lambda (x) (l-zero? x)) v)
      (<= (l-rank (cons v vecs)) (l-rank vecs))))

; поэлементное равенство матриц (списки строк)
(define (l-mat-eq? a b)
  (every? (lambda (pair)
            (every? (lambda (p) (l-zero? (list '- (car p) (cadr p))))
                    (map2 list (car pair) (cadr pair))))
          (map2 list a b)))

; сертификат P·X = A·P и det P ≠ 0
(define (l-check-pjp rows P X who)
  (if (not (l-mat-eq? (l-matmul P X) (l-matmul rows P)))
      (error (string-append "linalg/" who ": сертификат P·X − A·P ≠ 0")))
  (if (l-zero? (det (l-mat P)))
      (error (string-append "linalg/" who ": сертификат det P = 0")))
  #t)

; ---------- диагонализация ----------

(define (diagonalizable? m)
  (let* ((rows (l-rows m))
         (evs (eigenvalues m)))
    (every? (lambda (ev)
              (let ((lam (car ev)) (k (cadr ev)))
                (= (length (nullspace (l-mat (l-shift rows lam)))) k)))
            evs)))

(define (diagonalize m)
  (let* ((rows (l-rows m))
         (evs (eigenvalues m))
         (parts (map (lambda (ev)
                       (let* ((lam (car ev)) (k (cadr ev))
                              (vs (nullspace (l-mat (l-shift rows lam)))))
                         (if (not (= (length vs) k))
                             (error "linalg/diagonalize: матрица не диагонализуема (λ" lam ")")
                             (list lam vs))))
                     evs))
         (cols (append-map cadr parts))
         (lams (append-map (lambda (p) (map (lambda (v) (car p)) (cadr p))) parts))
         (P (l-from-cols cols))
         (D (l-diag lams)))
    (l-check-pjp rows P D "diagonalize")
    (list P D)))

; ---------- жорданова форма ----------

; d_j = dim N_j (d_0 = 0); для j > m — кратность
(define (l-d dims j)
  (cond ((<= j 0) 0)
        ((<= j (length dims)) (nth dims (- j 1)))
        (else (last dims))))

; b_j = d_j − d_{j−1} — число блоков размера ≥ j
(define (l-b dims j) (- (l-d dims j) (l-d dims (- j 1))))

; e_j = b_j − b_{j+1} — число блоков точного размера j
(define (l-e dims j) (- (l-b dims j) (l-b dims (+ j 1))))

; d_j, пока не достигнута кратность mult
(define (l-dim-chain-loop shifted mult n j acc)
  (let ((d (length (nullspace (l-mat (l-matpow shifted j))))))
    (cond ((>= d mult) (reverse (cons d acc)))
          ((> j n) (error "linalg/jordan-form: dim N_j не достигла кратности"))
          (else (l-dim-chain-loop shifted mult n (+ j 1) (cons d acc))))))
(define (l-dim-chain shifted mult n) (l-dim-chain-loop shifted mult n 1 '()))

; цепочка v, (A−λI)v, … до 0 (длина j); возвращает [w_0 … w_{j−1}]
(define (l-chain-loop shifted j t w acc)
  (if (= t j)
      (begin
        (if (not (every? (lambda (x) (l-zero? x)) w))
            (error "linalg/jordan-form: цепочка не оборвалась в 0"))
        (reverse acc))
      (l-chain-loop shifted j (+ t 1) (l-matvec shifted w) (cons w acc))))
(define (l-chain shifted v j) (l-chain-loop shifted j 0 v '()))

; вектор из N_j вне span(N_{j−1} ∪ used)
(define (l-pick-loop blocked cs)
  (cond ((null? cs) #f)
        ((not (l-in-span? (car cs) blocked)) (car cs))
        (else (l-pick-loop blocked (cdr cs)))))
(define (l-pick nj used nprev) (l-pick-loop (append nprev used) nj))

; count блоков размера j → (used chains); chains — (λ . векторы)
(define (l-build-blocks shifted lam j count used acc)
  (if (= count 0)
      (list used acc)
      (let* ((nj (nullspace (l-mat (l-matpow shifted j))))
             (nprev (if (= j 1) '() (nullspace (l-mat (l-matpow shifted (- j 1))))))
             (v (l-pick nj used nprev)))
        (if (not v)
            (error "linalg/jordan-form: не удалось выбрать обобщённый собственный вектор")
            (let* ((w (l-chain shifted v j))
                   (vecs (reverse w))
                   (used2 (append w used)))
              (l-build-blocks shifted lam j (- count 1) used2 (cons (cons lam vecs) acc)))))))

; все цепочки λ (по убыванию размера)
(define (l-jordan-loop shifted lam dims j used chains)
  (if (= j 0)
      (reverse chains)
      (let ((count (l-e dims j)))
        (if (<= count 0)
            (l-jordan-loop shifted lam dims (- j 1) used chains)
            (let ((res (l-build-blocks shifted lam j count used '())))
              (l-jordan-loop shifted lam dims (- j 1) (car res) (append (cadr res) chains)))))))
(define (l-jordan-chains rows lam mult)
  (let* ((shifted (l-shift rows lam))
         (n (l-nrows rows))
         (dims (l-dim-chain shifted mult n)))
    (l-jordan-loop shifted lam dims (length dims) '() '())))

(define (l-jordan-block lam s)
  (map (lambda (i) (map (lambda (j) (cond ((= i j) lam) ((= j (+ i 1)) 1) (else 0))) (range s))) (range s)))

; блочно-диагональная матрица
(define (l-place-blocks blocks)
  (if (null? blocks)
      '()
      (let* ((b (car blocks)) (s (length b)) (rest (l-place-blocks (cdr blocks))))
        (append
         (map (lambda (row) (append row (map (lambda (x) 0) (range (length rest))))) b)
         (map (lambda (row) (append (map (lambda (x) 0) (range s)) row)) rest)))))

(define (jordan-blocks m)
  (let ((rows (l-rows m)))
    (append-map (lambda (ev)
                  (let ((chains (l-jordan-chains rows (car ev) (cadr ev))))
                    (map (lambda (ch) (list (car ch) (length (cdr ch)))) chains)))
                (eigenvalues m))))

(define (jordan-form m)
  (let* ((rows (l-rows m))
         (evs (eigenvalues m))
         (chains (with-step ('jordan-chains "жордановы цепочки (обобщённые собственные векторы)" m)
                   (append-map (lambda (ev) (l-jordan-chains rows (car ev) (cadr ev))) evs)))
         (P (l-from-cols (append-map cdr chains)))
         (J (l-place-blocks (map (lambda (ch) (l-jordan-block (car ch) (length (cdr ch)))) chains))))
    (l-check-pjp rows P J "jordan-form")
    (list P J)))

; ========== Шаг LA.3: матричная экспонента, степень, функции ==========
; f(A) = P·f(J)·P⁻¹; для блока J_s(λ) элемент на k-й наддиагонали — f^{(k)}(λ)/k!.
; mat-exp: e^{λt}·tᵏ/k!; mat-power: C(n,k)·λ^{n−k}; mat-fn: f(λ) (k = 0) / производные (лямбда).
; Сертификаты: d/dt E = A·E и E(0) = I; Aⁿ при подстановке n = 0…6; f(A) коммутирует с A.

(define (l-lambda? f) (and (list? f) (not (null? f)) (equal? (car f) 'lambda)))

; f(x): символ-функция или (lambda (x) тело)
(define (l-apply-f f x)
  (cond ((l-lambda? f)
         (simplify (subst (list '= (car (cadr f)) x) (caddr f))))
        ((symbol? f) (simplify (list f x)))
        (else (error "linalg: f — символ или (lambda (x) …), получено" f))))

(define (l-fact k) (if (= k 0) 1 (* k (l-fact (- k 1)))))

(define (l-falling n k)
  (if (= k 0) 1 (simplify (list '* (list '- n (- k 1)) (l-falling n (- k 1))))))

(define (l-binom n k)
  (if (= k 0) 1 (simplify (list '* (l-falling n k) (list '^ (l-fact k) -1)))))

; матрица блока по коэффициентам наддиагоналей (coeffs[k] — k-я наддиагональ)
(define (l-block-from-coeffs s coeffs)
  (map (lambda (i) (map (lambda (j) (if (>= j i) (nth coeffs (- j i)) 0)) (range s))) (range s)))

(define (l-subst-mat t val mat)
  (map (lambda (row) (map (lambda (x) (simplify (subst (list '= t val) x))) row)) mat))

(define (l-diff-mat mat t)
  (map (lambda (row) (map (lambda (x) (simplify (diff t x))) row)) mat))

(define (l-zero-at? e t vals)
  (every? (lambda (v) (l-zero-num? (simplify (subst (list '= t v) e)))) vals))

(define (l-mat-eq-at? a b t vals)
  (every? (lambda (pair)
            (every? (lambda (p) (l-zero-at? (list '- (car p) (cadr p)) t vals))
                    (map2 list (car pair) (cadr pair))))
          (map2 list a b)))

; равенство матриц: точно (simplify) либо численно в трёх точках t
(define (l-mat-eq-or-at? a b t)
  (or (l-mat-eq? a b) (l-mat-eq-at? a b t '(1/2 1/3 1/5))))

; --- 2×2 с комплексными λ: e^{αt}(cos βt·I + sin βt·B), B = (A − αI)/β ---

(define (l-2x2-complex? rows)
  (and (= (l-nrows rows) 2)
       (let* ((a (nth (nth rows 0) 0)) (b (nth (nth rows 0) 1))
              (c (nth (nth rows 1) 0)) (d (nth (nth rows 1) 1))
              (disc (simplify (list '+ (list '^ (list '- a d) 2) (list '* 4 b c))))
              (v (l-num disc)))
         (and v (number? v) (< v 0)))))

(define (l-2x2-complex-exp rows t)
  (let* ((a (nth (nth rows 0) 0)) (b (nth (nth rows 0) 1))
         (c (nth (nth rows 1) 0)) (d (nth (nth rows 1) 1))
         (alpha (simplify (list '* 1/2 (list '+ a d))))
         (disc (simplify (list '+ (list '^ (list '- a d) 2) (list '* 4 b c))))
         (beta (simplify (list '* 1/2 (list 'sqrt (list '* -1 disc)))))
         (sh (l-shift rows alpha))
         (B (map (lambda (row) (map (lambda (x) (simplify (list '* x (list '^ beta -1)))) row)) sh))
         (ct (simplify (list 'cos (list '* beta t))))
         (st (simplify (list 'sin (list '* beta t))))
         (eat (simplify (list 'exp (list '* alpha t))))
         (I (l-identity 2)))
    (map2 (lambda (ri Ii)
            (map2 (lambda (x y) (simplify (list '* eat (list '+ (list '* ct y) (list '* st x)))))
                  ri Ii))
          B I)))

; --- матричная экспонента ---

(define (mat-exp m &rest targ)
  (let* ((rows (l-rows m))
         (tt (if (null? targ) '%lt (car targ)))
         (E (if (l-2x2-complex? rows)
                (l-2x2-complex-exp rows tt)
                (let* ((r (jordan-form m))
                       (P (car r))
                       (blocks (jordan-blocks m))
                       (fJ (l-place-blocks
                            (map (lambda (bl)
                                   (let ((lam (car bl)) (s (cadr bl)))
                                     (l-block-from-coeffs
                                      s
                                      (map (lambda (k)
                                             (simplify
                                              (list '* (list 'exp (list '* lam tt))
                                                    (list '* (list '^ tt k) (list '^ (l-fact k) -1)))))
                                           (range s)))))
                                 blocks))))
                  (let ((EE (l-matmul P (l-matmul fJ (inv (l-mat P))))))
                    ; Шаг LA.4: шаги «e^{Jt} по блокам» и «P·e^J·P⁻¹»
                    (record-step 'exp-blocks "e^{Jt} по жордановым блокам" "" blocks fJ)
                    (record-step 'pfjp "P·e^J·P⁻¹" "" fJ EE)
                    EE)))))
    (if (not (l-mat-eq-or-at? (l-diff-mat E tt) (l-matmul rows E) tt))
        (error "linalg/mat-exp: сертификат d/dt E = A·E не прошёл"))
    (let ((E0 (l-subst-mat tt 0 E)))
      (if (not (l-mat-eq? E0 (l-identity (l-nrows rows))))
          (error "linalg/mat-exp: сертификат E(0) = I не прошёл")))
    (if (null? targ) (l-subst-mat tt 1 E) E)))

; --- символьная степень ---

; Шаг LA.4: λ = 0 (нильпотентный блок) — явная форма: при n ≥ s блок N^n = 0 (числа, а не 0^n·C(n,k));
; числовые n идут напрямую (l-matpow); условие n ≥ s — record-condition
(define (l-zero-block s)
  (map (lambda (i) (map (lambda (j) 0) (range s))) (range s)))

(define (l-power-block lam s n)
  (if (and (real-numeric? lam) (= lam 0))
      (l-zero-block s)
      (map (lambda (i) (map (lambda (j)
                              (if (>= j i)
                                  (simplify (list '* (l-binom n (- j i))
                                                  (list '^ lam (list '- n (- j i)))))
                                  0))
                            (range s))) (range s))))

(define (mat-power m n)
  (let ((rows (l-rows m)))
    (if (integer? n)
        (l-matpow rows n)
        (let* ((r (jordan-form m))
               (P (car r))
               (blocks (jordan-blocks m))
               ; Шаг LA.4: минимальный размер нильпотентного блока (λ = 0) — для условия n ≥ s
               (s0 (foldl (lambda (a b) (if (and (real-numeric? (car b)) (= (car b) 0) (> (cadr b) a)) (cadr b) a)) 0 blocks))
               (fJ (l-place-blocks (map (lambda (bl) (l-power-block (car bl) (cadr bl) n)) blocks)))
               (res (l-matmul P (l-matmul fJ (inv (l-mat P))))))
          ; Шаг LA.4: нильпотентные блоки при λ=0 записаны нулём — верно при n ≥ s0
          (if (> s0 0)
              (record-condition (list '>= n s0)
                                (string-append "степень n ≥ " (to-string s0)
                                               ": нильпотентные блоки J^s(0) равны нулю (при меньших n использовать прямые степени)")))
          ; сертификат: подстановка n = s0…(s0+6) совпадает с прямой степенью (0…6 — если нет нильпотентных)
          (if (not (every? (lambda (k) (l-mat-eq? (l-subst-mat n (+ k s0) res) (l-matpow rows (+ k s0))))
                           (range 7)))
              (error "linalg/mat-power: сертификат (n = s0…s0+6) не прошёл"))
          res))))

; --- функции от матриц ---

(define (l-deriv-n var e k)
  (if (= k 0) e (l-deriv-n var (simplify (diff var e)) (- k 1))))

(define (l-fn-block f lam s)
  (cond ((= s 1) (list (list (l-apply-f f lam))))
        ((l-lambda? f)
         (let ((var (car (cadr f))) (body (caddr f)))
           (l-block-from-coeffs
            s
            (map (lambda (k) (simplify (list '* (simplify (subst (list '= var lam) (l-deriv-n var body k)))
                                            (list '^ (l-fact k) -1))))
                 (range s)))))
        (else (error "linalg/mat-fn: для недиагонализуемой матрицы нужна функция-выражение (lambda), не символ" f))))

(define (mat-fn f m)
  (let* ((rows (l-rows m))
         (r (jordan-form m))
         (P (car r))
         (blocks (jordan-blocks m))
         (fJ (l-place-blocks (map (lambda (bl) (l-fn-block f (car bl) (cadr bl))) blocks)))
         (res (l-matmul P (l-matmul fJ (inv (l-mat P))))))
    ; сертификат 1: f(A) коммутирует с A
    (if (not (l-mat-eq? (l-matmul res rows) (l-matmul rows res)))
        (error "linalg/mat-fn: сертификат f(A)·A = A·f(A) не прошёл"))
    ; сертификат 2: на собственных векторах f(A)·v = f(λ)·v
    (if (not (every? (lambda (ev)
                       (let ((lam (car ev)) (vs (caddr ev)) (flam (l-apply-f f (car ev))))
                         (every? (lambda (v)
                                   (let ((rv (l-matvec res v)))
                                     (every? (lambda (pair)
                                               (l-zero? (list '- (nth rv (cadr pair))
                                                              (simplify (list '* flam (nth v (cadr pair)))))))
                                             (map2 list rows (range (l-nrows rows))))))
                                 vs)))
                     (eigenvectors m)))
        (error "linalg/mat-fn: сертификат f(A)·v = f(λ)·v не прошёл"))
    res))

; ---------- Шаг LA.4: вызовы из mathlang (--math) и читаемая печать ----------

; матрица-список строк равной длины чисел/выражений → tensor (для читаемой печати [[..]])
(define (linalg-pretty x)
  (cond ((and (list? x) (not (null? x))
              (every? list? x)
              (not (null? (car x)))
              (every? (lambda (r) (= (length r) (length (car x)))) x))
         (tensor x))
        ; пара (P J) или список матриц → [M1, M2, ...]
        ((and (list? x) (every? (lambda (e) (and (list? e) (every? list? e) (not (null? e)))) x))
         (map linalg-pretty x))
        (else x)))

; обёртки для m-renames: результат → tensor
(define (math-jordan-form m)
  (let ((r (jordan-form m))) (list (linalg-pretty (car r)) (linalg-pretty (cadr r)))))

(define (math-jordan-blocks m)
  (jordan-blocks m))

(define (math-mat-exp m &rest targ)
  (linalg-pretty (apply mat-exp (cons m targ))))

(define (math-mat-power m n)
  (linalg-pretty (mat-power m n)))

(define (math-mat-fn f m)
  (linalg-pretty (mat-fn f m)))

(define (math-diagonalize m)
  (let ((r (diagonalize m))) (list (linalg-pretty (car r)) (linalg-pretty (cadr r)))))

(define (math-diagonalizable? m)
  (diagonalizable? m))
