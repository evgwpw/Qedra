; placesnf.lisp — Шаг R1-хвост: лог-часть Трагера для y² = P, когда знаменатель H содержит неприводимый g(x) степени k ≥ 3.
;
; Места над корнем α многочлена g: поле K = ℚ(α) = ℚ[t]/(g); y(α)² = P(α) = c·s², s ∈ K, c ∈ ℚ.
;   c = 1 (y(α) = s ∈ K): места (α, ±s) K-рациональны;
;   c ≠ 1 (P mod g — константа c = c₀·r², c₀ без квадратов): скручивание η = √c₀·y, Q = c₀·P, η² = Q, на кривой C_Q места
;   (α, ±c₀r) ℚ-рациональны по y; ∫H dx = (1/√c₀)·∫H_Q dx, H_Q = (c₁/D)·η — те же дробь и вычеты на C_Q (J_C ≅ J_{C_Q} над ℚ(√c₀),
;   порядок и главность дивизоров сохраняются).
; Вычет H dx в месте (α, +s): ρ(α) ∈ K (в (α, −s) — минус ρ).  Нечётная часть: c₀(x) ≡ 0 (иначе — прежний путь).
; Базис ℚ-пространства V вычетов (Трагер): D_j = Σ n_{jP}·P, n_{jP} — координаты вычета в P по базису V; ω элементарна ⇒ все D_j —
; кручение (Лиувилль).  Для k = 3 структура V строгая (подмодули ℚ³ для транзитивных C₃, S₃):
;   ρ ∈ ℚ            — один D = Σ_i E_i, E_i = [(α_i, s_i) − (α_i, −s_i)]  (ℚ-рациональный; прежний dv-irred-search);
;   Tr ρ ≠ 0          — сопряжённые вычеты ℚ-независимы: D_i = E_i;  режим B;
;   Tr ρ = 0, ρ ∉ ℚ   — единственное соотношение Σσ_i ρ = 0: D = E_1 − E_3, E_2 − E_3 (разности);  режим C.
; Кручение классов проверяется редукцией по простым 𝔓 | p (корень g mod p ↔ простой K; режим C: g расщепляется на три корня mod p,
; метки корней согласованы, если G = S₃, т. е. дискриминант g — не квадрат): образ торсионного класса порядка n в J(𝔽_p) имеет
; порядок ровно n (p > 2, 𝔓 неразветвлено); два разных порядка ⇒ не кручение.

(module integrate)

; ---------- арифметика K = ℚ[t]/(g): элемент — ib-p по модулю gg ----------

(define (nf-mul a b gg) (dv-a-mod (ib-p-mul a b) gg))

; след a ∈ K: сумма диагонали матрицы умножения на a в базисе 1, α, …, α^{k−1}
(define (nf-trace a gg)
  (foldl (lambda (acc j)
           (+ acc (dv-a-coef (dv-a-mod (ib-p-mul a (dv-a-pow (list 0 1) j gg)) gg) j)))
         0 (range (ib-p-deg gg))))

; неприводимые g знаменателя степени ≥ 2, не делящие P (выражения)
(define (nf-big-factors info P x)
  (let ((fl (try (factor-list (dv-nf-Dexpr info)) (lambda (e) #f)))
        (pp (ib-poly-parse P x)))
    (if (not (pair? fl))
        '()
        (filter (lambda (g)
                  (let ((gg (try (ib-poly-parse g x) (lambda (e) #f))))
                    (and gg (>= (ib-p-deg gg) 2)
                         (not (ib-p-zero? (dv-a-mod pp gg))))))
                (map car (cdr fl))))))

; ρ = c₁·s / (g′·D/g) mod g — вычет в месте (α, +s); #f — не обратим
(define (nf-rho info gg s)
  (let* ((c1p (dv-nf-c1 info)) (Dp (dv-nf-D info))
         (dr (car (ib-p-divmod Dp gg)))
         (den (dv-a-mod (ib-p-mul (dv-p-deriv gg) dr) gg))
         (iv (and (not (ib-p-zero? den)) (dv-a-inv den gg))))
    (and iv (not (ib-p-zero? (dv-a-mod dr gg)))
         (dv-a-mod (ib-p-mul (ib-p-mul c1p s) iv) gg))))

; c = c₀·r² (c₀ — целое без квадратов со знаком, не 1) → (c₀ r) | #f
(define (nf-sqrt-split c)
  (let ((k (try (ib-k-sqrt-rat c) (lambda (e) #f))))
    (and k (= 1 (length k)) (pair? (car (car k))) (= 1 (length (car (car k))))
         (list (car (car (car k))) (cdr (car k))))))

; ---------- редукция по модулю p ----------

; ib-p с рациональными коэффициентами → список коэффициентов mod p (cn-формат) | #f (знаменатель кратен p)
(define (nf-modpoly cs p)
  (try (cn-trim (map (lambda (c) (cn-in p c)) cs)) (lambda (e) #f)))

(define (nf-roots-mod gm p)
  (filter (lambda (a) (= 0 (cn-eval p gm a))) (range p)))

; порядок класса Dp в J(𝔽_p): N = #J(𝔽_p) (считается один раз на p) и спуск по простым; #f — не удалось
(define (nf-order-mod Cp N Dp)
  (if (not (and (integer? N) (> N 0)))
      #f
      (try (if (cn-zero-raw? (cn-mul-raw Cp N Dp))
               (cn-ord-from-multiple Cp Dp N)
               #f)
           (lambda (e) #f))))

; класс E = [(a, sa) − (a, −sa)] в J(𝔽_p)
(define (nf-class-E Cp p a sa)
  (cantor-from-points Cp (list (cons (list a sa) 1) (cons (list a (modulo (- sa) p)) -1))))

(define nf-scan-primes 6)      ; сколько подходящих p просматривается
(define nf-scan-limit 200)     ; p ≤ 200

; Данные по одному p: ((a sa E) …) по корням g mod p с sa ≠ 0 и (в режиме C) ровно тремя различными корнями; #f — p не подходит
; (плохое p, знаменатель, особая g mod p, подсчёт точек вне бюджета).
(define (nf-prime-data P x gg s mode p)
  (let ((g (cn-genus-odd P x)))
    (if (or (not (equal? (hyp-good-prime? P x p) #t)) (> (^ p g) (dv-cap)))
        #f
        (let* ((gm (nf-modpoly gg p)) (sm (nf-modpoly s p))
               (Cp (try (cantor-curve P x p) (lambda (e) #f))))
          (if (not (and gm sm Cp (= (cn-deg gm) (ib-p-deg gg))
                        (= 0 (cn-deg (car (cn-egcd p gm (cn-deriv p gm)))))))
              #f
              (let* ((pm (nf-modpoly (ib-poly-parse P x) p))
                     (rs (nf-roots-mod gm p))
                     (pts (filter (lambda (e) e)
                                  (map (lambda (a)
                                         (let ((sa (cn-eval p sm a)))
                                           (and (not (= sa 0))
                                                (= (modulo (* sa sa) p) (cn-eval p pm a))
                                                (list a sa (try (nf-class-E Cp p a sa) (lambda (e) #f))))))
                                       rs))))
                (cond ((null? pts) #f)
                      ((member? #f (map (lambda (e) (nth e 2)) pts)) #f)
                      ((and (equal? mode 'C) (not (= 3 (length pts)))) #f)
                      (else (list p Cp pts (try (hyp-jacobian-pick P x p) (lambda (e) 'unknown)))))))))))

; Порядки: режим B — порядки E_a по каждому корню; режим C — порядки попарных разностей E_a − E_b.
; Результат: (orders . данные) — ((p a ord) …) / ((p a b ord) …)
(define (nf-orders P x pd mode)
  (let* ((p (nth pd 0)) (Cp (nth pd 1)) (pts (nth pd 2)) (N (nth pd 3)))
    (if (equal? mode 'B)
        (map (lambda (e) (list p (nth e 0) (nf-order-mod Cp N (nth e 2)))) pts)
        (let loop ((i 0) (acc '()))
          (if (>= i (length pts))
              (reverse acc)
              (loop (+ i 1)
                    (let inner ((j (+ i 1)) (acc acc))
                      (if (>= j (length pts))
                          acc
                          (let ((D (try (cn-add-raw Cp (nth (nth pts i) 2) (cn-neg-raw Cp (nth (nth pts j) 2))) (lambda (e) #f))))
                            (inner (+ j 1)
                                   (cons (list p (nth (nth pts i) 0) (nth (nth pts j) 0)
                                               (and D (nf-order-mod Cp N D)))
                                         acc)))))))))))

(define (nf-ord-of e) (nth e (- (length e) 1)))

; ('inconsistent o1 e1 o2 e2) | ('order n entries) | #f — нет ни одного подходящего p / порядок не найден
(define (nf-scan P x gg s mode)
  (let loop ((p 3) (used 0) (all '()))
    (cond
      ((or (> p nf-scan-limit) (>= used nf-scan-primes))
       (if (null? all) #f (list 'order (nf-ord-of (car all)) (reverse all))))
      (else
       (let ((pd (nf-prime-data P x gg s mode p)))
         (if (not pd)
             (loop (next-prime p) used all)
             (let ((os (nf-orders P x pd mode)))
               (cond
                 ((member? #f (map nf-ord-of os)) (loop (next-prime p) used all))
                 (else
                  (let* ((all2 (append (reverse os) all))
                         (bad (let find ((l (cdr all2)))
                                (cond ((null? l) #f)
                                      ((not (= (nf-ord-of (car l)) (nf-ord-of (car all2)))) (car l))
                                      (else (find (cdr l)))))))
                    (if bad
                        (list 'inconsistent (car all2) bad)
                        (loop (next-prime p) (+ used 1) all2))))))))))))

; ---------- функция u над K (режим B): div u = n·(P₊ − P₋), u = (a(x) + b(x)·y)/(x − α)^n, a, b ∈ K[x] ----------
; N = a + b·y ∈ L(2n·∞): deg a ≤ n, deg b ≤ n − g − 1 (g — род), нули порядка ≥ 2n в P₊ = (α, s) — 2n условий над K.
; Неизвестные — коэффициенты в K по ℚ-базису 1, α, …: строки по координатам условий.

(define (nf-u-rows gg ys n da db)
  (let* ((k (ib-p-deg gg))
         (apow (map (lambda (t) (dv-a-pow (list 0 1) t gg)) (range k))))
    (let loop ((r 0) (rows '()))
      (if (>= r (* 2 n))
          (reverse rows)
          (let* ((ea (map (lambda (j) (dv-a-monom j r gg)) (range (+ da 1))))
                 (eb (map (lambda (j) (dv-a-ycoef j r ys gg)) (range (+ db 1))))
                 (cols (append (append-map (lambda (e) (map (lambda (ap) (nf-mul e ap gg)) apow)) ea)
                               (append-map (lambda (e) (map (lambda (ap) (nf-mul e ap gg)) apow)) eb)))
                 (rws (map (lambda (tp) (map (lambda (c) (dv-a-coef c tp)) cols)) (range k))))
            (loop (+ r 1) (append (reverse rws) rows)))))))

; вектор ядра → u(t; x, y) как выражение (t — корень g)
(define (nf-u-expr v n k da db x)
  (let* ((coef (lambda (off j) (ib-poly->expr (map (lambda (t) (nth v (+ off (* j k) t))) (range k)) 't)))
         (A (simplify (cons '+ (map (lambda (j) (list '* (coef 0 j) (list '^ x j))) (range (+ da 1))))))
         (B (simplify (cons '+ (map (lambda (j) (list '* (coef (* (+ da 1) k) j) (list '^ x j))) (range (+ db 1)))))))
    (list '/ (list '+ A (list '* B 'y)) (list '^ (list '- x 't) n))))

; коэффициенты a_j (j ≤ da) и b_j (j ≤ db) ∈ K из вектора ядра: ((a₀ …) (b₀ …)) — элементы K (ib-p)
(define (nf-vec->arrays v k da db)
  (let ((el (lambda (off j) (ib-p-trim (map (lambda (t) (nth v (+ off (* j k) t))) (range k))))))
    (list (map (lambda (j) (el 0 j)) (range (+ da 1)))
          (map (lambda (j) (el (* (+ da 1) k) j)) (range (+ db 1))))))

; ---------- точная проверка ω = Σ_t (ρ_t/n)·dlog u_t: вычисления в K[y]/(y² − P(x₀)) в рациональных точках ----------
; Разность D = H − Σ W_t регулярна во всех конечных точках (вычеты совпадают) и на ∞ (u_t там единица; H — оценка ниже), поэтому
; D = q(x)·dx/y, deg q ≤ max(γ − 1, deg c₁ − deg D + 2γ + 1) (ord_∞ q·dx/y = −2·deg q + 2γ − 2, ord_∞ H dx = 2(deg D − deg c₁) − 2γ − 4).
; Совпадение H и Σ W_t в M = deg q + 1 различных точках x₀ ⇒ D = 0 (точно, без вещественных чисел).  Элемент кольца — пара (e₀ e₁) = e₀ + e₁·y.

(define (nfe-mul a b p0 gg)
  (list (dv-a-mod (ib-p-add (ib-p-mul (car a) (car b)) (ib-p-scale (ib-p-mul (cadr a) (cadr b)) p0)) gg)
        (dv-a-mod (ib-p-add (ib-p-mul (car a) (cadr b)) (ib-p-mul (cadr a) (car b))) gg)))

(define (nfe-inv a p0 gg)
  (let* ((nrm (dv-a-mod (ib-p-sub (ib-p-mul (car a) (car a)) (ib-p-scale (ib-p-mul (cadr a) (cadr a)) p0)) gg))
         (iv (and (not (ib-p-zero? nrm)) (dv-a-inv nrm gg))))
    (and iv (list (dv-a-mod (ib-p-mul (car a) iv) gg)
                  (dv-a-mod (ib-p-neg (ib-p-mul (cadr a) iv)) gg)))))

; многочлен от x с K-коэффициентами (список ib-p) в рациональной точке
(define (nf-peval-k cs x0)
  (foldl (lambda (acc c) (ib-p-add (ib-p-scale acc x0) c)) '() (reverse cs)))

(define (nf-pder-k cs)
  (map (lambda (j) (ib-p-scale (nth cs (+ j 1)) (+ j 1))) (range (max 0 (- (length cs) 1)))))

; (ρ/n)·u′/u в точке x₀ для u = (A + B·y)/(x − t)^n — пара (e₀ e₁) | #f (вырожденная точка)
(define (nf-w-at As Bs n x0 pp rho gg)
  (let* ((p0 (dv-p-eval pp x0)) (dp0 (dv-p-eval (dv-p-deriv pp) x0)))
    (if (= p0 0)
        #f
        (let* ((Av (dv-a-mod (nf-peval-k As x0) gg)) (Bv (dv-a-mod (nf-peval-k Bs x0) gg))
               (dA (dv-a-mod (nf-peval-k (nf-pder-k As) x0) gg))
               (dB (dv-a-mod (nf-peval-k (nf-pder-k Bs) x0) gg))
               (Nv (list Av Bv))
               (dN (list dA (dv-a-mod (ib-p-add dB (ib-p-scale Bv (/ dp0 (* 2 p0)))) gg)))
               (iN (nfe-inv Nv p0 gg))
               (ix (dv-a-inv (list x0 -1) gg)))
          (and iN ix
               (let* ((q (nfe-mul dN iN p0 gg))
                      (q2 (list (dv-a-mod (ib-p-sub (car q) (ib-p-scale ix n)) gg) (cadr q))))
                 (nfe-mul (list (dv-a-mod (ib-p-scale rho (/ 1 n)) gg) '()) q2 p0 gg)))))))

; #t — H = Σ W_t точно; #f — нет; (хватает ли точек: 'skip)
(define (nf-exact-check info P x gg rho n As Bs)
  (let* ((pp (ib-poly-parse P x))
         (genus (cn-genus-odd P x))
         (c1p (dv-nf-c1 info)) (Dp (dv-nf-D info)) (c0p (dv-nf-c0 info))
         (dq (max (- genus 1) (+ (- (ib-p-deg c1p) (ib-p-deg Dp)) (* 2 genus) 1)))
         (M (+ dq 1)))
    (let loop ((x0 0) (cnt 0) (sgn 1))
      (cond
        ((>= cnt M) #t)
        ((> (abs x0) 40) 'skip)
        (else
         (let* ((dd (dv-p-eval Dp x0))
                (W (and (not (= dd 0)) (nf-w-at As Bs n x0 pp rho gg)))
                (next (if (> sgn 0) (- 0 (+ x0 1)) (- 0 x0))))   ; 0, −1, 1, −2, 2, …
           (if (not W)
               (loop next cnt (- sgn))
               (let ((t0 (nf-trace (car W) gg)) (t1 (nf-trace (cadr W) gg))
                     (h0 (/ (dv-p-eval c0p x0) dd)) (h1 (/ (dv-p-eval c1p x0) dd)))
                 (if (and (= t0 h0) (= t1 h1))
                     (loop next (+ cnt 1) (- sgn))
                     #f)))))))))

; ответ режима B: (logs-sum E #t) — root-sum по корням g от (ρ(t)/n)·log u(t; x, y), проверен точно | 'nonelementary (остаток —
; ненулевой дифференциал 1-го рода) | 'unknown
(define (nf-answer-b P x g gg s rho n info)
  (let* ((k (ib-p-deg gg))
         (genus (cn-genus-odd P x))
         (da n) (db (- n genus 1))
         (ys (dv-y-series g P x s (* 2 n))))
    (if (or (equal? ys 'unknown) (< db -1))
        'unknown
        (let* ((rows (nf-u-rows gg ys n da db))
               (ker (try (fm-nullspace (field-Q) rows) (lambda (e) 'unknown))))
          (if (or (equal? ker 'unknown) (null? ker))
              (begin (record-condition (list 'nf-principal-not-found n)
                                       "вычеты над ℚ(α): порядок кручения найден по модулям p, но функция u над ℚ(α) не найдена — не знаю")
                     'unknown)
              (let* ((arr (nf-vec->arrays (car ker) k da db))
                     (ok (nf-exact-check info P x gg rho n (car arr) (cadr arr))))
                (cond
                  ((equal? ok #t)
                   (let* ((u (nf-u-expr (car ker) n k da db x))
                          (gt (subst (list (list x 't)) g))
                          (rt (ib-poly->expr rho 't)))
                     (alg-step 'alg-principal "Проверка главности n·δ"
                               (string-append "найдена функция u(t) = (a(x) + b(x)·y)/(x − t)^" (to-string n)
                                              " (a, b ∈ ℚ(α)[x]) с div u = " (to-string n) "·E; точная проверка H = Σ (ρ/n)·u′/u в K[y]/(y² − P(x₀)) в рациональных точках: совпадает")
                               (list 'list n) (list 'log u))
                     (list 'logs-sum
                           (list 'root-sum 't gt (list '* (list '/ rt n) (list 'log u)))
                           #t)))
                  ; H − Σ W_t = q·dx/y: при deg q ≤ γ − 1 (голоморфный остаток) q ≠ 0 ⇒ неэлементарен
                  ((and (equal? ok #f)
                        (<= (+ (- (ib-p-deg (dv-nf-c1 info)) (ib-p-deg (dv-nf-D info))) (* 2 genus) 1) (- genus 1)))
                   (set! alg-why (string-append "дивизор вычетов над ℚ(α) — кручение (n = " (to-string n)
                                                "), но остаток H − Σ (ρ/n)·u′/u — ненулевой дифференциал 1-го рода — первообразной нет"))
                   'nonelementary)
                  (else 'unknown))))))))

; ---------- режимы B/C (c = 1: y(α) = s ∈ K) ----------

; ---------- шаги (журнал; только под alg-log?) ----------

(define nf-tw #f)          ; (c₀ Q) во время разбора скрученной кривой

(define (nf-note-places H P x g gg s rho T mode)
  (alg-step 'alg-residues "Вычеты H dx и дивизор вычетов δ"
            (string-append
             (if nf-tw
                 (string-append "скручивание η = √c₀·y, c₀ = " (to-string (car nf-tw)) ": кривая η² = Q, Q = " (alg-mp (cadr nf-tw))
                                "; H dx = (1/√c₀)·H_Q dx, H_Q = (c₁/D)·η; ")
                 "")
             "места над ℚ(α), α — корень g = " (alg-mp g) " (k = " (to-string (ib-p-deg gg)) "): на кривой y² = " (alg-mp P)
             " имеем y(α) = s = " (alg-mp (ib-poly->expr s 'α)) "; вычет в месте (α, +s) равен ρ = " (alg-mp (ib-poly->expr rho 'α))
             ", Tr ρ = " (to-string T) "; "
             (if (equal? mode 'B)
                 "Tr ρ ≠ 0 — сопряжённые вычеты ℚ-независимы, дивизор E = [(α, s) − (α, −s)] над ℚ(α)"
                 "Tr ρ = 0 — единственное соотношение между сопряжёнными вычетами, дивизоры E_a − E_b"))
            (int-form H x) (list '= 'rho (ib-poly->expr rho 'α))))

; строка записи сканирования: B — (p a ord), C — (p a b ord)
(define (nf-entry-str e mode)
  (if (equal? mode 'B)
      (string-append "p = " (to-string (nth e 0)) ", α ≡ " (to-string (nth e 1)) ": " (to-string (nth e 2)))
      (string-append "p = " (to-string (nth e 0)) ", α ≡ (" (to-string (nth e 1)) ", " (to-string (nth e 2)) "): " (to-string (nth e 3)))))

(define (nf-note-scan sc mode verdict)
  (alg-step 'alg-principal "Проверка главности n·δ"
            (string-append "Кантор по модулю p, "
                           (if (equal? mode 'B)
                               "корень α ≡ a (простой 𝔓 | p), порядок ord(E mod 𝔓): "
                               "корни α ≡ a, b согласованы (G = S₃), порядок ord((E_a − E_b) mod 𝔓): ")
                           (alg-join (map (lambda (e) (nf-entry-str e mode))
                                          (if (equal? (car sc) 'order)
                                              (let ((l (nth sc 2))) (if (> (length l) 6) (take l 6) l))
                                              (list (nth sc 1) (nth sc 2))))
                                     "; ")
                           (cond ((equal? (car sc) 'order)
                                  (string-append "; все порядки равны n = " (to-string (nth sc 1))
                                                 " — кандидат в кручение порядка n (обоснование: образ кручения порядка n в J(𝔽_p) имеет порядок ровно n; p > 2, 𝔓 | p неразветвлено)"))
                                 (else "; порядки различны ⇒ дивизор не кручение (иначе все порядки равны n)"))
                           verdict)
            (list 'list (if (equal? (car sc) 'order) (nth sc 1) 'non-torsion)) (if (equal? (car sc) 'order) (nth sc 1) 'non-torsion)))

(define (nf-log-bc H P x info g gg s rho)
  (let* ((k (ib-p-deg gg))
         (T (nf-trace rho gg))
         (mode (if (= T 0) 'C 'B))
         (ndeg (try (degree P x) (lambda (e) 0)))
         (strict (and (= k 3)
                      (or (equal? mode 'B) (equal? (try (galois-disc-square? g x) (lambda (e) 'unknown)) #f)))))
    (if (not (and (integer? ndeg) (odd? ndeg) (>= ndeg 3)))
        'unknown
        (begin
          (nf-note-places H P x g gg s rho T mode)
          (let ((sc (nf-scan P x gg s mode)))
            (cond
              ((not sc) 'unknown)
              ((equal? (car sc) 'inconsistent)
               (if strict
                   (begin (nf-note-scan sc mode "")
                          (set! alg-why (string-append "вычеты над ℚ(α), g — кубика: порядки образов дивизора в J(𝔽_p) различны (p = "
                                                       (to-string (car (nth sc 1))) " и p = " (to-string (car (nth sc 2)))
                                                       ") — не кручение, интеграл неэлементарен"))
                          'nonelementary)
                   'unknown))
              ((equal? mode 'C)
               (nf-note-scan sc mode "; функция u над замыканием поля не строится — не знаю")
               (record-condition (list 'nf-torsion-candidate (nth sc 1))
                                 "вычеты над ℚ(α) с Tr ρ = 0: порядки разностей мест согласованы, но функция u над замыканием поля не строится — не знаю")
               'unknown)
              (else
               (nf-note-scan sc mode "")
               (nf-answer-b P x g gg s rho (nth sc 1) info))))))))

(define (nf-direct H P x info g gg s)
  (let ((rho (nf-rho info gg s)))
    (cond ((not rho) 'unknown)
          ((dv-a-const rho) #f)            ; ρ ∈ ℚ — прежний dv-irred-search
          (else (nf-log-bc H P x info g gg s rho)))))

; ---------- c ≠ 1: скручивание ----------

(define (nf-untwist L c0)
  (let ((sc (list '^ c0 1/2)))
    (cond ((and (list? L) (equal? (car L) 'logs))
           (list 'logs (cadr L)
                 (map (lambda (tr)
                        (list (simplify (list '/ (car tr) sc)) (cadr tr)
                              (simplify (subst (list (list 'y (list '* sc 'y))) (caddr tr)))))
                      (caddr L))))
          ((and (list? L) (equal? (car L) 'logs-sum))
           (list 'logs-sum (simplify (list '/ (subst (list (list 'y (list '* sc 'y))) (cadr L)) sc)) (and (pair? (cddr L)) (caddr L))))
          (else L))))

; c₀ — класс P(α) по модулю квадратов K^*: P(α) = c₀·r²·s², s ∈ K.  Постоянная P mod g — сам класс; нечётная степень k —
; свободная часть нормы N(P(α)) = c₀^k·(квадрат): без квадратов N даёт c₀.  #f — не определён (чётное k, не константа).
(define (nf-twist-class g gg P x)
  (let* ((rem (dv-a-mod (ib-poly-parse P x) gg))
         (c (dv-a-const rem)))
    (cond ((and c (number? c)) (let ((sp (nf-sqrt-split c))) (and sp (car sp))))
          ((odd? (ib-p-deg gg))
           (let* ((lc (ib-p-lc gg))
                  (N (try (/ (resultant g (ib-poly->expr rem x) x) (^ lc (ib-p-deg rem))) (lambda (e) #f)))
                  (sp (and N (not (= N 0)) (nf-sqrt-split N))))
             (and sp (car sp))))
          (else #f))))

(define (nf-twisted H P x info g gg)
  (let ((c0 (nf-twist-class g gg P x)))
    (if (or (not c0) (= c0 1))
        'unknown
        (let* ((Q (expand (list '* c0 P)))
               (HQ (list '* (list '/ (ib-poly->expr (dv-nf-c1 info) x) (ib-poly->expr (dv-nf-D info) x)) 'y)))
          (set! nf-tw (list c0 Q))
          (nf-untwist (unwind-protect (hyp-log-irred HQ Q x) (set! nf-tw #f)) c0)))))

; #f — не наш случай (прежний путь); иначе результат hyp-log-irred
(define (nf-log-one H P x info g)
  (let* ((gg (ib-poly-parse g x)) (br (dv-g-branch g P x)))
    (cond
      ((not (ib-p-zero? (dv-nf-c0 info))) #f)
      ((or (equal? br 'tower) (and (pair? br) (equal? (car br) 'tower))) (nf-twisted H P x info g gg))
      ((and (pair? br) (number? (car br))) (nf-direct H P x info g gg br))
      (else #f))))

(define (hyp-log-nf H P x)
  (let ((info (dv-nf-info H P x)))
    (if (equal? info 'unknown)
        #f
        (let ((gl (nf-big-factors info P x)))
          (if (not (and (= 1 (length gl)) (>= (try (degree (car gl) x) (lambda (e) 0)) 3)))
              #f
              (try (nf-log-one H P x info (car gl)) (lambda (e) 'unknown)))))))
