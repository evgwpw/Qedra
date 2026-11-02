; cfinite.lisp — C-конечные последовательности (шаги RE.1–RE.3).
; Последовательность задаётся (cfinite (c1 … cr) (a0 … a_{r−1})):
;   a(n+r) = c1·a(n+r−1) + … + cr·a(n).
; Все коэффициенты и начальные значения — точные числа (float запрещён).
; Быстрое n-е значение — x^n mod χ(x), χ(x) = x^r − c1·x^{r−1} − … − cr (Фидуччи, удвоение).
; Порядок операций: r+s для суммы, r·s для произведения, r+1 для частичной суммы;
; построение — Берлекэмп–Мэсси по 2·R членам (R — оценка теоремы), что для C-конечной
; последовательности порядка ≤ R даёт точную рекуррентность.

(module cfinite
  (export cf? cfinite cf-coeffs cf-init cf-order cf-check
          cf-term cf-term-mod cf-terms cf-shift cf-from-terms
          cf+ cf* cf-scale cf-partial-sum
          cf-char-poly cf-of-expr cf-prove cf-check-proof
          cf->gf gf->cf cf-closed-form))

; ---------- представление ----------

(define (cf-num? x) (or (integer? x) (equal? (type-of x) 'rational)))

; (cfinite коэффициенты начальные) — конструктор с проверкой
(define (cfinite c init)
  (if (or (null? c) (null? init))
      (error "cfinite: нужны непустые коэффициенты и начальные значения" c init))
  (if (not (= (length c) (length init)))
      (error "cfinite: длина коэффициентов и начальных значений должна совпадать" c init))
  (if (not (and (cf-all-num? c) (cf-all-num? init)))
      (error "cfinite: коэффициенты и начальные значения — точные числа" c init))
  (list 'cfinite c init))

(define (cf-all-num? xs)
  (or (null? xs) (and (cf-num? (car xs)) (cf-all-num? (cdr xs)))))

(define (cf? s) (and (list? s) (= (length s) 3) (equal? (car s) 'cfinite)))
(define (cf-coeffs s) (nth s 1))
(define (cf-init s) (nth s 2))
(define (cf-order s) (length (cf-coeffs s)))

; (cf-check s) — рекуррентность подтверждается независимо посчитанными членами (cf-term)
(define (cf-check s)
  (let* ((c (cf-coeffs s)) (r (cf-order s)))
    (cf-check-n c s r r)))

(define (cf-check-n c s r n)
  (if (> n (+ r 5))
      #t
      (let ((lhs (cf-term s n))
            (rhs (cf-dot c (map (lambda (i) (cf-term s (- n 1 i))) (range r)))))
        (if (equal? lhs rhs) (cf-check-n c s r (+ n 1)) #f))))

; окно [i−r, i−1] в порядке (a(n+r−1) … a(n))
(define (cf-window ts i r)
  (if (= r 0) '() (cons (nth ts (- i 1)) (cf-window ts (- i 1) (- r 1)))))

(define (cf-dot a b)
  (if (null? a) 0 (+ (* (car a) (car b)) (cf-dot (cdr a) (cdr b)))))

; ---------- полиномы от x (списки коэффициентов, младшая степень первой) ----------

(define (cfp-trim p)
  (cond ((null? p) '())
        ((= (car (reverse p)) 0) (cfp-trim (butlast p)))
        (else p)))

(define (cfp-deg p) (- (length (cfp-trim p)) 1))

(define (cfp-add a b)
  (cond ((null? a) b) ((null? b) a)
        (else (cons (+ (car a) (car b)) (cfp-add (cdr a) (cdr b))))))

(define (cfp-neg a) (map (lambda (x) (- x)) a))
(define (cfp-sub a b) (cfp-add a (cfp-neg b)))
(define (cfp-scale a q) (map (lambda (x) (* q x)) a))

(define (cfp-shift-left p k)
  (if (= k 0) p (cons 0 (cfp-shift-left p (- k 1)))))

(define (cfp-mul-step a i b j v)
  (if (>= j (length b))
      #t
      (begin
        (vset! v (+ i j) (+ (vref v (+ i j)) (* (nth a i) (nth b j))))
        (cfp-mul-step a i b (+ j 1) v))))
(define (cfp-mul-outer a b i v)
  (if (>= i (length a))
      #t
      (begin (cfp-mul-step a i b 0 v) (cfp-mul-outer a b (+ i 1) v))))
(define (cfp-mul a b)
  (if (or (null? a) (null? b))
      '()
      (let* ((n (+ (length a) (length b) -1))
             (v (make-vector n 0)))
        (begin (cfp-mul-outer a b 0 v)
               (cfp-trim (map (lambda (i) (vref v i)) (range n)))))))

; остаток p по χ (χ приведённый, старший коэффициент 1)
(define (cfp-mod p chi)
  (let ((dp (cfp-deg p)) (dc (cfp-deg chi)))
    (if (or (< dp 0) (< dp dc))
        (cfp-trim p)
        (let* ((lead (nth p dp))
               (sub (cfp-shift-left (cfp-scale chi lead) (- dp dc))))
          (cfp-mod (cfp-sub p sub) chi)))))

; (cf-char-poly c) — χ(x) = x^r − c1·x^{r−1} − … − cr, коэффициенты младшая первой
(define (cf-char-poly c)
  (append (map (lambda (x) (- x)) (reverse c)) (list 1)))

; ---------- члены ----------

(define (cfp-pow-mod base n chi)
  (if (= n 0)
      '(1)
      (let* ((h (cfp-pow-mod base (quotient n 2) chi))
             (sq (cfp-mod (cfp-mul h h) chi)))
        (if (= (* 2 (quotient n 2)) n)
            sq
            (cfp-mod (cfp-mul sq base) chi)))))

; (cf-term s n) — n-е значение за O(r^2 log n)
(define (cf-term s n)
  (if (< n 0) (error "cf-term: отрицательный индекс" n))
  (let* ((init (cf-init s))
         (r (length init))
         (chi (cf-char-poly (cf-coeffs s)))
         (d (cfp-pow-mod (list 0 1) n chi)))
    (cf-dot (cf-take-pad d r) init)))

(define (cf-take-pad p k)
  (cond ((= k 0) '())
        ((null? p) (cons 0 (cf-take-pad '() (- k 1))))
        (else (cons (car p) (cf-take-pad (cdr p) (- k 1))))))

; (cf-terms s k) — первые k членов
(define (cf-extend c ts k)
  (if (>= (length ts) k)
      (take ts k)
      (let ((v (cf-dot c (cf-window ts (length ts) (length c)))))
        (cf-extend c (append ts (list v)) k))))
(define (cf-terms s k)
  (cf-extend (cf-coeffs s) (cf-init s) k))

; (cf-shift s j) — b(n) = a(n+j)
(define (cf-shift s j)
  (let* ((c (cf-coeffs s)) (r (length c)))
    (cond ((>= j 0)
           (cfinite c (drop (cf-terms s (+ j r)) j)))
          ((= (last c) 0)
           (error "cf-shift: обратный сдвиг невозможен (cr = 0)" j))
          (else
           (cfinite c (take (cf-shift-back c (cf-init s) j) r))))))

; обратный сдвиг: a(n−1) = (a(n+r−1) − c1·a(n+r−2) − … − c_{r−1}·a(n)) / cr
(define (cf-prev c ts)
  (let* ((r (length c)) (cr (last c))
         (rest (butlast c))
         (win (take ts r)))
    (/ (- (last win) (cf-dot rest (reverse (butlast win)))) cr)))

(define (cf-shift-back c ts j)
  (if (= j 0)
      ts
      (cf-shift-back c (cons (cf-prev c ts) ts) (+ j 1))))

; ---------- Берлекэмп–Мэсси (точные дроби) ----------

; C, B — полиномы (младшая первой), C[0] = 1
(define (cf-bm-discrepancy s n C L)
  (cf-bm-disc-step s n C L 0 0))

(define (cf-bm-disc-step s n C L i acc)
  (if (> i L)
      acc
      (cf-bm-disc-step s n C L (+ i 1) (+ acc (* (nth C i) (nth s (- n i)))))))

(define (cf-bm-loop s n C B L m b)
  (if (>= n (length s))
      (list C L)
      (let ((d (cf-bm-disc-step s n C L 0 0)))
        (if (= d 0)
            (cf-bm-loop s (+ n 1) C B L (+ m 1) b)
            (let* ((coef (/ d b))
                   (C1 (cfp-sub C (cfp-shift-left (cfp-scale B coef) m))))
              (if (>= (* 2 L) (+ n 1))
                  (cf-bm-loop s (+ n 1) C1 B L (+ m 1) b)
                  (cf-bm-loop s (+ n 1) C1 C (+ (- (+ n 1) L) 0) 1 d)))))))

; (cf-from-terms список) — кратчайшая рекуррентность, порождающая список (гипотеза;
; проверяется на всех данных членах). Пустой/короткий список — ошибка.
(define (cf-from-terms ts)
  (if (< (length ts) 2)
      (if (null? ts)
          (error "cf-from-terms: пустой список")
          (cfinite (list 1) (list (car ts))))
      (let* ((r (cf-bm-loop ts 0 '(1) '(1) 0 1 1))
             (C (car r)) (L (cadr r)))
        (if (= L 0)
            (cfinite (list 1) (list (car ts)))
            (let* ((coeffs (map (lambda (i) (- (nth C (+ i 1)))) (range L)))
                   (s (cfinite coeffs (take ts L))))
              (if (cf-check s)
                  s
                  (error "cf-from-terms: рекуррентность не подтверждается членами")))))))

; ---------- операции ----------

; (cf+ a b) — сумма; порядок ≤ r+s
(define (cf+ a b)
  (let* ((R (+ (cf-order a) (cf-order b)))
         (ts (map (lambda (i) (+ (cf-term a i) (cf-term b i)))
                  (range (* 2 R)))))
    (cf-from-terms ts)))

; (cf* a b) — произведение; порядок ≤ r·s
(define (cf* a b)
  (let* ((R (* (cf-order a) (cf-order b)))
         (ts (map (lambda (i) (* (cf-term a i) (cf-term b i)))
                  (range (* 2 R)))))
    (cf-from-terms ts)))

; (cf-scale s q) — умножение на константу
(define (cf-scale s q)
  (cfinite (cf-coeffs s) (map (lambda (x) (* q x)) (cf-init s))))

; (cf-partial-sum s) — S(n) = Σ_{k=0}^n a(k); порядок ≤ r+1
(define (cf-partial-sum s)
  (let* ((R (+ (cf-order s) 1))
         (ts (cf-partial-terms s (* 2 R) 0 '())))
    (cf-from-terms ts)))

(define (cf-partial-terms s k i acc)
  (if (= i k)
      (reverse acc)
      (let ((v (+ (if (null? acc) 0 (car acc)) (cf-term s i))))
        (cf-partial-terms s k (+ i 1) (cons v acc)))))

; ---------- модулярные значения ----------

; (cf-term-mod s n m) — n-е значение по модулю m (целые коэффициенты)
(define (cfm-mod x m) (modulo x m))

(define (cfm-dot a b m)
  (if (null? a) 0 (cfm-mod (+ (cfm-mod (* (car a) (car b)) m)
                              (cfm-dot (cdr a) (cdr b) m)) m)))

(define (cfm-add a b m)
  (cond ((null? a) b) ((null? b) a)
        (else (cons (cfm-mod (+ (car a) (car b)) m) (cfm-add (cdr a) (cdr b) m)))))

(define (cfm-sub a b m) (cfm-add a (map (lambda (x) (cfm-mod (- x) m)) b) m))

(define (cfm-scale a q m) (map (lambda (x) (cfm-mod (* q x) m)) a))

(define (cfm-shift-left p k) (if (= k 0) p (cons 0 (cfm-shift-left p (- k 1)))))

(define (cfm-trim p)
  (cond ((null? p) '())
        ((= (last p) 0) (cfm-trim (butlast p)))
        (else p)))

(define (cfm-mul-step a i b j v m)
  (if (>= j (length b)) #t
      (begin (vset! v (+ i j) (cfm-mod (+ (vref v (+ i j)) (* (nth a i) (nth b j))) m))
             (cfm-mul-step a i b (+ j 1) v m))))
(define (cfm-mul-outer a b i v m)
  (if (>= i (length a)) #t
      (begin (cfm-mul-step a i b 0 v m) (cfm-mul-outer a b (+ i 1) v m))))
(define (cfm-mul a b m)
  (if (or (null? a) (null? b)) '()
      (let* ((n (+ (length a) (length b) -1)) (v (make-vector n 0)))
        (begin (cfm-mul-outer a b 0 v m)
               (cfm-trim (map (lambda (i) (vref v i)) (range n)))))))

(define (cfm-mod-poly p chi m)
  (let* ((pt (cfm-trim p)) (dp (- (length pt) 1)) (dc (- (length (cfm-trim chi)) 1)))
    (if (or (< dp 0) (< dp dc))
        pt
        (let* ((lead (last pt))
               (sub (cfm-shift-left (cfm-scale chi lead m) (- dp dc))))
          (cfm-mod-poly (cfm-sub p sub m) chi m)))))

(define (cfm-pow-mod base n chi m)
  (if (= n 0) '(1)
      (let* ((h (cfm-pow-mod base (quotient n 2) chi m))
             (sq (cfm-mod-poly (cfm-mul h h m) chi m)))
        (if (= (* 2 (quotient n 2)) n)
            sq
            (cfm-mod-poly (cfm-mul sq base m) chi m)))))

(define (cf-term-mod s n m)
  (if (< n 0) (error "cf-term-mod: отрицательный индекс" n))
  (let* ((init (map (lambda (x) (modulo x m)) (cf-init s)))
         (r (length init))
         (chi (map (lambda (x) (modulo x m)) (cf-char-poly (map (lambda (x) (modulo x m)) (cf-coeffs s)))))
         (d (cfm-pow-mod (list 0 1) n chi m)))
    (cfm-dot (cf-take-pad d r) init m)))

; ================= RE.2: выражения от n и доказательство тождеств =================

; целая степень точного числа
(define (cf-pow q k)
  (if (= k 0) 1 (/ (^ (numer q) k) (^ (denom q) k))))

; (cf-arg-index arg n) → (c . d): индекс = c·n + d (c — целое >= 0), или #f
(define (cf-arg-index arg n)
  (cond ((equal? arg n) (cons 1 0))
        ((number? arg) (cons 0 arg))
        ((pair? arg)
         (let ((h (car arg)))
           (cond ((equal? h '+)
                  (let ((a (cf-arg-index (cadr arg) n)) (b (cf-arg-index (caddr arg) n)))
                    (if (and a b) (cons (+ (car a) (car b)) (+ (cdr a) (cdr b))) #f)))
                 ((equal? h '-)
                  (let ((a (cf-arg-index (cadr arg) n)) (b (cf-arg-index (caddr arg) n)))
                    (if (and a b) (cons (- (car a) (car b)) (- (cdr a) (cdr b))) #f)))
                 ((equal? h '*)
                  (let ((a (cf-arg-index (cadr arg) n)) (b (cf-arg-index (caddr arg) n)))
                    (cond ((and a b (= (car a) 0)) (cons (* (car b) (cdr a)) (* (cdr b) (cdr a))))
                          ((and a b (= (car b) 0)) (cons (* (car a) (cdr b)) (* (cdr a) (cdr b))))
                          (else #f))))
                 (else #f))))
        (else #f)))

; (cf-subseq s c d) — b(n) = a(c·n + d), c >= 1; порядок <= порядка a
; (корни χ возводятся в степень c — кратности сохраняются, теорема о 2r членах)
(define (cf-subseq s c d)
  (cond ((= c 0) (cfinite '(1) (list (cf-term s d))))
        ((< d 0) (cf-subseq (cf-shift s d) c 0))
        (else
         (let* ((r (cf-order s))
                (ts (map (lambda (i) (cf-term s (+ (* c i) d))) (range (* 2 r)))))
           (cf-from-terms ts)))))

(define cf-fib-seq (cfinite '(1 1) '(0 1)))
(define cf-luc-seq (cfinite '(1 1) '(2 1)))

; атом fib/lucas с аргументом c·n + d
(define (cf-atom seq arg n)
  (let ((p (cf-arg-index arg n)))
    (cond ((not p) #f)
          ((= (car p) 1) (cf-shift seq (cdr p)))
          ((= (car p) 0) (if (>= (cdr p) 0) (cfinite '(1) (list (cf-term seq (cdr p)))) #f))
          (else (cf-subseq seq (car p) (cdr p))))))

(define (cf-map-exprs es n)
  (if (null? es)
      '()
      (let ((x (cf-of-expr (car es) n)))
        (if (not x)
            #f
            (let ((rest (cf-map-exprs (cdr es) n)))
              (if (equal? rest #f) #f (cons x rest)))))))

(define (cf-fold-add cs)
  (if (null? cs) (cfinite '(1) '(0)) (foldl cf+ (car cs) (cdr cs))))
(define (cf-fold-mul cs)
  (if (null? cs) (cfinite '(1) '(1)) (foldl cf* (car cs) (cdr cs))))

(define (cf-pow-seq s k)
  (if (= k 1) s (cf* s (cf-pow-seq s (- k 1)))))

; (^ c n), (^ c (+ n k)), (^ выражение k) для целого k
(define (cf-expr-pow e n)
  (let ((base (cadr e)) (ex (caddr e)))
    (cond ((and (number? base) (cf-arg-index ex n))
           (let* ((p (cf-arg-index ex n)) (c (car p)) (d (cdr p)))
             (cond ((< c 0) #f)
                   ((= c 0) (cfinite '(1) (list (cf-pow base d))))
                   (else (cfinite (list (cf-pow base c)) (list (cf-pow base d)))))))
          ((and (integer? ex) (> ex 0))
           (let ((b (cf-of-expr base n)))
             (if b (cf-pow-seq b ex) #f)))
          (else #f))))

; (sum выражение k a n) — частичная сумма от a до n (a >= 0)
(define (cf-expr-sum e n)
  (let* ((body (cadr e)) (k (caddr e)) (a (nth e 3)) (hi (nth e 4)))
    (if (and (equal? hi n) (number? a) (integer? a) (>= a 0))
        (let ((base (cf-of-expr body k)))
          (if (not base)
              #f
              (let ((ps (cf-partial-sum base)))
                (if (= a 0)
                    ps
                    (cf+ ps (cfinite '(1) (list (- (cf-term ps (- a 1))))))))))
        #f)))

; (cf-of-expr e n) — C-конечная форма выражения от n; #f, если не C-конечное
(define (cf-of-expr e n)
  (cond ((number? e) (cfinite '(1) (list e)))
        ((symbol? e) (if (equal? e n) (cfinite '(2 -1) '(0 1)) #f))
        ((pair? e)
         (let ((h (car e)) (args (cdr e)))
           (cond ((equal? h '+)
                  (let ((cs (cf-map-exprs args n))) (if cs (cf-fold-add cs) #f)))
                 ((equal? h '*)
                  (let ((cs (cf-map-exprs args n))) (if cs (cf-fold-mul cs) #f)))
                 ((equal? h '-)
                  (if (< (length args) 2)
                      #f
                      (let ((a (cf-of-expr (car args) n)) (b (cf-of-expr (cadr args) n)))
                        (if (and a b) (cf+ a (cf-scale b -1)) #f))))
                 ((equal? h '^) (cf-expr-pow e n))
                 ((equal? h 'fib) (cf-atom cf-fib-seq (cadr e) n))
                 ((equal? h 'lucas) (cf-atom cf-luc-seq (cadr e) n))
                 ((equal? h 'sum) (cf-expr-sum e n))
                 (else #f))))
        (else #f)))

(define (cf-first-nonzero s k i)
  (if (>= i k)
      #f
      (if (= (cf-term s i) 0) (cf-first-nonzero s k (+ i 1)) i)))

; (cf-prove lhs rhs) — (proved R) или (disproved n0 lhs(n0) rhs(n0)).
; Разность — C-конечная последовательность порядка R; R нулей подряд достаточно.
(define (cf-prove lhs rhs)
  (let ((L (cf-of-expr lhs 'n)) (R (cf-of-expr rhs 'n)))
    (if (or (not L) (not R))
        (error "cf-prove: выражение не C-конечное" (if L rhs lhs))
        (let* ((D (cf+ L (cf-scale R -1)))
               (k (cf-order D))
               (bad (cf-first-nonzero D k 0)))
          (if (equal? bad #f)
              (list 'proved k)
              (list 'disproved bad (cf-term L bad) (cf-term R bad)))))))

; (cf-check-proof lhs rhs proof) — пересчёт членов; занижённое R отвергается
(define (cf-check-proof lhs rhs proof)
  (let ((L (cf-of-expr lhs 'n)) (R (cf-of-expr rhs 'n)))
    (if (or (not L) (not R) (not (pair? proof)))
        #f
        (let* ((D (cf+ L (cf-scale R -1)))
               (k (cf-order D)))
          (cond ((equal? (car proof) 'proved)
                 (let ((rq (cadr proof)))
                   (and (integer? rq) (>= rq k) (equal? (cf-first-nonzero D rq 0) #f))))
                ((equal? (car proof) 'disproved)
                 (let ((i (cadr proof)))
                   (and (integer? i) (>= i 0)
                        (equal? (nth proof 2) (cf-term L i))
                        (equal? (nth proof 3) (cf-term R i))
                        (not (equal? (cf-term L i) (cf-term R i))))))
                (else #f))))))

; ================= RE.3: производящие функции и замкнутая форма =================

(define (cf-range a b)
  (if (>= a b) '() (cons a (cf-range (+ a 1) b))))

; (cf->gf s x) — (P Q), коэффициенты младшая первой:
; Q(x) = 1 − c1·x − … − cr·x^r, P = (A·Q) mod x^r, A = a0 + a1·x + …
(define (cf->gf s x)
  (let* ((c (cf-coeffs s)) (init (cf-init s)) (r (length c))
         (Q (cons 1 (map (lambda (ci) (- ci)) c)))
         (P (take (cfp-mul init Q) r)))
    (list (cfp-trim P) (cfp-trim Q))))

; (gf->cf P Q) — обратно: Q = 1 + q1 x + … + qd x^d → a(n) = −(q1 a(n−1)+…+qd a(n−d))/q0
(define (gf-series-sum Q acc n i s)
  (if (or (> i n) (>= i (length Q)))
      s
      (gf-series-sum Q acc n (+ i 1) (+ s (* (nth Q i) (nth acc (- i 1)))))))

(define (gf-series-step P Q d n acc)
  (if (= n d)
      (reverse acc)
      (let* ((pn (if (< n (length P)) (nth P n) 0))
             (s (gf-series-sum Q acc n 1 0))
             (a (/ (- pn s) (car Q))))
        (gf-series-step P Q d (+ n 1) (cons a acc)))))

(define (gf->cf P Q)
  (let* ((Qt (cfp-trim Q)) (d (- (length Qt) 1)) (q0 (car Qt)))
    (if (or (<= d 0) (= q0 0))
        (error "gf->cf: Q должен быть ненулевым многочленом с q0 ≠ 0" Q)
        (let* ((coeffs (map (lambda (j) (/ (- (nth Qt j)) q0)) (cf-range 1 (+ d 1))))
               (init (gf-series-step (cfp-trim P) Qt d 0 '()))
               (s (cfinite coeffs init)))
          (if (cf-check s)
              s
              (error "gf->cf: ряд P/Q не удовлетворяет рекуррентности"))))))

; (cf-closed-form s n) — формула через корни χ (r = 1, 2; иначе #f)
(define (cf-closed-form s n)
  (let ((c (cf-coeffs s)) (a (cf-init s)))
    (cond ((= (length c) 1) (* (car a) (list '^ (car c) n)))
          ((= (length c) 2)
           (let* ((c1 (car c)) (c2 (cadr c)) (a0 (car a)) (a1 (cadr a))
                  (D (+ (* c1 c1) (* 4 c2))))
             (if (= D 0)
                 (let ((l (/ c1 2)))
                   (if (= l 0)
                       (if (and (= a0 0) (= a1 0)) 0 #f)
                       (let ((C2 (- (/ a1 l) a0)))
                         (simplify (list '* (list '+ a0 (list '* C2 n))
                                         (list '^ l n))))))
                 (let* ((sq (list 'sqrt D))
                        (l1 (/ (+ c1 sq) 2)) (l2 (/ (- c1 sq) 2))
                        (den (- l1 l2))
                        (C1 (/ (- a1 (* a0 l2)) den))
                        (C2 (/ (- (* a0 l1) a1) den)))
                   (simplify (list '+ (list '* C1 (list '^ l1 n))
                                   (list '* C2 (list '^ l2 n))))))))
          (else #f))))