; divisor.lisp — Шаг A5.1: места, ряды и вычеты гиперэллиптической кривой y² = P(x).
;
; Место — (a b): a ∈ ℚ или inf; b — значение y в точке (элемент ib-k, знак учтён)
; либо ram — точка ветвления.  Дивизор — список ((место . n) …), n ≠ 0.
; Ряд — ib-ser: список (порядок . элемент ib-k); усечение — по максимальному порядку.
;
; Вычет res_P(H dx) = [t^{−1}] H(x(t), y(t))·x′(t).  x(t) конечен (Лоран), числитель
; и знаменатель — конечные ряды Лорана, поэтому коэффициент вычисляется точно:
; обратный ряд берётся ровно до нужного порядка, без «усечения наугад».

(module integrate
  (export hyp-places hyp-place-series hyp-valuation hyp-residue hyp-residues
          hyp-residue-poly hyp-residues-check residue-divisors
          hyp-riemann-roch hyp-principal hyp-principal-check
          hyp-good-prime? hyp-count-points hyp-jacobian-order
          ec-divisor-sum ec-multiples ec-point-order-check
          hyp-torsion-bound hyp-torsion-order hyp-log-part hyp-log-check hyp-logs->expr
          hyp-holomorphic? hyp-second-kind?
          gv-places gv-place-series gv-valuation gv-residue gv-residues
          gv-residues-check gv-residue-poly gv-holomorphic?
          gv-l-basis gv-riemann-roch gv-principal gv-principal-check
          gv-good-prime? gv-count-points gv-jacobian-order gv-torsion-bound
          gv-torsion-order gv-log-part gv-log-check gv-logs->expr
          gv-add gv-scale gv-degree gv-normalize
          dv-sqrt-series dv-add dv-scale dv-degree dv-normalize
          dv-place-eq? dv-k-eq? dv-rat-res? dv-k->rat))

; ---------- элементы ℚ(√d₁, √d₂, …) ----------

(define (dv-k-rat c) (if (= c 0) '() (list (cons '() c))))
(define (dv-k-zero? k) (null? k))
(define (dv-k-eq? a b) (null? (ib-k-add a (ib-k-scale b -1))))
(define (dv-k-neg a) (ib-k-scale a -1))
(define (dv-k-one) (ib-k-one))

(define (dv-inter a b)
  (cond ((null? a) '())
        ((ib-member? (car a) b) (cons (car a) (dv-inter (cdr a) b)))
        (else (dv-inter (cdr a) b))))

(define (dv-subsets ds)
  (if (null? ds)
      (list '())
      (let ((rest (dv-subsets (cdr ds))))
        (append rest (map (lambda (s) (cons (car ds) s)) rest)))))

; сопряжение: меняем знак у √d для d из g
(define (dv-k-conj e g)
  (map (lambda (t)
         (let ((f (car t)))
           (cons f (if (= 1 (remainder (length (dv-inter f g)) 2)) (- (cdr t)) (cdr t)))))
       e))

; обратный элемент в ℚ(√d₁, …): норма по всем сопряжениям (мультипликативна)
(define (dv-k-inv k)
  (cond ((null? k) #f)
        ((and (pair? k) (null? (cdr k))) (ib-k-inv k))
        (else
         (let* ((ds (ib-unique (foldl (lambda (acc t) (append (car t) acc)) '() k)))
                (gs (filter (lambda (g) (pair? g)) (dv-subsets ds)))
                (num (foldl (lambda (acc g) (ib-k-mul acc (dv-k-conj k g))) (ib-k-one) gs))
                (norm (ib-k-mul k num)))
           (if (and (pair? norm) (null? (cdr norm)) (null? (car (car norm))))
               (ib-k-scale num (/ 1 (cdr (car norm))))
               #f)))))

; рациональное значение элемента (пустой ключ) или #f
(define (dv-k->rat k)
  (if (null? k) 0 (if (null? (cdr k)) (if (null? (car (car k))) (cdr (car k)) #f) #f)))
(define (dv-rat-res? r) (not (equal? (dv-k->rat r) #f)))

; элемент ℚ(√d) → выражение (для коэффициентов логарифмов)
(define (dv-k->expr k)
  (let ((ts (filter (lambda (t) (not (= (cdr t) 0))) k)))
    (if (null? ts)
        0
        (simplify
         (cons '+ (map (lambda (t)
                         (let ((f (car t)) (c (cdr t)))
                           (if (null? f)
                               c
                               (list '* c (simplify (cons '* (map (lambda (d) (list '^ d 1/2)) f)))))))
                       ts))))))

; ---------- ряды Лорана с коэффициентами в ℚ(√d) ----------

(define (dv-ser-clean s)
  (sort (filter (lambda (t) (not (dv-k-zero? (cdr t)))) s)
        (lambda (a b) (< (car a) (car b)))))

(define (dv-ser-ref s o)
  (let ((p (ib-assoc o s))) (if p (cdr p) '())))

(define (dv-ser-min s)
  (let ((s (dv-ser-clean s))) (if (null? s) #f (car (car s)))))

(define (dv-ser-null? s) (null? (dv-ser-clean s)))

(define (dv-ser-add a b)
  (dv-ser-clean (foldl (lambda (acc t) (ib-ser-add-term acc (car t) (cdr t))) a b)))

(define (dv-ser-scale s k)
  (let ((k (if (number? k) (dv-k-rat k) k)))
    (if (dv-k-zero? k)
        '()
        (dv-ser-clean (map (lambda (t) (cons (car t) (ib-k-mul (cdr t) k))) s)))))

(define (dv-ser-neg s) (dv-ser-scale s (dv-k-rat -1)))
(define (dv-ser-sub a b) (dv-ser-add a (dv-ser-neg b)))

; константа как ряд
(define (dv-ser-const k)
  (if (dv-k-zero? k) '() (list (cons 0 k))))

(define (dv-ser-mul a b M) (dv-ser-clean (ib-ser-mul a b M)))
(define (dv-ser-shift s k) (map (lambda (t) (cons (+ (car t) k) (cdr t))) s))

(define (dv-ser-trunc s M) (filter (lambda (t) (<= (car t) M)) s))

; обратный степенной ряд (свободный член при порядке 0 равен 1), до порядка J
(define (dv-ser-inv1 u J)
  (let loop ((r (list (cons 0 (ib-k-one)))) (steps 0))
    (if (or (>= steps 7) (< J 0))
        (dv-ser-trunc (dv-ser-clean r) J)
        (let* ((ru (dv-ser-mul r u J))
               (e (dv-ser-sub ru (list (cons 0 (ib-k-one)))))
               (r2 (dv-ser-mul r (dv-ser-sub (list (cons 0 (ib-k-one))) e) J)))
          (loop r2 (+ steps 1))))))

(define (dv-ser-inv s J)
  (let* ((c0 (dv-ser-ref s 0))
         (ic (dv-k-inv c0))
         (u (dv-ser-scale s ic)))
    (dv-ser-scale (dv-ser-inv1 u J) ic)))

; коэффициент при t^{−1} отношения n/d (d ≠ 0) — точно
(define (dv-lser-residue n d)
  (let* ((n (dv-ser-clean n)) (d (dv-ser-clean d)))
    (cond ((null? d) 'unknown)
          ((null? n) '())
          (else
           (let* ((vn (car (car n)))
                  (vd (car (car d)))
                  (target (- vd 1)))
             (if (< target vn)
                 '()
                 (let* ((d0 (dv-ser-shift d (- vd)))
                        (c0 (dv-ser-ref d0 0))
                        (ic (dv-k-inv c0))
                        (d1 (dv-ser-scale d0 ic))
                        (inv (dv-ser-inv1 d1 (- target vn)))
                        (prod (dv-ser-mul n inv target)))
                   (ib-k-mul (dv-ser-ref prod target) ic))))))))

; ---------- многочлены от x (ib-p) и ряды ----------

(define (dv-pow a m) (if (= m 0) 1 (* a (dv-pow a (- m 1)))))

(define (dv-binom j k)
  (let loop ((i 0) (acc 1))
    (if (= i k) acc (loop (+ i 1) (/ (* acc (- j i)) (+ i 1))))))

; коэффициенты p(x + a) по возрастанию степени
(define (dv-p-shift p a)
  (let ((p (ib-p-trim p)))
    (if (null? p)
        '()
        (let ((d (- (length p) 1)))
          (let loop ((k 0) (acc '()))
            (if (> k d)
                (ib-p-trim (reverse acc))
                (loop (+ k 1)
                      (cons (let sum ((j k) (s 0))
                              (if (> j d)
                                  s
                                  (sum (+ j 1)
                                       (+ s (* (nth p j) (dv-binom j k) (dv-pow a (- j k)))))))
                            acc))))))))

(define (dv-p-eval p a)
  (let loop ((ps (reverse (ib-p-trim p))) (acc 0))
    (if (null? ps) acc (loop (cdr ps) (+ (* acc a) (car ps))))))

(define (dv-p-deriv p)
  (let ((p (ib-p-trim p)))
    (if (null? p)
        '()
        (ib-p-trim (map (lambda (k) (* (+ k 1) (nth p (+ k 1))))
                        (range (- (length p) 1)))))))

; многочлен → ряд (коэффициент при s^k)
(define (dv-ser-poly p)
  (dv-ser-clean (map (lambda (k) (cons k (dv-k-rat (nth p k)))) (range (length p)))))

; то же при подстановке s = t²
(define (dv-ser-poly-sq p)
  (dv-ser-clean (map (lambda (k) (cons (* 2 k) (dv-k-rat (nth p k)))) (range (length p)))))

; значение многочлена от x в ряду x(t)
(define (dv-ser-peval p s M)
  (let ((p (ib-p-trim p)))
    (if (null? p)
        '()
        (let loop ((k (- (length p) 1)) (acc '()))
          (if (< k 0)
              (dv-ser-trunc (dv-ser-clean acc) M)
              (loop (- k 1)
                    (dv-ser-add (dv-ser-mul acc s M)
                                (dv-ser-const (dv-k-rat (nth p k))))))))))

; x′(t) для конечного ряда x(t)
(define (dv-ser-deriv s)
  (dv-ser-clean (map (lambda (t) (cons (- (car t) 1) (ib-k-scale (cdr t) (car t)))) s)))

; √(1 + u): биномиальный ряд до порядка N (u(0) = 0)
(define (dv-sqrt-series u N)
  (if (< N 0)
      (list (cons 0 (ib-k-one)))
      (let loop ((k 1) (up (dv-ser-trunc u N)) (acc (list (cons 0 (ib-k-one)))) (c 1/2))
        (if (> k N)
            (dv-ser-trunc (dv-ser-clean acc) N)
            (loop (+ k 1)
                  (dv-ser-mul up u N)
                  (dv-ser-add acc (dv-ser-scale up c))
                  (* c (/ (- 1/2 k) (+ k 1))))))))

; ---------- места ----------

(define (hyp-places P x a)
  (let ((p (ib-poly-parse P x)))
    (if (equal? p #f)
        'unknown
        (if (equal? a 'inf)
            (let ((n (ib-p-deg p)) (lc (ib-p-lc p)))
              (let ((b (ib-k-sqrt-rat lc)))
                (if (equal? b #f)
                    'unknown
                    (if (even? n)
                        (list (list 'inf b) (list 'inf (dv-k-neg b)))
                        (list (list 'inf 'ram))))))
            (if (not (ib-rat? a))
                'unknown
                (let ((pa (dv-p-eval p a)))
                  (cond ((= pa 0)
                         (let ((pp (dv-p-eval (dv-p-deriv p) a)))
                           (if (= pp 0) 'unknown (list (list a 'ram)))))
                        (else
                         (let ((b (ib-k-sqrt-rat pa)))
                           (if (equal? b #f)
                               'unknown
                               (list (list a b) (list a (dv-k-neg b)))))))))))))

(define (dv-smooth-series a b p N)
  (let* ((ps (dv-p-shift p a))
         (pa (dv-p-eval p a))
         (u (dv-ser-poly (ib-p-scale (ib-p-trim (cons 0 (cdr ps))) (/ 1 pa))))
         (s (dv-sqrt-series u (if (>= N 0) N 0)))
         (ys (dv-ser-scale s b)))
    (cons (list (cons 0 (dv-k-rat a)) (cons 1 (ib-k-one)))
          (dv-ser-trunc ys N))))

(define (dv-branch-series a p N)
  (let* ((ps (dv-p-shift p a))
         (q1 (ib-p-trim (cdr ps)))
         (pa (dv-p-eval (dv-p-deriv p) a))
         (q1sq (dv-ser-poly-sq q1))
         (w (dv-ser-scale (dv-ser-sub q1sq (dv-ser-const (dv-k-rat pa))) (/ 1 pa)))
         (s (dv-sqrt-series w (if (>= (- N 1) 0) (- N 1) 0)))
         (bb (ib-k-sqrt-rat pa))
         (ys (dv-ser-shift (dv-ser-scale s bb) 1)))
    (cons (list (cons 0 (dv-k-rat a)) (cons 2 (ib-k-one)))
          (dv-ser-trunc ys N))))

(define (dv-inf-series b p N)
  (let* ((n (ib-p-deg p))
         (lc (ib-p-lc p))
         (ev (even? n))
         (rev (reverse p))
         (q (dv-ser-scale (if ev (dv-ser-poly rev) (dv-ser-poly-sq rev)) (/ 1 lc)))
         (sh (if ev (quotient n 2) n))
         (M (if (>= (+ N sh) 0) (+ N sh) 0))
         (s (dv-sqrt-series (dv-ser-sub q (list (cons 0 (ib-k-one)))) M))
         (bb (if (equal? b 'ram) (ib-k-sqrt-rat lc) b))
         (ys (dv-ser-shift (dv-ser-scale s bb) (- sh)))
         (xs (if ev (list (cons -1 (ib-k-one))) (list (cons -2 (ib-k-one))))))
    (cons xs (dv-ser-trunc ys N))))

(define (hyp-place-series pl P x N)
  (let* ((a (car pl)) (b (cadr pl))
         (p (ib-poly-parse P x)))
    (cond ((equal? p #f) 'unknown)
          ((equal? a 'inf) (dv-inf-series b p N))
          ((not (ib-rat? a)) 'unknown)
          ((equal? b 'ram) (dv-branch-series a p N))
          ((not (list? b)) 'unknown)
          (else (dv-smooth-series a b p N)))))

; ---------- нормирование ----------

; v_P(f) для f = (c₀ + c₁y)/g: порядок усечения растёт, пока ведущий член не найден
; v_P(f) произвольного выражения от x, y — через подстановку ряда (см. dv-valuation-series)
(define (hyp-valuation pl f P x)
  (if (equal? (dv-place-ok? pl P x) #t)
      (dv-valuation-series pl f P x)
      'unknown))

; ---------- Шаг A5.3b: место должно лежать на кривой ----------
; Гладкое конечное место: b² = P(a); ветвление (ram): P(a) = 0 и корень простой;
; ∞: чётная степень — b² = lc(P), нечётная — только ram.
(define (dv-place-ok? pl P x)
  (if (not (and (list? pl) (= 2 (length pl))))
      'unknown
      (let ((a (car pl)) (b (cadr pl)) (p (ib-poly-parse P x)))
        (if (equal? p #f)
            'unknown
            (if (equal? a 'inf)
                (let ((n (ib-p-deg p)) (lc (ib-p-lc p)))
                  (cond ((even? n)
                         (let ((bs (ib-k-sqrt-rat lc)))
                           (and (not (equal? bs #f)) (not (equal? b 'ram))
                                (or (dv-k-eq? (if (number? b) (dv-k-rat b) b) bs)
                                    (dv-k-eq? (if (number? b) (dv-k-rat b) b) (dv-k-neg bs))))))
                        (else (equal? b 'ram))))
                (if (not (ib-rat? a))
                    'unknown
                    (let ((pa (dv-p-eval p a)))
                      (cond ((= pa 0)
                             (if (= 0 (dv-p-eval (dv-p-deriv p) a))
                                 'unknown
                                 (equal? b 'ram)))
                            ((equal? b 'ram) #f)
                            ((not (or (number? b) (list? b))) #f)
                            (else
                             (let ((bk (if (number? b) (dv-k-rat b) b))
                                   (bs (ib-k-sqrt-rat pa)))
                               (and (not (equal? bs #f))
                                    (or (dv-k-eq? bk bs) (dv-k-eq? bk (dv-k-neg bs))))))))))))))

; #t — все места на кривой, #f — есть место не на кривой, unknown — не разобрать
(define (dv-divisor-ok? D P x)
  (if (not (list? D))
      'unknown
      (let loop ((ds D) (res #t))
        (cond ((equal? res #f) #f)
              ((null? ds) res)
              ((not (pair? (car ds))) 'unknown)
              (else
               (let ((r (try (dv-place-ok? (car (car ds)) P x) (lambda (e) 'unknown))))
                 (loop (cdr ds) (if (equal? r #t) res r))))))))


; ---------- нормальная форма H ----------

; (vec c₀ c₁ D D_expr) или unknown; vec — коэффициенты при y⁰, y¹
(define (dv-nf-info H P x)
  (let ((nf (try (alg-nf H P 2 x) (lambda (e) #f))))
    (if (or (equal? nf #f) (not (pair? nf)))
        'unknown
        (let* ((vec (car nf)) (D (cdr nf)))
          (if (not (equal? (length vec) 2))
              'unknown
              (let ((c0 (ib-poly-parse (nth vec 0) x))
                    (c1 (ib-poly-parse (nth vec 1) x))
                    (Dp (ib-poly-parse D x)))
                (if (or (equal? c0 #f) (equal? c1 #f) (equal? Dp #f))
                    'unknown
                    (list vec c0 c1 Dp D))))))))

(define (dv-nf-vec info) (car info))
(define (dv-nf-c0 info) (nth info 1))
(define (dv-nf-c1 info) (nth info 2))
(define (dv-nf-D info) (nth info 3))
(define (dv-nf-Dexpr info) (nth info 4))

; ---------- вычеты ----------

; вычет в одном месте; c₀, c₁, D — многочлены (ib-p)
(define (dv-residue-at pl c0 c1 Dp P x)
  (let* ((sers (hyp-place-series pl P x 0))
         (xs (car sers))
         (jac (dv-ser-deriv xs))
         (c0s (dv-ser-peval c0 xs 400))
         (c1s (dv-ser-peval c1 xs 400))
         (ds (dv-ser-peval Dp xs 400))
         (vd (dv-ser-min ds)))
    (if (equal? vd #f)
        'unknown
        (let* ((target (- vd 1))
               (vj (let ((m (dv-ser-min jac))) (if (equal? m #f) 0 m)))
               (m1 (if (dv-ser-null? c1s) 0 (dv-ser-min c1s)))
               (ny (if (>= (+ (- target vj m1) 1) 0) (+ (- target vj m1) 1) 0))
               (ys (cdr (hyp-place-series pl P x ny)))
               (num (dv-ser-mul (dv-ser-add c0s (dv-ser-mul c1s ys 400)) jac 400)))
          (dv-lser-residue num ds)))))

(define (dv-residue-of info pl P x)
  (dv-residue-at pl (dv-nf-c0 info) (dv-nf-c1 info) (dv-nf-D info) P x))

; места над рациональными корнями знаменателя (неприводимые степени ≥ 2 пропускаем:
; вычеты там нулевые, это подтверждает результант)
(define (dv-finite-places Dex P x)
  (let ((fs (try (factor-list Dex) (lambda (e) #f))))
    (if (or (equal? fs #f) (not (pair? fs)))
        'unknown
        (let loop ((gs (cdr fs)) (acc '()))
          (if (null? gs)
              (reverse acc)
              (let ((g (car (car gs))))
                (if (= (try (degree g x) (lambda (e) -1)) 1)
                    (let ((a (alg-linear-root g x)))
                      (if (equal? a 'unknown)
                          'unknown
                          (let ((pls (hyp-places P x a)))
                            (if (equal? pls 'unknown)
                                'unknown
                                (loop (cdr gs) (append (reverse pls) acc))))))
                    (loop (cdr gs) acc))))))))

(define (dv-residues-all info places P x)
  (let loop ((pls places) (acc '()))
    (if (null? pls)
        (reverse acc)
        (let ((r (dv-residue-of info (car pls) P x)))
          (if (equal? r 'unknown)
              'unknown
              (loop (cdr pls) (cons (cons (car pls) r) acc)))))))

(define (hyp-residue pl H P x)
  (let ((info (dv-nf-info H P x)))
    (if (equal? info 'unknown)
        'unknown
        (dv-residue-of info pl P x))))

(define (hyp-residues H P x)
  (let ((info (dv-nf-info H P x)))
    (if (equal? info 'unknown)
        'unknown
        (let ((fin (dv-finite-places (dv-nf-Dexpr info) P x))
              (inf (hyp-places P x 'inf)))
          (if (or (equal? fin 'unknown) (equal? inf 'unknown))
              'unknown
              (let ((all (dv-residues-all info (append fin inf) P x)))
                (if (equal? all 'unknown)
                    'unknown
                    (filter (lambda (pr) (not (dv-k-zero? (cdr pr)))) all))))))))

; ---------- результант Трагера ----------

(define (dv-squarefree? D x)
  (let ((prs (try (alg-sqfree-pairs D) (lambda (e) #f))))
    (if (or (equal? prs #f) (not (pair? prs)))
        #f
        (every? (lambda (pe) (= 1 (cadr pe))) prs))))

; примитивная часть по t: коэффициенты — многочлены от x
(define (dv-p-gcd-list ps)
  (foldl (lambda (acc p) (if (ib-p-zero? p) acc (car (ib-p-egcd acc p)))) '() ps))

(define (dv-p-lcm-denoms ps)
  (foldl (lambda (acc p) (foldl (lambda (a c) (dv-lcm2 a (denom (together c)))) acc p)) 1 ps))

(define (dv-lcm2 a b) (quotient (* a b) (gcd a b)))

(define (dv-p-integer-gcd ps)
  (foldl (lambda (acc p) (foldl (lambda (a c) (gcd a (if (integer? c) c 1))) acc p)) 0 ps))

; pp_t: делим на НОД коэффициентов, затем приводим к целым взаимно простым;
; знак — по старшему коэффициенту (R определён с точностью до рациональной константы,
; но для сравнения в тестах удобен фиксированный знак)
(define (dv-p-primitive-list ps)
  (let* ((g (dv-p-gcd-list ps))
         (qs (if (ib-p-zero? g) ps (map (lambda (p) (car (ib-p-divmod p g))) ps)))
         (l (dv-p-lcm-denoms qs))
         (rs (map (lambda (p) (ib-p-scale p l)) qs))
         (ig (dv-p-integer-gcd rs))
         (rs (if (= ig 0) rs (map (lambda (p) (ib-p-scale p (/ 1 ig))) rs)))
         (top (last (filter (lambda (p) (not (ib-p-zero? p))) rs))))
    (if (and (pair? top) (< (ib-p-lc top) 0)) (ib-p-neg-list rs) rs)))

(define (ib-p-neg-list ps) (map (lambda (p) (ib-p-scale p -1)) ps))

(define (dv-p-list->expr ps t)
  (simplify (cons '+ (map (lambda (k) (list '* (ib-poly->expr (nth ps k) 'x) (list '^ t k)))
                          (range (length ps))))))

(define (hyp-residue-poly H P x t)
  (let ((info (dv-nf-info H P x)))
    (if (equal? info 'unknown)
        'unknown
        (let ((Dex (dv-nf-Dexpr info)) (G (dv-p-list->expr-y (dv-nf-vec info))))
          (if (not (dv-squarefree? Dex x))
              'unknown
              (let* ((Dp (diff x Dex))
                     (r1 (try (expand (resultant (list '- G (list '* t Dp))
                                                 (list '- (list '^ 'y 2) P) 'y))
                              (lambda (e) #f))))
                (if (or (equal? r1 #f) (equal? r1 0))
                    'unknown
                    (let* ((d (try (degree r1 t) (lambda (e) -1)))
                           (cs (if (and (integer? d) (>= d 0))
                                   (map (lambda (k) (ib-poly-parse (coeff r1 t k) x)) (range (+ d 1)))
                                   #f)))
                      (if (or (equal? cs #f) (member? #f cs))
                          'unknown
                          (let* ((pp (dv-p-list->expr (dv-p-primitive-list cs) t))
                                 (R (try (expand (resultant pp Dex x)) (lambda (e) #f))))
                            (if (or (equal? R #f) (equal? R 0))
                                'unknown
                                (dv-positive-lead R t))))))))))))

; R → R с положительным старшим коэффициентом по t (R определён с точностью до ℚ*)
(define (dv-positive-lead R t)
  (let ((d (try (degree R t) (lambda (e) -1))))
    (if (and (integer? d) (>= d 0))
        (let ((lc (try (coeff R t d) (lambda (e) 0))))
          (if (and (number? lc) (< lc 0)) (expand (list '* -1 R)) R))
        R)))

; G = Σ vecᵢ·yⁱ
(define (dv-p-list->expr-y vec)
  (simplify (cons '+ (map (lambda (i) (list '* (nth vec i) (list '^ 'y i)))
                          (range (length vec))))))

; ---------- проверка вычетов ----------

(define (dv-expr-coeffs R t)
  (let ((d (try (degree R t) (lambda (e) -1))))
    (if (or (not (integer? d)) (< d 0))
        'unknown
        (let loop ((k 0) (acc '()))
          (if (> k d)
              (reverse acc)
              (let* ((ck (try (coeff R t k) (lambda (e) 0)))
                     (p (if (number? ck) (dv-k-rat ck) (ib-k-parse ck))))
                (if (equal? p #f)
                    'unknown
                    (loop (+ k 1) (cons p acc)))))))))

(define (dv-k-list-trim l)
  (if (null? l)
      '()
      (let ((r (dv-k-list-trim (cdr l))))
        (if (and (null? r) (dv-k-zero? (car l))) '() (cons (car l) r)))))

; снять нули с младших степеней (множитель t^k) и отнормировать по старшему коэффициенту
(define (dv-k-list-drop-low l)
  (cond ((null? l) '())
        ((dv-k-zero? (car l)) (dv-k-list-drop-low (cdr l)))
        (else l)))

(define (dv-k-list-norm l)
  (let ((l (dv-k-list-drop-low (dv-k-list-trim l))))
    (if (null? l)
        'unknown
        (let ((lc (last l)))
          (map (lambda (k) (ib-k-mul k (dv-k-inv lc))) l)))))

; (Σ cᵢtⁱ)·(t − r)
(define (dv-mul-linear cl r)
  (let ((n (length cl)))
    (let loop ((i 0) (acc '()))
      (if (> i n)
          (reverse acc)
          (let ((a (if (= i 0) '() (nth cl (- i 1))))
                (b (if (>= i n) '() (nth cl i))))
            (loop (+ i 1) (cons (ib-k-add a (ib-k-mul (dv-k-neg r) b)) acc)))))))

(define (dv-k-list-eq? a b)
  (and (= (length a) (length b))
       (every? (lambda (i) (dv-k-eq? (nth a i) (nth b i))) (range (length a)))))

(define (hyp-residues-check H P x res)
  (if (or (equal? res 'unknown) (not (list? res)))
      #f
      (let* ((sum (foldl (lambda (acc pr) (ib-k-add acc (cdr pr))) '() res))
             (fin (filter (lambda (pr) (not (equal? (car (car pr)) 'inf))) res))
             (prod (foldl (lambda (acc pr) (dv-mul-linear acc (cdr pr)))
                          (list (dv-k-rat 1)) fin))
             (R (hyp-residue-poly H P x 't)))
        (if (or (equal? R 'unknown) (not (dv-k-zero? sum)))
            #f
            (let ((rc (dv-expr-coeffs R 't)))
              (if (equal? rc 'unknown)
                  #f
                  (dv-k-list-eq? (dv-k-list-norm rc) (dv-k-list-norm prod))))))))

; ---------- дивизоры ----------

(define (dv-place-eq? p q)
  (and (equal? (car p) (car q))
       (or (and (equal? (cadr p) 'ram) (equal? (cadr q) 'ram))
           (and (not (equal? (cadr p) 'ram)) (not (equal? (cadr q) 'ram))
                (dv-k-eq? (cadr p) (cadr q))))))

(define (dv-place-assoc pl al)
  (cond ((null? al) #f)
        ((dv-place-eq? pl (car (car al))) (car al))
        (else (dv-place-assoc pl (cdr al)))))

(define (dv-normalize d)
  (let loop ((rest d) (acc '()))
    (if (null? rest)
        (reverse acc)
        (let* ((pr (car rest)) (pl (car pr)) (n (cdr pr))
               (p (dv-place-assoc pl acc)))
          (if p
              (let ((s (+ (cdr p) n)))
                (loop (cdr rest)
                      (if (= s 0)
                          (filter (lambda (q) (not (dv-place-eq? (car q) pl))) acc)
                          (map (lambda (q) (if (dv-place-eq? (car q) pl) (cons pl s) q)) acc))))
              (loop (cdr rest) (if (= n 0) acc (cons (cons pl n) acc))))))))

(define (dv-add a b) (dv-normalize (append a b)))
(define (dv-scale d n) (dv-normalize (map (lambda (pr) (cons (car pr) (* (cdr pr) n))) d)))

(define (dv-degree d)
  (foldl (lambda (acc pr) (+ acc (cdr pr))) 0 d))

; ---------- ℚ-базис вычетов ----------

; ((m ((q₁ δ₁) …))) по §1.3; q — выражения, δ — дивизоры
(define (residue-divisors res)
  (if (or (equal? res 'unknown) (null? res))
      'unknown
      (let* ((keys (ib-unique (foldl (lambda (acc pr) (append (map car (cdr pr)) acc)) '() res)))
             (cs (foldl (lambda (acc pr) (append (map cdr (cdr pr)) acc)) '() res))
             (m (foldl (lambda (acc c) (dv-lcm2 acc (denom (together c)))) 1 cs))
             (pairs (map (lambda (f)
                           (list (dv-k->expr (list (cons f 1)))
                                 (dv-normalize
                                  (map (lambda (pr)
                                         (cons (car pr) (* m (ib-k-coeff (cdr pr) f))))
                                       res))))
                         keys)))
        (if (every? (lambda (pd) (and (every? integer? (map cdr (cadr pd)))
                                      (= 0 (dv-degree (cadr pd)))))
                    pairs)
            (cons m pairs)
            'unknown))))

; ---------- Шаг A5.2: L(D) и главность ----------
;
; D здесь — дивизор элемента: ищем u с v_P(u) = n_P во всех местах (div u = D).
; Так требует пример A5.2: D = 3·((0,1) − (0,−1)) → u = (y−1)/(y+1), и A5.4:
; res_P(H dx) = c·v_P(u) при H = c·u′/u.
; u = (c₀ + c₁y)/g, g = ∏(x−a)^{m_a} снимает полюсы (m_a = ⌈−n_P/e_P⌉),
; условия v_P(num) ≥ v_P(g) + n_P — линейные по коэффициентам c₀, c₁.

(define (dv-ser-pow s i limit) (ib-ser-pow s i limit))

(define (dv-dv-n-at D pl)
  (let ((p (dv-place-assoc pl D))) (if p (cdr p) 0)))

(define (dv-l-finite-n D pl) (dv-dv-n-at D pl))

; группы по конечным a: ((a m ((место n e) …)) …)
(define (dv-l-groups D P x)
  (let* ((as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                 (map (lambda (pr) (car (car pr))) D)))))
    (let loop ((as as) (acc '()))
      (if (null? as)
          (reverse acc)
          (let ((pls (hyp-places P x (car as))))
            (if (equal? pls 'unknown)
                'unknown
                (let* ((rows (map (lambda (pl)
                                    (list pl
                                          (dv-dv-n-at D pl)
                                          (if (equal? (cadr pl) 'ram) 2 1)))
                                  pls))
                       (m (foldl (lambda (mm r)
                                   (let ((nP (cadr r)) (e (caddr r)))
                                     (if (< nP 0)
                                         (let ((need (ceiling (/ (- nP) e))))
                                           (if (> need mm) need mm))
                                         mm)))
                                 0 rows)))
                  (loop (cdr as) (cons (list (car as) m rows) acc)))))))))

(define (dv-l-g groups x)
  (foldl (lambda (acc gr)
           (let ((a (car gr)) (m (cadr gr)))
             (let loop ((i 0) (p acc))
               (if (= i m) p (loop (+ i 1) (ib-p-mul p (list (- a) 1)))))))
         '(1) groups))

; максимум |n_P| по местам на ∞ (нужен и для полюсов, и для нулей)
(define (dv-l-ninf D P x)
  (let ((pls (hyp-places P x 'inf)))
    (if (equal? pls 'unknown)
        'unknown
        (foldl (lambda (m pl)
                 (let ((v (abs (dv-dv-n-at D pl)))) (if (> v m) v m)))
               0 pls))))

(define (dv-l-bounds groups D P x margin)
  (let* ((nd (try (degree P x) (lambda (e) 0)))
         (ev (even? nd))
         (sh (if ev (quotient nd 2) nd))
         (Dg (if ev 1 2))
         (dg (ib-p-deg (dv-l-g groups x)))
         (ninf (dv-l-ninf D P x)))
    (if (equal? ninf 'unknown)
        'unknown
        (let ((np (abs ninf)))
          (list (+ dg (ceiling (/ np Dg)) margin)
                (+ dg (ceiling (/ (+ np sh) Dg)) margin))))))

; строки условий в конечном месте: K = v_P(g) + n_P
(define (dv-l-rows-finite gr m P x dc0 dc1)
  (let* ((pl (car gr)) (nP (cadr gr)) (e (caddr gr))
         (K (+ (* m e) nP)))
    (if (<= K 0)
        '()
        (let* ((N (- K 1))
               (sers (hyp-place-series pl P x N))
               (xs (car sers))
               (ys (cdr sers))
               (p0 (map (lambda (k) (dv-ser-pow xs k N)) (range (+ dc0 1))))
               (p1 (map (lambda (k) (dv-ser-mul (dv-ser-pow xs k N) ys N))
                        (range (+ dc1 1)))))
          (let loop ((o 0) (rows '()))
            (if (>= o K)
                (reverse rows)
                (let ((row (append (map (lambda (s) (dv-ser-ref s o)) p0)
                                   (map (lambda (s) (dv-ser-ref s o)) p1))))
                  (if (every? dv-k-zero? row)
                      (loop (+ o 1) rows)
                      (loop (+ o 1) (cons row rows))))))))))

; строки условий на ∞: v_∞(g) = −Dg·Σm, K = v_∞(g) + n_P
(define (dv-l-rows-inf pl nP P x msum dc0 dc1)
  (let* ((nd (try (degree P x) (lambda (e) 0)))
         (ev (even? nd))
         (Dg (if ev 1 2))
         (sh (if ev (quotient nd 2) nd))
         (K (- nP (* Dg msum)))
         (N (if (>= (- K 1) 0) (- K 1) 0))
         (omin (min (* -1 Dg dc0) (- (* -1 Dg dc1) sh))))
    (if (<= K omin)
        '()
        (let* ((sers (hyp-place-series pl P x N))
               (xs (car sers))
               (ys (cdr sers))
               (p0 (map (lambda (k) (dv-ser-pow xs k N)) (range (+ dc0 1))))
               (p1 (map (lambda (k) (dv-ser-mul (dv-ser-pow xs k N) ys N))
                        (range (+ dc1 1)))))
          (let loop ((o omin) (rows '()))
            (if (>= o K)
                (reverse rows)
                (let ((row (append (map (lambda (s) (dv-ser-ref s o)) p0)
                                   (map (lambda (s) (dv-ser-ref s o)) p1))))
                  (if (every? dv-k-zero? row)
                      (loop (+ o 1) rows)
                      (loop (+ o 1) (cons row rows))))))))))

(define (dv-l-rows groups D P x dc0 dc1)
  (let* ((msum (foldl (lambda (acc gr) (+ acc (cadr gr))) 0 groups))
         (inf (hyp-places P x 'inf))
         (fin (foldl (lambda (acc gr)
                       (foldl (lambda (a2 r)
                                (append a2 (dv-l-rows-finite r (cadr gr) P x dc0 dc1)))
                              acc (caddr gr)))
                     '() groups)))
    (if (equal? inf 'unknown)
        'unknown
        (foldl (lambda (acc pl)
                 (append acc (dv-l-rows-inf pl (dv-dv-n-at D pl) P x msum dc0 dc1)))
               fin inf))))

(define (dv-unit-vec j n)
  (map (lambda (i) (if (= i j) 1 0)) (range n)))

; коэффициенты cᵢ ∈ ℚ (§1.4): строка условий, расщеплённая по ключам ℚ(√d),
; даёт скалярные уравнения, поэтому координата ядра — само рациональное число
(define (dv-l-coef v keys nunks j) (dv-k-rat (nth v j)))

(define (dv-l-poly-expr cs x)
  (simplify (cons '+ (map (lambda (k)
                            (let ((c (nth cs k)))
                              (if (dv-k-zero? c) 0
                                  (list '* (dv-k->expr c) (list '^ x k)))))
                          (range (length cs))))))

(define (dv-l-kernel->expr v keys nunks dc0 dc1 groups x)
  (let* ((c0s (map (lambda (k) (dv-l-coef v keys nunks k)) (range (+ dc0 1))))
         (c1s (map (lambda (k) (dv-l-coef v keys nunks (+ dc0 1 k))) (range (+ dc1 1))))
         (c0 (dv-l-poly-expr c0s x))
         (c1 (dv-l-poly-expr c1s x))
         (g (ib-poly->expr (dv-l-g groups x) x)))
    (simplify (list '/ (simplify (list '+ c0 (list '* c1 'y))) g))))

(define (dv-l-basis D P x margin)
  (let ((Dn (dv-normalize D)))
    (if (not (every? (lambda (pr) (integer? (cdr pr))) Dn))
        'unknown
        (let ((groups (dv-l-groups Dn P x)))
          (if (equal? groups 'unknown)
              'unknown
              (let ((bd (dv-l-bounds groups Dn P x margin)))
                (if (equal? bd 'unknown)
                    'unknown
                    (let* ((dc0 (car bd))
                           (dc1 (cadr bd))
                           (nunks (+ (+ dc0 1) (+ dc1 1)))
                           (rows (dv-l-rows groups Dn P x dc0 dc1)))
                      (if (equal? rows 'unknown)
                          'unknown
                          (let* ((keys (if (null? rows) (list '()) (ib-row-keys rows)))
                                 (qrows (ib-expand-rows rows keys))
                                 (ker (if (null? qrows)
                                          (map (lambda (j) (dv-unit-vec j nunks)) (range nunks))
                                          (try (fm-nullspace (field-Q) qrows)
                                               (lambda (e) 'unknown)))))
                            (cond ((equal? ker 'unknown) 'unknown)
                                  ((and (null? ker) (> (length keys) 1))
                                   'unknown)   ; решение могло быть в ℚ(√d) — не доказано
                                  (else
                                   (map (lambda (v) (dv-l-kernel->expr v keys nunks dc0 dc1 groups x))
                                        ker)))))))))))))

; L(D) в стандартном смысле (§1.4): {u : div u + D ≥ 0} = {v_P(u) ≥ −n_P};
; для главности (div u = D) — L(−D), см. hyp-principal
(define (hyp-riemann-roch D P x)
  (if (equal? (dv-divisor-ok? D P x) #t)
      (dv-l-basis (dv-scale D -1) P x 2)
      'unknown))

; ---------- главность ----------

(define (dv-l-all-places D P x)
  (let* ((as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                 (map (lambda (pr) (car (car pr))) D))))
         (fin (foldl (lambda (acc a)
                       (let ((ps (hyp-places P x a)))
                         (if (equal? ps 'unknown) 'unknown (append acc ps))))
                     '() as))
         (inf (hyp-places P x 'inf)))
    (cond ((equal? fin 'unknown) 'unknown)
          ((equal? inf 'unknown) 'unknown)
          (else (append fin inf)))))

; Замечание ревью A5.2: нули и полюсы u вне x-координат supp D раньше не проверялись — u·(x+1)/(x−5)
; проходил. Норма N(u) = u·ū ∈ ℚ(x) (ū — y ↦ −y) обращается в 0/∞ ровно над x-координатами нулей/полюсов u:
; числитель и знаменатель N должны раскладываться только на (x − a), a ∈ x(supp D) (∞ проверяется местами).
(define (dv-norm-supp-ok? Dn u P x)
  (let* ((Y (list '^ P 1/2))
         (uu (subst (list (list 'y Y)) u))
         (uc (subst (list (list 'y (list '* -1 Y))) u))
         (N (try (together (simplify (list '* uu uc))) (lambda (e) #f)))
         (as (ib-unique (filter (lambda (a) (not (equal? a 'inf))) (map (lambda (pr) (car (car pr))) Dn)))))
    (and N (not (equal? N 0))
         (polynomial? (numer N) x) (polynomial? (denom N) x)
         (dv-only-roots? (numer N) as x) (dv-only-roots? (denom N) as x))))

; многочлен p (≠ 0) — константа · ∏ (x − a)^k по a из as
(define (dv-only-roots? p as x)
  (let loop ((p (simplify p)) (as as))
    (if (null? as)
        (= (degree p x) 0)
        (loop (dv-strip-root p (car as) x) (cdr as)))))

(define (dv-strip-root p a x)
  (if (and (> (degree p x) 0) (equal? (simplify (subst (list (list x a)) p)) 0))
      (dv-strip-root (simplify (poly-quotient p (list '- x a) x)) a x)
      p))

(define (hyp-principal-check D u P x)
  (let ((Dn (dv-normalize D)))
    (cond ((not (equal? (dv-divisor-ok? D P x) #t)) #f)
          ((not (= 0 (dv-degree Dn))) #f)
          ((not (every? (lambda (pr) (integer? (cdr pr))) Dn)) #f)
          (else
           (let ((pls (dv-l-all-places Dn P x)))
             (if (or (equal? pls 'unknown) (not (dv-norm-supp-ok? Dn u P x)))
                 #f
                 (every? (lambda (pl)
                           (let ((v (hyp-valuation pl u P x)))
                             (and (integer? v) (= v (dv-dv-n-at Dn pl)))))
                         pls)))))))

; D — дивизор элемента (v_P(u) = n_P); нули на ∞ требуют z-модели
(define (hyp-principal D P x)
  (let ((Dn (dv-normalize D)))
    (cond
      ((not (equal? (dv-divisor-ok? D P x) #t)) 'unknown)
      ((not (= 0 (dv-degree Dn))) 'not-principal)
      ((equal? (dv-inf-zero? Dn P x) 'unknown) 'unknown)
      ((dv-inf-zero? Dn P x)
       (let ((zm (dv-zmodel Dn P x)))
         (if (equal? zm 'unknown)
             'unknown
             (let* ((h (quotient (try (degree P x) (lambda (e) 0)) 2))
                    (bz (dv-l-basis (car zm) (cdr zm) 'z 2)))
               (if (equal? bz 'unknown)
                   'unknown
                   (let loop ((us bz))
                     (if (null? us)
                         'not-principal
                         (let ((u (dv-zmodel-back (car us) h x)))
                           (if (hyp-principal-check Dn u P x)
                               (list 'principal u)
                               (loop (cdr us)))))))))))
      (else
       (let ((b (dv-l-basis Dn P x 2)))
         (cond ((equal? b 'unknown) 'unknown)
               ((null? b) 'not-principal)
               (else
                (let ((u (car b)))
                  (if (hyp-principal-check Dn u P x)
                      (list 'principal u)
                      'unknown)))))))))

; ---------- подстановка ряда в выражение (независимо от alg-nf) ----------

; 1/s для ряда Лорана s, до порядка N
(define (dv-ser-linv s N)
  (let ((s (dv-ser-clean s)))
    (if (null? s)
        'unknown
        (let* ((v (car (car s)))
               (s0 (dv-ser-shift s (- v)))
               (ic (dv-k-inv (dv-ser-ref s0 0))))
          (if (equal? ic #f)
              'unknown
              (let* ((d1 (dv-ser-scale s0 ic))
                     (J (if (>= (- N v) 0) (- N v) 0))
                     (inv (dv-ser-inv1 d1 J)))
                (dv-ser-trunc (dv-ser-shift (dv-ser-scale inv ic) (- v)) N)))))))

(define (dv-ser-bad? s) (equal? s 'unknown))

; значение выражения от x, y в рядах xs, ys (y² = P); #f — не поддерживается
(define (dv-expr-series e xs ys P x N)
  (let ((e (simplify e)))
    (cond ((number? e) (dv-ser-const (dv-k-rat (together e))))
          ; константа с радикалами (ℚ(√d), A5.5b): разбираем в ib-k
          ((and (x-free? e x) (not (contains-sym? e 'y)))
           (let ((k (try (ib-k-parse e) (lambda (err) #f))))
             (if (and k (pair? k)) (dv-ser-const k) 'unknown)))
          ((equal? e x) xs)
          ((equal? e 'y) ys)
          ((pair? e)
           (let ((op (car e)) (as (cdr e)))
             (cond
               ((equal? op '+)
                (let loop ((as as) (acc '()))
                  (if (null? as)
                      acc
                      (let ((s (dv-expr-series (car as) xs ys P x N)))
                        (if (dv-ser-bad? s) 'unknown
                            (loop (cdr as) (dv-ser-add acc s)))))))
               ((equal? op '-)
                (if (null? (cdr as))
                    (let ((s (dv-expr-series (car as) xs ys P x N)))
                      (if (dv-ser-bad? s) 'unknown (dv-ser-neg s)))
                    (let ((first (dv-expr-series (car as) xs ys P x N)))
                      (if (dv-ser-bad? first)
                          'unknown
                          (let loop ((as (cdr as)) (acc first))
                            (if (null? as)
                                acc
                                (let ((s (dv-expr-series (car as) xs ys P x N)))
                                  (if (dv-ser-bad? s) 'unknown
                                      (loop (cdr as) (dv-ser-sub acc s))))))))))
               ((equal? op '*)
                (let loop ((as as) (acc (dv-ser-const (ib-k-one))))
                  (if (null? as)
                      acc
                      (let ((s (dv-expr-series (car as) xs ys P x N)))
                        (if (dv-ser-bad? s) 'unknown
                            (loop (cdr as) (dv-ser-mul acc s N)))))))
               ((equal? op '/)
                (let ((first (dv-expr-series (car as) xs ys P x N)))
                  (if (dv-ser-bad? first)
                      'unknown
                      (let loop ((as (cdr as)) (acc first))
                        (if (null? as)
                            acc
                            (let* ((s (dv-expr-series (car as) xs ys P x N))
                                   (iv (if (dv-ser-bad? s) 'unknown (dv-ser-linv s N))))
                              (if (dv-ser-bad? iv) 'unknown
                                  (loop (cdr as) (dv-ser-mul acc iv N)))))))))
               ((equal? op '^)
                (let ((p (simplify (cadr as))))
                  (cond
                    ((and (equal? p 1/2) (null? (cdr (cdr as))))
                     (if (equal? (simplify (car as)) (simplify P))
                         ys
                         'unknown))
                    ((integer? p)
                     (let ((b (dv-expr-series (car as) xs ys P x N)))
                       (if (dv-ser-bad? b)
                           'unknown
                           (if (>= p 0)
                               (dv-ser-pow b p N)
                               (dv-ser-linv (dv-ser-pow b (- p) N) N)))))
                    (else 'unknown))))
               (else 'unknown))))
          (else 'unknown))))

; v_P(f) для произвольного рационального выражения от x, y (y² = P)
(define (dv-valuation-series pl f P x)
  (let loop ((N 8))
    (if (> N 256)
        'unknown
        (let* ((sers (hyp-place-series pl P x N))
               (fs (dv-expr-series f (car sers) (cdr sers) P x N)))
          ; R5.3b: при малом N степень x^(−k), k ≥ N, обнуляется при усечении (ряд пуст ⇒ unknown): повтор с большим N
          ; R5.3b: при малом N степень x^(−k), k ≥ N, обнуляется при усечении (ряд пуст ⇒ unknown): повтор с большим N
          (cond ((dv-ser-bad? fs) (if (< N 64) (loop (* N 2)) 'unknown))
                ((dv-ser-null? fs) (loop (* N 2)))
                ((<= (dv-ser-min fs) N) (dv-ser-min fs))
                (else (loop (* N 2))))))))

; ---------- Шаг A5.3: хорошие простые, счёт точек, граница кручения ----------

(define (dv-mod-inv a p)
  (let loop ((r0 p) (r1 (modulo a p)) (s0 0) (s1 1))
    (if (= r1 0)
        (modulo s0 p)
        (let ((q (quotient r0 r1)))
          (loop r1 (- r0 (* q r1)) s1 (- s0 (* q s1)))))))

; коэффициенты P по модулю p (общий знаменатель не должен делиться на p)
(define (dv-pmod-coeffs P x p)
  (let ((pl (ib-poly-parse P x)))
    (if (equal? pl #f)
        'unknown
        (let ((L (foldl (lambda (a c) (dv-lcm2 a (denom (together c)))) 1 pl)))
          (if (= 0 (modulo L p))
              'unknown
              (ib-p-trim (map (lambda (c) (modulo (* c L) p)) pl)))))))

(define (dv-pmod-sub a b p)
  (ib-p-trim (map (lambda (c) (modulo c p)) (ib-p-sub a b))))

(define (dv-pmod-mul a b p)
  (ib-p-trim (map (lambda (c) (modulo c p)) (ib-p-mul a b))))

(define (dv-pmod-rem a b p)
  (let loop ((a (ib-p-trim a)))
    (if (or (null? a) (null? (ib-p-trim b)) (< (ib-p-deg a) (ib-p-deg (ib-p-trim b))))
        a
        (let* ((b (ib-p-trim b))
               (k (- (ib-p-deg a) (ib-p-deg b)))
               (c (modulo (* (ib-p-lc a) (dv-mod-inv (ib-p-lc b) p)) p)))
          (loop (dv-pmod-sub a (dv-pmod-mul (ib-p-mono k c) b p) p))))))

(define (dv-pmod-monic a p)
  (let ((a (ib-p-trim a)))
    (if (null? a)
        '()
        (let ((ic (dv-mod-inv (modulo (ib-p-lc a) p) p)))
          (ib-p-trim (map (lambda (c) (modulo (* c ic) p)) a))))))

(define (dv-pmod-gcd a b p)
  (let ((b (ib-p-trim b)))
    (if (null? b)
        (dv-pmod-monic a p)
        (dv-pmod-gcd b (dv-pmod-rem a b p) p))))

(define (dv-pmod-deriv pl p)
  (let ((pl (ib-p-trim pl)))
    (if (null? pl)
        '()
        (ib-p-trim (map (lambda (k) (modulo (* (+ k 1) (nth pl (+ k 1))) p))
                        (range (- (length pl) 1)))))))

; хорошее p: нечётное простое, p ∤ lc(P), P mod p бесквадратен (p ∤ disc P)
(define (hyp-good-prime? P x p)
  (if (not (and (integer? p) (> p 2) (true? (prime? p))))
      #f
      (let ((pl (dv-pmod-coeffs P x p)))
        (cond ((equal? pl 'unknown) 'unknown)
              ((null? pl) #f)
              ((= 0 (modulo (ib-p-lc pl) p)) #f)
              (else (= 0 (ib-p-deg (dv-pmod-gcd pl (dv-pmod-deriv pl p) p))))))))

(define (dv-pmod-eval pl a p)
  (let loop ((cs (reverse (ib-p-trim pl))) (acc 0))
    (if (null? cs) acc (loop (cdr cs) (modulo (+ (* acc a) (car cs)) p)))))

; #C(𝔽_{p^k}); k = 1, 2
(define (hyp-count-points P x p k)
  (let ((pl (dv-pmod-coeffs P x p)))
    (if (equal? pl 'unknown)
        'unknown
        (let ((nd (ib-p-deg pl))
              (lc (ib-p-lc pl)))
          (cond
            ((= k 1)
             (+ (let loop ((a 0) (s 0))
                  (if (= a p)
                      s
                      (loop (+ a 1) (+ s 1 (jacobi (dv-pmod-eval pl a p) p)))))
                (if (even? nd) (+ 1 (jacobi lc p)) 1)))
            ((= k 2) (dv-count-points-sq pl p))
            (else 'unknown))))))

; неприводимый квадратичный многочлен над GF(p)
(define (dv-irr-quad p)
  (let loop ((b 0))
    (if (>= b p)
        'unknown
        (let ((m (list (modulo b p) 0 1)))
          (if (true? (gf-irreducible? m p)) m (loop (+ b 1)))))))

(define (dv-gf-peval pl a p F)
  (let loop ((cs (reverse (ib-p-trim pl))) (acc (gf-elt F 0)))
    (if (null? cs)
        acc
        (loop (cdr cs) (gf+ F (gf* F acc a) (gf-elt F (modulo (car cs) p)))))))

(define (dv-gf-char-val chi p F)
  (let ((v (gf->int F chi)))
    (cond ((= v 0) 0) ((= v 1) 1) ((= v (- p 1)) -1) (else 0))))

(define (dv-count-row-sq F pl p c0 e2)
  (let loop ((c1 0) (s 0))
    (if (= c1 p)
        s
        (let* ((a (gf-elt F (list c0 c1)))
               (v (dv-gf-peval pl a p F))
               (iv (gf->int F v))
               (ch (if (= iv 0) 0 (dv-gf-char-val (gf-power F v e2) p F))))
          (loop (+ c1 1) (+ s 1 ch))))))

(define (dv-count-points-sq pl p)
  (let* ((m (dv-irr-quad p))
         (deg (ib-p-deg pl))
         (lc (ib-p-lc pl)))
    (if (equal? m 'unknown)
        'unknown
        (let* ((F (gf-field p m 't))
               (e2 (quotient (- (* p p) 1) 2)))
          (+ (let loop ((c0 0) (s 0))
               (if (= c0 p) s (loop (+ c0 1) (+ s (dv-count-row-sq F pl p c0 e2)))))
             (if (even? deg) (+ 1 (jacobi lc p)) 1))))))

; #J(𝔽_p) для рода 1–2; род ≥ 3 — unknown
(define (hyp-jacobian-order P x p)
  (let* ((n (try (degree P x) (lambda (e) 0)))
         (g (if (even? n) (- (quotient n 2) 1) (quotient (- n 1) 2))))
    (cond
      ((= g 1) (hyp-count-points P x p 1))
      ((= g 2)
       (let ((n1 (hyp-count-points P x p 1))
             (n2 (hyp-count-points P x p 2)))
         (if (or (equal? n1 'unknown) (equal? n2 'unknown))
             'unknown
             (let* ((a1 (- n1 (+ p 1)))
                    (a2 (/ (+ (- n2 (* p p) 1) (* a1 a1)) 2)))
               (if (integer? a2)
                   (+ 1 a1 a2 (* p a1) (* p p))
                   'unknown)))))
      (else (hyp-jacobian-order-general P x p)))))

; R5.2: подсчёт точек над 𝔽_{p^g} стоит ≈ 15 мкс·p^g (таблицы по всем элементам), поэтому простые с p^g > dv-count-cap
; пропускаются (p^g растёт вместе с p — на первом же слишком дорогом просмотр заканчивается). Кручение J(K) вкладывается в
; J(𝔽_p) для КАЖДОГО хорошего p, значит B = #J(𝔽_p) по одному p — слабее, но верная граница (больше кандидатов n | B,
; отказ «не кручение» по-прежнему доказан); при отсутствии допустимых p — unknown (тогда n = 1…12 и ответ не «неэлементарен»).
(define dv-count-cap 150000)         ; при бюджете времени integrate (≈ 2,5 с на простое)
(define dv-count-cap-free 1200000)   ; без бюджета (int-time-limit = #f): до ≈ 20 с на простое

(define (dv-cap) (if int-time-limit dv-count-cap dv-count-cap-free))

(define (dv-genus P x)
  (let ((n (try (degree P x) (lambda (e) 0))))
    (if (even? n) (- (quotient n 2) 1) (quotient (- n 1) 2))))

(define dv-td-cache '())   ; ((P x cap) . данные) — последний подсчёт

; список (p . #J(𝔽_p)) по одному–двум наименьшим хорошим p ≥ 3 (p ≤ 50, p^g ≤ dv-count-cap) или 'unknown
(define (hyp-torsion-data P x)
  (let ((key (list P x (dv-cap))))
    (if (and (pair? dv-td-cache) (equal? (car dv-td-cache) key))
        (cdr dv-td-cache)
        (let ((r (hyp-torsion-data1 P x)))
          (set! dv-td-cache (cons key r))
          r))))

(define (hyp-torsion-data1 P x)
  (let ((g (max 1 (dv-genus P x))))
    (let loop ((p 3) (found '()))
      (cond ((>= (length found) 2) (reverse found))
            ((or (> p 50) (> (^ p g) (dv-cap))) (if (null? found) 'unknown (reverse found)))
            (else
             (let ((gp (hyp-good-prime? P x p)))
               (cond ((equal? gp 'unknown) 'unknown)
                     (gp (let ((j (hyp-jacobian-pick P x p)))
                           (if (equal? j 'unknown)
                               'unknown
                               (loop (next-prime p) (cons (cons p j) found)))))
                     (else (loop (next-prime p) found)))))))))

; B = gcd(#J(𝔽_p), #J(𝔽_q)) по двум наименьшим хорошим допустимым p, q ≥ 3 (или #J(𝔽_p) по одному)
(define (hyp-torsion-bound P x)
  (let ((d (hyp-torsion-data P x)))
    (if (equal? d 'unknown) 'unknown (foldl gcd 0 (map cdr d)))))

; поиск порядка: n по возрастанию; non-torsion — только если граница известна и всё отвергнуто
(define (dv-torsion-search D P x ns known?)
  (let loop ((ns ns) (unk #f))
    (cond ((null? ns) (if (and known? (not unk)) 'non-torsion 'unknown))
          (else
           (let ((r (hyp-principal (dv-scale D (car ns)) P x)))
             (cond ((and (pair? r) (equal? (car r) 'principal))
                    (list (car ns) (cadr r)))
                   ((equal? r 'unknown) (loop (cdr ns) #t))
                   (else (loop (cdr ns) unk))))))))

; ---------- ключевые шаги (журнал, alg-step): места, дивизор δ, граница кручения, главность ----------

; место (a b q) → строка «(x = a, y = b)»; ветвление — «(x = a, ветвление)»
(define (dv-note-place pl)
  (let ((a (car pl)) (b (cadr pl)))
    (cond ((equal? b 'ram) (string-append "(x = " (alg-mp a) ", ветвление)"))
          ((equal? a 'inf) (string-append "(∞, y = " (alg-mp (dv-k->expr b)) ")"))
          (else (string-append "(x = " (alg-mp a) ", y = " (alg-mp (dv-k->expr b)) ")")))))

; дивизор ((место . n) …) → «7·(x = 0, y = 4) + (-7)·(x = 0, y = -4)»
(define (dv-note-divisor d)
  (alg-join (map (lambda (pr) (string-append (if (< (cdr pr) 0) (string-append "(" (to-string (cdr pr)) ")") (to-string (cdr pr)))
                                             "·" (dv-note-place (car pr))))
                 d)
            " + "))

; хорошие простые p ≥ 3 и #J(F_p) — как в hyp-torsion-bound (только для пояснения шага)
(define (dv-note-torsion-data P x)
  (let ((d (hyp-torsion-data P x)))
    (if (equal? d 'unknown) '() d)))

; R(t) в разложенном виде: K·t^k·(t² − a²)·(t − r)·… — K = старший коэффициент, множители унитарны (factor над ℚ);
; пары линейных множителей (t − a)(t + a) одной кратности склеиваются в (t² − a²)
(define (dv-fmt-pow s k) (if (= k 1) s (string-append s "^" (to-string k))))

(define (dv-fmt-root r)   ; (t − r) | (t + r)
  (if (< r 0) (string-append "(t + " (to-string (- r)) ")") (string-append "(t − " (to-string r) ")")))

; монический многочлен от t по убыванию степеней: t^2 − 1/5, t^3 + 2t − 1
(define (dv-fmt-desc f)
  (let* ((d (degree f 't))
         (term (lambda (c k)
                 (let ((a (abs c)))
                   (string-append (if (< c 0) " − " " + ")
                                  (cond ((= k 0) (to-string a))
                                        (else (string-append (if (= a 1) "" (to-string a))
                                                             (if (= k 1) "t" (string-append "t^" (to-string k))))))))))
         (rest (let loop ((k (- d 1)) (acc '()))
                 (if (< k 0)
                     (reverse acc)
                     (let ((c (coeff f 't k)))
                       (loop (- k 1) (if (= c 0) acc (cons (term c k) acc))))))))
    (string-append (if (= d 1) "t" (string-append "t^" (to-string d))) (apply string-append rest))))

(define (dv-factored-R R)
  (let* ((d (try (degree R 't) (lambda (e) #f)))
         (K (and d (coeff R 't d)))
         (fl (try (factor-list R) (lambda (e) #f))))
    (if (not (and d (number? K) (pair? fl)))
        (alg-mp R)
        (let* ((fs (cdr fl))
               (lin (filter (lambda (pe) (equal? (try (degree (car pe) 't) (lambda (e) #f)) 1)) fs))
               (rest (filter (lambda (pe) (not (member? pe lin))) fs))
               (roots (map (lambda (pe) (cons (/ (- (coeff (car pe) 't 0)) (coeff (car pe) 't 1)) (cadr pe))) lin))
               (zero (filter (lambda (rk) (= (car rk) 0)) roots))
               (nz (filter (lambda (rk) (not (= (car rk) 0))) roots))
               (pairs (filter (lambda (rk) (and (> (car rk) 0) (member? (cons (- (car rk)) (cdr rk)) nz))) nz))
               (single (filter (lambda (rk) (not (or (member? rk pairs)
                                                    (and (< (car rk) 0) (member? (cons (- (car rk)) (cdr rk)) pairs)))))
                               nz))
               (terms (append
                       (map (lambda (rk) (dv-fmt-pow "t" (cdr rk))) zero)
                       (map (lambda (rk) (dv-fmt-pow (string-append "(t^2 − " (to-string (* (car rk) (car rk))) ")") (cdr rk))) pairs)
                       (map (lambda (rk) (dv-fmt-pow (dv-fmt-root (car rk)) (cdr rk))) single)
                       (map (lambda (pe) (let ((m (expand (list '/ (car pe) (coeff (car pe) 't (degree (car pe) 't))))))
                                           (dv-fmt-pow (string-append "(" (dv-fmt-desc m) ")") (cadr pe))))
                            rest))))
          (cond ((and (= K 1) (null? terms)) "1")
                ((= K 1) (alg-join terms "·"))
                (else (alg-join (cons (if (= K -1) "−1" (to-string K)) terms) "·")))))))

; вычеты (с обеими проверками) и дивизор δ по §1.3
(define (dv-note-residues H P x res rd)
  (let ((R (try (hyp-residue-poly H P x 't) (lambda (err) #f))))
    (alg-step 'alg-residues "Вычеты H dx и дивизор вычетов δ"
              (string-append "вычеты: "
                             (alg-join (map (lambda (pr) (string-append (alg-mp (dv-k->expr (cdr pr))) " в " (dv-note-place (car pr)))) res)
                                       "; ")
                             ". Проверки: сумма вычетов = 0; R(t) = "
                             (if (and R (not (equal? R 'unknown))) (dv-factored-R R) "?")
                             " с корнями — вычетами (с кратностями). δ = Σ m·res·P, m = " (to-string (car rd))
                             " (наименьшее натуральное, при котором все m·res целые): "
                             (alg-join (map (lambda (pd) (string-append (if (equal? (simplify (car pd)) 1) "" (string-append (alg-mp (car pd)) "·"))
                                                                        "[" (dv-note-divisor (cadr pd)) "]"))
                                            (filter (lambda (pd) (not (null? (cadr pd)))) (cdr rd)))
                                       "; ")
                             "; степень δ = 0")
              (int-form H x)
              (cons 'list (map (lambda (pr) (dv-k->expr (cdr pr))) res)))))

; аффинные точки кривой y² = P над 𝔽_p: список (a b) (b — все корни b² = P(a))
(define (dv-note-points P x p)
  (let ((pl (dv-pmod-coeffs P x p)))
    (if (equal? pl 'unknown)
        '()
        (let loop ((a 0) (pts '()))
          (if (= a p)
              (reverse pts)
              (let* ((v (dv-pmod-eval pl a p))
                     (bs (filter (lambda (b) (= (modulo (* b b) p) v)) (range p))))
                (loop (+ a 1) (append (reverse (map (lambda (b) (list a b)) bs)) pts))))))))

; число точек на ∞: нечётная степень — одна, чётная — 1 + (lc/p)
(define (dv-note-inf-count P x p)
  (let ((pl (dv-pmod-coeffs P x p)))
    (if (equal? pl 'unknown)
        0
        (if (even? (ib-p-deg pl)) (+ 1 (jacobi (ib-p-lc pl) p)) 1))))

; «(аффинных 6: (0, 1), (0, 2), …; на ∞: 1)» для рода 1 при совпадении с #E(F_p); иначе пусто
(define (dv-note-point-list P x p j)
  (let* ((pts (dv-note-points P x p))
         (k (dv-note-inf-count P x p)))
    (if (not (= j (+ (length pts) k)))
        ""
        (string-append " (аффинных " (to-string (length pts))
                       (if (<= (length pts) 20)
                           (string-append ": " (alg-join (map (lambda (pt) (string-append "(" (to-string (car pt)) ", " (to-string (cadr pt)) ")")) pts) ", "))
                           "")
                       "; на ∞: " (to-string k) ")"))))

(define (dv-note-bound P x B)
  (alg-step 'alg-torsion-bound "Граница кручения B (число точек по модулю p)"
            (if (equal? B 'unknown)
                "граница не найдена среди хороших p ≤ 50: перебираются n = 1…12"
                (let* ((dt (dv-note-torsion-data P x))
                       (dg (try (degree P x) (lambda (err) 0)))
                       (g (quotient (- dg 1) 2)))
                  (string-append "хорошие p (p ∤ disc P): "
                                 (alg-join (map (lambda (pj) (string-append "p = " (to-string (car pj)) ": "
                                                                            (if (= g 1) "#E(F_p) = " "#J(F_p) = ") (to-string (cdr pj))
                                                                            (if (and (= g 1) (number? (cdr pj)))
                                                                                (dv-note-point-list P x (car pj) (cdr pj))
                                                                                "")))
                                                dt)
                                           "; ")
                                 "; B = НОД = " (to-string B))))
            (cons 'list (map car (dv-note-torsion-data P x)))
            B))

; граница кручения над ℚ(√d): расщеплённые и инертные p
(define (dv-note-bound-ev P x d)
  (let ((dt (hyp-torsion-data-ev P x d)))
    (alg-step 'alg-torsion-bound "Граница кручения B (число точек по модулю p)"
              (if (equal? dt 'unknown)
                  "граница не найдена среди хороших p ≤ 50: перебираются n = 1…12"
                  (string-append "K = ℚ(√" (to-string d) "); хорошие p (p ∤ disc P·d): "
                                 (alg-join (map (lambda (e)
                                                  (string-append "p = " (to-string (car e))
                                                                 (if (equal? (cadr e) 'split)
                                                                     " (расщеплено, поле вычетов F_p): #J(F_p) = L_p(1) = "
                                                                     " (инертно, поле вычетов F_(p²)): #J(F_(p²)) = L_p(1)·L_p(−1) = ")
                                                                 (to-string (nth e 2))))
                                                dt)
                                           "; ")
                                 "; B = НОД = " (to-string (foldl gcd 0 (map (lambda (e) (nth e 2)) dt)))))
              (cons 'list (if (equal? dt 'unknown) '() (map car dt)))
              (hyp-torsion-bound-ev P x d))))

; почему перебираются только n | B
(define (dv-note-why-divisors B)
  (if (number? B)
      (string-append "; n | B = " (to-string B) ": порядок δ в J(ℚ) делит #J(F_p) для хороших p (редукция инъективна на кручении)")
      ""))

(define (dv-note-principal Dn t ns B cert)
  (let ((cert-s (if cert (string-append "; " cert) ""))
        (tried (if (and (pair? t) (= (length t) 2)) (filter (lambda (k) (<= k (car t))) ns) ns)))
    (cond
      ((and (pair? t) (= (length t) 2))
       (alg-step 'alg-principal "Проверка главности n·δ"
                 (string-append "n·δ главный при n = " (to-string (car t)) ": найдена функция u с div u = "
                                (to-string (car t)) "·δ (перебор n ∈ {" (alg-join (map to-string tried) ", ") "}"
                                (dv-note-why-divisors B)
                                (if (> (length tried) 1)
                                    (string-append "; при отвергнутых n ∈ {" (alg-join (map to-string (take tried (- (length tried) 1))) ", ")
                                                   "} пространство L(−n·δ) = {u : div u ≥ n·δ} нулевое, функции u нет")
                                    "")
                                ")" cert-s)
                 (cons 'list tried) (cadr t)))
      ((equal? t 'non-torsion)
       (set! alg-why (string-append "δ не кручение: B = " (to-string B) ", перебраны n ∈ {" (alg-join (map to-string ns) ", ")
                                    "}, n·δ не главный ни при одном — по Трагеру ∫ неэлементарен"))
       (alg-step 'alg-principal "Проверка главности n·δ"
                 (string-append "n·δ не главный ни при одном n ∈ {" (alg-join (map to-string ns) ", ") "} (B = " (to-string B) ")"
                                (dv-note-why-divisors B)
                                "; для каждого n пространство L(−n·δ) = {u : div u ≥ n·δ} нулевое, функции u нет" cert-s)
                 (cons 'list ns) 'non-torsion))
      (else
       (alg-step 'alg-principal "Проверка главности n·δ" "поиск функции u не завершён" (cons 'list tried) 'unknown)))))

; ---------- ST.1c: независимый сертификат порядка δ законом сложения (род 1, deg P = 3) ----------
;
; y² = a·x³ + b·x² + c·x + d, нулевая точка O — на ∞.  Точка — 'O или (x y) с рациональными x, y.
; δ = Σ nᵢ·Pᵢ (deg 0) ~ Σ nᵢ·(Pᵢ − O): порядок класса δ в J(ℚ) = E(ℚ) равен порядку T = Σ nᵢ·Pᵢ в группе E.

; коэффициенты (d c b a) (по возрастанию) при deg P = 3 над ℚ, иначе #f
(define (ec-coeffs P x)
  (let ((pl (try (ib-poly-parse P x) (lambda (e) #f))))
    (if (and (pair? pl) (= 4 (length pl)) (not (any? (lambda (c) (not (number? c))) pl)) (not (= 0 (nth pl 3)))) pl #f)))

(define (ec-on-curve? co pt)
  (or (equal? pt 'O)
      (and (pair? pt) (number? (car pt)) (number? (cadr pt))
           (let ((X (car pt)))
             (= (* (cadr pt) (cadr pt))
                (+ (* (nth co 3) X X X) (* (nth co 2) X X) (* (nth co 1) X) (nth co 0)))))))

(define (ec-neg pt) (if (equal? pt 'O) 'O (list (car pt) (- (cadr pt)))))

; сумма точек (хорда и касательная); обе точки лежат на кривой
(define (ec-add-co co p q)
  (cond ((equal? p 'O) q)
        ((equal? q 'O) p)
        (else
         (let ((x1 (car p)) (y1 (cadr p)) (x2 (car q)) (y2 (cadr q))
               (a (nth co 3)) (b (nth co 2)) (c (nth co 1)))
           (if (and (= x1 x2) (= (+ y1 y2) 0))
               'O
               (let* ((lam (if (= x1 x2)
                               (/ (+ (* 3 a x1 x1) (* 2 b x1) c) (* 2 y1))
                               (/ (- y2 y1) (- x2 x1))))
                      (x3 (- (/ (- (* lam lam) b) a) x1 x2))
                      (y3 (- (+ y1 (* lam (- x3 x1))))))
                 (list x3 y3)))))))

; kT, k = 1..n: список точек
(define (ec-multiples-co co T n)
  (let loop ((k 1) (cur T) (acc '()))
    (if (> k n)
        (reverse acc)
        (loop (+ k 1) (ec-add-co co cur T) (cons cur acc)))))

(define (ec-mul-co co k pt)
  (if (< k 0)
      (ec-mul-co co (- k) (ec-neg pt))
      (let loop ((i 0) (cur 'O))
        (if (= i k) cur (loop (+ i 1) (ec-add-co co cur pt))))))

; место (a b) → точка | 'skip (не над ℚ) | #f (не на кривой)
(define (ec-place-point co pl)
  (cond ((not (and (list? pl) (= 2 (length pl)))) 'skip)
        ((equal? (car pl) 'inf) (if (equal? (cadr pl) 'ram) 'O 'skip))
        ((not (number? (car pl))) 'skip)
        ((equal? (cadr pl) 'ram) (let ((pt (list (car pl) 0))) (if (ec-on-curve? co pt) pt #f)))
        (else
         (let ((y (if (number? (cadr pl)) (cadr pl) (try (dv-k->rat (cadr pl)) (lambda (e) #f)))))
           (if (number? y)
               (let ((pt (list (car pl) y))) (if (ec-on-curve? co pt) pt #f))
               'skip)))))

; T = Σ nᵢ·Pᵢ: точка | 'skip | #f (место не на кривой или deg D ≠ 0)
(define (ec-divisor-sum-co co D)
  (let loop ((ds D) (T 'O) (deg 0))
    (if (null? ds)
        (if (= deg 0) T #f)
        (let ((pt (ec-place-point co (car (car ds)))))
          (cond ((equal? pt 'skip) 'skip)
                ((equal? pt #f) #f)
                (else (loop (cdr ds) (ec-add-co co T (ec-mul-co co (cdr (car ds)) pt))
                            (+ deg (cdr (car ds))))))))))

; (ec-divisor-sum P x D) → точка 'O | (x y) | skip (кривая не deg 3 над ℚ или места не над ℚ) | #f
(define (ec-divisor-sum P x D)
  (let ((co (ec-coeffs P x)))
    (if co (ec-divisor-sum-co co (dv-normalize D)) 'skip)))

; (ec-multiples P x D n) → ((1 T) (2 (x y)) … (n nT)) | #f
(define (ec-multiples P x D n)
  (let* ((co (ec-coeffs P x)) (T (and co (ec-divisor-sum-co co (dv-normalize D)))))
    (if (and T (not (equal? T 'skip)) (integer? n) (> n 0))
        (let ((ms (ec-multiples-co co T n)))
          (map2 (lambda (k m) (list k m)) (map (lambda (i) (+ i 1)) (range n)) ms))
        #f)))

; (ec-point-order-check P x D n) → #t, если T = Σ nᵢ·Pᵢ имеет в точности порядок n: kT ≠ O (k < n), nT = O;
; #f — иначе (в том числе точка не на кривой, deg D ≠ 0, не deg 3 / не над ℚ)
(define (ec-point-order-check P x D n)
  (let ((ms (and (integer? n) (> n 0) (ec-multiples P x D n))))
    (and ms
         (equal? (cadr (nth ms (- n 1))) 'O)
         (not (any? (lambda (km) (equal? (cadr km) 'O)) (take ms (- n 1)))))))

(define (ec-fmt pt)
  (if (equal? pt 'O) "O" (string-append "(" (to-string (car pt)) ", " (to-string (cadr pt)) ")")))

(define (ec-fmt-k k) (if (= k 1) "T" (string-append (to-string k) "T")))

; сертификат для шага 1.1.5: #f (не выводить) | (ok "текст") | (bad "текст расхождения")
(define (dv-ec-cert Dn P x t ns)
  (let* ((co (ec-coeffs P x))
         (T (and co (try (ec-divisor-sum-co co Dn) (lambda (e) #f)))))
    (cond
      ((not (and T (not (equal? T 'skip)))) #f)
      ((and (pair? t) (= (length t) 2))
       (let* ((n (car t)) (ms (ec-multiples-co co T n))
              (zero-at (let loop ((ks ms) (k 1)) (cond ((null? ks) #f) ((equal? (car ks) 'O) k) (else (loop (cdr ks) (+ k 1)))))))
         (cond ((equal? zero-at n)
                (list 'ok (string-append "сертификат (закон сложения на E): "
                                         (alg-join (map2 (lambda (k m) (string-append (ec-fmt-k k) " = " (ec-fmt m)))
                                                        (map (lambda (i) (+ i 1)) (range n)) ms)
                                                   "; ")
                                         " — порядок δ равен " (to-string n))))
               (else
                (list 'bad (string-append "расхождение сертификата: L(D) даёт порядок δ, равный " (to-string n)
                                          ", а закон сложения на E — "
                                          (if zero-at (string-append "kT = O уже при k = " (to-string zero-at)) (string-append "nT ≠ O, nT = " (ec-fmt (nth ms (- n 1)))))
                                          " (T = " (ec-fmt T) ")"))))))
      ((equal? t 'non-torsion)
       (let* ((top (apply max ns)) (ms (ec-multiples-co co T top))
              (bad-ks (filter (lambda (k) (equal? (nth ms (- k 1)) 'O)) ns))
              (bad-k (and (pair? bad-ks) (car bad-ks))))
         (if bad-k
             (list 'bad (string-append "расхождение сертификата: L(D) не находит порядка (n·δ не главный при n ∈ {" (alg-join (map to-string ns) ", ")
                                       "}), а закон сложения на E — " (ec-fmt-k bad-k) " = O (T = " (ec-fmt T) ")"))
             (list 'ok (string-append "сертификат (закон сложения на E): T = " (ec-fmt T)
                                      (apply string-append
                                             (map (lambda (k) (let ((s (ec-fmt (nth ms (- k 1)))))
                                                                (string-append "; " (ec-fmt-k k)
                                                                               (if (> (string-length s) 60) "" (string-append " = " s)))))
                                                  (filter (lambda (k) (> k 1)) ns)))
                                      "; kT ≠ O для всех k | B = " (to-string top) " — δ не кручение")))))
      (else #f))))

; ---------- R5.3b: Кантор в решении «кручение / не кручение» (род ≥ 2, нечётная степень, места над ℚ) ----------

; многочлен (список коэффициентов) → строка; нуль группы — «O», длинная пара — только степени
; коэффициенты над K = ℚ(√d): пара (a b) → выражение a + b√d
(define (dv-ck-poly->expr cs x d)
  (simplify (cons '+ (let loop ((cs cs) (i 0) (acc '()))
                       (if (null? cs)
                           (reverse acc)
                           (loop (cdr cs) (+ i 1)
                                 (cons (list '* (dv-k->expr (list (cons '() (car (car cs))) (cons (list d) (cadr (car cs)))))
                                             (list '^ x i))
                                       acc)))))))

(define (dv-cn-pair x D &rest ds)
  (if (and (null? (cdr (car D))) (null? (cadr D)))
      "O"
      (let* ((d (and (pair? ds) (car ds)))
             (pe (lambda (cs) (if (null? cs) "0" (alg-mp (if d (dv-ck-poly->expr cs x d) (ib-poly->expr cs x))))))
             (s (string-append "(" (pe (car D)) ", " (pe (cadr D)) ")")))
        (if (> (string-length s) 120)
            (string-append "(deg u = " (to-string (- (length (car D)) 1)) ", deg v = " (to-string (- (length (cadr D)) 1)) ")")
            s))))

; таблица kδ, k = 1..m, парами Мамфорда (m ≤ 12) — только для шага
(define (dv-cn-table Dn P x m &rest ev)
  (let* ((even-model (and (pair? ev) (> (length (car ev)) 5) (nth (car ev) 5)))
         (d (and (pair? ev) (> (length (car ev)) 6) (car (nth (car ev) 6))))
         (ms (if (<= m 12) (if d (cantor-multiples P x Dn m d) (cantor-multiples P x Dn m)) #f))
         (xv (if even-model 'z x)))
    (if ms
        (string-append (if even-model "; kδ в модели w² = Q(z) — пары Мамфорда (u, v): " "; kδ — пары Мамфорда (u, v): ")
                       (alg-join (map (lambda (km) (string-append (to-string (car km)) "δ = " (dv-cn-pair xv (cadr km) d))) ms) "; "))
        "")))

; текст про p, q и точную проверку; r — результат cantor-torsion-check
(define (dv-cn-model-note r)
  (if (and (> (length r) 5) (nth r 5))
      (string-append "замена x = " (if (= 0 (car (nth r 5))) "1/z" (string-append (to-string (car (nth r 5))) " + 1/z"))
                     ": w² = Q(z) = " (alg-mp (cadr (nth r 5)))
                     "; точки δ перенесены: (x₀, y₀) ↦ (1/(x₀ − a), y₀/(x₀ − a)^(g+1)), (a, 0) ↦ ∞, ∞± ↦ (0, ±√lc);"
                     " порядок и главность δ сохраняются при бирациональном изоморфизме; ")
      ""))

; R5.3c2: текст про Кантор над K = ℚ(√d) (r — результат cantor-torsion-check с d)
(define (dv-cn-sq kd q)
  (let ((pr (assoc q (nth kd 1))))
    (string-append "√" (to-string (car kd)) " ≡ " (if pr (to-string (cdr pr)) "?") " mod " (to-string q))))

(define (dv-cn-evidence-k r)
  (let* ((p (nth r 1)) (m (nth r 2)) (qs (nth r 3)) (ms (to-string m)) (kd (nth r 6)) (d (car kd)))
    (string-append
     (dv-cn-model-note r)
     (if (equal? (nth r 4) 'bound)
         (string-append "Кантор над ℚ(√" (to-string d) "): B·δ mod 𝔭: ≠ 0 (B = " ms ", p = " (to-string p) ", " (dv-cn-sq kd p)
                        ") ⇒ δ не кручение (порядок кручения делит B)")
         (string-append "Кантор над ℚ(√" (to-string d) "): ord_𝔭(δ) = " ms " (p = " (to-string p) ", " (dv-cn-sq kd p) ")"))
     (cond ((equal? (nth r 4) 'bound) "")
           ((equal? (car r) 'non-torsion)
            (if (= (nth r 4) 0)
                (string-append (if (null? qs) ""
                                   (string-append "; " ms "·δ mod 𝔮: 0 (" (alg-join (map (lambda (q) (string-append "q = " (to-string q) ", " (dv-cn-sq kd q))) qs) "; ") ")"))
                               "; над K: " ms "·δ ≠ 0 ⇒ δ не кручение (иначе " ms "·δ = 0 над K)")
                (string-append "; " ms "·δ mod 𝔮: ≠ 0 (q = " (to-string (nth r 4)) ", " (dv-cn-sq kd (nth r 4))
                               (if (and (nth r 4) (assoc (nth r 4) (nth kd 1)) (< (nth r 4) p)) (string-append "; ord_𝔮(δ) > " (to-string (nth kd 2))) "")
                               ") ⇒ δ не кручение (иначе " ms "·δ = 0 над K и по модулю q)")))
           (else
            (string-append (if (null? qs)
                               "; проверка по модулю q не проводилась (нет хороших q ≤ 300)"
                               (string-append "; " ms "·δ mod 𝔮: 0 (" (alg-join (map (lambda (q) (string-append "q = " (to-string q) ", " (dv-cn-sq kd q))) qs) "; ") ")"))
                           (if (nth r 4)
                               (string-append "; над K: " ms "·δ = 0 ⇒ порядок δ равен " ms)
                               "; над K проверка опущена (порядок велик)")))))))

(define (dv-cn-evidence r)
  (if (and (> (length r) 6) (nth r 6))
      (dv-cn-evidence-k r)
      (dv-cn-evidence-q r)))

(define (dv-cn-evidence-q r)
  (let* ((p (nth r 1)) (m (nth r 2)) (qs (nth r 3)) (ms (to-string m)))
    (string-append
     (dv-cn-model-note r)
     "Кантор: ord_p(δ) = " ms " (p = " (to-string p) ")"
     (cond ((equal? (car r) 'non-torsion)
            (if (= (nth r 4) 0)
                (string-append (if (null? qs) "" (string-append "; " ms "·δ mod q: 0 (q = " (alg-join (map to-string qs) ", ") ")"))
                               "; над ℚ: " ms "·δ ≠ 0 ⇒ δ не кручение (иначе " ms "·δ = 0 над ℚ)")
                (string-append "; " ms "·δ mod q: ≠ 0 (q = " (to-string (nth r 4)) ") ⇒ δ не кручение (иначе "
                               ms "·δ = 0 над ℚ и по модулю q)")))
           (else
            (string-append (if (null? qs)
                               "; проверка по модулю q не проводилась (нет хороших q ≤ 200)"
                               (string-append "; " ms "·δ mod q: 0 (q = " (alg-join (map to-string qs) ", ") ")"))
                           (if (nth r 4)
                               (string-append "; над ℚ: " ms "·δ = 0 ⇒ порядок δ равен " ms)
                               "; над ℚ проверка опущена (порядок велик)")))))))

(define (dv-cn-just r)
  (if (and (> (length r) 6) (nth r 6))
      "; обоснование: p расщепляется в K, простой 𝔭 | p имеет степень 1 и поле вычетов 𝔽_p; редукция по 𝔭 (p > 2, неразветвлённо) инъективна на кручении J(K), поэтому порядок кручения n = ord_𝔭(δ)"
      "; обоснование: редукция по хорошему p > 2 инъективна на кручении J(ℚ), поэтому порядок кручения n = ord_p(δ)"))

(define (dv-note-cantor Dn P x r pr)
  (if (equal? (car r) 'non-torsion)
      (let ((s (dv-cn-evidence r)))
        (set! alg-why (string-append s " — по Трагеру ∫ неэлементарен"))
        (alg-step 'alg-principal "Проверка главности n·δ"
                  (string-append s (dv-cn-just r))
                  (cons 'list (nth r 3)) 'non-torsion))
      (let* ((m (nth r 2)) (found (and (pair? pr) (equal? (car pr) 'principal))))
        (alg-step 'alg-principal "Проверка главности n·δ"
                  (string-append (dv-cn-evidence r)
                                 (dv-cn-just r)
                                 (if found
                                     (string-append "; найдена функция u с div u = " (to-string m) "·δ")
                                     (string-append "; функция u с div u = " (to-string m) "·δ не найдена (расхождение с Кантором)"))
                                 (dv-cn-table Dn P x m r))
                  (cons 'list (list m)) (if found (list m (cadr pr)) 'unknown)))))

; Кантор для δ: #f — не применимо (старый путь); 'non-torsion-proved; (n u); 'unknown (расхождение с Кантором — условие записано)
(define (dv-cantor-order Dn P x)
  (let ((r (cantor-torsion-check P x Dn)))
    (cond
      ((not r) #f)
      ((equal? (car r) 'non-torsion)
       (begin (if alg-log? (dv-note-cantor Dn P x r #f))
              'non-torsion-proved))
      (else
       (let* ((m (nth r 2)) (pr (hyp-principal (dv-scale Dn m) P x))
              (found (and (pair? pr) (equal? (car pr) 'principal))))
         (cond
           (found
            (if alg-log? (dv-note-cantor Dn P x r pr))
            (list m (cadr pr)))
           ((nth r 4)   ; m·δ = 0 над ℚ проверено, а L(D) функции не нашёл
            (record-condition (list 'cantor-principal-mismatch m (nth r 1) (if (equal? pr 'unknown) 'L-unknown 'L-not-principal))
                              (string-append "Кантор: m·δ = 0 над ℚ при m = " (to-string m) ", но поиск функции u (L(−m·δ)) её не нашёл"))
            (if alg-log? (dv-note-cantor Dn P x r pr))
            'unknown)
           (else #f)))))))

; R5.3c2: то же для вычетов в K = ℚ(√d) — Кантор над K (порядок по расщеплённому p, √d ↦ s mod p); функция u — hyp-principal-ev
(define (dv-cantor-order-ev Dn P x d)
  (let* ((r0 (try (cantor-torsion-check P x Dn d) (lambda (e) #f)))     ; сначала перебор k·δ (дёшево); граница B (дорогой подсчёт точек) — только если порядок не найден
         (r (if (and r0 (equal? (car r0) 'order-large))
                (let ((B (hyp-torsion-bound-ev P x d)))
                  (if (integer? B) (try (cantor-torsion-check P x Dn d B) (lambda (e) #f)) r0))
                r0)))
    (cond
      ((not r) #f)
      ; ord_𝔭(δ) > N у всех просмотренных p, граница B неизвестна: кручения порядка ≤ N нет; старый путь (n ≤ 12) дал бы то же unknown
      ((equal? (car r) 'order-large)
       (begin
         (if alg-log?
             (let* ((kd (nth r 6)) (N (to-string (nth kd 2))))
               (alg-step 'alg-principal "Проверка главности n·δ"
                         (string-append (dv-cn-model-note r)
                                        "Кантор над ℚ(√" (to-string d) "): k·δ ≠ 0 по модулю 𝔭 при всех k ≤ " N " ("
                                        (alg-join (map (lambda (pr) (string-append "p = " (to-string (car pr)) ", " (dv-cn-sq kd (car pr)))) (nth kd 1)) "; ")
                                        "); кручение порядка ≤ " N " исключено, порядок не определён (граница кручения B неизвестна) — не знаю")
                         (cons 'list (nth r 3)) 'unknown)))
         'unknown))
      ((equal? (car r) 'non-torsion)
       (begin (if alg-log? (dv-note-cantor Dn P x r #f))
              'non-torsion-proved))
      (else
       (let* ((m (nth r 2)) (pr (hyp-principal-ev (dv-scale Dn m) P x d))
              (found (and (pair? pr) (equal? (car pr) 'principal))))
         (cond
           (found
            (if alg-log? (dv-note-cantor Dn P x r pr))
            (list m (cadr pr)))
           ((nth r 4)   ; m·δ = 0 над K проверено, а L(D) над K функции не нашёл
            (record-condition (list 'cantor-principal-mismatch m (nth r 1) (if (equal? pr 'unknown) 'L-unknown 'L-not-principal))
                              (string-append "Кантор над ℚ(√d): m·δ = 0 при m = " (to-string m) ", но поиск функции u (L(−m·δ)) её не нашёл"))
            (if alg-log? (dv-note-cantor Dn P x r pr))
            'unknown)
           (else #f)))))))

; внутренний вариант: 'non-torsion-proved отличается от 'non-torsion (последний требует известной границы B)
(define (hyp-torsion-order D P x)
  (let ((t (hyp-torsion-order* D P x)))
    (if (equal? t 'non-torsion-proved) 'non-torsion t)))

(define (hyp-torsion-order* D P x)
  (let ((Dn (dv-normalize D)))
    (cond ((not (equal? (dv-divisor-ok? D P x) #t)) #f)
          ((not (= 0 (dv-degree Dn))) 'non-torsion)
          (else
           (let ((cr (dv-cantor-order Dn P x)))
             (if cr cr (hyp-torsion-order-old Dn P x)))))))

; прежний путь: n | B (граница по #J(𝔽_p)) или n ≤ 12, hyp-principal на каждом n; сертификат ST.1c для рода 1
(define (hyp-torsion-order-old Dn P x)
  (let ((B (hyp-torsion-bound P x)))
    (let* ((known (not (equal? B 'unknown)))
           (ns (if known (divisors B) (map (lambda (i) (+ i 1)) (range 12))))
           (t (dv-torsion-search Dn P x ns known))
           (cert (if (or (and (pair? t) (= (length t) 2)) (and known (equal? t 'non-torsion)))
                     (dv-ec-cert Dn P x t ns)
                     #f)))
      (if alg-log?
          (begin (dv-note-bound P x B)
                 (dv-note-principal Dn t ns B (and cert (equal? (car cert) 'ok) (cadr cert)))))
      (if (and cert (equal? (car cert) 'bad))
          (begin
            (record-condition (list 'torsion-certificate-mismatch t B) (cadr cert))
            (if alg-log? (alg-step 'alg-principal "Проверка главности n·δ" (cadr cert) 'unknown 'unknown))
            'unknown)
          t))))

; ---------- z-модель: x = 1/z (нули на ∞) ----------
;
; u = (c₀ + c₁y)/g с g от x не может иметь нулей на ∞ (многочлен от x, y там
; только полюсы). Для дивизоров с n_P > 0 на ∞ переходим в z-модель:
; z = 1/x, w = y·z^{n/2}, Q(z) = z^n·P(1/z) (n чётно, Q(0) = lc);
; места ∞ ↦ (0, ±√lc), конечные a ↦ (1/a, b·a^{−n/2}).

(define (dv-inf-zero? D P x)
  (let ((inf (hyp-places P x 'inf)))
    (if (equal? inf 'unknown)
        'unknown
        (any? (lambda (pl) (> (dv-dv-n-at D pl) 0)) inf))))

(define (dv-zmodel D P x)
  (let* ((n (try (degree P x) (lambda (e) 0)))
         (pl (ib-poly-parse P x)))
    (cond
      ((or (equal? pl #f) (not (even? n)) (null? pl)) 'unknown)
      ((any? (lambda (pr) (and (not (equal? (car (car pr)) 'inf))
                               (= 0 (car (car pr)))))
             D)
       'unknown)
      (else
       (let* ((h (quotient n 2))
              (Q (reverse pl))   ; коэффициент при z^k равен p_{n−k}
              (Dz (map (lambda (pr)
                         (let ((a (car (car pr))) (b (cadr (car pr))) (m (cdr pr)))
                           (cond ((equal? a 'inf) (cons (list 0 b) m))
                                 ((equal? b 'ram) (cons (list (/ 1 a) 'ram) m))
                                 (else (cons (list (/ 1 a) (ib-k-scale b (dv-pow a (- h))))
                                             m)))))
                       D)))
         (cons (dv-normalize Dz) (ib-poly->expr Q 'z)))))))

; обратная замена z = 1/x, w = y·x^{−h}
(define (dv-zmodel-back e h x)
  (simplify (subst (list (list 'z (list '/ 1 x))
                         (list 'y (list '* 'y (list '^ x (- h)))))
                   e)))

; ---------- Шаг A5.4: сборка Трагера для y² = P ----------
;
; H — остаток после Эрмита: полюсы простые. Если вычеты есть, δ = Σ m·r·P —
; дивизор с целыми коэффициентами; если n·δ главен с div u = n·δ, то
; H dx = (1/(m n))·d(log u) + (голоморфное) — проверяется точно (alg-nf).
; Все условия §1.6 обязательны для nonelementary.

(define (dv-split-rational? D x)
  (let ((fs (try (factor-list D) (lambda (e) #f))))
    (and (pair? fs)
         (every? (lambda (pe) (= 1 (try (degree (car pe) x) (lambda (e) -1))))
                 (cdr fs)))))

; нормальная форма для y² = P с произвольным знаменателем по y:
; знаменатель d = (a₀ + a₁y)/D, обратный = D·(a₀ − a₁y)/(a₀² − a₁²P) — знаменатель без y
(define (dv-hyp-nf e P x)
  (let ((direct (try (alg-nf e P 2 x) (lambda (err) #f))))
    (if (and (pair? direct) (pair? (car direct)))
        direct
        (let ((sd (try (alg-split-full e) (lambda (err) #f))))
          (if (or (equal? sd #f) (not (pair? sd)))
              'unknown
              (let* ((num (car sd)) (den (cdr sd))
                     (nd (try (alg-nf den P 2 x) (lambda (err) #f))))
                (cond
                  ((or (equal? nd #f) (not (pair? nd))) 'unknown)
                  ((equal? (simplify den) 1) direct)
                  (else
                   (let* ((nv (car nd)) (D (cdr nd))
                          (a0 (nth nv 0)) (a1 (nth nv 1)))
                     (if (not (equal? (length nv) 2))
                         'unknown
                         (let* ((norm (simplify (list '- (list '^ a0 2)
                                                      (list '* (list '^ a1 2) P))))
                                (e2 (simplify (list '/ (list '* num D
                                                            (list '- a0 (list '* a1 'y)))
                                                    norm)))
                                (r (try (alg-nf e2 P 2 x) (lambda (err) #f))))
                           (if (and (pair? r) (pair? (car r))) r 'unknown))))))))))))

; разность тождественно 0 в нормальной форме (вектор alg-nf нулевой)
(define (dv-nf-zero? e P x)
  (let ((nf (dv-hyp-nf e P x)))
    (if (or (equal? nf 'unknown) (not (pair? nf)))
        #f
        (every? (lambda (p) (equal? (simplify p) 0)) (car nf)))))

; элемент по нормальной форме: (b₀ + b₁y)/D
(define (dv-nf-expr nf)
  (let ((vec (car nf)) (D (cdr nf)))
    (simplify (list '/ (list '+ (nth vec 0) (list '* (nth vec 1) 'y)) D))))

; Шаг A5.4b: голоморфность H·dx (y² = P) — нормальная форма + проверка alg-holomorphic-check
(define (hyp-holomorphic? H P x)
  (if (equal? (simplify H) 0)
      #t
      (let ((nf (dv-hyp-nf H P x)))
        (if (or (equal? nf 'unknown) (not (pair? nf)))
            'unknown
            (try (alg-holomorphic-check (dv-nf-expr nf) P 2 x)
                 (lambda (err) 'unknown))))))

; производная вдоль кривой: y′ = P′/(2y), а не частная по x
(define (dv-crv-deriv u P x)
  (let ((v (try (alg-der-e u P 2 x) (lambda (err) #f))))
    (if (and v (pair? v))
        v
        ; элемент с коэффициентами в ℚ(√d): alg-der-e рассчитан на ℚ, берём
        ; ∂/∂x + y′·∂/∂y напрямую (√d — константа, diff её не трогает)
        (let ((du (try (simplify (list '+ (diff x u)
                                        (list '* (simplify (list '/ (diff x P) (list '* 2 'y)))
                                              (diff 'y u))))
                       (lambda (err) #f))))
          (if (and du (pair? du)) du #f)))))

; ---------- Шаг A5.4c: дифференциал 2-го рода и полюс порядка ≥ 2 на ∞ ----------
; ω = H dx без конечных полюсов ⇔ H = U + V/y, U, V ∈ ℚ[x] (dx — нуль только в
; ветвлении, а там v(U) чётно; dx/y — единица во всех конечных точках).
; Точные дифференциалы: d(C + S·y) = C′dx + M(S)·dx/y, M(S) = P·S′ + (P′/2)·S.
; Для нечётной d = deg P: deg M(S) ≥ d−1, значит после снятия старших членов
; остаток Q имеет deg ≤ d−2 = 2g−1; Q = 0 ⇔ ω точный (иначе ω ≠ 0 в H¹).

(define (dv-mpoly S P x)
  (expand (list '+ (list '* P (diff x S)) (list '* 1/2 (diff x P) S))))

(define (dv-second-kind-remainder V P x)
  (let ((d (try (degree P x) (lambda (e) -1))))
    (if (< d 1)
        'unknown
        (let loop ((V (expand V)) (guard 0))
          (let ((m (try (degree V x) (lambda (e) -1))))
            (cond ((or (not (integer? m)) (equal? (simplify V) 0)) 0)
                  ((< m (- d 1)) V)
                  ((> guard 200) 'unknown)
                  (else
                   (let* ((k (- m (- d 1)))
                          (c (simplify (list '/ (list '* -1 (coeff V x m))
                                             (list '* (coeff P x d) (+ k (/ d 2)))))))
                     (loop (expand (list '+ V (dv-mpoly (list '* c (list '^ x k)) P x)))
                           (+ guard 1))))))))))

; H dx = U dx + V dx/y при U, V ∈ ℚ[x]; иначе (есть конечные полюсы) — unknown
(define (dv-poly-diff H P x)
  (let ((nf (dv-hyp-nf H P x)))
    (if (or (equal? nf 'unknown) (not (pair? nf)))
        'unknown
        (let* ((vec (car nf)) (D (cdr nf))
               (U (simplify (list '/ (nth vec 0) D)))
               (V (simplify (list '/ (list '* (nth vec 1) P) D))))
          (if (and (polynomial? U x) (polynomial? V x))
              (cons U V)
              'unknown)))))

; #t — ω = H dx точный (2-й род снимается), #f — ненулевой класс H¹, unknown
(define (hyp-second-kind? H P x)
  (let ((uv (dv-poly-diff H P x)))
    (if (equal? uv 'unknown)
        'unknown
        (let ((d (try (degree P x) (lambda (e) -1))))
          (cond ((or (not (integer? d)) (= 0 (modulo d 2))) 'unknown)
                (else
                 (let ((q (dv-second-kind-remainder (cdr uv) P x)))
                   (cond ((equal? q 'unknown) 'unknown)
                         ((equal? (simplify q) 0) #t)
                         (else #f)))))))))

; остаток = c·dx/y (U = 0, V = c — ненулевая константа) → c; иначе #f (только для пояснения шага)
(define (dv-first-kind-multiple rest P x)
  (let ((uv (try (dv-poly-diff rest P x) (lambda (e) 'unknown))))
    (and (pair? uv)
         (equal? (simplify (car uv)) 0)
         (let ((c (simplify (cdr uv))))
           (and (number? c) (not (= c 0)) c)))))

; ответ по найденному кручению: H = (1/(m n))·(log u)′, иначе unknown
(define (dv-log-answer H P x m n u)
  (let ((du (dv-crv-deriv u P x)))
    (if (not du)
        'unknown
        (let* ((up (simplify (list '/ du u)))
               (rest (simplify (together (list '- H (list '* (/ 1 (* m n)) up))))))
          (cond ((dv-nf-zero? rest P x)
                 (list 'logs m (list (list 1 n u))))
                ; остаток без вычетов и голоморфен, но не 0 — неэлементарен (§1.6)
                ((equal? (hyp-holomorphic? rest P x) #t)
                 (begin
                   (if alg-log?
                       (let ((c (dv-first-kind-multiple rest P x)))
                         (set! alg-why
                               (if c
                                   (string-append "дивизор вычетов — кручение (n = " (to-string n) "), но остаток H − (1/" (to-string (* m n))
                                                  ")·u′/u = (" (to-string c) ")·dx/y — дифференциал 1-го рода (голоморфный во всех точках, ненулевой)"
                                                  " — первообразной нет (Лиувилль, Трагер гл. 5)")
                                   (string-append "дивизор вычетов — кручение (n = " (to-string n) "), но остаток H − (1/" (to-string (* m n))
                                                  ")·u′/u голоморфен и не равен 0 — первообразной нет (1-й род, Лиувилль, Трагер гл. 5)")))))
                   'nonelementary))
                ; остаток 2-го рода с ненулевым классом (полюс ≥ 2 на ∞) — A5.4c
                ((equal? (hyp-second-kind? rest P x) #f)
                 (begin
                   (if alg-log?
                       (set! alg-why (string-append "дивизор вычетов — кручение (n = " (to-string n) "), но у остатка H − (1/" (to-string (* m n))
                                                    ")·u′/u неснимаемый полюс порядка ≥ 2 на ∞ (ненулевой класс 2-го рода) — первообразной нет")))
                   'nonelementary))
                (else 'unknown))))))

; ---------- Шаг A5.5b: чётный случай ℚ(√d) ----------
; Вычеты ±c√d в сопряжённых местах (σ: √d ↦ −√d): дивизор δ = Σ c·P антиинвариантен
; (σ(δ) = −δ). Главность ищется над ℚ(√d); ответ — (√d/(2mn))·log(u/ū): множитель 1/2
; потому что u/ū удваивает нормирования (div(u/ū) = 2·div u при div ū = −div u).

; сопряжение места: у b меняется знак; ram и рациональные b неподвижны
(define (dv-conj-place pl)
  (let ((b (cadr pl)))
    (if (or (equal? b 'ram) (not (equal? (dv-k->rat b) #f)))
        pl
        (list (car pl) (dv-k-neg b)))))

(define (dv-conj-divisor D)
  (dv-normalize (map (lambda (pr) (cons (dv-conj-place (car pr)) (cdr pr))) D)))

(define (dv-div-eq? a b)
  (and (= (length a) (length b))
       (every? (lambda (pr)
                 (let ((q (dv-place-assoc (car pr) b)))
                   (and q (= (cdr q) (cdr pr)))))
               a)))

(define (dv-anti-invariant? D)
  (dv-div-eq? (dv-conj-divisor D) (dv-scale D -1)))

; √d по выражению коэффициента (√d без числового множителя); иначе #f
(define (dv-sqrt-radicand q)
  (let ((q (simplify q)))
    (if (and (pair? q) (equal? (car q) '^) (= (length q) 3)
             (equal? (nth q 2) 1/2) (integer? (nth q 1)) (> (nth q 1) 1))
        (nth q 1)
        #f)))

; элемент ib-k лежит в ℚ(√d)?
(define (dv-k-in-qd? el d)
  (every? (lambda (t) (or (null? (car t)) (equal? (car t) (list d)))) el))

; сопряжение √d ↦ −√d в выражении (квадратичные радикалы меняют знак)
(define (dv-conj-expr e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) '^) (= (length e) 3) (equal? (nth e 2) 1/2)
              (number? (nth e 1)))
         (list '- (list '^ (nth e 1) 1/2)))
        (else (cons (car e) (map dv-conj-expr (cdr e))))))

; строки условий над ℚ(√d): элемент e₁ + e₂√d при неизвестном a + b√d даёт две ℚ-строки
;   (e₁·a + d·e₂·b, e₂·a + e₁·b); неизвестные — [a₀…a_{N−1}, b₀…b_{N−1}]
(define (dv-l-rows-ev rows d)
  (foldl (lambda (acc row)
           (let ((pairs (map (lambda (el)
                               (cons (ib-k-coeff el '()) (ib-k-coeff el (list d))))
                             row)))
             (cons (append (map car pairs)
                           (map (lambda (pr) (* d (cdr pr))) pairs))
                   (cons (append (map cdr pairs) (map car pairs)) acc))))
         '() rows))

(define (dv-l-kernel->expr-ev v nunks dc0 dc1 groups x d)
  (let* ((cf (lambda (j) (ib-k-add-term (dv-k-rat (nth v j)) (list d) (nth v (+ nunks j)))))
         (c0s (map (lambda (k) (cf k)) (range (+ dc0 1))))
         (c1s (map (lambda (k) (cf (+ dc0 1 k))) (range (+ dc1 1))))
         (c0 (dv-l-poly-expr c0s x))
         (c1 (dv-l-poly-expr c1s x))
         (g (ib-poly->expr (dv-l-g groups x) x)))
    (simplify (list '/ (simplify (list '+ c0 (list '* c1 'y))) g))))

; L(D) над ℚ(√d): те же группы и границы, что в dv-l-basis, но неизвестные в ℚ(√d)
(define (dv-l-basis-ev D P x d margin)
  (let ((Dn (dv-normalize D)))
    (if (not (every? (lambda (pr) (integer? (cdr pr))) Dn))
        'unknown
        (let ((groups (dv-l-groups Dn P x)))
          (if (equal? groups 'unknown)
              'unknown
              (let ((bd (dv-l-bounds groups Dn P x margin)))
                (if (equal? bd 'unknown)
                    'unknown
                    (let* ((dc0 (car bd))
                           (dc1 (cadr bd))
                           (nunks (+ (+ dc0 1) (+ dc1 1)))
                           (rows (dv-l-rows groups Dn P x dc0 dc1)))
                      (if (or (equal? rows 'unknown)
                              (not (every? (lambda (row)
                                             (every? (lambda (el) (dv-k-in-qd? el d)) row))
                                           rows)))
                          'unknown
                          (let* ((qrows (dv-l-rows-ev rows d))
                                 (ker (if (null? qrows)
                                          (map (lambda (j) (dv-unit-vec j (* 2 nunks)))
                                               (range (* 2 nunks)))
                                          (try (fm-nullspace (field-Q) qrows)
                                               (lambda (e) 'unknown)))))
                            (if (equal? ker 'unknown)
                                'unknown
                                (map (lambda (v)
                                       (dv-l-kernel->expr-ev v nunks dc0 dc1 groups x d))
                                     ker))))))))))))

; проверка главности над ℚ(√d): v_P(u) = n_P во всех местах supp D и над ∞
(define (dv-principal-check-ev D u P x)
  (let ((pls (dv-l-all-places D P x)))
    (if (equal? pls 'unknown)
        #f
        (every? (lambda (pl)
                  (let ((v (hyp-valuation pl u P x)))
                    (and (integer? v) (= v (dv-dv-n-at D pl)))))
                pls))))

(define (hyp-principal-ev D P x d)
  (let ((Dn (dv-normalize D)))
    (cond
      ((not (equal? (dv-divisor-ok? Dn P x) #t)) 'unknown)
      ((not (= 0 (dv-degree Dn))) 'not-principal)
      ((equal? (dv-inf-zero? Dn P x) 'unknown) 'unknown)
      ((dv-inf-zero? Dn P x) 'unknown)          ; z-модель с √d не реализована
      (else
       (let ((b (dv-l-basis-ev Dn P x d 2)))
         (cond ((equal? b 'unknown) 'unknown)
               ((null? b) 'not-principal)
               (else
                (let loop ((us b))
                  (if (null? us)
                      'not-principal
                      (if (dv-principal-check-ev Dn (car us) P x)
                          (list 'principal (car us))
                          (loop (cdr us))))))))))))

; граница кручения J(K), K = ℚ(√d): по хорошим нечётным p ∤ d (поле вычетов в K не ветвится, p > 2 — кручение вкладывается).
; Расщеплённое p (jacobi d p = 1): поле вычетов 𝔽_p, порядок #J(𝔽_p) = L_p(1).
; Инертное p (jacobi d p = −1): поле вычетов 𝔽_{p²}, порядок #J(𝔽_{p²}) = L_p(1)·L_p(−1).
; B = НОД по первым двум годным p по возрастанию. Возвращает B или 'unknown.
(define dv-ev-cache '())   ; (ключ . данные) — последняя граница (дорогой подсчёт не повторяется)

(define (hyp-torsion-data-ev P x d)
  (let ((key (list P x d (dv-cap))))
    (if (and (pair? dv-ev-cache) (equal? (car dv-ev-cache) key))
        (cdr dv-ev-cache)
        (let ((r (hyp-torsion-data-ev1 P x d)))
          (set! dv-ev-cache (cons key r))
          r))))

(define (hyp-torsion-data-ev1 P x d)
  (let ((g (max 1 (dv-genus P x))))
    (let loop ((p 3) (found '()))
      (cond ((>= (length found) 2) (reverse found))
            ((or (> p 50) (> (^ p g) (dv-cap))) (if (null? found) 'unknown (reverse found)))     ; R5.2: см. dv-count-cap
            (else
             (let ((jd (jacobi d p)))
               (if (and (not (= jd 0)) (equal? (hyp-good-prime? P x p) #t))
                   (let ((j (if (= jd 1) (hyp-jacobian-order P x p) (hyp-jacobian-order-sq P x p))))
                     (if (equal? j 'unknown)
                         'unknown
                         (loop (next-prime p) (cons (list p (if (= jd 1) 'split 'inert) j) found))))
                   (loop (next-prime p) found))))))))

(define (hyp-torsion-bound-ev P x d)
  (let ((fd (hyp-torsion-data-ev P x d)))
    (if (equal? fd 'unknown)
        'unknown
        (foldl gcd 0 (map (lambda (e) (nth e 2)) fd)))))

(define (dv-torsion-search-ev D P x d ns known?)
  (let loop ((ns ns) (unk #f))
    (cond ((null? ns) (if (and known? (not unk)) 'non-torsion 'unknown))
          (else
           (let ((r (hyp-principal-ev (dv-scale D (car ns)) P x d)))
             (cond ((and (pair? r) (equal? (car r) 'principal))
                    (list (car ns) (cadr r)))
                   ((equal? r 'unknown) (loop (cdr ns) #t))
                   (else (loop (cdr ns) unk))))))))

(define (hyp-torsion-order-ev D P x d)
  (let ((Dn (dv-normalize D)))
    (cond ((not (equal? (dv-divisor-ok? Dn P x) #t)) #f)
          ((not (= 0 (dv-degree Dn))) 'non-torsion)
          (else
           (let ((cr (dv-cantor-order-ev Dn P x d)))       ; R5.3c2: Кантор над K; #f — старый путь
             (if cr
                 cr
                 (let* ((B (hyp-torsion-bound-ev P x d))
                        (t (if (equal? B 'unknown)
                               (dv-torsion-search-ev Dn P x d (map (lambda (i) (+ i 1)) (range 12)) #f)
                               (dv-torsion-search-ev Dn P x d (divisors B) #t))))
                   (if alg-log? (dv-note-bound-ev P x d))
                   t)))))))

; ---------- Шаг A5.6: полюсы над неприводимыми g(x) степени ≥ 2 ----------
; Случай P ≡ b² (mod g), b ∈ ℚ: над каждым корнем α (g(α) = 0) два места (α, ±b);
; P(α) = b² ≠ 0, поэтому x — локальный параметр. Ряды в s = x − α имеют коэффициенты
; в ℚ(α) (элемент — список по возрастанию степеней α с редукцией по g).
; Ответ ищется над ℚ: u = (c₀(x) + c₁(x)y)/gden, условия v_P(u) ≥ e — линейная система над ℚ.

(define (dv-a-mod a g)
  (cond ((null? a) '())
        ((ib-p-zero? a) '())
        (else (nth (ib-p-divmod a g) 1))))

(define (dv-a-inv a g)
  (if (ib-p-zero? a)
      #f
      (let* ((r (ib-p-egcd a g)) (gg (car r)) (s (cadr r)))
        (if (or (not (= 0 (ib-p-deg gg))) (ib-p-zero? gg))
            #f
            (dv-a-mod s g)))))

(define (dv-a-const a)
  (cond ((ib-p-zero? a) 0)
        ((= 0 (ib-p-deg a)) (car a))
        (else #f)))

(define (dv-a-pow a n g)
  (let loop ((k 0) (r (list 1)))
    (if (= k n) r (loop (+ k 1) (dv-a-mod (ib-p-mul r a) g)))))

; C(j,r)·α^{j−r} mod g (0 при r > j)
(define (dv-a-monom j r g)
  (if (> r j)
      '()
      (dv-a-mod (ib-p-scale (dv-a-pow (list 0 1) (- j r) g) (dv-binom j r)) g)))

; коэффициенты ряда y(s) ветви b ∈ ℚ(α): y_0 = b, y_r = (P_r − Σ y_i y_{r−i})/(2b) mod g
(define (dv-y-series g P x b N)
  (let* ((gg (try (ib-poly-parse g x) (lambda (e) #f)))
         (pp (try (ib-poly-parse P x) (lambda (e) #f)))
         (inv2b (and gg (not (ib-p-zero? b))
                     (dv-a-inv (dv-a-mod (ib-p-scale b 2) gg) gg))))
    (if (or (equal? gg #f) (equal? pp #f) (not inv2b))
        'unknown
        (let loop ((r 1) (pk (dv-p-deriv pp)) (ys (list b)))
          (if (> r N)
              ys                                  ; y_0 … y_N (индекс = порядок)
              ; pk = P^{(r)}/r!  (R1-хвост: раньше делилось на r, а не на r! — ряд верен лишь до порядка 2)
              (let* ((Pr (dv-a-mod pk gg))
                     (sm (let s ((i 1) (acc '()))
                           (if (> i (- r 1)) acc
                               (s (+ i 1)
                                  (ib-p-add acc (dv-a-mod (ib-p-mul (nth ys i) (nth ys (- r i))) gg))))))
                     (yr (dv-a-mod (ib-p-mul (ib-p-sub Pr sm) inv2b) gg)))
                (loop (+ r 1) (ib-p-scale (dv-p-deriv pk) (/ 1 (+ r 1))) (append ys (list yr)))))))))

(define (dv-a-coef el t) (if (> (length el) t) (nth el t) 0))

; элементы строки: коэффициенты при c0_j и c1_j (в ℚ(α))
(define (dv-a-ycoef j r ys g)
  (let loop ((l 0) (acc '()))
    (if (> l r) acc
        (loop (+ l 1)
              (if (>= l (length ys))
                  acc
                  (ib-p-add acc (dv-a-mod (ib-p-mul (dv-a-monom j (- r l) g) (nth ys l)) g)))))))

(define (dv-g-rows g b ys dc0 dc1 e x)
  (let* ((gg (ib-poly-parse g x))
         (d (ib-p-deg gg)))
    (let loop ((r 0) (rows '()))
      (if (>= r e) (reverse rows)
          (let* ((els (append (map (lambda (j) (dv-a-monom j r gg)) (range (+ dc0 1)))
                              (map (lambda (j) (dv-a-ycoef j r ys gg)) (range (+ dc1 1)))))
                 (split (map (lambda (t) (map (lambda (el) (dv-a-coef el t)) els))
                             (range d))))
            (loop (+ r 1) (append (reverse split) rows)))))))

; b ∈ ℚ(α) с b² ≡ P (mod g), α — корень g; возвращает ib-p (b = (list b) для b ∈ ℚ),
; 0 если g | P (ветвление), 'tower если b ∉ ℚ(α) (нужна башня — пока unknown), #f при сбое
(define (dv-g-branch g P x)
  (let ((gg (try (ib-poly-parse g x) (lambda (e) #f)))
        (pp (try (ib-poly-parse P x) (lambda (e) #f))))
    (if (or (equal? gg #f) (equal? pp #f) (< (ib-p-deg gg) 2))
        #f
        (let* ((rem (dv-a-mod pp gg))
               (c (dv-a-const rem)))
          (cond
            ((null? rem) 0)
            ((and c (number? c))
             (let ((k (try (ib-k-sqrt-rat c) (lambda (e) #f))))
               (if (and k (= 1 (length k)) (null? (car (car k))) (> (cdr (car k)) 0))
                   (list (cdr (car k)))
                   ; R1b.1: корня нет в ℚ(α), но c ∈ ℚ — башня ℚ(α)(√c)
                   (let ((r (dv-g-sqrt-mod rem gg g x)))
                     (if (equal? r 'tower) (list 'tower c) r)))))
            (else (dv-g-sqrt-mod rem gg g x)))))))

; квадратный корень c в ℚ[t]/(g): factor-over T² − c; линейный множитель T − b
; (переменная поля у factor-over — t; см. common_pitfall/factor-over-field-variable)
(define (dv-g-sqrt-mod c gg g x)
  (let* ((ge (subst (list (list x 't)) g))
         (ce (ib-poly->expr c 't))
         (alpha (list 'root-of ge 't))
         (fac (try (factor-over (list '- (list '^ 'R1S 2) ce) 'R1S alpha)
                   (lambda (e) #f))))
    (if (not fac)
        'tower
        (let loop ((fs (cdr fac)))
          (if (null? fs)
              'tower
              (let* ((f (car (car fs)))
                     (dg (try (degree f 'R1S) (lambda (e) 0))))
                (if (= dg 1)
                    (let* ((a (simplify (coeff f 'R1S 1)))
                           (bb0 (simplify (coeff f 'R1S 0)))
                           (root (simplify (list '/ (list '* -1 bb0) a)))
                           (rt (replace-expr root alpha 't))
                           (F (try (alg-field ge 't) (lambda (e) #f))))
                      (if (not F)
                          (loop (cdr fs))
                          (let ((bb (try (expr->alg F rt) (lambda (e) #f))))
                            (if (and bb (equal? (dv-a-mod (ib-p-mul bb bb) gg) c))
                                bb
                                (loop (cdr fs))))))
                    (loop (cdr fs)))))))))

; ---------- Шаг R1b.1: башня ℚ(α)(β), β² = c ∈ ℚ ----------
; Элемент башни — пара (r0 r1) = r0 + r1·β, r0,r1 ∈ ℚ(α) (ib-p по модулю g).
; Вычеты хранятся в ℚ-базисе 1, α, …, β, αβ, … (§1.3 проекта).

(define (dv-t2-add a b) (list (ib-p-add (car a) (car b)) (ib-p-add (cadr a) (cadr b))))
(define (dv-t2-neg a) (list (ib-p-neg (car a)) (ib-p-neg (cadr a))))

; умножение по модулю g с β² = c
(define (dv-t2-mul a b gg c)
  (list (dv-a-mod (ib-p-add (ib-p-mul (car a) (car b))
                            (ib-p-scale (ib-p-mul (cadr a) (cadr b)) c)) gg)
        (dv-a-mod (ib-p-add (ib-p-mul (car a) (cadr b)) (ib-p-mul (cadr a) (car b))) gg)))

; 1/(a0+a1β) = (a0−a1β)/(a0² − c·a1²)
(define (dv-t2-inv a gg c)
  (let* ((den (dv-a-mod (ib-p-sub (ib-p-mul (car a) (car a))
                                 (ib-p-scale (ib-p-mul (cadr a) (cadr a)) c)) gg))
         (iv (and (not (ib-p-zero? den)) (dv-a-inv den gg))))
    (if (not iv)
        #f
        (list (dv-a-mod (ib-p-mul (car a) iv) gg)
              (dv-a-mod (ib-p-neg (ib-p-mul (cadr a) iv)) gg)))))

; вычет (c0 + β·c1)/(g′·Drest) в башне: пара (r0 r1) или 'unknown
(define (dv-g-residue-tower c0p c1p Drest gg c)
  (let ((den (dv-a-mod (ib-p-mul (dv-p-deriv gg) Drest) gg)))
    (let ((iv (and (not (ib-p-zero? den)) (dv-a-inv den gg))))
      (if (not iv)
          'unknown
          (list (dv-a-mod (ib-p-mul c0p iv) gg)
                (dv-a-mod (ib-p-mul c1p iv) gg))))))

; рациональное число — полный квадрат?
(define (dv-rat-sq? c)
  (and (rational-number? c) (> c 0)
       (let ((k (ib-k-sqrt-rat c)))
         (and (= 1 (length k)) (null? (car (car k)))))))

(define (dv-tower-entry? d) (and (pair? d) (equal? (nth d 1) 'tower)))

; α — корень квадратного g как элемент ℚ(√d): (p q ключ α-элемент) | #f
(define (dv-g2-alpha g x)
  (let ((gg (try (ib-poly-parse g x) (lambda (e) #f))))
    (if (or (not gg) (not (= 2 (ib-p-deg gg))))
        #f
        (let* ((cs (ib-p-trim gg)) (a (nth cs 2)) (b (nth cs 1)) (c0 (nth cs 0))
               (disc (- (* b b) (* 4 a c0))))
          (if (or (= a 0) (= disc 0))
              #f
              (let ((ak (try (ib-k-parse
                              (list '/ (list '+ (- b) (list '^ disc 1/2)) (* 2 a)))
                             (lambda (e) #f))))
                (if (not ak)
                    #f
                    (let* ((p (let ((t (ib-assoc '() ak))) (if t (cdr t) 0)))
                           (ts (filter (lambda (t) (pair? (car t))) ak)))
                      (if (and (= 1 (length ts)) (= 1 (length (car (car ts)))))
                          (list p (cdr (car ts)) (car (car ts)) ak)
                          #f)))))))))

(define (dv-k-rat-part k)
  (let ((t (ib-assoc '() k))) (if t (cdr t) 0)))

; симметрическая разность ключей (списки простых)
(define (dv-k-symdiff f g)
  (sort (append (filter (lambda (p) (not (ib-member? p g))) f)
                (filter (lambda (p) (not (ib-member? p f))) g))
        <))

; e = A + B·β, β = ccoef·√ckey: (A B)
(define (dv-k-split-beta e ckey ccoef)
  (let loop ((ts e) (a '()) (b '()))
    (if (null? ts)
        (list a b)
        (let* ((f (car (car ts))) (cf (cdr (car ts))))
          (if (odd? (length (dv-inter f ckey)))
              (loop (cdr ts) a (ib-k-add-term b (dv-k-symdiff f ckey) (/ cf ccoef)))
              (loop (cdr ts) (ib-k-add-term a f cf) b))))))

; координаты элемента ℚ(√d) в базисе {1, p + q√d}
(define (dv-k-coords2 e dkey p q)
  (let loop ((ts e) (u 0) (v 0))
    (cond ((null? ts)
           (if (= q 0) #f (let ((a1 (/ v q))) (list (- u (* a1 p)) a1))))
          ((null? (car (car ts)))
           (loop (cdr ts) (+ u (cdr (car ts))) v))
          ((equal? (sort (car (car ts)) <) (sort dkey <))
           (loop (cdr ts) u (+ v (cdr (car ts)))))
          (else #f))))

; многочлен от α (ib-p по модулю g) → элемент ℚ(α) как ib-k
(define (dv-a-eval-k p ak)
  (let loop ((cs (reverse (ib-p-trim p))) (acc '()))
    (if (null? cs)
        acc
        (loop (cdr cs) (ib-k-add (ib-k-mul acc ak) (dv-k-rat (car cs)))))))

; ib-k-коэффициенты → выражение-многочлен по x
(define (dv-k-poly cs x)
  (let loop ((i 0) (acc 0))
    (if (>= i (length cs))
        (simplify acc)
        (loop (+ i 1)
              (simplify (list '+ acc (list '* (dv-k->expr (nth cs i)) (list '^ x i))))))))

; места над квадратичным g: ((i s) . координаты в ℚ-базисе 1,α,β,αβ)
(define (dv-tower-places g c r0 r1 x)
  (let* ((gg (ib-poly-parse g x))
         (ak (dv-g2-alpha g x)))
    (if (not ak)
        'unknown
        (let* ((p (car ak)) (q (cadr ak)) (dkey (caddr ak)) (alpha-k (nth ak 3))
               (r0k (dv-a-eval-k r0 alpha-k))
               (r1k (dv-a-eval-k r1 alpha-k))
               (bk (ib-k-sqrt-rat c))
               (ckey (car (car bk))) (ccoef (cdr (car bk)))
               (conj (lambda (e) (dv-k-conj e dkey))))
          (let loop ((is '((0 1) (0 -1) (1 1) (1 -1))) (acc '()))
            (if (null? is)
                (reverse acc)
                (let* ((pl (car is)) (i (car pl)) (s (cadr pl))
                       (a0 (if (= i 0) r0k (conj r0k)))
                       (b0 (if (= i 0) r1k (conj r1k)))
                       (e (ib-k-add a0 (ib-k-scale (ib-k-mul b0 bk) s)))
                       (sp (dv-k-split-beta e ckey ccoef))
                       (ca (dv-k-coords2 (car sp) dkey p q))
                       (cb (dv-k-coords2 (cadr sp) dkey p q)))
                  (if (or (not ca) (not cb))
                      'unknown
                      (loop (cdr is) (cons (cons pl (append ca cb)) acc))))))))))

; строка длины n из нулей
(define (dv-make-row n) (map (lambda (z) 0) (range n)))

; заменить элемент строки (индекс с нуля)
(define (dv-row-set row idx val)
  (let loop ((i 0) (acc '()))
    (if (>= i (length row))
        (reverse acc)
        (loop (+ i 1) (cons (if (= i idx) val (nth row i)) acc)))))

; 2 строки (real и α) порядка r в месте (i,s); ofs — сдвиг блока неизвестных
(define (dv-tower-block-rows gg i r dc ofs w tr nrm)
  (let loop ((t 0)
             (a (dv-make-row w)) (b (dv-make-row w)))
    (if (> t dc)
        (list a b)
        (let* ((E (dv-a-monom t r gg))
               (e0 (if (> (length E) 0) (nth E 0) 0))
               (e1 (if (> (length E) 1) (nth E 1) 0))
               (e0 (if (= i 0) e0 (+ e0 (* e1 tr))))
               (e1 (if (= i 0) e1 (- e1))))
          (loop (+ t 1)
                (dv-row-set (dv-row-set a (+ ofs (* 2 t)) e0)
                            (+ ofs (* 2 t) 1) (* -1 e1 nrm))
                (dv-row-set (dv-row-set b (+ ofs (* 2 t)) e1)
                            (+ ofs (* 2 t) 1) (+ e0 (* e1 tr)))))))) 

; строки v_P(c0 + c1·y) ≥ e в месте (i,s): блоки c0 и c1 одинаковы
(define (dv-tower-place-rows gg i e dc0 dc1)
  (let* ((cs (ib-p-trim gg))
         (tr (- (/ (nth cs 1) (nth cs 2))))          ; α + ᾱ
         (nrm (/ (nth cs 0) (nth cs 2)))
         (w (+ (* 2 (+ dc0 1)) (* 2 (+ dc1 1))))
         (ofs1 (* 2 (+ dc0 1))))
    (let loop ((r 0) (rows '()))
      (if (>= r e)
          (reverse rows)
          (loop (+ r 1)
                (append (reverse (dv-tower-block-rows gg i r dc0 0 w tr nrm))
                        (reverse (dv-tower-block-rows gg i r dc1 ofs1 w tr nrm))
                        rows))))))

; коэффициенты многочлена из вектора ядра: (c₀ c₁ …) в ℚ(α) как ib-k
(define (dv-tower-kernel-coefs v off dc alpha-k)
  (let loop ((t 0) (lc '()))
    (if (> t dc)
        (reverse lc)
        (loop (+ t 1)
              (cons (ib-k-add (dv-k-rat (nth v (+ off (* 2 t))))
                              (ib-k-scale alpha-k (nth v (+ off (* 2 t) 1))))
                    lc)))))

; u = (c₀ + c₁y)/g^mden с div u = k·delta (одна ℚ-координата) или #f;
; ответ проверяется тем же сертификатом, что и финальный logs.
(define (dv-tower-principal-u H P x m g mden dc0 dc1 delta k gg alpha-k qj)
  (let* ((rows (foldl
                (lambda (acc pr)
                  (let* ((pl (car pr)) (n (cdr pr)) (i (car pl))
                         (e (+ mden (* k n))))
                    (if (<= e 0) acc (append acc (dv-tower-place-rows gg i e dc0 dc1)))))
                '() delta)))
    (if (null? rows)
        #f
        (let ((ker (try (fm-nullspace (field-Q) rows) (lambda (e) 'unknown))))
          (if (equal? ker 'unknown)
              #f
              (let loop ((vs ker))
                (if (null? vs)
                    #f
                    (let* ((v (car vs))
                           (cofs (dv-tower-kernel-coefs v 0 dc0 alpha-k))
                           (cifs (dv-tower-kernel-coefs v (* 2 (+ dc0 1)) dc1 alpha-k))
                           (c0 (dv-k-poly cofs 'x))
                           (c1 (dv-k-poly cifs 'x))
                           (u (simplify (list '/ (simplify (list '+ c0 (list '* c1 'y)))
                                              (list '^ g mden)))))
                      (if (hyp-log-check H P 'x (list 'logs m (list (list qj k u))))
                          u
                          (loop (cdr vs)))))))))))

; лог-часть по ℚ-базису вычетов над квадратичным g (башня, R1b.1)
(define (dv-tower-log-search dat H P x)
  (if (not (and (= 1 (length dat))
                (dv-tower-entry? (car dat))
                (= 2 (ib-p-deg (ib-poly-parse (nth (car dat) 0) x)))))
      'unknown
      (let* ((e0 (car dat))
             (g (nth e0 0)) (c (nth e0 2)) (r0 (nth e0 3)) (r1 (nth e0 4))
             (gg (ib-poly-parse g x))
             (ak (dv-g2-alpha g x))
             (places (if ak (dv-tower-places g c r0 r1 x) 'unknown)))
        (if (not (and ak (list? places)))
            'unknown
            (let* ((m (foldl (lambda (acc pr)
                               (foldl (lambda (a cj) (dv-lcm2 a (denom (together cj))))
                                      acc (cdr pr)))
                             1 places))
                   (pls (map (lambda (pr) (cons (car pr)
                                               (map (lambda (cj) (* m cj)) (cdr pr))))
                             places))
                   (alpha-e (dv-k->expr (nth ak 3)))
                   (beta-e (dv-k->expr (ib-k-sqrt-rat c)))
                   (pq (list 1 alpha-e beta-e (simplify (list '* alpha-e beta-e))))
                   (B (hyp-torsion-bound P x))
                   (known (not (equal? B 'unknown)))
                   (ns (if known (divisors B) (map (lambda (i) (+ i 1)) (range 12)))))
              (let loopj ((j 0) (terms '()) (bad #f) (weak #f))
                (if (> j 3)
                    (cond (bad (if known 'nonelementary 'unknown))
                          (weak 'unknown)
                          ((null? terms) 'unknown)
                          (else
                           (let ((L (list 'logs m (reverse terms))))
                             (if (hyp-log-check H P 'x L) L 'unknown))))
                    (let* ((delta (let build ((ps pls) (acc '()))
                                    (if (null? ps)
                                        (reverse acc)
                                        (let* ((pl (car (car ps))) (cv (cdr (car ps)))
                                               (n (nth cv j)))
                                          (build (cdr ps)
                                                 (if (= n 0) acc (cons (cons pl n) acc)))))))
                           (mden (foldl (lambda (a pr) (max a (max 0 (- (cdr pr))))) 0 delta)))
                      (if (null? delta)
                          (loopj (+ j 1) terms bad weak)
                          (let loopk ((ks ns))
                            (if (null? ks)
                                ; β-компоненты (j ≥ 2) требуют u с коэффициентами в башне —
                                ; без этого поиска вердикт только unknown, не nonelementary
                                (loopj (+ j 1) terms (if (< j 2) #t bad)
                                       (if (< j 2) weak #t))
                                (let ((u (dv-tower-principal-u
                                          H P x m g mden 4 4 delta (car ks) gg
                                          (nth ak 3) (nth pq j))))
                                  (if u
                                      (loopj (+ j 1)
                                             (cons (list (nth pq j) (car ks) u) terms)
                                             bad weak)
                                      (loopk (cdr ks)))))))))))))))

(define (dv-g-residue g b c0p c1p Drest x)
  (let* ((gg (ib-poly-parse g x))
         (N (dv-a-mod (ib-p-add c0p (ib-p-mul c1p b)) gg))
         (den (dv-a-mod (ib-p-mul (dv-p-deriv gg) Drest) gg)))
    (let ((inv (and (not (ib-p-zero? den)) (dv-a-inv den gg))))
      (if (not inv)
          'unknown
          (dv-a-const (dv-a-mod (ib-p-mul N inv) gg))))))

; данные по всем неприводимым множителям знаменателя степени ≥ 2: ((g b r+ r-))
(define (dv-irred-data H P x)
  (let* ((info (dv-nf-info H P x))
         (fl (and info (try (factor-list (dv-nf-Dexpr info)) (lambda (e) #f)))))
    (if (or (not info) (not (pair? fl)))
        'unknown
        (let ((Dp (dv-nf-D info)) (c0p (dv-nf-c0 info)) (c1p (dv-nf-c1 info)))
          (let loop ((fs (cdr fl)) (acc '()))
            (if (null? fs)
                (if (null? acc) 'unknown (reverse acc))
                (let* ((g (car (car fs)))
                       (gg (try (ib-poly-parse g x) (lambda (e) #f))))
                  (if (or (equal? gg #f) (< (ib-p-deg gg) 2))
                      (loop (cdr fs) acc)
                      (let* ((rem (dv-a-mod (ib-poly-parse P x) gg))
                             (c (cond ((null? rem) 0)
                                      ((= 1 (length rem)) (car rem))
                                      (else #f))))
                        (cond
                          ; g | P: корни — точки ветвления, вычеты там нулевые (y — параметр)
                          ((and (number? c) (= c 0)) (loop (cdr fs) acc))
                          (else
                           (let ((b (dv-g-branch g P x)))
                             (cond
                               ((or (not b) (equal? b 'tower)) 'unknown)
                               ; R1b.1: b ∉ ℚ(α), β² = c — вычет в башне
                               ((and (pair? b) (equal? (car b) 'tower))
                                (let* ((cc (cadr b))
                                       (dr (car (ib-p-divmod Dp gg)))
                                       (rr (dv-g-residue-tower c0p c1p dr gg cc)))
                                  (if (equal? rr 'unknown)
                                      'unknown
                                      (loop (cdr fs)
                                            (cons (list g 'tower cc (car rr) (cadr rr))
                                                  acc)))))
                               (else
                                (let* ((dr (car (ib-p-divmod Dp gg)))
                                       (rp (dv-g-residue g b c0p c1p dr x))
                                       (rm (dv-g-residue g (ib-p-neg b) c0p c1p dr x)))
                                  (if (or (equal? rp 'unknown) (equal? rm 'unknown)
                                          (not (= 0 (+ rp rm))))
                                      'unknown
                                      (loop (cdr fs) (cons (list g b rp rm) acc))))))))))))))))))

(define (dv-p-pow a n)
  (let loop ((k 0) (r (list 1)))
    (if (= k n) r (loop (+ k 1) (ib-p-mul r a)))))

; строки условий по всем ветвям при кратности k
(define (dv-irred-rows data k mden dc0 dc1 P x)
  (let loop ((ds data) (acc '()))
    (if (null? ds) (reverse acc)
        (let* ((d (car ds)) (g (nth d 0)) (b (nth d 1))
               (e1 (+ mden (* k (nth d 2))))
               (e2 (+ mden (* k (nth d 3))))
               (N (+ (max 0 e1 e2 1) 1))
               (ys (dv-y-series g P x b N))
               (ysn (if (equal? ys 'unknown) 'unknown (map ib-p-neg ys))))
          (if (equal? ys 'unknown)
              'unknown
              (let ((r1 (if (> e1 0) (dv-g-rows g b ys dc0 dc1 e1 x) '()))
                    (r2 (if (> e2 0) (dv-g-rows g (ib-p-neg b) ysn dc0 dc1 e2 x) '())))
                (loop (cdr ds) (append (reverse r1) (reverse r2) acc))))))))

(define (dv-row-rational row)
  (let ((rs (map dv-k->rat row)))
    (if (member? #f rs) #f rs)))

(define (dv-irred-u v dc0 dc1 gden x)
  (let ((c0 (dv-l-poly-expr (map (lambda (j) (dv-k-rat (nth v j))) (range (+ dc0 1))) x))
        (c1 (dv-l-poly-expr (map (lambda (j) (dv-k-rat (nth v (+ dc0 1 j))))
                                 (range (+ dc1 1))) x)))
    (simplify (list '/ (simplify (list '+ c0 (list '* c1 'y)))
                    (ib-poly->expr gden x)))))

; один порядок k: u с div u = k·(див. вычетов) или #f
(define (dv-irred-principal data k mden gden dc0 dc1 infs H P x m)
  (let* ((rows (dv-irred-rows data k mden dc0 dc1 P x)))
    (if (equal? rows 'unknown)
        'unknown
        (let* ((irows (foldl
                       (lambda (acc pl)
                         (let ((r (if (equal? acc 'unknown) 'unknown (dv-l-rows-inf pl 0 P x (ib-p-deg gden) dc0 dc1))))
                           (if (equal? r 'unknown)
                               'unknown
                               (append acc r))))
                       '() infs)))
          (if (equal? irows 'unknown)
              'unknown
              ; R1-хвост: строки на ∞ — в ℚ(√lc) (lc < 0 и т. п.): расщепляем по ключам, неизвестные c — рациональные
              (let* ((keys (if (null? irows) (list '()) (ib-row-keys irows)))
                     (ir (ib-expand-rows irows keys))
                     (qrows (append rows ir)))
                (if (not (every? (lambda (r) (every? number? r)) ir))
                    'unknown
                    (let ((ker (if (null? qrows)
                                   (map (lambda (j) (dv-unit-vec j (+ (+ dc0 1) (+ dc1 1))))
                                        (range 8))
                                   (try (fm-nullspace (field-Q) qrows) (lambda (e) 'unknown)))))
                      (if (equal? ker 'unknown)
                          'unknown
                          ; R1-хвост: u есть (div u = k·δ), но H ≠ (1/mk)·u′/u — вернуть кандидата (list 'cand u):
                          ; остаток надо разобрать (голоморфен / 2-го рода), а не объявлять «u нет»
                          (let loop ((vs ker) (cand #f))
                            (if (null? vs)
                                (if cand (list 'cand cand) #f)
                                (let ((u (dv-irred-u (car vs) dc0 dc1 gden x)))
                                  (if (not (equal? (simplify u) 0))
                                      (if (hyp-log-check H P x (list 'logs m (list (list 1 k u))))
                                          u
                                          (loop (cdr vs) (or cand u)))
                                      (loop (cdr vs) cand))))))))))))))

(define (dv-irred-search dat H P x)
  (let* ((m (foldl (lambda (a d) (dv-lcm2 a (denom (together (nth d 2))))) 1 dat))
         (m (foldl (lambda (a d) (dv-lcm2 a (denom (together (nth d 3))))) m dat)))
    (if (not (integer? m))
        'unknown
        (let* ((data (map (lambda (d)
                            (list (nth d 0) (nth d 1) (* m (nth d 2)) (* m (nth d 3))))
                          dat))
               ; R1-хвост: полюсы u лежат там, где k·коэффициент < 0 — знаменатель g^(k·mden0) зависит от k
               ; (прежняя формула брала max(0, +коэф.) и не зависела от k: кручение порядка k ≥ 2 и отрицательные
               ; коэффициенты терялись, а при известной границе B это давало ложное «неэлементарен»)
               (mden0 (foldl (lambda (a d)
                               (max a (max 0 (- (nth d 2))) (max 0 (- (nth d 3)))))
                             0 data))
               (ndeg (try (degree P x) (lambda (e) 0)))
               (ev (even? ndeg))
               (sh (if ev (quotient ndeg 2) ndeg))
               (Dg (if ev 1 2))
               (infs (hyp-places P x 'inf))
               (B (hyp-torsion-bound P x))
               (known (not (equal? B 'unknown)))
               (ns (if known (divisors B) (map (lambda (i) (+ i 1)) (range 12)))))
          (if (equal? infs 'unknown)
              'unknown
              (let loop ((ks ns) (unk #f))
                (if (null? ks)
                    (if (and known (not unk)) 'nonelementary 'unknown)
                    (let* ((k (car ks))
                           (mden (* k mden0))
                           (gden (foldl (lambda (a d)
                                          (ib-p-mul a (dv-p-pow (ib-poly-parse (nth d 0) x) mden)))
                                        (list 1) data))
                           (dg (ib-p-deg gden))
                           (dc0 (+ dg 2))
                           (dc1 (+ dg (ceiling (/ sh Dg)) 2))
                           (u (dv-irred-principal data k mden gden dc0 dc1 infs H P x m)))
                      (cond ((equal? u 'unknown) (loop (cdr ks) #t))
                            ((and (pair? u) (equal? (car u) 'cand))
                             (try (dv-log-answer H P x m k (cadr u)) (lambda (e) 'unknown)))
                            (u (list 'logs m (list (list 1 k u))))
                            (else (loop (cdr ks) unk)))))))))))

; R1.3: места y³ = P над рациональным a: P(a) = b³ (b ∈ ℚ) ⇒ три ветви
; y = ζ₃^k·b; P(a) = 0 ⇒ одно разветвлённое место (индекс 3).
(define (hypn3-places P a x)
  (let* ((v (try (simplify (subst (list (list x a)) P)) (lambda (e) #f)))
         (b (and (number? v) (not (equal? v 0))
                 (let ((c (try (simplify (list '^ v 1/3)) (lambda (e) #f))))
                   (and (rational-number? c) c)))))
    (cond ((not (number? v)) 'unknown)
          ((equal? v 0) (list (list a 0 3)))
          (b (list (list a 0 1) (list a 1 1) (list a 2 1)))
          (else 'unknown))))

(define (hyp-log-irred H P x)
  (let ((nf (hyp-log-nf H P x)))                    ; R1-хвост: g степени ≥ 3 (placesnf.lisp); #f — не наш случай
    (if nf
        nf
        (let ((dat (dv-irred-data H P x)))
          (cond
            ((equal? dat 'unknown) 'unknown)
            ((every? dv-tower-entry? dat) (dv-tower-log-search dat H P x))
            ((member? #t (map dv-tower-entry? dat)) 'unknown)
            (else (dv-irred-search dat H P x)))))))

; ответ чётного случая: H = (√d/(2mn))·(log(u/ū))′
(define (dv-log-answer-ev H P x m n d ue)
  (let ((du (dv-crv-deriv ue P x)))
    (if (not du)
        'unknown
        (let* ((q (list '* 1/2 (list '^ d 1/2)))
               (up (simplify (list '/ du ue)))
               (rest (simplify (together (list '- H (list '* (/ 1 (* m n))
                                                       (list '* q up)))))))
          (cond ((dv-nf-zero? rest P x)
                 (list 'logs m (list (list q n ue))))
                ((equal? (hyp-holomorphic? rest P x) #t)
                 'nonelementary)
                ((equal? (hyp-second-kind? rest P x) #f)
                 'nonelementary)
                (else 'unknown))))))

; сборка ответа по найденному порядку (рациональный случай)
(define (hyp-log-finish H P x m t)
  (cond ((and (pair? t) (= (length t) 2))
         (dv-log-answer H P x m (car t) (cadr t)))
        ((equal? t 'non-torsion-proved) 'nonelementary)   ; R5.3b: не кручение доказано по Кантору (граница B не нужна)
        ((equal? t 'non-torsion)
         (if (not (equal? (hyp-torsion-bound P x) 'unknown)) 'nonelementary 'unknown))
        (else 'unknown)))

; логарифмическая часть H dx: (logs m ((q n u) …)) | nonelementary | unknown
(define (hyp-log-part H P x)
  (let ((info (dv-nf-info H P x)))
    (cond
      ((equal? info 'unknown) 'unknown)
      ((equal? (simplify H) 0) 'unknown)
      (else
       (let ((res (hyp-residues H P x)))
         (cond
           ((equal? res 'unknown) 'unknown)
           ; вычетов нет: элементарен только H = 0; голоморфность — A4.3/A5.4b,
           ; ненулевой класс 2-го рода (полюс ≥ 2 на ∞) — A5.4c
           ((null? res)
            (let ((ir (hyp-log-irred H P x)))       ; A5.6: полюсы над неприводимыми g(x)
              (cond ((and (list? ir) (member? (car ir) '(logs logs-sum))) ir)
                    ((equal? ir 'nonelementary)
                     (begin (if (equal? alg-why "")      ; R1-хвост: причину могла уже записать лог-часть над ℚ(α) (placesnf.lisp)
                                (set! alg-why "полюсы над неприводимыми множителями знаменателя: ни при каком n функция u не найдена (B — граница кручения)"))
                            'nonelementary))
                    ((equal? (hyp-holomorphic? H P x) #t)
                     (begin (set! alg-why "вычетов нет, остаток H голоморфен и H ≠ 0 — интеграл 1-го рода неэлементарен (Лиувилль, Трагер гл. 5)")
                            'nonelementary))
                    ((equal? (hyp-second-kind? H P x) #f)
                     (begin (set! alg-why "вычетов нет, у H неснимаемый полюс порядка ≥ 2 на ∞ (ненулевой класс 2-го рода) — интеграл неэлементарен")
                            'nonelementary))
                    (else 'unknown))))
           ((not (hyp-residues-check H P x res)) 'unknown)
           (else
            (let ((rd (residue-divisors res)))
              (if (and alg-log? (list? rd))
                  (dv-note-residues H P x res rd))
              (cond
                ((equal? rd 'unknown) 'unknown)
                (else
                 (let* ((m (car rd))
                        ; пары с нулевым дивизором не участвуют
                        (nz (filter (lambda (pd) (not (null? (cadr pd)))) (cdr rd))))
                   (cond
                     ; только рациональные вычеты
                     ((and (= 1 (length nz))
                           (equal? (simplify (car (car nz))) 1))
                      (hyp-log-finish H P x m
                                      (hyp-torsion-order* (cadr (car nz)) P x)))
                     ; чётный случай ℚ(√d): единственный ненулевой дивизор с коэффициентом √d
                     ((and (= 1 (length nz))
                           (dv-sqrt-radicand (car (car nz)))
                           (dv-anti-invariant? (cadr (car nz))))
                      (let* ((d (dv-sqrt-radicand (car (car nz))))
                             (t (hyp-torsion-order-ev (cadr (car nz)) P x d)))
                        (cond
                          ; R5.3c2: Кантор над K доказал «не кручение»
                          ((equal? t 'non-torsion-proved)
                           'nonelementary)
                          ((and (pair? t) (= 2 (length t)))
                           (let ((ue (simplify (list '/ (cadr t)
                                                      (dv-conj-expr (cadr t))))))
                             (dv-log-answer-ev H P x m (car t) d ue)))
                          ; §1.6, п. 4: не кручение только при известной границе
                          ((equal? t 'non-torsion)
                           (if (not (equal? (hyp-torsion-bound-ev P x d) 'unknown))
                               (begin (set! alg-why "вычеты в ℚ(√d): дивизор δ не кручение (граница кручения известна, n·δ не главный) — интеграл неэлементарен")
                                      'nonelementary)
                               'unknown))
                          (else 'unknown))))
                     (else 'unknown)))))))))))))

; u′/u для u = (a₀ + a₁y)/D (y² = P): знаменатель освобождается от y домножением на сопряжённое —
; прямая нормальная форма (alg-nf) работает без громоздкого разбора дробей с y внизу; иначе u′/u как есть
(define (dv-log-deriv-quot du u P x)
  (let ((nf (try (dv-hyp-nf u P x) (lambda (err) #f))))
    (if (and (pair? nf) (list? (car nf)) (= 2 (length (car nf))))
        (let* ((a0 (nth (car nf) 0)) (a1 (nth (car nf) 1)) (D (cdr nf))
               (norm (simplify (list '- (list '^ a0 2) (list '* (list '^ a1 2) P)))))
          (if (equal? norm 0)
              (list '/ du u)
              (list '/ (list '* du D (list '- a0 (list '* a1 'y))) norm)))
        (list '/ du u))))

; сертификат: H − (1/m)·Σ (q/n)·u′/u ≡ 0 (alg-nf)
; подтверждённые проверки (#t) запоминаются: log-part проверяет свой ответ сам, затем его проверяет вызывающий
(define dv-check-cache '())
(define (hyp-log-check H P x logs)
  (let ((key (list H P x logs)))
    (if (member? key dv-check-cache)
        #t
        (let ((r (hyp-log-check-raw H P x logs)))
          (if (equal? r #t)
              (set! dv-check-cache (cons key (if (> (length dv-check-cache) 7) (take dv-check-cache 7) dv-check-cache))))
          r))))

(define (hyp-log-check-raw H P x logs)
  (cond
    ((not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs))) #f)
    ; один логарифм: H = c·u′/u ⇔ H·u = c·u′ при u ≠ 0 (без знаменателя нормы N(u), он раздувает раскрытие)
    ((and (= 1 (length (caddr logs))) (not (equal? (simplify (caddr (car (caddr logs)))) 0)))
     (let* ((tr (car (caddr logs))) (c (/ (car tr) (* (cadr logs) (cadr tr)))) (u (caddr tr))
            (du (dv-crv-deriv u P x))
            (fast (and du (dv-log-check-fast H P x c u du))))
       (cond ((equal? fast 'fallback)
              (and du (dv-nf-zero? (simplify (together (list '- (list '* H u) (list '* c du)))) P x)))
             (else fast))))
    (else (hyp-log-check-sum H P x logs))))

; Точная проверка H·u = c·u′ на кривой y² = P без символьного раскрытия: H, u, u′ приводятся к (a₀ + a₁y)/D (alg-nf),
; многочлены a₀, a₁, D от x — списки рациональных коэффициентов (ib-p), произведения ib-p-mul, y² = P.
; Равенство (h₀+h₁y)(a₀+a₁y)·Dd = c·(d₀+d₁y)·Dh·Du в базисе 1, y. 'fallback — не всё разобралось (не ℚ-коэффициенты и т. п.)
(define (dv-nf-ibp e P x)
  (let ((nf (try (dv-hyp-nf e P x) (lambda (err) #f))))
    (and (pair? nf) (list? (car nf)) (<= (length (car nf)) 2)
         (let ((a (map (lambda (t) (ib-poly-parse t x)) (car nf)))
               (D (ib-poly-parse (cdr nf) x)))
           (and (not (member? #f a)) D (pair? D)
                (every? (lambda (cs) (every? number? cs)) (cons D a))
                (list (if (>= (length a) 1) (nth a 0) '()) (if (>= (length a) 2) (nth a 1) '()) D))))))

(define (dv-log-check-fast H P x c u du)
  (let ((h (dv-nf-ibp H P x)) (a (dv-nf-ibp u P x)) (d (dv-nf-ibp du P x)) (Pp (ib-poly-parse P x)))
    (if (not (and h a d Pp (number? c) (every? number? Pp)))
        'fallback
        (let* ((mul ib-p-mul)
               (sub (lambda (p q) (ib-p-trim (ib-p-add p (ib-p-scale q -1)))))
               (h0 (nth h 0)) (h1 (nth h 1)) (Dh (nth h 2))
               (a0 (nth a 0)) (a1 (nth a 1)) (Du (nth a 2))
               (d0 (nth d 0)) (d1 (nth d 1)) (Dd (nth d 2))
               (r0 (ib-p-trim (ib-p-add (mul h0 a0) (mul (mul h1 a1) Pp))))
               (r1 (ib-p-trim (ib-p-add (mul h0 a1) (mul h1 a0))))
               (k (mul Dh Du)))
          (and (null? (sub (mul r0 Dd) (ib-p-scale (mul d0 k) c)))
               (null? (sub (mul r1 Dd) (ib-p-scale (mul d1 k) c))))))))

(define (hyp-log-check-sum H P x logs)
  (if (not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs)))
      #f
      (let* ((m (cadr logs))
             (terms (caddr logs))
             (expr (foldl (lambda (acc tr)
                            (let* ((q (car tr)) (n (cadr tr)) (u (caddr tr))
                                   (du (dv-crv-deriv u P x)))
                              (if (not du)
                                  #f
                                  (simplify (list '+
                                                  acc
                                                  (list '* (/ q (* m n))
                                                        (dv-log-deriv-quot du u P x)))))))
                          0 terms))
             (rest (simplify (together (list '- H expr)))))
        (dv-nf-zero? rest P x))))

; ответ «G + Σ (q/(m n))·log u» в виде выражения
(define (hyp-logs->expr G logs)
  (if (not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs)))
      G
      (let ((m (cadr logs)))
        (simplify (foldl (lambda (acc tr)
                           (list '+ acc
                                 (list '* (/ (car tr) (* m (cadr tr)))
                                       (list 'log (caddr tr)))))
                         G (caddr logs))))))

; =====================================================================
; Шаг A5.5: общая кривая F(x, y)
;
; Место — (a i q): a ∈ ℚ или inf (база z-модели на ∞), i — номер ветви Пюизё,
; q — индекс ветвления (x − a = t^q конечно, z = 1/(x − a) = t^q на ∞).
; Ряды — в t с коэффициентами ib-k (ℚ(√d₁, √d₂, …)); кубические радикалы → unknown.
; Ветви с q = 2, переходящие друг в друга при t → −t, — одно место (орбита Галуа).
; Дивизор — список ((место . n) …).  Работаем через Пюизё и нормальную форму alg-g-nf.
; =====================================================================

(define gv-N 4)

(define (gv-place? pl)
  (and (list? pl) (= 3 (length pl)) (integer? (nth pl 1)) (integer? (nth pl 2))
       (or (equal? (car pl) 'inf) (number? (car pl)))))

(define (gv-place-eq? p q) (equal? p q))

(define (gv-place-assoc pl al)
  (cond ((null? al) #f)
        ((gv-place-eq? pl (car (car al))) (car al))
        (else (gv-place-assoc pl (cdr al)))))

(define (gv-normalize d)
  (let loop ((rest d) (acc '()))
    (if (null? rest)
        (reverse acc)
        (let* ((pr (car rest)) (pl (car pr)) (nn (cdr pr))
               (p (gv-place-assoc pl acc)))
          (if p
              (let ((s (+ (cdr p) nn)))
                (loop (cdr rest)
                      (if (= s 0)
                          (filter (lambda (x) (not (gv-place-eq? (car x) pl))) acc)
                          (map (lambda (x) (if (gv-place-eq? (car x) pl) (cons pl s) x)) acc))))
              (if (= nn 0)
                  (loop (cdr rest) acc)
                  (loop (cdr rest) (cons (cons pl nn) acc))))))))

(define (gv-add a b) (gv-normalize (append a b)))
(define (gv-scale d k) (gv-normalize (map (lambda (pr) (cons (car pr) (* (cdr pr) k))) d)))
(define (gv-degree d) (foldl (lambda (s pr) (+ s (cdr pr))) 0 (gv-normalize d)))
(define (gv-n-at D pl) (let ((p (gv-place-assoc pl D))) (if p (cdr p) 0)))

; x(t) = a + t^q (конечная) или a + t^{−q} (∞)
(define (gv-x-ser a q inf?)
  (if (or (equal? a 'inf) (= a 0))
      (list (cons (if inf? (- q) q) (dv-k-rat 1)))
      (list (cons 0 (dv-k-rat a)) (cons (if inf? (- q) q) (dv-k-rat 1)))))

; --- ветви и места (орбиты t → −t при q = 2) ---

(define (gv-flip-serif s)
  (map (lambda (t) (cons (car t) (if (even? (car t)) (cdr t) (ib-k-scale (cdr t) -1)))) s))

(define (gv-serif-eq? a b)
  (and (= (length a) (length b))
       (every? (lambda (i)
                 (and (= (car (nth a i)) (car (nth b i)))
                      (dv-k-eq? (cdr (nth a i)) (cdr (nth b i)))))
               (range (length a)))))

(define (gv-conj-entry? e1 e2)
  (and (equal? (nth (car e1) 0) (nth (car e2) 0))
       (= 2 (nth (car e1) 2)) (= 2 (nth (car e2) 2))
       (gv-serif-eq? (gv-flip-serif (nth e1 2)) (nth e2 2))))

(define (gv-find-conj e ents)
  (cond ((null? ents) #f)
        ((and (not (equal? (car (car ents)) (car e)))
              (gv-conj-entry? e (car ents))) (car ents))
        (else (gv-find-conj e (cdr ents)))))

(define (gv-merge-orbits ents)
  (let loop ((es ents) (done '()) (acc '()))
    (if (null? es)
        (let ((m (reverse acc)))
          (if (any? (lambda (e) (> (nth (car e) 2) 2)) m) 'unknown m))
        (let ((e (car es)))
          (if (member? (car e) done)
              (loop (cdr es) done acc)
              (let ((c (gv-find-conj e ents)))
                (loop (cdr es)
                      (if c (cons (car c) done) done)
                      (cons e acc))))))))

(define (gv-inf-entries brs aa M)
  (let loop ((bs brs) (i 0) (acc '()))
    (if (null? bs)
        (gv-merge-orbits (reverse acc))
        (let ((sb (ib-ser-branch (car bs))))
          (if (equal? sb #f)
              'unknown
              (let* ((q (car sb))
                     (xs (gv-x-ser aa q #t))
                     (ys (dv-ser-shift (cdr sb) (- (* q M)))))
                (loop (cdr bs) (+ i 1) (cons (list (list 'inf i q) xs ys) acc))))))))

(define (gv-branches-inf F x y N)
  (let* ((n (alg-g-ydeg F y))
         (aa (if n (alg-g-inf-a F x y) #f))
         (sh (if aa (alg-g-inf-shift F n x y aa 'z 'w) #f))
         (brs (if sh (try (px-cached (car sh) 'z 'w N) (lambda (e) #f)) #f)))
    (if (or (not sh) (not brs) (null? brs))
        'unknown
        (gv-inf-entries brs aa (cadr sh)))))

(define (gv-fin-entries brs a)
  (let loop ((bs brs) (i 0) (acc '()))
    (if (null? bs)
        (gv-merge-orbits (reverse acc))
        (let ((sb (ib-ser-branch (car bs))))
          (if (equal? sb #f)
              'unknown
              (let ((q (car sb)))
                (loop (cdr bs) (+ i 1)
                      (cons (list (list a i q) (gv-x-ser a q #f) (cdr sb)) acc))))))))

(define (gv-branches-fin F x y a N)
  (if (not (number? a))
      'unknown
      (let* ((Fa (if (= a 0) F (expand (subst (list (list x (list '+ x a))) F))))
             (brs (try (px-cached Fa x y N) (lambda (e) #f))))
        (if (or (not brs) (null? brs))
            'unknown
            (gv-fin-entries brs a)))))

(define (gv-branches F x y a N)
  (let ((n (if (> N 0) N gv-N)))
    (if (equal? a 'inf)
        (gv-branches-inf F x y n)
        (gv-branches-fin F x y a n))))

(define (gv-branch-of pl brs)
  (cond ((null? brs) #f)
        ((gv-place-eq? pl (car (car brs))) (car brs))
        (else (gv-branch-of pl (cdr brs)))))

(define (gv-places F x y a)
  (let ((br (gv-branches F x y a 2)))
    (if (equal? br 'unknown) 'unknown (map car br))))

(define (gv-place-series pl F x y N)
  (if (not (gv-place? pl))
      'unknown
      (let ((e (gv-branch-of pl (gv-branches F x y (car pl) (max N gv-N)))))
        (if e (list (nth pl 2) (nth e 1) (nth e 2)) 'unknown))))

; (a . ветви) для всех a; один расчёт Пюизё на a
(define (gv-grps as F x y N)
  (let loop ((as as) (acc '()))
    (if (null? as)
        (reverse acc)
        (let ((brs (gv-branches F x y (car as) N)))
          (if (equal? brs 'unknown)
              'unknown
              (loop (cdr as) (cons (cons (car as) brs) acc)))))))

; --- нормальная форма и ряды ---

(define (gv-nf e F x y)
  (let ((n (alg-g-ydeg F y)))
    (and n (alg-g-nf e F n x y))))

; (Σ vecᵢyⁱ)/D в рядах xs, ys → (числитель . знаменатель) | unknown
(define (gv-nf-series vec D xs ys x M)
  (let loop ((i 0) (acc '()))
    (if (= i (length vec))
        (let ((p (try (ib-poly-parse D x) (lambda (e) #f))))
          (if (not p)
              'unknown
              (cons acc (dv-ser-peval p xs M))))
        (let ((p (try (ib-poly-parse (nth vec i) x) (lambda (e) #f))))
          (if (not p)
              'unknown
              (let* ((pi (dv-ser-peval p xs M))
                     (yi (dv-ser-pow ys i M)))
                (loop (+ i 1) (dv-ser-add acc (dv-ser-mul pi yi M)))))))))

; x′(t): конечно q·t^{q−1}, на ∞ −q·t^{−q−1}
(define (gv-dx-ser pl)
  (let ((q (nth pl 2)))
    (if (equal? (car pl) 'inf)
        (list (cons (- (- q) 1) (dv-k-rat (- q))))
        (list (cons (- q 1) (dv-k-rat q))))))

(define (gv-nf-val nf ent x)
  (let* ((M 24)
         (ns (gv-nf-series (car nf) (cdr nf) (nth ent 1) (nth ent 2) x M)))
    (if (equal? ns 'unknown)
        'unknown
        (let* ((num (car ns)) (den (cdr ns))
               (vn (dv-ser-min num)) (vd (dv-ser-min den)))
          (cond ((or (not vn) (not vd)) 'unknown)
                ((or (>= vn (- M 2)) (>= vd (- M 2))) 'unknown)
                (else (- vn vd)))))))

(define (gv-nf-res nf ent x)
  (let* ((M 24)
         (ns (gv-nf-series (car nf) (cdr nf) (nth ent 1) (nth ent 2) x M)))
    (if (equal? ns 'unknown)
        'unknown
        (let* ((num (dv-ser-mul (car ns) (gv-dx-ser (car ent)) M))
               (r (dv-lser-residue num (cdr ns))))
          (cond ((equal? r 'unknown) 'unknown)
                ((null? r) 0)
                (else (dv-k->expr r)))))))

(define (gv-valuation pl H F x y)
  (if (not (gv-place? pl))
      'unknown
      (let ((nf (gv-nf H F x y)))
        (if (not nf)
            'unknown
            (let ((e (gv-branch-of pl (gv-branches F x y (car pl) gv-N))))
              (if e (gv-nf-val nf e x) 'unknown))))))

(define (gv-residue pl H F x y)
  (if (not (gv-place? pl))
      'unknown
      (let ((nf (gv-nf H F x y)))
        (if (not nf)
            'unknown
            (let ((e (gv-branch-of pl (gv-branches F x y (car pl) gv-N))))
              (if e (gv-nf-res nf e x) 'unknown))))))

; --- вычеты ---

; рациональные корни знаменателя (все множители линейны); иначе unknown
(define (gv-den-roots Dn x)
  (let ((fl (try (factor-list (expand Dn)) (lambda (e) #f))))
    (if (or (not fl) (not (pair? fl)))
        'unknown
        (let loop ((gs (cdr fl)) (acc '()))
          (cond ((null? gs) (reverse acc))
                ((not (= 1 (try (degree (car (car gs)) x) (lambda (e) -1)))) 'unknown)
                (else (let ((a (try (ib-linear-root (car (car gs)) x) (lambda (e) #f))))
                        (if (not (number? a)) 'unknown (loop (cdr gs) (cons a acc))))))))))

(define (gv-residues-from grps infs H F x y)
  (let ((nf (gv-nf H F x y)))
    (if (not nf)
        'unknown
        (let ((ents (append (foldl (lambda (acc g) (append acc (cdr g))) '() grps) infs)))
          (let loop ((es ents) (acc '()))
            (if (null? es)
                (reverse acc)
                (let ((r (gv-nf-res nf (car es) x)))
                  (if (equal? r 'unknown)
                      'unknown
                      (loop (cdr es) (cons (cons (car (car es)) r) acc))))))))))

(define (gv-residues H F x y)
  (let ((nf (gv-nf H F x y)))
    (if (not nf)
        'unknown
        (let ((as (gv-den-roots (cdr nf) x)))
          (if (equal? as 'unknown)
              'unknown
              (let ((grps (gv-grps (ib-unique as) F x y 4))
                    (infs (gv-branches F x y 'inf 4)))
                (if (or (equal? grps 'unknown) (equal? infs 'unknown))
                    'unknown
                    (gv-residues-from grps infs H F x y))))))))

; R(t) по §1.2: Res_x(pp_t(Res_y(G − t·D′, F)), D)
(define (gv-residue-poly H F x y t)
  (let ((nf (gv-nf H F x y)))
    (if (not nf)
        'unknown
        (let* ((vec (car nf)) (D (cdr nf)))
          (if (not (dv-squarefree? D x))
              'unknown
              (let* ((G (simplify (cons '+ (map (lambda (i)
                                                  (list '* (nth vec i) (list '^ 'y i)))
                                                (range (length vec))))))
                     (Dp (expand (diff x D)))
                     (r1 (try (expand (resultant (list '- G (list '* t Dp)) F 'y))
                              (lambda (e) #f))))
                (if (or (not r1) (equal? r1 0))
                    'unknown
                    (let* ((d (try (degree r1 t) (lambda (e) -1)))
                           (cs (if (and (integer? d) (>= d 0))
                                   (map (lambda (k) (ib-poly-parse (coeff r1 t k) x))
                                        (range (+ d 1)))
                                   #f)))
                      (if (or (not cs) (member? #f cs))
                          'unknown
                          (let* ((pp (dv-p-list->expr (dv-p-primitive-list cs) t))
                                 (R (try (expand (resultant pp D x)) (lambda (e) #f))))
                            (if (or (not R) (equal? R 0))
                                'unknown
                                (dv-positive-lead R t))))))))))))

; Σ вычетов = 0 и R(t) = c·∏(t − res_P/q_P)^{q_P} по конечным местам
(define (gv-residues-check H F x y res)
  (if (or (equal? res 'unknown) (not (list? res)))
      #f
      (let ((sum (foldl (lambda (acc pr) (if (number? (cdr pr)) (+ acc (cdr pr)) 'bad)) 0 res)))
        (if (not (number? sum))
            #f
            (and (= 0 sum)
                 (let* ((fin (filter (lambda (pr) (not (equal? (car (car pr)) 'inf))) res))
                        (prod (foldl (lambda (acc pr)
                                       (let* ((q (nth (car pr) 2))
                                              (r (dv-k-rat (/ (cdr pr) q))))
                                         (let loop ((i 0) (p acc))
                                           (if (= i q) p (loop (+ i 1) (dv-mul-linear p r))))))
                                     (list (dv-k-rat 1)) fin))
                        (R (gv-residue-poly H F x y 't)))
                   (if (equal? R 'unknown)
                       #f
                       (let ((rc (dv-expr-coeffs R 't)))
                         (if (equal? rc 'unknown)
                             #f
                             (dv-k-list-eq? (dv-k-list-norm rc) (dv-k-list-norm prod)))))))))))

; --- L(D) ---

; группа по конечному a: (a m ((место n_P q xs ys) …))
(define (gv-l-group D brs a)
  (let ((rows (map (lambda (e)
                     (list (car e) (gv-n-at D (car e)) (nth (car e) 2) (nth e 1) (nth e 2)))
                   brs)))
    (list a
          (foldl (lambda (mm r)
                   (let ((nP (nth r 1)) (q (nth r 2)))
                     (if (< nP 0)
                         (let ((need (ceiling (/ (- nP) q))))
                           (if (> need mm) need mm))
                         mm)))
                 0 rows)
          rows)))

; deg cᵢ ≤ min по местам ∞ от floor((i·vy − R)/q) + margin, R = n_P − q·msum
(define (gv-l-bounds n infs Dn msum margin)
  (let loop ((es infs) (acc '()) (first #t))
    (if (null? es)
        (reverse acc)
        (let* ((e (car es))
               (q (nth (car e) 2))
               (vy (dv-ser-min (nth e 2)))
               (nP (gv-n-at Dn (car e))))
          (if (not vy)
              'unknown
              (let* ((R (- nP (* q msum)))
                     (bs (map (lambda (i) (+ (floor (/ (- (* i vy) R) q)) margin))
                              (range n))))
                (loop (cdr es)
                      (if first
                          bs
                          (map (lambda (i) (let ((b (nth bs i)))
                                             (if (< b (nth acc i)) b (nth acc i))))
                               (range n)))
                      #f)))))))

(define (gv-l-g grps x)
  (foldl (lambda (acc gr)
           (let ((a (car gr)) (m (cadr gr)))
             (let loop ((i 0) (p acc))
               (if (= i m) p (loop (+ i 1) (expand (list '* p (list '- x a))))))))
         1 grps))

(define (gv-monomial-sers xs ys bounds lim)
  (let loop ((i 0) (acc '()))
    (if (= i (length bounds))
        acc
        (let ((b (nth bounds i)))
          (if (< b 0)
              (loop (+ i 1) acc)
              (let* ((yi (dv-ser-pow ys i lim))
                     (row (map (lambda (k) (dv-ser-mul (dv-ser-pow xs k lim) yi lim))
                               (range (+ b 1)))))
                (loop (+ i 1) (append acc row))))))))

(define (gv-l-rows-finite m e bounds)
  (let* ((nP (nth e 1)) (q (nth e 2))
         (K (+ (* m q) nP)))
    (if (<= K 0)
        '()
        (let* ((lim (- K 1))
               (sers (gv-monomial-sers (nth e 3) (nth e 4) bounds lim)))
          (let loop ((o 0) (rows '()))
            (if (> o lim)
                (reverse rows)
                (let ((row (map (lambda (s) (dv-ser-ref s o)) sers)))
                  (if (every? dv-k-zero? row)
                      (loop (+ o 1) rows)
                      (loop (+ o 1) (cons row rows))))))))))

(define (gv-l-rows-inf Dn e msum bounds)
  (let* ((pl (car e))
         (nP (gv-n-at Dn pl))
         (q (nth pl 2))
         (K (- nP (* q msum)))
         (lim (if (>= (- K 1) 0) (- K 1) 0))
         (sers (gv-monomial-sers (nth e 1) (nth e 2) bounds lim))
         (omin (foldl (lambda (mm s)
                        (let ((o (dv-ser-min s))) (if (and o (< o mm)) o mm)))
                      0 sers)))
    (if (<= K omin)
        '()
        (let loop ((o omin) (rows '()))
          (if (>= o K)
              (reverse rows)
              (let ((row (map (lambda (s) (dv-ser-ref s o)) sers)))
                (if (every? dv-k-zero? row)
                    (loop (+ o 1) rows)
                    (loop (+ o 1) (cons row rows)))))))))

(define (gv-l-rows grps infs Dn msum bounds)
  (let ((fin (foldl (lambda (acc gr)
                      (foldl (lambda (a2 r)
                               (append a2 (gv-l-rows-finite (cadr gr) r bounds)))
                             acc (caddr gr)))
                    '() grps)))
    (foldl (lambda (acc e) (append acc (gv-l-rows-inf Dn e msum bounds))) fin infs)))

(define (gv-poly-from v idx d x)
  (simplify (cons '+ (map (lambda (k)
                            (let ((c (nth v (+ idx k))))
                              (if (= c 0) 0 (if (= k 0) c (list '* c (list '^ x k))))))
                          (range d)))))

(define (gv-kernel->expr v bounds grps x y)
  (let ((num
         (let loop ((i 0) (idx 0) (acc 0))
           (if (= i (length bounds))
               acc
               (let ((b (nth bounds i)))
                 (if (< b 0)
                     (loop (+ i 1) idx acc)
                     (loop (+ i 1) (+ idx (+ b 1))
                           (simplify (list '+ acc
                                           (list '* (gv-poly-from v idx (+ b 1) x)
                                                 (if (= i 0) 1 (list '^ y i))))))))))))
    (simplify (list '/ num (gv-l-g grps x)))))

; {u : v_P(u) ≥ n_P для всех P} по уже посчитанным ветвям
(define (gv-l-basis-from grps infs D F x y margin)
  (let ((n (alg-g-ydeg F y)))
    (if (not n)
        'unknown
        (let ((Dn (gv-normalize D)))
          (if (not (every? (lambda (pr) (integer? (cdr pr))) Dn))
              'unknown
              (let ((gs (map (lambda (g) (gv-l-group Dn (cdr g) (car g))) grps)))
                (if (member? 'unknown gs)
                    'unknown
                    (let* ((msum (foldl (lambda (s gr) (+ s (cadr gr))) 0 gs))
                           (bounds (gv-l-bounds n infs Dn msum margin)))
                      (if (equal? bounds 'unknown)
                          'unknown
                          (let* ((nunks (foldl (lambda (s b) (+ s (if (>= b 0) (+ b 1) 0)))
                                               0 bounds))
                                 (rows (if (= nunks 0)
                                           '()
                                           (gv-l-rows gs infs Dn msum bounds))))
                            (if (equal? rows 'unknown)
                                'unknown
                                (let* ((keys (if (null? rows) (list '()) (ib-row-keys rows)))
                                       (qrows (ib-expand-rows rows keys))
                                       (ker (if (null? qrows)
                                                (map (lambda (j) (map (lambda (i) (if (= i j) 1 0)) (range nunks)))
                                                     (range nunks))
                                                (try (fm-nullspace (field-Q) qrows)
                                                     (lambda (e) 'unknown)))))
                                  (cond ((equal? ker 'unknown) 'unknown)
                                        ((and (null? ker) (> (length keys) 1)) 'unknown)
                                        (else (map (lambda (v)
                                                     (gv-kernel->expr v bounds gs x y))
                                                   ker)))))))))))))))

(define (gv-l-basis D F x y margin)
  (let ((nf (gv-normalize D)))
    (let ((as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                 (map (lambda (pr) (car (car pr))) nf))))
          (infs (gv-branches F x y 'inf 4)))
      (if (or (not (every? number? as)) (equal? infs 'unknown))
          'unknown
          (let ((grps (gv-grps as F x y 4)))
            (if (equal? grps 'unknown)
                'unknown
                (gv-l-basis-from grps infs nf F x y margin)))))))

(define (gv-riemann-roch D F x y)
  (if (gv-divisor-ok? D F x y)
      (gv-l-basis (gv-scale D -1) F x y 2)
      'unknown))

; --- места и главность ---

(define (gv-divisor-ok-from grps infs D)
  (let ((Dn (gv-normalize D)))
    (if (or (not (every? (lambda (pr) (gv-place? (car pr))) Dn))
            (not (every? (lambda (pr) (integer? (cdr pr))) Dn)))
        'unknown
        (let loop ((ps Dn) (ok #t))
          (cond ((null? ps) ok)
                ((not (equal? ok #t)) ok)
                (else
                 (let* ((pl (car (car ps)))
                        (g (if (equal? (car pl) 'inf)
                               (cons 'inf infs)
                               (let ((p (gv-assoc-a (car pl) grps)))
                                 p))))
                   (if (or (not g) (equal? (cdr g) 'unknown))
                       (loop (cdr ps) #f)
                       (loop (cdr ps) (if (member? pl (map car (cdr g))) #t #f))))))))))

(define (gv-assoc-a a grps)
  (cond ((null? grps) #f)
        ((equal? a (car (car grps))) (car grps))
        (else (gv-assoc-a a (cdr grps)))))

(define (gv-divisor-ok? D F x y)
  (let* ((Dn (gv-normalize D))
         (as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                (map (lambda (pr) (car (car pr))) Dn)))))
    (if (not (every? number? as))
        'unknown
        (let ((grps (gv-grps as F x y 4))
              (infs (gv-branches F x y 'inf 4)))
          (if (or (equal? grps 'unknown) (equal? infs 'unknown))
              'unknown
              (gv-divisor-ok-from grps infs Dn))))))

; знаменатель u в нормальной форме раскладывается только по a из supp D
(define (gv-den-supported? Dn nf x)
  (let* ((D (cdr nf))
         (fl (try (factor-list (expand D)) (lambda (e) #f)))
         (as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                (map (lambda (pr) (car (car pr))) Dn)))))
    (and fl
         (every? (lambda (g)
                   (let ((r (try (ib-linear-root (car g) x) (lambda (e) #f))))
                     (and (number? r) (member? r as))))
                 (cdr fl)))))

; v_P(u) = n_P во всех местах над x-координатами supp D и над ∞
(define (gv-vals-ok-from grps infs Dn nf x)
  (let ((fin (foldl (lambda (acc g)
                      (if (not (equal? acc #t))
                          acc
                          (if (every? (lambda (e)
                                        (let ((v (gv-nf-val nf e x)))
                                          (and (integer? v) (= v (gv-n-at Dn (car e))))))
                                      (cdr g))
                              #t #f)))
                    #t grps)))
    (if (not (equal? fin #t))
        fin
        (every? (lambda (e)
                  (let ((v (gv-nf-val nf e x)))
                    (and (integer? v) (= v (gv-n-at Dn (car e))))))
                infs))))

(define (gv-principal-check-from grps infs D u F x y)
  (let ((Dn (gv-normalize D)))
    (cond ((not (equal? (gv-divisor-ok-from grps infs Dn) #t)) #f)
          ((not (= 0 (gv-degree Dn))) #f)
          ((equal? (simplify u) 0) #f)
          (else
           (let ((nf (gv-nf u F x y)))
             (if (or (not nf) (not (gv-den-supported? Dn nf x)))
                 #f
                 (equal? (gv-vals-ok-from grps infs Dn nf x) #t)))))))

(define (gv-principal-check D u F x y)
  (let* ((Dn (gv-normalize D))
         (as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                (map (lambda (pr) (car (car pr))) Dn)))))
    (if (not (every? number? as))
        #f
        (let ((grps (gv-grps as F x y 4))
              (infs (gv-branches F x y 'inf 4)))
          (if (or (equal? grps 'unknown) (equal? infs 'unknown))
              #f
              (gv-principal-check-from grps infs Dn u F x y))))))

(define (gv-principal-from grps infs D F x y)
  (let ((Dn (gv-normalize D)))
    (cond ((not (= 0 (gv-degree Dn))) 'not-principal)
          ((not (equal? (gv-divisor-ok-from grps infs Dn) #t)) 'unknown)
          (else
           (let ((b (gv-l-basis-from grps infs Dn F x y 2)))
             (cond
               ((equal? b 'unknown) 'unknown)
               ((pair? b)
                (let loop ((us b))
                  (cond ((null? us) 'unknown)
                        ((equal? (gv-principal-check-from grps infs Dn (car us) F x y) #t)
                         (list 'principal (car us)))
                        (else (loop (cdr us))))))
               (else
                (let ((b2 (gv-l-basis-from grps infs Dn F x y 4)))
                  (cond ((equal? b2 'unknown) 'unknown)
                        ((pair? b2) 'unknown)
                        (else 'not-principal))))))))))

(define (gv-principal D F x y)
  (let* ((Dn (gv-normalize D))
         (as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                (map (lambda (pr) (car (car pr))) Dn)))))
    (if (not (every? number? as))
        'unknown
        (let ((grps (gv-grps as F x y 4))
              (infs (gv-branches F x y 'inf 4)))
          (if (or (equal? grps 'unknown) (equal? infs 'unknown))
              'unknown
              (gv-principal-from grps infs Dn F x y))))))

; --- граница кручения (гладкая плоская модель рода 1) ---

(define (gv-pow-mod a k p)
  (if (= k 0) (modulo 1 p)
      (modulo (* (modulo a p) (gv-pow-mod a (- k 1) p)) p)))

(define (gv-peval-mod ms x0 y0 p)
  (foldl (lambda (acc m)
           (modulo (+ acc (* (car m) (gv-pow-mod x0 (nth m 1) p) (gv-pow-mod y0 (nth m 2) p))) p))
         0 ms))

; (gv-monomials-mod F x y p) → ((a i j) …) по модулю p | unknown | #f (p делит знаменатель)
(define (gv-monomials-mod F x y p)
  (let ((n (alg-g-ydeg F y)))
    (if (not n)
        'unknown
        (let* ((cs (map (lambda (i) (expand (coeff F y i))) (range (+ n 1))))
               (ps (map (lambda (c) (try (ib-poly-parse c x) (lambda (e) #f))) cs)))
          (if (member? #f ps)
              'unknown
              (let ((L (foldl (lambda (a pl)
                                (if (equal? a #f) #f
                                    (foldl (lambda (a2 k)
                                             (if (equal? a2 #f) #f
                                                 (dv-lcm2 a2 (denom (together (nth pl k))))))
                                           a (range (length pl)))))
                             1 ps)))
                (if (or (not (integer? L)) (= 0 (modulo L p)))
                    #f
                    (foldl (lambda (acc i)
                             (let ((pl (nth ps i)))
                               (append acc (map (lambda (k)
                                                  (list (modulo (* (nth pl k) L) p) k i))
                                                (range (length pl))))))
                           '() (range (+ n 1))))))))))

(define (gv-plane-degree F x y)
  (let ((n (alg-g-ydeg F y)))
    (if (not n)
        'unknown
        (let loop ((i 0) (d 0))
          (if (> i n)
              d
              (let ((f (try (expand (coeff F y i)) (lambda (e) #f))))
                (if (not f)
                    'unknown
                    (if (equal? (simplify f) 0)
                        (loop (+ i 1) d)
                        (let ((di (try (degree f x) (lambda (e) -1))))
                          (loop (+ i 1) (max d (if (and (integer? di) (>= di 0)) (+ di i) i))))))))))))

(define (gv-affine-smooth-mod? m0 mx my p)
  (let loop ((x0 0))
    (if (= x0 p)
        #t
        (let loop2 ((y0 0))
          (cond ((= y0 p) (loop (+ x0 1)))
                ((and (= 0 (gv-peval-mod m0 x0 y0 p))
                      (= 0 (gv-peval-mod mx x0 y0 p))
                      (= 0 (gv-peval-mod my x0 y0 p)))
                 #f)
                (else (loop2 (+ y0 1))))))))

(define (gv-inf-points-mod ms d p)
  (let ((top (filter (lambda (m) (= (+ (nth m 1) (nth m 2)) d)) ms)))
    (let loop ((y 0) (acc '()))
      (if (= y p)
          (cons (list 0 1) acc)
          (loop (+ y 1)
                (if (= 0 (gv-peval-mod top 1 y p)) (cons (list 1 y) acc) acc))))))

(define (gv-inf-smooth-mod? ms d p)
  (let* ((top (filter (lambda (m) (= (+ (nth m 1) (nth m 2)) d)) ms))
         (low (filter (lambda (m) (= (+ (nth m 1) (nth m 2)) (- d 1))) ms)))
    (let loop ((ys (append (map (lambda (y) (list 1 y)) (range p)) (list (list 0 1)))))
      (if (null? ys)
          #t
          (let ((pt (car ys)))
            (if (and (= 0 (gv-peval-mod top (car pt) (cadr pt) p))
                     (= 0 (gv-peval-mod low (car pt) (cadr pt) p)))
                #f
                (loop (cdr ys))))))))

(define (gv-good-prime? F x y p)
  (if (not (and (integer? p) (> p 4) (true? (prime? p))))
      #f
      (let ((m0 (gv-monomials-mod F x y p))
            (mx (gv-monomials-mod (expand (diff x F)) x y p))
            (my (gv-monomials-mod (expand (diff y F)) x y p))
            (d (gv-plane-degree F x y)))
        (cond ((or (equal? m0 'unknown) (equal? mx 'unknown) (equal? my 'unknown)
                   (equal? d 'unknown)) 'unknown)
              ((or (equal? m0 #f) (equal? mx #f) (equal? my #f)) #f)
              (else
               (and (gv-affine-smooth-mod? m0 mx my p)
                    (gv-inf-smooth-mod? m0 d p)))))))

(define (gv-count-points F x y p)
  (let ((ms (gv-monomials-mod F x y p))
        (d (gv-plane-degree F x y)))
    (if (or (equal? ms 'unknown) (equal? ms #f) (equal? d 'unknown))
        'unknown
        (+ (let loop ((x0 0) (s 0))
             (if (= x0 p) s
                 (loop (+ x0 1)
                       (+ s (let loop2 ((y0 0) (c 0))
                              (if (= y0 p) c
                                  (loop2 (+ y0 1)
                                         (if (= 0 (gv-peval-mod ms x0 y0 p)) (+ c 1) c))))))))
           (length (gv-inf-points-mod ms d p))))))

(define (gv-jacobian-order F x y p)
  (let ((d (gv-plane-degree F x y)))
    (if (and (integer? d) (= d 3))
        (gv-count-points F x y p)
        'unknown)))

(define (gv-torsion-bound F x y)
  (let loop ((p 5) (found '()))
    (cond ((>= (length found) 2) (gcd (car found) (cadr found)))
          ((> p 50) 'unknown)
          (else
           (let ((gp (gv-good-prime? F x y p)))
             (cond ((equal? gp 'unknown) 'unknown)
                   ((equal? gp #t)
                    (let ((j (gv-jacobian-order F x y p)))
                      (if (equal? j 'unknown) 'unknown (loop (next-prime p) (cons j found)))))
                   (else (loop (next-prime p) found))))))))

; --- сборка логарифмической части ---

(define (gv-der u F x y)
  (let ((n (alg-g-ydeg F y)))
    (and n (alg-g-expr (alg-g-der u F n x y) y))))

(define (gv-nf-zero? e F x y)
  (let ((nf (gv-nf e F x y)))
    (and nf (every? (lambda (c) (equal? (simplify c) 0)) (car nf)))))

(define (gv-holomorphic? H F x y)
  (let ((n (alg-g-ydeg F y)))
    (if (not n) 'unknown (alg-g-holomorphic? H F n x y))))

(define (gv-log-answer H F x y m n u)
  (let ((du (gv-der u F x y)))
    (if (not du)
        'unknown
        (let* ((up (simplify (list '/ du u)))
               (rest (simplify (together (list '- H (list '* (/ 1 (* m n)) up))))))
          (cond ((gv-nf-zero? rest F x y)
                 (list 'logs m (list (list 1 n u))))
                ((equal? (gv-holomorphic? rest F x y) #t)
                 'nonelementary)
                (else 'unknown))))))

(define (gv-torsion-search-from grps infs D F x y ns known?)
  (let loop ((ns ns) (unk #f))
    (cond ((null? ns) (if (and known? (not unk)) 'non-torsion 'unknown))
          (else
           (let ((r (gv-principal-from grps infs (gv-scale D (car ns)) F x y)))
             (cond ((and (pair? r) (equal? (car r) 'principal))
                    (list (car ns) (cadr r)))
                   ((equal? r 'unknown) (loop (cdr ns) #t))
                   (else (loop (cdr ns) unk))))))))

(define (gv-torsion-order-from grps infs D F x y)
  (let ((Dn (gv-normalize D)))
    (cond ((not (equal? (gv-divisor-ok-from grps infs Dn) #t)) #f)
          ((not (= 0 (gv-degree Dn))) 'non-torsion)
          (else
           (let ((B (gv-torsion-bound F x y)))
             (if (equal? B 'unknown)
                 (gv-torsion-search-from grps infs Dn F x y
                                         (map (lambda (i) (+ i 1)) (range 12)) #f)
                 (gv-torsion-search-from grps infs Dn F x y (divisors B) #t)))))))

(define (gv-torsion-order D F x y)
  (let* ((Dn (gv-normalize D))
         (as (ib-unique (filter (lambda (a) (not (equal? a 'inf)))
                                (map (lambda (pr) (car (car pr))) Dn)))))
    (if (not (every? number? as))
        #f
        (let ((grps (gv-grps as F x y 4))
              (infs (gv-branches F x y 'inf 4)))
          (if (or (equal? grps 'unknown) (equal? infs 'unknown))
              'unknown
              (gv-torsion-order-from grps infs Dn F x y))))))

; (m δ): только рациональные вычеты (чётный случай ℚ(√d) не реализован)
(define (gv-residue-divisor res)
  (if (not (every? (lambda (pr) (and (number? (cdr pr))
                                     (= (cdr pr) (simplify (cdr pr)))))
                   res))
      'unknown
      (let ((m (foldl (lambda (a pr) (dv-lcm2 a (denom (together (cdr pr))))) 1 res)))
        (if (not (integer? m))
            'unknown
            (let ((D (gv-normalize (map (lambda (pr) (cons (car pr) (* m (cdr pr)))) res))))
              (list m D))))))

(define (gv-log-part-n H F x y ord)
  (let* ((n (alg-g-ydeg F y))
         (nf (and n (alg-g-nf H F n x y))))
    (cond
      ((not nf) 'unknown)
      ((equal? (simplify H) 0) 'unknown)
      (else
       (let ((as (gv-den-roots (cdr nf) x)))
         (if (equal? as 'unknown)
             'unknown
             (let ((grps (gv-grps (ib-unique as) F x y ord))
                   (infs (gv-branches F x y 'inf ord)))
               (if (or (equal? grps 'unknown) (equal? infs 'unknown))
                   'unknown
                   (let ((res (gv-residues-from grps infs H F x y)))
                     (cond
                       ((equal? res 'unknown) 'unknown)
                       ((null? res)
                        (if (equal? (gv-holomorphic? H F x y) #t) 'nonelementary 'unknown))
                       ((not (gv-residues-check H F x y res)) 'unknown)
                       (else
                        (let ((rd (gv-residue-divisor res)))
                          (cond
                            ((equal? rd 'unknown) 'unknown)
                            (else
                             (let ((m (car rd)) (delta (cadr rd)))
                               (if (null? delta)
                                   'unknown
                                   (let ((t (gv-torsion-order-from grps infs delta F x y)))
                                     (cond
                                       ((and (pair? t) (= (length t) 2))
                                        (gv-log-answer H F x y m (car t) (cadr t)))
                                       ((equal? t 'non-torsion)
                                        (if (not (equal? (gv-torsion-bound F x y) 'unknown))
                                            'nonelementary
                                            'unknown))
                                       (else 'unknown)))))))))))))))))))

; при нехватке членов (unknown) — повтор с более длинными рядами; R1.1: начинаем с 2
; (вычетам на простых полюсах хватает ведущих членов, сертификат всё равно точный)
(define (gv-log-part H F x y)
  (let ((r (gv-log-part-n H F x y 2)))
    (if (equal? r 'unknown)
        (let ((r2 (gv-log-part-n H F x y 4)))
          (if (equal? r2 'unknown) (gv-log-part-n H F x y 8) r2))
        r)))

(define (gv-log-check H F x y logs)
  (if (not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs)))
      #f
      (let* ((m (cadr logs))
             (terms (caddr logs))
             (expr (foldl (lambda (acc tr)
                            (let* ((q (car tr)) (nn (cadr tr)) (u (caddr tr))
                                   (du (gv-der u F x y)))
                              (if (not du)
                                  #f
                                  (simplify (list '+
                                                  acc
                                                  (list '* (/ q (* m nn))
                                                        (list '/ du u)))))))
                          0 terms)))
        (and (not (equal? expr #f))
             (gv-nf-zero? (simplify (together (list '- H expr))) F x y)))))

(define (gv-logs->expr G logs)
  (if (not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs)))
      G
      (let ((m (cadr logs)))
        (simplify (foldl (lambda (acc tr)
                           (list '+ acc
                                 (list '* (/ (car tr) (* m (cadr tr)))
                                       (list 'log (caddr tr)))))
                         G (caddr logs))))))

; ===== R1.3: арифметика Q(zeta3) и вычеты y^3 = P =====
; элемент — пара (a b) = a + b*zeta, zeta^2 = -zeta - 1
(define h3-zeta '(0 1))
(define (h3-add u v) (list (+ (car u) (car v)) (+ (cadr u) (cadr v))))
(define (h3-neg u) (list (- (car u)) (- (cadr u))))
(define (h3-sub u v) (h3-add u (h3-neg v)))
(define (h3-mul u v)
  (let ((a (car u)) (b (cadr u)) (c (car v)) (d (cadr v)))
    (list (- (* a c) (* b d))
          (- (+ (* a d) (* b c)) (* b d)))))
(define (h3-scale u c) (list (* (car u) c) (* (cadr u) c)))
(define (h3-conj u) (list (- (car u) (cadr u)) (- (cadr u))))
(define (h3-norm u) (let ((a (car u)) (b (cadr u))) (+ (* a a) (* -1 a b) (* b b))))
(define (h3-inv u) (h3-scale (h3-conj u) (/ 1 (h3-norm u))))
(define (h3-div u v) (h3-mul u (h3-inv v)))
(define (h3-pow u n) (let loop ((k 0) (r '(1 0))) (if (= k n) r (loop (+ k 1) (h3-mul r u)))))
(define (h3-zero? u) (and (equal? (car u) 0) (equal? (cadr u) 0)))

; значение многочлена от y с рациональными коэффициентами в паре b
(define (h3-eval-poly p b)
  (let loop ((cs (reverse (coefficients p 'y))) (acc '(0 0)))
    (if (null? cs) acc
        (loop (cdr cs) (h3-add (h3-mul acc b) (list (car cs) 0))))))

; ветвь y = zeta^k * P(a)^{1/3} (b in Q); иначе #f
(define (hypn3-branch P a k x)
  (let* ((v (try (simplify (subst (list (list x a)) P)) (lambda (e) #f)))
         (b0 (and (number? v) (not (equal? v 0))
                  (let ((c (try (simplify (list '^ v 1/3)) (lambda (e) #f))))
                    (and (rational-number? c) c)))))
    (and b0 (h3-scale (h3-pow h3-zeta k) b0))))

; вычет H dx в простом неразветвлённом месте (a,k,1):
; res = N(a,b) / (D_x(a,b) + D_y(a,b)*y'(0)), y'(0) = P'(a)/(3b^2)
(define (hypn3-residue H P a k x)
  (let* ((u (try (together H) (lambda (e) #f)))
         (b (hypn3-branch P a k x)))
    (if (or (not u) (not b))
        'unknown
        (let* ((N (expand (numer u)))
               (D (expand (denom u)))
               (Na (expand (subst (list (list x a)) N)))
               (Da (expand (subst (list (list x a)) D)))
               (Db (h3-eval-poly Da b)))
          (if (not (h3-zero? Db))
              0
              (let* ((dDb (h3-eval-poly (expand (diff 'y Da)) b))
                     (dDa (h3-eval-poly (expand (subst (list (list x a)) (diff x D))) b))
                     (Pp (simplify (subst (list (list x a)) (diff x P))))
                     (yp (h3-div (list Pp 0) (h3-scale (h3-mul b b) 3)))
                     (den (h3-add dDa (h3-mul dDb yp)))
                     (num (h3-eval-poly Na b)))
                (if (h3-zero? den) 'unknown (h3-div num den))))))))

; ===== R1.3: ряд y(t) в Q(zeta3) =====
(define (h3-ser-mul a b N)
  (let loop ((k 0) (acc '()))
    (if (> k N) (reverse acc)
        (loop (+ k 1)
              (cons (let inner ((i 0) (s '(0 0)))
                      (if (> i k) s
                          (inner (+ i 1)
                                 (if (or (>= i (length a)) (>= (- k i) (length b)))
                                     s
                                     (h3-add s (h3-mul (nth a i) (nth b (- k i))))))))
                    acc)))))
(define (h3-ser-cube a N) (h3-ser-mul (h3-ser-mul a a N) a N))
(define (h3-ser-coef a k) (if (>= k (length a)) '(0 0) (nth a k)))

(define (h3-p-coeffs P a x N)
  (let ((e (expand (subst (list (list x (list '+ a 't))) P))))
    (map (lambda (r) (coeff e 't r)) (range (+ N 1)))))

; y_0 = zeta^k*b, b^3 = P(a); y_r = (p_r - [t^r](partial^3)) / (3 y_0^2)
(define (hypn3-y-series P a k x N)
  (let* ((ps (h3-p-coeffs P a x N))
         (b (try (simplify (list '^ (car ps) 1/3)) (lambda (e) #f))))
    (if (not (rational-number? b))
        'unknown
        (let* ((y0 (h3-scale (h3-pow h3-zeta k) b))
               (den (h3-scale (h3-mul y0 y0) 3)))
          (let loop ((r 1) (ys (list y0)))
            (if (> r N) ys
                (let* ((c (h3-ser-coef (h3-ser-cube ys N) r))
                       (pr (list (nth ps r) 0))
                       (yr (h3-div (h3-sub pr c) den)))
                  (loop (+ r 1) (append ys (list yr))))))))))

; ===== R1.3: вычет q=3 и сборка logs =====
; разветвлённое место (a,0,3): x = a + t^3, y ~ c t, c^3 = P'(a), dx = 3t^2 dt.
; Для D = y^3 * Dx(x) (простой полюс в t): res = 3*N(a,0)/(P'(a)*Dx(a)).
(define (hypn3-residue-ram H P a x)
  (let* ((u (try (together H) (lambda (e) #f)))
         (N (and u (expand (numer u))))
         (D (and u (expand (denom u))))
         (c3 (try (simplify (subst (list (list x a)) (diff x P))) (lambda (e) #f))))
    (if (or (not u) (not (number? c3)) (equal? c3 0))
        'unknown
        (let ((Dy (try (coeff D 'y 3) (lambda (e) #f))))
          (if (not Dy)
              'unknown
              (let ((rest (expand (list '- D (list '* Dy (list '^ 'y 3))))))
                (if (not (equal? (simplify rest) 0))
                    'unknown
                    (let ((Na (simplify (subst (list (list x a) (list 'y 0)) N)))
                          (Da (simplify (subst (list (list x a)) Dy))))
                      (if (or (not (number? Na)) (not (number? Da)) (equal? Da 0))
                          'unknown
                          (simplify (list '/ (list '* 3 Na) (list '* c3 Da))))))))))))

; производная вдоль y^3 = P: u_x + u_y * P'/(3y^2)
(define (hypn3-der u P x)
  (let ((yp (try (simplify (list '/ (diff x P) (list '* 3 (list '^ 'y 2))))
                 (lambda (e) #f))))
    (and yp (simplify (together (list '+ (diff 'x u) (list '* (diff 'y u) yp)))))))

; точная проверка logs: H = (1/m) * sum (q/n) * u'/u
(define (hypn3-log-check H P x logs)
  (if (not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs)))
      #f
      (let* ((m (cadr logs))
             (terms (caddr logs))
             (expr (foldl (lambda (acc tr)
                            (let* ((q (car tr)) (nn (cadr tr)) (u (caddr tr))
                                   (du (hypn3-der u P x)))
                              (if (not du)
                                  #f
                                  (simplify (list '+
                                                  acc
                                                  (list '* (/ q (* m nn))
                                                        (list '/ du u)))))))
                          0 terms)))
        (and (not (equal? expr #f))
             (equal? 0 (simplify (together (list '- H expr))))))))

(define (hypn3-logs->expr G logs)
  (if (not (and (list? logs) (= 3 (length logs)) (equal? (car logs) 'logs)))
      G
      (let ((m (cadr logs)))
        (simplify (foldl (lambda (acc tr)
                           (list '+ acc
                                 (list '* (/ (car tr) (* m (cadr tr)))
                                       (list 'log (caddr tr)))))
                         G (caddr logs))))))

; ===== R1.3: места на бесконечности y^3 = P =====
; z = 1/x, w = y z^M, M = ceil(deg P / 3), Q(z) = z^{3M} P(1/z).
; Q(0) != 0 ⇒ три неразветвлённых места (inf k 1); Q(0) = 0 с порядком e
; ⇒ одно место с индексом 3/gcd(3,e).
(define (h3-order-at-0 Q z)
  (let loop ((k 0) (q (expand Q)))
    (let ((v (try (simplify (subst (list (list z 0)) q)) (lambda (e) #f))))
      (if (and (number? v) (equal? v 0))
          (loop (+ k 1) (expand (poly-quotient q z z)))
          k))))

(define (hypn3-places-inf P x)
  (let ((d (try (degree P x) (lambda (e) -1))))
    (if (< d 1)
        'unknown
        (let* ((M (ceiling (/ d 3)))
               (Q (try (expand (list '* (list '^ 'z (* 3 M))
                                     (subst (list (list x (list '^ 'z -1))) P)))
                       (lambda (e) #f))))
          (if (not Q)
              'unknown
              (let ((e (h3-order-at-0 Q 'z)))
                (if (> e 0)
                    (list (list 'inf 0 (quotient 3 (gcd 3 e))))
                    (let ((c (try (simplify (subst (list (list 'z 0)) Q)) (lambda (e) #f))))
                      (if (and (number? c) (rational-number? c)
                               (rational-number? (simplify (list '^ c 1/3))))
                          (list (list 'inf 0 1) (list 'inf 1 1) (list 'inf 2 1))
                          'unknown)))))))))

; ===== R1.3: нормирование и главность для y^3 = P =====
(define (h3-ser-add a b N)
  (map (lambda (i) (h3-add (h3-ser-coef a i) (h3-ser-coef b i))) (range (+ N 1))))

; многочлен p(x) → ряд по t = x - a (коэффициенты — пары)
(define (h3-poly-series p x a N)
  (let ((e (try (expand (subst (list (list x (list '+ a 't))) p)) (lambda (er) 0))))
    (map (lambda (r) (list (coeff e 't r) 0)) (range (+ N 1)))))

; v_P(u) в конечном неразветвлённом месте (a,k,1): первый ненулевой коэффициент
; ряда u(a+t, y(t)); u — многочлен по y степени <= 2
(define (hypn3-valuation P a k u x N)
  (let ((ys (try (hypn3-y-series P a k x N) (lambda (e) 'unknown))))
    (if (equal? ys 'unknown)
        'unknown
        (let* ((c0 (h3-poly-series (coeff u 'y 0) x a N))
               (c1 (h3-poly-series (coeff u 'y 1) x a N))
               (c2 (h3-poly-series (coeff u 'y 2) x a N))
               (y2 (h3-ser-mul ys ys N))
               (s (h3-ser-add c0
                              (h3-ser-add (h3-ser-mul c1 ys N)
                                          (h3-ser-mul c2 y2 N) N) N)))
          (let loop ((i 0))
            (cond ((> i N) 'unknown)
                  ((not (h3-zero? (h3-ser-coef s i))) i)
                  (else (loop (+ i 1)))))))))

; D = ((place . n) …) только конечные неразветвлённые; div u = D (главность)
(define (hypn3-principal-check D u P x)
  (if (not (every? (lambda (pr)
                     (and (pair? (car pr))
                          (not (equal? (car (car pr)) 'inf))
                          (= 1 (caddr (car pr)))))
                   D))
      'unknown
      (let loop ((ds D))
        (if (null? ds)
            #t
            (let* ((pr (car ds)) (pl (car pr)) (n (cdr pr))
                   (v (try (hypn3-valuation P (car pl) (cadr pl) u x 8) (lambda (e) 'unknown))))
              (cond ((equal? v 'unknown) 'unknown)
                    ((= v n) (loop (cdr ds)))
                    (else #f)))))))

; ===== R1.3: ряд y(t) на бесконечности для y^3 = P =====
; z = 1/x, w = y z^M, Q(z) = z^{3M} P(1/z); Q(0) != 0 — q = 1,
; Q(0) = 0 порядка e — q = 3/gcd(3,e), z = t^q, w = t^{e/d} v(t^q).
; Возвращает список (порядок . пара) по возрастанию порядка.
(define (hypn3-y-series-inf P k x N)
  (let ((d (try (degree P x) (lambda (e) -1))))
    (if (< d 1)
        'unknown
        (let* ((M (ceiling (/ d 3)))
               (Q (try (expand (list '* (list '^ 'z (* 3 M))
                                     (subst (list (list x (list '^ 'z -1))) P)))
                       (lambda (e) #f))))
          (if (not Q)
              'unknown
              (let ((e (h3-order-at-0 Q 'z)))
                (if (= e 0)
                    (let ((ws (hypn3-y-series Q 0 k 'z N)))
                      (if (equal? ws 'unknown)
                          'unknown
                          (map (lambda (r) (cons (- r M) (nth ws r))) (range (+ N 1)))))
                    (let* ((dd (gcd 3 e)) (q (quotient 3 dd)) (ep (quotient e dd))
                           (R (try (expand (poly-quotient Q (list '^ 'z e) 'z))
                                   (lambda (er) #f)))
                           (vs (and R (hypn3-y-series R 0 k 'z N))))
                      (if (not vs)
                          'unknown
                          (map (lambda (r) (cons (+ (- ep (* M q)) (* q r)) (nth vs r)))
                               (range (+ N 1))))))))))))

; ===== R1.3: строки L(D) для y^3 = P =====
; u = c0 + c1 y + c2 y^2, c_i = a_i + b_i zeta; неизвестные (a0 b0 a1 b1 a2 b2).
; Условие v_P(u) >= -n_P: коэффициенты при t^r (r < -n_P) равны нулю.
(define (hypn3-l-row f0 f1 f2)
  (list (list (car f0) (- (cadr f0)) (car f1) (- (cadr f1)) (car f2) (- (cadr f2)))
        (list (cadr f0) (- (car f0) (cadr f0))
              (cadr f1) (- (car f1) (cadr f1))
              (cadr f2) (- (car f2) (cadr f2)))))

(define (hypn3-l-rows D P x N)
  (let loop ((ds D) (rows '()) (ok #t))
    (if (null? ds)
        (if ok (reverse rows) 'unknown)
        (let* ((pr (car ds)) (pl (car pr)) (n (cdr pr)))
          (cond
            ((or (not (pair? pl)) (equal? (car pl) 'inf) (not (= 1 (caddr pl))))
             (loop (cdr ds) rows #f))
            ((>= n 0) (loop (cdr ds) rows ok))
            (else
             (let ((ys (hypn3-y-series P (car pl) (cadr pl) x N)))
               (if (equal? ys 'unknown)
                   (loop (cdr ds) rows #f)
                   (let ((y2 (h3-ser-mul ys ys N)))
                     (let inner ((rs (range (- n))) (rows rows))
                       (if (null? rs)
                           (loop (cdr ds) rows ok)
                           (let* ((r (car rs))
                                  (f0 (if (= r 0) '(1 0) '(0 0)))
                                  (f1 (h3-ser-coef ys r))
                                  (f2 (h3-ser-coef y2 r))
                                  (rr (hypn3-l-row f0 f1 f2)))
                             (inner (cdr rs) (append (reverse rr) rows))))))))))))))

(define (hypn3-l-basis D P x N)
  (let ((rows (hypn3-l-rows D P x N)))
    (if (equal? rows 'unknown)
        'unknown
        (if (null? rows)
            (map (lambda (j) (map (lambda (k) (if (= j k) 1 0)) (range 6))) (range 6))
            (try (nullspace rows) (lambda (e) 'unknown))))))

; ===== R1.3: кручение для y^3 = P =====
(define (h3-ser-const c N)
  (cons c (map (lambda (i) '(0 0)) (range N))))

(define (h3-ser-pair c s N)
  (map (lambda (i) (h3-mul c (h3-ser-coef s i))) (range (+ N 1))))

; v_P(u) для вектора (a0 b0 a1 b1 a2 b2) в конечном неразветвлённом месте
(define (hypn3-valuation-vec P a k v x N)
  (let ((ys (try (hypn3-y-series P a k x N) (lambda (e) 'unknown))))
    (if (equal? ys 'unknown)
        'unknown
        (let* ((y2 (h3-ser-mul ys ys N))
               (s (h3-ser-add (h3-ser-const (list (nth v 0) (nth v 1)) N)
                              (h3-ser-add (h3-ser-pair (list (nth v 2) (nth v 3)) ys N)
                                          (h3-ser-pair (list (nth v 4) (nth v 5)) y2 N) N) N)))
          (let loop ((i 0))
            (cond ((> i N) 'unknown)
                  ((not (h3-zero? (h3-ser-coef s i))) i)
                  (else (loop (+ i 1)))))))))

(define (hypn3-principal-check-vec D v P x)
  (if (not (every? (lambda (pr)
                     (and (pair? (car pr))
                          (not (equal? (car (car pr)) 'inf))
                          (= 1 (caddr (car pr)))))
                   D))
      'unknown
      (let loop ((ds D))
        (if (null? ds)
            #t
            (let* ((pr (car ds)) (pl (car pr)) (n (cdr pr))
                   (vv (try (hypn3-valuation-vec P (car pl) (cadr pl) v x 10)
                            (lambda (e) 'unknown))))
              (cond ((equal? vv 'unknown) 'unknown)
                    ((= vv n) (loop (cdr ds)))
                    (else #f)))))))

; строки v_P(u) >= n_P (нули) для конечных неразветвлённых мест
(define (hypn3-principal-rows D P x N)
  (let loop ((ds D) (rows '()) (ok #t))
    (if (null? ds)
        (if ok (reverse rows) 'unknown)
        (let* ((pr (car ds)) (pl (car pr)) (n (cdr pr)))
          (cond
            ((or (not (pair? pl)) (equal? (car pl) 'inf) (not (= 1 (caddr pl))) (< n 0))
             (loop (cdr ds) rows #f))
            ((= n 0) (loop (cdr ds) rows ok))
            (else
             (let ((ys (hypn3-y-series P (car pl) (cadr pl) x N)))
               (if (equal? ys 'unknown)
                   (loop (cdr ds) rows #f)
                   (let ((y2 (h3-ser-mul ys ys N)))
                     (let inner ((rs (range n)) (rows rows))
                       (if (null? rs)
                           (loop (cdr ds) rows ok)
                           (let* ((r (car rs))
                                  (f0 (if (= r 0) '(1 0) '(0 0)))
                                  (f1 (h3-ser-coef ys r))
                                  (f2 (h3-ser-coef y2 r))
                                  (rr (hypn3-l-row f0 f1 f2)))
                             (inner (cdr rs) (append (reverse rr) rows))))))))))))))

; порядок кручения конечного дивизора: k = 1..12, u из точных условий v = k*n
(define (hypn3-torsion-search D P x)
  (if (not (every? (lambda (pr) (>= (cdr pr) 0)) D))
      'unknown
      (let loop ((k 1))
        (if (> k 12)
            'unknown
            (let* ((Dk (map (lambda (pr) (cons (car pr) (* k (cdr pr)))) D))
                   (rows (hypn3-principal-rows Dk P x 10)))
              (if (equal? rows 'unknown)
                  'unknown
                  (let ((bs (if (null? rows)
                                (map (lambda (j) (map (lambda (q) (if (= j q) 1 0)) (range 6)))
                                     (range 6))
                                (try (nullspace rows) (lambda (e) 'unknown)))))
                    (if (equal? bs 'unknown)
                        'unknown
                        (let find ((vs bs))
                          (if (null? vs)
                              (loop (+ k 1))
                              (if (equal? (hypn3-principal-check-vec Dk (car vs) P x) #t)
                                  (list k (car vs))
                                  (find (cdr vs)))))))))))))

; ===== R1.3 spike: ∞ в L(D) и кручении =====
; лоран — список (порядок . пара)
(define (h3-lser-add a b)
  (let loop ((xs a) (acc b))
    (if (null? xs)
        acc
        (let* ((o (car (car xs))) (c (cdr (car xs)))
               (hit (let f ((ys acc))
                      (cond ((null? ys) #f)
                            ((= (car (car ys)) o) (car ys))
                            (else (f (cdr ys)))))))
          (if hit
              (loop (cdr xs)
                    (map (lambda (p) (if (= (car p) o) (cons o (h3-add (cdr p) c)) p)) acc))
              (loop (cdr xs) (append acc (list (cons o c)))))))))

(define (h3-lser-scale c a)
  (map (lambda (p) (cons (car p) (h3-mul c (cdr p)))) a))

(define (h3-lser-mul a b)
  (foldl (lambda (acc pa)
           (foldl (lambda (acc2 pb)
                    (h3-lser-add acc2
                                 (list (cons (+ (car pa) (car pb)) (h3-mul (cdr pa) (cdr pb))))))
                  acc b))
         '() a))

(define (h3-lser-coef a r)
  (let f ((xs a))
    (cond ((null? xs) '(0 0))
          ((= (car (car xs)) r) (cdr (car xs)))
          (else (f (cdr xs))))))

(define (hypn3-basis-inf P k x N)
  (let ((ys (try (hypn3-y-series-inf P k x N) (lambda (e) 'unknown))))
    (if (equal? ys 'unknown)
        'unknown
        (list (list (cons 0 '(1 0))) ys (h3-lser-mul ys ys)))))

; порядок вектора u в ∞-месте; #f если ряд нулевой (unknown)
(define (hypn3-valuation-inf-vec P k v x N)
  (let ((bs (hypn3-basis-inf P k x N)))
    (if (equal? bs 'unknown)
        'unknown
        (let ((s (h3-lser-add (h3-lser-scale (list (nth v 0) (nth v 1)) (car bs))
                              (h3-lser-add (h3-lser-scale (list (nth v 2) (nth v 3)) (cadr bs))
                                           (h3-lser-scale (list (nth v 4) (nth v 5)) (caddr bs))))))
          (let loop ((xs s) (best #f))
            (cond ((null? xs) (if best best 'unknown))
                  ((h3-zero? (cdr (car xs))) (loop (cdr xs) best))
                  (else (loop (cdr xs) (let ((o (car (car xs))))
                                         (if (or (not best) (< o best)) o best))))))))))

(define (hypn3-principal-check-vec2 D v P x)
  (let loop ((ds D))
    (if (null? ds)
        #t
        (let* ((pr (car ds)) (pl (car pr)) (n (cdr pr))
               (vv (if (equal? (car pl) 'inf)
                       (try (hypn3-valuation-inf-vec P (cadr pl) v x 8) (lambda (e) 'unknown))
                       (try (hypn3-valuation-vec P (car pl) (cadr pl) v x 8)
                            (lambda (e) 'unknown)))))
          (cond ((equal? vv 'unknown) 'unknown)
                ((= vv n) (loop (cdr ds)))
                (else #f))))))

; строки v_P(u) >= n_P для конечных и ∞-мест
(define (hypn3-rows-at pl n P x N)
  (cond
    ((< n 0) '())
    ((equal? (car pl) 'inf)
     (let ((bs (hypn3-basis-inf P (cadr pl) x N)))
       (if (equal? bs 'unknown)
           'unknown
           (append-map (lambda (r)
                         (hypn3-l-row (h3-lser-coef (car bs) r)
                                      (h3-lser-coef (cadr bs) r)
                                      (h3-lser-coef (caddr bs) r)))
                       (filter (lambda (o) (< o n))
                               (map car (append (car bs) (cadr bs) (caddr bs))))))))
    (else
     (let ((ys (hypn3-y-series P (car pl) (cadr pl) x N)))
       (if (equal? ys 'unknown)
           'unknown
           (let ((y2 (h3-ser-mul ys ys N)))
             (append-map (lambda (r)
                           (hypn3-l-row (if (= r 0) '(1 0) '(0 0))
                                        (h3-ser-coef ys r)
                                        (h3-ser-coef y2 r)))
                         (filter (lambda (r) (< r n)) (range (+ N 1))))))))))

(define (hypn3-principal-rows2 D P x N)
  (let loop ((ds D) (rows '()))
    (if (null? ds)
        (reverse rows)
        (let* ((pr (car ds)) (rr (hypn3-rows-at (car pr) (cdr pr) P x N)))
          (if (equal? rr 'unknown)
              'unknown
              (loop (cdr ds) (append rr rows)))))))

(define (hypn3-torsion-search2 D P x)
  (let loop ((k 1))
    (if (> k 12)
        'unknown
        (let* ((Dk (map (lambda (pr) (cons (car pr) (* k (cdr pr)))) D))
               (rows (hypn3-principal-rows2 Dk P x 8)))
          (if (equal? rows 'unknown)
              'unknown
              (let ((bs (if (null? rows)
                            (map (lambda (j) (map (lambda (q) (if (= j q) 1 0)) (range 6)))
                                 (range 6))
                            (try (nullspace rows) (lambda (e) 'unknown)))))
                (if (equal? bs 'unknown)
                    'unknown
                    (let find ((vs bs))
                      (if (null? vs)
                          (loop (+ k 1))
                          (if (equal? (hypn3-principal-check-vec2 Dk (car vs) P x) #t)
                              (list k (car vs))
                              (find (cdr vs))))))))))))

; ===== R1.3: сборка logs из H (кандидаты из множителей) =====
(define (h3-factor-args e)
  (if (and (pair? e) (equal? (car e) '*)) (cdr e) (list e)))

(define (h3-pow-parts f)
  (if (and (pair? f) (equal? (car f) '^) (= 3 (length f))
           (symbol? (cadr f)) (integer? (caddr f)) (> (caddr f) 1))
      (let ((b (cadr f)) (k (caddr f)))
        (append (list f b) (if (>= k 2) (list (list '^ b 2)) '())))
      (list f)))

(define (hypn3-candidates H)
  (let ((u (try (together H) (lambda (e) #f))))
    (if (not u)
        '()
        (let* ((nn (try (factor (expand (numer u))) (lambda (e) (numer u))))
               (dd (try (factor (expand (denom u))) (lambda (e) (denom u))))
               (fs (append (h3-factor-args nn) (h3-factor-args dd)))
               (base (filter (lambda (f) (not (number? f))) (append-map h3-pow-parts fs)))
               (prods (append-map (lambda (a)
                                    (map (lambda (b) (simplify (list '* a b))) base))
                                  base)))
          (append (list 1) base prods)))))

(define (hypn3-log-part H P x)
  (let loop ((cs (hypn3-candidates H)))
    (if (null? cs)
        (hypn3-g-nonelementary H P x)
        (let* ((u (car cs))
               (lg (list 'logs 1 (list (list 1 1 u)))))
          (if (and (not (equal? (simplify u) 0))
                   (try (hypn3-log-check H P x lg) (lambda (e) #f)))
              lg
              (loop (cdr cs)))))))

; ---------- R1b.2: вычеты над неприводимым g(x), b ∈ ℚ(α), b³ ≡ P (mod g) ----------
; Элемент ℚ(α,ζ₃) — пара (u v) = u + vζ, u,v — ib-p по модулю g.
; h3-* работает с рациональными коэффициентами, поэтому здесь своя арифметика.

(define (h3p-zero? u) (and (ib-p-zero? (car u)) (ib-p-zero? (cadr u))))
(define (h3p-num c) (list (if (= c 0) '() (list c)) '()))
(define (h3p-add u v) (list (ib-p-add (car u) (car v)) (ib-p-add (cadr u) (cadr v))))
(define (h3p-neg u) (list (ib-p-neg (car u)) (ib-p-neg (cadr u))))
(define (h3p-sub u v) (h3p-add u (h3p-neg v)))
(define (h3p-scale u c) (list (ib-p-scale (car u) c) (ib-p-scale (cadr u) c)))

; (a+bζ)(c+dζ) = (ac−bd) + (ad+bc−bd)ζ, ζ² = −1−ζ
(define (h3p-mul u v gg)
  (let* ((a (car u)) (b (cadr u)) (c (car v)) (d (cadr v))
         (bd (dv-a-mod (ib-p-mul b d) gg))
         (r0 (ib-p-sub (dv-a-mod (ib-p-mul a c) gg) bd))
         (r1 (ib-p-sub (ib-p-add (dv-a-mod (ib-p-mul a d) gg)
                                 (dv-a-mod (ib-p-mul b c) gg))
                       bd)))
    (list (dv-a-mod r0 gg) (dv-a-mod r1 gg))))

; норма N = a²−ab+b²; (a+bζ)^{-1} = ((a−b) − bζ)/N
(define (h3p-inv u gg)
  (let* ((a (car u)) (b (cadr u))
         (N (dv-a-mod (ib-p-add (ib-p-sub (dv-a-mod (ib-p-mul a a) gg)
                                          (dv-a-mod (ib-p-mul a b) gg))
                                (dv-a-mod (ib-p-mul b b) gg))
                      gg)))
    (if (ib-p-zero? N)
        #f
        (let ((iv (dv-a-inv N gg)))
          (if (not iv)
              #f
              (list (dv-a-mod (ib-p-mul (ib-p-sub a b) iv) gg)
                    (dv-a-mod (ib-p-mul (ib-p-neg b) iv) gg)))))))

(define (h3p-div u v gg)
  (let ((iv (and v (h3p-inv v gg))))
    (if iv (h3p-mul u iv gg) #f)))

(define (h3p-pow u n gg)
  (let loop ((k n) (base u) (acc (h3p-num 1)))
    (if (= k 0)
        acc
        (loop (quotient k 2)
              (h3p-mul base base gg)
              (if (= 1 (remainder k 2)) (h3p-mul acc base gg) acc)))))

; значение выражения от x,y при x = α, y = bp (пара)
(define (h3p-eval e alpha bp x gg)
  (cond ((number? e) (h3p-num e))
        ((equal? e x) (list alpha '()))
        ((equal? e 'y) bp)
        ((pair? e)
         (let ((as (cdr e)))
           (cond
             ((equal? (car e) '+)
              (foldl (lambda (acc t)
                       (if (not acc) #f
                           (let ((v (h3p-eval t alpha bp x gg)))
                             (if v (h3p-add acc v) #f))))
                     (h3p-num 0) as))
             ((equal? (car e) '*)
              (foldl (lambda (acc t)
                       (if (not acc) #f
                           (let ((v (h3p-eval t alpha bp x gg)))
                             (if v (h3p-mul acc v gg) #f))))
                     (h3p-num 1) as))
             ((equal? (car e) '-)
              (let ((v (h3p-eval (car as) alpha bp x gg)))
                (if (not v) #f
                    (if (null? (cdr as))
                        (h3p-neg v)
                        (let ((w (h3p-eval (cadr as) alpha bp x gg)))
                          (if w (h3p-sub v w) #f))))))
             ((equal? (car e) '/)
              (let ((v (h3p-eval (car as) alpha bp x gg))
                    (w (h3p-eval (cadr as) alpha bp x gg)))
                (if (and v w (not (h3p-zero? w))) (h3p-div v w gg) #f)))
             ((equal? (car e) '^)
              (let ((v (h3p-eval (car as) alpha bp x gg)) (n (cadr as)))
                (if (and v (integer? n) (>= n 0)) (h3p-pow v n gg) #f)))
             (else #f))))
        (else #f)))

; коэффициент s^r в P(α+s) по модулю g
(define (dv-a-pseries pp gg r)
  (let loop ((t 0) (acc '()))
    (if (>= t (length pp))
        (dv-a-mod acc gg)
        (loop (+ t 1)
              (ib-p-add acc (ib-p-scale (dv-a-monom t r gg) (nth pp t)))))))

; b ∈ ℚ(α) с b³ ≡ P (mod g): линейный множитель T − b у T³ − c
(define (hypn3-g-cube-root g P x)
  (let ((gg (try (ib-poly-parse g x) (lambda (e) #f)))
        (pp (try (ib-poly-parse P x) (lambda (e) #f))))
    (if (or (not gg) (not pp) (< (ib-p-deg gg) 2))
        #f
        (let* ((rem (dv-a-mod pp gg))
               (ge (subst (list (list x 't)) g))
               (ce (ib-poly->expr rem 't))
               (alpha (list 'root-of ge 't))
               (fac (try (factor-over (list '- (list '^ 'R1S 3) ce) 'R1S alpha)
                         (lambda (e) #f))))
          (if (not fac)
              'tower
              (let loop ((fs (cdr fac)))
                (if (null? fs)
                    'tower
                    (let* ((f (car (car fs)))
                           (dg (try (degree f 'R1S) (lambda (e) 0))))
                      (if (= dg 1)
                          (let* ((a (simplify (coeff f 'R1S 1)))
                                 (b0 (simplify (coeff f 'R1S 0)))
                                 (root (simplify (list '/ (list '* -1 b0) a)))
                                 (rt (replace-expr root alpha 't))
                                 (F (try (alg-field ge 't) (lambda (e) #f))))
                            (if (not F)
                                (loop (cdr fs))
                                (let ((bb (try (expr->alg F rt) (lambda (e) #f))))
                                  (if (and bb (equal? (dv-a-mod (dv-a-pow bb 3 gg) gg) rem))
                                      bb
                                      (loop (cdr fs))))))
                          (loop (cdr fs)))))))))))

; пара y = ζ^k·b
(define (hypn3-yk b k)
  (cond ((= k 0) (list b '()))
        ((= k 1) (list '() b))
        (else (list (ib-p-neg b) (ib-p-neg b)))))

; вычет H dx в месте (α, ζ^k b): N/(D_x + D_y·y′), y′ = P′/(3y²)
(define (hypn3-g-residue H P g b k x)
  (let* ((gg (ib-poly-parse g x))
         (pp (ib-poly-parse P x))
         (alpha (list 0 1))
         (bp (hypn3-yk b k))
         (N (h3p-eval (numer H) alpha bp x gg))
         (Dv (h3p-eval (denom H) alpha bp x gg))
         (Dx (h3p-eval (diff x (denom H)) alpha bp x gg))
         (Dy (h3p-eval (diff 'y (denom H)) alpha bp x gg)))
    (if (or (not N) (not Dv) (not Dx) (not Dy))
        'unknown
        (if (not (h3p-zero? Dv))
            (h3p-num 0)                          ; нет полюса
            (let* ((dp (dv-a-pseries pp gg 1))
                   (den (h3p-scale (h3p-mul (hypn3-yk b k) (hypn3-yk b k) gg) 3))
                   (ypp (h3p-div (list dp '()) den gg)))
              (if (not ypp)
                  'unknown
                  (let ((den2 (h3p-add Dx (h3p-mul Dy ypp gg))))
                    (if (h3p-zero? den2) 'unknown (h3p-div N den2 gg)))))))))

; данные: ((g b ((k u v) …)) …) по неприводимым g результанта
(define (hypn3-g-residues H P x)
  (let* ((Dn (try (expand (denom H)) (lambda (e) #f)))
         (R (and Dn (try (expand (resultant Dn (list '- (list '^ 'y 3) P) 'y))
                         (lambda (e) #f))))
         (fl (and R (try (factor-list R) (lambda (e) #f)))))
    (if (or (not Dn) (not R) (not (pair? fl)))
        'unknown
        (let loop ((fs (cdr fl)) (acc '()))
          (if (null? fs)
              (if (null? acc) 'unknown (reverse acc))
              (let* ((g (car (car fs)))
                     (gg (try (ib-poly-parse g x) (lambda (e) #f))))
                (if (or (not gg) (< (ib-p-deg gg) 2))
                    (loop (cdr fs) acc)
                    (let ((b (hypn3-g-cube-root g P x)))
                      (cond
                        ((or (not b) (equal? b 'tower)) 'unknown)
                        (else
                         (let ((rs (map (lambda (k)
                                          (let ((r (hypn3-g-residue H P g b k x)))
                                            (if (equal? r 'unknown)
                                                'unknown
                                                (list k (car r) (cadr r)))))
                                        (range 3))))
                           (if (member? 'unknown rs)
                               'unknown
                               (loop (cdr fs) (cons (list g b rs) acc))))))))))))))

; ---------- R1b.2: ряд y(s) в ℚ(α,ζ₃) ----------

(define (h3ps-ref ys r)
  (if (< r (length ys)) (nth ys r) (h3p-num 0)))

(define (h3ps-mul a b N gg)
  (let loop ((r 0) (acc '()))
    (if (> r N)
        (reverse acc)
        (loop (+ r 1)
              (cons (let sum ((i 0) (s (h3p-num 0)))
                      (if (> i r)
                          s
                          (sum (+ i 1)
                               (h3p-add s (h3p-mul (h3ps-ref a i) (h3ps-ref b (- r i)) gg)))))
                    acc)))))

(define (h3ps-cube a N gg) (h3ps-mul (h3ps-mul a a N gg) a N gg))

; y(s)³ = P(α+s), y_0 = ζ^k b; список пар по порядку 0..N
(define (hypn3-y-series-g P g b k x N)
  (let* ((gg (ib-poly-parse g x))
         (pp (ib-poly-parse P x))
         (y0 (hypn3-yk b k))
         (inv (h3p-inv (h3p-scale (h3p-mul y0 y0 gg) 3) gg)))
    (if (not inv)
        'unknown
        (let loop ((r 1) (ys (list y0)))
          (if (> r N)
              ys
              (let* ((Pr (dv-a-pseries pp gg r))
                     (part (append ys (list (h3p-num 0))))
                     (cr (nth (h3ps-cube part r gg) r))
                     (yr (h3p-mul (h3p-sub (list Pr '()) cr) inv gg)))
                (loop (+ r 1) (append ys (list yr)))))))))

; ---------- R1b.2: нормальное замыкание K = ℚ(α,i), i² = −1 ----------
; Элемент K — пара (A B) = A + B·i, A,B — ib-p по модулю g.

(define (i2-num c) (list (if (= c 0) '() (list c)) '()))
(define (i2-add u v) (list (ib-p-add (car u) (car v)) (ib-p-add (cadr u) (cadr v))))
(define (i2-neg u) (list (ib-p-neg (car u)) (ib-p-neg (cadr u))))
(define (i2-sub u v) (i2-add u (i2-neg v)))
(define (i2-zero? u) (and (ib-p-zero? (car u)) (ib-p-zero? (cadr u))))

(define (i2-mul u v gg)
  (let* ((a (car u)) (b (cadr u)) (c (car v)) (d (cadr v)))
    (list (dv-a-mod (ib-p-sub (ib-p-mul a c) (ib-p-mul b d)) gg)
          (dv-a-mod (ib-p-add (ib-p-mul a d) (ib-p-mul b c)) gg))))

(define (i2-inv u gg)
  (let* ((a (car u)) (b (cadr u))
         (N (dv-a-mod (ib-p-add (ib-p-mul a a) (ib-p-mul b b)) gg)))
    (if (ib-p-zero? N)
        #f
        (let ((iv (dv-a-inv N gg)))
          (if (not iv)
              #f
              (list (dv-a-mod (ib-p-mul a iv) gg)
                    (dv-a-mod (ib-p-mul (ib-p-neg b) iv) gg)))))))

(define (i2-div u v gg)
  (let ((iv (and v (i2-inv v gg))))
    (if iv (i2-mul u iv gg) #f)))

(define (i2-pow u n gg)
  (let loop ((k n) (base u) (acc (i2-num 1)))
    (if (= k 0)
        acc
        (loop (quotient k 2)
              (i2-mul base base gg)
              (if (= 1 (remainder k 2)) (i2-mul acc base gg) acc)))))

; четыре корня g = x⁴ − 7 в K: α, −α, iα, −iα
(define (hypn3-g-roots)
  (list (list (list 0 1) '())
        (list (list 0 -1) '())
        (list '() (list 0 1))
        (list '() (list 0 -1))))

(define (i2-ref a r) (if (< r (length a)) (nth a r) (i2-num 0)))

(define (i2-ser-mul a b N gg)
  (let loop ((r 0) (acc '()))
    (if (> r N)
        (reverse acc)
        (loop (+ r 1)
              (cons (let sum ((i 0) (s (i2-num 0)))
                      (if (> i r)
                          s
                          (sum (+ i 1)
                               (i2-add s (i2-mul (i2-ref a i) (i2-ref b (- r i)) gg)))))
                    acc)))))

(define (i2-ser-cube a N gg) (i2-ser-mul (i2-ser-mul a a N gg) a N gg))

; коэффициент s^r в P(α_j+s) для K-корня alpha
(define (i2-pseries pp gg alpha r)
  (let loop ((t 0) (acc (i2-num 0)))
    (if (>= t (length pp))
        acc
        (loop (+ t 1)
              (i2-add acc
                      (i2-mul (i2-num (nth pp t))
                              (i2-mul (i2-num (dv-binom t r))
                                      (i2-pow alpha (- t r) gg) gg)
                              gg))))))

; y(s)³ = P(α_j+s), y_0 = b (b ∈ ℚ); список K-элементов по порядку 0..N
(define (hypn3-y-series-K P g alpha b N)
  (let* ((gg (ib-poly-parse g 'x))
         (pp (ib-poly-parse P 'x))
         (y0 (i2-num b))
         (inv (i2-inv (i2-num (* 3 b b)) gg)))
    (if (not inv)
        'unknown
        (let loop ((r 1) (ys (list y0)))
          (if (> r N)
              ys
              (let* ((Pr (i2-pseries pp gg alpha r))
                     (cr (nth (i2-ser-cube (append ys (list (i2-num 0))) r gg) r))
                     (yr (i2-mul (i2-sub Pr cr) inv gg)))
                (loop (+ r 1) (append ys (list yr)))))))))

; ---------- R1b.2: F = K(ζ₃), ζ² = −1−ζ; элемент — пара (A B) = A + Bζ, A,B : K ----------

(define (z2-num c) (list (i2-num c) (i2-num 0)))
(define (z2-add u v) (list (i2-add (car u) (car v)) (i2-add (cadr u) (cadr v))))
(define (z2-neg u) (list (i2-neg (car u)) (i2-neg (cadr u))))
(define (z2-sub u v) (z2-add u (z2-neg v)))
(define (z2-zero? u) (and (i2-zero? (car u)) (i2-zero? (cadr u))))

(define (z2-mul u v gg)
  (let* ((a (car u)) (b (cadr u)) (c (car v)) (d (cadr v))
         (bd (i2-mul b d gg)))
    (list (i2-sub (i2-mul a c gg) bd)
          (i2-sub (i2-add (i2-mul a d gg) (i2-mul b c gg)) bd))))

(define (z2-norm u gg)
  (let ((a (car u)) (b (cadr u)))
    (i2-add (i2-sub (i2-mul a a gg) (i2-mul a b gg)) (i2-mul b b gg))))

(define (z2-inv u gg)
  (let ((N (z2-norm u gg)))
    (if (i2-zero? N)
        #f
        (let ((iv (i2-inv N gg)))
          (if (not iv)
              #f
              (list (i2-mul (i2-sub (car u) (cadr u)) iv gg)
                    (i2-mul (i2-neg (cadr u)) iv gg)))))))

(define (z2-div u v gg)
  (let ((iv (and v (z2-inv v gg))))
    (if iv (z2-mul u iv gg) #f)))

(define (z2-pow u n gg)
  (let loop ((k n) (base u) (acc (z2-num 1)))
    (if (= k 0)
        acc
        (loop (quotient k 2)
              (z2-mul base base gg)
              (if (= 1 (remainder k 2)) (z2-mul acc base gg) acc)))))

(define (hypn3-y0-F b k)
  (cond ((= k 0) (list (i2-num b) (i2-num 0)))
        ((= k 1) (list (i2-num 0) (i2-num b)))
        (else (list (i2-num (- b)) (i2-num (- b))))))

(define (z2-ref a r) (if (< r (length a)) (nth a r) (z2-num 0)))

(define (z2-ser-mul a b N gg)
  (let loop ((r 0) (acc '()))
    (if (> r N)
        (reverse acc)
        (loop (+ r 1)
              (cons (let sum ((i 0) (s (z2-num 0)))
                      (if (> i r)
                          s
                          (sum (+ i 1)
                               (z2-add s (z2-mul (z2-ref a i) (z2-ref b (- r i)) gg)))))
                    acc)))))

(define (z2-ser-cube a N gg) (z2-ser-mul (z2-ser-mul a a N gg) a N gg))

(define (z2-pseries pp gg alpha r)
  (let loop ((t 0) (acc (z2-num 0)))
    (if (>= t (length pp))
        acc
        (loop (+ t 1)
              (z2-add acc
                      (z2-mul (z2-num (nth pp t))
                              (z2-mul (z2-num (dv-binom t r))
                                      (list (i2-pow alpha (- t r) gg) (i2-num 0))
                                      gg)
                              gg))))))

(define (hypn3-y-series-F P g alpha k b N)
  (let* ((gg (ib-poly-parse g 'x))
         (pp (ib-poly-parse P 'x))
         (y0 (hypn3-y0-F b k))
         (inv (z2-inv (z2-mul (z2-num 3) (z2-mul y0 y0 gg) gg) gg)))
    (if (not inv)
        'unknown
        (let loop ((r 1) (ys (list y0)))
          (if (> r N)
              ys
              (let* ((Pr (z2-pseries pp gg alpha r))
                     (cr (nth (z2-ser-cube (append ys (list (z2-num 0))) r gg) r))
                     (yr (z2-mul (z2-sub Pr cr) inv gg)))
                (loop (+ r 1) (append ys (list yr)))))))))

; ---------- строки Трагера в F: u = c₀+c₁y+c₂y², 48 неизвестных ----------

(define (vec-trim l)
  (let loop ((r (reverse l)))
    (cond ((null? r) '())
          ((= 0 (car r)) (loop (cdr r)))
          (else (reverse r)))))

(define (vec-slice v s n)
  (if (<= n 0)
      '()
      (let loop ((i 0) (acc '()))
        (if (= i n) (reverse acc) (loop (+ i 1) (cons (nth v (+ s i)) acc))))))

(define (pad4 p)
  (let loop ((i 0) (acc '()))
    (if (= i 4) (reverse acc)
        (loop (+ i 1) (cons (if (< i (length p)) (nth p i) 0) acc)))))

(define (k-coords u) (append (pad4 (car u)) (pad4 (cadr u))))
(define (z-coords u) (append (k-coords (car u)) (k-coords (cadr u))))

(define (coords->z v)
  (list (list (vec-trim (vec-slice v 0 4)) (vec-trim (vec-slice v 4 4)))
        (list (vec-trim (vec-slice v 8 4)) (vec-trim (vec-slice v 12 4)))))

(define (dv-mat-transpose M)
  (if (null? M)
      '()
      (let loop ((j 0) (acc '()))
        (if (= j (length (car M)))
            (reverse acc)
            (loop (+ j 1) (cons (map (lambda (r) (nth r j)) M) acc))))))

(define (unit16 j)
  (let loop ((i 0) (acc '()))
    (if (= i 16) (reverse acc)
        (loop (+ i 1) (cons (if (= i j) 1 0) acc)))))

(define (z-mat w gg)
  (let loop ((j 0) (cols '()))
    (if (= j 16)
        (dv-mat-transpose (reverse cols))
        (loop (+ j 1)
              (cons (z-coords (z2-mul (coords->z (unit16 j)) w gg)) cols)))))

(define (zero-rows16 wdt)
  (map (lambda (i) (map (lambda (j) 0) (range wdt))) (range 16)))

; map в диалекте берёт одну последовательность — почленная функция двух списков
(define (dv-zip2 f a b)
  (if (or (null? a) (null? b))
      '()
      (cons (f (car a) (car b)) (dv-zip2 f (cdr a) (cdr b)))))

(define (add-block rows M ofs)
  (dv-zip2 (lambda (ri Mi)
             (append (vec-slice ri 0 ofs)
                     (dv-zip2 (lambda (a b) (+ a b)) (vec-slice ri ofs 16) Mi)
                     (vec-slice ri (+ ofs 16) (- 48 (+ ofs 16)))))
           rows M))

(define (hypn3-F-place-rows P g alpha k b e)
  (let* ((gg (ib-poly-parse g 'x))
         (N (max 0 (- e 1)))
         (ys (hypn3-y-series-F P g alpha k b N))
         (y2 (z2-ser-mul ys ys N gg)))
    (if (equal? ys 'unknown)
        'unknown
        (let loop ((r 0) (rows (zero-rows16 48)))
          (if (>= r e)
              rows
              (loop (+ r 1)
                    (add-block
                     (add-block
                      (add-block rows (z-mat (if (= r 0) (z2-num 1) (z2-num 0)) gg) 0)
                      (z-mat (z2-ref ys r) gg) 16)
                     (z-mat (z2-ref y2 r) gg) 32)))))))

; значение ib-p многочлена в K-точке alpha
(define (i2-poly-eval p alpha gg)
  (let loop ((cs (reverse (ib-p-trim p))) (acc (i2-num 0)))
    (if (null? cs)
        acc
        (loop (cdr cs) (i2-add (i2-mul acc alpha gg) (i2-num (car cs)))))))

; вычеты по всем 4 корням g и 3 ветвям: ((j k) . 16 координат F)
(define (hypn3-g-all-residues dat x)
  (let* ((g (nth (car dat) 0)) (rs (nth (car dat) 2))
         (gg (ib-poly-parse g x))
         (roots (hypn3-g-roots)))
    (append-map
     (lambda (j)
       (let ((alpha (nth roots j)))
         (map (lambda (k)
                (let* ((r (nth rs k))
                       (U (i2-poly-eval (nth r 1) alpha gg))
                       (V (i2-poly-eval (nth r 2) alpha gg)))
                  (cons (list j k) (z-coords (list U V)))))
              (range 3))))
     (range 4))))

; v_P(u) по вектору 48 координат в месте (j k)
(define (hypn3-F-vec-valuation P g b v j k N)
  (let* ((gg (ib-poly-parse g 'x))
         (alpha (nth (hypn3-g-roots) j))
         (ys (hypn3-y-series-F P g alpha k b N))
         (y2 (z2-ser-mul ys ys N gg))
         (c0 (coords->z (vec-slice v 0 16)))
         (c1 (coords->z (vec-slice v 16 16)))
         (c2 (coords->z (vec-slice v 32 16))))
    (let loop ((r 0))
      (if (> r N)
          'inf
          (let ((ur (z2-add (if (= r 0) c0 (z2-num 0))
                            (z2-add (z2-mul c1 (z2-ref ys r) gg)
                                    (z2-mul c2 (z2-ref y2 r) gg)))))
            (if (z2-zero? ur) (loop (+ r 1)) r))))))

; u = (c₀+c₁y+c₂y²)/g^mden с div u = k·delta; ищем v(num) ≥ mden + k·n
(define (hypn3-g-principal P g b delta k)
  (let* ((gg (ib-poly-parse g 'x))
         (roots (hypn3-g-roots))
         (mden (foldl (lambda (a pr) (max a (max 0 (- (cdr pr))))) 0 delta))
         (eof (lambda (n) (+ mden (* k n))))
         (rows (foldl
                (lambda (acc pr)
                  (let* ((pl (car pr)) (e (eof (cdr pr))))
                    (if (<= e 0)
                        acc
                        (append acc (hypn3-F-place-rows
                                     P g (nth roots (car pl)) (cadr pl) b e)))))
                '() delta))
         (N (foldl (lambda (a pr) (max a (eof (cdr pr)))) 0 delta)))
    (if (null? rows)
        #f
        (let ((ker (try (fm-nullspace (field-Q) rows) (lambda (e) 'unknown))))
          (if (or (equal? ker 'unknown) (null? ker))
              #f
              (let loop ((vs ker))
                (if (null? vs)
                    #f
                    (let* ((v (car vs))
                           (ok (every? (lambda (pr)
                                         (equal? (hypn3-F-vec-valuation
                                                  P g b v (car (car pr)) (cadr (car pr)) N)
                                                 (eof (cdr pr))))
                                       delta)))
                      (if ok v (loop (cdr vs)))))))))))

; 'nonelementary, если хоть одна ℚ-компонента δ не крутильная; иначе 'unknown
(define (hypn3-g-nonelementary H P x)
  (let ((dat (try (hypn3-g-residues H P x) (lambda (e) 'unknown))))
    (if (or (equal? dat 'unknown) (null? dat))
        'unknown
        (let* ((g (nth (car dat) 0)) (bp (nth (car dat) 1))
               (b (and (= 0 (ib-p-deg bp)) (car (ib-p-trim bp))))
               (res (hypn3-g-all-residues dat x))
               (m (foldl (lambda (a pr)
                           (foldl (lambda (a1 c) (dv-lcm2 a1 (denom (together c))))
                                  a (cdr pr)))
                         1 res)))
          (if (not b)
              'unknown
              (let loop ((c 0) (verdict 'unknown))
            (if (> c 15)
                verdict
                (let* ((delta (let build ((ps res) (acc '()))
                                (if (null? ps)
                                    (reverse acc)
                                    (let* ((pr (car ps)) (n (* m (nth (cdr pr) c))))
                                      (build (cdr ps)
                                             (if (= n 0) acc (cons (cons (car pr) n) acc))))))))
                  (cond
                    ((null? delta) (loop (+ c 1) verdict))
                    (else
                     (let found ((ks (map (lambda (i) (+ i 1)) (range 12))))
                       (cond ((null? ks)
                              (loop (+ c 1) 'nonelementary))
                             ((hypn3-g-principal P g b delta (car ks))
                              (loop (+ c 1) verdict))
                             (else (found (cdr ks)))))))))))))))

; ===== R1.4: #J(F_p) через дзета-функцию для рода >= 3 =====
(define (dv-tuples p k)
  (if (= k 0)
      (list '())
      (append-map (lambda (c)
                    (map (lambda (t) (cons c t)) (dv-tuples p (- k 1))))
                  (range p))))

(define dv-irr-cache '())

(define (dv-irr-lookup p k)
  (let loop ((cs dv-irr-cache))
    (cond ((null? cs) #f)
          ((and (= (car (car cs)) p) (= (cadr (car cs)) k)) (nth (car cs) 2))
          (else (loop (cdr cs))))))

; разреженные кандидаты: x^k + a x^j + b и x^k + a x^j (j = 1..k-1)
(define (dv-sparse-cands p k)
  (let ((js (map (lambda (i) (+ i 1)) (range (- k 1))))
        (idx (range (+ k 1))))
    (append
     (append-map (lambda (j)
                   (append-map (lambda (a)
                                 (map (lambda (b)
                                        (map (lambda (i)
                                               (cond ((= i 0) b) ((= i j) a) ((= i k) 1) (else 0)))
                                             idx))
                                      (range p)))
                               (range p)))
                 js)
     (append-map (lambda (j)
                   (map (lambda (a)
                          (map (lambda (i)
                                 (cond ((= i j) a) ((= i k) 1) (else 0)))
                               idx))
                        (map (lambda (i) (+ i 1)) (range (- p 1)))))
                 js))))

(define (dv-irr-poly p k)
  (or (dv-irr-lookup p k)
      (let ((found (let loop ((cs (append (dv-sparse-cands p k) (dv-tuples p k))))
                     (cond ((null? cs) #f)
                           ((true? (gf-irreducible? (car cs) p)) (car cs))
                           (else (loop (cdr cs)))))))
        (if found
            (begin (set! dv-irr-cache (cons (list p k found) dv-irr-cache)) found)
            'unknown))))

(define (dv-count-generic F pl p e k)
  (foldl (lambda (acc cs)
           (let* ((a (gf-elt F cs))
                  (v (dv-gf-peval pl a p F))
                  (iv (gf->int F v))
                  (ch (if (= iv 0) 0 (dv-gf-char-val (gf-power F v e) p F))))
             (+ acc 1 ch)))
         0 (dv-tuples p k)))

(define (hyp-count-points-k P x p k)
  (let ((pl (dv-pmod-coeffs P x p)))
    (if (equal? pl 'unknown)
        'unknown
        (let* ((nd (ib-p-deg pl))
               (lc (ib-p-lc pl))
               (inf (if (even? nd) (+ 1 (jacobi lc p)) 1)))
          (cond
            ((= k 1)
             (+ (let loop ((a 0) (s 0))
                  (if (= a p)
                      s
                      (loop (+ a 1) (+ s 1 (jacobi (dv-pmod-eval pl a p) p)))))
                inf))
            (else
             (let ((m (dv-prim-poly p k)))
               (if (equal? m 'unknown)
                   'unknown
                   (+ (dv-count-tables pl p m k) inf)))))))))

; Подсчёт ∑(1 + χ(P(a))) по a ∈ 𝔽_q (q = p^k) без общей арифметики поля: порождающий g, таблицы g^i (цифры по основанию p)
; и логарифмов; a = g^i, aʲ = g^(ij mod q−1), значение P(a) — сумма цифровых векторов cⱼ·aʲ, χ — чётность логарифма.
; m — моническое неприводимое (коэффициенты по возрастанию), ответ совпадает с dv-count-generic.
; R5.2: элемент 𝔽_q = целое (цифры по основанию p, младшая — коэффициент при 1). Порождающий — корень x примитивного
; многочлена m: умножение на x — арифметика над целыми (сдвиг цифр + поправка по ненулевым членам m). Таблицы: E[i] = код x^i,
; lg[код] = i, Z[d] = log(1 + x^d) (логарифм Жюши, −1 — нуль). P(x^i) = Σ cⱼ·x^(ij) складывается в логарифмах:
; log(u + v) = log u + Z(log v − log u). χ(v) — чётность lg v. Цикл Фробениуса i → p·i (mod q−1) сохраняет χ(P(a)), считаем один
; представитель орбиты с весом её размера.
(define (dv-code-digits c p k)
  (let loop ((i 0) (c c) (acc '()))
    (if (= i k) (reverse acc) (loop (+ i 1) (quotient c p) (cons (modulo c p) acc)))))

(define dv-prim-cache '())

; (−1)^k·m₀ — норма x — порождает 𝔽_p* (необходимо для примитивности x)
(define (dv-norm-ok? m0 p k)
  (let ((a (modulo (if (even? k) m0 (- m0)) p)))
    (and (> a 0)
         (let loop ((e 1) (v a))
           (cond ((= v 1) (= e (- p 1))) ((>= e p) #f) (else (loop (+ e 1) (modulo (* v a) p))))))))

; произведение a·b по модулю m в 𝔽_p[x] (a, b — векторы длины k по возрастанию, mv — вектор младших коэффициентов m)
(define (dv-mulmod a b mv p k)
  (let ((r (make-vector (- (* 2 k) 1) 0)))
    (let il ((i 0))
      (if (< i k)
          (let ((ai (vref a i)))
            (if (> ai 0)
                (let jl ((j 0))
                  (if (< j k)
                      (begin (vset! r (+ i j) (+ (vref r (+ i j)) (* ai (vref b j)))) (jl (+ j 1))))))
            (il (+ i 1)))))
    (let dl ((d (- (* 2 k) 2)))
      (if (>= d k)
          (let ((c (modulo (vref r d) p)))
            (if (> c 0)
                (let tl ((t 0))
                  (if (< t k)
                      (begin (vset! r (+ (- d k) t) (- (vref r (+ (- d k) t)) (* c (vref mv t)))) (tl (+ t 1))))))
            (dl (- d 1)))))
    (let ((o (make-vector k 0)))
      (let fl ((i 0))
        (if (< i k) (begin (vset! o i (modulo (vref r i) p)) (fl (+ i 1)))))
      o)))

; x^e mod m (вектор)
(define (dv-xpow e xv mv p k)
  (if (= e 0)
      (let ((o (make-vector k 0))) (vset! o 0 1) o)
      (let* ((h (dv-xpow (quotient e 2) xv mv p k))
             (h2 (dv-mulmod h h mv p k)))
        (if (odd? e) (dv-mulmod h2 xv mv p k) h2))))

(define (dv-vec-one? v k)
  (and (= (vref v 0) 1)
       (let loop ((i 1)) (or (= i k) (and (= (vref v i) 0) (loop (+ i 1)))))))

; x порождает (𝔽_p[x]/m)* порядка q−1 ⇒ кольцо — поле (иначе единиц меньше q−1) и x примитивен; rs — простые делители q−1
(define (dv-prim-candidate? m p k rs)
  (and (> (car m) 0)
       (dv-norm-ok? (car m) p k)
       (let loop ((a 1)) (or (= a p) (and (not (= 0 (dv-pmod-eval m a p))) (loop (+ a 1)))))   ; нет корней в 𝔽_p
       (let* ((mv (list->vector (take m k)))
              (xv (let ((o (make-vector k 0))) (vset! o 1 1) o))
              (n (- (^ p k) 1)))
         (and (dv-vec-one? (dv-xpow n xv mv p k) k)
              (every? (lambda (r) (not (dv-vec-one? (dv-xpow (quotient n r) xv mv p k) k))) rs)))))

; моническое m степени k над 𝔽_p, для которого x порождает 𝔽_q* (по возрастанию степеней; тем самым m неприводим); разреженные первыми
(define (dv-prim-poly p k)
  (let ((hit (assoc (list p k) dv-prim-cache)))
    (if hit
        (cdr hit)
        (let* ((q (^ p k))
               (rs (map car (factor-integer (- q 1))))
               (found (let loop ((c 1))      ; хвост m — цифры c: малые c дают мало ненулевых членов
                        (if (>= c q)
                            #f
                            (let ((m (append (dv-code-digits c p k) (list 1))))
                              (if (dv-prim-candidate? m p k rs) m (loop (+ c 1))))))))
          (let ((r (or found 'unknown)))
            (set! dv-prim-cache (cons (cons (list p k) r) dv-prim-cache))
            r)))))

; Σ_{a ∈ 𝔽_q} (1 + χ(P(a))) (без бесконечной точки); m — примитивный многочлен из dv-prim-poly, p нечётное
(define (dv-count-tables pl p m k)
  (let* ((q (^ p k)) (n (- q 1)) (P1 (^ p (- k 1)))
         (nm0 (modulo (- (car m)) p))
         (hi (let loop ((j 1) (cs (cdr m)) (acc '()))
               (if (= j k)
                   (reverse acc)
                   (loop (+ j 1) (cdr cs)
                         (if (= (car cs) 0) acc (cons (cons (^ p j) (modulo (- (car cs)) p)) acc))))))
         (E (make-vector n 0))
         (lg (make-vector q -1))
         (Z (make-vector n -1))
         (tp (ib-p-trim pl))
         (c0 (if (null? tp) 0 (modulo (car tp) p))))
    (let build ((i 0) (c 1))
      (if (< i n)
          (begin
            (vset! E i c)
            (vset! lg c i)
            (let* ((top (quotient c P1)) (sh (* (- c (* top P1)) p)))
              (build (+ i 1)
                     (if (= top 0)
                         sh
                         (let fix ((hs hi) (sh (+ sh (modulo (* top nm0) p))))
                           (if (null? hs)
                               sh
                               (let* ((pw (car (car hs)))
                                      (dj (modulo (quotient sh pw) p))
                                      (nd (modulo (+ dj (* top (cdr (car hs)))) p)))
                                 (fix (cdr hs) (+ sh (* (- nd dj) pw))))))))))
          (if (not (= c 1)) (error "dv-count-tables: x не порождает 𝔽_q*"))))
    (let zf ((d 0))
      (if (< d n)
          (let ((c (vref E d)))
            (vset! Z d (vref lg (if (= (modulo c p) (- p 1)) (- c (- p 1)) (+ c 1))))
            (zf (+ d 1)))))
    (let* ((tl (let loop ((cs (if (null? tp) '() (cdr tp))) (j 1) (acc '()))
                 (cond ((null? cs) (reverse acc))
                       ((= (car cs) 0) (loop (cdr cs) (+ j 1) acc))
                       (else (loop (cdr cs) (+ j 1) (cons (cons j (vref lg (modulo (car cs) p))) acc))))))
           (acc0 (if (= c0 0) -1 (vref lg c0)))
           (vis (make-vector n 0)))
      (let loop ((i 0) (s (if (= c0 0) 1 (+ 1 (if (even? (vref lg c0)) 1 -1)))))
        (if (= i n)
            s
            (if (= (vref vis i) 1)
                (loop (+ i 1) s)
                (let* ((w (let ow ((j i) (w 1))
                            (vset! vis j 1)
                            (let ((j2 (modulo (* j p) n)))
                              (if (= j2 i) w (ow j2 (+ w 1))))))
                       (acc (let ev ((ts tl) (acc acc0))
                              (if (null? ts)
                                  acc
                                  (let ((v (modulo (+ (cdr (car ts)) (* i (car (car ts)))) n)))
                                    (ev (cdr ts)
                                        (if (< acc 0)
                                            v
                                            (let* ((dd (- v acc)) (z (vref Z (if (< dd 0) (+ dd n) dd))))
                                              (if (< z 0) -1 (modulo (+ acc z) n))))))))))
                  (loop (+ i 1)
                        (+ s (* w (+ 1 (cond ((< acc 0) 0) ((even? acc) 1) (else -1)))))))))))))


(define (hyp-newton-a S m)
  (let loop ((k 1) (a (list 1)))
    (if (> k m)
        a
        (let* ((sum (let s ((i 1) (acc 0))
                      (if (> i k)
                          acc
                          (s (+ i 1) (+ acc (* (nth S (- i 1)) (nth a (- k i))))))))
               (ak (/ (- sum) k)))
          (if (not (integer? ak))
              'unknown
              (loop (+ k 1) (append a (list ak))))))))

(define (hyp-jacobian-from-Ns Ns p g)
  (if (not (= (length Ns) (* 2 g)))
      'unknown
      (let* ((m (* 2 g))
             (S (map (lambda (k) (- (+ (^ p k) 1) (nth Ns (- k 1))))
                     (map (lambda (i) (+ i 1)) (range m))))
             (a (hyp-newton-a S m)))
        (if (equal? a 'unknown)
            'unknown
            (let ((J (foldl + 0 a)))
              (if (and (integer? J)
                       (every? (lambda (i)
                                 (= (nth a (- m i)) (* (^ p (- g i)) (nth a i))))
                               (range (+ g 1)))
                       (every? (lambda (k)
                                 (<= (* (nth S (- k 1)) (nth S (- k 1)))
                                     (* 4 g g (^ p k))))
                               (map (lambda (i) (+ i 1)) (range m))))
                  J
                  'unknown))))))

; коэффициенты L-многочлена L_p(T) = 1 + a1 T + … + p^g T^{2g} (по возрастанию) по N_1..N_g; 'unknown при несогласии
(define (hyp-L-coeffs P x p)
  (let* ((n (try (degree P x) (lambda (e) 0)))
         (g (if (even? n) (- (quotient n 2) 1) (quotient (- n 1) 2))))
    (if (< g 1)
        'unknown
        (let* ((ks (map (lambda (i) (+ i 1)) (range g)))
               (Ns (map (lambda (k) (hyp-count-points-k P x p k)) ks)))
          (if (member? 'unknown Ns)
              'unknown
              (let* ((S (map (lambda (k) (- (+ (^ p k) 1) (nth Ns (- k 1)))) ks))
                     (a (hyp-newton-a S g)))
                (if (equal? a 'unknown)
                    'unknown
                    (let* ((tail (map (lambda (j) (* (^ p j) (nth a (- g j))))
                                      (map (lambda (i) (+ i 1)) (range g))))
                           (full (append a tail)))
                      (if (and (every? integer? full)
                               (every? (lambda (k)
                                         (<= (* (nth S (- k 1)) (nth S (- k 1)))
                                             (* 4 g g (^ p k))))
                                       ks))
                          full
                          'unknown)))))))))

(define (hyp-jacobian-order-general P x p)
  (let ((full (hyp-L-coeffs P x p)))
    (if (equal? full 'unknown) 'unknown (foldl + 0 full))))

; #J(𝔽_{p²}) = ∏(1 − αᵢ²) = L(1)·L(−1)
(define (hyp-jacobian-order-sq P x p)
  (let ((full (hyp-L-coeffs P x p)))
    (if (equal? full 'unknown)
        'unknown
        (* (foldl + 0 full)
           (foldl + 0 (map2 (lambda (c i) (if (even? i) c (- c))) full (range (length full))))))))

; R1b.3: строгая проверка по 2g значениям N_k (симметрия L и Хассе — Вейль)
(define (hyp-jacobian-order-strict P x p)
  (let* ((n (try (degree P x) (lambda (e) 0)))
         (g (if (even? n) (- (quotient n 2) 1) (quotient (- n 1) 2))))
    (if (< g 1)
        'unknown
        (let* ((ks (map (lambda (i) (+ i 1)) (range (* 2 g))))
               (Ns (map (lambda (k) (hyp-count-points-k P x p k)) ks)))
          (if (member? 'unknown Ns)
              'unknown
              (hyp-jacobian-from-Ns Ns p g))))))

; публичный выбор: 2g-проверка при p^{2g} ≤ 2000, иначе быстрый хвост R1.4
(define (hyp-jacobian-pick P x p)
  (let* ((n (try (degree P x) (lambda (e) 0)))
         (g (if (even? n) (- (quotient n 2) 1) (quotient (- n 1) 2))))
    (if (and (>= g 3) (<= (^ p (* 2 g)) 2000))
        (hyp-jacobian-order-strict P x p)
        (hyp-jacobian-order P x p))))

(define (hyp-torsion-bound-general P x)
  (let loop ((p 3) (found '()))
    (cond ((>= (length found) 2) (gcd (car found) (cadr found)))
          ((> p 20) 'unknown)
          (else
           (let ((gp (hyp-good-prime? P x p)))
             (if (equal? gp #t)
                 (let ((j (hyp-jacobian-order-general P x p)))
                   (if (equal? j 'unknown)
                       'unknown
                       (loop (next-prime p) (cons j found))))
                 (loop (next-prime p) found)))))))
