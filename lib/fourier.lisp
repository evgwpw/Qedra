; Шаг FS: ряды Фурье (тригонометрические) на отрезке [a, b], период L = b − a, ω = 2π/L.
; f(x) ~ a0/2 + Σ_{n≥1} (an cos(nωx) + bn sin(nωx)); a0 = (2/L)∫f, an = (2/L)∫f cos(nωx), bn = (2/L)∫f sin(nωx).
; Коэффициенты считаются символьно по n: n объявляется целым положительным (временно, на время вычисления),
; поэтому sin(nπ) = 0, cos(nπ) = (−1)^n; множители (−1)^(±n + k) приводятся к (−1)^n или к числу.
; Кусочная f (piecewise) и |линейное| режутся по точкам излома: интеграл — по кускам, ветвь на куске выбирается
; в его середине. Невычисленное (интеграл не берётся, особенность, параметр в условии ветви) — `unknown`, не числа.
; Это ряд Фурье f, а не её значение: сходимость (Дирихле) — для кусочно гладкой f; значение в разрыве — полусумма
; пределов (fourier-value-at).
(module fourier
  (export fourier-coefficients fourier-series fourier-sine-series fourier-cosine-series
          fourier-complex-coefficients fourier-value-at fourier-coefficients-check parseval-check))

; ---------- служебное ----------

(define (fs-try thunk) (try (thunk) (lambda (e) #f)))
(define (fs-fail) (raise (list 'fs-fail)))
(define (fs-num e)
  (let ((v (fs-try (lambda () (eval-num e)))))
    (if (number? v) v #f)))
(define (fs-abs v) (if (< v 0) (- 0 v) v))
(define (fs-even? k) (= (modulo k 2) 0))
(define (fs-item x v) (if (equal? v x) #f v))

; ---------- точки излома и куски ----------

; корень линейного по x выражения u = c·x + d: −d/c или #f
(define (fs-lin-root u x)
  (let ((c (fs-try (lambda () (simplify (diff x u))))))
    (if (and c (not (equal? c 0)) (not (contains-sym? c x)) (fs-num c))
        (simplify (/ (- 0 (simplify (subst (list x 0) u))) c))
        #f)))

(define (fs-cond-roots c x)
  (cond ((not (pair? c)) '())
        ((member? (car c) '(< > <= >= = /=))
         (let ((r (fs-lin-root (list '- (cadr c) (caddr c)) x))) (if r (list r) '())))
        ((member? (car c) '(and or not)) (append-map (lambda (a) (fs-cond-roots a x)) (cdr c)))
        (else '())))

(define (fs-collect f x)
  (cond ((not (pair? f)) '())
        ((equal? (car f) 'piecewise)
         (append-map (lambda (br) (append (fs-cond-roots (car br) x) (fs-collect (cadr br) x))) (cadr f)))
        ((equal? (car f) 'abs)
         (let ((r (fs-lin-root (cadr f) x)))
           (append (if r (list r) '()) (fs-collect (cadr f) x))))
        (else (append-map (lambda (a) (fs-collect a x)) (cdr f)))))

(define (fs-uniq l)
  (let loop ((l (sort l (lambda (p q) (< (fs-num p) (fs-num q))))) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? acc) (< (fs-abs (- (fs-num (car l)) (fs-num (car acc)))) 1e-12)) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

(define (fs-holds? c x mid)
  (cond ((equal? c #t) #t)
        ((equal? c 'else) #t)
        ((not (pair? c)) (fs-fail))
        ((equal? (car c) 'and) (every? (lambda (a) (fs-holds? a x mid)) (cdr c)))
        ((equal? (car c) 'or) (any? (lambda (a) (fs-holds? a x mid)) (cdr c)))
        ((equal? (car c) 'not) (not (fs-holds? (cadr c) x mid)))
        (else
         (let ((v (fs-num (subst (list x mid) (list '- (cadr c) (caddr c)))))
               (h (car c)))
           (cond ((not v) (fs-fail))
                 ((equal? h '<) (< v 0))
                 ((equal? h '>) (> v 0))
                 ((equal? h '<=) (<= v 0))
                 ((equal? h '>=) (>= v 0))
                 ((equal? h '=) (= v 0))
                 ((equal? h '/=) (not (= v 0)))
                 (else (fs-fail)))))))

; выражение на куске с серединой mid: piecewise → ветвь, abs → ±аргумент
(define (fs-resolve f x mid)
  (cond ((not (pair? f)) f)
        ((equal? (car f) 'piecewise)
         (let loop ((brs (cadr f)))
           (cond ((null? brs) (fs-fail))
                 ((fs-holds? (car (car brs)) x mid) (fs-resolve (cadr (car brs)) x mid))
                 (else (loop (cdr brs))))))
        ((equal? (car f) 'abs)
         (let* ((u (fs-resolve (cadr f) x mid))
                (v (fs-num (subst (list x mid) u))))
           (cond ((not v) (fs-fail))
                 ((< v 0) (simplify (list '* -1 u)))
                 ((> v 0) u)
                 (else (fs-fail)))))
        (else (cons (car f) (map (lambda (a) (fs-resolve a x mid)) (cdr f))))))

; куски: список (lo hi g); #f — не разобрали
(define (fs-pieces f x a b)
  (let ((na (fs-num a)) (nb (fs-num b)))
    (if (not (and na nb (< na nb)))
        #f
        (fs-try
          (lambda ()
            (let* ((rs (filter (lambda (r) (let ((v (fs-num r))) (and v (< na v) (< v nb)))) (fs-collect f x)))
                   (bounds (append (list a) (fs-uniq rs) (list b))))
              (let loop ((bs bounds) (acc '()))
                (if (null? (cdr bs))
                    (reverse acc)
                    (let* ((lo (car bs)) (hi (cadr bs))
                           (mid (/ (+ (fs-num lo) (fs-num hi)) 2))
                           (g (simplify (fs-resolve f x mid))))
                      (loop (cdr bs) (cons (list lo hi g) acc)))))))))))

; знаменатели (основания отрицательных степеней) выражения
(define (fs-denoms e)
  (cond ((not (pair? e)) '())
        ((and (equal? (car e) '^) (pair? (cddr e)) (number? (caddr e)) (< (caddr e) 0))
         (cons (cadr e) (fs-denoms (cadr e))))
        (else (append-map fs-denoms (cdr e)))))

; деление на нуль в готовом ответе: (^ 0 отрицательное)
(define (fs-div0? e)
  (cond ((not (pair? e)) #f)
        ((and (equal? (car e) '^) (equal? (cadr e) 0) (pair? (cddr e)) (number? (caddr e)) (< (caddr e) 0)) #t)
        (else (any? fs-div0? (cdr e)))))

; знаменатель обращается в нуль (или меняет знак) на [lo, hi] — особенность: интеграл не берём (сетка 120 точек)
(define (fs-pole? g x lo hi)
  (let ((nlo (fs-num lo)) (nhi (fs-num hi)))
    (any? (lambda (b)
            (let loop ((i 0) (prev #f))
              (if (> i 120)
                  #f
                  (let ((v (fs-num (subst (list x (+ nlo (* (/ i 120) (- nhi nlo)))) b))))
                    (cond ((not v) (loop (+ i 1) prev))
                          ((< (fs-abs v) 1e-9) #t)
                          ((and prev (< (* prev v) 0)) #t)
                          (else (loop (+ i 1) v)))))))
          (fs-denoms g))))

; ∫ h(g) по кускам; #f, если какой-то интеграл не вычислился или есть особенность
(define (fs-integrate-pieces pieces x h)
  (let loop ((ps pieces) (acc '()))
    (if (null? ps)
        (simplify (cons '+ acc))
        (let* ((p (car ps))
               (v (if (fs-pole? (nth p 2) x (nth p 0) (nth p 1))
                      #f
                      (fs-try (lambda () (integrate (h (nth p 2)) x (nth p 0) (nth p 1)))))))
          (if (or (not v) (contains-sym? v 'integrate) (contains-sym? v 'unknown) (contains-sym? v 'limit)
                  (fs-div0? v))
              #f
              (loop (cdr ps) (cons v acc)))))))

; ---------- приведение (−1)^(линейное по n) ----------

(define (fs-m1-pow u n)
  (let* ((e (fs-try (lambda () (expand (simplify u)))))
         (c (and e (fs-try (lambda () (simplify (diff n e)))))))
    (if (and c (integer? c))
        (let ((d (simplify (subst (list n 0) e))))
          (if (integer? d)
              (simplify (list '* (if (fs-even? d) 1 -1) (if (fs-even? c) 1 (list '^ -1 n))))
              (list '^ -1 u)))
        (list '^ -1 u))))

; sin/cos (π (c n + d)) при целом c и числе d: (−1)^(c n) · sin/cos(d π)
(define (fs-trig-int e n)
  (let* ((r (fs-try (lambda () (expand (simplify (/ (cadr e) 'pi))))))
         (c (and r (fs-try (lambda () (simplify (diff n r))))))
         (d (and c (integer? c) (fs-try (lambda () (simplify (subst (list n 0) r)))))))
    (if (and d (number? d) (not (equal? (type-of d) 'float)))
        (simplify (list '* (if (fs-even? c) 1 (list '^ -1 n)) (list (car e) (simplify (list '* d 'pi)))))
        e)))

(define (fs-m1 e n)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) '^) (equal? (cadr e) -1) (pair? (cddr e)))
         (fs-m1-pow (fs-m1 (caddr e) n) n))
        ((and (member? (car e) '(sin cos)) (pair? (cdr e)))
         (fs-trig-int (list (car e) (fs-m1 (cadr e) n)) n))
        (else (cons (car e) (map (lambda (a) (fs-m1 a n)) (cdr e))))))

; ---------- особые целые n (знаменатели, обращающиеся в 0): общая формула в них неверна ----------

(define (fs-sing-base b n)
  (let ((c (fs-try (lambda () (simplify (diff n b))))))
    (if (and c (number? c) (not (equal? c 0)))
        (let ((r (simplify (/ (- 0 (simplify (subst (list n 0) b))) c))))
          (if (and (integer? r) (>= r 1)) (list r) '()))
        (filter (lambda (k) (equal? (fs-try (lambda () (simplify (subst (list n k) b)))) 0))
                (map (lambda (i) (+ i 1)) (range 20))))))

(define (fs-singulars e n)
  (let loop ((bs (append-map (lambda (d) (fs-sing-base d n)) (fs-denoms e))) (acc '()))
    (cond ((null? bs) (sort acc <))
          ((member? (car bs) acc) (loop (cdr bs) acc))
          (else (loop (cdr bs) (cons (car bs) acc))))))

; значение коэффициента (возможно piecewise по n) при n = k
(define (fs-coef-at c n k)
  (if (and (pair? c) (equal? (car c) 'piecewise))
      (let loop ((brs (cadr c)))
        (cond ((null? brs) 'unknown)
              ((fs-holds? (car (car brs)) n k) (simplify (subst (list n k) (cadr (car brs)))))
              (else (loop (cdr brs)))))
      (simplify (subst (list n k) c))))

(define (fs-pw? c) (and (pair? c) (equal? (car c) 'piecewise)))

; применить h к телам ветвей (или к самому значению)
(define (fs-pw-map h c)
  (if (fs-pw? c)
      (list 'piecewise (map (lambda (br) (list (car br) (h (cadr br)))) (cadr c)))
      (h c)))

(define (fs-norm e n)
  (simplify (fs-m1 (simplify (fs-m1 (simplify e) n)) n)))

; ---------- коэффициенты ----------

(define (fs-omega a b) (simplify (/ (* 2 'pi) (simplify (- b a)))))

; (a0 an bn) для ядра cos/sin(n w x) и множителя 2/(b − a); n — символ 'n; #f — не вычислили
(define (fs-coefs f x a b w)
  (let ((n 'n))
    (if (contains-sym? f n)
        (error "fourier: имя n занято индексом ряда, переименуйте параметр n в f")
        (let ((pieces (fs-pieces f x a b)))
          (if (not pieces)
              #f
              (let* ((k (simplify (/ 2 (simplify (- b a)))))
                     (arg (simplify (list '* n w x)))
                     (i0 (fs-integrate-pieces pieces x (lambda (g) g))))
                (if (not i0)
                    #f
                    (assuming-call (list (list 'n integers positive))
                      (lambda ()
                        (let ((ic (fs-integrate-pieces pieces x (lambda (g) (list '* g (list 'cos arg)))))
                              (is (fs-integrate-pieces pieces x (lambda (g) (list '* g (list 'sin arg))))))
                          (if (not (and ic is))
                              #f
                              (let* ((sing (fs-singulars (list '+ ic is) n))
                                     (an (fs-norm (list '* k ic) n))
                                     (bn (fs-norm (list '* k is) n))
                                     (sp (map (lambda (m) (fs-special pieces x k w m)) sing)))
                                (if (any? (lambda (s) (not s)) sp)
                                    #f
                                    (list (fs-norm (list '* k i0) n)
                                          (fs-wrap n sing (map car sp) an)
                                          (fs-wrap n sing (map cadr sp) bn)))))))))))))))

; коэффициенты при конкретном целом n = m (там, где общая формула имеет нулевой знаменатель)
(define (fs-special pieces x k w m)
  (let* ((arg (simplify (list '* m w x)))
         (ic (fs-integrate-pieces pieces x (lambda (g) (list '* g (list 'cos arg)))))
         (is (fs-integrate-pieces pieces x (lambda (g) (list '* g (list 'sin arg))))))
    (if (and ic is)
        (list (simplify (list '* k ic)) (simplify (list '* k is)))
        #f)))

; (piecewise (((= n m1) v1) … (#t общая)))
(define (fs-wrap n sing vals generic)
  (let ((brs (filter (lambda (b) b)
                     (map2 (lambda (m v) (if (equal? v generic) #f (list (list '= n m) v))) sing vals))))
    (if (null? brs)
        generic
        (list 'piecewise (append brs (list (list #t generic)))))))

(define (fs-full f x a b) (fs-coefs f x a b (fs-omega a b)))
(define (fs-half f x l) (fs-coefs f x 0 l (simplify (/ 'pi l))))

; (fourier-coefficients f x a b) → (a0 an bn); an, bn — выражения по n (n ≥ 1); unknown — не вычислено
(define (fourier-coefficients f x a b)
  (let ((r (fs-full f x a b))) (if r r 'unknown)))

; член ряда по n и частичная/общая сумма
(define (fs-build a0 an bn w x n N)
  (let* ((arg (simplify (list '* n w x)))
         (half (if a0 (simplify (list '* 1/2 a0)) 0)))
    (if (not N)
        (let ((ts (filter (lambda (t) t)
                          (list (and an (fs-item 0 an) (list '* an (list 'cos arg)))
                                (and bn (fs-item 0 bn) (list '* bn (list 'sin arg)))))))
          (if (null? ts)
              half
              (let ((s (list 'sum (simplify (cons '+ ts)) n 1 'inf)))
                (if (equal? half 0) s (list '+ half s)))))
        (let loop ((k 1) (acc (if (equal? half 0) '() (list half))))
          (if (> k N)
              (simplify (cons '+ acc))
              (let* ((ak (and an (fs-coef-at an n k)))
                     (bk (and bn (fs-coef-at bn n k)))
                     (argk (simplify (list '* k w x)))
                     (t1 (if (and ak (not (equal? ak 0))) (list (list '* ak (list 'cos argk))) '()))
                     (t2 (if (and bk (not (equal? bk 0))) (list (list '* bk (list 'sin argk))) '())))
                (loop (+ k 1) (append t2 t1 acc))))))))

; (fourier-series f x a b [N]) — без N: общий вид a0/2 + (sum … n 1 inf); с N — частичная сумма
(define (fourier-series f x a b &rest opts)
  (let ((c (fs-full f x a b)))
    (if (not c)
        'unknown
        (fs-build (car c) (cadr c) (caddr c) (fs-omega a b) x 'n (if (null? opts) #f (car opts))))))

; синус-ряд на [0, L]: нечётное продолжение, bn = (2/L)∫ f sin(nπx/L)
(define (fourier-sine-series f x l &rest opts)
  (let ((c (fs-half f x l)))
    (if (not c)
        'unknown
        (fs-build #f #f (caddr c) (simplify (/ 'pi l)) x 'n (if (null? opts) #f (car opts))))))

; косинус-ряд на [0, L]: чётное продолжение
(define (fourier-cosine-series f x l &rest opts)
  (let ((c (fs-half f x l)))
    (if (not c)
        'unknown
        (fs-build (car c) (cadr c) #f (simplify (/ 'pi l)) x 'n (if (null? opts) #f (car opts))))))

; (c0 cn c-n): f ~ Σ c_k e^{i k ω x}; c0 = a0/2, cn = (an − i bn)/2, c_{−n} = (an + i bn)/2, n ≥ 1
(define (fourier-complex-coefficients f x a b)
  (let ((c (fs-full f x a b)))
    (if (not c)
        'unknown
        (let ((an (cadr c)) (bn (caddr c)))
          (list (simplify (list '* 1/2 (car c)))
                (fs-pw-zip (lambda (p q) (simplify (list '* 1/2 (list '+ p (list '* -1 '%i q))))) an bn)
                (fs-pw-zip (lambda (p q) (simplify (list '* 1/2 (list '+ p (list '* '%i q))))) an bn))))))

(define (fs-pw-zip h p q)
  (if (fs-pw? p)
      (list 'piecewise (map2 (lambda (b1 b2) (list (car b1) (h (cadr b1) (cadr b2)))) (cadr p) (cadr q)))
      (h p q)))

; ---------- значение ряда (Дирихле) ----------

(define (fs-at g x pt)
  (let ((v (fs-try (lambda () (simplify (subst (list x pt) g))))))
    (if (or (not v) (contains-sym? v 'unknown) (fs-div0? v)) #f v)))

; (fourier-value-at f x a b x0): значение суммы ряда в x0 — f(x0) в точке непрерывности, иначе
; (f(x0−) + f(x0+))/2 с периодическим продолжением (концы a, b — по пределам изнутри отрезка)
(define (fourier-value-at f x a b x0)
  (let ((pieces (fs-pieces f x a b)))
    (if (or (not pieces) (any? (lambda (p) (fs-pole? (nth p 2) x (nth p 0) (nth p 1))) pieces))
        'unknown
        (let* ((len (simplify (- b a)))
               (q (fs-num (simplify (/ (- x0 a) len)))))
          (if (not q)
              'unknown
              (let* ((k (floor (+ q 1e-9)))
                     (xr (simplify (- x0 (* k len))))
                     (nx (fs-num xr))
                     (cnt (length pieces))
                     (idx (let loop ((i 0))
                            (cond ((>= i cnt) #f)
                                  ((< (fs-abs (- nx (fs-num (car (nth pieces i))))) 1e-9) (list 'edge i))
                                  ((< (fs-num (car (nth pieces i))) nx)
                                   (if (< nx (fs-num (cadr (nth pieces i)))) (list 'in i) (loop (+ i 1))))
                                  (else #f)))))
                (cond ((not nx) 'unknown)
                      ((not idx)
                       (if (< (fs-abs (- nx (fs-num b))) 1e-9)
                           (fs-edge pieces x 0 cnt)
                           'unknown))
                      ((equal? (car idx) 'in) (or (fs-at (nth (nth pieces (cadr idx)) 2) x xr) 'unknown))
                      (else (fs-edge pieces x (cadr idx) cnt)))))))))

; граница в начале куска i: слева — предел предыдущего куска (по кругу), справа — предел куска i
(define (fs-edge pieces x i cnt)
  (let* ((right (nth pieces i))
         (left (nth pieces (if (= i 0) (- cnt 1) (- i 1))))
         (lv (fs-at (nth left 2) x (nth left 1)))
         (rv (fs-at (nth right 2) x (nth right 0))))
    (if (and lv rv) (simplify (list '* 1/2 (list '+ lv rv))) 'unknown)))

; ---------- численная проверка коэффициентов ----------

; ∫ g по [lo, hi] составной Симпсон, M — чётное число отрезков; #f — не получилось
(define (fs-simpson g x lo hi M)
  (let ((nlo (fs-num lo)) (nhi (fs-num hi)))
    (if (not (and nlo nhi))
        #f
        (let* ((h (/ (- nhi nlo) M)))
          (let loop ((i 0) (s 0.0))
            (if (> i M)
                (* s (/ h 3))
                (let* ((v (fs-num (subst (list x (+ nlo (* i h))) g)))
                       (w (cond ((or (= i 0) (= i M)) 1) ((fs-even? i) 2) (else 4))))
                  (if v (loop (+ i 1) (+ s (* w v))) #f))))))))

(define (fs-num-integral pieces x h)
  (let loop ((ps pieces) (acc 0.0))
    (if (null? ps)
        acc
        (let ((v (fs-simpson (h (nth (car ps) 2)) x (nth (car ps) 0) (nth (car ps) 1) 400)))
          (if v (loop (cdr ps) (+ acc v)) #f)))))

; (fourier-coefficients-check f x a b coefs) → numeric | #f | unknown: coefs = (a0 an bn) сравниваются
; с численной квадратурой (Симпсон на кусках) при n = 0 (a0), 1, 2, 3 (an, bn); допуск 1e-6
(define (fourier-coefficients-check f x a b coefs)
  (let ((pieces (fs-pieces f x a b)))
    (if (or (not pieces) (not (and (list? coefs) (= (length coefs) 3))))
        'unknown
        (let* ((len (fs-num (simplify (- b a))))
               (w (fs-omega a b))
               (res (fs-try
                      (lambda ()
                        (map (lambda (k)
                               (let* ((arg (simplify (list '* k w x)))
                                      (ik (fs-num-integral pieces x (lambda (g) (if (= k 0) g (list '* g (list 'cos arg))))))
                                      (is (if (= k 0) 0.0 (fs-num-integral pieces x (lambda (g) (list '* g (list 'sin arg))))))
                                      (ea (fs-num (if (= k 0) (car coefs) (fs-coef-at (cadr coefs) 'n k))))
                                      (eb (if (= k 0) 0.0 (fs-num (fs-coef-at (caddr coefs) 'n k)))))
                                 (if (and ik is ea eb)
                                     (and (< (fs-abs (- (* (/ 2 len) ik) ea)) 1e-6)
                                          (< (fs-abs (- (* (/ 2 len) is) eb)) 1e-6))
                                     (fs-fail))))
                             (list 0 1 2 3))))))
          (cond ((not res) 'unknown)
                ((every? (lambda (r) (equal? r #t)) res) 'numeric)
                (else #f))))))

; ---------- Парсеваль ----------

(define (fs-fact k) (if (<= k 1) 1 (* k (fs-fact (- k 1)))))

; ζ(p), p чётное ≥ 2: (−1)^(p/2+1) B_p (2π)^p / (2 p!)
(define (fs-zeta p)
  (simplify (list '* (if (fs-even? (/ p 2)) -1 1) (bernoulli p) (list '^ (list '* 2 'pi) p) (/ 1 (* 2 (fs-fact p))))))

; член разложенной суммы: (c p alt) — c·n^(−p)·(−1)^(alt·n); #f — не такой вид
(define (fs-split-term t n)
  (let loop ((fs (if (and (pair? t) (equal? (car t) '*)) (cdr t) (list t))) (c '()) (p 0) (alt #f))
    (if (null? fs)
        (list (simplify (cons '* c)) p alt)
        (let ((f (car fs)))
          (cond ((not (contains-sym? f n)) (loop (cdr fs) (cons f c) p alt))
                ((and (pair? f) (equal? (car f) '^) (equal? (cadr f) n) (integer? (caddr f)) (< (caddr f) 0))
                 (loop (cdr fs) c (- p (caddr f)) alt))
                ((and (pair? f) (equal? (car f) '^) (equal? (cadr f) -1) (equal? (caddr f) n))
                 (if alt #f (loop (cdr fs) c p #t)))
                (else #f))))))

; Σ_{n≥1} T(n) точно для T = Σ c·n^(−p)·(−1)^(alt n), p чётное ≥ 2; иначе #f
(define (fs-sum-known T n)
  (let* ((e (fs-try (lambda () (expand (fs-norm (expand (fs-norm T n)) n)))))
         (terms (and e (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e)))))
    (if (not terms)
        #f
        (let loop ((ts terms) (acc '()))
          (if (null? ts)
              (simplify (cons '+ acc))
              (let ((s (fs-split-term (car ts) n)))
                (if (or (not s) (< (cadr s) 2) (not (fs-even? (cadr s))))
                    #f
                    (let* ((p (cadr s))
                           (z (fs-zeta p))
                           (v (if (caddr s) (list '* -1 (- 1 (^ 2 (- 1 p))) z) z)))
                      (loop (cdr ts) (cons (list '* (car s) v) acc))))))))))

; частичные суммы Σ T(k) до M1 и M2: (S1 S2 T1 T2) или #f
(define (fs-tk an bn n k)
  (let ((ak (fs-num (fs-coef-at an n k))) (bk (fs-num (fs-coef-at bn n k))))
    (if (and ak bk) (+ (* ak ak) (* bk bk)) #f)))

(define (fs-partial an bn n M1 M2)
  (let loop ((k 1) (s 0.0) (s1 #f) (t1 #f))
    (if (> k M2)
        (list s1 s t1 (fs-tk an bn n M2))
        (let ((v (fs-tk an bn n k)))
          (if (not v)
              #f
              (let ((s2 (+ s v)))
                (loop (+ k 1) s2 (if (= k M1) s2 s1) (if (= k M1) v t1))))))))

; (parseval-check f x a b [coefs]) → (вердикт lhs rhs): lhs = (1/L)∫f², rhs = a0²/4 + ½Σ(an² + bn²);
; coefs = (a0 an bn) — проверяемые (подставные) коэффициенты, по умолчанию свои.
; exact — точная равенство (ряд суммируется через ζ(2k)); numeric — совпало численно (частичные суммы с оценкой хвоста
; или с допуском 1e-9); mismatch — не совпало; unknown — интеграл или сумма не вычислены
(define (parseval-check f x a b &rest opts)
  (let* ((n 'n)
         (pieces (fs-pieces f x a b))
         (cs (if (null? opts) (fs-full f x a b) (car opts))))
    (if (not (and pieces cs))
        (list 'unknown 'unknown 'unknown)
        (let* ((len (simplify (- b a)))
               (i2 (fs-integrate-pieces pieces x (lambda (g) (list '^ g 2))))
               (lhs (and i2 (fs-norm (list '/ i2 len) n))))
          (if (not lhs)
              (list 'unknown 'unknown 'unknown)
              (let* ((a0 (car cs))
                     (T (list '+ (list '^ (cadr cs) 2) (list '^ (caddr cs) 2)))
                     (S (if (or (fs-pw? (cadr cs)) (fs-pw? (caddr cs))) #f (fs-sum-known T n))))
                (if S
                    (let* ((rhs (fs-norm (list '+ (list '* 1/4 (list '^ a0 2)) (list '* 1/2 S)) n))
                           (d (fs-norm (list '- lhs rhs) n))
                           (dv (fs-num d)))
                      (cond ((equal? d 0) (list 'exact lhs rhs))
                            ((not dv) (list 'unknown lhs rhs))
                            ((< (fs-abs dv) 1e-9) (list 'numeric lhs rhs))
                            (else (list 'mismatch lhs rhs))))
                    (let ((p (fs-partial (cadr cs) (caddr cs) n 1000 2000))
                          (la (fs-num lhs))
                          (a0v (fs-num a0)))
                      (if (not (and p la a0v))
                          (list 'unknown lhs 'unknown)
                          (let* ((s2 (cadr p)) (ds (- s2 (car p)))
                                 (rhs (+ (* 1/4 a0v a0v) (* 1/2 s2))))
                            (cond ((or (< ds 0) (> ds (+ 1e-9 (* 0.1 (fs-abs s2)))) (> (fs-abs (nth p 3)) (+ 1e-12 (fs-abs (nth p 2)))))
                                   (list 'unknown lhs 'unknown))
                                  ((<= (fs-abs (- la rhs)) (+ 1e-9 ds)) (list 'numeric lhs rhs))
                                  (else (list 'mismatch lhs rhs)))))))))))))
