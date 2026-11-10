; Шаг TEN: метрика и кривизна — риманова и псевдориманова геометрия в координатах.
; Метрика g_{ab} — симметричная матрица (тензор ранга 2 или вложенный список), координаты — список символов.
; Соглашения (MTW / Wald; у сферы R > 0):
;   Γ^a_{bc} = ½ g^{ad} (∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc});  христоффель — тензор ранга 3, индексы (a b c), a — верхний.
;   R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb};  тензор ранга 4, индексы (a b c d), a — верхний.
;   R_{abcd} = g_{ae} R^e_{bcd};  Ricci R_{bd} = R^a_{bad};  R = g^{bd} R_{bd};  G_{ab} = R_{ab} − ½ R g_{ab}.
;   Ковариантная производная: индекс производной — ПОСЛЕДНИЙ у результата: (∇T)^{a…}_{b…; e} = (∇_e T)^{a…}_{b…}.
;   Вариантность тензора задаётся списком up/down по индексам (up — верхний, down — нижний); скаляр — пустой список.
; Индексы тензоров с 0 (tref), как в модуле tensor. Каждая компонента нормализуется (simplify + together + trigsimp),
; независимые компоненты считаются по симметриям (Γ по нижним, R^a_{bcd} по cd, R_{abcd} по ab, cd и парам, Ricci — симметричен).
(module curvature
  (export metric-inverse christoffel riemann riemann-lower ricci ricci-scalar einstein
          covariant-derivative kretschmann geodesic-equations curvature-check curvature-normalize))

; ---------- нормализация ----------

; нормальный вид компоненты: общий знаменатель, затем упрощение (sin² + cos² сворачивается в simplify/trigsimp)
(define (cv-norm0 e)
  (if (number? e) e (simplify (together (simplify e)))))
(define (cv-norm e)
  (let ((r (cv-norm0 e)))
    (if (or (number? r) (not (list? r))) r
        (let ((t2 (try (trigsimp r) (lambda (er) r))))
          (if (< (trigsimp-size t2) (trigsimp-size r)) (cv-norm0 t2) r)))))
(define (curvature-normalize e) (cv-norm e))
(define (cv-zero? e) (equal? (cv-norm e) 0))

(define (cv-sum terms)
  (let ((ts (filter (lambda (t) (not (equal? t 0))) terms)))
    (cond ((null? ts) 0)
          ((null? (cdr ts)) (car ts))
          (else (cons '+ ts)))))
(define (cv-mul a b)
  (if (or (equal? a 0) (equal? b 0)) 0 (list '* a b)))
(define (cv-neg e)
  (cond ((equal? e 0) 0) ((number? e) (- e)) (else (simplify (list '* -1 e)))))

; ---------- вход ----------

(define (cv-list x) (if (tensor? x) (tensor->list x) x))

(define (cv-check-input gl xs who)
  (let ((n (length xs)))
    (cond ((not (and (list? xs) (not (null? xs)) (every? symbol? xs)))
           (error (string-append who ": координаты — непустой список символов")))
          ((not (and (list? gl) (= (length gl) n) (every? (lambda (r) (and (list? r) (= (length r) n))) gl)))
           (error (string-append who ": метрика — квадратная матрица по числу координат")))
          (else #t))))

; метрика → вложенный список; симметрия проверяется
(define (cv-metric g xs who)
  (let ((gl (cv-list g)) (xs (cv-list xs)))
    (cv-check-input gl xs who)
    (let ((n (length xs)))
      (for-each (lambda (i)
                  (for-each (lambda (j)
                              (when (> j i)
                                (unless (cv-zero? (list '+ (nth (nth gl i) j) (cv-neg (nth (nth gl j) i))))
                                  (error (string-append who ": метрика не симметрична")))))
                            (range n)))
                (range n))
      (map (lambda (r) (map cv-norm r)) gl))))

(define (cv-at m i j) (nth (nth m i) j))
(define (cv-diag? m)
  (let ((n (length m)))
    (every? (lambda (i) (every? (lambda (j) (or (= i j) (equal? (cv-at m i j) 0))) (range n))) (range n))))

; обратная метрика (вложенный список)
(define (cv-inverse gl)
  (let ((n (length gl)))
    (if (cv-diag? gl)
        (map (lambda (i) (map (lambda (j) (if (= i j) (cv-norm (list '^ (cv-at gl i i) -1)) 0)) (range n))) (range n))
        (let ((iv (inv gl)))
          (map (lambda (r) (map cv-norm r)) (cv-list iv))))))

; ---------- Кристоффель ----------

; Γ_{d,bc} = ½ (∂_b g_dc + ∂_c g_db − ∂_d g_bc)
(define (cv-gamma-low gl xs d b c)
  (list '* 1/2 (cv-sum (list (diff (nth xs b) (cv-at gl d c))
                             (diff (nth xs c) (cv-at gl d b))
                             (cv-neg (diff (nth xs d) (cv-at gl b c)))))))

; вложенный список Γ[a][b][c] (a — верхний)
(define (cv-gamma gl gi xs)
  (let* ((n (length xs)) (h (make-hash)))
    (for-each
     (lambda (b)
       (for-each
        (lambda (c)
          (when (<= b c)
            (let ((low (map (lambda (d) (cv-gamma-low gl xs d b c)) (range n))))
              (for-each
               (lambda (a)
                 (hash-set! h (list a b c)
                            (cv-norm (cv-sum (map (lambda (d) (cv-mul (cv-at gi a d) (nth low d))) (range n))))))
               (range n)))))
        (range n)))
     (range n))
    (map (lambda (a)
           (map (lambda (b)
                  (map (lambda (c) (hash-ref h (if (<= b c) (list a b c) (list a c b)) 0)) (range n)))
                (range n)))
         (range n))))

(define (cv-g3 gm a b c) (nth (nth (nth gm a) b) c))

(define (cv-tensor-of l) (as-tensor l))

(define (metric-inverse g xs)
  (let ((gl (cv-metric g xs "metric-inverse")))
    (cv-tensor-of (cv-inverse gl))))

(define (christoffel g xs)
  (let* ((gl (cv-metric g xs "christoffel")) (xs (cv-list xs)))
    (cv-tensor-of (cv-gamma gl (cv-inverse gl) xs))))

; ---------- Риман ----------

; R^a_{bcd} (вложенный список), независимые — c < d
(define (cv-riemann-up gm xs)
  (let* ((n (length xs)) (h (make-hash)))
    (for-each
     (lambda (a)
       (for-each
        (lambda (b)
          (for-each
           (lambda (c)
             (for-each
              (lambda (d)
                (when (< c d)
                  (hash-set! h (list a b c d)
                             (cv-norm
                              (cv-sum
                               (append
                                (list (diff (nth xs c) (cv-g3 gm a d b))
                                      (cv-neg (diff (nth xs d) (cv-g3 gm a c b))))
                                (map (lambda (e) (cv-mul (cv-g3 gm a c e) (cv-g3 gm e d b))) (range n))
                                (map (lambda (e) (cv-neg (cv-mul (cv-g3 gm a d e) (cv-g3 gm e c b)))) (range n))))))))
              (range n)))
           (range n)))
        (range n)))
     (range n))
    (map (lambda (a)
           (map (lambda (b)
                  (map (lambda (c)
                         (map (lambda (d)
                                (cond ((= c d) 0)
                                      ((< c d) (hash-ref h (list a b c d) 0))
                                      (else (cv-neg (hash-ref h (list a b d c) 0)))))
                              (range n)))
                       (range n)))
                (range n)))
         (range n))))

(define (cv-g4 rm a b c d) (nth (nth (nth (nth rm a) b) c) d))

; R_{abcd}: считаются пары (a<b), (c<d), пара (ab) <= пара (cd)
(define (cv-riemann-low gl rup xs)
  (let* ((n (length xs)) (h (make-hash)))
    (define (low a b c d)
      (cv-norm (cv-sum (map (lambda (e) (cv-mul (cv-at gl a e) (cv-g4 rup e b c d))) (range n)))))
    (for-each
     (lambda (a)
       (for-each
        (lambda (b)
          (when (< a b)
            (for-each
             (lambda (c)
               (for-each
                (lambda (d)
                  (when (and (< c d) (<= (+ (* a n) b) (+ (* c n) d)))
                    (hash-set! h (list a b c d) (low a b c d))))
                (range n)))
             (range n))))
        (range n)))
     (range n))
    (define (get a b c d)
      (cond ((or (= a b) (= c d)) 0)
            ((> a b) (cv-neg (get b a c d)))
            ((> c d) (cv-neg (get a b d c)))
            ((> (+ (* a n) b) (+ (* c n) d)) (get c d a b))
            (else (hash-ref h (list a b c d) 0))))
    (map (lambda (a)
           (map (lambda (b)
                  (map (lambda (c) (map (lambda (d) (get a b c d)) (range n))) (range n)))
                (range n)))
         (range n))))

(define (riemann g xs)
  (let* ((gl (cv-metric g xs "riemann")) (xs (cv-list xs))
         (gm (cv-gamma gl (cv-inverse gl) xs)))
    (cv-tensor-of (cv-riemann-up gm xs))))

(define (riemann-lower g xs)
  (let* ((gl (cv-metric g xs "riemann-lower")) (xs (cv-list xs))
         (gm (cv-gamma gl (cv-inverse gl) xs))
         (rup (cv-riemann-up gm xs)))
    (cv-tensor-of (cv-riemann-low gl rup xs))))

; ---------- Риччи, скаляр, Эйнштейн ----------

(define (cv-ricci rup xs)
  (let* ((n (length xs)) (h (make-hash)))
    (for-each
     (lambda (b)
       (for-each
        (lambda (d)
          (when (<= b d)
            (hash-set! h (list b d)
                       (cv-norm (cv-sum (map (lambda (a) (cv-g4 rup a b a d)) (range n)))))))
        (range n)))
     (range n))
    (map (lambda (b)
           (map (lambda (d) (hash-ref h (if (<= b d) (list b d) (list d b)) 0)) (range n)))
         (range n))))

(define (cv-scalar gi ric xs)
  (let ((n (length xs)))
    (cv-norm (cv-sum (append-map (lambda (b)
                                   (map (lambda (d) (cv-mul (cv-at gi b d) (cv-at ric b d))) (range n)))
                                 (range n))))))

(define (cv-einstein gl ric rs xs)
  (let ((n (length xs)))
    (map (lambda (a)
           (map (lambda (b)
                  (cv-norm (cv-sum (list (cv-at ric a b) (cv-mul -1/2 (cv-mul rs (cv-at gl a b)))))))
                (range n)))
         (range n))))

; общий предвычислитель: метрика, обратная, Γ, R^a_{bcd}
(define (cv-prep g xs who)
  (let* ((gl (cv-metric g xs who)) (xs (cv-list xs)) (gi (cv-inverse gl))
         (gm (cv-gamma gl gi xs)) (rup (cv-riemann-up gm xs)))
    (list gl gi xs gm rup)))

(define (ricci g xs)
  (let ((p (cv-prep g xs "ricci")))
    (cv-tensor-of (cv-ricci (nth p 4) (nth p 2)))))

(define (ricci-scalar g xs)
  (let* ((p (cv-prep g xs "ricci-scalar")) (ric (cv-ricci (nth p 4) (nth p 2))))
    (cv-scalar (nth p 1) ric (nth p 2))))

(define (einstein g xs)
  (let* ((p (cv-prep g xs "einstein")) (ric (cv-ricci (nth p 4) (nth p 2)))
         (rs (cv-scalar (nth p 1) ric (nth p 2))))
    (cv-tensor-of (cv-einstein (nth p 0) ric rs (nth p 2)))))

; K = R_{abcd} R^{abcd} = R^{ab}_{cd} R^{cd}_{ab}, R^{ab}_{cd} = g^{bf} R^a_{fcd}
(define (kretschmann g xs)
  (let* ((p (cv-prep g xs "kretschmann")) (gi (nth p 1)) (xs (nth p 2)) (rup (nth p 4)) (n (length xs))
         (mix (map (lambda (a)
                     (map (lambda (b)
                            (map (lambda (c)
                                   (map (lambda (d)
                                          (cv-norm (cv-sum (map (lambda (f) (cv-mul (cv-at gi b f) (cv-g4 rup a f c d)))
                                                                (range n)))))
                                        (range n)))
                                 (range n)))
                          (range n)))
                   (range n))))
    (cv-norm (cv-sum (append-map (lambda (a)
                                   (append-map (lambda (b)
                                                 (append-map (lambda (c)
                                                               (map (lambda (d) (cv-mul (cv-g4 mix a b c d) (cv-g4 mix c d a b)))
                                                                    (range n)))
                                                             (range n)))
                                               (range n)))
                                 (range n))))))

; ---------- ковариантная производная ----------

(define (cv-replace l i v) (append (take l i) (cons v (drop l (+ i 1)))))

; (covariant-derivative T variance g coords): variance — список up/down по индексам T ('() у скаляра);
; результат — тензор ранга (ранг T + 1), производная — последний индекс
(define (covariant-derivative tt variance g xs)
  (let* ((gl (cv-metric g xs "covariant-derivative")) (xs (cv-list xs)) (n (length xs))
         (gm (cv-gamma gl (cv-inverse gl) xs))
         (variance (cv-list variance))
         (scalar? (null? variance))
         (tn (if scalar? #f (as-tensor tt)))
         (sh (if scalar? '() (tensor-shape-list tn))))
    (cond ((not (every? (lambda (v) (or (equal? v 'up) (equal? v 'down))) variance))
           (error "covariant-derivative: вариантность — список up/down"))
          ((not (= (length variance) (length sh)))
           (error "covariant-derivative: длина списка вариантности не равна рангу тензора"))
          ((not (every? (lambda (d) (= d n)) sh))
           (error "covariant-derivative: размерности тензора не равны числу координат")))
    (let ((get (lambda (idx) (if scalar? tt (apply tref (cons tn idx))))))
      (make-tensor (append sh (list n))
                   (lambda (idx)
                     (let* ((k (length sh)) (e (nth idx k)) (base (take idx k))
                            (terms
                             (append
                              (list (diff (nth xs e) (get base)))
                              (append-map
                               (lambda (p)
                                 (let ((ip (nth base p)))
                                   (map (lambda (s)
                                          (if (equal? (nth variance p) 'up)
                                              (cv-mul (cv-g3 gm ip e s) (get (cv-replace base p s)))
                                              (cv-neg (cv-mul (cv-g3 gm s e ip) (get (cv-replace base p s))))))
                                        (range n))))
                               (range k)))))
                       (cv-norm (cv-sum terms))))))))

; ---------- геодезические ----------

; (geodesic-equations g coords tau): список равенств d²x^a/dτ² = −Γ^a_{bc} ẋ^b ẋ^c; x^a — функции (x tau)
(define (geodesic-equations g xs tau)
  (let* ((gl (cv-metric g xs "geodesic-equations")) (xs (cv-list xs)) (n (length xs))
         (gm (cv-gamma gl (cv-inverse gl) xs))
         (fx (map (lambda (x) (list x tau)) xs))
         (rules (map2 (lambda (x f) (list x f)) xs fx))
         (vel (map (lambda (f) (list 'diff f tau)) fx)))
    (map (lambda (a)
           (let ((rhs (cv-sum (append-map (lambda (b)
                                            (map (lambda (c)
                                                   (cv-mul (cv-g3 gm a b c) (list '* (nth vel b) (nth vel c))))
                                                 (range n)))
                                          (range n)))))
             (list '= (list 'diff (list 'diff (nth fx a) tau) tau)
                   (simplify (list '* -1 (subst rules rhs))))))
         (range n))))

; ---------- сертификат ----------

; значения для численной проверки: i-й символ — 0.7 + 0.37 i (+ сдвиг), параметры — 1.3 + 0.41 i
(define (cv-sample-rules syms shift)
  (let loop ((l syms) (i 0) (acc '()))
    (if (null? l) acc
        (loop (cdr l) (+ i 1) (cons (list (car l) (+ 0.7 shift (* 0.37 i))) acc)))))

(define (cv-heads e acc)
  (cond ((not (list? e)) acc)
        ((null? e) acc)
        (else
         (let ((acc1 (if (and (symbol? (car e)) (not (fbound? (car e))) (not (member? (car e) acc))
                              (not (member? (car e) '(+ * ^ diff))))
                         (cons (car e) acc) acc)))
           (foldl (lambda (a x) (cv-heads x a)) acc1 (cdr e))))))

; подстановка пробной функции вместо неизвестной f(arg)
(define (cv-test-fun e heads k)
  (foldl (lambda (acc h)
           (replace-fun acc h k))
         e heads))
(define (replace-fun e h k)
  (cond ((not (list? e)) e)
        ((null? e) e)
        ((and (equal? (car e) h) (= (length e) 2))
         (let ((u (replace-fun (cadr e) h k)))
           (list '+ 2 (list '* (/ k 3) u) (list '* 1/5 (list '^ u 2)))))
        (else (map (lambda (x) (replace-fun x h k)) e))))

; невычисленная запись производной (diff u v) → вычисленная (diff v u)
(define (cv-do-diffs e)
  (cond ((not (list? e)) e)
        ((null? e) e)
        ((and (equal? (car e) 'diff) (= (length e) 3) (symbol? (caddr e)))
         (diff (caddr e) (cv-do-diffs (cadr e))))
        (else (map cv-do-diffs e))))

(define (cv-numeric-nonzero? e shift)
  (let* ((heads (cv-heads e '()))
         (e1 (if (null? heads) e (cv-do-diffs (cv-test-fun e heads (+ 1 shift)))))
         (e2 (try (simplify e1) (lambda (er) e1)))
         (syms (const-free-syms e2))
         (v (try (eval-num (subst (cv-sample-rules syms shift) e2)) (lambda (er) 'none))))
    (cond ((equal? v 'none) 'unknown)
          ((not (number? v)) 'unknown)
          ((> (cv-abs v) 1e-9) 'nonzero)
          (else 'zero))))

(define (cv-abs v) (if (< v 0) (- v) v))

; вердикт по разности: verified (тождественно 0) | mismatch (численно ≠ 0 в пробной точке) | unknown
(define (cv-diff-verdict d)
  (let ((dn (cv-norm d)))
    (if (equal? dn 0) 'verified
        (let ((rs (map (lambda (s) (cv-numeric-nonzero? dn s)) '(0 0.21 0.53))))
          (if (member? 'nonzero rs) 'mismatch 'unknown)))))

(define (cv-flat-tensor x)
  (cond ((tensor? x) (vector->list (tensor-data x)))
        ((cv-level? x) (append-map cv-flat-tensor x))
        (else (list x))))
(define (cv-level? x)
  (and (list? x) (not (null? x))
       (not (and (symbol? (car x)) (or (fbound? (car x)) (member? (car x) '(+ * ^ - /)))))))

; (curvature-check g coords quantity claimed): quantity — christoffel, riemann, riemann-lower, ricci, ricci-scalar,
; einstein, kretschmann; claimed — скаляр или тензор/вложенный список той же формы
(define (curvature-check g xs what claimed)
  (let* ((p (cv-prep g xs "curvature-check")) (gl (nth p 0)) (gi (nth p 1)) (xs1 (nth p 2)) (gm (nth p 3)) (rup (nth p 4))
         (ric (cv-ricci rup xs1)) (rs (cv-scalar gi ric xs1))
         (actual (cond ((equal? what 'christoffel) gm)
                       ((equal? what 'riemann) rup)
                       ((equal? what 'riemann-lower) (cv-riemann-low gl rup xs1))
                       ((equal? what 'ricci) ric)
                       ((equal? what 'ricci-scalar) rs)
                       ((equal? what 'einstein) (cv-einstein gl ric rs xs1))
                       ((equal? what 'kretschmann) (kretschmann g xs))
                       (else (error "curvature-check: величина — christoffel, riemann, riemann-lower, ricci, ricci-scalar, einstein, kretschmann"))))
         (scalar? (or (equal? what 'ricci-scalar) (equal? what 'kretschmann)))
         (cl (if scalar? (list (cv-list claimed)) (cv-flat-tensor (cv-list claimed))))
         (al (if scalar? (list actual) (cv-flat-tensor actual))))
    (if (not (= (length cl) (length al)))
        'mismatch
        (let ((vs (map2 (lambda (c a) (cv-diff-verdict (list '+ c (cv-neg a)))) cl al)))
          (cond ((member? 'mismatch vs) 'mismatch)
                ((member? 'unknown vs) 'unknown)
                (else 'verified))))))
