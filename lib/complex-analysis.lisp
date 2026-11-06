; Шаг CA: ТФКП как инструменты — вычеты, ряды Лорана, тип особой точки, интеграл по окружности, ∫R(x)dx по ℝ через вычеты.
; Функция f — выражение от символа z из «мероморфного» словаря: + * - / ^ (целая степень), exp sin cos tan cot sec csc
; sinh cosh tanh coth, числа и символы. Всё остальное (sqrt, log, abs, ^ с нецелой степенью …) — `unknown`: ветвления не берём.
; Точка z0 — конечная (в том числе комплексная: %i, (+ 1 %i)) или `inf`. Разложение — через `series` после замены
; z = z0 + t (z = 1/t при z0 = inf); вычет на бесконечности: Res_∞ f = −Res_{t=0} f(1/t)/t².
; Существенная особенность (ряд не строится): f = Σ (мероморфный)·exp/sin/cos/sinh/cosh(A), где A имеет полюс в точке.
; Тип `essential` объявляется только при ровно одном существенном слагаемом (иначе — unknown: слагаемые могли сократиться).
; Коэффициенты существенного случая — точно, если мероморфный множитель и главная часть A — многочлены Лорана
; (иначе вычет — бесконечная сумма, `unknown`). Честность: невычисленное — `unknown`; сертификаты — численные (круг, трапеции).
(module complex-analysis
  (export residue laurent singularity-type singularities contour-integral
          residue-check contour-integral-check integral-by-residues branch-check
          integral-fourier integral-pv integral-keyhole integral-trig integral-residues-check definite-by-residues))

(define ca-t 'ca_t)
(define (ca-try thunk) (try (thunk) (lambda (e) #f)))
(define (ca-inf? p) (equal? p 'inf))

; ---------- словарь ----------

(define ca-fns '(exp sin cos tan cot sec csc sinh cosh tanh coth))
(define (ca-ok? e)
  (cond ((not (pair? e)) #t)
        ((member? (car e) '(+ * - /)) (every? ca-ok? (cdr e)))
        ((equal? (car e) '^) (and (= (length e) 3)
                                  (or (integer? (caddr e)) (ca-num-const? e))
                                  (ca-ok? (cadr e))))
        ((member? (car e) ca-fns) (and (= (length e) 2) (ca-ok? (cadr e))))
        (else #f)))

; числовая константа вида 2^(1/2): рациональные основание и показатель (алгебраические коэффициенты точек)
(define (ca-num-const? e) (and (number? (cadr e)) (number? (caddr e))))

(define (ca-rational? e)
  (cond ((not (pair? e)) #t)
        ((member? (car e) '(+ * - /)) (every? ca-rational? (cdr e)))
        ((equal? (car e) '^) (and (= (length e) 3)
                                  (or (integer? (caddr e)) (ca-num-const? e))
                                  (ca-rational? (cadr e))))
        (else #f)))

; ---------- комплексные числа с плавающей точкой: (re . im) ----------

(define ca-pi (eval-num 'pi))
(define (ca-cadd a b) (cons (+ (car a) (car b)) (+ (cdr a) (cdr b))))
(define (ca-csub a b) (cons (- (car a) (car b)) (- (cdr a) (cdr b))))
(define (ca-cmul a b)
  (cons (- (* (car a) (car b)) (* (cdr a) (cdr b))) (+ (* (car a) (cdr b)) (* (cdr a) (car b)))))
(define (ca-cinv a)
  (let ((d (+ (* (car a) (car a)) (* (cdr a) (cdr a)))))
    (if (< d 1e-300) (error "ca: деление на ноль") (cons (/ (car a) d) (/ (- 0.0 (cdr a)) d)))))
(define (ca-cdiv a b) (ca-cmul a (ca-cinv b)))
(define (ca-cabs a) (sqrt-float (+ (* (car a) (car a)) (* (cdr a) (cdr a)))))
(define (sqrt-float x) (eval-num (list '^ x 0.5)))
(define (ca-cexp a)
  (let ((m (exp (car a)))) (cons (* m (cos (cdr a))) (* m (sin (cdr a))))))
(define (ca-ci z) (cons (- 0.0 (cdr z)) (car z)))       ; i·z
(define (ca-cneg z) (cons (- 0.0 (car z)) (- 0.0 (cdr z))))
(define (ca-csin z)   ; (e^{iz} − e^{−iz}) / 2i
  (let ((p (ca-cexp (ca-ci z))) (m (ca-cexp (ca-cneg (ca-ci z)))))
    (ca-cdiv (ca-csub p m) (cons 0.0 2.0))))
(define (ca-ccos z)
  (let ((p (ca-cexp (ca-ci z))) (m (ca-cexp (ca-cneg (ca-ci z)))))
    (ca-cmul (ca-cadd p m) (cons 0.5 0.0))))
(define (ca-csinh z)
  (ca-cmul (ca-csub (ca-cexp z) (ca-cexp (ca-cneg z))) (cons 0.5 0.0)))
(define (ca-ccosh z)
  (ca-cmul (ca-cadd (ca-cexp z) (ca-cexp (ca-cneg z))) (cons 0.5 0.0)))
(define (ca-cpow a n)
  (cond ((< n 0) (ca-cinv (ca-cpow a (- 0 n))))
        ((= n 0) (cons 1.0 0.0))
        ((= (modulo n 2) 0) (let ((h (ca-cpow a (quotient n 2)))) (ca-cmul h h)))
        (else (ca-cmul a (ca-cpow a (- n 1))))))

; значение выражения в комплексной точке (zv — значение символа zs); ошибка при неизвестном символе
(define (ca-ceval e zs zv)
  (cond ((number? e) (cons (* 1.0 e) 0.0))
        ((equal? e '%i) (cons 0.0 1.0))
        ((equal? e 'pi) (cons ca-pi 0.0))
        ((and zs (equal? e zs)) zv)
        ((symbol? e) (error "ca: неизвестный символ" e))
        ((not (pair? e)) (cons (* 1.0 (eval-num e)) 0.0))
        (else
         (let* ((h (car e)) (args (map (lambda (a) (ca-ceval a zs zv)) (cdr e))) (a (car args)))
           (cond ((equal? h '+) (foldl ca-cadd (cons 0.0 0.0) args))
                 ((equal? h '*) (foldl ca-cmul (cons 1.0 0.0) args))
                 ((equal? h '-) (if (null? (cdr args)) (ca-cneg a) (ca-csub a (foldl ca-cadd (cons 0.0 0.0) (cdr args)))))
                 ((equal? h '/) (foldl (lambda (acc x) (ca-cdiv acc x)) a (cdr args)))
                 ((equal? h '^) (cond ((integer? (caddr e)) (ca-cpow a (caddr e)))
                                      ((and (number? (cadr e)) (number? (caddr e)))
                                       (cons (* 1.0 (eval-num e)) 0.0))
                                      (else (error "ca: нецелая степень"))))
                 ((equal? h 'exp) (ca-cexp a))
                 ((equal? h 'sin) (ca-csin a))
                 ((equal? h 'cos) (ca-ccos a))
                 ((equal? h 'tan) (ca-cdiv (ca-csin a) (ca-ccos a)))
                 ((equal? h 'cot) (ca-cdiv (ca-ccos a) (ca-csin a)))
                 ((equal? h 'sec) (ca-cinv (ca-ccos a)))
                 ((equal? h 'csc) (ca-cinv (ca-csin a)))
                 ((equal? h 'sinh) (ca-csinh a))
                 ((equal? h 'cosh) (ca-ccosh a))
                 ((equal? h 'tanh) (ca-cdiv (ca-csinh a) (ca-ccosh a)))
                 ((equal? h 'coth) (ca-cdiv (ca-ccosh a) (ca-csinh a)))
                 (else (error "ca: неизвестная функция" h)))))))

(define (ca-cnum e) (ca-try (lambda () (ca-ceval e #f #f))))

; ---------- нуль ли значение ----------

; #t | #f | unknown
(define (ca-zero3 v)
  (let ((s (ca-try (lambda () (simplify v)))))
    (cond ((not s) 'unknown)
          ((equal? s 0) #t)
          ((number? s) #f)
          (else
           (let ((c (ca-cnum s)))
             (cond ((not c) 'unknown)
                   ((> (ca-cabs c) 1e-9) #f)
                   (else 'unknown)))))))

; ---------- ряд в нуле по t ----------

; основания целых степеней раскрываем (константы вида 5 + 2z0 + z0² сворачиваются в 0 — иначе ряд «не видит» полюс)
(define (ca-nd e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) '^) (integer? (caddr e)) (pair? (cadr e)) (equal? (car (cadr e)) '+))
         (list '^ (simplify (expand (ca-nd (cadr e)))) (caddr e)))
        ((member? (car e) '(+ * - / ^ exp sin cos tan cot sec csc sinh cosh tanh coth))
         (simplify (cons (car e) (map ca-nd (cdr e)))))
        (else e)))

(define (ca-shift f z z0)
  (ca-nd (if (ca-inf? z0)
             (subst (list z (list '^ ca-t -1)) f)
             (subst (list z (list '+ z0 ca-t)) f))))

(define (ca-series g n) (ca-try (lambda () (series g ca-t 0 n))))

(define ca-maxpole 60)
; наименьший k < n с ненулевым коэффициентом; #f — все нули до n; unknown — нуль не распознан
(define (ca-lowest s n)
  (let loop ((k (- 0 ca-maxpole)))
    (if (>= k n)
        #f
        (let ((z (ca-zero3 (series-coeff s k))))
          (cond ((equal? z 'unknown) 'unknown)
                (z (loop (+ k 1)))
                (else k))))))

(define (ca-coef-mero g k)
  (let ((s (series g ca-t 0 (if (< k 0) 1 (+ k 1)))))
    (simplify (series-coeff s k))))

; ---------- разбор многочленов Лорана по t ----------

(define (ca-terms e) (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e)))
(define (ca-factors e) (if (and (pair? e) (equal? (car e) '*)) (cdr e) (list e)))

(define (ca-lp-term tm)
  (let loop ((l (ca-factors tm)) (k 0) (c 1))
    (cond ((null? l) (cons k c))
          ((equal? (car l) ca-t) (loop (cdr l) (+ k 1) c))
          ((and (pair? (car l)) (equal? (car (car l)) '^) (equal? (cadr (car l)) ca-t) (integer? (caddr (car l))))
           (loop (cdr l) (+ k (caddr (car l))) c))
          ((contains-sym? (car l) ca-t) #f)
          (else (loop (cdr l) k (simplify (list '* c (car l))))))))

(define (ca-lp-merge ts)
  (let loop ((l ts) (acc '()))
    (if (null? l)
        acc
        (let* ((k (car (car l))) (hit (assoc k acc)))
          (loop (cdr l)
                (if hit
                    (map (lambda (p) (if (equal? (car p) k) (cons k (simplify (list '+ (cdr p) (cdr (car l))))) p)) acc)
                    (cons (car l) acc)))))))

; ((k . c) …) — e = Σ c t^k; #f — не многочлен Лорана по t
(define (ca-lp-terms e)
  (let ((x (ca-try (lambda () (simplify (expand e))))))
    (and x
         (let loop ((l (ca-terms x)) (acc '()))
           (if (null? l)
               (ca-lp-merge acc)
               (let ((r (ca-lp-term (car l))))
                 (and r (loop (cdr l) (cons r acc)))))))))

; ---------- существенный случай ----------

; множители: exp(B) для exp, sin, cos, sinh, cosh от A: список (вес . множитель-при-A)
(define (ca-exps head)
  (cond ((equal? head 'exp) (list (cons 1 1)))
        ((equal? head 'sin) (list (cons '(* -1/2 %i) '%i) (cons '(* 1/2 %i) '(* -1 %i))))     ; (e^{iA} − e^{−iA}) / 2i = (−i/2) e^{iA} + (i/2) e^{−iA}
        ((equal? head 'cos) (list (cons (/ 1 2) '%i) (cons (/ 1 2) '(* -1 %i))))
        ((equal? head 'sinh) (list (cons (/ 1 2) 1) (cons (/ -1 2) -1)))
        ((equal? head 'cosh) (list (cons (/ 1 2) 1) (cons (/ 1 2) -1)))
        (else #f)))

; e_0 … e_Q — коэффициенты exp(p1 u + p2 u² + …) по u = 1/t: q e_q = Σ j p_j e_{q−j}
(define (ca-exp-coefs p q)
  (let loop ((i 1) (acc (list 1)))   ; acc — e_{i−1} … e_0 (в обратном порядке)
    (if (> i q)
        (reverse acc)
        (let ((s (let sl ((j 1) (sum 0))
                   (if (or (> j i) (> j (length p)))
                       sum
                       (sl (+ j 1) (simplify (list '+ sum (list '* j (nth p (- j 1)) (nth (reverse acc) (- i j)))))))))
              )
          (loop (+ i 1) (cons (simplify (list '/ s i)) acc))))))

; главная часть A: список p_1…p_K (коэффициенты при t^−j) и константа; #f — A не многочлен Лорана без положительных степеней
(define (ca-principal at mul)
  (let ((lp (ca-lp-terms (list '* mul at))))
    (and lp
         (every? (lambda (p) (<= (car p) 0)) lp)
         (let* ((kmax (foldl (lambda (m p) (max m (- 0 (car p)))) 0 lp))
                (get (lambda (k) (let ((h (assoc k lp))) (if h (cdr h) 0)))))
           (cons (map (lambda (j) (get (- 0 j))) (range-1 kmax)) (get 0))))))
(define (range-1 n) (if (< n 1) '() (map (lambda (i) (+ i 1)) (range n))))

; коэффициент при t^e у R · F(A): rt — термы R; ex — ((вес . mul) …); at — A
(define (ca-ess-coef-fn rt head at)
  (let ((ex (ca-exps head)))
    (and rt
         (let ((pr (map (lambda (w) (ca-principal at (cdr w))) ex)))
           (and (every? (lambda (x) x) pr)
                (lambda (e)
                  (let loop ((ws ex) (ps pr) (tot 0))
                    (if (null? ws)
                        (simplify tot)
                        (let* ((p (car (car ps))) (b0 (cdr (car ps)))
                               (qmax (foldl (lambda (m r) (max m (- (car r) e))) 0 rt))
                               (ec (ca-exp-coefs p qmax))
                               (s (foldl (lambda (acc r)
                                           (let ((q (- (car r) e)))
                                             (if (< q 0) acc (list '+ acc (list '* (cdr r) (nth ec q))))))
                                         0 rt)))
                          (loop (cdr ws) (cdr ps)
                                (list '+ tot (list '* (car (car ws)) (list 'exp b0) s))))))))))))

; класс множителя: (mero) | (ess head A) | #f
(define (ca-fclass f)
  (let ((s (ca-series f 3)))
    (cond (s (let ((v (ca-lowest s 3))) (if (number? v) (list 'mero) (if (equal? v #f) (list 'mero) #f))))
          ((and (pair? f) (member? (car f) '(exp sin cos sinh cosh)))
           (let* ((a (cadr f)) (sa (ca-series a 3)))
             (and sa
                  (let ((v (ca-lowest sa 3)))
                    (and (number? v) (< v 0) (list 'ess (car f) a))))))
          (else #f))))

; слагаемое: (mero) | (ess coef-fn) | #f
(define (ca-term-class tm)
  (let* ((fs (ca-factors tm)) (cl (map ca-fclass fs)))
    (if (any? (lambda (c) (not c)) cl)
        #f
        (let ((es (filter (lambda (p) (equal? (car (cdr p)) 'ess)) (map2 cons fs cl))))
          (cond ((null? es) (list 'mero))
                ((> (length es) 1) #f)
                (else
                 (let* ((ef (car es))
                        (rs (filter (lambda (f) (not (equal? f (car ef)))) fs))
                        (r (simplify (cons '* rs)))
                        (rt (ca-lp-terms r)))
                   (list 'ess (ca-ess-coef-fn rt (cadr (cdr ef)) (caddr (cdr ef)))))))))))

; (ess cert fn) — fn: k → коэффициент или #f; cert — тип доказан | unknown
(define (ca-ess-analyze g)
  (let* ((e (ca-try (lambda () (simplify g)))))
    (if (not e)
        'unknown
        (let* ((tms (ca-terms e)) (cls (map ca-term-class tms)))
          (if (any? (lambda (c) (not c)) cls)
              'unknown
              (let* ((pairs (map2 cons tms cls))
                     (ess (filter (lambda (p) (equal? (car (cdr p)) 'ess)) pairs))
                     (mero (map car (filter (lambda (p) (equal? (car (cdr p)) 'mero)) pairs)))
                     (m (if (null? mero) 0 (simplify (cons '+ mero)))))
                (if (null? ess)
                    'unknown
                    (let ((fns (map (lambda (p) (cadr (cdr p))) ess)))
                      (list 'ess (if (= (length ess) 1) 'cert 'unknown)
                            (and (every? (lambda (f) f) fns)
                                 (lambda (k)
                                   (simplify (list '+
                                                   (if (equal? m 0) 0 (ca-coef-mero m k))
                                                   (cons '+ (map (lambda (f) (f k)) fns)))))))))))))))

; ---------- анализ g(t) в нуле ----------

; (mero g v) — v: наименьший показатель (v ≥ 30 — «нули до 30»); (ess cert fn); unknown
(define (ca-analyze g)
  (if (not (ca-ok? g))
      'unknown
      (let ((s (ca-series g 1)))
        (if s
            (ca-mero-order g s 1)
            (ca-ess-analyze g)))))

; порядок усечения растёт 1 → 6 → 30, пока не найден ненулевой коэффициент ниже усечения
(define (ca-mero-order g s n)
  (let ((v (ca-lowest s n)))
    (cond ((equal? v 'unknown) 'unknown)
          (v (list 'mero g v))
          ((>= n 30) (list 'mero g 30))
          (else
           (let* ((n2 (if (< n 6) 6 30)) (s2 (ca-series g n2)))
             (if s2 (ca-mero-order g s2 n2) 'unknown))))))

; коэффициент при t^k: выражение или #f
(define (ca-info-coef info k)
  (cond ((equal? info 'unknown) #f)
        ((equal? (car info) 'mero) (if (< k (caddr info)) 0 (ca-try (lambda () (ca-coef-mero (cadr info) k)))))
        ((equal? (car info) 'ess) (let ((fn (caddr info))) (and fn (ca-try (lambda () (fn k))))))
        (else #f)))

; ---------- вычет ----------

; упрощение с общим знаменателем (дроби с алгебраическими числами сворачиваются)
(define (ca-clean e)
  (or (ca-try (lambda () (simplify (together e)))) (simplify e)))

(define (ca-residue f z z0)
  (if (ca-inf? z0)
      (let* ((g (ca-shift f z z0))
             (h (ca-try (lambda () (simplify (list '* g (list '^ ca-t -2))))))
             (c (and h (ca-info-coef (ca-analyze h) -1))))
        (and c (ca-clean (list '* -1 c))))
      (let ((c (ca-info-coef (ca-analyze (ca-shift f z z0)) -1)))
        (and c (ca-clean c)))))

; (residue f z z0) — вычет f в z0 (число, выражение или inf); unknown, если не вычислен
(define (residue f z z0)
  (let ((r (ca-try (lambda () (ca-residue f z z0)))))
    (if r r 'unknown)))

; ---------- ряд Лорана ----------

(define (ca-back e z z0)
  (subst (list ca-t (if (ca-inf? z0) (list '^ z -1) (list '+ z (list '* -1 z0)))) e))

; (laurent f z z0 n) — ряд Лорана по степеням (z − z0) (при z0 = inf — по 1/z) до степени n включительно
(define (laurent f z z0 n)
  (if (not (and (integer? n) (>= n 0)))
      (error "laurent: порядок n — целое ≥ 0")
      (let* ((g (ca-shift f z z0)) (info (ca-analyze g)))
        (cond ((equal? info 'unknown) 'unknown)
              ((equal? (car info) 'mero)
               (let ((s (ca-series g (+ n 1))))
                 (if s (ca-back (series->expr s) z z0) 'unknown)))
              (else
               (let ((fn (caddr info)))
                 (if (not fn)
                     'unknown
                     (let loop ((k (- 0 n)) (acc '()))
                       (if (> k n)
                           (ca-back (simplify (cons '+ acc)) z z0)
                           (let ((c (ca-try (lambda () (fn k)))))
                             (cond ((not c) 'unknown)
                                   ((equal? c 0) (loop (+ k 1) acc))
                                   (else (loop (+ k 1) (cons (list '* c (list '^ ca-t k)) acc))))))))))))))

; ---------- тип особой точки ----------

(define (ca-at0 e) (ca-try (lambda () (simplify (subst (list ca-t 0) e)))))
(define (ca-nonzero? v)
  (cond ((not v) #f)
        ((equal? v 0) #f)
        ((number? v) #t)
        (else (let ((c (ca-cnum v))) (if c (> (ca-cabs c) 1e-9) #t)))))

; подвыражение g определено при t = 0: знаменатели и tan/cot/sec/csc/tanh/coth не обращаются в 0/∞
(define (ca-head-defined? e)
  (let ((h (car e)))
    (cond ((and (equal? h '^) (number? (caddr e)) (< (caddr e) 0)) (ca-nonzero? (ca-at0 (cadr e))))
          ((equal? h '/) (every? (lambda (d) (ca-nonzero? (ca-at0 d))) (cddr e)))
          ((member? h '(tan sec)) (ca-nonzero? (ca-at0 (list 'cos (cadr e)))))
          ((member? h '(cot csc)) (ca-nonzero? (ca-at0 (list 'sin (cadr e)))))
          ((equal? h 'tanh) (ca-nonzero? (ca-at0 (list 'cosh (cadr e)))))
          ((equal? h 'coth) (ca-nonzero? (ca-at0 (list 'sinh (cadr e)))))
          (else #t))))
(define (ca-defined? e)
  (cond ((not (pair? e)) #t)
        (else (and (every? ca-defined? (cdr e)) (ca-head-defined? e)))))

; removable | regular | (pole k) | essential | unknown
(define (singularity-type f z z0)
  (let* ((g (ca-shift f z z0)) (info (ca-try (lambda () (ca-analyze g)))))
    (cond ((not info) 'unknown)
          ((equal? info 'unknown) 'unknown)
          ((equal? (car info) 'mero)
           (let ((v (caddr info)))
             (if (< v 0)
                 (list 'pole (- 0 v))
                 (if (ca-defined? (or (ca-try (lambda () (together g))) g)) 'regular 'removable))))
          ((and (equal? (car info) 'ess) (equal? (cadr info) 'cert)) 'essential)
          (else 'unknown))))

; ---------- особые точки ----------

; основания отрицательных степеней и знаменатели, содержащие z; unknown — tan-подобные функции от z
(define (ca-bases e z)
  (cond ((not (pair? e)) '())
        ((and (member? (car e) '(tan cot sec csc tanh coth)) (contains-sym? (cadr e) z)) 'unknown)
        (else
         (let ((sub (map (lambda (a) (ca-bases a z)) (cdr e))))
           (if (any? (lambda (s) (equal? s 'unknown)) sub)
               'unknown
               (let ((own (cond ((and (equal? (car e) '^) (number? (caddr e)) (< (caddr e) 0)) (list (cadr e)))
                                ((equal? (car e) '/) (cddr e))
                                (else '()))))
                 (append own (append-map (lambda (s) s) sub))))))))

; корни основания b (многочлен по z): список или unknown
(define (ca-base-roots b z)
  (cond ((not (contains-sym? b z)) '())
        ((not (polynomial? b z)) 'unknown)
        (else
         (let ((rs (ca-try (lambda () (set->list (solve b z))))))
           (if (or (not rs)
                   (any? (lambda (r) (and (pair? r) (member? (car r) '(root-of piecewise)))) rs))
               'unknown
               rs)))))

(define (ca-uniq l)
  (let loop ((l l) (acc '()))
    (cond ((null? l) (reverse acc))
          ((member? (car l) acc) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

; (singularities f z) — конечные особые точки (нули знаменателей, в том числе внутри аргументов exp/sin/…); unknown —
; корни не найдены явно, f не мероморфного вида или в знаменателе нерациональная функция от z; точки без особенности отброшены
(define (singularities f z)
  (if (not (ca-ok? f))
      'unknown
      (let ((bs (ca-try (lambda () (ca-bases f z)))))
        (if (or (not bs) (equal? bs 'unknown))
            'unknown
            (let loop ((l bs) (acc '()))
              (if (null? l)
                  (let ((cands (ca-uniq (map (lambda (p) (simplify p)) acc)))
                        (ok (lambda (p) (not (equal? (singularity-type f z p) 'regular)))))
                    (filter ok cands))
                  (let ((r (ca-base-roots (car l) z)))
                    (if (equal? r 'unknown) 'unknown (loop (cdr l) (append acc r))))))))))

; ---------- интеграл по окружности ----------

(define (ca-dist p c) (ca-cabs (ca-csub p c)))

; позиция точек относительно окружности: список (p . inside?) | unknown (точка на контуре или не вычислена)
(define (ca-classify pts cn rn)
  (let loop ((l pts) (acc '()))
    (if (null? l)
        (reverse acc)
        (let* ((pn (ca-cnum (car l))))
          (if (not pn)
              'unknown
              (let ((d (ca-dist pn cn)))
                (if (< (abs-float (- d rn)) (* 1e-9 (+ 1 rn)))
                    'unknown
                    (loop (cdr l) (cons (cons (car l) (< d rn)) acc)))))))))
(define (abs-float x) (if (< x 0) (- 0.0 x) x))

; (contour-integral f z center radius) — ∮_{|z − center| = radius}, против часовой: 2πi · Σ вычетов внутри;
; unknown: особая точка на контуре, не вычислен вычет или особые точки не найдены
(define (contour-integral f z center radius)
  (let ((cn (ca-cnum center)) (rn (ca-try (lambda () (eval-num radius)))))
    (if (or (not cn) (not (number? rn)) (<= rn 0))
        'unknown
        (let ((sg (ca-try (lambda () (singularities f z)))))
          (if (or (not sg) (equal? sg 'unknown))
              'unknown
              (let ((cl (ca-classify sg cn rn)))
                (if (equal? cl 'unknown)
                    'unknown
                    (let loop ((l cl) (tot 0))
                      (cond ((null? l) (ca-clean (list '* 2 '%i 'pi tot)))
                            ((not (cdr (car l))) (loop (cdr l) tot))
                            (else
                             (let ((r (residue f z (car (car l)))))
                               (if (equal? r 'unknown)
                                   'unknown
                                   (loop (cdr l) (list '+ tot r))))))))))))))

; ---------- численные сертификаты ----------

; ∮ f dz по окружности (центр c — комплексная пара, радиус r) — n узлов, правило трапеций (для аналитической
; подынтегральной экспоненциально точное); #f — не вычислилось
(define (ca-circle-int f z c r n)
  (ca-try
   (lambda ()
     (let ((h (/ (* 2.0 ca-pi) n)))
       (let loop ((k 0) (sum (cons 0.0 0.0)))
         (if (= k n)
             sum
             (let* ((th (* h k)) (w (cons (cos th) (sin th)))
                    (zz (ca-cadd c (ca-cmul (cons r 0.0) w)))
                    (fv (ca-ceval f z zz))
                    (dz (ca-cmul (cons 0.0 (* r h)) w)))
               (loop (+ k 1) (ca-cadd sum (ca-cmul fv dz))))))))))

; сравнение ∮ с целью target (пара): numeric | mismatch | unknown (два числа узлов должны сойтись)
(define (ca-verdict f z c r target)
  (let ((i1 (ca-circle-int f z c r 1024)) (i2 (ca-circle-int f z c r 2048)))
    (cond ((or (not i1) (not i2) (not target)) 'unknown)
          ((> (ca-cabs (ca-csub i1 i2)) (* 1e-7 (+ 1.0 (ca-cabs i2)))) 'unknown)
          ((< (ca-cabs (ca-csub i2 target)) (* 1e-6 (+ 1.0 (ca-cabs target)))) 'numeric)
          (else 'mismatch))))

; (contour-integral-check f z center radius ans) — численный ∮ по параметризации окружности против ans:
; numeric | mismatch | unknown
(define (contour-integral-check f z center radius ans)
  (let ((cn (ca-cnum center)) (rn (ca-try (lambda () (eval-num radius)))) (an (ca-cnum ans)))
    (if (or (not cn) (not (number? rn)) (<= rn 0) (not an) (equal? ans 'unknown))
        'unknown
        (ca-verdict f z cn rn an))))

; (residue-check f z z0 ans) — вычет ans сверяется с ∮ по малой окружности вокруг z0 (при z0 = inf — по большой, Res_∞ = −∮/2πi):
; numeric | mismatch | unknown (если особые точки не найдены — только numeric на кругах радиусов 1/20 и 1/40, иначе unknown)
(define (ca-residue-check-blind f z z0 an)
  (let ((cn (ca-cnum z0)))
    (if (or (not cn) (ca-inf? z0))
        'unknown
        (let ((t (cons 0.0 (* 2.0 ca-pi))))
          (if (and (equal? (ca-verdict f z cn 0.05 (ca-cmul t an)) 'numeric)
                   (equal? (ca-verdict f z cn 0.025 (ca-cmul t an)) 'numeric))
              'numeric
              'unknown)))))

(define (residue-check f z z0 ans)
  (let ((an (ca-cnum ans)) (sg (ca-try (lambda () (singularities f z)))))
    (cond
      ((or (not an) (equal? ans 'unknown)) 'unknown)
      ((or (not sg) (equal? sg 'unknown)) (ca-residue-check-blind f z z0 an))
      (else
        (let ((pn (map ca-cnum sg)))
          (if (any? (lambda (p) (not p)) pn)
              'unknown
              (if (ca-inf? z0)
                  (let ((r (+ 1.0 (* 2.0 (foldl (lambda (m p) (max m (ca-cabs p))) 0.0 pn)))))
                    (ca-verdict f z (cons 0.0 0.0) r (ca-cmul (cons 0.0 (* -2.0 ca-pi)) an)))
                  (let ((cn (ca-cnum z0)))
                    (if (not cn)
                        'unknown
                        (let* ((others (filter (lambda (p) (> (ca-dist p cn) 1e-9)) pn))
                               (dm (foldl (lambda (m p) (min m (ca-dist p cn))) 1.0 others)))
                          (ca-verdict f z cn (* 0.5 dm) (ca-cmul (cons 0.0 (* 2.0 ca-pi)) an))))))))))))

; ---------- ∫ R(x) dx по ℝ ----------

; (integral-by-residues f x) — ∫_{−∞}^{∞} R(x) dx = 2πi Σ_{Im p > 0} Res; R рациональна, deg знаменателя ≥ deg числителя + 2,
; вещественных полюсов нет; иначе unknown
(define (integral-by-residues f x)
  (if (not (ca-rational? f))
      'unknown
      (let* ((g (ca-shift f x 'inf)) (info (ca-try (lambda () (ca-analyze g)))))
        (if (or (not info) (equal? info 'unknown) (not (equal? (car info) 'mero)) (< (caddr info) 2))
            'unknown
            (let ((sg (ca-try (lambda () (singularities f x)))))
              (if (or (not sg) (equal? sg 'unknown))
                  'unknown
                  (let loop ((l sg) (tot 0))
                    (if (null? l)
                        (let* ((v (ca-clean (list '* 2 '%i 'pi tot))) (c (ca-cnum v)))
                          (if (and c (< (abs-float (cdr c)) 1e-9)) v 'unknown))
                        (let ((pn (ca-cnum (car l))))
                          (cond ((not pn) 'unknown)
                                ((< (abs-float (cdr pn)) 1e-9) 'unknown)
                                ((< (cdr pn) 0) (loop (cdr l) tot))
                                (else
                                 (let ((r (residue f x (car l))))
                                   (if (equal? r 'unknown)
                                       'unknown
                                       (loop (cdr l) (list '+ tot r)))))))))))))))

; ---------- шаг AS: проверка тождества с учётом ветвей и допущений ----------
; (branch-check lhs rhs cond) → numeric | mismatch | unknown. Численно в 12 точках главной ветви
; (log z: arg ∈ (−π, π], разрез по отрицательной полуоси; √z = exp(log z / 2); z^w = exp(w log z)).
; cond — #f/() (без условий: вещественные точки обеих знаков и комплексные по обе стороны разреза), форма (> x 0) |
; (>= x 0) | (< x 0) | (<= x 0) | (/= x 0) | (in x reals|integers|rationals|naturals|positive|…) | (real x) |
; (and c …) | список условий; точки берутся только из допущения. Условие вне словаря (x > a с символом a) — unknown.
; numeric — совпало во всех вычисленных точках (не доказательство); mismatch — найдена точка расхождения.
(define (bc-polar r th) (cons (* r (cos th)) (* r (sin th))))
(define bc-pool
  (list (cons -1.0 0.0) (cons 0.5 0.0) (cons -2.0 0.0) (cons 2.0 0.0) (cons 1.0 0.0) (cons -0.5 0.0)
        (cons 3.5 0.0) (cons -3.0 0.0) (cons 1.7 0.0) (cons -1.3 0.0)
        (bc-polar 1.5 (- ca-pi 0.1)) (bc-polar 1.5 (- 0.1 ca-pi)) (bc-polar 0.7 2.0) (bc-polar 2.0 -1.0)
        (bc-polar 1.2 0.5) (bc-polar 0.8 -2.5) (cons 0.5 4.0) (cons -1.0 -3.5)))

(define (bc-arg z)
  (let ((x (car z)) (y (cdr z)))
    (cond ((> x 0) (atan (/ y x)))
          ((< x 0) (if (>= y 0) (+ (atan (/ y x)) ca-pi) (- (atan (/ y x)) ca-pi)))
          ((> y 0) (/ ca-pi 2))
          ((< y 0) (/ ca-pi -2))
          (else 0.0))))
(define (bc-real? z) (= (cdr z) 0))
(define (bc-zero? z) (and (= (car z) 0) (= (cdr z) 0)))
(define (bc-log z)
  (if (bc-zero? z) (error "branch: log 0") (cons (log (ca-cabs z)) (bc-arg z))))
(define (bc-pow z w)
  (cond ((bc-zero? z) (if (> (car w) 0) (cons 0.0 0.0) (error "branch: 0^w")))
        ((and (bc-real? w) (= (car w) (floor (car w))) (< (abs-float (car w)) 60))
         (ca-cpow z (floor (car w))))
        (else (ca-cexp (ca-cmul w (bc-log z))))))
(define (bc-sqrt z) (if (bc-zero? z) z (ca-cexp (ca-cmul (cons 0.5 0.0) (bc-log z)))))

(define (bc-eval e env)
  (cond ((number? e) (cons (* 1.0 e) 0.0))
        ((equal? e '%i) (cons 0.0 1.0))
        ((equal? e 'pi) (cons ca-pi 0.0))
        ((symbol? e) (let ((p (assoc e env))) (if p (cdr p) (error "branch: неизвестный символ" e))))
        ((not (pair? e)) (error "branch: неизвестная форма"))
        (else
         (let* ((h (car e)) (args (map (lambda (a) (bc-eval a env)) (cdr e))) (a (car args)))
           (cond ((equal? h '+) (foldl ca-cadd (cons 0.0 0.0) args))
                 ((equal? h '*) (foldl ca-cmul (cons 1.0 0.0) args))
                 ((equal? h '-) (if (null? (cdr args)) (ca-cneg a) (ca-csub a (foldl ca-cadd (cons 0.0 0.0) (cdr args)))))
                 ((equal? h '/) (foldl (lambda (acc x) (ca-cdiv acc x)) a (cdr args)))
                 ((equal? h '^) (bc-pow a (cadr args)))
                 ((equal? h 'sqrt) (bc-sqrt a))
                 ((member? h '(log ln)) (bc-log a))
                 ((equal? h 'exp) (ca-cexp a))
                 ((equal? h 'abs) (cons (ca-cabs a) 0.0))
                 ((equal? h 'sin) (ca-csin a))
                 ((equal? h 'cos) (ca-ccos a))
                 ((equal? h 'sinh) (ca-csinh a))
                 ((equal? h 'cosh) (ca-ccosh a))
                 (else (error "branch: неизвестная функция" h)))))))

(define (bc-vars e)
  (cond ((number? e) '())
        ((symbol? e) (if (member? e '(%i pi)) '() (list e)))
        ((pair? e) (foldl (lambda (acc a) (foldl (lambda (s x) (if (member? x s) s (append s (list x)))) acc (bc-vars a))) '() (cdr e)))
        (else '())))

; условие → список (символ . предикат на комплексной точке) | #f (не разобрано)
(define (bc-bound-pred op c)
  (cond ((equal? op '>) (lambda (z) (and (bc-real? z) (> (car z) c))))
        ((equal? op '>=) (lambda (z) (and (bc-real? z) (>= (car z) c))))
        ((equal? op '<) (lambda (z) (and (bc-real? z) (< (car z) c))))
        (else (lambda (z) (and (bc-real? z) (<= (car z) c))))))
(define (bc-flip op) (cond ((equal? op '>) '<) ((equal? op '>=) '<=) ((equal? op '<) '>) (else '>=)))
(define (bc-dom-pred d)
  (cond ((equal? d 'reals) bc-real?)
        ((equal? d 'integers) (lambda (z) (and (bc-real? z) (= (car z) (floor (car z))))))
        ((equal? d 'naturals) (lambda (z) (and (bc-real? z) (= (car z) (floor (car z))) (>= (car z) 0))))
        ((equal? d 'rationals) bc-real?)
        ((equal? d 'complexes) (lambda (z) #t))
        ((equal? d 'positive) (bc-bound-pred '> 0))
        ((equal? d 'nonnegative) (bc-bound-pred '>= 0))
        ((equal? d 'negative) (bc-bound-pred '< 0))
        ((equal? d 'nonpositive) (bc-bound-pred '<= 0))
        (else #f)))
(define (bc-cond-preds c)
  (cond ((or (null? c) (equal? c #f)) '())
        ((not (pair? c)) #f)
        ((pair? (car c)) (bc-and-preds c))
        ((member? (car c) '(and m-vector)) (bc-and-preds (cdr c)))
        ((and (member? (car c) '(> >= < <=)) (= (length c) 3) (symbol? (cadr c)) (number? (caddr c)))
         (list (cons (cadr c) (bc-bound-pred (car c) (caddr c)))))
        ((and (member? (car c) '(> >= < <=)) (= (length c) 3) (number? (cadr c)) (symbol? (caddr c)))
         (list (cons (caddr c) (bc-bound-pred (bc-flip (car c)) (cadr c)))))
        ((and (equal? (car c) '/=) (= (length c) 3) (symbol? (cadr c)) (equal? (caddr c) 0))
         (list (cons (cadr c) (lambda (z) (not (bc-zero? z))))))
        ((and (member? (car c) '(in :in)) (= (length c) 3) (symbol? (cadr c)) (bc-dom-pred (caddr c)))
         (list (cons (cadr c) (bc-dom-pred (caddr c)))))
        ((and (equal? (car c) 'real) (= (length c) 2) (symbol? (cadr c))) (list (cons (cadr c) bc-real?)))
        (else #f)))
(define (bc-and-preds cs)
  (let ((rs (map bc-cond-preds cs)))
    (if (member? #f rs) #f (append-map (lambda (r) r) rs))))

(define (bc-var-pool v preds)
  (filter (lambda (z) (every? (lambda (p) ((cdr p) z)) (filter (lambda (p) (equal? (car p) v)) preds))) bc-pool))

(define (bc-close? a b)
  (let ((d (ca-cabs (ca-csub a b))))
    (< d (* 1e-9 (+ 1.0 (ca-cabs a) (ca-cabs b))))))

; результат точки: #t (совпало) | #f (расхождение) | skip (значение не определено)
(define (bc-point lhs rhs vars pools i)
  (let ((env (bc-env vars pools i 0)))
    (let ((l (ca-try (lambda () (bc-eval lhs env)))) (r (ca-try (lambda () (bc-eval rhs env)))))
      (if (or (not l) (not r)) 'skip (bc-close? l r)))))
(define (bc-env vars pools i j)
  (if (null? vars)
      '()
      (cons (cons (car vars) (nth (car pools) (mod (+ (* 5 i) (if (< i 6) 0 (* 7 j))) (length (car pools)))))
            (bc-env (cdr vars) (cdr pools) i (+ j 1)))))

(define (branch-check lhs rhs cond-form)
  (let ((preds (bc-cond-preds cond-form)))
    (if (equal? preds #f)
        'unknown
        (let* ((vars (bc-vars (list '+ lhs rhs)))
               (pools (map (lambda (v) (bc-var-pool v preds)) vars)))
          (if (member? '() pools)
              'unknown
              (let ((rs (map (lambda (i) (bc-point lhs rhs vars pools i)) '(0 1 2 3 4 5 6 7 8 9 10 11))))
                (cond ((member? #f rs) 'mismatch)
                      ((< (length (filter (lambda (r) (equal? r #t)) rs)) 6) 'unknown)
                      (else 'numeric))))))))

; ---------- шаг CA.b: определённые интегралы вычетами (Жордан, главное значение, замочная скважина) ----------
; (integral-fourier f x) — ∫_{−∞}^{∞} Σ R_k(x)·{cos(a x) | sin(a x) | exp(i a x) | 1} dx, R_k рациональны. Лемма Жордана: R e^{i b x}
;   (b > 0) замыкается в верхней полуплоскости, e^{−i b x} — в нижней; cos/sin/exp — линейные комбинации (знак a — из деклараций,
;   неизвестен → unknown). Порядок убывания R на ∞ ≥ 1 (без экспоненты ≥ 2). Вещественные полюсы — только если подынтегральная
;   функция в них устранима (sin x / x): полувычеты πi·Res складываются в обычное значение; иначе unknown (интеграл расходится).
; (integral-pv f x) — то же, но допускает простые вещественные полюса: v.p. ∫ = 2πi Σ_{Im>0} + πi Σ_{Im=0} (при e^{−ibx} — −2πi Σ_{Im<0} − πi Σ_{Im=0});
;   пишет условие (principal-value …). Обычный integrate такой интеграл не берёт (расходится).
; (integral-keyhole f x) — ∫_0^∞ Σ x^α R(x) dx (α нецелое рациональное), ∫_0^∞ R(x) log x dx и ∫_0^∞ R(x) dx по контуру «замочная скважина»:
;   ветвь z^α = |z|^α e^{iα arg z}, arg ∈ (0, 2π); I = −π/sin(πα)·Σ_{z≠0} Res[e^{−iπα} z^α R] (= 2πi/(1−e^{2πiα})·Σ Res);
;   ∫R = −Σ Res[R log z]; ∫R log x = Σ Res[R(−log²z/2 + iπ log z)]. Сходимость: α + v₀ > −1 и d − α > 1 (v₀ — порядок R в 0, d — убывание на ∞);
;   для log и ∫R: v₀ ≥ 0, d ≥ 2. Полюсы на (0, ∞) — unknown; вычеты кратных полюсов — по главной части ряда Лорана.
; (integral-residues-check f x lo hi ans) → numeric | mismatch | unknown: независимая квадратура (трапеции по x = e^t / x = sinh t; для cos/sin
;   на ℝ — средние Чезаро по двум длинам). Параметры берутся при знаках из деклараций.
; (definite-by-residues f x lo hi) — запасной путь integrate: lo, hi — (−inf, inf) или (0, inf); ответ только после численной сверки.
(define cb-eps 1e-9)
(define (cb-pi2i) (list '* 2 '%i 'pi))
(define (cb-pii) (list '* '%i 'pi))

(define (cb-sign a)
  (cond ((number? a) (cond ((> a 0) 1) ((< a 0) -1) (else #f)))
        ((true? (positive? a)) 1)
        ((true? (negative? a)) -1)
        ((cb-ipos? a) 1)
        ((cb-ineg? a) -1)
        (else #f)))

(define (cb-fact n) (if (< n 2) 1 (* n (cb-fact (- n 1)))))

; ---------- CA.c: интервальная оценка по декларациям ----------
; интервал — (lo lc hi hc): границы — числа с плавающей точкой (±cb-big — бесконечность), lc/hc — граница достижима.
; Знак выражения (a² − b², α + 1 …) выводится по интервалам деклараций символов (assuming ((a (interval 2 'inf 'open 'open))) …);
; оценка консервативна (зависимые вхождения не сокращаются): «доказано» — только при строгом знаке всего интервала.
(define cb-big 1e300)
(define cb-assumed '())    ; ((символ . интервал) …) — дополнительные допущения на время сверки (область сходимости)
(define (cb-bnd b) (cond ((equal? b 'inf) cb-big) ((equal? b '-inf) (- 0.0 cb-big)) (else (* 1.0 b))))
(define (cb-clamp v) (cond ((> v cb-big) cb-big) ((< v (- 0.0 cb-big)) (- 0.0 cb-big)) (else v)))
(define (cb-iv-pt v) (list (* 1.0 v) #t (* 1.0 v) #t))
(define (cb-iv-meet a b)
  (let* ((lo (cond ((> (nth a 0) (nth b 0)) (list (nth a 0) (nth a 1)))
                   ((< (nth a 0) (nth b 0)) (list (nth b 0) (nth b 1)))
                   (else (list (nth a 0) (and (nth a 1) (nth b 1))))))
         (hi (cond ((< (nth a 2) (nth b 2)) (list (nth a 2) (nth a 3)))
                   ((> (nth a 2) (nth b 2)) (list (nth b 2) (nth b 3)))
                   (else (list (nth a 2) (and (nth a 3) (nth b 3)))))))
    (list (car lo) (cadr lo) (car hi) (cadr hi))))
(define (cb-iv-of i) (list (cb-bnd (interval-lo i)) (interval-lo-closed? i) (cb-bnd (interval-hi i)) (interval-hi-closed? i)))

; пересечение интервалов деклараций символа (и допущений сверки); #f — вещественных деклараций нет
(define (cb-decl-ival x)
  (let* ((base (let loop ((cs (constraints-of x)) (r (list (- 0.0 cb-big) #f cb-big #f)) (any #f))
                 (if (null? cs)
                     (and any r)
                     (let* ((c (car cs)) (i (cond ((interval? c) c) ((domain? c) (domain-hull c)) (else #f))))
                       (if i (loop (cdr cs) (cb-iv-meet r (cb-iv-of i)) #t) (loop (cdr cs) r any))))))
         (extra (assoc x cb-assumed)))
    (cond ((and base extra) (cb-iv-meet base (cdr extra)))
          (base base)
          (extra (cdr extra))
          (else #f))))

(define (cb-iv-pos? a) (or (> (nth a 0) 0.0) (and (= (nth a 0) 0.0) (not (nth a 1)))))
(define (cb-iv-neg? a) (or (< (nth a 2) 0.0) (and (= (nth a 2) 0.0) (not (nth a 3)))))
(define (cb-iv-add a b)
  (list (cb-clamp (+ (nth a 0) (nth b 0))) (and (nth a 1) (nth b 1)) (cb-clamp (+ (nth a 2) (nth b 2))) (and (nth a 3) (nth b 3))))
(define (cb-mul-pt x xc y yc)
  (cond ((= x 0.0) (cons 0.0 xc)) ((= y 0.0) (cons 0.0 yc)) (else (cons (cb-clamp (* x y)) (and xc yc)))))
(define (cb-iv-mul a b)
  (let* ((ps (list (cb-mul-pt (nth a 0) (nth a 1) (nth b 0) (nth b 1)) (cb-mul-pt (nth a 0) (nth a 1) (nth b 2) (nth b 3))
                   (cb-mul-pt (nth a 2) (nth a 3) (nth b 0) (nth b 1)) (cb-mul-pt (nth a 2) (nth a 3) (nth b 2) (nth b 3))))
         (lo (foldl (lambda (m p) (min m (car p))) (car (car ps)) ps))
         (hi (foldl (lambda (m p) (max m (car p))) (car (car ps)) ps)))
    (list lo (any? (lambda (p) (and (= (car p) lo) (cdr p))) ps) hi (any? (lambda (p) (and (= (car p) hi) (cdr p))) ps))))
(define (cb-iv-negate a) (list (- 0.0 (nth a 2)) (nth a 3) (- 0.0 (nth a 0)) (nth a 1)))
(define (cb-iv-inv a)    ; 1/a для строго положительного или отрицательного интервала
  (cond ((cb-iv-pos? a)
         (list (if (>= (nth a 2) cb-big) 0.0 (/ 1.0 (nth a 2))) (and (nth a 3) (< (nth a 2) cb-big))
               (if (= (nth a 0) 0.0) cb-big (/ 1.0 (nth a 0))) (and (nth a 1) (> (nth a 0) 0.0))))
        ((cb-iv-neg? a) (let ((r (cb-iv-inv (cb-iv-negate a)))) (and r (cb-iv-negate r))))
        (else #f)))
(define (cb-fpow v n) (if (= n 0) 1.0 (cb-clamp (* v (cb-fpow v (- n 1))))))
(define (cb-iv-abs a)
  (cond ((>= (nth a 0) 0.0) a)
        ((<= (nth a 2) 0.0) (cb-iv-negate a))
        (else (let ((m (max (- 0.0 (nth a 0)) (nth a 2))))
                (list 0.0 #t m (cond ((> (- 0.0 (nth a 0)) (nth a 2)) (nth a 1)) ((< (- 0.0 (nth a 0)) (nth a 2)) (nth a 3)) (else (or (nth a 1) (nth a 3)))))))))
(define (cb-iv-pow a n)
  (cond ((= n 0) (cb-iv-pt 1))
        ((= n 1) a)
        ((< n 0) (let ((r (cb-iv-inv a))) (and r (cb-iv-pow r (- 0 n)))))
        ((= (modulo n 2) 1) (list (cb-fpow (nth a 0) n) (nth a 1) (cb-fpow (nth a 2) n) (nth a 3)))
        (else (let ((b (cb-iv-abs a))) (list (cb-fpow (nth b 0) n) (nth b 1) (cb-fpow (nth b 2) n) (nth b 3))))))
(define (cb-fold-iv f args)
  (let ((first (cb-ival (car args))))
    (let loop ((l (cdr args)) (acc first))
      (if (or (null? l) (not acc)) acc (loop (cdr l) (let ((v (cb-ival (car l)))) (and v (f acc v))))))))
(define (cb-ival1 e)
  (cond ((number? e) (cb-iv-pt e))
        ((equal? e 'pi) (list 3.14159 #t 3.1416 #t))
        ((symbol? e) (cb-decl-ival e))
        ((not (pair? e)) #f)
        ((equal? (car e) '+) (cb-fold-iv cb-iv-add (cdr e)))
        ((equal? (car e) '*) (cb-fold-iv cb-iv-mul (cdr e)))
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (caddr e)))
         (let ((b (cb-ival (cadr e)))) (and b (cb-iv-pow b (caddr e)))))
        ((and (equal? (car e) 'abs) (= (length e) 2)) (let ((b (cb-ival (cadr e)))) (and b (cb-iv-abs b))))
        (else #f)))
(define (cb-ival e) (ca-try (lambda () (cb-ival1 e))))
(define (cb-ipos? e) (let ((v (cb-ival e))) (and v (cb-iv-pos? v))))
(define (cb-ineg? e) (let ((v (cb-ival e))) (and v (cb-iv-neg? v))))
(define (cb-inonpos? e) (let ((v (cb-ival e))) (and v (<= (nth v 2) 0.0))))    ; e ≤ 0 на всей области

; до трёх значений символа внутри интервала деклараций (k — номер символа: разводит значения); #f — вещественных деклараций нет
(define (cb-cands s k)
  (let ((iv (cb-decl-ival s)))
    (and iv
         (let ((lo (nth iv 0)) (hi (nth iv 2)) (fl (<= (nth iv 0) (- 0.0 cb-big))) (fh (>= (nth iv 2) cb-big)))
           (cond ((and fl fh) (list (+ 1.3 (* 0.37 k)) (- 0.0 (+ 0.55 (* 0.2 k))) (+ 2.9 (* 0.5 k))))
                 (fh (list (+ lo 1.3 (* 0.37 k)) (+ lo 0.55 (* 0.2 k)) (+ lo 2.9 (* 0.5 k))))
                 (fl (list (- hi 1.3 (* 0.37 k)) (- hi 0.55 (* 0.2 k)) (- hi 2.9 (* 0.5 k))))
                 ((<= (- hi lo) 0.0) (list lo))
                 (else (let ((w (- hi lo))) (list (+ lo (* 0.43 w)) (+ lo (* 0.27 w)) (+ lo (* 0.71 w))))))))))

; n окружений: i-е значение каждого символа (пары по номеру); #f — у какого-то символа нет вещественной декларации
(define (cb-envs syms n)
  (if (null? syms)
      (list '())
      (let loop ((l syms) (k 0) (cs '()))
        (if (null? l)
            (let ((cs (reverse cs)))
              (map (lambda (i) (map2 (lambda (s c) (list s (nth c (min i (- (length c) 1))))) syms cs)) (range n)))
            (let ((c (cb-cands (car l) k))) (and c (loop (cdr l) (+ k 1) (cons c cs))))))))

; все сочетания кандидатов (≤ 81), иначе пары
(define (cb-env-grid syms)
  (let loop ((l syms) (k 0) (cs '()))
    (if (null? l)
        (let ((cs (reverse cs)))
          (if (> (foldl (lambda (m c) (* m (length c))) 1 cs) 81)
              (cb-envs syms 3)
              (let build ((ss syms) (cc cs))
                (if (null? ss)
                    (list '())
                    (let ((rest (build (cdr ss) (cdr cc))))
                      (append-map (lambda (v) (map (lambda (e) (cons (list (car ss) v) e)) rest)) (car cc)))))))
        (let ((c (cb-cands (car l) k))) (and c (loop (cdr l) (+ k 1) (cons c cs)))))))

; наименьший показатель ряда R по (x − p) (p = inf: по 1/x); отрицательный — полюс; #f — не определено / ноль
(define (cb-order R x p)
  (let ((info (ca-try (lambda () (ca-analyze (ca-shift R x p))))))
    (and info (not (equal? info 'unknown)) (equal? (car info) 'mero) (< (caddr info) 30) (caddr info))))

; ((p kind c) …), kind = real | upper | lower; #f — полюса не найдены явно
(define (cb-poles R x)
  (let ((sg (ca-try (lambda () (singularities R x)))))
    (and sg (not (equal? sg 'unknown))
         (let loop ((l sg) (acc '()))
           (if (null? l)
               (reverse acc)
               (let ((c (ca-cnum (car l))))
                 (and c (loop (cdr l)
                              (cons (list (car l)
                                          (cond ((< (abs-float (cdr c)) cb-eps) 'real) ((> (cdr c) 0) 'upper) (else 'lower))
                                          c)
                                    acc)))))))))

; главная часть R в точке p: (c₋₁ c₋₂ … c₋ₘ); () — нет полюса; #f — не определено
(define (cb-neg-coefs R x p)
  (let ((info (ca-try (lambda () (ca-analyze (ca-shift R x p))))))
    (and info (not (equal? info 'unknown)) (equal? (car info) 'mero)
         (let ((m (- 0 (caddr info))))
           (let loop ((k 1) (acc '()))
             (if (> k m)
                 (reverse acc)
                 (let ((c (ca-info-coef info (- 0 k))))
                   (and c (loop (+ k 1) (cons c acc))))))))))

; Res_{z=p} R·φ = Σ_k c₋ₖ φ^{(k−1)}(p)/(k−1)!; dv j — значение φ^{(j)}(p); #f — не определено
(define (cb-res R x p dv)
  (let ((cs (cb-neg-coefs R x p)))
    (and cs
         (let loop ((l cs) (k 1) (acc '()))
           (if (null? l)
               (ca-clean (cons '+ acc))
               (loop (cdr l) (+ k 1)
                     (cons (list '* (car l) (dv (- k 1)) (/ 1 (cb-fact (- k 1)))) acc)))))))

; Σ вес(вид полюса)·Res[R φ]; вещественные полюса при ненулевом весе — только простые; #f — не определено
(define (cb-contour R x poles wts dv)
  (let loop ((l poles) (acc '()))
    (if (null? l)
        (ca-clean (cons '+ acc))
        (let* ((p (car (car l))) (kind (cadr (car l)))
               (w (cond ((equal? kind 'upper) (car wts)) ((equal? kind 'real) (cadr wts)) (else (caddr wts)))))
          (cond ((equal? w 0) (loop (cdr l) acc))
                ((and cb-strict (equal? kind 'real) (not (equal? (length (or (cb-neg-coefs R x p) '(1 2))) 1))) #f)
                (else (let ((r (cb-res R x p dv)))
                        (and r (loop (cdr l) (cons (list '* w r) acc))))))))))

; ∫ R(x) e^{i s b x} dx, s = ±1, b > 0 (главное значение при вещественных полюсах)
(define (cb-K R x b s poles)
  (let ((sb (list '* '%i s b)))
    (cb-contour-p R x poles
                  (if (= s 1) (list (cb-pi2i) (cb-pii) 0) (list 0 (list '* -1 (cb-pii)) (list '* -1 (cb-pi2i))))
                  (lambda (p j) (list '* (list '^ sb j) (cb-cexp (list '* sb p)))))))

; cos B + i sin B (угол B делаем неотрицательным: упрощатель чётность cos/sin не применяет)
(define (cb-neg? B)
  (let ((c (ca-cnum B))) (if c (< (car c) 0) (equal? (cb-sign B) -1))))
(define (cb-cis B)
  (if (cb-neg? B)
      (let ((C (simplify (list '* -1 B)))) (list '+ (list 'cos C) (list '* -1 '%i (list 'sin C))))
      (list '+ (list 'cos B) (list '* '%i (list 'sin B)))))
; exp(u) для точного комплексного u (символы вещественны): e^{Re u}(cos Im u + i sin Im u)
(define (cb-cexp u)
  (let* ((uc (cb-conj u))
         (A (simplify (expand (list '* 1/2 (list '+ u uc)))))
         (B (simplify (expand (list '* -1/2 '%i (list '+ u (list '* -1 uc)))))))
    (if (equal? B 0) (list 'exp A) (list '* (list 'exp A) (cb-cis B)))))

; вариант cb-contour, где dv зависит от полюса: (dv p j)
(define (cb-contour-p R x poles wts dv)
  (let loop ((l poles) (acc '()))
    (if (null? l)
        (ca-clean (cons '+ acc))
        (let* ((p (car (car l))) (kind (cadr (car l)))
               (w (cond ((equal? kind 'upper) (car wts)) ((equal? kind 'real) (cadr wts)) (else (caddr wts)))))
          (cond ((equal? w 0) (loop (cdr l) acc))
                ((and cb-strict (equal? kind 'real) (not (equal? (length (or (cb-neg-coefs R x p) '(1 2))) 1))) #f)
                (else (let ((r (cb-res R x p (lambda (j) (dv p j)))))
                        (and r (loop (cdr l) (cons (list '* w r) acc))))))))))

; a = u / x, без x (u линейна по x без свободного члена) или #f
(define (cb-linear-coef u x)
  (let ((a (ca-try (lambda () (simplify (list '/ u x))))))
    (and a (not (contains-sym? a x)) a)))

; множитель-тригонометрия: (cos a) | (sin a) | (exp a) (a — вещественная частота) | #f
(define (cb-trig-factor fc x)
  (and (pair? fc) (= (length fc) 2)
       (cond ((member? (car fc) '(cos sin))
              (let ((a (cb-linear-coef (cadr fc) x))) (and a (not (contains-sym? a '%i)) (list (car fc) a))))
             ((equal? (car fc) 'exp)
              (let ((a (cb-linear-coef (ca-try (lambda () (simplify (list '/ (cadr fc) '%i)))) x)))
                (and a (not (contains-sym? a '%i)) (list 'exp a))))
             (else #f))))

; слагаемое → (R вид a), вид = cos | sin | exp | none; #f — не разобрано
(define (cb-term tm x)
  (let loop ((fs (ca-factors tm)) (trig #f) (rest '()))
    (if (null? fs)
        (let ((R (simplify (cons '* (reverse rest)))))
          (and (ca-rational? R) (contains-sym? R x)
               (if trig (list R (car trig) (cadr trig)) (list R 'none 0))))
        (let ((t (cb-trig-factor (car fs) x)))
          (cond ((and t trig) #f)
                (t (loop (cdr fs) t rest))
                (else (loop (cdr fs) trig (cons (car fs) rest))))))))

; CA.c: слагаемое с произведением или степенью тригонометрии (sin²x, cos ax·cos bx, sin x·cos x) → список слагаемых R·cos / R·sin / R
; (понижение степени через e^{iωx}: коэффициенты — точные гауссовы рациональные, частоты — выражения без деклараций)
(define cb-strict #t)    ; #t — вещественные полюса только простые (главное значение); #f — любой порядок (устранимость всей суммы проверяется отдельно)
(define (cb-gadd a b) (cons (+ (car a) (car b)) (+ (cdr a) (cdr b))))
(define (cb-gmul a b) (cons (- (* (car a) (car b)) (* (cdr a) (cdr b))) (+ (* (car a) (cdr b)) (* (cdr a) (car b)))))
(define (cb-gzero? a) (and (= (car a) 0) (= (cdr a) 0)))
(define (cb-gexpr a) (simplify (list '+ (car a) (list '* (cdr a) '%i))))
(define (cb-tp-add tp w c)
  (cond ((null? tp) (list (cons w c)))
        ((equal? (car (car tp)) w) (cons (cons w (cb-gadd (cdr (car tp)) c)) (cdr tp)))
        (else (cons (car tp) (cb-tp-add (cdr tp) w c)))))
(define (cb-tp-mul p q)
  (foldl (lambda (acc a)
           (foldl (lambda (acc2 b) (cb-tp-add acc2 (simplify (list '+ (car a) (car b))) (cb-gmul (cdr a) (cdr b)))) acc q))
         '() p))
(define (cb-tp-of tf)    ; (cos a) | (sin a) | (exp a) → тригонометрический многочлен
  (let ((a (cadr tf)) (na (simplify (list '* -1 (cadr tf)))))
    (cond ((equal? (car tf) 'cos) (list (cons a (cons 1/2 0)) (cons na (cons 1/2 0))))
          ((equal? (car tf) 'sin) (list (cons a (cons 0 -1/2)) (cons na (cons 0 1/2))))
          (else (list (cons a (cons 1 0)))))))
(define (cb-tp-pow tp n) (if (= n 1) tp (cb-tp-mul tp (cb-tp-pow tp (- n 1)))))
; множитель: тригонометрия или её натуральная степень (≤ 8) → (многочлен . степень) | #f
(define (cb-trig-power fc x)
  (let ((t (cb-trig-factor fc x)))
    (cond (t (cons (cb-tp-of t) 1))
          ((and (pair? fc) (equal? (car fc) '^) (= (length fc) 3) (integer? (caddr fc)) (>= (caddr fc) 2) (<= (caddr fc) 8))
           (let ((b (cb-trig-factor (cadr fc) x)))
             (and b (cons (cb-tp-pow (cb-tp-of b) (caddr fc)) (caddr fc)))))
          (else #f))))
; Σ c e^{iωx} → ((R' вид ω) …): c e^{iωx} + c' e^{−iωx} = (c + c') cos ωx + i (c − c') sin ωx
(define (cb-tp-parts tp R)
  (let loop ((l tp) (done '()) (acc '()))
    (cond ((null? l) (reverse acc))
          ((member? (car (car l)) done) (loop (cdr l) done acc))
          (else
           (let* ((w (car (car l))) (c1 (cdr (car l))) (nw (simplify (list '* -1 w)))
                  (pr (assoc nw tp)) (c2 (if pr (cdr pr) (cons 0 0)))
                  (mk (lambda (cf kind)
                        (if (cb-gzero? cf) '() (list (list (simplify (list '* (cb-gexpr cf) R)) kind w))))))
             (loop (cdr l) (cons nw (cons w done))
                   (if (equal? w 0)
                       (append (reverse (mk c1 'none)) acc)
                       (append (reverse (mk (cb-gmul (cons 0 1) (cb-gadd c1 (cons (- 0 (car c2)) (- 0 (cdr c2)))))
                                            'sin))
                               (reverse (mk (cb-gadd c1 c2) 'cos))
                               acc))))))))
(define (cb-term-multi tm x)
  (let loop ((fs (ca-factors tm)) (tp (list (cons 0 (cons 1 0)))) (cnt 0) (rest '()))
    (if (null? fs)
        (let ((R (simplify (cons '* (reverse rest)))))
          (and (> cnt 1) (ca-rational? R) (contains-sym? R x) (cb-tp-parts tp R)))
        (let ((pw (cb-trig-power (car fs) x)))
          (if pw
              (loop (cdr fs) (cb-tp-mul tp (car pw)) (+ cnt (cdr pw)) rest)
              (loop (cdr fs) tp cnt (cons (car fs) rest)))))))

(define (cb-parts f x)
  (let ((g (ca-try (lambda () (expand f)))))
    (and g (let loop ((ts (ca-terms g)) (acc '()))
             (if (null? ts)
                 acc
                 (let ((p (cb-term (car ts) x)))
                   (if p
                       (loop (cdr ts) (append acc (list p)))
                       (let ((ps (cb-term-multi (car ts) x)))
                         (and ps (loop (cdr ts) (append acc ps)))))))))))

; интеграл одного слагаемого по ℝ (главное значение), #f — условия не выполнены
(define (cb-term-int R kind a x poles)
  (let ((d (cb-order R x 'inf)))
    (cond ((not d) #f)
          ((equal? kind 'none)
           (and (>= d 2) (cb-contour R x poles (list (cb-pi2i) (cb-pii) 0) (lambda (j) (if (= j 0) 1 0)))))
          ((< d 1) #f)
          (else
           (let ((sg (cb-sign a)))
             (and sg
                  (let* ((b (if (= sg 1) a (simplify (list '* -1 a))))
                         (kp (cb-K R x b 1 poles)) (km (cb-K R x b -1 poles)))
                    (and kp km
                         (cond ((equal? kind 'cos) (list '* 1/2 (list '+ kp km)))
                               ((equal? kind 'sin) (list '* sg -1/2 '%i (list '+ kp (list '* -1 km))))
                               (else (if (= sg 1) kp km)))))))))))

(define (cb-fourier f x pv?)
  (set! cb-strict pv?)
  (let ((parts (cb-parts f x)))
    (if (or (not parts) (null? parts))
        'unknown
        (let loop ((l parts) (acc '()) (reals '()))
          (if (null? l)
              (cb-fourier-finish f x acc reals pv?)
              (let* ((pt (car l)) (R (car pt)) (poles (cb-poles R x)))
                (if (not poles)
                    'unknown
                    (let ((v (cb-term-int R (cadr pt) (caddr pt) x poles)))
                      (if (not v)
                          'unknown
                          (loop (cdr l) (cons v acc)
                                (append reals (map car (filter (lambda (q) (equal? (cadr q) 'real)) poles)))))))))))))

(define (cb-fourier-finish f x acc reals pv?)
  (let ((v (ca-try (lambda () (simplify (expand (cons '+ acc)))))))
    (cond ((not v) 'unknown)
          ((and (not pv?)
                (not (every? (lambda (p) (member? (ca-try (lambda () (singularity-type f x p))) '(removable regular))) reals)))
           'unknown)
          ((let ((c (ca-cnum v))) (and c (not (contains-sym? f '%i)) (> (abs-float (cdr c)) 1e-7))) 'unknown)
          (else v))))

(define (integral-fourier f x) (cb-fourier f x #f))

(define (integral-pv f x)
  (let ((v (cb-fourier f x #t)))
    (when (not (equal? v 'unknown))
      (record-condition (list 'principal-value f) "значение — главное по Коши (интеграл как несобственный расходится при вещественных полюсах)"))
    v))

; ---------- замочная скважина ----------

; слагаемое → (α R lg), lg = #t для множителя log x; α = 0 без степени; #f — не разобрано
; CA.c: показатель α — рациональное число, «символ + число» (x^(a−1)) или выражение с объявленными интервалами; целозначный — нет
(define (cb-split-const e)    ; e = rest + c
  (if (and (pair? e) (equal? (car e) '+))
      (let loop ((l (cdr e)) (rest '()) (c 0))
        (cond ((null? l) (cons (cond ((null? rest) 0) ((null? (cdr rest)) (car rest)) (else (cons '+ (reverse rest)))) c))
              ((number? (car l)) (loop (cdr l) rest (+ c (car l))))
              (else (loop (cdr l) (cons (car l) rest) c))))
      (if (number? e) (cons 0 e) (cons e 0))))
(define (cb-sym-form al)      ; (s . c) для α = s + c, s — символ (не pi, не %i)
  (let ((sp (cb-split-const al))) (and (symbol? (car sp)) (not (member? (car sp) '(pi %i))) sp)))
(define (cb-key-exp? e x)
  (and (not (contains-sym? e x)) (not (contains-sym? e '%i))
       (or (equal? (type-of e) 'rational)
           (and (not (number? e)) (ca-rational? e) (not (true? (integer-valued? e)))
                (or (cb-sym-form e) (cb-ival e))))))

(define (cb-key-term tm x)
  (let loop ((fs (ca-factors tm)) (al #f) (lg #f) (rest '()))
    (if (null? fs)
        (let ((R (simplify (cons '* (reverse rest)))))
          (and (ca-rational? R) (contains-sym? R x)
               (list (or al 0) R lg)))
        (let ((fc (car fs)))
          (cond ((and (pair? fc) (equal? (car fc) '^) (equal? (cadr fc) x) (cb-key-exp? (caddr fc) x))
                 (and (not al) (loop (cdr fs) (caddr fc) lg rest)))
                ((and (pair? fc) (equal? (car fc) 'log) (equal? (cadr fc) x))
                 (and (not lg) (loop (cdr fs) al #t rest)))
                (else (loop (cdr fs) al lg (cons fc rest))))))))

(define (cb-conj e) (subst (list '%i (list '* -1 '%i)) e))

; q = θ/π — рациональное с небольшим знаменателем или #f
(define (cb-rat q)
  (let loop ((n 1))
    (cond ((> n 24) #f)
          ((< (abs-float (- (* q n) (floor (+ (* q n) 0.5)))) 1e-7) (/ (floor (+ (* q n) 0.5)) n))
          (else (loop (+ n 1))))))

; (θ/π, |p|²) для полюса p ∈ (0, 2π) по аргументу; #f — не определено
(define (cb-polar p c)
  (let* ((th0 (bc-arg c)) (th (if (> th0 1e-12) th0 (+ th0 (* 2.0 ca-pi)))) (q (cb-rat (/ th ca-pi)))
         (r2 (ca-try (lambda () (simplify (expand (list '* p (cb-conj p))))))))
    (and q r2 (list q r2))))

(define cb-u 'cb_u)
(define cb-z 'cb_z)
; φ^{(j)}: D f = ∂_z f + ∂_u f / z (u = log z)
(define (cb-dphi phi j)
  (if (= j 0)
      phi
      (cb-dphi (simplify (list '+ (diff cb-z phi) (list '/ (diff cb-u phi) cb-z))) (- j 1))))

; Σ по полюсам вне 0 (на положительной полуоси — #f); make-dv p q r2 → dv
(define (cb-key-sum R x make-dv)
  (let ((poles (cb-poles R x)))
    (and poles
         (let loop ((l poles) (acc '()))
           (if (null? l)
               (ca-clean (cons '+ acc))
               (let* ((p (car (car l))) (c (nth (car l) 2)))
                 (cond ((< (ca-cabs c) cb-eps) (loop (cdr l) acc))
                       ((and (< (abs-float (cdr c)) cb-eps) (> (car c) 0)) #f)
                       (else
                        (let ((pl (cb-polar p c)))
                          (and pl
                               (let ((r (cb-res R x p (make-dv p (car pl) (cadr pl)))))
                                 (and r (loop (cdr l) (cons r acc))))))))))))))

(define (cb-key-int al R lg x)
  (let ((v0 (cb-order R x 0)) (d (cb-order R x 'inf)))
    (cond ((or (not v0) (not d)) #f)
          ((equal? al 0)
           (and (>= v0 0) (>= d 2)
                (let ((phi0 (if lg
                                (list '+ (list '* -1/2 cb-u cb-u) (list '* '%i 'pi cb-u))
                                (list '* -1 cb-u))))
                  (cb-key-sum R x
                              (lambda (p q r2)
                                (let ((uv (list '+ (list '* 1/2 (list 'log r2)) (list '* '%i q 'pi))))
                                  (lambda (j) (subst (list (list cb-z p) (list cb-u uv)) (cb-dphi phi0 j)))))))))
          (else
           (let ((cv (cb-key-conv al v0 d)))
             (and cv
                  (let ((r (cb-key-F* al R lg x)))
                    (and r (begin (when (pair? cv) (for-each (lambda (c) (cb-note-cond c "условие сходимости ∫₀^∞ x^α R(x) dx")) cv))
                                  r)))))))))

; условия сходимости ∫₀^∞ x^α R: α + v₀ + 1 > 0 и d − 1 − α > 0. #t — доказаны декларациями; список условий — не доказаны, но совместимы
; с декларациями (α = s + c: s > −1 − v₀ − c, s < d − 1 − c); #f — нарушены или нельзя записать
(define (cb-key-conv al v0 d)
  (let ((e1 (simplify (list '+ al v0 1))) (e2 (simplify (list '+ d -1 (list '* -1 al)))))
    (cond ((and (cb-ipos? e1) (cb-ipos? e2)) #t)
          ((or (cb-inonpos? e1) (cb-inonpos? e2)) #f)
          ((number? al) #f)
          (else (let ((sf (cb-sym-form al)))
                  (and sf
                       (let ((s (car sf)) (c (cdr sf)))
                         (append (if (cb-ipos? e1) '() (list (list '> s (- (- -1 v0) c))))
                                 (if (cb-ipos? e2) '() (list (list '< s (- (- d 1) c))))))))))))

; −π/sin(πα)·Σ Res[e^{−iπα} z^α R] (без проверки сходимости)
(define (cb-key-F al R x)
  (let ((s (cb-key-sum R x
                       (lambda (p q r2)
                         (let* ((ang (list '* (* al (- q 1)) 'pi))
                                (W (list '* (list '^ r2 (/ al 2)) (cb-cis ang))))
                           (lambda (j)
                             (list '* (cb-ff al j) W (list '^ p (- 0 j)))))))))
    (and s (list '* -1 'pi (list '^ (cb-sinpi al) -1) s))))
(define (cb-sinpi al)
  (if (number? al)
      (list 'sin (list '* al 'pi))
      (let* ((sp (cb-split-const al)) (c (cdr sp)))
        (if (and (integer? c) (not (equal? (car sp) 0)))
            (let ((b (list 'sin (list '* (car sp) 'pi)))) (if (= (modulo c 2) 0) b (list '* -1 b)))
            (list 'sin (list '* al 'pi))))))
; чётность sin/cos при отрицательном числовом множителе аргумента (упрощатель её не применяет)
(define (cb-par e)
  (cond ((not (pair? e)) e)
        ((and (member? (car e) '(sin cos)) (= (length e) 2))
         (let ((u (cb-par (cadr e))))
           (if (and (pair? u) (equal? (car u) '*) (number? (cadr u)) (< (cadr u) 0))
               (let ((nu (simplify (list '* -1 u)))) (if (equal? (car e) 'sin) (list '* -1 (list 'sin nu)) (list 'cos nu)))
               (list (car e) u))))
        (else (cons (car e) (map cb-par (cdr e))))))
(define (cb-real-part e)
  (ca-try (lambda () (simplify (cb-par (simplify (expand (list '* 1/2 (list '+ e (cb-conj e))))))))))
; x^α·log x·R = ∂/∂s [x^s R] при s = α
(define (cb-key-F* al R lg x)
  (if (not lg)
      (let ((F (cb-key-F al R x))) (and F (if (number? al) F (cb-real-part F))))
      (let* ((s 'cb_s) (F (cb-key-F s R x)) (Fr (and F (cb-real-part F))))
        (and Fr (ca-try (lambda () (simplify (subst (list s al) (diff s Fr)))))))))

; область сходимости символьных показателей: ((s . интервал) …) — для выбора значений при сверке
(define (cb-key-region f x)
  (let ((g (ca-try (lambda () (expand f)))))
    (if (not g)
        '()
        (let loop ((ts (ca-terms g)) (acc '()))
          (if (null? ts)
              acc
              (let* ((pt (ca-try (lambda () (cb-key-term (car ts) x))))
                     (sf (and pt (not (number? (car pt))) (cb-sym-form (car pt))))
                     (v0 (and sf (cb-order (cadr pt) x 0))) (d (and sf (cb-order (cadr pt) x 'inf))))
                (if (and sf v0 d)
                    (let* ((iv (list (* 1.0 (- (- -1 v0) (cdr sf))) #f (* 1.0 (- (- d 1) (cdr sf))) #f)) (old (assoc (car sf) acc)))
                      (loop (cdr ts) (cons (cons (car sf) (if old (cb-iv-meet (cdr old) iv) iv)) (if old (filter (lambda (p) (not (equal? (car p) (car sf)))) acc) acc))))
                    (loop (cdr ts) acc))))))))

; условия, найденные при вычислении, откладываются до успешной сверки (definite-by-residues)
(define cb-defer #f)
(define cb-deferred '())
(define (cb-note-cond c why)
  (if cb-defer (set! cb-deferred (cons (cons c why) cb-deferred)) (record-condition c why)))

; убывающая факториальная степень α(α−1)…(α−j+1)
(define (cb-ff al j) (if (= j 0) 1 (* (- al (- j 1)) (cb-ff al (- j 1)))))

(define (integral-keyhole f x)
  (let ((g (ca-try (lambda () (expand f)))))
    (if (not g)
        'unknown
        (let loop ((ts (ca-terms g)) (acc '()))
          (if (null? ts)
              (let ((v (ca-try (lambda () (simplify (expand (cons '+ acc)))))))
                (cond ((not v) 'unknown)
                      ((let ((c (ca-cnum v))) (and c (not (contains-sym? f '%i)) (> (abs-float (cdr c)) 1e-7))) 'unknown)
                      (else v)))
              (let ((pt (cb-key-term (car ts) x)))
                (if (not pt)
                    'unknown
                    (let ((v (cb-key-int (car pt) (cadr pt) (caddr pt) x)))
                      (if v (loop (cdr ts) (cons v acc)) 'unknown)))))))))

; ---------- численная сверка ----------

(define (cb-sample-env f ans x)
  (let loop ((vs (filter (lambda (s) (not (equal? s x))) (bc-vars (list '+ f ans)))) (k 0) (acc '()))
    (if (null? vs)
        acc
        (let ((sg (cb-sign (car vs))))
          (and sg (loop (cdr vs) (+ k 1) (cons (list (car vs) (* sg (+ 1.3 (* 0.37 k)))) acc)))))))

(define (cb-cval e)
  (cond ((ca-cnum e) (ca-cnum e))
        (else (let ((v (ca-try (lambda () (eval-num e))))) (and v (number? v) (cons (* 1.0 v) 0.0))))))

; максимальная |частота| в cos/sin (или 0.0 без них); #f — аргумент нелинеен
(define (cb-freq e x)
  (cond ((not (pair? e)) 0.0)
        ((and (member? (car e) '(cos sin)) (= (length e) 2))
         (let ((a (cb-linear-coef (cadr e) x)))
           (and a (let ((v (ca-try (lambda () (eval-num a))))) (and v (abs-float v))))))
        ((and (member? (car e) '(exp tan cot sec csc sinh cosh tanh coth)) (contains-sym? e x)) #f)
        (else (let loop ((l (cdr e)) (m 0.0))
                (if (null? l)
                    m
                    (let ((w (cb-freq (car l) x))) (and w (loop (cdr l) (max m w)))))))))

(define (cb-quad-0inf fx)
  (let ((h 0.08))
    (let loop ((k -1000) (s1 0.0) (s2 0.0))
      (if (> k 1000)
          (cons (* h s1) (* h s2))
          (let* ((t (* k h)) (xv (exp t)) (fv (fx xv)))
            (and fv
                 (let ((w (* fv xv)))
                   (loop (+ k 1) (if (<= (abs k) 500) (+ s1 w) s1) (+ s2 w)))))))))

(define (cb-quad-rinf fx)
  (let ((h 0.05))
    (let loop ((k -480) (s1 0.0) (s2 0.0))
      (if (> k 480)
          (cons (* h s1) (* h s2))
          (let* ((t (* k h)) (e1 (exp t)) (e2 (exp (- 0.0 t))) (xv (* 0.5 (- e1 e2))) (fv (fx xv)))
            (and fv
                 (let ((w (* fv 0.5 (+ e1 e2))))
                   (loop (+ k 1) (if (<= (abs k) 240) (+ s1 w) s1) (+ s2 w)))))))))

; cos/sin на ℝ: середины, L₁ = 40π/Ω и L₂ = L₁ + π/Ω; ответ — среднее двух усечений (подавляет ведущий хвост)
(define (cb-quad-osc fx om)
  (let* ((kk 50) (h (/ ca-pi (* om kk))) (n1 (* 40 kk)) (n2 (* 41 kk)))
    (let loop ((j (- 0 n2)) (s1 0.0) (s2 0.0))
      (if (>= j n2)
          (cons (* h s1) (* h s2))
          (let* ((xv (* (+ j 0.5) h)) (fv (fx xv)))
            (and fv (loop (+ j 1) (if (and (>= j (- 0 n1)) (< j n1)) (+ s1 fv) s1) (+ s2 fv))))))))

; CA.c: произведения и степени cos/sin — степень тригонометрического множителя (для частоты и окна)
(define (cb-trig-deg e)
  (cond ((not (pair? e)) 0)
        ((and (member? (car e) '(cos sin)) (= (length e) 2)) 1)
        ((equal? (car e) '*) (foldl + 0 (map cb-trig-deg (cdr e))))
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (caddr e)) (> (caddr e) 0)) (* (caddr e) (cb-trig-deg (cadr e))))
        (else (foldl max 0 (map cb-trig-deg (cdr e))))))

; окна Гаусса L, 2L, 4L (e^{−(x/L)²}) и экстраполяция Ричардсона 1/3·I(L) − 2·I(2L) + 8/3·I(4L): убирает хвосты 1/L и 1/L²
; неколеблющейся части (sin²x/x² → ½/x²), колеблющиеся хвосты гасит гладкое окно; ответ (v . оценка погрешности)
(define (cb-quad-win fx om)
  (let* ((L (if (< om 1.0) (/ 10.0 om) 10.0)) (h (/ 0.25 (max om 1.0))) (n (ceiling (/ (* 20.0 L) h))))
    (let loop ((j (- 0 n)) (s1 0.0) (s2 0.0) (s3 0.0))
      (if (>= j n)
          (let* ((i1 (* h s1)) (i2 (* h s2)) (i3 (* h s3))
                 (v (+ (* 1/3 i1) (* -2 i2) (* 8/3 i3))) (v2 (- (* 2 i3) i2)))
            (cons v (abs-float (- v v2))))
          (let* ((xv (* (+ j 0.5) h)) (fv (fx xv)))
            (and fv (let ((u (/ xv L)))
                      (loop (+ j 1)
                            (+ s1 (* fv (exp (- 0.0 (* u u)))))
                            (+ s2 (* fv (exp (- 0.0 (* 0.25 u u)))))
                            (+ s3 (* fv (exp (- 0.0 (* 0.0625 u u)))))))))))))

; один набор значений параметров: (v est использовать-est? базовый допуск) | #f
(define (cb-check-quad fx lo om deg)
  (let* ((osc (> om 0.0))
         (fold (cond ((equal? lo 0) (lambda (v) (fx (abs-float v))))           ; ∫₀^∞ f = ½∫_ℝ f(|x|)
                     ((equal? lo 0.5) (lambda (v) (fx (- 0.0 (abs-float v)))))   ; ∫_{−∞}^0 f = ½∫_ℝ f(−|x|)
                     (else fx))))
    (cond ((and osc (> deg 1))
           (let ((w (cb-quad-win (if (equal? lo '-inf) fx fold) (* om deg))))
             (and w (list (if (equal? lo '-inf) (car w) (* 0.5 (car w))) (if (equal? lo '-inf) (cdr w) (* 0.5 (cdr w))) #t 1e-3))))
          (osc
           (let ((w (cb-quad-osc (if (equal? lo '-inf) fx fold) om)))
             (and w (let ((k (if (equal? lo '-inf) 1.0 0.5)))
                      (list (* k 0.5 (+ (car w) (cdr w))) (abs-float (- (car w) (cdr w))) #f 1e-3)))))
          ((equal? lo 0) (let ((q (cb-quad-0inf fx))) (and q (list (cdr q) (abs-float (- (car q) (cdr q))) #t 1e-5))))
          ((equal? lo 0.5) (let ((q (cb-quad-0inf (lambda (v) (fx (- 0.0 v)))))) (and q (list (cdr q) (abs-float (- (car q) (cdr q))) #t 1e-5))))
          (else (let ((q (cb-quad-rinf fx))) (and q (list (cdr q) (abs-float (- (car q) (cdr q))) #t 1e-5)))))))

(define (cb-verdict av q)
  (let* ((v (car q)) (est (cadr q)) (use (caddr q))
         (diff (ca-cabs (ca-csub av (cons v 0.0)))) (tol (* (cadddr* q) (+ 1.0 (abs-float v)))))
    (cond ((and (<= diff tol) (or (not use) (<= est (* 10 tol)))) 'numeric)
          ((and (> diff (* 10 tol)) (or (not use) (<= est (* 1e-3 (+ 1.0 (abs-float v)))))) 'mismatch)
          (else 'unknown))))
(define (cadddr* l) (nth l 3))

; сверка при одном наборе значений параметров; lo = −inf и hi = 0 кодируем как lo = 0.5 (отражение)
(define (cb-check-env f x lo hi ans env)
  (let* ((f2 (ca-try (lambda () (subst env f)))) (a2 (ca-try (lambda () (subst env ans))))
         (av (and a2 (cb-cval a2)))
         (om (and f2 (cb-freq f2 x)))
         (fx (lambda (v) (ca-try (lambda () (let ((r (eval-num (subst (list x v) f2)))) (and (number? r) r)))))))
    (if (or (not f2) (not av) (not om))
        'unknown
        (let ((q (cb-check-quad fx lo om (if (> om 0.0) (cb-trig-deg f2) 1))))
          (if q (cb-verdict av q) 'unknown)))))

; несколько наборов значений параметров из деклараций (и области сходимости x^α); любой mismatch — mismatch
(define (cb-check-all f x lo hi ans)
  (let* ((syms (filter (lambda (s) (not (equal? s x))) (bc-vars (list '+ f ans))))
         (old cb-assumed)
         (lo2 (if (and (equal? lo '-inf) (equal? hi 0)) 0.5 lo)))
    (set! cb-assumed (append (cb-key-region f x) cb-assumed))
    (unwind-protect
      (let ((envs (cb-envs syms (if (contains-sym? f 'cos) 2 (if (contains-sym? f 'sin) 2 3)))))
        (if (not envs)
            'unknown
            (let ((vs (map (lambda (env) (cb-check-env f x lo2 hi ans env)) envs)))
              (cond ((member? 'mismatch vs) 'mismatch)
                    ((every? (lambda (v) (equal? v 'numeric)) vs) 'numeric)
                    (else 'unknown)))))
      (set! cb-assumed old))))

(define (integral-residues-check f x lo hi ans)
  (cond ((cb-period-kind lo hi) (cb-check-period f x lo hi ans))
        ((not (or (and (equal? lo '-inf) (equal? hi 'inf)) (and (equal? lo 0) (equal? hi 'inf)) (and (equal? lo '-inf) (equal? hi 0))))
         'unknown)
        ((contains-sym? f '%i) 'unknown)
        (else (cb-check-all f x lo hi ans))))

; ---------- запасной путь integrate ----------

; чётность по разбору: cos·R — как R, sin·R — наоборот, без экспоненты e^{iax}; все слагаемые чётны
(define (cb-parity R x)
  (let* ((Rm (ca-try (lambda () (subst (list x (list '* -1 x)) R))))
         (zero? (lambda (e) (equal? (ca-try (lambda () (simplify (expand (together e))))) 0))))
    (cond ((not Rm) #f)
          ((zero? (list '+ Rm (list '* -1 R))) 1)
          ((zero? (list '+ Rm R)) -1)
          (else #f))))
(define (cb-even? f x)
  (let ((parts (cb-parts f x)))
    (and parts (not (null? parts))
         (every? (lambda (pt)
                   (let ((pr (cb-parity (car pt) x)))
                     (and pr (cond ((equal? (cadr pt) 'cos) (= pr 1))
                                   ((equal? (cadr pt) 'sin) (= pr -1))
                                   ((equal? (cadr pt) 'none) (= pr 1))
                                   (else #f)))))
                 parts))))

(define (cb-half f x)
  (let ((v (integral-keyhole f x)))
    (if (not (equal? v 'unknown))
        v
        (let ((even (cb-even? f x)))
          (if even
              (let ((w (integral-fourier f x))) (if (equal? w 'unknown) 'unknown (simplify (list '* 1/2 w))))
              'unknown)))))

; CA.c: (−inf, 0) — подстановка x → −x: ∫_{−∞}^0 f(x) dx = ∫_0^∞ f(−x) dx; только R·cos/sin (без x^α и log: на x < 0 ветвь не вещественна)
(define (cb-neg-half f x)
  (if (not (cb-parts f x))
      'unknown
      (let ((g (ca-try (lambda () (simplify (subst (list x (list '* -1 x)) f))))))
        (if g (cb-half g x) 'unknown))))

; ---------- CA.c: тригонометрические интегралы по периоду ----------
; ∫_0^{2π} R(cos θ, sin θ) dθ (и [−π, π]; [0, π] — при чётности по θ, половина): z = e^{iθ}, cos kθ = (z^k + z^−k)/2, sin kθ = (z^k − z^−k)/(2i),
; dθ = dz/(iz): I = 2π Σ_{|p|<1} Res_{z=p} F(z)/z. Полюс на окружности — unknown. Параметры: расположение полюсов относительно окружности должно
; быть одним и тем же при всех сочетаниях значений внутри деклараций (кандидаты — cb-env-grid); вычет в символьном полюсе — N(p)/D'(p) (простой полюс).
(define (cb-period-kind lo hi)
  (let ((l (ca-try (lambda () (simplify lo)))) (h (ca-try (lambda () (simplify hi)))))
    (cond ((not (and l h)) #f)
          ((and (equal? l 0) (equal? h '(* 2 pi))) 'full)
          ((and (equal? l '(* -1 pi)) (equal? h 'pi)) 'full)
          ((and (equal? l 0) (equal? h 'pi)) 'half)
          (else #f))))

(define (cb-trig-z e x z)    ; e(x) → F(z); #f — не разобрано
  (cond ((not (contains-sym? e x)) e)
        ((not (pair? e)) #f)
        ((and (member? (car e) '(cos sin)) (= (length e) 2))
         (let ((k (cb-linear-coef (cadr e) x)))
           (and k (integer? k) (not (= k 0))
                (if (equal? (car e) 'cos)
                    (list '/ (list '+ (list '^ z k) (list '^ z (- 0 k))) 2)
                    (list '/ (list '+ (list '^ z k) (list '* -1 (list '^ z (- 0 k)))) (list '* 2 '%i))))))
        ((and (member? (car e) '(tan cot sec csc)) (= (length e) 2))
         (let ((u (cadr e)))
           (cb-trig-z (cond ((equal? (car e) 'tan) (list '/ (list 'sin u) (list 'cos u)))
                            ((equal? (car e) 'cot) (list '/ (list 'cos u) (list 'sin u)))
                            ((equal? (car e) 'sec) (list '/ 1 (list 'cos u)))
                            (else (list '/ 1 (list 'sin u))))
                      x z)))
        ((member? (car e) '(+ * - /))
         (let ((args (map (lambda (a) (cb-trig-z a x z)) (cdr e)))) (and (not (member? #f args)) (cons (car e) args))))
        ((and (equal? (car e) '^) (= (length e) 3) (not (contains-sym? (caddr e) x)))
         (let ((b (cb-trig-z (cadr e) x z))) (and b (list '^ b (caddr e)))))
        (else #f)))

; числитель и знаменатель после together: ((N D)) | #f
(define (cb-num-den g)
  (let ((t (ca-try (lambda () (together g)))))
    (and t
         (let loop ((fs (ca-factors t)) (n '()) (d '()))
           (if (null? fs)
               (list (simplify (cons '* (reverse n))) (simplify (cons '* (reverse d))))
               (let ((fc (car fs)))
                 (if (and (pair? fc) (equal? (car fc) '^) (= (length fc) 3) (integer? (caddr fc)) (< (caddr fc) 0))
                     (loop (cdr fs) n (cons (list '^ (cadr fc) (- 0 (caddr fc))) d))
                     (loop (cdr fs) (cons fc n) d))))))))

; значение |p| при наборе параметров env: число | #f
(define (cb-pole-abs2 p env)
  (let ((c (cb-cval-env (subst env p))))
    (and c (+ (* (car c) (car c)) (* (cdr c) (cdr c))))))
; комплексное значение выражения без символов: ca-cnum, иначе eval-num (корни от параметров); sqrt отрицательного — #f
(define (cb-cval-env e)
  (or (ca-try (lambda () (ca-cnum e)))
      (let ((v (ca-try (lambda () (eval-num e))))) (and v (number? v) (cons (* 1.0 v) 0.0)))))

; вычеты внутри единичного круга: сумма | unknown
(define (cb-inside-sum G z)
  (let* ((T (ca-try (lambda () (together G)))) (nd (and T (cb-num-den T)))
         (poles (and T (ca-try (lambda () (singularities T z))))))
    (if (or (not poles) (equal? poles 'unknown))
        'unknown
        (let* ((syms (filter (lambda (s) (not (equal? s z))) (bc-vars G)))
               (envs (cb-env-grid syms)))
          (if (not envs)
              'unknown
              (let* ((pat (lambda (env)
                            (map (lambda (p) (let ((a (cb-pole-abs2 p env)))
                                               (cond ((not a) 'bad) ((< (abs-float (- a 1.0)) 1e-7) 'bad) ((< a 1.0) 'in) (else 'out))))
                                 poles)))
                     (pats (map pat envs)))
                (cond ((member? 'bad (car pats)) 'unknown)
                      ((not (every? (lambda (q) (equal? q (car pats))) pats)) 'unknown)
                      (else
                       (let loop ((ps poles) (st (car pats)) (acc '()))
                         (cond ((null? ps) (ca-clean (cons '+ acc)))
                               ((equal? (car st) 'out) (loop (cdr ps) (cdr st) acc))
                               (else
                                (let ((r (cb-pole-res T z (car ps) nd envs)))
                                  (if r (loop (cdr ps) (cdr st) (cons r acc)) 'unknown)))))))))))))

(define (cb-pole-res T z p nd envs)
  (let ((r (ca-try (lambda () (residue T z p)))))
    (if (and r (not (equal? r 'unknown)))
        r
        (and nd
             (let* ((N (car nd)) (D (cadr nd)) (D1 (diff z D)))
               (and (every? (lambda (env)
                              (let ((c (cb-cval-env (subst env (subst (list z p) D1)))))
                                (and c (> (ca-cabs c) 1e-6))))
                            envs)
                    (ca-try (lambda () (simplify (subst (list z p) (list '/ N D1)))))))))))

; √(4A − 4B) → 2√(A − B): целочисленное содержание подкоренного, если оно полный квадрат (упрощатель его не выносит)
(define (cb-int-sqrt n) (let loop ((k 1)) (cond ((> (* k k) n) #f) ((= (* k k) n) k) (else (loop (+ k 1))))))
(define (cb-term-coef tm) (if (and (pair? tm) (equal? (car tm) '*) (number? (cadr tm))) (cadr tm) (if (number? tm) tm 1)))
(define (cb-tidy e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2))
         (let* ((E (cb-tidy (cadr e))) (cs (map cb-term-coef (ca-terms E))))
           (if (every? integer? cs)
               (let* ((g (foldl gcd 0 cs)) (k (and (> g 1) (cb-int-sqrt g))))
                 (if k (list '* k (list 'sqrt (simplify (expand (list '* (/ 1 g) E))))) (list 'sqrt E)))
               (list 'sqrt E))))
        (else (cons (car e) (map cb-tidy (cdr e))))))

(define (integral-trig f x lo hi)
  (let ((kind (cb-period-kind lo hi)) (z 'cb_w))
    (if (not kind)
        'unknown
        (let ((F (ca-try (lambda () (cb-trig-z f x z)))))
          (if (not F)
              'unknown
              (let* ((even (or (equal? kind 'full)
                               (equal? 0 (ca-try (lambda () (simplify (expand (together (list '+ F (list '* -1 (subst (list z (list '^ z -1)) F)))))))))))
                     (s (if even (cb-inside-sum (list '/ F z) z) 'unknown)))
                (if (equal? s 'unknown)
                    'unknown
                    (let ((v (ca-try (lambda () (simplify (cb-tidy (simplify (expand (list '* 2 'pi s)))))))))
                      (cond ((not v) 'unknown)
                            ((let ((c (ca-cnum v))) (and c (> (abs-float (cdr c)) 1e-7))) 'unknown)
                            ((equal? kind 'half) (simplify (list '* 1/2 v)))
                            (else v))))))))))

; сверка по периоду: середины, N = 600 и 1200 узлов (для аналитического периодического подынтегрального — спектральная точность)
(define (cb-check-period-env f x lo hi ans env)
  (let* ((f2 (ca-try (lambda () (subst env f)))) (a2 (ca-try (lambda () (subst env ans))))
         (av (and a2 (cb-cval a2))) (l (ca-try (lambda () (eval-num lo)))) (h (ca-try (lambda () (eval-num hi))))
         (fx (lambda (v) (ca-try (lambda () (let ((r (eval-num (subst (list x v) f2)))) (and (number? r) r)))))))
    (if (or (not f2) (not av) (not (number? l)) (not (number? h)))
        'unknown
        (let ((quad (lambda (n)
                      (let ((dx (/ (- h l) n)))
                        (let loop ((k 0) (s 0.0))
                          (if (>= k n)
                              (* dx s)
                              (let ((fv (fx (+ l (* (+ k 0.5) dx))))) (and fv (loop (+ k 1) (+ s fv))))))))))
          (let ((a (quad 600)) (b (quad 1200)))
            (if (not (and a b))
                'unknown
                (cb-verdict av (list b (abs-float (- a b)) #t 1e-7))))))))

(define (cb-check-period f x lo hi ans)
  (let* ((syms (filter (lambda (s) (not (equal? s x))) (bc-vars (list '+ f ans)))) (envs (cb-envs syms 3)))
    (if (or (not envs) (contains-sym? f '%i))
        'unknown
        (let ((vs (map (lambda (env) (cb-check-period-env f x lo hi ans env)) envs)))
          (cond ((member? 'mismatch vs) 'mismatch)
                ((every? (lambda (v) (equal? v 'numeric)) vs) 'numeric)
                (else 'unknown))))))

(define (cb-run-deferred thunk)
  (let ((old-d cb-defer))
    (set! cb-defer #t)
    (set! cb-deferred '())
    (unwind-protect (thunk) (set! cb-defer old-d))))

(define (definite-by-residues f x lo hi)
  (let* ((v (cb-run-deferred
             (lambda ()
               (cond ((and (equal? lo '-inf) (equal? hi 'inf)) (integral-fourier f x))
                     ((and (equal? lo 0) (equal? hi 'inf)) (cb-half f x))
                     ((and (equal? lo '-inf) (equal? hi 0)) (cb-neg-half f x))
                     ((cb-period-kind lo hi) (integral-trig f x lo hi))
                     (else 'unknown)))))
         (conds cb-deferred))
    (if (equal? v 'unknown)
        'unknown
        (if (equal? (integral-residues-check f x lo hi v) 'numeric)
            (begin (for-each (lambda (c) (record-condition (car c) (cdr c))) (reverse conds)) v)
            'unknown))))
