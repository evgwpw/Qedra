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
          residue-check contour-integral-check integral-by-residues branch-check))

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
