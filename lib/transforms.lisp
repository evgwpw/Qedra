; transforms.lisp — Z-преобразование и преобразование Фурье (шаг TR.3)
; Z: односторонее Z[a_n](z) = Σ_{n≥0} a_n z^{-n}; δ_n — (kdelta n), ступенька в дискретном смысле θ(0) = 1.
; Фурье: F(ω) = ∫ f(t) e^{−iωt} dt, обратное f(t) = (1/2π) ∫ F(ω) e^{iωt} dω; θ, δ — heaviside, dirac из модуля laplace;
; |t| — (abs t), sgn t — (sign t). Внутренние имена: tr- (общие), tz- (Z), tf- (Фурье).
(module transforms
  (export ztransform inverse-ztransform ztransform-check ztransform-initial ztransform-final kdelta
          zsolve zsolve-check fourier inverse-fourier fourier-check))

; ---------- общее ----------

(define (tr-free? e x) (not (contains-sym? e x)))
(define (tr-head? e h) (and (pair? e) (equal? (car e) h)))
(define (tr-factors e) (if (tr-head? e '*) (cdr e) (list e)))
(define (tr-try thunk) (try (thunk) (lambda (e) #f)))
(define (tr-terms e) (let ((v (expand e))) (if (tr-head? v '+) (cdr v) (list v))))
(define (tr-prod l) (if (null? l) 1 (simplify (apply * l))))
(define (tr-sum l) (if (null? l) 0 (simplify (apply + l))))
(define (tr-int? x) (and (number? x) (equal? (type-of x) 'integer)))

; u = a·x + b (a, b без x) → (a . b), иначе #f
(define (tr-lin u x)
  (let ((v (expand u)))
    (if (polynomial? v x)
        (let ((cs (coefficients v x)))
          (cond ((null? cs) (cons 0 0))
                ((null? (cdr cs)) (cons 0 (car cs)))
                ((null? (cddr cs)) (cons (cadr cs) (car cs)))
                (else #f)))
        #f)))

(define (tr-has-i? e) (contains-sym? e '%i))
(define (tr-numeric? v) (or (number? v) (and (pair? v) (tr-has-i? v))))

; (re . im) численного значения (eval-num) или #f
(define (tr-cplx v)
  (cond ((number? v) (cons v 0.0))
        ((equal? v '%i) (cons 0.0 1.0))
        ((and (tr-head? v '*) (= (length v) 3) (number? (cadr v)) (equal? (caddr v) '%i)) (cons 0.0 (cadr v)))
        ((tr-head? v '+)
         (let loop ((l (cdr v)) (re 0.0) (im 0.0))
           (if (null? l)
               (cons re im)
               (let ((p (tr-cplx (car l))))
                 (if p (loop (cdr l) (+ re (car p)) (+ im (cdr p))) #f)))))
        (else #f)))

(define (tr-num-eval e)
  (let ((v (tr-try (lambda () (eval-num e))))) (and v (tr-cplx v))))

(define (tr-close? a b)
  (and (<= (abs (- (car a) (car b))) (* 0.001 (+ 1.0 (abs (car b)))))
       (<= (abs (- (cdr a) (cdr b))) (* 0.001 (+ 1.0 (abs (cdr b)))))))

; равенство выражений: simplify(together(a − b)) = 0 (допускает %i)
(define (tr-equal? a b)
  (let ((d (tr-try (lambda () (simplify (expand (numer (together (- a b)))))))))
    (and d (equal? d 0))))

; ступеньки: (kdelta число), (heaviside число) → число (в дискретном смысле θ(0) = 1)
(define (tr-fix e)
  (cond ((not (pair? e)) e)
        ((and (tr-head? e 'kdelta) (number? (cadr e))) (if (= (cadr e) 0) 1 0))
        ((and (tr-head? e 'heaviside) (number? (cadr e))) (if (>= (cadr e) 0) 1 0))
        (else (cons (car e) (map tr-fix (cdr e))))))

; δ_n: (kdelta u) → 1 при u = 0, 0 для другого числа, иначе данные
(define (kdelta u)
  (let ((v (simplify u)))
    (cond ((number? v) (if (= v 0) 1 0))
          (else (list 'kdelta v)))))

(define (tr-known-head? h)
  (member? h '(+ * ^ exp sin cos sinh cosh tan atan asin acos log sqrt abs sign binomial heaviside dirac kdelta sum diff
               fourier fourier-convolve ztransform factorial gamma)))

; неизвестная функция (h arg) с одним аргументом
(define (tr-unknown-call? e)
  (and (pair? e) (symbol? (car e)) (not (tr-known-head? (car e))) (= (length e) 2)))


; ===================================================================================
; Z-преобразование
; ===================================================================================

; условие сходимости |z| > R
(define (tz-bases e n)
  (cond ((not (pair? e)) '())
        ((and (tr-head? e '^) (tr-free? (cadr e) n) (tr-lin (caddr e) n) (not (equal? (car (tr-lin (caddr e) n)) 0)))
         (list (simplify (^ (cadr e) (car (tr-lin (caddr e) n))))))
        ((and (tr-head? e 'exp) (tr-lin (cadr e) n) (not (equal? (car (tr-lin (cadr e) n)) 0)))
         (list (simplify (list 'exp (car (tr-lin (cadr e) n))))))
        (else (append-map (lambda (x) (tz-bases x n)) (cdr e)))))

(define (tz-abs b) (if (and (number? b) (< b 0)) (- b) (if (number? b) b (list 'abs b))))

(define (tz-record-roc a n z)
  (let* ((bs (tz-bases a n))
         (nums (filter number? (map tz-abs bs)))
         (syms (filter (lambda (b) (not (number? b))) (map tz-abs bs)))
         (r (foldl max 0 nums)))
    (if (symbol? z)
        (begin
          (record-condition (list '> (list 'abs z) r) "Z-преобразование сходится при |z| > радиуса сходимости")
          (for-each (lambda (b) (record-condition (list '> (list 'abs z) b) "Z-преобразование сходится при |z| > |основание|")) syms)
          #t)
        #f)))

(define (tz-Z a n z)
  (let ((g (simplify a)))
    (cond ((tr-free? g n) (if (equal? g 0) 0 (simplify (/ (* g z) (- z 1)))))
          ((tr-head? g '+) (tz-sum (cdr g) n z))
          (else (let ((e (expand g)))
                  (if (tr-head? e '+) (tz-sum (cdr e) n z) (tz-term g n z)))))))

(define (tz-sum ts n z)
  (let loop ((l ts) (acc '()))
    (if (null? l)
        (simplify (apply + acc))
        (let ((r (tz-Z (car l) n z)))
          (if r (loop (cdr l) (cons r acc)) #f)))))

; θ_z F = −z dF/dz, k раз
(define (tz-theta F k z)
  (if (= k 0)
      F
      (tz-theta (simplify (together (* -1 z (diff z F)))) (- k 1) z)))

(define (tz-term f n z)
  (let ((fs (tr-factors f)))
    (cond ((tr-find (lambda (x) (or (tr-head? x 'kdelta) (tr-head? x 'heaviside))) fs)
           (tz-step f fs n z))
          ((and (tr-head? f 'sum) (= (length f) 5)) (tz-conv f n z))
          ((tr-find (lambda (x) (tr-unknown-call? x)) fs) (tz-unknown fs n z))
          (else (or (tz-monomial fs n z) (tz-fallback f n z))))))

(define (tr-find p l)
  (cond ((null? l) #f) ((p (car l)) (car l)) (else (tr-find p (cdr l)))))

(define (tr-remove x l)
  (cond ((null? l) '())
        ((equal? x (car l)) (cdr l))
        (else (cons (car l) (tr-remove x (cdr l))))))

; множитель δ_{n−k} или θ(n−k): сдвиг
(define (tz-step f fs n z)
  (let* ((st (tr-find (lambda (x) (or (tr-head? x 'kdelta) (tr-head? x 'heaviside))) fs))
         (rest (tr-prod (tr-remove st fs)))
         (ab (tr-lin (cadr st) n)))
    (cond ((not (and ab (equal? (car ab) 1) (tr-int? (cdr ab)))) #f)
          (else
           (let ((k (- (cdr ab))))
             (if (tr-head? st 'kdelta)
                 (if (< k 0)
                     0
                     (let ((g (simplify (tr-fix (subst (list n k) rest)))))
                       (simplify (* g (^ z (- k))))))
                 ; θ(n − k): n ≥ k → 1 (k < 0 — всегда)
                 (if (<= k 0)
                     (tz-Z rest n z)
                     (let ((r (tz-Z (subst (list n (+ n k)) rest) n z)))
                       (and r (simplify (* (^ z (- k)) r)))))))))))

; свёртка (sum A(k)·B(n−k) k 0 n)
(define (tz-conv f n z)
  (let* ((body (cadr f)) (k (caddr f)) (lo (nth f 3)) (hi (nth f 4)))
    (if (not (and (equal? lo 0) (equal? hi n)))
        #f
        (let* ((fs (tr-factors (simplify body)))
               (ap (filter (lambda (x) (tr-free? x n)) fs))
               (bp (filter (lambda (x) (contains-sym? x n)) fs))
               (aN (tr-prod (map (lambda (x) (subst (list k n) x)) ap)))
               (bk (tr-prod bp))
               (bN (simplify (subst (list k 0) bk)))
               (ok (tr-equal? (subst (list (list k (list '+ k 1)) (list n (list '+ n 1))) bk) bk)))
          (and (not (null? bp)) ok
               (let ((A (tz-Z aN n z)) (B (tz-Z bN n z)))
                 (and A B (simplify (* A B)))))))))

; множители: константа, n^k, b^n, exp(cn), одна тригонометрия или биномиальный коэффициент
; → (c k b trig bin) или #f
(define (tz-parse fs n)
  (let loop ((l fs) (c 1) (k 0) (b 1) (trig #f) (bin #f))
    (if (null? l)
        (list c k b trig bin)
        (let ((x (car l)))
          (cond ((tr-free? x n) (loop (cdr l) (* c x) k b trig bin))
                ((equal? x n) (loop (cdr l) c (+ k 1) b trig bin))
                ((and (tr-head? x '^) (equal? (cadr x) n) (tr-int? (caddr x)) (> (caddr x) 0))
                 (loop (cdr l) c (+ k (caddr x)) b trig bin))
                ((and (tr-head? x '^) (tr-free? (cadr x) n) (tr-lin (caddr x) n))
                 (let ((ab (tr-lin (caddr x) n)))
                   (loop (cdr l) (* c (^ (cadr x) (cdr ab))) k (* b (^ (cadr x) (car ab))) trig bin)))
                ((and (tr-head? x 'exp) (tr-lin (cadr x) n))
                 (let ((ab (tr-lin (cadr x) n)))
                   (loop (cdr l) (* c (list 'exp (cdr ab))) k (* b (list 'exp (car ab))) trig bin)))
                ((and (or (tr-head? x 'sin) (tr-head? x 'cos)) (not trig) (not bin) (tr-lin (cadr x) n)
                      (equal? (cdr (tr-lin (cadr x) n)) 0))
                 (loop (cdr l) c k b (list (car x) (car (tr-lin (cadr x) n))) bin))
                ((and (tr-head? x 'binomial) (equal? (cadr x) n) (tr-int? (caddr x)) (>= (caddr x) 0) (not trig) (not bin))
                 (loop (cdr l) c k b trig (caddr x)))
                (else #f))))))

(define (tz-monomial fs n z)
  (let ((p (tz-parse fs n)))
    (if (not p)
        #f
        (let* ((c (car p)) (k (cadr p)) (b (simplify (caddr p))) (trig (nth p 3)) (bin (nth p 4))
               (base (cond (trig
                            (let ((w (cadr trig)) (den (list '+ (list '^ z 2) (list '* -2 z (list 'cos (cadr trig))) 1)))
                              (if (equal? (car trig) 'sin)
                                  (/ (* z (list 'sin w)) den)
                                  (/ (* z (- z (list 'cos w))) den))))
                           (bin (/ z (^ (- z 1) (+ bin 1))))
                           (else (/ z (- z 1)))))
               (h (tz-theta (simplify (together base)) k z))
               (hb (if (equal? b 1) h (simplify (subst (list z (/ z b)) h)))))
          (simplify (together (* c hb)))))))

; неизвестная последовательность (h (n + k)): z^k A − Σ_{j<k} a_j z^{k−j}
(define (tz-unknown fs n z)
  (let* ((u (tr-find tr-unknown-call? fs))
         (rest (tr-remove u fs))
         (ab (tr-lin (cadr u) n)))
    (if (and ab (equal? (car ab) 1) (tr-int? (cdr ab)) (>= (cdr ab) 0) (every? (lambda (x) (tr-free? x n)) rest))
        (let* ((k (cdr ab)) (h (car u))
               (A (list 'ztransform (list h n) n z))
               (r (- (* (^ z k) A)
                     (apply + (map (lambda (j) (* (list h j) (^ z (- k j)))) (range k))))))
          (simplify (* (tr-prod rest) r)))
        #f)))

; запасной путь: сумма ряда через sum-symbolic и предел
(define (tz-fallback f n z)
  (let* ((N 'tz-N)
         (s (tr-try (lambda () (sum-symbolic (* f (^ z (* -1 n))) n 0 N)))))
    (if (and s (not (contains-sym? s 'sum)))
        (let ((l (tr-try (lambda () (limit s N 'inf)))))
          (if (and l (not (contains-sym? l 'limit)) (not (contains-sym? l N)) (not (equal? l 'unknown))
                   (not (contains-sym? l 'inf)))
              (simplify l)
              #f))
        #f)))

; ---------- шаги (ST.3в-1) ----------
(define (tf-mp e) (try (math-print e) (lambda (err) (to-string e))))

; правило Z-преобразования по форме последовательности
(define (tz-rule-of a n)
  (let ((g (simplify a)))
    (cond ((tr-head? g 'sum) "свёртка: Z[A ⋆ B] = A(z)·B(z)")
          ((tr-find (lambda (x) (or (tr-head? x 'kdelta) (tr-head? x 'heaviside))) (tr-factors g))
           "сдвиг: δ_{n−k} или θ(n−k) → z^{−k}·A(z)")
          ((tr-head? g '+) "линейность: Z[f + g] = Z[f] + Z[g]")
          (else
           (let ((p (tz-parse (tr-factors g) n)))
             (cond ((not p) "табличное значение")
                   ((> (cadr p) 0) "умножение на n^k: θ_z^k A(z), θ_z = −z d/dz")
                   ((not (equal? (simplify (caddr p)) 1)) "масштаб b^n: A(z/b)")
                   ((nth p 3) "табличное значение тригонометрии")
                   ((nth p 4) "табличное значение биномиального коэффициента")
                   (else "табличное значение z/(z − 1)")))))))

(define (ztransform a n z)
  (let ((r (with-step ('tz-forward "Z-преобразование" (list 'ztransform a n z))
              (tz-Z a n z))))
    (if r
        (begin (tz-record-roc a n z)
               (if (step-log-enabled?)
                   (record-step 'tz-rule "Применённое правило" (tz-rule-of a n) a r 'main))
               r)
        (list 'ztransform a n z))))

; ---------- обратное Z-преобразование ----------

(define (tz-degree p z) (- (length (coefficients p z)) 1))

(define (tz-inv F z n)
  (let ((g (simplify (together (simplify F)))))
    (cond ((tr-free? g z) (if (equal? g 0) 0 (simplify (* g (list 'kdelta n)))))
          ((and (polynomial? (numer g) z) (polynomial? (denom g) z)
                (<= (tz-degree (expand (numer g)) z) (tz-degree (expand (denom g)) z)))
           (tz-inv-rat g z n))
          ((tr-head? g '+) (tz-inv-sum (cdr g) z n))
          (else #f))))

(define (tz-inv-sum ts z n)
  (let loop ((l ts) (acc '()))
    (if (null? l)
        (simplify (apply + acc))
        (let ((r (tz-inv (car l) z n)))
          (if r (loop (cdr l) (cons r acc)) #f)))))

(define (tz-inv-rat g z n)
  (let* ((a (simplify (apart (/ g z) z)))
         (ts (if (tr-head? a '+) (cdr a) (list a))))
    (if (step-log-enabled?)
        (record-step 'tz-inv-partial "Разложение F(z)/z на простейшие дроби"
                     (string-append "знаменатель " (tf-mp (denom g)) "; полюса: "
                                    (tf-mp (try (solve (list '= (denom g) 0) z)
                                                (lambda (err) 'unknown)))
                                    "; коэффициенты — слагаемые разложения")
                     g a 'main))
    (let loop ((l ts) (acc '()))
      (if (null? l)
          (simplify (expand (apply + acc)))
          (let ((r (tz-inv-term (car l) z n)))
            (if (and r (step-log-enabled?))
                (record-step 'tz-inv-term "Обратное Z-преобразование слагаемого"
                             "табличное значение / вычет в полюсе" (car l) r 'detail))
            (if r (loop (cdr l) (cons r acc)) #f))))))

; C(n, m) как многочлен по n
(define (tz-binom-poly n m)
  (if (= m 0)
      1
      (/ (apply * (map (lambda (j) (+ n (- j))) (range m))) (factorial m))))

; угол θ с cos θ = c: рациональное кратное π, если найдётся, иначе acos
(define (tz-find-angle cv)
  (let loop ((j 1) (k 0))
    (cond ((> j 12) #f)
          ((> k j) (loop (+ j 1) 0))
          ((< (abs (- (eval-num (list 'cos (list '* (/ k j) 'pi))) cv)) 0.000000000001) (/ k j))
          (else (loop j (+ k 1))))))

(define (tz-angle-of c)
  (let* ((v (tr-try (lambda () (eval-num c))))
         (q (and (number? v) (tz-find-angle v))))
    (if q (simplify (* q 'pi)) (list 'acos c))))

(define (tz-inv-term term z n)
  (let ((nu (numer term)) (d (denom term)))
    (if (tr-free? d z)
        #f
        (let ((fl (factor-list d)))
          (if (not (= (length fl) 2))
              #f
              (let* ((c (car fl)) (q (car (cadr fl))) (m (cadr (cadr fl))) (dg (tz-degree q z))
                     (qc (coefficients q z)))
                (cond ((= dg 1)
                       (if (not (tr-free? nu z))
                           #f
                           (let* ((q0 (car qc)) (q1 (cadr qc)) (rho (simplify (/ (- q0) q1)))
                                  (K (simplify (/ nu (* c (^ q1 m))))))
                             (if (equal? rho 0)
                                 (simplify (* K (list 'kdelta (simplify (+ n (- (- m 1)))))))
                                 (simplify (* K (tz-binom-poly n (- m 1)) (^ rho (- (- m 1))) (^ rho n)))))))
                      ((and (= dg 2) (= m 1) (<= (tz-degree nu z) 1))
                       (tz-inv-quad nu c qc z n))
                      (else #f))))))))

; (n1 z + n0)/(c (q2 z² + q1 z + q0)) в G = F/z; F-часть z(n1 z + n0)/…
(define (tz-inv-quad nu c qc z n)
  (let* ((q2 (caddr qc)) (p (/ (cadr qc) q2)) (r0 (/ (car qc) q2))
         (nc (coefficients nu z))
         (n0 (if (null? nc) 0 (car nc)))
         (n1 (if (or (null? nc) (null? (cdr nc))) 0 (cadr nc)))
         (K0 (/ 1 (* c q2)))
         (D (- (* p p) (* 4 r0))))
    (if (< D 0)
        (let* ((r (simplify (^ r0 1/2)))
               (cs (simplify (/ (- p) (* 2 r))))
               (sn (simplify (/ (^ (- D) 1/2) (* 2 r))))
               (th (tz-angle-of cs))
               (a (simplify (* n1 (list 'cos (* th n)))))
               (bco (simplify (/ (+ n0 (* n1 r cs)) (* r sn)))))
          (simplify (* K0 (^ r n) (+ (* n1 (list 'cos (simplify (* th n)))) (* bco (list 'sin (simplify (* th n))))))))
        (let* ((sq (simplify (^ D 1/2)))
               (rp (simplify (/ (+ (- p) sq) 2)))
               (rm (simplify (/ (- (- p) sq) 2)))
               (Ap (simplify (* K0 (/ (+ (* n1 rp) n0) (- rp rm)))))
               (Am (simplify (* K0 (/ (+ (* n1 rm) n0) (- rm rp))))))
          (simplify (+ (* Ap (^ rp n)) (* Am (^ rm n))))))))

(define (inverse-ztransform F z n)
  (let ((r (with-step ('tz-inverse "Обратное Z-преобразование" (list 'inverse-ztransform F z n))
              (tz-inv F z n))))
    (if r
        (begin
          (record-condition (list '>= n 0) "обратное Z-преобразование: ответ для целых n ≥ 0")
          (if (and (step-log-enabled?) (not (tr-free? (simplify F) z)))
              (let* ((chk (call-quietly (lambda () (tz-Z r n z))))
                     (ok (and chk (tr-equal? chk F))))
                (record-step 'tz-inv-check "Проверка обратного Z-преобразования"
                             (if ok "Z-преобразование ответа равно F(z): проверено"
                                 "Z-преобразование ответа не совпало: не проверено")
                             F r 'main)))
          r)
        (list 'inverse-ztransform F z n))))

; ---------- теоремы о предельных значениях ----------

; a_0 = lim_{z→∞} F(z)
(define (ztransform-initial F z)
  (let ((r (tr-try (lambda () (limit F z 'inf)))))
    (if (and r (not (contains-sym? r 'limit))) r (list 'ztransform-initial F z))))

; lim_{n→∞} a_n = lim_{z→1} (z−1)F(z), если все полюса (z−1)F внутри единичного круга
(define (ztransform-final F z)
  (let* ((G (simplify (together (* (- z 1) F))))
         (d (denom G))
         (poles (if (tr-free? d z) '() (tr-try (lambda () (transfer-poles G z)))))
         (mods (and poles (map (lambda (p) (tr-try (lambda () (eval-num (list 'abs p))))) poles))))
    (cond ((not poles) (list 'ztransform-final F z))
          ((not (every? number? mods)) 'unknown)
          ((any? (lambda (m) (>= m 1.0)) mods)
           (begin (record-condition '(< (abs z) 1) "теорема о конечном значении: полюса (z−1)F вне единичного круга")
                  'unknown))
          (else (let ((r (tr-try (lambda () (limit G z 1)))))
                  (if (and r (not (contains-sym? r 'limit))) r (list 'ztransform-final F z)))))))

; ---------- сертификат Z-преобразования ----------

(define (tz-ev a n k)
  (tr-try (lambda () (eval-num (tr-fix (simplify (subst (list n k) a)))))))

(define (tz-radius F z)
  (let ((g (simplify (together F))))
    (if (and (polynomial? (numer g) z) (polynomial? (denom g) z))
        (let* ((d (denom g))
               (poles (if (tr-free? d z) '() (tr-try (lambda () (transfer-poles g z))))))
          (and poles
               (let ((ms (map (lambda (p) (tr-try (lambda () (eval-num (list 'abs p))))) poles)))
                 (and (every? number? ms) (foldl max 0.0 ms)))))
        #f)))

(define (tz-num-sum a n z0 R)
  (let* ((N (min 3000 (max 40 (ceiling (/ 40.0 (log-num (/ z0 (max R 0.5))))))))
         (zi (/ 1.0 z0)))
    (let loop ((k 0) (acc 0.0) (zp 1.0))
      (if (>= k N)
          acc
          (let ((v (tz-ev a n k)))
            (if (and (number? v) )
                (loop (+ k 1) (+ acc (* v zp)) (* zp zi))
                #f))))))

(define (log-num x) (eval-num (list 'log x)))

; (ztransform-check a F n z) → #t (совпадает с таблицей/правилами), numeric (частичные суммы в трёх точках z), #f, unknown
(define (ztransform-check a F n z)
  (let ((r (tz-Z a n z)))
    (cond ((and r (tr-equal? r F)) #t)
          (else
           (let ((R (tz-radius F z)))
             (if (not R)
                 'unknown
                 (let ((res (map (lambda (z0)
                                   (let ((s (tz-num-sum a n z0 R))
                                         (v (tr-try (lambda () (eval-num (subst (list z z0) F))))))
                                     (if (and (number? s) (number? v))
                                         (<= (abs (- s v)) (* 0.000001 (+ 1.0 (abs v))))
                                         'unknown)))
                                 (list (+ R 2.0) (+ R 3.0) (+ R 5.0)))))
                   (cond ((member? #f res) #f)
                         ((member? 'unknown res) 'unknown)
                         (else 'numeric)))))))))

; ---------- разностные уравнения ----------

(define (tz-cname j) (string->symbol (string-append "C" (number->string (+ j 1)))))

; разбор линейного уравнения → (cs g) : cs[k] — коэффициент при a(n+k), g — правая часть; или #f
(define (tz-parse-eq eq a n)
  (if (not (tr-head? eq '=))
      #f
      (let* ((e (expand (simplify (- (cadr eq) (caddr eq)))))
             (ts (if (tr-head? e '+) (cdr e) (list e))))
        (let loop ((l ts) (cs '()) (g '()))
          (if (null? l)
              (if (null? cs)
                  #f
                  (let* ((K (foldl max 0 (map car cs)))
                         (kmin (foldl min K (map car cs))))
                    (if (not (= kmin 0))
                        #f
                        (list (map (lambda (k) (let ((p (assoc k cs))) (if p (cdr p) 0))) (range (+ K 1)))
                              (simplify (* -1 (apply + g)))))))
              (let* ((t (car l)) (fs (tr-factors t))
                     (u (tr-find (lambda (x) (and (pair? x) (equal? (car x) a))) fs)))
                (cond ((not u) (if (contains-sym? t a) #f (loop (cdr l) cs (cons t g))))
                      (else
                       (let* ((rest (tr-prod (tr-remove u fs))) (ab (and (= (length u) 2) (tr-lin (cadr u) n))))
                         (if (and ab (equal? (car ab) 1) (tr-int? (cdr ab)) (>= (cdr ab) 0)
                                  (tr-free? rest n) (not (contains-sym? rest a)))
                             (let ((p (assoc (cdr ab) cs)))
                               (loop (cdr l)
                                     (if p
                                         (map (lambda (q) (if (equal? (car q) (cdr ab)) (cons (car q) (+ (cdr q) rest)) q)) cs)
                                         (cons (cons (cdr ab) rest) cs))
                                     g))
                             #f))))))))))

(define (tz-parse-conds conds a)
  (if (null? conds)
      '()
      (let ((c (car conds)))
        (if (and (tr-head? c '=) (pair? (cadr c)) (equal? (car (cadr c)) a) (number? (cadr (cadr c))))
            (cons (list (cadr (cadr c)) (caddr c)) (tz-parse-conds (cdr conds) a))
            (tz-parse-conds (cdr conds) a)))))

(define (zsolve eq yn conds)
  (let* ((a (car yn)) (n (cadr yn))
         (pe (tr-try (lambda () (tz-parse-eq eq a n)))))
    (if (not pe)
        (list 'zsolve eq yn conds)
        (let* ((cs (car pe)) (g (cadr pe)) (K (- (length cs) 1))
               (z 'tz-z)
               (given (tz-parse-conds conds a))
               (P (simplify (apply + (map2 (lambda (c k) (* c (^ z k))) cs (range (+ K 1))))))
               (G (if (equal? g 0) 0 (tz-Z g n z)))
               (Az (if (equal? G 0) 0 (simplify (/ G P))))
               (parts
                (and G
                     (cons (if (equal? G 0) 0 (tz-inv Az z n))
                           (map (lambda (j)
                                  (let* ((aj (let ((p (assoc j given))) (if p (cadr p) (tz-cname j))))
                                         (Q (simplify (apply + (map (lambda (k) (* (nth cs k) (^ z (- k j))))
                                                                    (drop (range (+ K 1)) (+ j 1))))))
                                         (inv (tz-inv (simplify (/ Q P)) z n)))
                                    (and inv (simplify (* aj inv)))))
                                (range K))))))
          (if (or (not parts) (not (every? (lambda (x) x) parts)))
              (list 'zsolve eq yn conds)
              (let* ((sol (simplify (apply + parts)))
                     (res (list '= (list a n) sol))
                     (ck (zsolve-check eq yn res conds)))
                (if (equal? ck #f)
                    (list 'zsolve eq yn conds)
                    (begin
                      (if (step-log-enabled?)
                          (begin
                            (record-step 'tz-transform "Преобразованное уравнение"
                                         "Z: разностное уравнение → алгебраическое по z"
                                         eq (list '= P G) 'main)
                            (record-step 'tz-initial "Начальные условия"
                                         "a(j) при j < K подставлены в изображение"
                                         conds given 'main)
                            (record-step 'tz-az "Изображение A(z)"
                                         "A(z) = G(z)/P(z)"
                                         (list '= P G) (list '= (list 'tz-A n) Az) 'main)
                            (record-step 'tz-solution "Решение разностного уравнения"
                                         "A(z) → a(n): простейшие дроби F(z)/z" Az res 'main)
                            (record-step 'tz-check "Проверка подстановкой"
                                         (cond ((equal? ck #t) "последовательность подставлена в уравнение: тождество проверено")
                                               ((equal? ck 'numeric) "проверено численно в точках")
                                               (else "проверка не выполнена"))
                                         eq res 'main)))
                      (record-condition (list '>= n 0) "разностное уравнение: решение для целых n ≥ 0") res))))))))


; подстановка найденной последовательности: (a arg) → sol(n := arg)
(define (tz-subst-seq e a n sol)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) a) (= (length e) 2)) (subst (list n (cadr e)) sol))
        (else (cons (car e) (map (lambda (x) (tz-subst-seq x a n sol)) (cdr e))))))

(define (tz-const-vals e)
  (subst '((C1 3/7) (C2 -2/5) (C3 5/3) (C4 -1/3) (C5 2/9) (C6 -4/7)) e))

; b^(n + c) → b^c · b^n (упрощатель степени сам не разделяет)
(define (tz-norm e n)
  (cond ((not (pair? e)) e)
        ((and (tr-head? e '^) (tr-free? (cadr e) n) (tr-lin (caddr e) n)
              (not (equal? (car (tr-lin (caddr e) n)) 0)) (not (equal? (cdr (tr-lin (caddr e) n)) 0)))
         (let ((ab (tr-lin (caddr e) n)) (b (tz-norm (cadr e) n)))
           (list '* (list '^ b (cdr ab)) (list '^ b (list '* (car ab) n)))))
        (else (cons (car e) (map (lambda (x) (tz-norm x n)) (cdr e))))))

(define (tz-zero-test r n)
  (let ((e (tr-try (lambda () (simplify (expand (tz-norm r n)))))))
    (cond ((and e (equal? e 0)) #t)
          (else
           (let ((vs (map (lambda (k) (let ((v (tr-try (lambda () (eval-num (tz-const-vals (subst (list n k) r))))))) v))
                          '(0 1 2 3 4 5))))
             (cond ((not (every? number? vs)) 'unknown)
                   ((every? (lambda (v) (< (abs v) 0.000000001)) vs) 'numeric)
                   (else #f)))))))

(define (tz-and3 rs)
  (cond ((member? #f rs) #f)
        ((member? 'unknown rs) 'unknown)
        ((every? (lambda (r) (equal? r #t)) rs) #t)
        (else 'numeric)))

; (zsolve-check eq (a n) sol conds): подстановка в уравнение и начальные значения; #t | numeric | #f | unknown
(define (zsolve-check eq yn sol conds)
  (let* ((a (car yn)) (n (cadr yn))
         (expr (if (tr-head? sol '=) (caddr sol) sol))
         (resid (tr-try (lambda () (simplify (- (tz-subst-seq (cadr eq) a n expr) (tz-subst-seq (caddr eq) a n expr))))))
         (r1 (if resid (tz-zero-test resid n) 'unknown))
         (rs (map (lambda (c)
                    (let ((v (tr-try (lambda () (simplify (subst (list n (car c)) expr))))))
                      (if (not v)
                          'unknown
                          (if (tr-equal? v (cadr c))
                              #t
                              (let ((x (tr-try (lambda () (eval-num (tz-const-vals v)))))
                                    (y (tr-try (lambda () (eval-num (tz-const-vals (cadr c)))))))
                                (if (and (number? x) (number? y))
                                    (if (< (abs (- x y)) 0.000000001) 'numeric #f)
                                    'unknown))))))
                  (tz-parse-conds conds a))))
    (tz-and3 (cons r1 rs))))

; ===================================================================================
; Преобразование Фурье
; ===================================================================================

(define (tf-two-pi) (* 2 'pi))

; сумма: пары θ с нулевой суммой коэффициентов (прямоугольный импульс) — отдельно
(define (tf-pure-step t term)
  ; c·θ(a t + b), a = 1 → (c . τ), иначе #f
  (let* ((fs (tr-factors term))
         (st (tr-find (lambda (x) (tr-head? x 'heaviside)) fs)))
    (and st
         (every? (lambda (x) (or (equal? x st) (tr-free? x t))) fs)
         (let ((ab (tr-lin (cadr st) t)))
           (and ab (equal? (car ab) 1)
                (cons (tr-prod (tr-remove st fs)) (simplify (- (cdr ab)))))))))

(define (tf-F f t w)
  (let ((g (simplify f)))
    (cond ((tr-free? g t) (if (equal? g 0) 0 (simplify (* 2 'pi g (list 'dirac w)))))
          ((tr-head? g '+) (tf-sum (cdr g) t w))
          (else (let ((e (expand g)))
                  (if (and (tr-head? e '+) (not (equal? e g)))
                      (tf-sum (cdr e) t w)
                      (tf-term g t w)))))))

(define (tf-rect-pair steps t w)
  ; steps: список (c . τ); сумма c = 0 → Σ c e^{−iωτ}/(iω)
  (let ((tot (simplify (apply + (map car steps)))))
    (if (and (equal? tot 0) (>= (length steps) 2))
        (if (and (= (length steps) 2)
                 (equal? (simplify (+ (cdr (car steps)) (cdr (cadr steps)))) 0))
            ; c θ(t + T) − c θ(t − T) → 2c sin(ωT)/ω
            (let* ((sw (tf-neg? (car (car steps)))) (s1 (if sw (cadr steps) (car steps))) (s2 (if sw (car steps) (cadr steps)))
                   (T (cdr s2)) (c (- (car s2))))
              (simplify (/ (* 2 c (list 'sin (* w T))) w)))
            (simplify (/ (apply + (map (lambda (s) (* (car s) (list 'exp (* -1 '%i w (cdr s))))) steps))
                         (* '%i w))))
        #f)))

(define (tf-sum ts t w)
  (let* ((ps (map (lambda (x) (tf-pure-step t x)) ts))
         (steps (filter (lambda (p) p) ps))
         (rect (and (>= (length steps) 2) (tf-rect-pair steps t w)))
         (others (if rect
                     (let loop ((l ts) (p ps) (acc '()))
                       (if (null? l) (reverse acc) (loop (cdr l) (cdr p) (if (car p) acc (cons (car l) acc)))))
                     ts)))
    (let loop ((l others) (acc (if rect (list rect) '())))
      (if (null? l)
          (simplify (apply + acc))
          (let ((r (tf-F (car l) t w)))
            (if r (loop (cdr l) (cons r acc)) #f))))))

; число производных: (diff (diff X t) t) → (n . X)
(define (tf-nth-diff e t)
  (if (and (tr-head? e 'diff) (= (length e) 3) (equal? (caddr e) t))
      (let ((r (tf-nth-diff (cadr e) t))) (cons (+ 1 (car r)) (cdr r)))
      (cons 0 e)))

(define (tf-term f t w)
  (let ((fs (tr-factors f)))
    (cond ((tr-find (lambda (x) (tr-head? x 'dirac)) fs) (tf-dirac fs t w))
          ((tr-find (lambda (x) (tr-head? x 'heaviside)) fs) (tf-heaviside f fs t w))
          ((tr-find (lambda (x) (tr-head? x 'diff)) fs) (tf-deriv fs t w))
          ((tr-find (lambda (x) (tr-head? x 'fourier-convolve)) fs) (tf-conv fs t w))
          ((tr-find (lambda (x) (tr-unknown-call? x)) fs) (tf-unknown fs t w))
          ((tf-sinc fs t w) (tf-sinc fs t w))
          (else (tf-smooth f fs t w)))))

(define (tf-tidy e)
  (cond ((not (pair? e)) e)
        ((tr-head? e (quote exp)) (list (quote exp) (simplify (expand (tf-tidy (cadr e))))))
        (else (cons (car e) (map tf-tidy (cdr e))))))

; c sin(a t)/t: π c (θ(ω + a) − θ(ω − a))
(define (tf-sinc fs t w)
  (let* ((s (tr-find (lambda (x) (and (tr-head? x (quote sin)) (tr-lin (cadr x) t) (equal? (cdr (tr-lin (cadr x) t)) 0))) fs))
         (inv (tr-find (lambda (x) (and (tr-head? x (quote ^)) (equal? (cadr x) t) (equal? (caddr x) -1))) fs)))
    (and s inv
         (let ((rest (tr-remove inv (tr-remove s fs))) (a (car (tr-lin (cadr s) t))))
           (and (every? (lambda (x) (tr-free? x t)) rest)
                (simplify (* (tr-prod rest) (quote pi) (- (heaviside (+ w a)) (heaviside (- w a))))))))))

; δ(a t + b) g(t)
(define (tf-dirac fs t w)
  (let* ((d (tr-find (lambda (x) (tr-head? x 'dirac)) fs))
         (rest (tr-remove d fs))
         (ab (tr-lin (cadr d) t)))
    (if (and ab (number? (car ab)) (not (= (car ab) 0)) (not (tr-find (lambda (x) (tr-head? x 'dirac)) rest)))
        (let* ((t0 (simplify (/ (- (cdr ab)) (car ab))))
               (g (simplify (tr-fix-step (subst (list t t0) (tr-prod rest))))))
          (simplify (/ (* g (list 'exp (* -1 '%i w t0))) (abs-num (car ab)))))
        #f)))

(define (abs-num x) (if (< x 0) (- x) x))

(define (tr-fix-step e)
  (cond ((not (pair? e)) e)
        ((and (tr-head? e 'heaviside) (number? (cadr e))) (cond ((> (cadr e) 0) 1) ((< (cadr e) 0) 0) (else 1/2)))
        ((and (tr-head? e 'dirac) (number? (cadr e)) (not (= (cadr e) 0))) 0)
        ((and (tr-head? e 'sign) (number? (cadr e))) (cond ((> (cadr e) 0) 1) ((< (cadr e) 0) -1) (else 0)))
        (else (cons (car e) (map tr-fix-step (cdr e))))))

; тригонометрия → экспоненты
(define (tf-exp-form e)
  (cond ((not (pair? e)) e)
        ((and (tr-head? e 'cos) (= (length e) 2))
         (let ((x (tf-exp-form (cadr e))))
           (list '* 1/2 (list '+ (list 'exp (list '* '%i x)) (list 'exp (list '* -1 '%i x))))))
        ((and (tr-head? e 'sin) (= (length e) 2))
         (let ((x (tf-exp-form (cadr e))))
           (list '* (list '* -1/2 '%i) (list '+ (list 'exp (list '* '%i x)) (list '* -1 (list 'exp (list '* -1 '%i x)))))))
        (else (cons (car e) (map tf-exp-form (cdr e))))))

; θ(a t + b) h(t)
(define (tf-heaviside f fs t w)
  (let* ((st (tr-find (lambda (x) (tr-head? x 'heaviside)) fs))
         (rest (tr-remove st fs))
         (ab (tr-lin (cadr st) t)))
    (cond ((not (and ab (number? (car ab)) (not (= (car ab) 0)))) #f)
          ((tr-find (lambda (x) (or (tr-head? x 'heaviside) (tr-head? x 'dirac))) rest) #f)
          ((< (car ab) 0)
           ; отражение: f(−t) имеет ступеньку с положительным коэффициентом; F[f](ω) = F[f(−·)](−ω)
           (let* ((fr (simplify (subst (list t (list '* -1 t)) f)))
                  (r (tf-F fr t w)))
             (and r (simplify (subst (list w (list '* -1 w)) r)))))
          ((not (equal? (car ab) 1))
           ; θ(a t + b) = θ(t + b/a) при a > 0
           (tf-F (simplify (list '* (list 'heaviside (list '+ t (/ (cdr ab) (car ab)))) (tr-prod rest))) t w))
          (else
           (let* ((tau (simplify (- (cdr ab))))
                  (h1 (simplify (subst (list t (list '+ t tau)) (tr-prod rest))))
                  (r (tf-causal h1 t w)))
             (and r (simplify (* (list 'exp (* -1 '%i w tau)) r))))))))

; F[θ(t) h(t)] для h — сумма c·t^k·e^{λ t} (тригонометрия раскрывается)
(define (tf-causal h t w)
  (let* ((e (expand (tf-exp-form h)))
         (ts (if (tr-head? e '+) (cdr e) (list e))))
    (let loop ((l ts) (acc '()))
      (if (null? l)
          (simplify (apply + acc))
          (let ((r (tf-causal-term (car l) t w)))
            (if r (loop (cdr l) (cons r acc)) #f))))))

(define (tf-causal-term term t w)
  (let ((fs (tr-factors term)))
    (let loop ((l fs) (c 1) (k 0) (lam 0))
      (if (null? l)
          (cond ((and (number? lam) (>= lam 0) (not (and (= lam 0) (= k 0)))) #f)
                ((and (= k 0) (equal? lam 0))
                 (simplify (+ (/ c (* '%i w)) (* 'pi c (list 'dirac w)))))
                (else
                 (begin
                   (if (and (symbol? lam) #t) (record-condition (list '< lam 0) "преобразование Фурье e^{λt}θ(t): Re λ < 0") #f)
                   (simplify (/ (* c (factorial k)) (^ (+ (* -1 lam) (* '%i w)) (+ k 1)))))))
          (let ((x (car l)))
            (cond ((tr-free? x t) (loop (cdr l) (* c x) k lam))
                  ((equal? x t) (loop (cdr l) c (+ k 1) lam))
                  ((and (tr-head? x '^) (equal? (cadr x) t) (tr-int? (caddr x)) (> (caddr x) 0))
                   (loop (cdr l) c (+ k (caddr x)) lam))
                  ((and (tr-head? x 'exp) (tr-lin (cadr x) t) (tr-free? (cdr (tr-lin (cadr x) t)) t))
                   (let ((ab (tr-lin (cadr x) t)))
                     (loop (cdr l) (* c (list 'exp (cdr ab))) k (simplify (+ lam (car ab))))))
                  (else #f)))))))

; (diff X t) · const
(define (tf-deriv fs t w)
  (let* ((d (tr-find (lambda (x) (tr-head? x 'diff)) fs))
         (rest (tr-remove d fs))
         (nb (tf-nth-diff d t)))
    (cond ((not (every? (lambda (x) (tr-free? x t)) rest)) #f)
          ((tr-unknown-call? (cdr nb))
           (simplify (* (tr-prod rest) (^ (* '%i w) (car nb)) (list 'fourier (cdr nb) t w))))
          (else
           (let* ((base (cdr nb))
                  (dn (let loop ((k (car nb)) (e base)) (if (= k 0) e (loop (- k 1) (diff t e)))))
                  (r (tf-F dn t w)))
             (and r (simplify (* (tr-prod rest) r))))))))

; свёртка по всей прямой
(define (tf-conv fs t w)
  (let* ((cv (tr-find (lambda (x) (tr-head? x 'fourier-convolve)) fs))
         (rest (tr-remove cv fs)))
    (if (and (every? (lambda (x) (tr-free? x t)) rest) (= (length cv) 4))
        (let ((a (tf-F (cadr cv) t w)) (b (tf-F (caddr cv) t w)))
          (and a b (simplify (* (tr-prod rest) a b))))
        #f)))

; неизвестная функция (h (a t + b))
(define (tf-unknown fs t w)
  (let* ((u (tr-find tr-unknown-call? fs))
         (rest (tr-remove u fs))
         (ab (tr-lin (cadr u) t)))
    (if (and ab (not (equal? (car ab) 0)) (every? (lambda (x) (tr-free? x t)) rest))
        (let* ((a (car ab)) (b (cdr ab))
               (base (list 'fourier (list (car u) t) t (simplify (/ w a)))))
          (simplify (/ (* (tr-prod rest) (list 'exp (* '%i w (/ b a))) base) (if (number? a) (abs-num a) (list 'abs a)))))
        #f)))

; без ступенек и дельт: c · t^k · exp(...) или рациональный множитель
(define (tf-smooth f fs t w)
  (let ((e (expand (tf-exp-form f))))
    (if (tr-head? e '+)
        (let loop ((l (cdr e)) (acc '()))
          (if (null? l)
              (simplify (apply + acc))
              (let ((r (tf-smooth-term (car l) t w)))
                (if r (loop (cdr l) (cons r acc)) #f))))
        (tf-smooth-term e t w))))

; разложение множителей: (c k E rat) — константа, степень t, сумма показателей, рациональные множители
(define (tf-smooth-term term t w)
  (let ((fs (tr-factors term)))
    (let loop ((l fs) (c 1) (k 0) (E 0) (rat '()))
      (if (null? l)
          (tf-smooth-core (simplify c) k (simplify E) rat t w)
          (let ((x (car l)))
            (cond ((tr-free? x t) (loop (cdr l) (* c x) k E rat))
                  ((equal? x t) (loop (cdr l) c (+ k 1) E rat))
                  ((and (tr-head? x '^) (equal? (cadr x) t) (tr-int? (caddr x)) (> (caddr x) 0))
                   (loop (cdr l) c (+ k (caddr x)) E rat))
                  ((tr-head? x 'exp) (loop (cdr l) c k (+ E (cadr x)) rat))
                  ((and (tr-head? x '^) (tr-int? (caddr x)) (< (caddr x) 0)
                        (polynomial? (expand (cadr x)) t))
                   (loop (cdr l) c k E (cons x rat)))
                  (else #f)))))))

; E = α|t| + γ t² + β t + c0 → (α γ β c0) или #f
(define (tf-exponent E t)
  (let* ((x (expand E))
         (ts (if (tr-head? x '+) (cdr x) (list x))))
    (let loop ((l ts) (al 0) (ga 0) (be 0) (c0 0))
      (if (null? l)
          (list al ga be c0)
          (let* ((u (car l)) (fs (tr-factors u))
                 (ab (tr-find (lambda (y) (tr-head? y 'abs)) fs)))
            (cond ((tr-free? u t) (loop (cdr l) al ga be (+ c0 u)))
                  ((and ab (equal? (cadr ab) t) (tr-free? (tr-prod (tr-remove ab fs)) t))
                   (loop (cdr l) (+ al (tr-prod (tr-remove ab fs))) ga be c0))
                  ((polynomial? u t)
                   (let ((cs (coefficients u t)))
                     (cond ((= (length cs) 2) (loop (cdr l) al ga (+ be (cadr cs)) (+ c0 (car cs))))
                           ((= (length cs) 3) (loop (cdr l) al (+ ga (caddr cs)) (+ be (cadr cs)) (+ c0 (car cs))))
                           (else #f))))
                  (else #f)))))))

(define (tf-pos-cond a)
  (if (symbol? a) (record-condition (list '> a 0) "преобразование Фурье: коэффициент затухания a > 0") #f))

(define (tf-smooth-core c k E rat t w)
  (cond
    ((not (null? rat)) (tf-rational-factor c k E rat t w))
    (else
     (let ((p (tf-exponent E t)))
       (if (not p)
           #f
           (let* ((al (car p)) (ga (cadr p)) (be (caddr p)) (c0 (nth p 3))
                  (coef (simplify (* c (list 'exp c0))))
                  (shifted (lambda (G) (simplify (subst (list w (list '+ w (list '* '%i be))) G))))
                  (G0 (cond
                        ; чистая экспонента e^{βt}: 2π δ(ω + iβ) только при β = iω0
                        ((and (equal? al 0) (equal? ga 0))
                         (if (and (equal? be 0) (= k 0)) (* 2 'pi (list 'dirac w)) #f))
                        ((and (equal? ga 0) (not (equal? al 0)) (tf-neg? al))
                         (let ((a (simplify (* -1 al))))
                           (tf-pos-cond a)
                           (/ (* 2 a) (+ (^ a 2) (^ w 2)))))
                        ((and (equal? al 0) (not (equal? ga 0)) (tf-neg? ga))
                         (let ((a (simplify (* -1 ga))))
                           (tf-pos-cond a)
                           (* (^ (/ 'pi a) 1/2) (list 'exp (/ (* -1 (^ w 2)) (* 4 a))))))
                        (else #f))))
             (cond
               ((and (not G0) (equal? al 0) (equal? ga 0) (tr-has-i? be) (= k 0))
                ; e^{iω0 t}: 2π δ(ω − ω0)
                (let ((w0 (simplify (/ be '%i))))
                  (simplify (* coef 2 'pi (list 'dirac (- w w0))))))
               ((not G0) #f)
               (else
                (let* ((Gk (let loop ((j k) (G G0)) (if (= j 0) G (loop (- j 1) (simplify (* '%i (diff w G)))))))
                       (Gs (if (equal? be 0) Gk (shifted Gk))))
                  (simplify (tf-tidy (simplify (* coef Gs)))))))))))))

(define (tf-neg? x)
  (cond ((number? x) (< x 0))
        ((tr-head? x '*) (and (number? (cadr x)) (< (cadr x) 0)))
        (else #f)))

; 1/(c0 + c2 t²) с модуляцией e^{iω0 t}: (π/(c2 a)) e^{−a|ω|}
(define (tf-rational-factor c k E rat t w)
  (if (or (not (= k 0)) (not (= (length rat) 1)) (not (equal? (caddr (car rat)) -1)))
      #f
      (let* ((q (expand (cadr (car rat)))) (cs (coefficients q t)))
        (if (not (and (= (length cs) 3) (equal? (cadr cs) 0)))
            #f
            (let* ((c0 (car cs)) (c2 (caddr cs)) (a2 (simplify (/ c0 c2))) (a (simplify (^ a2 1/2)))
                   (p (tf-exponent E t)))
              (if (not (and p (equal? (car p) 0) (equal? (cadr p) 0)
                            (or (equal? (caddr p) 0) (tr-has-i? (caddr p)))))
                  #f
                  (let* ((w0 (simplify (/ (caddr p) '%i)))
                         (coef (simplify (* c (list 'exp (nth p 3)))))
                         (pos (or (and (number? a2) (> a2 0)) (symbol? a2) #f)))
                    (if (not pos)
                        #f
                        (begin
                          (if (not (number? a2)) (record-condition (list '> a 0) "преобразование Фурье 1/(a²+t²): a > 0") #f)
                          (simplify (* coef (/ 'pi (* c2 a)) (list 'exp (* -1 a (list 'abs (- w w0)))))))))))))))

(define (fourier f t w)
  (let ((r (with-step ('tf-forward "Преобразование Фурье" (list 'fourier f t w))
              (tf-F f t w))))
    (if r
        (begin
          (if (step-log-enabled?)
              (record-step 'tf-rule "Применённое правило" (tf-rule-of f t) f r 'main))
          r)
        (list 'fourier f t w))))

; правило Фурье по форме функции
(define (tf-rule-of f t)
  (let* ((g (simplify f))
         (fs (tr-factors g)))
    (cond ((tr-head? g '+) "линейность: F[f + g] = F[f] + F[g]")
          ((tr-find (lambda (x) (tr-head? x 'dirac)) fs) "δ-функция: просеивание")
          ((tr-find (lambda (x) (tr-head? x 'heaviside)) fs) "θ-функция: причинность / прямоугольный импульс")
          ((tr-find (lambda (x) (tr-head? x 'diff)) fs) "дифференцирование: F[f′] = iω·F[f]")
          ((tr-find (lambda (x) (tr-head? x 'fourier-convolve)) fs) "свёртка: F[f ⋆ g] = F[f]·F[g]")
          (else "табличное значение (e^{−a|t|}, 1/(a²+t²), sin(at)/t, …)"))))

; ---------- обратное преобразование Фурье ----------

; отделить множитель e^{−iωτ}: (τ . остаток) или #f
(define (tf-strip-shift F w)
  (let* ((fs (tr-factors (simplify F)))
         (ex (tr-find (lambda (x) (and (tr-head? x 'exp) (tr-lin (cadr x) w) (tr-has-i? (car (tr-lin (cadr x) w)))
                                       (not (equal? (car (tr-lin (cadr x) w)) 0))
                                       (tr-free? (cdr (tr-lin (cadr x) w)) w)))
                      fs)))
    (and ex
         (let* ((ab (tr-lin (cadr ex) w)) (tau (simplify (* '%i (car ab)))))
           (cons tau (tr-prod (cons (list 'exp (cdr ab)) (tr-remove ex fs))))))))

(define (tf-inv F w t)
  (let ((g (simplify F)))
    (cond ((tr-free? g w) (if (equal? g 0) 0 (simplify (* g (list 'dirac t)))))
          ((tr-head? g '+)
           (let loop ((l (cdr g)) (acc '()))
             (if (null? l)
                 (simplify (apply + acc))
                 (let ((r (tf-inv (car l) w t))) (if r (loop (cdr l) (cons r acc)) #f)))))
          (else
           (or (let ((sh (tf-strip-shift g w)))
                 (and sh (let ((r (tf-inv (cdr sh) w t)))
                           (and r (simplify (subst (list t (- t (car sh))) r))))))
               (tf-inv-rational g w t)
               (tf-inv-dual g w t))))))

; двойственность: ∫ F(ω) e^{iωt} dω = (F[F])(−t), обратное = (1/2π)(F[F])(−t)
(define (tf-inv-dual F w t)
  (let* ((u 'tf-u) (G (tf-F F w u)))
    (and G (not (contains-sym? G 'fourier))
         (simplify (/ (subst (list u (list '* -1 t)) G) (* 2 'pi))))))

(define (tf-rational? g w)
  (and (polynomial? (expand (numer g)) w) (polynomial? (expand (denom g)) w)))

(define (tf-inv-rational F w t)
  (let ((g (simplify (together F))))
    (and (tf-rational? g w)
         (let ((r (or (tf-inv-real g w t) (tf-inv-laplace g w t))))
           (if (and r (step-log-enabled?))
               (record-step 'tf-inv-partial "Обратное преобразование: разложение"
                            (string-append "знаменатель " (tf-mp (denom g)) "; маршрут: "
                                           (if (tr-has-i? g) "Лаплас по s = iω" "вещественные квадратичные множители"))
                            g r 'main))
           r))))

; маршрут 2: вещественные коэффициенты, неприводимые квадратичные множители кратности 1
(define (tf-inv-real g w t)
  (and (not (tr-has-i? g))
       (let* ((a (simplify (apart g w)))
              (ts (if (tr-head? a '+) (cdr a) (list a))))
         (let loop ((l ts) (acc '()))
           (if (null? l)
               (simplify (apply + acc))
               (let ((r (tf-inv-real-term (car l) w t)))
                 (if r (loop (cdr l) (cons r acc)) #f)))))))

(define (tf-inv-real-term term w t)
  (let ((nu (numer term)) (d (denom term)))
    (if (tr-free? d w)
        #f
        (let ((fl (factor-list d)))
          (if (not (= (length fl) 2))
              #f
              (let* ((c (car fl)) (q (car (cadr fl))) (m (cadr (cadr fl)))
                     (cs (coefficients q w)))
                (if (not (and (= m 1) (= (length cs) 3) (<= (length (coefficients nu w)) 2)))
                    #f
                    (let* ((q2 (caddr cs)) (p (/ (cadr cs) q2)) (r0 (/ (car cs) q2))
                           (kap (- r0 (/ (* p p) 4))))
                      (if (not (and (number? kap) (> kap 0)))
                          #f
                          (let* ((nc (coefficients nu w))
                                 (be (if (null? nc) 0 (car nc)))
                                 (al (if (or (null? nc) (null? (cdr nc))) 0 (cadr nc)))
                                 (K0 (/ 1 (* c q2)))
                                 (sk (simplify (^ kap 1/2)))
                                 (damp (list 'exp (* -1 sk (list 'abs t))))
                                 (osc (if (equal? p 0) 1 (list 'exp (* '%i (/ p -2) t))))
                                 (br (+ (- be (* al (/ p 2))) (if (equal? al 0) 0 (* '%i al sk (list 'sign t))))))
                            (simplify (* K0 (/ 1 (* 2 sk)) osc damp br))))))))))))

; маршрут 1: F(ω) = H(s), s = iω; полюса слева → θ(t)·L⁻¹, справа → θ(−t)·g(−t)
(define (tf-split-i e)
  ; e (выражение без деления) → (re . im), каждое без %i, или #f
  (let* ((x (simplify (expand e)))
         (re (simplify (subst '(%i 0) x)))
         (im (simplify (/ (- x re) '%i))))
    (and (not (tr-has-i? re)) (not (tr-has-i? im)) (cons re im))))

(define (tf-inv-laplace g w t)
  (let* ((s 'tf-s)
         (H (simplify (together (subst (list w (list '* -1 '%i s)) g))))
         (nu (numer H)) (de (denom H))
         (dp (tf-split-i de)) (np (tf-split-i nu)))
    (and dp np (equal? (cdr dp) 0) (not (equal? (car dp) 0))
         (let* ((Hr (simplify (/ (car np) (car dp)))) (Hi (simplify (/ (cdr np) (car dp))))
                (fr (tf-inv-causal Hr s t)) (fi (tf-inv-causal Hi s t)))
           (and fr fi (simplify (+ fr (* '%i fi))))))))

; знак вещественной части полюсов множителя q (степени 1 или 2) относительно s: -1 слева, 1 справа, 0 — на оси / смешанно
(define (tf-pole-side q s)
  (let ((cs (coefficients q s)))
    (cond ((= (length cs) 2)
           (let ((rho (/ (- (car cs)) (cadr cs)))) (cond ((< rho 0) -1) ((> rho 0) 1) (else 0))))
          ((= (length cs) 3)
           (let* ((p (/ (cadr cs) (caddr cs))) (r0 (/ (car cs) (caddr cs))))
             (cond ((<= r0 0) 0)
                   ((> p 0) -1)
                   ((< p 0) 1)
                   (else 0))))
          (else 0))))

(define (tf-inv-causal P s t)
  (if (equal? P 0)
      0
      (let* ((a (simplify (apart P s)))
             (ts (if (tr-head? a '+) (cdr a) (list a))))
        (let loop ((l ts) (causal '()) (anti '()))
          (if (null? l)
              (let* ((Pc (simplify (apply + causal))) (Pa (simplify (apply + anti)))
                     (gc (if (equal? Pc 0) 0 (inverse-laplace Pc s t)))
                     (ga (if (equal? Pa 0) 0 (inverse-laplace (simplify (subst (list s (list '* -1 s)) Pa)) s t))))
                (and (not (contains-sym? gc 'inverse-laplace)) (not (contains-sym? ga 'inverse-laplace))
                     (simplify (+ (if (equal? gc 0) 0 (* gc (heaviside t)))
                                  (if (equal? ga 0) 0 (* (subst (list t (list '* -1 t)) ga) (heaviside (* -1 t))))))))
              (let* ((term (car l)) (d (denom term)))
                (if (tr-free? d s)
                    (loop (cdr l) (cons term causal) anti)
                    (let ((fl (factor-list d)))
                      (if (not (= (length fl) 2))
                          #f
                          (let ((side (tf-pole-side (car (cadr fl)) s)))
                            (cond ((= side -1) (loop (cdr l) (cons term causal) anti))
                                  ((= side 1) (loop (cdr l) causal (cons term anti)))
                                  (else #f))))))))))))

(define (inverse-fourier F w t)
  (let ((r (with-step ('tf-inverse "Обратное преобразование Фурье" (list 'inverse-fourier F w t))
              (tf-inv F w t))))
    (if r
        (begin
          (if (step-log-enabled?)
              (let ((chk (call-quietly (lambda () (fourier-check r F t w)))))
                (record-step 'tf-inv-check "Проверка обратного преобразования"
                             (cond ((equal? chk #t) "прямое преобразование ответа равно F: проверено")
                                   ((equal? chk 'numeric) "прямое преобразование совпало в численной квадратуре")
                                   (else "прямое преобразование не проверено"))
                             F r 'main)))
          r)
        (list 'inverse-fourier F w t))))

; ---------- сертификат Фурье ----------

(define (tf-step-free? f) (not (or (contains-sym? f 'heaviside) (contains-sym? f 'dirac))))

; значение f в точке (θ/δ учтены)
(define (tf-ev f t x)
  (let ((v (tr-try (lambda () (eval-num (tr-fix-step (subst (list t x) f)))))))
    (and v (tr-cplx v))))

(define (tf-mag p) (eval-num (list '^ (+ (* (car p) (car p)) (* (cdr p) (cdr p))) 1/2)))

(define (tf-breaks f t)
  (cond ((not (pair? f)) '())
        ((and (tr-head? f 'heaviside) (tr-lin (cadr f) t))
         (let ((ab (tr-lin (cadr f) t)))
           (if (and (number? (car ab)) (not (= (car ab) 0)) (number? (cdr ab)))
               (list (/ (- (cdr ab)) (car ab)))
               '())))
        (else (append-map (lambda (x) (tf-breaks x t)) (cdr f)))))

(define (tf-smooth-part f t)
  (let* ((e (expand (simplify f))) (ts (if (tr-head? e '+) (cdr e) (list e))))
    (cons (filter (lambda (x) (not (contains-sym? x 'dirac))) ts)
          (filter (lambda (x) (contains-sym? x 'dirac)) ts))))

; полуширина окна: наименьшая из 8…256, где |f(±T)| мала; #f — не абсолютно интегрируема
(define (tf-window f t)
  (let loop ((ts '(8 16 32 64 128 256)))
    (if (null? ts)
        #f
        (let ((a (tf-ev f t (car ts))) (b (tf-ev f t (- (car ts)))))
          (cond ((not (and a b)) #f)
                ((< (max (tf-mag a) (tf-mag b)) 0.000001) (car ts))
                ((and (null? (cdr ts)) (< (max (tf-mag a) (tf-mag b)) 0.0001)) (car ts))
                (else (loop (cdr ts))))))))

(define (tf-gl-panel f t a b ws)
  ; узлы GL на [a, b]: список (x . f(x))
  (let* ((half (/ (- b a) 2.0)) (mid (/ (+ a b) 2.0)))
    (map (lambda (p) (let ((x (+ mid (* half (cdr p))))) (list (* half (car p)) x (tf-ev f t x))))
         (map2 cons tf-gl-weights tf-gl-nodes))))

(define tf-gl-nodes '(-0.906179845938664 -0.5384693101056831 0.0 0.5384693101056831 0.906179845938664))
(define tf-gl-weights '(0.2369268850561891 0.4786286704993665 0.5688888888888889 0.4786286704993665 0.2369268850561891))

(define (tf-sort l) (sort l <))

; узлы (вес x f(x)) на [−L, L] с разбиением в точках разрыва и в 0
(define (tf-nodes f t L)
  (let* ((bs (filter (lambda (b) (and (> b (- L)) (< b L))) (tf-breaks f t)))
         (pts (tf-sort (append (list (* -1.0 L) 0.0 (* 1.0 L)) (map (lambda (b) (* 1.0 b)) bs))))
         (uniq (let loop ((l pts) (acc '()))
                 (cond ((null? l) (reverse acc))
                       ((and (pair? acc) (< (abs (- (car l) (car acc))) 0.0000001)) (loop (cdr l) acc))
                       (else (loop (cdr l) (cons (car l) acc)))))))
    (let loop ((p uniq) (acc '()))
      (if (null? (cdr p))
          acc
          (let* ((a (car p)) (b (cadr p)) (n (max 1 (ceiling (/ (- b a) 0.5)))) (wd (/ (- b a) n)))
            (loop (cdr p)
                  (append acc
                          (append-map (lambda (i) (tf-gl-panel f t (+ a (* i wd)) (+ a (* (+ i 1) wd)) #f))
                                      (range n)))))))))

; ∫ f e^{−iω0 t} dt по узлам → (re . im)
(define (tf-quad-at nodes w0)
  (let loop ((l nodes) (re 0.0) (im 0.0))
    (if (null? l)
        (cons re im)
        (let* ((nd (car l)) (wt (car nd)) (x (cadr nd)) (fx (caddr nd)))
          (if (not fx)
              #f
              (let ((c (cos-num (* w0 x))) (s (sin-num (* w0 x))))
                (loop (cdr l)
                      (+ re (* wt (+ (* (car fx) c) (* (cdr fx) s))))
                      (+ im (* wt (- (* (cdr fx) c) (* (car fx) s)))))))))))

(define (cos-num x) (eval-num (list 'cos x)))
(define (sin-num x) (eval-num (list 'sin x)))

; вклад δ-членов: Σ g(t0) e^{−iω0 t0}/|a|
(define (tf-dirac-at ds t w0)
  (let loop ((l ds) (re 0.0) (im 0.0))
    (if (null? l)
        (cons re im)
        (let* ((fs (tr-factors (car l))) (d (tr-find (lambda (x) (tr-head? x 'dirac)) fs))
               (ab (and d (tr-lin (cadr d) t))))
          (if (not (and ab (number? (car ab)) (not (= (car ab) 0)) (number? (cdr ab))))
              #f
              (let* ((t0 (/ (- (cdr ab)) (car ab)))
                     (g (tf-ev (tr-prod (tr-remove d fs)) t t0)))
                (if (not g)
                    #f
                    (let ((sr (/ (car g) (abs-num (car ab)))) (si (/ (cdr g) (abs-num (car ab))))
                          (c (cos-num (* w0 t0))) (s (sin-num (* w0 t0))))
                      (loop (cdr l)
                            (+ re (+ (* sr c) (* si s)))
                            (+ im (- (* si c) (* sr s))))))))))))

(define (tf-num-F f t w0)
  (let* ((sp (tf-smooth-part f t))
         (smooth (tr-sum (car sp)))
         (L (tf-window smooth t)))
    (and L
         (let* ((nodes (tf-nodes smooth t L))
                (q (tf-quad-at nodes w0))
                (dq (if (null? (cdr sp)) (cons 0.0 0.0) (tf-dirac-at (cdr sp) t w0))))
           (and q dq (cons (+ (car q) (car dq)) (+ (cdr q) (cdr dq))))))))

; допустимые головы для точной попытки
(define (tf-exact-ok? f)
  (cond ((not (pair? f)) #t)
        ((member? (car f) '(+ * exp abs heaviside sin cos)) (every? tf-exact-ok? (cdr f)))
        ((equal? (car f) '^) (and (tr-int? (caddr f)) (> (caddr f) 0) (tf-exact-ok? (cadr f))))
        (else #f)))

; ∫_0^∞ g e^{−iωt} dt = L[g](s) при s = iω — независимо от правил Фурье (таблица модуля laplace)
(define (tf-L g t w)
  (let ((r (tr-try (lambda () (laplace g t 'tf-s)))))
    (and r (not (contains-sym? r 'laplace))
         (simplify (subst (list 'tf-s (list '* '%i w)) r)))))

; точный пересчёт интеграла через преобразование Лапласа: |t| (правая и левая полупрямые) и θ(t − τ)·g
(define (tf-direct f t w)
  (let ((g (simplify f)))
    (cond ((not (tf-exact-ok? g)) #f)
          ((contains-sym? g 'dirac) #f)
          ((and (contains-sym? g 'abs) (tf-step-free? g))
           (let* ((gr (simplify (replace-expr g (list 'abs t) t)))
                  (gl (simplify (subst (list t (list '* -1 t)) (replace-expr g (list 'abs t) (list '* -1 t)))))
                  (r (tf-L gr t w))
                  (l (and r (tf-L gl t (list '* -1 w)))))
             (and r l (simplify (+ r l)))))
          ((and (contains-sym? g 'heaviside) (not (contains-sym? g 'abs)))
           (let* ((ts (tr-terms g)) (ps (map (lambda (x) (tf-pure-step-g t x)) ts)))
             (and (every? (lambda (p) p) ps)
                  (let ((rs (map (lambda (p)
                                   (let ((r (tf-L (simplify (subst (list t (list '+ t (caddr p))) (cadr p))) t w)))
                                     (and r (simplify (* (car p) (list 'exp (* -1 '%i w (caddr p))) r)))))
                                 ps)))
                    (and (every? (lambda (r) r) rs) (simplify (apply + rs)))))))
          (else #f))))

; c·g(t)·θ(t − τ), g без ступенек: (c g τ)
(define (tf-pure-step-g t term)
  (let* ((fs (tr-factors term)) (st (tr-find (lambda (x) (tr-head? x 'heaviside)) fs)))
    (and st (not (tr-find (lambda (x) (and (not (equal? x st)) (contains-sym? x 'heaviside))) fs))
         (let ((ab (tr-lin (cadr st) t)))
           (and ab (equal? (car ab) 1)
                (let* ((rest (tr-remove st fs))
                       (cst (tr-prod (filter (lambda (x) (tr-free? x t)) rest)))
                       (gt (tr-prod (filter (lambda (x) (contains-sym? x t)) rest))))
                  (list cst gt (simplify (- (cdr ab))))))))))

; (fourier-check f F t w) → #t (точный пересчёт интеграла), numeric (квадратура в трёх точках ω), #f, unknown
(define (fourier-check f F t w)
  (let ((ex (tr-try (lambda () (tf-direct f t w)))))
    (cond ((and ex (tr-equal? ex F)) #t)
          (else (tf-check-numeric f F t w)))))

(define (tf-check-numeric f F t w)
  (let* ((pts '(1/2 3/2 3))
         (res (map (lambda (w0)
                     (let ((q (tr-try (lambda () (tf-num-F f t (* 1.0 w0)))))
                           (v (tr-num-eval (subst (list w w0) F))))
                       (if (and q v) (tr-close? q v) 'unknown)))
                   pts)))
    (cond ((member? #f res) #f)
          ((member? 'unknown res) 'unknown)
          (else 'numeric))))
