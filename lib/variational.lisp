; variational.lisp — вариационное исчисление (шаги CV.1–CV.2)
; Функционал ∫ L dx; неизвестные — (y x), производные — штатные вложенные (diff (y x) x).
; Внутри — «струи» (jets): узел (y x) и его производные заменяются символами J<i>_<переменные>,
; полная производная D_v считается как ∂/∂v + Σ ∂/∂J · J_{+v} — всё остаётся рациональным в символах.
; Префикс var- (cv- занят curves.lisp).
(module variational
  (export euler-lagrange var-first-integrals var-natural-conditions var-transversality
          var-noether var-legendre var-jacobi var-convex? var-classify
          variational-solve var-check var-isoperimetric var-isoperimetric-check
          var-check-first-integral var-solution var-status var-field))

; ---------- струи ----------

(define *var-jets* (make-hash))   ; символ струи -> (индекс-функции . переменные)

(define (var-sort-vars vs)
  (sort vs (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

(define (var-join vs)
  (foldl (lambda (acc v) (string-append acc "_" (symbol->string v))) "" vs))

(define (var-jet-sym i vars)
  (let ((s (string->symbol (string-append "J" (to-string i) (var-join vars)))))
    (hash-set! *var-jets* s (cons i vars))
    s))

(define (var-specs yx) (if (pair? (car yx)) yx (list yx)))

(define (var-node spec vars)
  (foldl (lambda (acc v) (list 'diff acc v)) spec vars))

; переменные дифференцирования, если e — узел функции spec или её производная; иначе #f
(define (var-node-vars e spec)
  (cond ((equal? e spec) '())
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3) (symbol? (caddr e)))
         (let ((r (var-node-vars (cadr e) spec)))
           (if r (append r (list (caddr e))) #f)))
        (else #f)))

(define (var-match e specs)
  (let loop ((ss specs) (i 0))
    (cond ((null? ss) #f)
          (else (let ((r (var-node-vars e (car ss))))
                  (if r (cons i r) (loop (cdr ss) (+ i 1))))))))

(define (var-jetify e specs)
  (let ((hit (if (pair? e) (var-match e specs) #f)))
    (cond (hit (var-jet-sym (car hit) (var-sort-vars (cdr hit))))
          ((pair? e) (map (lambda (z) (var-jetify z specs)) e))
          (else e))))

(define (var-unjet e specs)
  (cond ((and (symbol? e) (hash-has? *var-jets* e))
         (let ((d (hash-ref *var-jets* e))) (var-node (nth specs (car d)) (cdr d))))
        ((pair? e) (map (lambda (z) (var-unjet z specs)) e))
        (else e)))

(define (var-jets-in e acc)
  (cond ((symbol? e) (if (and (hash-has? *var-jets* e) (not (member? e acc))) (append acc (list e)) acc))
        ((pair? e) (foldl (lambda (a z) (var-jets-in z a)) acc e))
        (else acc)))

; полная производная по v
(define (var-D e v)
  (foldl (lambda (acc s)
           (let ((d (hash-ref *var-jets* s)))
             (+ acc (* (diff s e) (var-jet-sym (car d) (var-sort-vars (cons v (cdr d))))))))
         (diff v e)
         (var-jets-in e '())))

(define (var-apply-D e vars) (foldl (lambda (acc v) (var-D acc v)) e vars))

; целые a … b−1
(define (var-seq a b) (if (>= a b) '() (cons a (var-seq (+ a 1) b))))

(define (var-sign-of vars) (if (= (modulo (length vars) 2) 0) 1 -1))

; левые части уравнений Эйлера — Остроградского (в струях), по одной на функцию
(define (var-euler Lj n)
  (let ((js (var-jets-in Lj '())))
    (map (lambda (i)
           (foldl (lambda (acc j)
                    (let ((d (hash-ref *var-jets* j)))
                      (if (= (car d) i)
                          (+ acc (* (var-sign-of (cdr d)) (var-apply-D (diff j Lj) (cdr d))))
                          acc)))
                  0 js))
         (range n))))

; ---------- радикалы: приведение к числителю ----------

(define (var-frac? r) (and (number? r) (not (integer? r)) (equal? (type-of r) 'rational)))

(define (var-add-base b acc) (if (member? b acc) acc (append acc (list b))))

; различные основания дробных степеней и sqrt
(define (var-bases e acc)
  (cond ((not (pair? e)) acc)
        ((and (equal? (car e) 'sqrt) (= (length e) 2))
         (var-bases (cadr e) (var-add-base (cadr e) acc)))
        ((and (equal? (car e) '^) (= (length e) 3) (var-frac? (caddr e)))
         (var-bases (cadr e) (var-add-base (cadr e) acc)))
        (else (foldl (lambda (a z) (var-bases z a)) acc (cdr e)))))

; знаменатель показателя основания b
(define (var-base-q e b)
  (cond ((not (pair? e)) 1)
        ((and (equal? (car e) 'sqrt) (= (length e) 2) (equal? (cadr e) b)) 2)
        ((and (equal? (car e) '^) (= (length e) 3) (var-frac? (caddr e)) (equal? (cadr e) b))
         (lcm (denom (caddr e)) (foldl (lambda (a z) (lcm a (var-base-q z b))) 1 (cdr e))))
        (else (foldl (lambda (a z) (lcm a (var-base-q z b))) 1 (cdr e)))))

; al: список (B w q)
(define (var-radsub e al)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2) (assoc (cadr e) al))
         (let ((r (assoc (cadr e) al))) (^ (cadr r) (/ (caddr r) 2))))
        ((and (equal? (car e) '^) (= (length e) 3) (var-frac? (caddr e)) (assoc (cadr e) al))
         (let ((r (assoc (cadr e) al))) (^ (cadr r) (* (caddr e) (caddr r)))))
        (else (map (lambda (z) (var-radsub z al)) e))))

; множители знаменателя основания (они ≠ 0 в области определения L)
(define (var-atoms d)
  (cond ((number? d) '())
        ((and (pair? d) (equal? (car d) '*)) (append-map (lambda (z) (var-atoms z)) (cdr d)))
        ((and (pair? d) (equal? (car d) '^) (= (length d) 3) (integer? (caddr d))) (list (cadr d)))
        (else (list d))))

(define (var-monomial? d ws)
  (cond ((number? d) #t)
        ((member? d ws) #t)
        ((and (pair? d) (equal? (car d) '^) (= (length d) 3) (member? (cadr d) ws) (integer? (caddr d))) #t)
        ((and (pair? d) (equal? (car d) '*)) (every? (lambda (z) (var-monomial? z ws)) (cdr d)))
        (else #f)))

(define (var-back e al)
  (simplify (subst (map (lambda (r) (list (cadr r) (^ (car r) (/ 1 (caddr r))))) al) e)))

; e = N/D с радикалами, исключёнными по w^q = B; результат (N D drop?): drop? — D одночлен от радикалов/число
(define (var-clean e)
  (let* ((bs (var-bases e '())))
    (if (any? (lambda (b) (pair? (var-bases b '()))) bs)
        (let ((n (numer e)) (d (denom e))) (list n d (number? d)))
        (let* ((al (let loop ((bs bs) (i 1) (acc '()))
                     (if (null? bs) (reverse acc)
                         (loop (cdr bs) (+ i 1)
                               (cons (list (car bs) (string->symbol (string-append "varw" (to-string i)))
                                                          (var-base-q e (car bs)))
                                     acc)))))
               (ws (map (lambda (r) (cadr r)) al))
               (e2 (var-radsub e al))
               (n0 (numer e2)) (d0 (denom e2))
               (n1 (foldl (lambda (n r)
                            (let* ((b (car r)) (w (cadr r)) (q (caddr r))
                                   (rel (- (* (denom b) (^ w q)) (numer b))))
                              (try (poly-remainder n rel w) (lambda (er) n))))
                          n0 al)))
          (list (var-back n1 al) (var-back d0 al)
                (var-monomial? d0 (append ws (append-map (lambda (r) (var-atoms (denom (car r)))) al))))))))

; N/D → полином: убрать числовой множитель при старшей струе
(define (var-normalize-lhs n)
  (let* ((js (var-jets-in n '())))
    (if (null? js) n
        (let* ((top (foldl (lambda (best j)
                             (if (> (length (cdr (hash-ref *var-jets* j))) (length (cdr (hash-ref *var-jets* best)))) j best))
                           (car js) (cdr js)))
               (c (simplify (diff top n))))
          (if (and (number? c) (not (equal? c 0)) (not (equal? (type-of c) 'float)))
              (if (and (pair? n) (equal? (car n) '+))
                  (simplify (cons '+ (map (lambda (t) (simplify (/ t c))) (cdr n))))
                  (simplify (/ n c)))
              (if (and (pair? c) (equal? (car c) '*) (number? (cadr c)) (< (cadr c) 0))
                  (if (and (pair? n) (equal? (car n) '+))
                      (simplify (cons '+ (map (lambda (t) (simplify (* -1 t))) (cdr n))))
                      (simplify (* -1 n)))
                  n))))))

(define (var-eq-lhs lhsj)
  (let ((z (simplify lhsj)))
    (if (equal? z 0) 0
        (let ((c (var-clean (together z))))
          (if (caddr c)
              (var-normalize-lhs (simplify (car c)))
              (simplify (together z)))))))

; ---------- уравнения Эйлера — Лагранжа ----------

; (euler-lagrange L (y x))              → (= ЛЧ 0), порядок до 2k: Эйлер — Пуассон
; (euler-lagrange L ((y x) (z x)))      → список уравнений
; (euler-lagrange L (u x y))            → УрЧП Эйлера — Остроградского
(define (euler-lagrange L yx)
  (let* ((specs (var-specs yx))
         (Lj (var-jetify L specs))
         (ls (var-euler Lj (length specs)))
         (eqs (map (lambda (l) (list '= (simplify (var-unjet (var-eq-lhs l) specs)) 0)) ls)))
    (if (pair? (car yx)) eqs (car eqs))))

; ---------- первые интегралы ----------

(define (var-x-of specs) (cadr (car specs)))

; число струй порядка k функции i в Lj; порядок функции — максимум
(define (var-order-of Lj i)
  (foldl (lambda (m j)
           (let ((d (hash-ref *var-jets* j)))
             (if (= (car d) i) (max m (length (cdr d))) m)))
         0 (var-jets-in Lj '())))

(define (var-xs k x) (if (= k 0) '() (cons x (var-xs (- k 1) x))))

; импульсы p_k = Σ_{j≥k} (−D)^{j−k} L_{J_j}, k = 1..n (в струях)
(define (var-momenta Lj i x n)
  (map (lambda (k)
         (foldl (lambda (acc j)
                  (+ acc (* (if (= (modulo (- j k) 2) 0) 1 -1)
                            (var-apply-D (diff (var-jet-sym i (var-xs j x)) Lj) (var-xs (- j k) x)))))
                0 (var-seq k (+ n 1))))
       (var-seq 1 (+ n 1))))

; энергия: L − Σ J_k p_k (Бельтрами при первом порядке)
(define (var-energy-jet Lj nspecs x)
  (foldl (lambda (acc i)
           (let* ((n (var-order-of Lj i)) (ps (var-momenta Lj i x n)))
             (- acc (foldl (lambda (s k) (+ s (* (var-jet-sym i (var-xs k x)) (nth ps (- k 1)))))
                           0 (var-seq 1 (+ n 1))))))
         Lj (range nspecs)))

(define (var-no-x? ej x) (equal? (simplify (diff x ej)) 0))

; сократить дробь с радикалами; квадрат — если после него радикалов нет
(define (var-polish-integral ej specs)
  (let* ((z (simplify ej)))
    (if (null? (var-bases z '()))
        (simplify (var-unjet (simplify (together z)) specs))
        (let* ((c2 (var-clean (together (* z z)))))
          (if (null? (var-bases (together (car c2)) '()))
              (let* ((n2 (simplify (car c2))) (d2 (simplify (cadr c2))))
                (simplify (var-unjet (if (number? n2) d2 (together (/ n2 d2))) specs)))
              (let ((c (var-clean (together z))))
                (simplify (var-unjet (simplify (together (/ (car c) (cadr c)))) specs))))))))

(define (var-cname k) (string->symbol (string-append "C" (to-string k))))

; (var-first-integrals L (y x)) → список (= интеграл Cn): энергия (Бельтрами), если L без x;
; импульс p_1 = Cn для функции, от которой L не зависит (одна независимая переменная)
(define (var-first-integrals L yx)
  (let* ((specs (var-specs yx)) (x (var-x-of specs)) (Lj (var-jetify L specs)))
    (if (not (= (length (cdr (car specs))) 1))
        '()
        (let* ((k 0)
               (en (if (var-no-x? Lj x)
                       (let ((e (var-polish-integral (var-energy-jet Lj (length specs) x) specs)))
                         (set! k (+ k 1))
                         (list (list '= e (var-cname k))))
                       '()))
               (mo (append-map
                    (lambda (i)
                      (let ((n (var-order-of Lj i)))
                        (if (and (>= n 1) (equal? (simplify (diff (var-jet-sym i '()) Lj)) 0))
                            (let ((p (simplify (var-unjet (simplify (car (var-momenta Lj i x n))) specs))))
                              (set! k (+ k 1))
                              (list (list '= p (var-cname k))))
                            '())))
                    (range (length specs)))))
          (append en mo)))))

; (var-natural-conditions L (y x)) → ((= p_1 0) … (= p_n 0)): выражения от x, обязаны выполняться
; на свободном конце (p_1 = ∂L/∂y′ − …; p_k для свободной (k−1)-й производной)
(define (var-natural-conditions L yx)
  (let* ((specs (list yx)) (x (cadr yx)) (Lj (var-jetify L specs)) (n (var-order-of Lj 0)))
    (map (lambda (p) (list '= (simplify (var-unjet (simplify p) specs)) 0))
         (var-momenta Lj 0 x n))))

; (var-transversality L (y x) phi): свободный конец на кривой y = φ(x):  L + (φ′ − y′)·∂L/∂y′ = 0
(define (var-transversality L yx phi)
  (let* ((specs (list yx)) (x (cadr yx)) (Lj (var-jetify L specs))
         (q (var-jet-sym 0 (list x)))
         (e (+ Lj (* (- (diff x phi) q) (diff q Lj)))))
    (list '= (simplify (var-unjet (simplify e) specs)) 0)))

; (var-noether L (y x)) → список (вид выражение): (x-translation H) — энергия (L без x),
; (shift y p) — импульс по сдвигу y → y + ε (L без y)
(define (var-noether L yx)
  (let* ((specs (var-specs yx)) (x (var-x-of specs)) (Lj (var-jetify L specs))
         (en (if (var-no-x? Lj x)
                 (list (list 'x-translation
                             (simplify (var-unjet (simplify (- 0 (var-energy-jet Lj (length specs) x))) specs))))
                 '()))
         (mo (append-map
              (lambda (i)
                (let ((n (var-order-of Lj i)))
                  (if (and (>= n 1) (equal? (simplify (diff (var-jet-sym i '()) Lj)) 0))
                      (list (list 'shift (car (nth specs i))
                                  (simplify (var-unjet (simplify (car (var-momenta Lj i x n))) specs))))
                      '())))
              (range (length specs)))))
    (append en mo)))

; ======================= CV.2: решение, сертификат, достаточные условия =======================

; ---------- объект результата ----------

(define (var-solution &rest kv) (cons 'var-solution kv))

(define (var-field r key)
  (let loop ((xs (cdr r)))
    (cond ((null? xs) #f)
          ((equal? (car xs) key) (cadr xs))
          (else (loop (cddr xs))))))

(define (var-status r) (var-field r :status))

; ---------- численные и точные проверки ----------

(define (var-at e x pt) (simplify (subst (list x pt) e)))

(define (var-replace e target value)
  (cond ((equal? e target) value)
        ((pair? e) (map (lambda (z) (var-replace z target value)) e))
        (else e)))

(define (var-has-head? e h)
  (or (equal? e h) (and (pair? e) (any? (lambda (z) (var-has-head? z h)) e))))

; точный ноль (или малый float)
(define (var-zero-exact? z)
  (let ((z (simplify z)))
    (or (equal? z 0) (equal? z 0.0)
        (and (number? z) (equal? (type-of z) 'float) (< (abs z) 1e-12)))))

; eval-num знает cosh/sinh/tanh; имя оставлено для совместимости вызовов
(define (var-hyp->exp e) e)

(define (var-closed-num e)
  (let ((v (try (eval-num (var-hyp->exp e)) (lambda (er) e))))
    (if (number? v) v #f)))

; ноль: #t (точно), numeric (замкнутое число < 1e-9), #f
(define (var-zero? e)
  (let ((z (simplify (together e))))
    (cond ((var-zero-exact? z) #t)
          (else (let ((v (var-closed-num z)))
                  (cond ((not v) #f)
                        ((< (abs v) 1e-9) 'numeric)
                        (else #f)))))))

(define (var-and3 a b)
  (cond ((or (not a) (not b)) #f)
        ((or (equal? a 'numeric) (equal? b 'numeric)) 'numeric)
        (else #t)))

(define (var-all3 xs) (foldl var-and3 #t xs))

; tanh-sinh квадратура ∫_a^b f dx (a, b — числа, f — выражение от x); ловит особенности на концах
(define (var-tanh-sinh f x a b)
  (let* ((h 0.0625) (c (/ (+ a b) 2.0)) (r (/ (- b a) 2.0)) (pi2 1.5707963267948966))
    (let loop ((k -48) (acc 0.0))
      (if (> k 48)
          (* acc h r)
          (let* ((t (* k h)) (u (* pi2 (sinh t))) (cs (cosh u)) (tt (tanh u))
                 (w (/ (* pi2 (cosh t)) (* cs cs)))
                 (xx (+ c (* r tt)))
                 (v (if (or (<= xx a) (>= xx b)) #f
                        (try (eval-num (subst (list x xx) (var-hyp->exp f))) (lambda (er) #f)))))
            (loop (+ k 1) (if (and v (number? v)) (+ acc (* w v)) acc)))))))

; ∫_a^b f dx: точная (первообразная) или численная (float); (значение . точно?)
(define (var-integral f x a b)
  (let ((F (try (integrate f x) (lambda (er) #f))))
    (if (and F (not (var-has-head? F 'integrate)))
        (let ((v (simplify (- (subst (list x b) F) (subst (list x a) F)))))
          (cons v #t))
        (let ((na (var-closed-num a)) (nb (var-closed-num b)))
          (if (and na nb) (cons (var-tanh-sinh f x na nb) #f) (cons #f #f))))))

; ---------- условия ----------

; (= (y p) v) → (p . v); иначе #f
(define (var-parse-cond c y)
  (if (and (pair? c) (equal? (car c) '=) (pair? (cadr c)) (equal? (car (cadr c)) y) (= (length (cadr c)) 2))
      (cons (cadr (cadr c)) (caddr c))
      #f))

(define (var-fixed-at conds pt)
  (any? (lambda (c) (equal? (simplify (car c)) (simplify pt))) conds))

; невязки краевых условий на кандидате rhs: значения и естественные (свободные концы) — должны быть нулями
(define (var-bc-residuals L yx a b conds rhs)
  (let* ((x (cadr yx))
         (nat (map (lambda (e) (cadr e)) (var-natural-conditions L yx)))
         (vals (map (lambda (c) (- (var-at rhs x (car c)) (cdr c))) conds))
         (ends (list a b)))
    (append vals
            (append-map
             (lambda (pt)
               (let ((ks (if (var-fixed-at conds pt) (cdr nat) nat)))
                 (map (lambda (p) (var-at (ode-subst p yx rhs) x pt)) ks)))
             ends))))

; ---------- сертификат ----------

; (var-check L (y x) a b conds cand) → #t | numeric | #f:
; кандидат (= (y x) f) или f подставлен в уравнение Эйлера — Лагранжа и краевые условия
(define (var-check L yx a b conds cand)
  (let* ((y (car yx)) (x (cadr yx))
         (rhs (if (and (pair? cand) (equal? (car cand) '=)) (caddr cand) cand))
         (cs (map (lambda (c) (var-parse-cond c y)) conds)))
    (if (any? (lambda (c) (not c)) cs)
        #f
        (let* ((eq (euler-lagrange L yx))
               (r1 (dsolve-check eq (var-hyp->exp rhs) yx))
               (r2 (var-all3 (map var-zero? (var-bc-residuals L yx a b cs rhs)))))
          (var-and3 r1 r2)))))

; ---------- достаточные условия ----------

(define (var-even-int? r) (and (integer? r) (= (modulo r 2) 0)))

; строго положительно на [a, b] (структурно или замкнутое число)
(define (var-pos? e x a)
  (let ((v (var-closed-num e)))
    (cond (v (> v 1e-9))
          ((equal? e x) (and (var-closed-num a) (> (var-closed-num a) 0)))
          ((not (pair? e)) #f)
          ((member? (car e) '(exp cosh)) #t)
          ((equal? (car e) 'sqrt) (var-pos? (cadr e) x a))
          ((and (equal? (car e) '^) (= (length e) 3)) (var-pos? (cadr e) x a))
          ((equal? (car e) '*) (every? (lambda (z) (var-pos? z x a)) (cdr e)))
          ((equal? (car e) '+) (and (every? (lambda (z) (var-nonneg? z x a)) (cdr e))
                                    (any? (lambda (z) (var-pos? z x a)) (cdr e))))
          (else #f))))

(define (var-nonneg? e x a)
  (let ((v (var-closed-num e)))
    (cond (v (>= v -1e-12))
          ((var-pos? e x a) #t)
          ((not (pair? e)) #f)
          ((and (equal? (car e) '^) (= (length e) 3))
           (or (var-even-int? (caddr e))
               (and (number? (caddr e)) (> (caddr e) 0) (var-nonneg? (cadr e) x a))))
          ((equal? (car e) 'sqrt) (var-nonneg? (cadr e) x a))
          ((member? (car e) '(+ *)) (every? (lambda (z) (var-nonneg? z x a)) (cdr e)))
          (else #f))))

; то же для дроби с радикалами: радикалы исключаются (var-clean), знаки числителя и знаменателя — структурно
(define (var-pos-expr? e x a)
  (let ((c (var-clean (together e))))
    (and (var-pos? (car c) x a) (var-pos? (cadr c) x a))))

(define (var-nonneg-expr? e x a)
  (let ((c (var-clean (together e))))
    (and (var-nonneg? (car c) x a) (var-pos? (cadr c) x a))))

; заведомо отрицательно: замкнутое число
(define (var-neg? e)
  (let ((v (var-closed-num e))) (and v (< v -1e-9))))

; (var-legendre L yx a b extremal) → strict | nonstrict | negative | unknown (∂²L/∂y′² на экстремали)
(define (var-legendre L yx a b extremal)
  (let* ((specs (list yx)) (x (cadr yx))
         (rhs (if (and (pair? extremal) (equal? (car extremal) '=)) (caddr extremal) extremal))
         (Lj (var-jetify L specs)) (q (var-jet-sym 0 (list x)))
         (P (ode-subst (var-unjet (simplify (diff q (diff q Lj))) specs) yx rhs)))
    (cond ((var-pos-expr? P x a) (quote strict))
          ((var-neg? P) 'negative)
          ((var-nonneg-expr? P x a) (quote nonstrict))
          (else 'unknown))))

(define (var-subsets xs)
  (if (null? xs) '(())
      (let ((r (var-subsets (cdr xs))))
        (append r (map (lambda (s) (cons (car xs) s)) r)))))

(define (var-drop-col row j)
  (let drop ((r row) (k 0) (out '()))
    (cond ((null? r) (reverse out))
          ((= k j) (drop (cdr r) (+ k 1) out))
          (else (drop (cdr r) (+ k 1) (cons (car r) out))))))

(define (var-det m)
  (if (= (length m) 1)
      (car (car m))
      (let loop ((j 0) (acc 0))
        (if (>= j (length m))
            acc
            (loop (+ j 1)
                  (+ acc (* (if (= (modulo j 2) 0) 1 -1) (nth (car m) j)
                            (var-det (map (lambda (row) (var-drop-col row j)) (cdr m))))))))))

; гессиан L по всем струям положительно полуопределён (все главные миноры ≥ 0) → #t;
; доказанно отрицательный минор → #f; иначе unknown
(define (var-convex? L yx)
  (let* ((specs (var-specs yx)) (x (var-x-of specs)) (Lj (var-jetify L specs))
         (js (var-jets-in Lj '()))
         (idx (var-seq 0 (length js)))
         (H (map (lambda (ji) (map (lambda (jj) (simplify (diff jj (diff ji Lj)))) js)) js))
         (subs (filter (lambda (s) (pair? s)) (var-subsets idx)))
         (minors (map (lambda (s)
                        (simplify (together (var-det (map (lambda (i) (map (lambda (j) (nth (nth H i) j)) s)) s)))))
                      subs)))
    (cond ((null? js) #t)
          ((any? (lambda (m) (var-neg? m)) minors) #f)
          ((every? (lambda (m) (var-nonneg-expr? m x #f)) minors) #t)
          (else 'unknown))))

; символы-параметры корня (кроме pi, %i, e)
(define (var-free-params e acc)
  (cond ((symbol? e) (if (or (member? e '(pi %i e)) (member? e acc)) acc (append acc (list e))))
        ((pair? e) (foldl (lambda (a z) (var-free-params z a)) acc (cdr e)))
        (else acc)))

(define (var-root-values r syms)
  (if (null? syms)
      (let ((v (var-closed-num r))) (if v (list v) '()))
      (let loop ((k -40) (acc '()))
        (if (> k 40)
            acc
            (let ((v (var-closed-num (subst (list (car syms) k) r))))
              (loop (+ k 1) (if v (cons v acc) acc)))))))

; первый нуль u(x) на (a, b]: сначала сетка (смена знака), затем точные корни через solve
(define (var-first-zero u x a b)
  (let* ((na (var-closed-num a)) (nb (var-closed-num b)))
    (if (not (and na nb))
        'unknown
        (let ((scan
               (let loop ((i 1) (prev #f))
                 (if (> i 240)
                     #f
                     (let* ((xi (+ na (* (- nb na) (/ i 240.0))))
                            (v (try (eval-num (subst (list x xi) (var-hyp->exp u))) (lambda (er) #f))))
                       (cond ((not (number? v)) (loop (+ i 1) prev))
                             ((< (abs v) 1e-9) (list 'conjugate xi))
                             ((and prev (< (* prev v) 0)) (list 'conjugate xi))
                             (else (loop (+ i 1) v))))))))
          (if scan
              scan
              (let ((rs (try (solve (list '= u 0) x) (lambda (er) #f))))
                (if (not (and rs (equal? (type-of rs) 'set)))
                    'unknown
                    (let* ((roots (set->list rs))
                           (syms (foldl (lambda (acc r) (var-free-params r acc)) '() roots)))
                      (cond ((null? roots) 'unknown)
                            ((> (length syms) 1) 'unknown)
                            (else
                             (let* ((vals (append-map (lambda (r) (var-root-values r syms)) roots))
                                    (big (filter (lambda (v) (> v (+ na 1e-9))) vals)))
                               (cond ((null? vals) 'unknown)
                                     ((and (pair? big) (<= (foldl min (car big) (cdr big)) (+ nb 1e-9)))
                                      (list 'conjugate (foldl min (car big) (cdr big))))
                                     (else 'none)))))))))))))

; (var-jacobi L yx a b extremal) → none (нет сопряжённой точки в (a, b]) | (conjugate c) | unknown
; уравнение Якоби (P u′)′ − Q u = 0, P = L_{y′y′}, Q = L_{yy} − D L_{yy′}; u(a) = 0, u′(a) = 1
(define (var-jacobi L yx a b extremal)
  (let* ((specs (list yx)) (x (cadr yx))
         (rhs (if (and (pair? extremal) (equal? (car extremal) '=)) (caddr extremal) extremal))
         (Lj (var-jetify L specs))
         (q0 (var-jet-sym 0 '())) (q (var-jet-sym 0 (list x)))
         (Pj (simplify (diff q (diff q Lj))))
         (Qj (simplify (- (diff q0 (diff q0 Lj)) (var-D (diff q0 (diff q Lj)) x))))
         (P (ode-subst (var-unjet Pj specs) yx rhs))
         (Q (ode-subst (var-unjet Qj specs) yx rhs))
         (u (list 'varu x))
         (eq (list '= (simplify (list '+ (list '* P (list 'diff (list 'diff u x) x))
                                      (list '* (diff x P) (list 'diff u x))
                                      (list '* -1 Q u)))
                   0))
         (r (try (dsolve eq (list 'varu x)) (lambda (er) #f))))
    (if (not (and r (equal? (ode-status r) 'ok) (pair? (ode-solutions r))))
        'unknown
        (let* ((sol (car (ode-solutions r))) (urhs (caddr sol)) (cs (var-field r :constants)))
          (if (not (= (length cs) 2))
              'unknown
              (let* ((e1 (var-at urhs x a))
                     (e2 (var-at (diff x urhs) x a))
                     (s (try (solve (list (list '= e1 0) (list '= e2 1)) cs) (lambda (er) #f)))
                     (sl (if (and s (equal? (type-of s) 'set)) (set->list s) '())))
                (if (null? sl)
                    'unknown
                    (var-first-zero (var-subst-solution (car sl) urhs) x a b))))))))

(define (var-subst-solution rules rhs)
  (simplify (subst (map (lambda (e) (list (cadr e) (caddr e))) rules) rhs)))

; (var-classify L yx a b extremal fixed?) → (var-classification :kind minimum|extremal :basis … :legendre … :jacobi … :convex …)
; «минимум» — только при доказанной выпуклости (глобальный) либо Лежандр strict + Якоби none при двух закреплённых
; концах (слабый); иначе «экстремаль»
(define (var-classify L yx a b extremal fixed?)
  (let* ((specs (list yx)) (Lj (var-jetify L specs)) (n (var-order-of Lj 0))
         (cvx (var-convex? L yx)))
    (cond ((true? cvx)
           (list 'var-classification :kind 'minimum :basis 'convex :legendre 'n/a :jacobi 'n/a :convex #t))
          ((not (= n 1))
           (list 'var-classification :kind 'extremal :basis 'order :legendre 'n/a :jacobi 'n/a :convex cvx))
          (else
           (let* ((lg (var-legendre L yx a b extremal))
                  (jc (if (and fixed? (equal? lg 'strict)) (var-jacobi L yx a b extremal) 'skipped))
                  (ok (and fixed? (equal? lg 'strict) (equal? jc 'none))))
             (list 'var-classification
                   :kind (if ok 'minimum 'extremal)
                   :basis (if ok 'legendre-jacobi 'none)
                   :legendre lg :jacobi jc :convex cvx))))))

; ---------- решение ----------

; наборы значений констант, обращающие невязки в нули
(define (var-solve-constants res consts)
  (cond ((null? consts) (if (every? (lambda (r) (true? (var-zero? r))) res) (list '()) '()))
        (else
         (let* ((eqs (map (lambda (r) (list '= r 0)) res))
                (s (try (solve eqs consts) (lambda (er) #f))))
           (if (and s (equal? (type-of s) 'set)) (set->list s) '())))))

; первый интеграл → разрешить относительно y′ → квадратура: неявные соотношения (по возможности)
(define (var-reduce L yx)
  (let* ((x (cadr yx)) (fis (var-first-integrals L yx)))
    (if (null? fis)
        '()
        (let* ((F (cadr (car fis))) (K (caddr (car fis)))
               (vy 'varyy) (vq 'varqq)
               (Fs (var-replace (var-replace F (list 'diff yx x) vq) yx vy))
               (s (try (solve (list '= Fs K) vq) (lambda (er) #f))))
          (if (not (and s (equal? (type-of s) 'set)))
              '()
              (let* ((branches (set->list s))
                     (ints (map (lambda (g)
                                  (let ((I (try (integrate (simplify (list '/ 1 g)) vy) (lambda (er) #f))))
                                    (if (and I (not (var-has-head? I 'integrate))) I #f)))
                                branches)))
                (if (or (null? ints) (any? (lambda (i) (not i)) ints))
                    '()
                    (let ((C2 (var-cname 2)))
                      (if (and (= (length ints) 2) (equal? (simplify (+ (car ints) (cadr ints))) 0))
                          (list (list '= (list '^ (list '+ x C2) 2)
                                      (var-replace (simplify (list '^ (car ints) 2)) vy yx)))
                          (map (lambda (I) (list '= (list '+ x C2) (var-replace I vy yx))) ints))))))))))

; (variational-solve L (y x) a b conds): экстремаль функционала ∫_a^b L dx; conds — список (= (y p) v);
; конец без условия — свободный (естественное условие). Результат (var-solution :status … :kind … …)
(define (variational-solve L yx a b conds)
  (let* ((y (car yx)) (x (cadr yx))
         (cs (map (lambda (c) (var-parse-cond c y)) conds)))
    (if (any? (lambda (c) (not c)) cs)
        (var-solution :status 'unknown :reason "условия: только (= (y точка) значение)")
        (let* ((eq (euler-lagrange L yx))
               (fis (var-first-integrals L yx))
               (r (try (dsolve eq yx) (lambda (er) #f)))
               (sols (if (and r (equal? (ode-status r) 'ok)) (ode-solutions r) '()))
               (consts (if r (var-field r :constants) '()))
               (cands
                (append-map
                 (lambda (s)
                   (if (and (pair? s) (equal? (car s) '=) (equal? (cadr s) yx))
                       (let* ((rhs (caddr s))
                              (res (var-bc-residuals L yx a b cs rhs))
                              (ans (var-solve-constants res consts)))
                         (map (lambda (rules) (var-subst-solution rules rhs)) ans))
                       '()))
                 sols))
               (good (filter (lambda (c) (not (equal? (var-check L yx a b conds c) #f))) cands)))
          (if (pair? good)
              (let* ((c (car good))
                     (chk (var-check L yx a b conds c))
                     (fixed? (and (var-fixed-at cs a) (var-fixed-at cs b)))
                     (cl (var-classify L yx a b c fixed?)))
                (var-solution :status 'ok :kind (var-field cl :kind) :equation eq
                              :extremal (list '= yx c) :alternatives (cdr good)
                              :free-constants (filter (lambda (k) (var-has-head? c k)) consts)
                              :first-integrals fis :check chk :classification cl))
              (let ((imp (var-reduce L yx)))
                (var-solution :status (if (or (pair? sols) (pair? imp)) 'family 'unknown)
                              :kind 'extremal :equation eq :first-integrals fis
                              :general (if (pair? sols) sols imp)
                              :reason "константы по краевым условиям не найдены или общее решение не получено; проверка кандидата — var-check"
                              :check 'none)))))))

; ---------- изопериметрические задачи ----------

(define (var-lam L G) (list '+ L (list '* 'lam G)))

; (var-isoperimetric-check L G yx a b conds ell cand lam) → #t | numeric | #f:
; кандидат удовлетворяет уравнению для L + lam·G, краевым условиям и ограничению ∫G = ell
(define (var-isoperimetric-check L G yx a b conds ell cand lam)
  (let* ((x (cadr yx))
         (rhs (if (and (pair? cand) (equal? (car cand) '=)) (caddr cand) cand))
         (Lam (simplify (subst (list 'lam lam) (var-lam L G))))
         (c1 (var-check Lam yx a b conds rhs))
         (Ig (var-integral (ode-subst G yx rhs) x a b))
         (c2 (if (car Ig)
                 (if (cdr Ig)
                     (var-zero? (- (car Ig) ell))
                     (let ((ne (var-closed-num ell)))
                       (if (and ne (< (abs (- (car Ig) ne)) 1e-6)) 'numeric #f)))
                 #f)))
    (var-and3 c1 c2)))

; (var-isoperimetric L G (y x) a b conds ell): min ∫L при ∫G = ell; уравнение Эйлера для L + lam·G
; (параметр — символ `lam`); константы — по краевым условиям, lam — из ограничения. Результат var-solution
(define (var-isoperimetric L G yx a b conds ell)
  (let* ((y (car yx)) (x (cadr yx)) (Lam (var-lam L G))
         (cs (map (lambda (c) (var-parse-cond c y)) conds)))
    (if (any? (lambda (c) (not c)) cs)
        (var-solution :status 'unknown :reason "условия: только (= (y точка) значение)")
        (let* ((eq (euler-lagrange Lam yx))
               (fis (var-first-integrals Lam yx))
               (r (try (dsolve eq yx) (lambda (er) #f)))
               (sols (if (and r (equal? (ode-status r) 'ok)) (ode-solutions r) '()))
               (consts (if r (var-field r :constants) '()))
               (cands
                (append-map
                 (lambda (s)
                   (if (and (pair? s) (equal? (car s) '=) (equal? (cadr s) yx))
                       (let* ((rhs (caddr s))
                              (res (var-bc-residuals Lam yx a b cs rhs))
                              (ans (var-solve-constants res consts)))
                         (append-map
                          (lambda (rules)
                            (let* ((cand (var-subst-solution rules rhs))
                                   (Ig (var-integral (ode-subst G yx cand) x a b)))
                              (if (not (car Ig))
                                  '()
                                  (let ((ls (try (solve (list '= (car Ig) ell) 'lam) (lambda (er) #f))))
                                    (if (and ls (equal? (type-of ls) 'set))
                                        (map (lambda (lv) (list (simplify (subst (list 'lam lv) cand)) lv))
                                             (set->list ls))
                                        '())))))
                          ans))
                       '()))
                 sols))
               (good (filter (lambda (c)
                               (not (equal? (var-isoperimetric-check L G yx a b conds ell (car c) (cadr c)) #f)))
                             cands)))
          (if (pair? good)
              (let ((c (car good)))
                (var-solution :status 'ok :kind 'extremal :equation eq :first-integrals fis
                              :extremal (list '= yx (car c)) :lam (cadr c)
                              :check (var-isoperimetric-check L G yx a b conds ell (car c) (cadr c))
                              :alternatives (cdr good)))
              (let ((imp (var-reduce Lam yx)))
                (var-solution :status (if (or (pair? sols) (pair? imp)) 'family 'unknown)
                              :kind 'extremal :equation eq :first-integrals fis
                              :general (if (pair? sols) sols imp)
                              :reason "lam и константы не найдены; проверка кандидата — var-isoperimetric-check"
                              :check 'none)))))))

; ---------- первый интеграл на параметрической кривой ----------

; (var-check-first-integral F (y x) xt yt t) → (статус значение): F — интеграл (= F C) или выражение от (y x) и
; (diff (y x) x); на кривой x = xt(t), y = yt(t) значение не должно зависеть от t. Статус #t | numeric | #f
(define (var-check-first-integral F yx xt yt t)
  (let* ((x (cadr yx)) (e (if (and (pair? F) (equal? (car F) '=)) (cadr F) F))
         (slope (simplify (list '/ (diff t yt) (diff t xt))))
         (v (simplify (var-replace (var-replace e (list 'diff yx x) slope) yx yt)))
         (d (simplify (together (diff t v)))))
    (if (equal? d 0)
        (list #t v)
        ; численно: параметры (кроме t) → 7/5, t — в нескольких точках; значение постоянно?
        (let* ((ps (filter (lambda (s) (not (equal? s t))) (var-free-params v '())))
               (v1 (subst (map (lambda (s) (list s 7/5)) ps) v))
               (pts '(1/3 1/2 2/3 4/5))
               (vals (map (lambda (p) (var-closed-num (subst (list t p) v1))) pts)))
          (if (and (every? (lambda (z) z) vals)
                   (every? (lambda (z) (< (abs (- z (car vals))) 1e-9)) vals))
              (list 'numeric v)
              (list #f v))))))
