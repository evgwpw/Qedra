; linear.lisp — линейные ОДУ с постоянными коэффициентами (шаг ODE.3)
; Однородные: характеристический многочлен, кратности, комплексные корни → вещественная форма.
; Неоднородные: вариация постоянных (n = 2); вронскиан — часть сертификата.
(module ode)

; ---------- коэффициенты и свободный член ----------

; (lo-coeffs eq y x) → (cs g): cs — от старшей производной к y (после нормировки a_n = 1), g — правая часть
(define (lo-coeffs eq y x)
  (let* ((n (ode-order eq y x))
         (e (ode-normalize eq))
         (ds (map (lambda (k) (if (= k 0) (list y x) (ode-nth-deriv y x k)))
                  (range (+ n 1))))
         (as (map (lambda (d)
                    (let ((r (ode-coeff-of d e y x)))
                      (and r (number? (car r)) (car r))))
                  ds)))
    (if (any? (lambda (a) (not a)) as)
        #f
        (let* ((an (car (reverse as)))
               (cs (map (lambda (a) (simplify (list '/ a an))) as))
               (g (simplify (foldl (lambda (acc p) (list '- acc (list '* (car p) (cadr p))))
                                   e (map2 list as ds)))))
          (if (or (ode-y-node-any? g y x) (ode-mentions-sym? g y))
              #f
              (list cs g))))))

; ---------- характеристический многочлен и базис ----------

(define (lo-charpoly cs)
  (let ((n (- (length cs) 1)))
    (foldl (lambda (acc k) (list '+ acc (list '* (nth cs k) (list '^ '%l k))))
           0 (range (+ n 1)))))

(define (lo-exp-series r m x)
  (map (lambda (j) (simplify (list '* (list '^ x j) (list 'exp (list '* r x)))))
       (range m)))

(define (lo-trig-series alpha beta m x)
  (append
   (map (lambda (j) (simplify (list '* (list '^ x j) (list 'exp (list '* alpha x))
                                       (list 'cos (list '* beta x))))) (range m))
   (map (lambda (j) (simplify (list '* (list '^ x j) (list 'exp (list '* alpha x))
                                       (list 'sin (list '* beta x))))) (range m))))

(define (lo-factor-basis f m x)
  (let ((d (degree f '%l)))
    (cond ((= d 1)
           (let* ((a (coeff f '%l 1)) (b (coeff f '%l 0))
                  (r (simplify (list '/ (list '- 0 b) a))))
             (lo-exp-series r m x)))
          ((= d 2)
           (let* ((a (coeff f '%l 2)) (b (coeff f '%l 1)) (c (coeff f '%l 0))
                  (D (simplify (list '- (list '^ b 2) (list '* 4 a c)))))
             (if (and (number? D) (< D 0))
                 (let* ((alpha (simplify (list '/ (list '- 0 b) (list '* 2 a))))
                        (beta (simplify (list '/ (list 'sqrt (list '- 0 D)) (list '* 2 a)))))
                   (lo-trig-series alpha beta m x))
                 (append-map (lambda (r) (lo-exp-series r m x))
                             (set->list (solve (list '= f 0) '%l))))))
          (else
           (append-map (lambda (r) (lo-exp-series r m x))
                       (set->list (solve (list '= f 0) '%l)))))))

(define (lo-basis cs x)
  (let* ((fl (ode-quiet (lambda () (factor-list (expand (lo-charpoly cs))))))
         (factors (cdr fl)))
    (ode-quiet (lambda ()
                 (append-map (lambda (fm) (lo-factor-basis (car fm) (cadr fm) x)) factors)))))

; ---------- вронскиан и однородное решение ----------

(define (lo-w2 y1 y2 x)
  (simplify (list '- (list '* y1 (diff 'x y2)) (list '* (diff 'x y1) y2))))

; корни с кратностями для пояснения: «λ = 1 (кратность 1), λ = 2 (кратность 1)»
(define (lo-roots-str fl)
  (ode-mp-join
   (append-map
    (lambda (fm)
      (let* ((f (car fm)) (m (cadr fm))
             (rs (ode-quiet (lambda ()
                              (try (set->list (solve (list '= f 0) '%l)) (lambda (e) '()))))))
        (if (null? rs)
            (list (string-append (ode-mp f) " = 0 (кратность " (to-string m) ")"))
            (map (lambda (r)
                   (string-append "λ = " (ode-mp r) " (кратность " (to-string m) ")"))
                 rs))))
    fl)))

; частота правой части для пояснения: «λ = 3 (кратность 0)» / «λ = 1 + 2i (кратность 1 ⇒ резонанс)»
(define (lo-freq-str key m)
  (let ((a (car key)) (b (cadr key)))
    (string-append "λ = " (ode-mp (if (ode-zero? b) a (simplify (list '+ a (list '* b 'i)))))
                   " (кратность " (to-string m) (if (> m 0) " ⇒ резонанс" "") ")")))

; уравнение по коэффициентам cs: Σ cs[k]·y⁽ᵏ⁾ = 0 (для сертификата однородного решения)
(define (lo-eq-of-cs cs y x)
  (let* ((n (- (length cs) 1))
         (ds (map (lambda (k) (if (= k 0) (list y x) (ode-nth-deriv y x k)))
                  (range (+ n 1)))))
    (list '= (simplify (foldl (lambda (acc p) (list '+ acc (list '* (car p) (cadr p))))
                              0 (map2 list cs ds)))
          0)))

(define (lo-hom eq y x cs)
  (let* ((cp (lo-charpoly cs))
         (fl (ode-quiet (lambda () (factor-list (expand cp)))))
         (fs (lo-basis cs x))
         (n (length fs)))
    (if (not (= n (- (length cs) 1)))
        #f
        (let ((W (if (= n 2) (ode-quiet (lambda () (lo-w2 (car fs) (cadr fs) x))) 1)))
          (if (ode-zero? W)
              #f
              (let* ((cnames (map (lambda (k) (string->symbol (string-append "C" (to-string (+ k 1)))))
                                  (range n)))
                     (rhs (simplify (foldl (lambda (acc p) (list '+ acc (list '* (car p) (cadr p))))
                                           0 (map2 list cnames fs))))
                     (sol (list '= (list y x) rhs))
                     (ok (ode-quiet (lambda () (dsolve-check (lo-eq-of-cs cs y x) sol (list y x))))))
                (if ok
                    (with-step ('ode-lo-hom "Однородное уравнение с постоянными коэффициентами" eq
                                :comment (string-append "P(λ) = " (ode-mp (expand cp))
                                                        "; корни: " (lo-roots-str (cdr fl))
                                                        "; ФСР: " (ode-mp-list fs)
                                                        (if (= n 2) (string-append "; W = " (ode-mp W)) ""))
                                :after (lambda (r) (ode-field r :solutions)))
                      (ode-solution 'general (list sol) cnames '() 'ok 'const-coeff #t))
                    (error "lo-solve: однородное решение не прошло проверку"))))))))

; ---------- вариация постоянных (n = 2) ----------

(define (lo-variation eq y x cs g)
  (let* ((fs (lo-basis cs x)))
    (if (not (= (length fs) 2))
        #f
        (let* ((y1 (car fs)) (y2 (cadr fs)) (W (lo-w2 y1 y2 x)))
          (if (ode-zero? W)
              #f
              (let* ((u1 (ode-quiet (lambda () (integrate (simplify (list '/ (list '* y2 g) W)) x))))
                     (u2 (ode-quiet (lambda () (integrate (simplify (list '/ (list '* y1 g) W)) x))))
                     (yp (simplify (list '+ (list '* (list '- 0 y1) u1) (list '* y2 u2))))
                     (rhs (simplify (list '+ (list '* 'C1 y1) (list '* 'C2 y2) yp)))
                     (sol (list '= (list y x) rhs)))
                (if (dsolve-check eq sol (list y x))
                    (with-step ('ode-lo-var "Вариация постоянных" g
                                :comment (string-append "ФСР: y₁ = " (ode-mp y1) ", y₂ = " (ode-mp y2)
                                                        "; W = " (ode-mp W)
                                                        "; u₁ = ∫y₂·g/W = " (ode-mp u1)
                                                        ", u₂ = ∫y₁·g/W = " (ode-mp u2)
                                                        "; y = C₁y₁ + C₂y₂ − y₁u₁ + y₂u₂")
                                :after (lambda (r) (ode-field r :solutions)))
                      (ode-solution 'general (list sol) (list 'C1 'C2) '() 'ok 'variation #t))
                    #f)))))))

; ---------- неопределённые коэффициенты: резонанс (шаг ODE.5b) ----------
; Правая часть — сумма членов x^m·e^{ax}, x^m·e^{ax}·cos bx, x^m·e^{ax}·sin bx.
; Пробное решение того же вида с многочленом степени deg + k, где k — кратность λ = a + bi
; как корня характеристического многочлена (резонанс). Коэффициенты — из линейной системы:
; остаток раскладывается по частотам (e^{(a+bi)x}·x^j), коэффициент каждой частоты = 0.

; ---- комплексные пары (re . im) ----
(define (lo-cx+ p q)
  (cons (simplify (list '+ (car p) (car q))) (simplify (list '+ (cdr p) (cdr q)))))
(define (lo-cx* p q)
  (cons (simplify (list '- (list '* (car p) (car q)) (list '* (cdr p) (cdr q))))
        (simplify (list '+ (list '* (car p) (cdr q)) (list '* (cdr p) (car q))))))
(define (lo-cx-zero? p) (and (ode-zero? (car p)) (ode-zero? (cdr p))))

; P(λ) = Σ cs[k]·λ^k (cs[k] — коэффициент при y⁽ᵏ⁾), схема Горнера
(define (lo-poly-cx cs lam)
  (let ((ks (reverse (range (length cs)))))
    (let loop ((xs ks) (acc (cons 0 0)))
      (cond ((null? xs) acc)
            (else (loop (cdr xs) (lo-cx+ (lo-cx* acc lam) (cons (nth cs (car xs)) 0))))))))

(define (lo-cs-deriv cs)
  (map (lambda (k) (simplify (list '* (+ k 1) (nth cs (+ k 1)))))
       (range (max 0 (- (length cs) 1)))))

(define (lo-cs-all-zero? cs) (every? (lambda (c) (ode-zero? c)) cs))

; кратность λ как корня P (λ ≠ 0 учитывается автоматически: P(0) = cs[0])
(define (lo-cx-mult cs lam)
  (let loop ((c cs) (m 0))
    (cond ((> m (length cs)) m)
          ((lo-cs-all-zero? c) m)
          ((lo-cx-zero? (lo-poly-cx c lam)) (loop (lo-cs-deriv c) (+ m 1)))
          (else m))))


; ---- разбор правой части: x^m·e^{ax}·(cos|sin)(bx) ----

(define (lo-uc-occ? e s)
  (cond ((equal? e s) #t)
        ((pair? e) (any? (lambda (z) (lo-uc-occ? z s)) e))
        (else #f)))

(define (lo-uc-summands e)
  (let ((v (expand e)))
    (if (and (pair? v) (equal? (car v) '+)) (cdr v) (list v))))

(define (lo-uc-factors t)
  (cond ((and (pair? t) (equal? (car t) '*)) (append-map lo-uc-factors (cdr t)))
        (else (list t))))

; e = a·x + b → (a . b); #f — не линейно по x
(define (lo-uc-split-lin e x)
  (cond ((not (lo-uc-occ? e x)) (cons 0 e))
        ((equal? e x) (cons 1 0))
        ((and (pair? e) (equal? (car e) '+))
         (let loop ((ts (cdr e)) (a 0) (b 0))
           (if (null? ts) (cons (simplify a) (simplify b))
               (let ((s (lo-uc-split-lin (car ts) x)))
                 (if (not s) #f
                     (loop (cdr ts) (simplify (list '+ a (car s)))
                           (simplify (list '+ b (cdr s)))))))))
        ((and (pair? e) (equal? (car e) '*))
         (let* ((fs (cdr e))
                (w (filter (lambda (z) (lo-uc-occ? z x)) fs))
                (c (filter (lambda (z) (not (lo-uc-occ? z x))) fs)))
           (if (not (= (length w) 1))
               #f
               (let ((s (lo-uc-split-lin (car w) x)) (k (foldl * 1 c)))
                 (if (not s) #f
                     (cons (simplify (list '* k (car s)))
                           (simplify (list '* k (cdr s)))))))))
        (else #f)))

; a, если аргумент = a·x (без фазы); иначе #f
(define (lo-uc-lin0 e x)
  (let ((p (lo-uc-split-lin e x)))
    (and p (ode-zero? (cdr p)) (not (ode-zero? (car p))) (car p))))

(define (lo-uc-powx f x)
  (cond ((equal? f x) 1)
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3) (equal? (cadr f) x)
              (integer? (caddr f)) (> (caddr f) 0)) (caddr f))
        (else #f)))

; терм → (степень exp-коэффициент триг-ключ коэффициент); #f — не разобрать
(define (lo-uc-decompose t x)
  (let loop ((fs (lo-uc-factors t)) (pw 0) (ek #f) (tk #f) (cf 1) (ok #t))
    (cond ((not ok) #f)
          ((null? fs) (list pw ek tk (simplify cf)))
          (else
           (let* ((f (car fs)) (k (lo-uc-powx f x)))
             (cond (k (loop (cdr fs) (+ pw k) ek tk cf ok))
                   ((and (pair? f) (equal? (car f) 'exp) (= (length f) 2))
                    (let ((a (lo-uc-lin0 (cadr f) x)))
                      (if (and a (not ek))
                          (loop (cdr fs) pw (cons 'exp a) tk cf ok)
                          (loop (cdr fs) pw ek tk cf #f))))
                   ((and (pair? f) (member? (car f) '(sin cos)) (= (length f) 2))
                    (let ((b (lo-uc-lin0 (cadr f) x)))
                      (if (and b (not tk))
                          (loop (cdr fs) pw ek (cons (car f) b) cf ok)
                          (loop (cdr fs) pw ek tk cf #f))))
                   (else (loop (cdr fs) pw ek tk (list '* cf f) ok))))))))

; разобранный терм → ключ частоты (a b)
(define (lo-uc-key d)
  (list (if (cadr d) (cdr (cadr d)) 0) (if (caddr d) (cdr (caddr d)) 0)))

; правая часть → ((ключ максимальная-степень) …) или #f
(define (lo-uc-groups g x)
  (let loop ((ts (lo-uc-summands g)) (acc '()))
    (if (null? ts)
        (reverse acc)
        (let* ((d (lo-uc-decompose (car ts) x)))
          (if (not d)
              #f
              (let* ((key (lo-uc-key d))
                     (pw (car d))
                     (old (assoc key acc))
                     (acc2 (if old
                               (map (lambda (p)
                                      (if (equal? (car p) key)
                                          (list key (max (cadr p) pw))
                                          p))
                                    acc)
                               (append acc (list (list key pw))))))
                (loop (cdr ts) acc2)))))))

; ---- пробное решение: ячейки (неизвестная . вид(x)) ----

; степень многочлена = deg + кратность λ как корня P (резонанс)
(define (lo-uc-trial key pw cs x)
  (let* ((a (car key)) (b (cadr key))
         (m (lo-cx-mult cs (cons a b)))
         (d (+ pw m))
         (js (range (+ d 1)))
         (ek (simplify (list 'exp (list '* a x))))
         (shapes (if (ode-zero? b)
                     (map (lambda (j) (simplify (list '* (list '^ x j) ek))) js)
                     (append
                      (map (lambda (j) (simplify (list '* (list '^ x j) ek
                                                       (list 'cos (list '* b x))))) js)
                      (map (lambda (j) (simplify (list '* (list '^ x j) ek
                                                       (list 'sin (list '* b x))))) js))))
         (us (map (lambda (i) (gensym "odK")) (range (length shapes)))))
    (map2 cons us shapes)))

(define (lo-uc-remove1 v l)
  (cond ((null? l) '())
        ((equal? (car l) v) (cdr l))
        (else (cons (car l) (lo-uc-remove1 v (cdr l))))))

; произведение cf → (неизвестная . коэффициент-без-неизвестной) либо (0 . cf)
(define (lo-uc-cell cf us)
  (let* ((fs (if (and (pair? cf) (equal? (car cf) '*)) (cdr cf) (list cf)))
         (hit (filter (lambda (z) (member? z us)) fs)))
    (cond ((null? hit) (cons 0 cf))
          ((= (length hit) 1)
           (cons (car hit) (simplify (foldl * 1 (lo-uc-remove1 (car hit) fs)))))
          (else #f))))

; остаток → alist идентификатор (ключ степень вид) → список ячеек (неизвестная . коэффициент)
(define (lo-uc-collect res us x)
  (let loop ((ts (lo-uc-summands res)) (acc '()))
    (if (null? ts)
        (reverse acc)
        (let* ((d (lo-uc-decompose (car ts) x)))
          (if (not d)
              #f
              (let* ((key (lo-uc-key d))
                     (kind (if (caddr d) (car (caddr d)) 'none))
                     (ident (list key (car d) kind))
                     (cell (lo-uc-cell (caddr (cdr d)) us)))
                (if (not cell)
                    #f
                    (let ((old (assoc ident acc)))
                      (loop (cdr ts)
                            (if old
                                (map (lambda (p) (if (equal? (car p) ident)
                                                     (list ident (append (cadr p) (list cell)))
                                                     p))
                                     acc)
                                (append acc (list (list ident (list cell))))))))))))))

; уравнение по ячейкам: Σ coef_u·u + свободная часть = 0
(define (lo-uc-eq-of cells us)
  (let* ((vars (filter (lambda (u) (not (equal? u 0))) us))
         (coef (lambda (u)
                 (simplify (foldl (lambda (a c) (if (equal? (car c) u)
                                                     (list '+ a (cdr c)) a))
                                  0 cells))))
         (free (coef 0)))
    (list '= (simplify (foldl (lambda (a u) (list '+ a (list '* (coef u) u))) 0 vars))
          (simplify (list '- 0 free)))))

; значения неизвестных из списка связываний ((= u v) …); свободная (= u u) или не упомянутая — 0
(define (lo-uc-val u binds)
  (let loop ((bs binds))
    (cond ((null? bs) 0)
          ((and (pair? (car bs)) (equal? (cadr (car bs)) u) (not (equal? (caddr (car bs)) u)))
           (caddr (car bs)))
          (else (loop (cdr bs))))))

(define (lo-uc-apply trial binds)
  (simplify (foldl (lambda (acc c)
                     (list '+ acc (list '* (lo-uc-val (car c) binds) (cdr c))))
                   0 trial)))

; уравнения по всем группам остатка
(define (lo-uc-eqs col us)
  (let loop ((cs col) (acc '()))
    (if (null? cs)
        (reverse acc)
        (let ((e (try (lo-uc-eq-of (cadr (car cs)) us) (lambda (err) #f))))
          (if e (loop (cdr cs) (cons e acc)) #f)))))

; ---- сборка: пробное решение, система, подстановка, сертификат ----
(define (lo-undet eq y x cs g)
  (let ((gs (lo-uc-groups g x)))
    (if (not gs)
        #f
        (let* ((cells (append-map (lambda (gr) (lo-uc-trial (car gr) (cadr gr) cs x)) gs))
               (us (map car cells))
               (trial (simplify (foldl (lambda (acc c) (list '+ acc (list '* (car c) (cdr c))))
                                       0 cells)))
               (mult (map (lambda (gr) (lo-cx-mult cs (cons (car (car gr)) (cadr (car gr))))) gs))
               (ubinds (map2 (lambda (u k) (list u (ode-letter k)))
                             us (range (length us))))
               (yp (ode-quiet
                    (lambda ()
                      (let* ((res (ode-subst (ode-normalize eq) (list y x) trial))
                             (col (lo-uc-collect (expand res) us x))
                             (eqs (and col (lo-uc-eqs col us)))
                             (sol (and eqs (try (set->list (solve eqs us)) (lambda (e) #f)))))
                        (if (or (not sol) (null? sol))
                            #f
                            (let ((v (lo-uc-apply cells (car sol))))
                              (if (dsolve-check eq (list '= (list y x) v) (list y x)) v #f))))))))
          (if (not yp)
              #f
              (with-step ('ode-lo-undet "Метод неопределённых коэффициентов" g
                          :comment (string-append "частоты правой части: "
                                                  (ode-mp-join (map2 lo-freq-str (map car gs) mult))
                                                  "; пробное: " (ode-mp* ubinds trial)
                                                  "; неизвестных коэффициентов: " (to-string (length us)))
                          :after (lambda (r) (ode-field r :solutions)))
                (let ((hom (lo-hom eq y x cs)))
                  (if (not hom)
                      #f
                      (let* ((h (caddr (car (ode-solutions hom))))
                             (full (simplify (list '+ h yp))))
                        (ode-solution 'general
                                      (list (list '= (list y x) full))
                                      (ode-field hom :constants) '() 'ok
                                      'undetermined #t))))))))))

(define (lo-solve eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)) (n (ode-order eq y x)))
        (if (< n 2)
            #f
            (let ((cg (lo-coeffs eq y x)))
              (if (not cg)
                  #f
                  (let ((cs (car cg)) (g (cadr cg)))
                    (if (ode-zero? g)
                        (lo-hom eq y x cs)
                        (or (lo-undet eq y x cs (simplify (list '- 0 g)))
                            (and (= n 2) (lo-variation eq y x cs (simplify (list '- 0 g)))))))))))))


(define *ode-linear-loaded* #t)
