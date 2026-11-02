; first-order.lisp — ОДУ первого порядка (шаг ODE.1)
; Разделяющиеся, линейные, Бернулли, однородные; неявные ответы и потерянные решения.
(module ode)

; ---------- сведение к y′ = f(x, y) ----------

; правая часть, если уравнение разрешимо относительно y′; иначе #f
(define (fo-rhs eq y x)
  (let* ((d (ode-nth-deriv y x 1))
         (r (ode-coeff-of d (ode-normalize eq) y x)))
    (and r
         (number? (car r))
         (not (ode-zero? (car r)))
         (simplify (list '/ (list '- (cdr r)) (car r))))))

; (y x) → символ y (для классификации f(x, y))
(define (fo-bare f y x) (ode-replace f (list y x) 'y))

(define (fo-free-y? e) (not (ode-mentions-sym? e 'y)))

; ---------- разбор f = g(x)·h(y) ----------

(define (fo-mul-factors f)
  (cond ((and (pair? f) (equal? (car f) '*)) (cdr f))
        ((and (pair? f) (equal? (car f) '/) (= (length f) 3))
         (append (fo-mul-factors (cadr f))
                 (map (lambda (z) (list '/ 1 z)) (fo-mul-factors (caddr f)))))
        (else (list f))))

(define (fo-separable-parts f)
  (if (not (ode-mentions-sym? f 'x))
      (cons 1 f)                       ; f зависит только от y (например, 1 + y²)
      (let* ((fs (fo-mul-factors f))
             (sum-y (any? (lambda (z) (and (pair? z) (equal? (car z) '+)
                                           (ode-mentions-sym? z 'y))) fs)))
        (if sum-y
            #f
            (let ((ys (filter (lambda (z) (ode-mentions-sym? z 'y)) fs))
                  (xs (filter (lambda (z) (not (ode-mentions-sym? z 'y))) fs)))
              (cons (foldl * 1 xs) (foldl * 1 ys)))))))

; ---------- результат и проверки ----------

(define (fo-result eq y x rhs method constants singular)
  (let ((sol (list '= (list y x) rhs)))
    (if (dsolve-check eq sol (list y x))
        (ode-solution 'general (list sol) constants singular 'ok method #t)
        (error "fo-solve: решение не прошло проверку"))))

; неявное F(x,y) = C: проверяем F_x + F_y·y′ = 0 на найденном f (символьно, иначе численно)
(define (fo-implicit-check eq F f y x)
  (let ((res (simplify (list '+ (diff 'x F) (list '* (diff 'y F) f)))))
    (cond ((ode-zero? res) #t)
          ((ode-surely-nonzero? res) #f)
          (else
           (let loop ((ps '((1 2) (2 3) (3 1) (5 2) (2 5))) (n 0))
             (cond ((null? ps) (and (> n 0) 'numeric))
                   (else
                    (let ((v (eval-num (subst (list y (cadr (car ps)))
                                              (subst (list x (car (car ps))) res)))))
                      (if (and (number? v) (< (abs v) 1e-7))
                          (loop (cdr ps) (+ n 1))
                          #f)))))))))

(define (fo-implicit eq y x F f method)
  (let ((c (fo-implicit-check eq F f y x)))
    (if c
        (ode-solution 'implicit (list (list '= F 'C1)) (list 'C1) '() 'ok method c)
        #f)))

; ---------- разделяющиеся ----------

(define (fo-sep-solve eq y x f parts)
  (let* ((g (car parts)) (h (cdr parts))
         (Hy (ode-quiet (lambda () (integrate (list '/ 1 h) y))))
         (Gx (ode-quiet (lambda () (integrate g x)))))
    (with-step ('ode-fo-separable "Разделение переменных" f
                :comment (string-append "f = g(x)·h(y), g = " (ode-mp g) ", h = " (ode-mp h)
                                        "; ∫dy/h(y) = " (ode-mp Hy)
                                        ", ∫g(x) dx = " (ode-mp Gx))
                :after (lambda (r) (ode-field r :solutions)))
      (if (ode-has-head? Hy 'integrate)
          (fo-implicit eq y x (simplify (list '- Hy Gx)) f 'separable)
          (let ((sols (try (set->list (solve (list '= Hy (list '+ Gx 'C1)) y))
                           (lambda (e) '()))))
            (if (null? sols)
                (fo-implicit eq y x (simplify (list '- Hy Gx)) f 'separable)
                ; все ветви решения (solve может дать ±√…): берём каждую, прошедшую проверку
                (let ((rhs-list (filter (lambda (s) (dsolve-check eq (list '= (list y x) s) (list y x)))
                                        (map simplify sols))))
                  (if (null? rhs-list)
                      (fo-implicit eq y x (simplify (list '- Hy Gx)) f 'separable)
                      (ode-solution 'general
                                    (map (lambda (s) (list '= (list y x) s)) rhs-list)
                                    (list 'C1) '() 'ok 'separable #t)))))))))

; ---------- линейные ----------

(define (fo-linear-parts f)
  (let ((r (ode-coeff-of 'y f 'y 'x)))
    (and r (fo-free-y? (car r)) (fo-free-y? (cdr r)) r)))

(define (fo-linear-solve eq y x f lr)
  (let* ((a (car lr)) (b (cdr lr))
         (P (list '- 0 a))
         (Ip (ode-quiet (lambda () (integrate P x))))
         (mu (simplify (list 'exp Ip)))
         (Iq (ode-quiet (lambda () (integrate (list '* mu b) x))))
         (rhs (simplify (list '/ (list '+ Iq 'C1) mu))))
    (with-step ('ode-fo-linear "Линейное уравнение 1-го порядка" f
                :comment (string-append "y′ + P·y = Q; P = " (ode-mp (simplify P))
                                        ", Q = " (ode-mp (simplify b))
                                        "; ∫P dx = " (ode-mp Ip)
                                        ", μ = e^{∫P dx} = " (ode-mp mu)
                                        "; ∫μ·Q dx = " (ode-mp Iq))
                :after (lambda (r) (ode-field r :solutions)))
      (fo-result eq y x rhs 'linear (list 'C1) '()))))

; ---------- Бернулли ----------

; степень по y у одночлена (#f — не одночлен по y)
(define (fo-deg-y e)
  (cond ((fo-free-y? e) 0)
        ((equal? e 'y) 1)
        ((and (pair? e) (equal? (car e) '^) (equal? (cadr e) 'y) (number? (caddr e)))
         (caddr e))
        ((and (pair? e) (equal? (car e) '*))
         (let ((ds (map fo-deg-y (cdr e))))
           (if (any? (lambda (z) (not z)) ds) #f (foldl + 0 ds))))
        (else #f)))

(define (fo-bern-parts f)
  (let* ((e (expand f))
         (ts (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e))))
    (let loop ((rest ts) (p 0) (q 0) (n #f))
      (cond ((null? rest)
             (if (and n (> n 1) (not (ode-zero? q))) (list p q n) #f))
            (else
             (let* ((t (car rest)) (d (fo-deg-y t)))
               (cond ((not d) #f)
                     ((= d 0) (if (ode-zero? t) (loop (cdr rest) p q n) #f))
                     ((= d 1)
                      (loop (cdr rest) (+ p (simplify (list '/ t 'y))) q n))
                     (else
                      (if (and (or (not n) (= n d)) (not (ode-zero? t)))
                          (loop (cdr rest) p (+ q (simplify (list '/ t (list '^ 'y d)))) d)
                          #f)))))))))

(define (fo-bern-solve eq y x f parts)
  (let* ((p (car parts)) (q (cadr parts)) (n (caddr parts))
         (k (simplify (list '- 1 n)))
         (P (simplify (list '* (list '- 0 k) p)))
         (Q (simplify (list '* k q)))
         (mu (simplify (list 'exp (ode-quiet (lambda () (integrate P x))))))
         (u (simplify (list '/ (list '+ (ode-quiet (lambda () (integrate (list '* mu Q) x))) 'C1) mu)))
         (rhs (simplify (list '^ u (list '/ 1 k))))
         (sing (if (> n 0) (list (list '= (list y x) 0)) '())))
    (with-step ('ode-fo-bernoulli "Уравнение Бернулли" f
                :comment (string-append "y′ + p(x)·y = q(x)·y^n, n = " (to-string n)
                                        "; замена v = y^(1−n) = " (ode-mp (list '^ 'y k))
                                        "; v′ + P·v = Q, P = " (ode-mp P) ", Q = " (ode-mp Q)
                                        ", μ = " (ode-mp mu))
                :after (lambda (r) (list (ode-field r :solutions) (ode-field r :singular))))
      (fo-result eq y x rhs 'bernoulli (list 'C1) sing))))

; ---------- однородные ----------

(define (fo-hom-solve eq y x f)
  (let* ((fu (simplify (together (ode-replace f 'y (list '* 'u 'x))))))
    (if (ode-mentions-sym? fu 'x)
        #f
        (let* ((den (simplify (list '- fu 'u)))
               (A (ode-quiet (lambda () (integrate (list '/ 1 den) 'u)))))
          (with-step ('ode-fo-homogeneous "Однородное уравнение (y = v·x)" f
                      :comment (string-append "f(x, v·x) = " (ode-mp fu)
                                              "; v′·x + v = f(x, v·x): A(v) = ∫dv/(φ(v) − v) = " (ode-mp A))
                      :after (lambda (r) (ode-field r :solutions)))
            (cond ((or (ode-has-head? A 'integrate) (ode-zero? den)) #f)
                  (else
                   (let ((sols (try (set->list (solve (list '= A (list '+ (list 'log 'x) 'C1)) 'u))
                                    (lambda (e) '()))))
                     (if (null? sols)
                         ; явно не выражается — неявное F(x, y) = C1 (F = A с u = y/x)
                         (fo-implicit eq y x
                                      (simplify (list '- (subst (list 'u (list '/ 'y 'x)) A)
                                                      (list 'log 'x)))
                                      f 'homogeneous)
                         (fo-result eq y x
                                    (simplify (list '* (car sols) 'x))
                                    'homogeneous (list 'C1)
                                    (map (lambda (u0) (list '= (list y x) (list '* u0 'x)))
                                         (set->list (solve (list '= den 0) 'u)))))))))))))

; постоянные решения автономного уравнения f(y) = 0 (потерянные при делении)
(define (fo-equilibria eq y x f)
  (if (ode-mentions-sym? f 'x)
      '()
      (let ((rs (ode-quiet (lambda ()
                             (try (set->list (solve (list '= f 0) 'y)) (lambda (e) '()))))))
        (filter (lambda (r)
                  (and (number? r)
                       (dsolve-check eq (list '= (list y x) r) (list y x))))
                rs))))

(define (fo-add-singular eq r y x f)
  (let* ((old (ode-field r :singular))
         (add (map (lambda (v) (list '= (list y x) v)) (fo-equilibria eq y x f)))
         (new (foldl (lambda (acc s)
                       (if (any? (lambda (z) (equal? z s)) acc) acc (append acc (list s))))
                     old add)))
    (if (and (pair? add) (step-log-enabled?))
        (record-step 'ode-fo-singular "Особые решения"
                     "постоянные решения f(y) = 0, проверены подстановкой"
                     f add 'detail))
    (if (= (length new) (length old))
        r
        (ode-solution (ode-field r :type) (ode-field r :solutions) (ode-field r :constants)
                      new (ode-field r :status) (ode-field r :method) (ode-field r :check)))))

; ---------- диспетчер ----------

(define (fo-solve eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)))
        (let* ((rhs (fo-rhs eq y x))
               (f (if rhs (fo-bare rhs y x) #f)))
          (cond ((not f) #f)
                ((fo-free-y? f) #f)          ; чистая квадратура — в core
                (else
                 ; классификацию частей считаем один раз: она же объясняет выбранный метод
                 (let* ((lr (fo-linear-parts f))
                        (bp (and (not lr) (fo-bern-parts f)))
                        (sp (and (not lr) (not bp) (fo-separable-parts f)))
                        (sep? (and sp (not (fo-free-y? (cdr sp)))))
                        (r (cond (lr (fo-linear-solve eq y x f lr))
                                 (bp (fo-bern-solve eq y x f bp))
                                 (sep? (fo-sep-solve eq y x f sp))
                                 (else (fo-hom-solve eq y x f)))))
                   (if r (fo-add-singular eq r y x f) #f))))))))

(define *ode-first-order-loaded* #t)
