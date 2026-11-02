; specfun-ode.lisp — ODE.9: решения y″ + a·y′ + b·y = 0 через головы Бесселя/Эйри/Лежандра/₂F₁ (шаг ODE.9).
; Классы: (Б) Бессель и обобщённый, модифицированный; (Э) Эйри; (Л) Лежандр; (Г) Эрмит; (Г₂) гипергеометрическое.
; Ответ принимается только после dsolve-check (символьно или численно); статус Ковачича no-liouvillian
; сохраняется — добавляется ответ через спецфункции.
(module ode)

; ---------- помощники ----------

; рациональное (не float) число?
(define (sfo-rat? e) (and (number? e) (not (equal? (type-of e) 'float))))

; многочлен по x с рациональными коэффициентами → (c0 … cn) | #f
(define (sfo-poly-coeffs e x)
  (if (polynomial? e x)
      (let ((cs (try (coefficients e x) (lambda (err) #f))))
        (and cs (every? sfo-rat? cs) cs))
      #f))

; ненулевые коэффициенты только при x^0 и x^deg
(define (sfo-two-terms? cs deg)
  (let loop ((k 1) (xs (cdr cs)))
    (cond ((null? xs) #t)
          ((= k deg) (and (null? (cdr xs)) (not (kv-zero? (car xs)))))
          ((kv-zero? (car xs)) (loop (+ k 1) (cdr xs)))
          (else #f))))

; квадратный корень неотрицательного рационального: точный, иначе символьный
(define (sfo-sqrt q)
  (let ((r (simplify (list '^ q 1/2))))
    (if (sfo-rat? r) r (list '^ q 1/2))))

; вещественный кубический корень рационального q
(define (sfo-cbrt q)
  (let* ((s (if (< q 0) -1 1)) (r (simplify (list '^ (abs q) 1/3))))
    (if (sfo-rat? r) (* s r) (simplify (list '* s (list '^ (abs q) 1/3))))))

; неотрицательное целое n из n(n+1) = m | #f
(define (sfo-n-from-qq m)
  (let loop ((n 0))
    (cond ((> n 200) #f)
          ((kv-zero? (simplify (list '- (list '* n (+ n 1)) m))) n)
          (else (loop (+ n 1))))))

; ---------- (Э) Эйри: y″ = (αx + β)·y ----------

(define (sfo-airy a b x)
  (if (not (kv-zero? a))
      #f
      (let* ((nb (simplify (list '- b)))
             (cs (sfo-poly-coeffs nb x)))
        (if (or (not cs) (> (length cs) 2))
            #f
            (let ((beta (if (pair? cs) (car cs) 0))
                  (alpha (if (> (length cs) 1) (cadr cs) 0)))
              (if (or (kv-zero? alpha) (not (sfo-rat? alpha)))
                  #f
                  (let* ((k (sfo-cbrt alpha))
                         (d (simplify (list '/ beta (list '^ k 2))))
                         (t (simplify (list '+ (list '* k x) d))))
                    (list 'airy (list 'airy-ai t) (list 'airy-bi t)))))))))

; ---------- (Б1) x²y″ + xy′ + (α²x^{2m} − ν²)·y = 0 ----------

(define (sfo-bessel1 a b x)
  (if (not (kv-zero? (simplify (list '- (list '* a x) 1))))
      #f
      (let ((cs (sfo-poly-coeffs (expand (simplify (list '* b (list '^ x 2)))) x)))
        (if (or (not cs) (< (length cs) 3))
            #f
            (let* ((deg (- (length cs) 1)) (m (/ deg 2)))
              (if (or (not (= 0 (remainder deg 2))) (< m 1) (> m 24) (not (sfo-two-terms? cs deg)))
                  #f
                  (let ((c0 (car cs)) (lead (nth cs deg)))
                    (if (or (kv-zero? lead) (> c0 0))
                        #f
                        (let* ((mod? (< lead 0))
                               (alpha (sfo-sqrt (abs lead)))
                               (nu (if (< c0 0) (sfo-sqrt (- c0)) 0))
                               (arg (simplify (list '* (/ alpha m) (list '^ x m))))
                               (ord (simplify (list '/ nu m)))
                               (h1 (if mod? 'bessel-i 'bessel-j))
                               (h2 (if mod? 'bessel-k 'bessel-y)))
                          (list 'bessel (list h1 ord arg) (list h2 ord arg)))))))))))

; ---------- (Б2) y″ + c·x^m·y = 0 (m ≥ 2): √x·Z_{1/(m+2)}(2√c/(m+2)·x^{(m+2)/2}) ----------

(define (sfo-bessel2 a b x)
  (if (not (kv-zero? a))
      #f
      (let ((cs (sfo-poly-coeffs (expand (simplify b)) x)))
        (if (or (not cs) (< (length cs) 3))
            #f
            (let ((deg (- (length cs) 1)) (c (nth cs (- (length cs) 1))))
              (if (or (not (= 0 (remainder deg 2))) (not (sfo-two-terms? cs deg)) (kv-zero? c))
                  #f
                  (let* ((m deg)
                         (mod? (< c 0))
                         (k (simplify (list '/ (list '* 2 (sfo-sqrt (abs c))) (+ m 2))))
                         (arg (simplify (list '* k (list '^ x (/ (+ m 2) 2)))))
                         (ord (simplify (list '/ 1 (+ m 2))))
                         (sq (simplify (list '^ x 1/2)))
                         (h1 (if mod? 'bessel-i 'bessel-j))
                         (h2 (if mod? 'bessel-k 'bessel-y)))
                    (list 'bessel
                          (simplify (list '* sq (list h1 ord arg)))
                          (simplify (list '* sq (list h2 ord arg)))))))))))

; ---------- (Л) Лежандр: (1 − x²)y″ − 2xy′ + n(n+1)y = 0 ----------

(define (sfo-legendre a b x)
  (let ((q (simplify (list '- 1 (list '^ x 2)))))
    (if (kv-zero? q)
        #f
        (let ((ra (expand (simplify (list '* a q)))) (rb (expand (simplify (list '* b q)))))
          (if (not (kv-zero? (simplify (list '+ ra (list '* 2 x)))))
              #f
              (let ((cs (sfo-poly-coeffs rb x)))
                (if (or (not cs) (> (length cs) 1))
                    #f
                    (let ((n (sfo-n-from-qq (if (pair? cs) (car cs) 0))))
                      (and n (list 'legendre (list 'legendre-p n x) (list 'legendre-q n x)))))))))))

; ---------- (Г) Эрмит: y″ − 2xy′ + 2ny = 0 ----------

(define (sfo-hermite-poly n x)
  (if (= n 0)
      1
      (let loop ((k 1) (prev 1) (cur (simplify (list '* 2 x))))
        (if (= k n)
            (expand cur)
            (loop (+ k 1) cur
                  (simplify (list '- (list '* 2 x cur) (list '* (* 2 k) prev))))))))

(define (sfo-hermite a b x)
  (if (not (kv-zero? (simplify (list '+ a (list '* 2 x)))))
      #f
      (let ((cs (sfo-poly-coeffs b x)))
        (if (or (not cs) (> (length cs) 1))
            #f
            (let ((m (if (pair? cs) (car cs) 0)))
              (let loop ((n 0))
                (cond ((> n 200) #f)
                      ((kv-zero? (simplify (list '- (list '* 2 n) m)))
                       (let ((h (sfo-hermite-poly n x)))
                         (list (list 'hermite n) h
                               (simplify (list '* h
                                               (list 'integrate
                                                     (simplify (list '/ (list 'exp (list '^ x 2))
                                                                     (list '^ h 2)))
                                                     x))))))
                      (else (loop (+ n 1))))))))))

; ---------- (Г₂) гипергеометрическое: x(1−x)y″ + (c − (a+b+1)x)y′ − ab·y = 0 ----------

(define (sfo-hyper a b x)
  (let* ((q (simplify (list '* x (list '- 1 x))))
         (pa (expand (simplify (list '* a q))))
         (pb (expand (simplify (list '* b q)))))
    (let ((ca (sfo-poly-coeffs pa x)) (cb (sfo-poly-coeffs pb x)))
      (if (or (not ca) (> (length ca) 2) (not cb) (> (length cb) 1))
          #f
          (let* ((c (if (pair? ca) (car ca) 0))
                 (s (if (> (length ca) 1) (- (- (cadr ca)) 1) 0))   ; a + b
                 (ab (if (pair? cb) (- (car cb)) 0))
                 (d (simplify (list '- (list '^ s 2) (list '* 4 ab))))
                 (sq (and (sfo-rat? c) (not (kv-zero? c)) (not (equal? c 1))
                          (>= d 0) (sfo-sqrt d))))
            (if (not sq)
                #f
                (let* ((aa (simplify (list '* 1/2 (list '+ s sq))))
                       (bb (simplify (list '* 1/2 (list '- s sq))))
                       (h1 (list 'hyper (list aa bb) (list c) x))
                       (e1 (try (hyperexpand h1) (lambda (err) h1)))
                       (y1 (if (equal? e1 h1) h1 e1))
                       (y2 (if (integer? c)
                               (simplify (list '* y1
                                               (list 'integrate
                                                     (simplify (list '/ (list 'exp (list '* -1 (integrate a x)))
                                                                     (list '^ y1 2)))
                                                     x)))
                               (simplify (list '* (list '^ x (- 1 c))
                                               (list 'hyper (list (+ aa (- 1 c)) (+ bb (- 1 c)))
                                                     (list (- 2 c)) x))))))
                  (list 'hyper y1 y2))))))))

; ---------- распознавание и добавление ответа ----------

(define (sfo-solve eq yx)
  (let* ((y (car yx)) (x (cadr yx))
         (cb (try (kv-coeffs eq y x) (lambda (err) #f))))
    (if (not cb)
        #f
        (let ((a (car cb)) (b (cadr cb)))
          (or (sfo-airy a b x)
              (sfo-bessel1 a b x)
              (sfo-bessel2 a b x)
              (sfo-legendre a b x)
              (sfo-hermite a b x)
              (sfo-hyper a b x))))))

; встречается ли в выражении невычисленный интеграл
(define (sfo-has-integrate? e)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) 'integrate) #t)
        (else (any? sfo-has-integrate? e))))

; линейная независимость: вронскиан W = y₁y₂′ − y₁′y₂ ≠ 0 численно в одной точке
; (для второй ветви через ∫ независимость следует из формулы понижения порядка)
(define (sfo-wronskian-nonzero? u1 u2 x)
  (let loop ((ps (list 1/3 2/5 7/11 5/4 -3/7 11/13)))
    (if (null? ps)
        #f
        (let* ((p (car ps))
               (sub (lambda (e) (eval-num (subst (list (list x p)) e))))
               (v1 (sub u1)) (v2 (sub u2))
               (d1 (sub (diff x u1))) (d2 (sub (diff x u2))))
          (if (and (number? v1) (number? v2) (number? d1) (number? d2)
                   (> (abs (- (* v1 d2) (* d1 v2))) 1e-9))
              #t
              (loop (cdr ps)))))))

(define (sfo-independent? u1 u2 x)
  (or (sfo-has-integrate? u2) (sfo-wronskian-nonzero? u1 u2 x)))

; принять найденный ответ: каждая ветвь проверяется подстановкой (dsolve-check);
; статус no-liouvillian Ковачича сохраняется (сертификат отказа не ослабляется)
(define (sfo-augment r eq yx)
  (if (not (and (pair? yx) (= (ode-order eq (car yx) (cadr yx)) 2)))
      r
      (let ((sf (try (ode-quiet (lambda () (sfo-solve eq yx))) (lambda (err) #f))))
        (if (not sf)
            r
            (let* ((y (car yx)) (x (cadr yx))
                   (cls (car sf)) (u1 (cadr sf)) (u2 (caddr sf))
                   (s1 (list '= (list y x) u1))
                   (s2 (list '= (list y x) u2)))
              (if (not (ode-quiet (lambda ()
                                    (and (dsolve-check eq s1 yx) (dsolve-check eq s2 yx)
                                         (sfo-independent? u1 u2 x)))))
                  r
                  (let* ((sol (list '= (list y x)
                                    (simplify (list '+ (list '* 'C1 u1)
                                                    (list '* 'C2 u2)))))
                         (status (ode-field r :status))
                         (method (ode-field r :method)))
                    (cond
                      ((equal? status 'no-liouvillian)
                       (ode-solution 'general (list sol) '(C1 C2) '() 'no-liouvillian
                                     method (ode-field r :check)))
                      ((or (equal? status 'unknown)
                           (member? method '(series frobenius))
                           ; ответ с невычисленным ∫ заменяем, когда голова даёт замкнутую форму:
                           ; Лежандр (П3) и Эрмит n ≥ 2 (П4); Эрмит n = 1 (y₁ = x у Ковачича) не трогаем
                           (and (any? (lambda (s) (sfo-has-integrate? s)) (ode-field r :solutions))
                                (or (equal? cls 'legendre)
                                    (and (pair? cls) (equal? (car cls) 'hermite) (>= (cadr cls) 2))))
                           ; (Г₂): ответ Ковачича через log(x−1) ветвится на x < 1 — заменяем на ₂F₁
                           (and (equal? method 'kovacic) (equal? cls 'hyper)))
                       (ode-solution 'general (list sol) '(C1 C2) '() 'ok 'specfun 'numeric))
                      (else r)))))))))

(define *ode-sf-loaded* #t)
