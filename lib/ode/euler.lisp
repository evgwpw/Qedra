; euler.lisp — уравнение Эйлера–Коши a_n x^n y⁽ⁿ⁾ + … + b x y′ + c y = 0 (шаг ODE.4a, n ≤ 4)
; Подстановка x = e^t → постоянные коэффициенты по λ = r(r−1)…(r−k+1); ответ x^r·(log x)^j.
; Комплексные корни a ± bi → x^a·cos(b·log x), x^a·sin(b·log x). Требуется x > 0 (record-condition).
(module ode)

; ---------- коэффициенты: уравнение Эйлера a_k·x^k·y⁽ᵏ⁾, a_k числа ----------

; множитель при производной: число · x^k → (a . k); #f — не такого вида
(define (eu-xk e x)
  (cond ((equal? e x) (cons 1 1))
        ((and (pair? e) (equal? (car e) '*))
         (let* ((fs (cdr e))
                (px (filter (lambda (z) (equal? z x)) fs))
                (pows (filter (lambda (z) (and (pair? z) (equal? (car z) '^)
                                                (equal? (cadr z) x)
                                                (number? (caddr z)) (integer? (caddr z))
                                                 (> (caddr z) 0)))
                              fs))
                (rest (filter (lambda (z) (and (not (equal? z x))
                                               (not (and (pair? z) (equal? (car z) '^)
                                                         (equal? (cadr z) x)))))
                              fs)))
           (if (and (= (length px) 1) (null? pows) (not (any? (lambda (w) (not (number? w))) rest)))
               (cons (foldl * 1 rest) 1)
               (if (and (null? px) (= (length pows) 1) (not (any? (lambda (w) (not (number? w))) rest)))
                   (cons (foldl * 1 rest) (caddr (car pows)))
                   #f))))
        ((and (pair? e) (equal? (car e) '^) (equal? (cadr e) x)
              (number? (caddr e)) (integer? (caddr e)) (> (caddr e) 0))
         (cons 1 (caddr e)))
        ((number? e) (cons e 0))
        (else #f)))

; (eu-coeffs eq y x) → (cs g) или #f: cs — числа a_n…a_0 при x^k·y⁽ᵏ⁾, g — правая часть от x
(define (eu-coeffs eq y x)
  (let* ((n (ode-order eq y x))
         (e (ode-normalize eq))
         (ds (map (lambda (k) (if (= k 0) (list y x) (ode-nth-deriv y x k)))
                  (range (+ n 1))))
         (as (map (lambda (d)
                    (let ((r (ode-coeff-of d e y x)))
                      (and r
                           (let* ((a (car r))
                                  (ak (eu-xk a x)))
                             (and ak
                                  (number? (car ak))
                                  (= (cdr ak) (ode-diff-depth d y x))
                                  (car ak))))))
                  ds)))
    (if (any? (lambda (a) (not a)) as)
        #f
        (let* ((kx (map (lambda (d) (^ x (ode-diff-depth d y x))) ds))
               (full (map2 * as kx))
               (an (car (reverse as)))
               (cs (map (lambda (a) (simplify (list '/ a an))) as))
               (g (simplify (foldl (lambda (acc p) (list '- acc (list '* (car p) (cadr p))))
                                    e (map2 list full ds)))))
          (if (or (ode-y-node-any? g y x) (ode-mentions-sym? g y))
              #f
              (list cs g))))))


; ---------- характеристический многочлен и базис ----------

; падающие факториалы r(r−1)…(r−k+1)
(define (eu-fall r k)
  (let loop ((j 0) (acc 1))
    (if (>= j k) acc (loop (+ j 1) (list '* acc (list '- r j))))))

; λ-многочлен уравнения Эйлера: Σ a_k·r(r−1)…(r−k+1)
(define (eu-charpoly cs)
  (let ((n (- (length cs) 1)))
    (simplify (expand (foldl (lambda (acc k) (list '+ acc (list '* (nth cs k) (eu-fall '%l k))))
                           0 (range (+ n 1)))))))

; x^r·(log x)^j
(define (eu-power-series r m x)
  (map (lambda (j) (simplify (list '* (list '^ x r) (list '^ (list 'log x) j))))
       (range m)))

; корни a ± bi (мнимая часть символьная) → x^a·cos(b log x), x^a·sin(b log x)
(define (eu-trig-series alpha beta m x)
  (append
   (map (lambda (j) (simplify (list '* (list '^ x alpha) (list '^ (list 'log x) j)
                                   (list 'cos (list '* beta (list 'log x))))))
        (range m))
   (map (lambda (j) (simplify (list '* (list '^ x alpha) (list '^ (list 'log x) j)
                                   (list 'sin (list '* beta (list 'log x))))))
        (range m))))

(define (eu-factor-basis f m x)
  (let ((d (degree f '%l)))
    (cond ((= d 1)
           (let* ((a (coeff f '%l 1)) (b (coeff f '%l 0))
                  (r (simplify (list '/ (list '- 0 b) a))))
             (eu-power-series r m x)))
          ((= d 2)
           (let* ((a (coeff f '%l 2)) (b (coeff f '%l 1)) (c (coeff f '%l 0))
                  (D (simplify (list '- (list '^ b 2) (list '* 4 a c)))))
             (if (and (number? D) (< D 0))
                 (let* ((alpha (simplify (list '/ (list '- 0 b) (list '* 2 a))))
                        (beta (simplify (list '/ (list 'sqrt (list '- 0 D)) (list '* 2 a)))))
                   (eu-trig-series alpha beta m x))
                 (append-map (lambda (r) (eu-power-series r m x))
                             (set->list (solve (list '= f 0) '%l))))))
          (else
           (append-map (lambda (r) (eu-power-series r m x))
                       (set->list (solve (list '= f 0) '%l)))))))

(define (eu-basis cs x)
  (let* ((fl (ode-quiet (lambda () (factor-list (eu-charpoly cs)))))
         (factors (cdr fl)))
    (ode-quiet (lambda ()
                 (append-map (lambda (fm) (eu-factor-basis (car fm) (cadr fm) x)) factors)))))

; ---------- решение ----------

(define (eu-solve eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)) (n (ode-order eq y x)))
        (if (or (< n 1) (> n 4))
            #f
            (let ((cg (eu-coeffs eq y x)))
              (if (not cg)
                  #f
                  (let ((cs (car cg)) (g (cadr cg)))
                    (if (not (ode-zero? g))
                        #f
                        (let* ((fs (eu-basis cs x))
                               (nn (length fs)))
                          (if (not (= nn n))
                              #f
                              (let* ((cp (eu-charpoly cs))
                                     (cnames (map (lambda (k) (string->symbol (string-append "C" (to-string (+ k 1)))))
                                                  (range nn)))
                                     (rhs (simplify (foldl (lambda (acc p) (list '+ acc (list '* (car p) (cadr p))))
                                                           0 (map2 list cnames fs))))
                                     (sol (list '= (list y x) rhs)))
                                (record-condition (list 'ode-euler x)
                                  "dsolve: уравнение Эйлера — решение верно при x > 0 (log x веществен)")
                                (with-step ('ode-eu-subst "Уравнение Эйлера–Коши: замена x = e^t" eq
                                            :comment (string-append "R(r) = " (ode-mp* (list (list '%l 'r)) cp)
                                                                    "; ФСР: " (ode-mp-list fs))
                                            :after (lambda (r) (ode-field r :solutions)))
                                  (let ((chk (dsolve-check eq sol yx)))
                                    (if chk
                                        (ode-solution 'general (list sol) cnames '() 'ok 'euler chk)
                                        #f))))))))))))))

(define *ode-euler-loaded* #t)

