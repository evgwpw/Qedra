; kovacic.lisp — алгоритм Ковачича для y″ + a·y′ + b·y = 0 (шаг ODE.8a).
; Нормальная форма z = y·e^{½∫a}: z″ = r·z, r = a²/4 + a′/2 − b.
; Условия случаев по полюсам r и порядку на ∞; случай 1 — ω и многочлен P (линейная система);
; доказанный отказ no-liouvillian — когда отсеяны все три случая. Случаи 2–3 — следующие подшаги.
(module ode
  (export kovacic kovacic-check))

; ---------- рациональные данные ----------

(define (kv-num-den e)
  (let ((t (together (simplify e))))
    (list (simplify (numer t)) (simplify (denom t)))))

(define (kv-at e x c) (try (simplify (subst (list (list x c)) e)) (lambda (err) #f)))
(define (kv-zero? e) (equal? (simplify e) 0))
(define (kv-int? e) (and (number? e) (integer? e)))
(define (kv-even-int? e) (and (kv-int? e) (= 0 (remainder e 2))))
(define (kv-sqrt e) (simplify (list '^ e 1/2)))
(define (kv-list->set l) l)

; ---------- коэффициенты и нормальная форма ----------

; (kv-coeffs eq y x) → (a b) для y″ + a·y′ + b·y = 0 с a, b ∈ ℚ(x); иначе #f
(define (kv-coeffs eq y x)
  (let* ((e (ode-normalize eq))
         (d2 (ode-nth-deriv y x 2)) (d1 (ode-nth-deriv y x 1)) (d0 (list y x))
         (q2 (ode-coeff-of d2 e y x)) (q1 (ode-coeff-of d1 e y x)) (q0 (ode-coeff-of d0 e y x)))
    (and q2 q1 q0
         (let* ((a2 (car q2)) (a1 (car q1)) (a0 (car q0))
                (rem (simplify (expand (list '- e (list '+ (list '* a2 d2)
                                                             (list '* a1 d1)
                                                             (list '* a0 d0)))))))
           (and (kv-zero? rem)
                (not (kv-zero? a2))
                (let* ((a (simplify (/ a1 a2)))
                       (b (simplify (/ a0 a2)))
                       (an (kv-num-den a)) (bn (kv-num-den b)))
                  (and (polynomial? (car an) x) (polynomial? (cadr an) x)
                       (polynomial? (car bn) x) (polynomial? (cadr bn) x)
                       (list a b))))))))

; r = a²/4 + a′/2 − b (одна дробь)
(define (kv-r a b x)
  (simplify (together (list '- (list '+ (list '* 1/4 (list '^ a 2))
                                         (list '* 1/2 (ode-diff x a)))
                            b))))

; ---------- полюса и порядки ----------

; порядок r в c (0 — не полюс), m — кратность (x−c) в знаменателе
(define (kv-pole-order r x c m)
  (let loop ((k 0))
    (if (> k m) #f
        (let ((v (try (limit (list '* (list '^ (list '- x c) k) r) x c)
                      (lambda (err) #f))))
          (if (and v (number? v) (not (kv-zero? v))) k (loop (+ k 1)))))))

; ((c порядок) …) | 'not-rational (полюс не над ℚ)
(define (kv-poles r x)
  (let* ((t (cadr (kv-num-den r)))
         (fl (try (factor-list t) (lambda (err) #f))))
    (if (not fl)
        'not-rational
        (let loop ((fs (cdr fl)) (acc '()))
          (cond ((null? fs) (reverse acc))
                ((> (degree (car (car fs)) x) 1) 'not-rational)
                (else
                 (let* ((roots (try (set->list (solve (list '= (car (car fs)) 0) x))
                                    (lambda (err) '())))
                        (c (and (pair? roots) (car roots))))
                   (if (not (number? c))
                       'not-rational
                       (let ((k (kv-pole-order r x c (cadr (car fs)))))
                         (if (not k)
                             'not-rational
                             (loop (cdr fs) (cons (list c k) acc))))))))))))

; o(∞) = deg знаменателя − deg числителя; #f — r = 0 (нулевой числитель)
(define (kv-ord-inf r x)
  (let* ((nd (kv-num-den r)) (s (car nd)) (t (cadr nd)))
    (if (kv-zero? s) #f (- (degree t x) (degree s x)))))

; (случай 1 возможен? случай 2 возможен? случай 3 возможен?); r = 0 (o = #f) сюда не доходит —
; такие уравнения решаются раньше (постоянные коэффициенты/квадратура), иначе честное «не знаю»
(define (kv-cases poles o)
  (if (not (number? o))
      '(#f #f #f)
      (let ((ms (map (lambda (p) (cadr p)) poles)))
        (list (and (every? (lambda (m) (or (= m 1) (kv-even-int? m))) ms)
                   (or (kv-even-int? o) (> o 2)))
              (any? (lambda (m) (or (= m 2) (and (> m 2) (not (kv-even-int? m))))) ms)
              (and (every? (lambda (m) (<= m 2)) ms) (>= o 2))))))

; ---------- данные случая 1 ----------

; ((c α+ α-) …) | 'unknown — порядок > 2 не реализован
(define (kv-pole-alphas poles r x)
  (let loop ((ps poles) (acc '()))
    (cond ((null? ps) (reverse acc))
          ((= (cadr (car ps)) 1) (loop (cdr ps) (cons (list (car (car ps)) 1 1) acc)))
          ((= (cadr (car ps)) 2)
           (let* ((c (car (car ps)))
                  (b (kv-at (list '* (list '^ (list '- x c) 2) r) x c))
                  (s (kv-sqrt (simplify (list '+ 1 (list '* 4 b))))))
             (loop (cdr ps)
                   (cons (list c
                               (simplify (list '* 1/2 (list '+ 1 s)))
                               (simplify (list '* 1/2 (list '- 1 s))))
                         acc))))
          (else 'unknown))))

; коэффициенты x^(2m−k) в разложении r на ∞ (k = 0…m): полиномиальная часть числителя/знаменателя
(define (kv-inf-coeffs r x m)
  (let ((q (poly-quotient (numer r) (denom r) x)))
    (map (lambda (k) (coeff q x (- (* 2 m) k))) (range (+ m 1)))))

; W — полиномиальная часть √r на ∞ (степень m): W² ≡ r mod O(x^(m−1))
; коэффициенты могут быть комплексными (%i) — важно лишь, что они не содержат x
(define (kv-inf-sqrt-poly r x m)
  (let* ((cs (kv-inf-coeffs r x m))
         (a0 (kv-sqrt (car cs))))
    (if (or (not a0) (ode-mentions-sym? a0 x) (kv-zero? a0))
        #f
        (let loop ((k 1) (as (list a0)))
          (cond ((> k m)
                 (foldl (lambda (acc j)
                          (list '+ acc (list '* (nth as j) (list '^ x (- m j)))))
                        0 (range (+ m 1))))
                (else
                 (let* ((inner (foldl (lambda (acc i)
                                        (list '+ acc (list '* (nth as i) (nth as (- k i)))))
                                      0
                                      (map (lambda (i) (+ i 1)) (range (- k 1)))))
                        (ak (try (simplify (list '/ (list '- (nth cs k) inner)
                                                  (list '* 2 a0)))
                                 (lambda (err) #f))))
                   (if (and ak (not (ode-mentions-sym? ak x)))
                       (loop (+ k 1) (append as (list ak)))
                       #f))))))))

; α∞ для знака s: r − W² − sW′ = 2W·α∞/x + O(1/x²)
(define (kv-inf-alpha r x w s)
  (let* ((ww (if (= s 1) w (list '* -1 w)))
         (e (simplify (together (list '* x (list '- r (list '^ ww 2) (diff x ww))))))
         (a (try (limit (list '/ e (list '* 2 ww)) x 'inf) (lambda (err) #f))))
    (and a (not (ode-mentions-sym? a x)) a)))

; данные на ∞: (W α+ α-) | 'impossible | 'unknown
(define (kv-inf-data r x o)
  (cond ((and (<= o 0) (kv-even-int? o))
         (let* ((m (/ (- o) 2))
                (w (and (<= m 12) (try (kv-inf-sqrt-poly r x m) (lambda (err) #f)))))
           (if w
               (let ((ap (kv-inf-alpha r x w 1)) (am (kv-inf-alpha r x w -1)))
                 (if (and (number? ap) (number? am))
                     (list w ap am)
                     'unknown))
               'unknown)))
        ((= o 2)
         (let* ((nd (kv-num-den r)) (s (car nd)) (t (cadr nd))
                (b (simplify (/ (coeff s x (degree s x)) (coeff t x (degree t x)))))
                (sq (kv-sqrt (simplify (list '+ 1 (list '* 4 b))))))
           (list 0
                 (simplify (list '* 1/2 (list '+ 1 sq)))
                 (simplify (list '* 1/2 (list '- 1 sq))))))
        ((> o 2) (list 0 0 1))
        (else 'impossible)))

; все наборы выбора α по полюсам: (0 1 0 …)
(define (kv-combos n)
  (if (= n 0) (list '())
      (let ((rest (kv-combos (- n 1))))
        (append (map (lambda (r) (cons 0 r)) rest)
                (map (lambda (r) (cons 1 r)) rest)))))

(define (kv-alpha p i) (if (= i 0) (cadr p) (caddr p)))

(define (kv-sum-alphas alphas combo)
  (let loop ((ps alphas) (cs combo) (acc 0))
    (if (null? ps) acc
        (loop (cdr ps) (cdr cs) (simplify (list '+ acc (kv-alpha (car ps) (car cs))))))))

; ω = Σ α_c/(x−c) + s∞·[√r]_∞
(define (kv-omega alphas combo inf s-inf x)
  (let loop ((ps alphas) (cs combo) (acc 0))
    (if (null? ps)
        (simplify (list '+ acc (list '* s-inf (car inf))))
        (loop (cdr ps) (cdr cs)
              (list '+ acc (list '* (kv-alpha (car ps) (car cs))
                                 (list '^ (list '- x (car (car ps))) -1)))))))

; ---------- многочлен P ----------

; уравнение P″ + 2ωP′ + (ω′ + ω² − r)P = 0, P = x^d + Σ c_k x^k; → P | #f
(define (kv-solve-p d om r x)
  (if (= d 0)
      (let ((ee (simplify (together (list '+ (diff x om) (list '^ om 2) (list '* -1 r))))))
        (and (kv-zero? ee) 1))
      (let* ((ks (range d))
         (cs (map (lambda (k) (string->symbol (string-append "kvc" (to-string k)))) ks))
         (p (foldl (lambda (acc k)
                     (list '+ acc (list '* (nth cs k) (list '^ x k))))
                   (list '^ x d) ks))
         (eq (simplify (together (list '+ (diff x (diff x p))
                                      (list '* 2 om (diff x p))
                                      (list '* (list '+ (diff x om) (list '^ om 2) (list '* -1 r)) p)))))
         (num (numer (together eq)))
         (cfs (coefficients (expand num) x))
         (eqs (map (lambda (c) (list '= c 0)) cfs))
         (sol (try (solve eqs cs) (lambda (err) #f))))
    (if (or (not sol) (null? sol))
        #f
        (let* ((s0 (car (set->list sol)))
               (p1 (if (null? s0) p (subst (map (lambda (e) (list (cadr e) (caddr e))) s0) p)))
               ; свободные параметры — нули (гомогенная система)
               (p2 (foldl (lambda (acc u) (subst (list (list u 0)) acc)) p1 cs))
               (p3 (simplify p2)))
          (and (not (kv-zero? p3)) p3))))))

; ---------- проверка и сборка ----------

(define (kv-check-solution eq yx y1)
  (ode-quiet (lambda ()
               (try (let ((c (dsolve-check eq (list '= (list (car yx) (cadr yx)) y1) yx)))
                      (and c (not (equal? c #f))))
                    (lambda (err) #f)))))

; y₂ = y₁·∫ e^{−∫a}/y₁² dx (невычисленный интеграл допустим)
(define (kv-second y1 a x)
  (let* ((y1 (kv-exp-log y1 x))
         (ea (ode-quiet (lambda () (integrate a x))))
         (w (ode-quiet (lambda ()
                         (integrate (simplify (list '* (kv-exp-log
                                                        (list 'exp (simplify (list '* -1 ea))) x)
                                                    (list '^ y1 -2)))
                                    x)))))
    (simplify (list '* y1 w))))

; вещественная форма: для вещественных a, b сопряжённое к решению — тоже решение,
; поэтому Re y₁ и Im y₁ дают вещественную ФСР (Бессель 1/2: cos x/√x, sin x/√x).
(define (kv-conj e)
  (simplify (subst (list (list '%i (list '* -1 '%i))) e)))

; e = R + i·I (линейно по %i) → (R . I)
(define (kv-split-i e)
  (cond ((and (pair? e) (equal? (car e) '+) (> (length e) 2))
         (let loop ((ts (cdr e)) (R 0) (I 0))
           (if (null? ts) (cons R I)
               (let ((p (kv-split-i (car ts))))
                 (loop (cdr ts)
                       (simplify (list '+ R (car p)))
                       (simplify (list '+ I (cdr p))))))))
        ((and (pair? e) (equal? (car e) '-) (= (length e) 2))
         (let ((p (kv-split-i (cadr e))))
           (cons (simplify (list '- 0 (car p))) (simplify (list '- 0 (cdr p))))))
        ((and (pair? e) (equal? (car e) '*)
              (any? (lambda (z) (equal? z '%i)) (cdr e)))
         (cons 0 (simplify (foldl (lambda (acc z) (if (equal? z '%i) acc (list '* acc z)))
                                  1 (cdr e)))))
        (else (cons e 0))))

; exp(R + i·I) → exp(R)·(cos I + i·sin I) — только для показателей с мнимой частью
(define (kv-trig e)
  (cond ((number? e) e)
        ((symbol? e) e)
        ((and (pair? e) (equal? (car e) 'exp) (= (length e) 2))
         (let ((p (kv-split-i (cadr e))))
           (if (kv-zero? (cdr p))
               e
               (list '* (list 'exp (car p))
                     (list '+ (list 'cos (cdr p))
                           (list '* '%i (list 'sin (cdr p))))))))
        ((pair? e) (map kv-trig e))
        (else e)))

; t = c·log x (c без x) → c; t = log x → 1; иначе #f
(define (kv-log-coef t x)
  (cond ((and (pair? t) (equal? (car t) 'log) (= (length t) 2) (equal? (cadr t) x)) 1)
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3))
         (let ((u (cadr t)) (v (caddr t)))
           (cond ((and (pair? v) (equal? (car v) 'log) (= (length v) 2)
                       (equal? (cadr v) x) (not (ode-mentions-sym? u x))) u)
                 ((and (pair? u) (equal? (car u) 'log) (= (length u) 2)
                       (equal? (cadr u) x) (not (ode-mentions-sym? v x))) v)
                 (else #f))))
        (else #f)))

; exp(Σ t) → ∏ exp(t), exp(c·log x) → x^c: y₁ = x^{3/4}, а не exp(3/4·log x)
(define (kv-exp-log e x)
  (if (not (and (pair? e) (equal? (car e) 'exp) (= (length e) 2)))
      e
      (let* ((arg (cadr e))
             (terms (if (and (pair? arg) (equal? (car arg) '+)) (cdr arg) (list arg))))
        (simplify (foldl (lambda (acc t)
                           (let ((c (kv-log-coef t x)))
                             (list '* acc (if c (list '^ x c) (list 'exp t)))))
                         1 terms)))))

(define (kv-realify y1 y2)
  (let* ((e (try (simplify (expand (kv-trig y1))) (lambda (err) y1)))
         (p (try (kv-split-i e) (lambda (err) (cons e 0))))
         (u (simplify (car p)))
         (v (simplify (cdr p))))
    (if (and (not (kv-zero? u)) (not (kv-zero? v))
             (not (ode-mentions-sym? u '%i)) (not (ode-mentions-sym? v '%i)))
        (list u v)
        (list y1 y2))))

; ---------- шаги ----------

(define (kv-step-normal a b r yx)
  (if (step-log-enabled?)
      (record-step 'kovacic-normal "Ковачич: нормальная форма"
                   (string-append "z = y·e^(½∫a dx), z″ = r·z; a = " (ode-mp a)
                                  ", b = " (ode-mp b) "; r = a²/4 + a′/2 − b = " (ode-mp r))
                   (car yx) r 'main))
  #t)

(define (kv-step-poles r poles o)
  (if (step-log-enabled?)
      (record-step 'kovacic-poles "Ковачич: полюса r и порядок на ∞"
                   (string-append "полюса: "
                                  (if (null? poles) "нет"
                                      (ode-mp-join (map (lambda (p)
                                                          (string-append "x = " (ode-mp (car p))
                                                                         " (порядок " (to-string (cadr p)) ")"))
                                                        poles)))
                                  "; o(∞) = " (to-string o))
                   '() '() 'main))
  #t)

(define (kv-step-cases cs)
  (if (step-log-enabled?)
      (let ((ps (filter (lambda (i) (nth cs i)) '(0 1 2))))
        (record-step 'kovacic-cases "Ковачич: какие случаи возможны"
                     (cond ((null? ps) "ни один случай невозможен — лиувиллевых решений нет")
                           ((= (length ps) 1)
                            (string-append "возможен только случай " (to-string (+ (car ps) 1))))
                           (else
                            (string-append "возможны случаи: "
                                           (ode-mp-join (map (lambda (i) (to-string (+ i 1))) ps)))))
                     '() '() 'main)))
  #t)

(define (kv-step-case1 om p d)
  (if (step-log-enabled?)
      (record-step 'kovacic-case1 "Ковачич: случай 1"
                   (string-append "d = " (to-string d) "; ω = " (ode-mp om)
                                  "; P = " (ode-mp p) "; z = P·e^(∫ω dx)")
                   om p 'main))
  #t)

(define (kv-step-solution y1 y2)
  (if (step-log-enabled?)
      (record-step 'kovacic-solution "Ковачич: решение"
                   "y₁ проверено подстановкой; y₂ = y₁·∫e^(−∫a)/y₁² dx — по формуле понижения порядка"
                   y1 y2 'main))
  #t)

(define (kv-step-none poles o cs)
  (if (step-log-enabled?)
      (record-step 'kovacic-none "Ковачич: лиувиллевых решений нет"
                   (string-append "сертификат отсева: полюса " (to-string (map cadr poles))
                                  ", o(∞) = " (to-string o)
                                  "; условия случаев: " (to-string cs) " — все нарушены")
                   '() '() 'main))
  #t)

; ---------- сертификаты ----------

(define (kv-cert-none poles o cs) (list 'kovacic-none poles o cs))
(define (kv-cert-case1 poles o om p r) (list 'kovacic-case1 poles o om p r))

; независимая проверка сертификата: (kovacic-check eq cert yx) → #t | #f
(define (kovacic-check eq cert yx)
  (ode-quiet (lambda () (kv-check-cert eq cert yx))))

(define (kv-check-cert eq cert yx)
  (if (not (and (pair? cert) (pair? (cdr cert)) (pair? yx) (= (length yx) 2)))
      #f
      (if (not (or (equal? (car cert) 'kovacic-none)
                   (equal? (car cert) 'kovacic-case1)
                   (equal? (car cert) 'kovacic-case2)
                   (equal? (car cert) 'kovacic-case3)))
          #f
          (let* ((y (car yx)) (x (cadr yx))
                 (cb (try (kv-coeffs eq y x) (lambda (err) #f))))
            (if (not cb)
                #f
                (let* ((a (car cb)) (b (cadr cb)) (r (kv-r a b x))
                       (poles (try (kv-poles r x) (lambda (err) 'not-rational))))
                  (if (equal? poles 'not-rational)
                      #f
                      (let* ((o (kv-ord-inf r x)) (cs (kv-cases poles o)))
                        (cond ((equal? (car cert) 'kovacic-none)
                               (and (every? (lambda (c) (not c)) cs)
                                    (equal? (nth cert 1) poles)
                                    (= (nth cert 2) o)
                                    (equal? (nth cert 3) cs)))
                              ((equal? (car cert) 'kovacic-case2)
                               (let ((om (nth cert 3)))
                                 (and (not (null? om))
                                      (equal? (nth cert 1) poles)
                                      (= (nth cert 2) o)
                                      (kv-riccati-zero?
                                       (simplify (list '+ om (list '* -1/2 a))) a b x))))
                              ((equal? (car cert) 'kovacic-case3)
                               (let ((om (nth cert 3)))
                                 (and (not (null? om))
                                      (equal? (nth cert 1) poles)
                                      (= (nth cert 2) o)
                                      (kv-riccati-zero?
                                       (simplify (list '+ om (list '* -1/2 a))) a b x))))
                              (else
                               (let ((om (nth cert 3)) (p (nth cert 4)))
                                 (and (not (null? om))
                                      (not (null? p))
                                      (equal? (nth cert 1) poles)
                                      (= (nth cert 2) o)
                                      (kv-zero?
                                       (simplify (together
                                                  (list '+ (diff x (diff x p))
                                                        (list '* 2 om (diff x p))
                                                        (list '* (list '+ (diff x om)
                                                                        (list '^ om 2)
                                                                        (list '* -1 r))
                                                              p)))))
                                      (kv-check-solution
                                       eq yx
                                       (simplify (list '* p
                                                       (list 'exp
                                                             (integrate (simplify (list '+ om
                                                                                        (list '* -1/2 a)))
                                                                        x)))))))))))))))))

; ---------- поиск случая 1 ----------

; → (om p d y1 y2) | #f
(define (kv-try-case1 eq yx a b r x poles inf alphas)
  (let loop ((combos (kv-combos (length alphas))) (done #f))
    (if (or done (null? combos)) done
        (let* ((combo (car combos))
               (sum (kv-sum-alphas alphas combo))
               (res (let try-si ((si 0))
                      (if (> si 1) #f
                          (let* ((al-inf (if (= si 0) (cadr inf) (caddr inf)))
                                 (d (simplify (list '- al-inf sum))))
                            (if (and (kv-int? d) (>= d 0) (<= d 4))
                                (let* ((om (kv-omega alphas combo inf (if (= si 0) 1 -1) x))
                                       (p (kv-solve-p d om r x)))
                                  (or (and p (list om p d))
                                      (try-si (+ si 1))))
                                (try-si (+ si 1))))))))
          (if res
              (let* ((y1 (simplify (list '* (cadr res)
                                         (kv-exp-log
                                          (list 'exp (ode-quiet (lambda ()
                                                                  (integrate (simplify (list '+ (car res)
                                                                                             (list '* -1/2 a)))
                                                                             x))))
                                          x)))))
                (if (kv-check-solution eq yx y1)
                    (let* ((y2 (kv-second y1 a x))
                           (rl (kv-realify y1 y2)))
                      (list (car res) (cadr res) (caddr res) (car rl) (cadr rl)))
                    (loop (cdr combos) done)))
              (loop (cdr combos) done))))))

; ---------- случай 2 ----------

(define (kv-int-list l) (filter kv-int? l))

; E_c по полюсам и E_∞ (только целые значения)
(define (kv-e-sets poles r x o)
  (let ((ecs (map (lambda (p)
                    (let ((c (car p)) (m (cadr p)))
                      (cond ((= m 1) (list 4))
                            ((= m 2)
                             (let* ((b (try (simplify (list '* (list '^ (list '- x c) 2) r))
                                            (lambda (err) #f)))
                                    (b (and b (kv-at b x c)))
                                    (s (and b (kv-sqrt (simplify (list '+ 1 (list '* 4 b)))))))
                               (if (not (and b s))
                                   (list 2)
                                   (kv-int-list (list 2
                                                      (simplify (list '+ 2 (list '* 2 s)))
                                                      (simplify (list '- 2 (list '* 2 s))))))))
                            (else (list m)))))
                  poles))
        (ef (cond ((> o 2) (list 0 2 4))
                  ((= o 2)
                   (let* ((nd (kv-num-den r)) (s (car nd)) (t (cadr nd))
                          (b (simplify (/ (coeff s x (degree s x)) (coeff t x (degree t x)))))
                          (sq (kv-sqrt (simplify (list '+ 1 (list '* 4 b))))))
                     (kv-int-list (list 2
                                        (simplify (list '+ 2 (list '* 2 sq)))
                                        (simplify (list '- 2 (list '* 2 sq)))))))
                  (else (list o)))))
    (list ecs ef)))

; декартово произведение наборов
(define (kv-prod sets)
  (if (null? sets) (list '())
      (let ((rest (kv-prod (cdr sets))))
        (apply append (map (lambda (v) (map (lambda (u) (cons v u)) rest)) (car sets))))))

; θ = ½ Σ e_c/(x−c)
(define (kv-theta poles combo x)
  (let loop ((ps poles) (cs combo) (acc 0))
    (if (null? ps)
        (simplify (list '* 1/2 acc))
        (loop (cdr ps) (cdr cs)
              (list '+ acc (list '* (car cs) (list '^ (list '- x (car (car ps))) -1)))))))

; P из уравнения p''' + 3θp'' + (3θ²+3θ'−4r)p' + (θ''+3θθ'+θ³−4rθ−2r')p = 0
(define (kv-solve-p3 d th r x)
  (if (= d 0)
      (let ((e0 (simplify (together (list '+ (diff x (diff x th))
                                           (list '* 3 th (diff x th))
                                           (list '^ th 3)
                                           (list '* -4 r th)
                                           (list '* -2 (diff x r)))))))
        (and (kv-zero? e0) 1))
      (let* ((ks (range d))
             (cs (map (lambda (k) (string->symbol (string-append "kvc" (to-string k)))) ks))
             (p (foldl (lambda (acc k) (list '+ acc (list '* (nth cs k) (list '^ x k))))
                       (list '^ x d) ks))
             (eq (simplify (together (list '+
                                          (diff x (diff x (diff x p)))
                                          (list '* 3 th (diff x (diff x p)))
                                          (list '* (list '+ (list '* 3 (list '^ th 2))
                                                           (list '* 3 (diff x th))
                                                           (list '* -4 r))
                                                (diff x p))
                                          (list '* (list '+ (diff x (diff x th))
                                                           (list '* 3 th (diff x th))
                                                           (list '^ th 3)
                                                           (list '* -4 r th)
                                                           (list '* -2 (diff x r)))
                                                p)))))
             (num (numer (together eq)))
             (cfs (coefficients (expand num) x))
             (eqs (map (lambda (c) (list '= c 0)) cfs))
             (sol (try (solve eqs cs) (lambda (err) #f))))
        (if (or (not sol) (null? sol))
            #f
            (let* ((s0 (car (set->list sol)))
                   (p1 (if (null? s0) p (subst (map (lambda (e) (list (cadr e) (caddr e))) s0) p)))
                   (p2 (foldl (lambda (acc u) (subst (list (list u 0)) acc)) p1 cs)))
              (and (not (kv-zero? (simplify p2))) (simplify p2)))))))

; φ = θ + P′/P; ω — корни ω² − φω + (φ′/2 + φ²/2 − r) = 0 (явная формула: дискриминант может содержать √)
(define (kv-case2-omega th p r x)
  (let* ((phi (simplify (together (list '+ th (list '* (diff x p) (list '^ p -1))))))
         (q (simplify (together (list '+ (list '* 1/2 (diff x phi))
                                      (list '* 1/2 (list '^ phi 2))
                                      (list '* -1 r)))))
         (disc (simplify (together (list '- (list '^ phi 2) (list '* 4 q))))))
    (list (simplify (kv-rad-simplify (list '* 1/2 (list '+ phi (kv-sqrt disc))) x))
          (simplify (kv-rad-simplify (list '* 1/2 (list '- phi (kv-sqrt disc))) x)))))

; подбор d и θ для одного набора e_c
(define (kv-case2-poles ef combo sum poles x r)
  (let loop ((fs ef))
    (if (null? fs) #f
        (let ((d (simplify (list '* 1/2 (list '- (car fs) sum)))))
          (if (and (kv-int? d) (>= d 0) (<= d 4))
              (let* ((th (kv-theta poles combo x)) (p (kv-solve-p3 d th r x)))
                (or (and p (list th p d)) (loop (cdr fs))))
              (loop (cdr fs)))))))

; e = c·x^p (c без x) → (c . p); иначе #f
(define (kv-mono e x)
  (cond ((number? e) (cons e 0))
        ((equal? e x) (cons 1 1))
        ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (equal? (cadr e) x) (number? (caddr e)))
         (cons 1 (caddr e)))
        ((and (pair? e) (equal? (car e) '*))
         (let loop ((ts (cdr e)) (c 1) (p 0))
           (if (null? ts)
               (cons c p)
               (let ((m (kv-mono (car ts) x)))
                 (if m (loop (cdr ts) (* c (car m)) (+ p (cdr m))) #f)))))
        (else #f)))

; (c·x^p)^{1/2} → √c·x^{p/2}: убирает радикал из знаменателя (x·(4/x)^{1/2} → 2√x)
(define (kv-rad-simplify e x)
  (cond ((number? e) e)
        ((symbol? e) e)
        ((and (pair? e) (equal? (car e) '^) (= (length e) 3) (equal? (caddr e) 1/2))
         (let ((m (kv-mono (cadr e) x)))
           (if m
               (list '* (kv-sqrt (car m)) (list '^ x (/ (cdr m) 2)))
               e)))
        ((pair? e) (map (lambda (z) (kv-rad-simplify z x)) e))
        (else e)))

; y = e^{∫(ω − a/2) dx}
(define (kv-exp-int w a x)
  (let* ((ee (simplify (kv-rad-simplify (list '+ w (list '* -1/2 a)) x)))
         (ii (ode-quiet (lambda () (integrate ee x)))))
    (simplify (kv-exp-log (list 'exp (simplify (kv-rad-simplify ii x))) x))))

; ω — лог-производная y₁; y₁ решает y″ + a·y′ + b·y = 0 ⇔ ω′ + ω² + a·ω + b = 0
; (проверка без дифференцирования exp(√x), которое не сводит dsolve-check)
(define (kv-riccati-zero? w a b x)
  (kv-zero? (simplify (together (list '+ (diff x w) (list '^ w 2) (list '* a w) b)))))

; первый корень ω, дающий проверенное y₁
(define (kv-case2-y1 eq yx a b ws x)
  (if (null? ws)
      #f
      (let* ((w (car ws))
             (y1 (kv-exp-int w a x))
             (ok (or (kv-riccati-zero? (simplify (list '+ w (list '* -1/2 a))) a b x)
                     (kv-check-solution eq yx y1))))
        (if ok
            (let* ((y2 (kv-second y1 a x)) (rl (kv-realify y1 y2)))
              (list w (car rl) (cadr rl)))
            (kv-case2-y1 eq yx a b (cdr ws) x)))))

; → (om p d y1 y2) | #f
(define (kv-try-case2 eq yx a b r x poles o)
  (let* ((es (kv-e-sets poles r x o)) (ecs (car es)) (ef (cadr es)))
    (let loop ((combos (kv-prod ecs)) (done #f))
      (if (or done (null? combos)) done
          (let* ((combo (car combos))
                 (sum (foldl + 0 combo))
                 (res (kv-case2-poles ef combo sum poles x r)))
            (if res
                (let ((ws (kv-case2-omega (car res) (cadr res) r x)))
                  (if ws
                      (let ((found (kv-case2-y1 eq yx a b ws x)))
                        (if found
                            (list (car found) (cadr res) (caddr res) (nth found 1) (nth found 2))
                            (loop (cdr combos) done)))
                      (loop (cdr combos) done)))
                (loop (cdr combos) done)))))))

(define (kv-cert-case2 poles o om p r) (list 'kovacic-case2 poles o om p r))
(define (kv-cert-case3 poles o om n) (list 'kovacic-case3 poles o om n))

; случай 3 (n = 4): результат или #f
(define (kv-case3-run eq yx a b r x poles o)
  (let ((res (try (ode-quiet (lambda () (kv-try-case3-n4 eq yx a b r x poles o)))
                  (lambda (err) #f))))
    (if res
        (begin
          (if (step-log-enabled?)
              (record-step 'kovacic-case3 "Ковачич: случай 3 (n = 4)"
                           (string-append "d = 0; ω = " (ode-mp (car res))
                                          "; Q(ω) степени 4; z = e^(∫ω dx)")
                           (ode-mp (car res)) (cadr res) 'main))
          (kv-step-solution (nth res 2) (nth res 3))
          (ode-solution 'general
                        (list (list '= (list (car yx) (cadr yx))
                                    (simplify (list '+ (list '* 'C1 (nth res 2))
                                                    (list '* 'C2 (nth res 3))))))
                        '(C1 C2) '() 'ok 'kovacic
                        (kv-cert-case3 poles o (car res) 4)))
        #f)))

; ---------- случай 3 (n = 4, d = 0) ----------

(define (kv-fact k) (if (<= k 1) 1 (* k (kv-fact (- k 1)))))

; E-набор случая 3: {6 + 12k/n·√(1+4b)}, k = −n/2…n/2, только целые
(define (kv-c3-e-set b n)
  (let* ((s (kv-sqrt (simplify (list '+ 1 (list '* 4 b)))))
         (js (range (+ n 1))))
    (kv-int-list (map (lambda (j)
                        (let ((k (- j (/ n 2))))
                          (simplify (list '+ 6 (list '* (/ (* 12 k) n) s)))))
                      js))))

; (E_c …) и E_∞ | #f (порядок > 2 или o ≠ 2 не поддержаны)
(define (kv-c3-sets poles r x o n)
  (let ((ecs (map (lambda (p)
                    (let ((c (car p)) (m (cadr p)))
                      (cond ((= m 1) (list 12))
                            ((= m 2)
                             (let* ((b (try (limit (list '* (list '^ (list '- x c) 2) r) x c)
                                            (lambda (e) #f))))
                               (if (number? b) (kv-c3-e-set b n) '())))
                            (else '()))))
                  poles)))
    (if (any? (lambda (e) (null? e)) ecs)
        #f
        (if (= o 2)
            (let* ((nd (kv-num-den r)) (s (car nd)) (t (cadr nd))
                   (b (simplify (/ (coeff s x (degree s x)) (coeff t x (degree t x))))))
              (list ecs (kv-c3-e-set b n)))
            #f))))

; θ = n/12·Σ e_c/(x−c)
(define (kv-theta-sum poles combo x)
  (let loop ((ps poles) (cs combo) (acc 0))
    (if (null? ps) (simplify (together acc))
        (loop (cdr ps) (cdr cs)
              (list '+ acc (list '* (car cs) (list '^ (list '- x (car (car ps))) -1)))))))

; S = ∏(x−c)
(define (kv-c3-s-pol poles x)
  (simplify (foldl (lambda (acc p) (list '* acc (list '- x (car p)))) 1 poles)))

; P_n = −1, P_{i−1} = −S P_i′ + ((n−i)S′ − Sθ)P_i − (n−i)(i+1)S²r P_{i+1}
(define (kv-c3-ps s th r n x)
  (let loop ((i n) (ps (list (cons n -1))) (pnext 0))
    (if (< i 0)
        ps
        (let* ((pi (cdr (assoc i ps)))
               (pim1 (simplify (together (list '+
                                               (list '* -1 s (diff x pi))
                                               (list '* (list '- (list '* (- n i) (diff x s))
                                                               (list '* s th))
                                                     pi)
                                               (list '* -1 (- n i) (+ i 1) (list '^ s 2) r pnext))))))
          (loop (- i 1) (cons (cons (- i 1) pim1) ps) pi)))))

; Q(ω) = Σ S^i P_i/(n−i)!·ω^i
(define (kv-c3-quartic ps s n x)
  (foldl (lambda (acc i)
           (list '+ acc (list '* (list '^ s i)
                              (/ (cdr (assoc i ps)) (kv-fact (- n i)))
                              (list '^ 'kvw i))))
         0 (range (+ n 1))))

; корни Q: свёрнутая степень (^ L k) — решаем L = 0, иначе solve по исходной сумме
(define (kv-c3-roots q x)
  (let ((qq (simplify (together q))))
    (if (and (pair? qq) (equal? (car qq) '^) (= (length qq) 3) (equal? (caddr qq) 4))
        (let ((sol (try (set->list (solve (list '= (cadr qq) 0) 'kvw)) (lambda (e) '()))))
          (if (null? sol) #f sol))
        (let ((sol (try (set->list (solve (list '= q 0) 'kvw)) (lambda (e) '()))))
          (if (null? sol) #f sol)))))

; → (w n y1 y2) | #f
(define (kv-try-case3-n4 eq yx a b r x poles o)
  (let ((sets (try (kv-c3-sets poles r x o 4) (lambda (e) #f))))
    (if (not sets)
        #f
        (let* ((ecs (car sets)) (einf (cadr sets)))
          (let loop ((combos (kv-prod ecs)) (done #f))
            (if (or done (null? combos)) done
                (let* ((combo (car combos)) (sum (foldl + 0 combo))
                       (res (let try-e ((fs einf))
                              (if (null? fs) #f
                                  (let ((d (simplify (list '* 1/3 (list '- (car fs) sum)))))
                                    (if (and (kv-int? d) (= d 0))
                                        (let* ((th (simplify (list '* 1/3 (kv-theta-sum poles combo x))))
                                               (s (kv-c3-s-pol poles x))
                                               (ps (try (kv-c3-ps s th r 4 x) (lambda (e) #f))))
                                          (if (and ps (kv-zero? (simplify (together (cdr (assoc -1 ps))))))
                                              (let* ((q (kv-c3-quartic ps s 4 x))
                                                     (ws (kv-c3-roots q x)))
                                                (if ws (list th s q ws) (try-e (cdr fs))))
                                              (try-e (cdr fs))))
                                        (try-e (cdr fs))))))))
                  (if res
                      (let loop-w ((ws (nth res 3)))
                        (if (null? ws)
                            (loop (cdr combos) done)
                            (let* ((w (car ws)) (y1 (kv-exp-int w a x)))
                              (if (or (kv-riccati-zero? (simplify (list '+ w (list '* -1/2 a))) a b x)
                                      (kv-check-solution eq yx y1))
                                  (let* ((y2 (kv-second y1 a x)) (rl (kv-realify y1 y2)))
                                    (list w 4 (car rl) (cadr rl)))
                                  (loop-w (cdr ws))))))
                      (loop (cdr combos) done)))))))))

; ---------- вход из dsolve ----------

(define (kv-solve eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))
                (= (ode-order eq (car yx) (cadr yx)) 2)))
      #f
      (let* ((y (car yx)) (x (cadr yx))
             (cb (try (kv-coeffs eq y x) (lambda (err) #f))))
        (if (not cb)
            #f
            (let* ((a (car cb)) (b (cadr cb)) (r (kv-r a b x)))
              (kv-run eq yx a b r x))))))

(define (kv-run eq yx a b r x)
  (let* ((poles (try (ode-quiet (lambda () (kv-poles r x))) (lambda (err) 'not-rational))))
    (kv-step-normal a b r yx)
    (if (equal? poles 'not-rational)
        ; полюса не над ℚ — честное «не знаю»: не отказ, пропускаем к следующим методам
        #f
        (let* ((o (kv-ord-inf r x)) (cs (kv-cases poles o)))
          (kv-step-poles r poles o)
          (kv-step-cases cs)
          (let* ((res1 (and (car cs) (kv-case1-run eq yx a b r x poles o)))
                 (res2 (and (not res1) (cadr cs) (kv-case2-run eq yx a b r x poles o)))
                 (res3 (and (not res1) (not res2) (caddr cs)
                            (kv-case3-run eq yx a b r x poles o))))
            (cond (res1 res1)
                  (res2 res2)
                  (res3 res3)
                  ; какой-то случай возможен, но не решён — «не знаю», не отказ
                  ((or (car cs) (cadr cs) (caddr cs))
                   (if (and (caddr cs) (step-log-enabled?))
                       (record-step 'kovacic-case3 "Ковачич: случай 3"
                                    "условия случая 3 выполнены (полюса ≤ 2, o(∞) ≥ 2), но реализация n = 4/6/12 не доведена — unknown, не отказ"
                                    '() '() 'main)
                       #f)
                   #f)
                  (else
                   (kv-step-none poles o cs)
                   (ode-solution 'general '() '() '() 'no-liouvillian 'kovacic
                                 (kv-cert-none poles o cs)))))))))

; случай 1: результат или #f
(define (kv-case1-run eq yx a b r x poles o)
  (let* ((al (try (ode-quiet (lambda () (kv-pole-alphas poles r x))) (lambda (err) 'unknown)))
         (inf (try (ode-quiet (lambda () (kv-inf-data r x o))) (lambda (err) 'unknown))))
    (if (or (equal? al 'unknown) (equal? inf 'unknown) (equal? inf 'impossible))
        #f
        (let ((res (try (ode-quiet (lambda () (kv-try-case1 eq yx a b r x poles inf al)))
                        (lambda (err) #f))))
          (if res
              (begin
                (kv-step-case1 (car res) (cadr res) (caddr res))
                (kv-step-solution (nth res 3) (nth res 4))
                (ode-solution 'general
                              (list (list '= (list (car yx) (cadr yx))
                                          (simplify (list '+ (list '* 'C1 (nth res 3))
                                                          (list '* 'C2 (nth res 4))))))
                              '(C1 C2) '() 'ok 'kovacic
                              (kv-cert-case1 poles o (car res) (cadr res) r)))
              #f)))))

; случай 2: результат или #f
(define (kv-case2-run eq yx a b r x poles o)
  (let ((res (try (ode-quiet (lambda () (kv-try-case2 eq yx a b r x poles o)))
                  (lambda (err) #f))))
    (if res
        (begin
          (if (step-log-enabled?)
              (record-step 'kovacic-case2 "Ковачич: случай 2"
                           (string-append "E_c и E_∞ — целые; d = " (to-string (caddr res))
                                          "; θ = " (ode-mp (car res))
                                          "; φ = θ + P′/P, P = " (ode-mp (cadr res))
                                          "; ω — корень ω² − φω + (φ′/2 + φ²/2 − r) = 0")
                           (ode-mp (car res)) (cadr res) 'main))
          (kv-step-solution (nth res 3) (nth res 4))
          (ode-solution 'general
                        (list (list '= (list (car yx) (cadr yx))
                                    (simplify (list '+ (list '* 'C1 (nth res 3))
                                                    (list '* 'C2 (nth res 4))))))
                        '(C1 C2) '() 'ok 'kovacic
                        (kv-cert-case2 poles o (car res) (cadr res) r)))
        #f)))

; публичный вход (для тестов и языка): (kovacic eq '(y x))
(define (kovacic eq yx) (kv-solve eq yx))

(define *ode-kovacic-loaded* #t)
