; reduction.lisp — понижение порядка и автономные уравнения (шаг ODE.5b)
; 1) известное решение y₁ линейного однородного уравнения 2-го порядка →
;    второе y₂ = y₁·∫ e^{−∫p dx}/y₁² dx (формула Абеля), (reduce-order eq (y x) y1).
; 2) F(x, y′, y″) = 0 (нет y): замена p = y′ → уравнение 1-го порядка по p(x), затем квадратура.
; 3) F(y, y′, y″) = 0 (нет x, автономное): p(y) = y′, y″ = p·dp/dy → 1-го порядка по p(y),
;    затем dy/dx = p(y) — разделяющееся уравнение.
; Каждое решение проверяется dsolve-check (после обратной подстановки).
(module ode
  (export reduce-order ode-drop-y ode-autonomous))


; ---------- общее: имена констант, структурная замена ----------

(define (rd-const-names n)
  (map (lambda (k) (string->symbol (string-append "C" (to-string (+ k 1))))) (range n)))

; переименовать символы по парам (from . to)
(define (rd-rename e pairs)
  (cond ((null? pairs) e)
        (else (rd-rename (ode-replace e (car (car pairs)) (cdr (car pairs))) (cdr pairs)))))

; константы интегрирования p(y) переименовываем в rdK1…, чтобы свободная постоянная
; второго интегрирования не столкнулась с ними (иначе dsolve называет её тоже C1)
(define (rd-fresh-consts cs)
  (let loop ((xs cs) (k 0) (acc '()))
    (if (null? xs)
        (reverse acc)
        (loop (cdr xs) (+ k 1)
              (cons (cons (car xs) (string->symbol (string-append "rdK" (to-string (+ k 1)))))
                    acc)))))

; обратное переименование: rdKᵢ → C_{off+i} (свободные имена после констант квадратуры)
(define (rd-shift-consts cs off)
  (let loop ((xs cs) (k 0) (acc '()))
    (if (null? xs)
        (reverse acc)
        (loop (cdr xs) (+ k 1)
              (cons (cons (string->symbol (string-append "rdK" (to-string (+ k 1))))
                          (string->symbol (string-append "C" (to-string (+ off k 1)))))
                    acc)))))

; ---------- 1) понижение порядка по известному решению ----------

; term c·log(u) → (u . c); иначе #f
(define (rd-log-term t)
  (let ((is-log? (lambda (z) (and (pair? z) (equal? (car z) 'log) (= (length z) 2)))))
    (cond ((is-log? t) (cons (cadr t) 1))
          ((and (pair? t) (equal? (car t) '*))
           (let* ((fs (cdr t))
                  (ls (filter is-log? fs))
                  (os (filter (lambda (z) (not (is-log? z))) fs)))
             (if (= (length ls) 1)
                 (cons (cadr (car ls)) (if (null? os) 1 (simplify (cons '* os))))
                 #f)))
          (else #f))))

; S — сумма c·log(u) → ((u . c) …); иначе #f
(define (rd-log-sum S)
  (let loop ((ts (if (and (pair? S) (equal? (car S) '+)) (cdr S) (list S))) (acc '()))
    (cond ((null? ts) (reverse acc))
          (else (let ((p (rd-log-term (car ts))))
                  (if p (loop (cdr ts) (cons p acc)) #f))))))

; exp(Σ c·log u) → Π u^c (чтобы интеграл брался как от рациональной функции)
(define (rd-exp-logs e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'exp) (= (length e) 2))
         (let ((ls (rd-log-sum (cadr e))))
           (if ls
               (simplify (cons '* (map (lambda (p) (list '^ (car p) (cdr p))) ls)))
               e)))
        ((equal? (car e) 'diff) e)
        (else (map rd-exp-logs e))))

; первый интеграл, который не остался невычисленным
(define (rd-first-integral cands x)
  (if (null? cands) #f
      (let ((r (simplify (integrate (car cands) x))))
        (if (rd-unresolved? r) (rd-first-integral (cdr cands) x) r))))

(define (rd-unresolved? e)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) 'integrate) #t)
        (else (any? rd-unresolved? e))))

; коэффициент p при y′ в уравнении a₂·y″ + a₁·y′ + a₀·y = f: p = a₁/a₂;
; #f — коэффициенты зависят от y или a₂ = 0
(define (rd-p-coeff eq y x)
  (let* ((e (ode-normalize eq))
         (d2 (ode-nth-deriv y x 2))
         (d1 (ode-nth-deriv y x 1))
         (r2 (ode-coeff-of d2 e y x))
         (r1 (ode-coeff-of d1 e y x)))
    (and r2 r1
         (not (ode-zero? (simplify (car r2))))
         (not (ode-y-node-any? (car r1) y x)) (not (ode-y-node-any? (car r2) y x))
         (simplify (list '/ (car r1) (car r2))))))

; (reduce-order eq (y x) y1) → ode-solution с вторым решением y₂ = y₁·∫e^{−∫p}/y₁²
(define (reduce-order eq yx y1)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)) (n (ode-order eq y x)))
        (if (not (= n 2))
            #f
            (let ((p (rd-p-coeff eq y x)))
              (if (not p)
                  #f
                  (let* ((y1 (simplify y1))
                         (Ip (ode-quiet (lambda () (simplify (integrate p x)))))
                         (q (simplify (list '/ (list 'exp (list '- 0 Ip)) (list '^ y1 2))))
                         (Iq (ode-quiet (lambda () (rd-first-integral (list q (rd-exp-logs q)) x)))))
                    (if (not Iq)
                        #f
                        (let* ((y2 (simplify (list '* y1 Iq)))
                               (rhs (simplify (list '+ (list '* 'C1 y1) (list '* 'C2 y2))))
                               (sol (list '= (list y x) rhs))
                               (W (ode-quiet (lambda () (lo-w2 y1 y2 x)))))
                          (with-step ('ode-re-known "Понижение порядка (известное y₁)" eq
                                      :comment (string-append "p = a₁/a₂ = " (ode-mp p)
                                                              "; y₂ = y₁·∫e^{−∫p}/y₁² = " (ode-mp y2)
                                                              "; W(y₁, y₂) = " (ode-mp W))
                                      :after (lambda (r) (ode-field r :solutions)))
                            (if (dsolve-check eq sol yx)
                                (ode-solution 'general (list sol) (list 'C1 'C2) '() 'ok 'reduction #t)
                                #f)))))))))))

; ---------- 2) F(x, y′, y″) = 0: замена p = y′ ----------

; заменить y″ → p′, y′ → p (y не должно встречаться — проверяется отдельно)
(define (rd-to-p e y x xv pv)
  (let* ((d2 (ode-nth-deriv y x 2))
         (d1 (ode-nth-deriv y x 1))
         (dp (list 'diff (list pv xv) xv)))
    (ode-replace (ode-replace e d2 dp) d1 (list pv xv))))

; (ode-drop-y eq (y x)) → ode-solution или #f; уравнение без y
(define (ode-drop-y eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)) (n (ode-order eq y x)) (e (ode-normalize eq)))
        (if (or (not (= n 2)) (ode-y-node? e y x) (rd-mentions-y? e y x))
            #f
            (let* ((peq (rd-to-p e y x x 'p))
                   (r (ode-quiet (lambda () (try (dsolve (list '= peq 0) (list 'p x)) (lambda (err) #f))))))
              (if (not (and r (equal? (ode-status r) 'ok) (pair? (ode-solutions r))))
                  #f
                  (let* ((prhs (caddr (car (ode-solutions r))))
                         (yrhs (simplify (list '+ (ode-quiet
                                                   (lambda ()
                                                     (integrate (ode-replace prhs (list 'p x) (list 'p x)) x)))
                                                'C2)))
                         (sol (list '= (list y x) (simplify yrhs))))
                    (with-step ('ode-re-drop-y "Уравнение без y (p = y′)" eq
                                :comment (string-append "p-уравнение: " (to-string (list '= peq 0))
                                                        "; p(x) = " (to-string prhs)
                                                        "; y = ∫p dx + C2")
                                :after (lambda (r) (ode-field r :solutions)))
                      (if (dsolve-check eq sol yx)
                          (ode-solution 'general (list sol)
                                        (append (ode-field r :constants) (list 'C2))
                                        '() 'ok 'drop-y #t)
                          #f)))))))))

; встречается ли y (голая или как (y x)) вне производных — «уравнение без y»
(define (rd-mentions-y? e y x)
  (cond ((equal? e (list y x)) #t)
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3) (equal? (caddr e) x)) #f)
        ((pair? e) (any? (lambda (z) (rd-mentions-y? z y x)) e))
        (else #f)))

; ---------- нормировка p-уравнения: уравнение однородно по p → делим на p^d ----------

; суммарная степень p в терме (p y), (p y)^k, (diff (p y) y) считаются степенью 1
(define (rd-p-degree e pv yv)
  (cond ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3)
              (equal? (cadr e) (list pv yv)))
         1)
        ((equal? e (list pv yv)) 1)
        ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (equal? (cadr e) (list pv yv)) (integer? (caddr e)))
         (caddr e))
        ((and (pair? e) (equal? (car e) '*))
         (apply + (map (lambda (z) (rd-p-degree z pv yv)) (cdr e))))
        ((and (pair? e) (equal? (car e) '/) (= (length e) 3))
         (- (rd-p-degree (cadr e) pv yv) (rd-p-degree (caddr e) pv yv)))
        ((pair? e) 0)
        (else 0)))

; поделить обе части на p^m почленно; #f при сбое
(define (rd-div-p eq pv yv m)
  (if (= m 0)
      eq
      (let* ((pw (list '^ (list pv yv) m))
             (lhs (cadr eq))
             (terms (if (and (pair? lhs) (equal? (car lhs) '+)) (cdr lhs) (list lhs)))
             (qt (map (lambda (z) (try (simplify (list '/ z pw)) (lambda (err) #f))) terms)))
        (if (any? (lambda (q) (not q)) qt)
            #f
            (list '= (try (simplify (cons '+ qt)) (lambda (err) #f))
                  (try (simplify (list '/ (caddr eq) pw)) (lambda (err) #f)))))))

; кандидаты: делим на p^m от полной однородной степени вниз до 1
; (при m < d часть членов получает отрицательные степени p, но уравнение остаётся
;  линейным по p′ — например y·p·p′ − p² = 0 → y·p′ − p = 0 при m = 1)
(define (rd-p-cands eq pv yv)
  (let* ((lhs (cadr eq))
         (terms (if (and (pair? lhs) (equal? (car lhs) '+)) (cdr lhs) (list lhs)))
         (ds (map (lambda (z) (rd-p-degree z pv yv)) terms))
         (d (apply min ds)))
    (if (< d 1)
        (list eq)
        (filter (lambda (c) c)
                (map (lambda (m) (try (rd-div-p eq pv yv m) (lambda (err) #f)))
                     (range (+ d 1)))))))

; y″ → p·p′, y′ → p (по переменной y), (y x) → y; x не должно встречаться
(define (rd-to-p-aut e y x xv pv)
  (let* ((d2 (ode-nth-deriv y x 2))
         (d1 (ode-nth-deriv y x 1))
         (dp (list 'diff (list pv xv) xv))
         (pp (list '* (list pv xv) dp)))
    (ode-replace (ode-replace (ode-replace e d2 pp) d1 (list pv xv)) (list y x) xv)))

; перебор кандидатов деления на p^m: первый успешно решённый p(y)
(define (rd-try-p eq y x peq0)
  (let loop ((cs (rd-p-cands peq0 'p y)) (acc #f))
    (cond (acc acc)
          ((null? cs) #f)
          (else
           (let ((r (ode-quiet (lambda () (try (dsolve (car cs) (list 'p y)) (lambda (err) #f))))))
             (loop (cdr cs)
                   (if (and r (equal? (ode-status r) 'ok)
                            (equal? (length (ode-solutions r)) 1))
                       r
                       #f)))))))

; (ode-autonomous eq (y x)) → ode-solution или #f; уравнение без x
; p(y) решается как уравнение 1-го порядка, затем dy/dx = p(y) — разделяющееся
(define (ode-autonomous eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)) (n (ode-order eq y x)) (e (ode-normalize eq)))
        (if (or (not (= n 2)) (ode-mentions-x? e y x))
            #f
            (let* ((peq0 (list '= (rd-to-p-aut e y x y 'p) 0))
                   (r (rd-try-p eq y x peq0)))
              (if (or (not (and r (equal? (ode-status r) 'ok) (pair? (ode-solutions r))))
                      (not (equal? (length (ode-solutions r)) 1)))
                  #f
                  (let* ((pc (ode-field r :constants))
                         (prhs0 (rd-rename (caddr (car (ode-solutions r))) (rd-fresh-consts pc)))
                         ; dy/dx = p(y) решаем как обычное уравнение 1-го порядка
                         (yr (ode-quiet (lambda ()
                                          (try (dsolve (list '= (list 'diff (list y x) x) prhs0) yx)
                                               (lambda (err) #f)))))
                         (yc (if yr (ode-field yr :constants) '()))
                         ; параметры p(y) получают следующие свободные имена C_{k+1}…
                         (back (rd-shift-consts pc (length yc)))
                         (sols (if (and yr (equal? (ode-status yr) 'ok)
                                       (equal? (ode-field yr :type) 'general))
                                   (map (lambda (s) (rd-rename s back)) (map caddr (ode-solutions yr)))
                                   '()))
                         (sols (rd-check-all eq yx sols y x)))
                    (with-step ('ode-re-autonomous "Автономное уравнение (замена p = y′)" eq
                                :comment (string-append "y″ = p·dp/dy; p-уравнение: "
                                                        (to-string peq0)
                                                        "; p(y) = " (to-string prhs0)
                                                        "; dy/dx = p(y) — разделяющееся")
                                :after (lambda (r) (list (ode-field r :solutions) (ode-field r :singular))))
                      (if (null? sols)
                          ; явного y(x) нет — неявное: ∫dy/p(y) = x + C1
                          (let* ((F (simplify (list '- (ode-quiet
                                                        (lambda () (integrate (list '/ 1 prhs0) y)))
                                                      x)))
                                 (imp (simplify (rd-rename F back))))
                            (if (rd-implicit-ok? eq imp prhs0 y x)
                                (ode-solution 'implicit (list (list '= imp 'C1)) (list 'C1) '()
                                              'ok 'autonomous #t)
                                #f))
                          (ode-solution 'general
                                        (map (lambda (s) (list '= (list y x) s)) sols)
                                        (append yc (map (lambda (p) (cdr p)) (reverse back)))
                                        '() 'ok 'autonomous #t))))))))))

; все решения проходят проверку → список, иначе '()
(define (rd-check-all eq yx xs y x)
  (if (every? (lambda (s) (dsolve-check eq (list '= (list y x) s) yx)) xs) xs '()))

; неявный ответ F(y, x) = C1 для автономного: F_y·y′ + F_x = 0 при y′ = p(y)
(define (rd-implicit-ok? eq F p y x)
  (if (ode-has-head? F 'integrate)
      #f
      (let ((res (simplify (list '+ (list '* (diff 'y F) p) (diff 'x F)))))
        (cond ((ode-zero? (simplify (together res))) #t)
              ((ode-surely-nonzero? res) #f)
              ((ode-trig-zero? (simplify (together res))) #t)
              (else #f)))))

(define *ode-reduction-loaded* #t)
