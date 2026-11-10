; exact.lisp — точные уравнения, интегрирующий множитель, Риккати, Клеро/Лагранж (шаг ODE.2)
; Форма M dx + N dy = 0 из уравнения y′ = f(x,y): из f = A/B берём M = −A/B_y-часть, N = …;
; простой случай f = A/B (B свободен от y): M = −A, N = B; иначе M = −f, N = 1.
(module ode)

; ---------- разбор формы M dx + N dy ----------

; разбить f на (M . N): f = A/B ⇒ M = −A, N = B; иначе M = −f, N = 1
; (умножение формы на общий знаменатель сохраняет и решения, и критерий точности)
; simplify даёт дробь как (* A (^ B -1)) — разбираем на множители
(define (ex-mul-den? z)
  (and (pair? z) (equal? (car z) '^) (equal? (caddr z) -1)))

(define (ex-form f)
  (cond ((and (pair? f) (equal? (car f) '/) (= (length f) 3))
         (cons (simplify (list '- 0 (cadr f))) (caddr f)))
        (else
         (let* ((fs (fo-mul-factors f))
                (dens (filter ex-mul-den? fs))
                (nums (filter (lambda (z) (not (ex-mul-den? z))) fs)))
           (if (null? dens)
               (cons (simplify (list '- 0 f)) 1)
               (cons (simplify (list '- 0 (foldl * 1 nums)))
                     (simplify (foldl * 1 (map cadr dens)))))))))

; нормализованный остаток точности: (M_y − N_x)/N (сокращённый)
(define (ex-exact-residue M N x y)
  (ode-quiet (lambda ()
               (simplify (together (list '/ (list '- (ode-diff 'y M) (ode-diff 'x N)) N))))))

; точно ли выражение не содержит символа (после simplify)
(define (ex-free-of? e s) (not (ode-mentions-sym? (simplify e) s)))

; ---------- потенциал и ответ ----------

; F = ∫M dx + h(y); h′(y) = N − ∫(∂M/∂y)dx
(define (ex-potential M N x y)
  (let* ((Ix (ode-quiet (lambda () (integrate M x))))
         (My (ode-quiet (lambda () (ode-diff 'y M))))
         (Iy (ode-quiet (lambda () (integrate My x))))
         (rem (simplify (list '- N Iy)))
         (h (ode-quiet (lambda () (integrate rem y)))))
    (if (or (ode-has-head? Ix 'integrate) (ode-has-head? h 'integrate))
        #f
        (simplify (list '+ Ix h)))))
; явное решение: solve F = C1 по y; ветви с проверкой; иначе неявное
(define (ex-answer eq y x F f method)
  (let ((sols (try (set->list (solve (list '= F 'C1) y)) (lambda (e) '()))))
    (if (null? sols)
        (fo-implicit eq y x F f method)
        (let ((rhs-list (filter (lambda (s) (dsolve-check eq (list '= (list y x) s) (list y x)))
                                (map simplify sols))))
          (if (null? rhs-list)
              (fo-implicit eq y x F f method)
              (ode-solution 'general
                            (map (lambda (s) (list '= (list y x) s)) rhs-list)
                            (list 'C1) '() 'ok method #t))))))

; ---------- интегрирующие множители ----------

; кандидаты μ: μ(x) из r = (M_y−N_x)/N зависящего только от x; μ(y) из −r′ при r′ только от y;
; μ(xy): (M_y−N_x)/(y·N−x·M) только от xy; μ(x+y): (M_y−N_x)/(N−M) только от x+y
(define (ex-mu-candidates M N x y)
  (list
   ; μ(x): (1/μ)dμ/dx = (M_y−N_x)/N
   (let ((r (ex-exact-residue M N x y)))
     (and (not (ode-zero? r)) (ex-free-of? r 'y) (list 'x r)))
   ; μ(y): (1/μ)dμ/dy = (N_x−M_y)/M
   (let ((r2 (simplify (together (list '/ (list '- (ode-diff 'x N) (ode-diff 'y M)) M)))))
     (and (not (ode-zero? r2)) (ex-free-of? r2 'x) (list 'y r2)))
   ; μ(xy): (M_y−N_x)/(yN−xM) = f(xy)
   (let ((q (simplify (together (list '/ (list '- (ode-diff 'y M) (ode-diff 'x N))
                                    (list '- (list '* 'y N) (list '* 'x M)))))))
     (and (not (ode-zero? q))
          (ex-depends-only? q (lambda (e) (equal? e (list '* 'x 'y))))
          (list (list '* 'x 'y) q)))
   ; μ(x+y): (M_y−N_x)/(N−M) = f(x+y)
   (let ((q (simplify (together (list '/ (list '- (ode-diff 'y M) (ode-diff 'x N))
                                    (list '- N M))))))
     (and (not (ode-zero? q))
          (ex-depends-only? q (lambda (e) (equal? e (list '+ 'x 'y))))
          (list (list '+ 'x 'y) q)))))

; зависит ли e только от комбинации comb (структурно: замена comb→v упрощает к виду без x,y)
; для (* x y) и (+ x y) понимает и «рассыпанные» формы: x^a·y^a → v^a, x^a·y^b (a=b)
(define (ex-depends-only? e comb?)
  (let* ((v 'ode-mu-var)
         (re (ex-replace-comb e comb? v)))
    (and re (ex-free-of? (simplify re) 'x) (ex-free-of? (simplify re) 'y))))

; структурная замена узлов, удовлетворяющих pred, на v; #f — если встретился голый x или y;
; дополнительно: произведения только из степеней x и y с равными суммарными степенями
; (для comb = xy) заменяем на v^степень
(define (ex-replace-comb e pred v)
  (cond ((pred e) v)
        ((equal? e 'x) #f)
        ((equal? e 'y) #f)
        ((and (pair? e) (equal? (car e) '*))
         (let ((r (ex-replace-mul-pow (cdr e) v)))
           (if r r
               (let ((rs (map (lambda (z) (ex-replace-comb z pred v)) e)))
                 (if (any? (lambda (z) (not z)) rs) #f rs)))))
        ((pair? e) (let ((rs (map (lambda (z) (ex-replace-comb z pred v)) e)))
                     (if (any? (lambda (z) (not z)) rs) #f rs)))
        (else e)))

; произведение множителей-степеней x/y (числовые константы игнорируются):
; c·x^a·y^b с a=b → c·v^a; иначе #f
(define (ex-replace-mul-pow fs v)
  (let* ((pw (lambda (z) (cond ((equal? z 'x) 'x)
                                ((equal? z 'y) 'y)
                                ((and (pair? z) (equal? (car z) '^)
                                      (or (equal? (cadr z) 'x) (equal? (cadr z) 'y))
                                      (number? (caddr z))) (cadr z))
                                (else #f)))))
    (let loop ((rest fs) (ax 0) (ay 0) (cs 1))
      (cond ((null? rest)
             (if (and (= ax ay) (not (= ax 0))) (list '* cs (list '^ v ax)) #f))
            (else
             (let ((p (pw (car rest))))
               (cond ((number? (car rest)) (loop (cdr rest) ax ay (* cs (car rest))))
                     ((not p) #f)
                     ((equal? p 'x)
                      (loop (cdr rest) (+ ax (if (equal? (car rest) 'x) 1 (caddr (car rest)))) ay cs))
                     ((equal? p 'y)
                      (loop (cdr rest) ax (+ ay (if (equal? (car rest) 'y) 1 (caddr (car rest)))) cs))
                     (else #f))))))))

; exp(k·log(v)) → v^k; exp(log(v)) → v; иначе без изменений (рекурсивно)
(define (ex-exp-simp e)
  (cond ((and (pair? e) (equal? (car e) 'exp) (pair? (cadr e))
              (equal? (car (cadr e)) 'log))
         (cadr (cadr e)))
        ((and (pair? e) (equal? (car e) 'exp) (pair? (cadr e))
              (equal? (car (cadr e)) '*) (= (length (cadr e)) 3)
              (equal? (cadr (cadr e)) 'log))
         (let ((k (ex-exp-simp (caddr (cadr e)))))
           (if (equal? k 1) (caddr (cadr (cadr e))) (list '^ (caddr (cadr (cadr e))) k))))
        ((pair? e) (map ex-exp-simp e))
        (else e)))

; решить μ из (1/μ)dμ/dvar = q(var): μ = exp(∫ q dvar); var — x, y, (* x y) или (+ x y)
(define (ex-mu-of var q)
  (let* ((qf (if (or (equal? var 'x) (equal? var 'y)) q
                 (simplify (ex-replace-comb q (lambda (e) (equal? e var)) 'ode-mu-var))))
         (vv (if (or (equal? var 'x) (equal? var 'y)) var 'ode-mu-var))
         (I (ode-quiet (lambda () (integrate qf vv))))
         (I2 (if (equal? vv var) I (ode-replace I 'ode-mu-var var))))
    (if (ode-has-head? I 'integrate) #f (simplify (ex-exp-simp (list 'exp I2))))))

; ---------- точность после умножения ----------

(define (ex-exact-after-mu? M N mu x y)
  (ode-zero? (simplify (together (list '- (ode-diff 'y (simplify (list '* mu M)))
                                        (ode-diff 'x (simplify (list '* mu N))))))))

; потерянные решения при μ от одной переменной: нули μ⁻¹-«плотности»;
; для μ = exp(φ(v)) решений не теряется (μ>0), поэтому список пуст — оставим крючок
(define (ex-mu-lost eq y x mu) '())

; ---------- точное уравнение (п. 1) ----------

(define (ex-solve-exact eq y x f M N)
  (let ((F (ex-potential M N x y)))
    (if (not F) #f
        (with-step ('ode-ex-exact "Точное уравнение" (list (list '= 'M M) (list '= 'N N))
                    :comment (string-append "M_y = " (ode-mp (ode-diff 'y M))
                                            ", N_x = " (ode-mp (ode-diff 'x N))
                                            "; F = " (ode-mp F)
                                            "; F_x = M, F_y = N — проверено")
                    :after (lambda (r) (ode-field r :solutions)))
          (ex-answer eq y x F f 'exact)))))

; ---------- интегрирующий множитель (п. 2) ----------

(define (ex-solve-mu eq y x f M N)
  (let loop ((cands (filter (lambda (c) c) (ex-mu-candidates M N x y))))
    (if (null? cands) #f
        (let* ((c (car cands)) (var (car c)) (q (cadr c))
               (mu (ex-mu-of var q)))
          (cond ((not mu) (loop (cdr cands)))
                ((not (ex-exact-after-mu? M N mu x y)) (loop (cdr cands)))
                (else
                 (let* ((M2 (simplify (together (list '* mu M))))
                        (N2 (simplify (together (list '* mu N))))
                        (F (ex-potential M2 N2 x y)))
                   (if (not F)
                       (loop (cdr cands))
                       (with-step ('ode-ex-mu "Интегрирующий множитель" (list (list '= 'M M) (list '= 'N N))
                                   :comment (string-append "μ зависит от " (to-string var)
                                                           "; (1/μ)·dμ/dv = " (ode-mp q)
                                                           "; μ = " (ode-mp mu)
                                                           "; после умножения M_y − N_x = 0 — проверено")
                                   :after (lambda (r) (ode-field r :solutions)))
                         (ex-answer eq y x F f 'integrating-factor))))))))))

; ---------- Риккати (п. 3) ----------

; f = a·y² + b·y + c, коэффициенты свободны от y; иначе #f
(define (ex-riccati-parts f)
  (let* ((e (simplify (expand f)))
         (ts (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e))))
    (let loop ((rest ts) (a 0) (b 0) (c 0))
      (cond ((null? rest) (list (simplify a) (simplify b) (simplify c)))
            (else
             (let* ((t (car rest)) (d (ex-deg-y t)))
               (cond ((not d) #f)
                     ((= d 0) (loop (cdr rest) a b (+ c t)))
                     ((= d 1) (loop (cdr rest) a (+ b (simplify (list '/ t 'y))) c))
                     ((= d 2) (loop (cdr rest) (+ a (simplify (list '/ t (list '^ 'y 2)))) b c))
                     (else #f))))))))

; степень по y у одночлена (0 — свободен от y, #f — не одночлен по y)
(define (ex-deg-y e)
  (cond ((fo-free-y? e) 0)
        ((equal? e 'y) 1)
        ((and (pair? e) (equal? (car e) '^) (equal? (cadr e) 'y) (number? (caddr e)))
         (caddr e))
        ((and (pair? e) (equal? (car e) '*))
         (let ((ds (map ex-deg-y (cdr e))))
           (if (any? (lambda (z) (not z)) ds) #f (foldl + 0 ds))))
        (else #f)))

; частное решение: анзацы k/x, k·x, k, k·x², k/x² — решаем по k, проверяем подстановкой.
; Анзац подставляем в остаток уравнения (y′ заменяем на d(анзац)/dx), а не только в f.
(define (ex-riccati-residual eq y x form)
  (ode-eval-diffs
   (ode-subst (ode-replace (ode-normalize eq)
                            (ode-nth-deriv y x 1)
                            (ode-diff 'x form))
              (list y x) form)
   x))

(define (ex-riccati-particular-for form eq y x)
  (try (let ((ps (set->list (solve (list '= (simplify (ex-riccati-residual eq y x form)) 0) 'k))))
         (filter (lambda (s) (dsolve-check eq (list '= (list y x) s) (list y x)))
                 (map (lambda (kv) (simplify (subst (list 'k kv) form))) ps)))
       (lambda (e) '())))

(define (ex-riccati-try-particular eq y x f)
  (let ((forms (list (list '/ 'k 'x) (list '* 'k 'x) 'k
                     (list '* 'k (^ 'x 2)) (list '/ 'k (^ 'x 2)))))
    (foldl (lambda (acc form) (append acc (ex-riccati-particular-for form eq y x)))
           '() forms)))
; Риккати через частное y₁: y = y₁ + 1/v, v′ + (2a·y₁+b)·v = −a
(define (ex-riccati-solve eq y x f parts)
  (let* ((a (car parts)) (b (cadr parts))
         (y1s (ex-riccati-try-particular eq y x f)))
    (if (null? y1s) #f
        (let* ((y1 (car y1s))
               (P (simplify (list '+ (list '* 2 (list '* a y1)) b)))
               (E (simplify (list 'exp (ode-quiet (lambda () (integrate P x))))))
               (v (simplify (list '/ (list '+ 'C1
                              (list '* -1 (ode-quiet (lambda () (integrate (list '* a E) x))))) E)))
               (rhs (simplify (list '+ y1 (list '/ 1 v))))
               (sol (list '= (list y x) rhs)))
          (with-step ('ode-ex-riccati "Уравнение Риккати" f
                      :comment (string-append "y′ = " (ode-mp (simplify a)) "·y² + "
                                              (ode-mp (simplify b)) "·y + " (ode-mp (simplify (caddr parts)))
                                              "; частное y₁ = " (ode-mp y1) " (подстановкой — проверено)"
                                              "; y = y₁ + 1/v: v′ + " (ode-mp P) "·v = "
                                              (ode-mp (simplify (list '- 0 a))))
                      :after (lambda (r) (ode-field r :solutions)))
            (if (dsolve-check eq sol (list y x))
                (ode-solution 'general (list sol) (list 'C1) '() 'ok 'riccati #t)
                #f))))))

; ---------- Клеро / Лагранж (п. 4): y = x·φ(p) + ψ(p), p = y′ ----------

; разбор y = x·φ(p) + ψ(p): LHS = (y x), RHS после замены y′ → p линейно по x;
; возвращает (phi . psi) — коэффициент при x и свободный член (функции p); #f — не этот случай
(define (ex-lagrange-parts eq y x)
  (let* ((lhs (cadr eq))
         (rhs (ode-replace (caddr eq) (ode-nth-deriv y x 1) 'p))
         (r (ode-coeff-of 'x rhs 'y 'x)))
    (and r
         (equal? lhs (list y x))
         (not (ode-mentions-sym? (car r) 'x)) (not (ode-mentions-sym? (car r) 'y))
         (not (ode-mentions-sym? (cdr r) 'x)) (not (ode-mentions-sym? (cdr r) 'y))
         (ode-mentions-sym? (car r) 'p)
         (cons (car r) (cdr r)))))

; Клеро: φ(p) = p. Общее: y = C1·x + ψ(C1). Особое (огибающая): x = −ψ′(p),
; y = x·p + ψ(p); исключаем p: p = solve(x = −ψ′(p), p) → y явное; иначе параметрическое.
(define (ex-clairaut-solve eq y x parts)
  (let* ((psi (cdr parts))
         (gen (list '= (list y x) (simplify (list '+ (list '* 'C1 x) (subst (list 'p 'C1) psi))))))
    (if (not (ode-quiet (lambda () (dsolve-check eq gen (list y x)))))
        #f
        (with-step ('ode-ex-clairaut "Уравнение Клеро" eq
                    :comment (string-append "φ(p) = p, ψ(p) = " (ode-mp psi)
                                            "; общее: y = C1·x + ψ(C1)"
                                            "; особое: x = −ψ′(p), y = x·p + ψ(p), проверка dy/dx = y′")
                    :after (lambda (r) (list (ode-field r :solutions) (ode-field r :singular))))
          (let* ((g1 (ode-diff 'p psi))
                 ; p-параметризация огибающей: x = −ψ′(p), y = x·p + ψ(p)
                 (xs (simplify (list '- 0 g1)))
                 (ys (simplify (list '+ (list '* xs 'p) psi)))
                 (chk (ex-param-check eq y x xs ys)))
            (if (not chk)
                (ode-solution 'general (list gen) (list 'C1) '() 'ok 'clairaut #t)
                ; исключить p из x = −ψ′(p): решить xs = x относительно p
                (let ((ps (try (set->list (solve (list '= (list '- xs x) 0) 'p)) (lambda (e) '()))))
                  (if (and (not (null? ps))
                           (all-true? (map (lambda (p0) (not (ode-mentions-sym? p0 'p))) ps)))
                      (ode-solution 'general (list gen) (list 'C1)
                                    (map (lambda (p0) (list '= (list y x) (simplify (subst (list 'p p0) ys)))) ps)
                                    'ok 'clairaut #t)
                      ; p не исключается — параметрическое особое решение
                      (ode-solution 'general (list gen) (list 'C1)
                                    (list (list '= 'x xs) (list '= (list y x) ys))
                                    'ok 'clairaut #t)))))))))

; Лагранж: y = x·φ(p) + ψ(p), φ(p) ≠ p. Дифференцируем по x, y′ = p:
; p − φ = p′·(x·φ′(p) + ψ′(p)), p′ = dp/dx ⇒ dx/dp = (x·φ′ + ψ′)/(p − φ)
; ⇒ x′(p) − [φ′/(p−φ)]·x = ψ′/(p−φ) — линейное ОДУ по x(p).
(define (ex-lagrange-solve eq y x parts)
  (let* ((phi (car parts)) (psi (cdr parts))
         (den (simplify (list '- 'p phi)))
         (Pp (simplify (list '/ (ode-diff 'p phi) den)))
         (Qp (simplify (list '/ (ode-diff 'p psi) den))))
    (if (ode-zero? den) #f
        (let* ((mu (simplify (list 'exp (ode-quiet (lambda () (integrate (list '- 0 Pp) 'p))))))
               (xp (simplify (list '/ (list '+ 'C1 (ode-quiet (lambda () (integrate (list '* mu Qp) 'p)))) mu)))
               (yp (simplify (list '+ (list '* xp phi) psi)))
               (chk (ex-param-check eq y x xp yp)))
          (if (not chk)
              ; запасной путь: неявный ответ дифференцированием не построен — unknown
              #f
              (with-step ('ode-ex-lagrange "Уравнение Лагранжа" eq
                          :comment (string-append "y = x·φ(p) + ψ(p), φ(p) = " (ode-mp phi)
                                                  ", ψ(p) = " (ode-mp psi)
                                                  "; x′(p) − [" (ode-mp Pp) "]·x = " (ode-mp Qp)
                                                  "; x(p) = " (ode-mp xp)
                                                  ", y(p) = " (ode-mp yp)
                                                  "; проверка dy/dx = y′/x′ — пройдена")
                          :after (lambda (r) (ode-field r :solutions)))
                (ode-solution 'parametric
                              (list (list '= 'x xp) (list '= (list y x) yp))
                              (list 'C1) '() 'ok 'lagrange chk)))))))

; все ли элементы списка — #t (локальная копия: cauchy.lisp грузится после)
(define (all-true? xs)
  (cond ((null? xs) #t)
        ((car xs) (all-true? (cdr xs)))
        (else #f)))

; проверка параметрического решения: x(p), y(p) подставить в уравнение,
; dy/dx = y′(p)/x′(p); остаток — точно ноль или численно
(define (ex-param-check eq y x xp yp)
  (let* ((dydp (ode-diff 'p yp)) (dxdp (ode-diff 'p xp))
         (res (simplify (together
                (ode-subst (ode-replace (ode-normalize eq)
                                        (ode-nth-deriv y x 1)
                                        (list '/ dydp dxdp))
                           (list y x) yp))))
         ; x в уравнении тоже заменить на x(p)
         (r (simplify (together (subst (list 'x xp) res)))))
    (cond ((ode-zero? r) #t)
          ((ode-surely-nonzero? r) #f)
          (else
           (let loop ((ps '((1 2) (2 3) (3 1))) (n 0))
             (cond ((null? ps) (and (> n 0) 'numeric))
                   (else
                    (let ((v (eval-num (subst (list 'p (car (car ps))) r))))
                      (if (and (number? v) (< (abs v) 1e-7))
                          (loop (cdr ps) (+ n 1))
                          #f)))))))))

; ---------- диспетчер ODE.2 ----------

; правая часть y′ = f(x,y) без требования числового коэффициента при y′
(define (ex-rhs eq y x)
  (let* ((d (ode-nth-deriv y x 1))
         (r (ode-coeff-of d (ode-normalize eq) y x)))
    (and r (not (ode-zero? (car r)))
         (simplify (together (list '/ (list '- 0 (cdr r)) (car r)))))))

(define (ex-solve eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)))
        (let ((r (or (ex-try-lagrange eq y x)
                     (ex-try-rhs eq y x))))
          (if r r #f)))))

; Клеро/Лагранж из общей формы (= y x-выражение)
(define (ex-try-lagrange eq y x)
  (if (not (and (pair? eq) (equal? (car eq) '=) (= (length eq) 3))) #f
      (let ((parts (ex-lagrange-parts eq y x)))
        (cond ((not parts) #f)
              ; Клеро: φ(p) = p
              ((equal? (car parts) 'p) (ex-clairaut-solve eq y x parts))
              (else (ex-lagrange-solve eq y x parts))))))

; из y′ = f: точность / μ / Риккати
; M,N берём прямо из линеаризации normalize = a·y′ + b (M = b, N = a) —
; это сохраняет факторизацию (together бы развернул дробь и убил структуру μ(xy))
(define (ex-mn-of eq y x)
  (let* ((d (ode-nth-deriv y x 1))
         (r (ode-coeff-of d (ode-normalize eq) y x)))
    (and r (not (ode-zero? (car r)))
         (cons (fo-bare (cdr r) y x) (fo-bare (car r) y x)))))

(define (ex-try-rhs eq y x)
  (let* ((f0 (ex-rhs eq y x)))
    (if (not f0) #f
        (let ((f (fo-bare f0 y x)))
          (cond ((fo-free-y? f) #f)
                (else
                 (let* ((mn (or (ex-mn-of eq y x) (ex-form f)))
                        (M (car mn)) (N (cdr mn)))
                   (or (and (ode-zero? (ex-exact-residue M N x y))
                            (ex-solve-exact eq y x f M N))
                       (ex-solve-mu eq y x f M N)
                       (let ((rp (ex-riccati-parts f)))
                         (and rp (ex-riccati-solve eq y x f rp)))))))))))

(define *ode-exact-loaded* #t)


