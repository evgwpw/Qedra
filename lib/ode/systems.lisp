; systems.lisp — системы линейных ОДУ с постоянными коэффициентами (шаг ODE.5a)
; x′ = A·x + f(t): однородная часть — e^{At} в вещественной форме, частное — вариация постоянных
; x_p = e^{At}∫e^{−As}f(s)ds. Начальные условия — линейная система на C1…Cn.
; ОДУ порядка n → система первого порядка: (ode->system eq (y x)).
(module ode
  (export dsolve-system dsolve-system-check ode->system))

; ---------- разбор: выражения как линейные формы по функциям и их производным ----------

(define (sys-mentions? e atoms)
  (cond ((any? (lambda (a) (equal? e a)) atoms) #t)
        ((pair? e) (any? (lambda (z) (sys-mentions? z atoms)) e))
        (else #f)))

(define (sys-zero-vec n) (map (lambda (i) 0) (range n)))
(define (sys-vec-add a b) (map2 (lambda (x y) (simplify (list '+ x y))) a b))
(define (sys-vec-scale v c) (map (lambda (x) (simplify (list '* x c))) v))

; e → (в-коэффициенты . свободный член); коэффициенты по atoms; #f — нелинейно
(define (sys-lin e atoms)
  (cond ((any? (lambda (a) (equal? e a)) atoms)
         (cons (map (lambda (a) (if (equal? e a) 1 0)) atoms) 0))
        ((not (pair? e)) (cons (sys-zero-vec (length atoms)) e))
        ((equal? (car e) '+)
         (let loop ((ts (cdr e)) (v (sys-zero-vec (length atoms))) (r 0))
           (if (null? ts)
               (cons v (simplify r))
               (let ((s (sys-lin (car ts) atoms)))
                 (if (not s) #f
                     (loop (cdr ts) (sys-vec-add v (car s))
                           (simplify (list '+ r (cdr s)))))))))
        ((equal? (car e) '*)
         (let* ((fs (cdr e))
                (w (filter (lambda (z) (sys-mentions? z atoms)) fs))
                (c (filter (lambda (z) (not (sys-mentions? z atoms))) fs)))
           (if (not (= (length w) 1))
               #f
               (let ((s (sys-lin (car w) atoms)) (k (foldl * 1 c)))
                 (if (not s) #f
                     (cons (sys-vec-scale (car s) k)
                           (simplify (list '* (cdr s) k))))))))
        (else (cons (sys-zero-vec (length atoms)) e))))

; ---------- матрицы как списки строк ----------

(define (sys-columns m)
  (if (null? m) '()
      (map (lambda (j) (map (lambda (row) (nth row j)) m))
           (range (length (car m))))))

(define (sys-transpose m) (sys-columns m))

(define (sys-nrows m) (length m))
(define (sys-ncols m) (length (car m)))

(define (sys-map2 f a b) (map2 (lambda (ra rb) (map2 f ra rb)) a b))

(define (sys-scale m c)
  (map (lambda (row) (map (lambda (v) (simplify (list '* v c))) row)) m))

; A·B для списков строк
(define (sys-mul a b)
  (let* ((bt (sys-transpose b)))
    (map (lambda (row)
           (map (lambda (col) (simplify (foldl (lambda (acc p) (list '+ acc (list '* (car p) (cdr p))))
                                               0 (map2 cons row col))))
                bt))
         a)))

; M как столбец из списка
(define (sys-col v) (map (lambda (z) (list z)) v))
(define (sys-uncol m) (map car m))

(define (sys-zero-mat n) (map (lambda (i) (sys-zero-vec n)) (range n)))
(define (sys-identity n)
  (map (lambda (i) (map (lambda (j) (if (= i j) 1 0)) (range n))) (range n)))

; сложение матриц
(define (sys-add2 a b) (sys-map2 (lambda (x y) (simplify (list '+ x y))) a b))

(define (sys-rank vecs)
  (if (null? vecs)
      0
      (let ((rows (tensor->list (rref vecs))))
        (length (filter (lambda (row)
                          (not (every? (lambda (v) (equal? (simplify v) 0)) row)))
                        rows)))))

(define (sys-mat-zero? m)
  (every? (lambda (row) (every? (lambda (v) (ode-zero? v)) row)) m))

(define (sys-mat-eq? a b)
  (and (= (sys-nrows a) (sys-nrows b))
       (every? (lambda (p) (ode-zero? (simplify (list '- (car p) (cadr p)))))
               (map2 cons (sys-flat a) (sys-flat b)))))

(define (sys-flat m)
  (foldl (lambda (acc row) (append acc row)) '() m))
; ---------- вещественная форма e^{At} ----------

(define (sys-summands e)
  (let ((v (expand e)))
    (if (and (pair? v) (equal? (car v) '+)) (cdr v) (list v))))

(define (sys-factors t)
  (if (and (pair? t) (equal? (car t) '*)) (append-map sys-factors (cdr t)) (list t)))

; e = c0 + %i·c1 (структурно: %i — только множителем); #f — не разобрать
(define (sys-i-split v)
  (let loop ((ts (sys-summands v)) (c0 0) (c1 0))
    (if (null? ts)
        (list (simplify c0) (simplify c1))
        (let* ((fs (sys-factors (car ts)))
               (n (length (filter (lambda (z) (equal? z '%i)) fs)))
               (rest (foldl * 1 (filter (lambda (z) (not (equal? z '%i))) fs))))
          (cond ((= n 0) (loop (cdr ts) (simplify (list '+ c0 rest)) c1))
                ((= n 1) (loop (cdr ts) c0 (simplify (list '+ c1 rest))))
                (else #f))))))

; e = k·x + b → (k . b); #f — не линейно по x
(define (sys-lin-arg e x)
  (cond ((not (sys-mentions? e (list x))) (cons 0 e))
        ((equal? e x) (cons 1 0))
        ((and (pair? e) (equal? (car e) '+))
         (let loop ((ts (cdr e)) (k 0) (b 0))
           (if (null? ts) (cons (simplify k) (simplify b))
               (let ((s (sys-lin-arg (car ts) x)))
                 (if (not s) #f
                     (loop (cdr ts) (simplify (list '+ k (car s)))
                           (simplify (list '+ b (cdr s)))))))))
        ((and (pair? e) (equal? (car e) '*))
         (let* ((fs (cdr e))
                (w (filter (lambda (z) (sys-mentions? z (list x))) fs))
                (c (filter (lambda (z) (not (sys-mentions? z (list x)))) fs)))
           (if (not (= (length w) 1))
               #f
               (let ((s (sys-lin-arg (car w) x)) (q (foldl * 1 c)))
                 (if (not s) #f
                     (cons (simplify (list '* q (car s)))
                           (simplify (list '* q (cdr s)))))))))
        (else #f)))

; exp((a + b·i)·x + c) → e^{a x + c}(cos bx + i·sin bx); прочее — рекурсивно
(define (sys-eulerify e x)
  (cond ((and (pair? e) (equal? (car e) 'exp) (= (length e) 2))
         (let ((s (sys-lin-arg (cadr e) x)))
           (if (not s)
               e
               (let* ((k (car s)) (b0 (cdr s)) (sp (sys-i-split k)))
                 (if (not sp)
                     e
                     (let ((al (car sp)) (be (cadr sp)))
                       (simplify
                        (list '* (list 'exp (list '+ (list '* al x) b0))
                              (list '+ (list 'cos (list '* be x))
                                    (list '* '%i (list 'sin (list '* be x))))))))))))
        ((pair? e) (map (lambda (z) (sys-eulerify z x)) e))
        (else e)))

; вещественная часть элемента (второй элемент — мнимая)
(define (sys-reim v)
  (let ((sp (sys-i-split (expand v))))
    (if sp sp (list (expand v) 0))))

(define (sys-real-cols mat x)
  (let ((cols (sys-columns mat)))
    (map (lambda (c)
           (map (lambda (v) (car (sys-reim (sys-eulerify v x)))) c))
         cols)))

(define (sys-imag-cols mat x)
  (let ((cols (sys-columns mat)))
    (map (lambda (c)
           (map (lambda (v) (cadr (sys-reim (sys-eulerify v x)))) c))
         cols)))

; вещественный фундаментальный набор: вещественные части, при нехватке ранга — мнимые
(define (sys-fundamental A x)
  (let* ((n (sys-nrows A))
         (mat (tensor->list (mat-exp A x)))
         (cand (append (sys-real-cols mat x) (sys-imag-cols mat x))))
    (let loop ((cs cand) (acc '()))
      (cond ((>= (sys-rank acc) n) (reverse acc))
            ((null? cs) (reverse acc))
            (else
             (let ((v (car cs)))
               (if (every? (lambda (z) (ode-zero? z)) v)
                   (loop (cdr cs) acc)
                   (if (= (sys-rank (cons v acc)) (+ 1 (sys-rank acc)))
                       (loop (cdr cs) (cons v acc))
                       (loop (cdr cs) acc)))))))))

; (sys-const-names n) → (C1 … Cn)
(define (sys-const-names n)
  (map (lambda (k) (string->symbol (string-append "C" (to-string (+ k 1))))) (range n)))

; компоненты однородного решения: Σ_j X[i][j]·Cj
(define (sys-hom-rows A x names)
  (let ((cols (sys-fundamental A x)))
    (if (not (= (length cols) (length names)))
        #f
        (let ((n (length names)))
          (map (lambda (i)
                 (simplify (sys-parity
                            (simplify (foldl (lambda (acc p) (list '+ acc (list '* (cadr p) (car p))))
                                             0 (map2 (lambda (c nm) (list c nm))
                                                     (map (lambda (c) (nth c i)) cols) names))))))
               (range n))))))

; ---------- частное решение: e^{At}∫e^{−As}f(s)ds ----------

; множитель — «чисто тригонометрический» (число, sin/cos или степень sin/cos)
(define (sys-trig-only? q)
  (or (number? q)
      (and (not (pair? q)) #f)
      (and (pair? q)
           (or (and (or (equal? (car q) 'sin) (equal? (car q) 'cos)) (= (length q) 2))
               (and (equal? (car q) '^) (= (length q) 3)
                    (pair? (cadr q))
                    (or (equal? (car (cadr q)) 'sin) (equal? (car (cadr q)) 'cos)))
               (and (equal? (car q) '*)
                    (every? sys-trig-only? (cdr q)))))))

; чётность: sin(−z) → −sin z, cos(−z) → cos z, tan(−z) → −tan z (simplify это не делает)
(define (sys-neg-arg? z)
  (and (pair? z)
       (or (and (equal? (car z) '*) (any? (lambda (q) (equal? q -1)) (cdr z)))
           (and (equal? (car z) '-) (= (length z) 2)))))

(define (sys-neg-of z)
  (if (equal? (car z) '-)
      (cadr z)
      (simplify (cons '* (sys-rm1 (lambda (q) (equal? q -1)) (cdr z))))))

; удалить первое вхождение подходящего элемента
(define (sys-rm1 p l)
  (cond ((null? l) '())
        ((p (car l)) (cdr l))
        (else (cons (car l) (sys-rm1 p (cdr l))))))

(define (sys-parity e)
  (cond ((not (pair? e)) e)
        ((and (or (equal? (car e) 'sin) (equal? (car e) 'cos) (equal? (car e) 'tan))
              (= (length e) 2)
              (sys-neg-arg? (cadr e)))
         (let* ((u (sys-parity (sys-neg-of (cadr e))))
                (f (list (car e) u)))
           (if (equal? (car e) 'cos) f (simplify (list '* -1 f)))))
        (else (map sys-parity e))))

; причёсывание: чисто тригонометрические слагаемые суммы факторизуем вместе
; (cos²z·sin z + sin³z = sin z), принимая результат только при точном тождестве
(define (sys-tidy e)
  (let* ((g (simplify (sys-parity (simplify (expand e)))))
         (terms (if (and (pair? g) (equal? (car g) '+)) (cdr g) (list g)))
         (ts (filter (lambda (q) (and (pair? (ode-trig-args q '())) (sys-trig-only? q))) terms))
         (rs (filter (lambda (q) (not (member? q ts))) terms)))
    (if (< (length ts) 2)
        g
        (let* ((s (simplify (cons '+ ts)))
               (f (try (factor s) (lambda (err) s)))
               (ok (and (not (equal? f s))
                        (ode-trig-zero? (simplify (list '- s f)))))
               (parts (append rs (list (if ok (simplify (expand f)) s)))))
          (simplify (cons '+ parts))))))

(define (sys-particular A f x)
  (let* ((s 'odes)
         (X (tensor->list (mat-exp A x)))
         (Xs (subst (list x s) X))
         (fs (subst (list x s) f))
         (Xi (try (tensor->list (inv Xs)) (lambda (e) #f))))
    (if (not Xi)
        #f
        (let* ((w (sys-mul Xi (sys-col fs)))
               (wi (map (lambda (row)
                          (map (lambda (v)
                                 (integrate (expand (car (sys-reim (sys-eulerify v s)))) s))
                               row))
                        w))
               (wit (map (lambda (row) (map (lambda (v) (subst (list s x) v)) row)) wi))
               (xp (sys-mul X wit))
               (inexact (any? (lambda (row)
                                (any? (lambda (v)
                                        (and (pair? v) (equal? (car v) 'integrate))) row))
                              wi)))
          (list (map (lambda (v) (sys-tidy v)) (sys-uncol xp))
                inexact)))))



; ---------- разбор входных уравнений ----------

(define (index-of-fn f funcs)
  (let loop ((k 0) (fs funcs))
    (cond ((null? fs) #f)
          ((equal? (car fs) f) k)
          (else (loop (+ k 1) (cdr fs))))))

; уравнение (= (diff (xi t) t) rhs) → (i rhs) или #f
(define (sys-parse-eq eq funcs t)
  (if (not (and (pair? eq) (equal? (car eq) '=) (= (length eq) 3)))
      #f
      (let ((lhs (cadr eq)) (rhs (caddr eq)))
        (if (not (and (pair? lhs) (equal? (car lhs) 'diff) (= (length lhs) 3)
                      (equal? (caddr lhs) t)))
            #f
            (let ((i (index-of-fn (cadr lhs) funcs)))
              (and i (list i rhs)))))))

; rhs → (строка A . свободный член)
(define (sys-row rhs funcs)
  (let ((r (sys-lin (expand rhs) funcs)))
    (and r (cons (car r) (simplify (cdr r))))))

; eqs,funcs → (A f) или #f
(define (sys-build eqs funcs t)
  (let ((parsed (map (lambda (eq) (sys-parse-eq eq funcs t)) eqs)))
    (if (any? (lambda (p) (not p)) parsed)
        #f
        (let ((rows (map (lambda (p) (sys-row (cadr p) funcs)) parsed)))
          (if (any? (lambda (r) (not r)) rows)
              #f
              (list (map car rows) (map cdr rows)))))))

; ---------- сертификат ----------

(define (ode-replace-all e from to)
  (if (null? from)
      e
      (ode-replace-all (ode-replace e (car from) (car to)) (cdr from) (cdr to))))

; остаток i-го уравнения после подстановки компонент
(define (sys-residual eq funcs t comps i)
  (let ((lhs (simplify (diff t (nth comps i))))
        (rhs (simplify (ode-replace-all (caddr eq) funcs comps))))
    (simplify (together (list '- lhs rhs)))))

; (dsolve-system-check eqs sol funcs t) → #t | 'numeric | #f
(define (dsolve-system-check eqs sol funcs t)
  (let* ((fns (sys-normalize-funcs funcs))
         (comps (map (lambda (s) (if (and (pair? s) (equal? (car s) '=)) (caddr s) s)) sol))
         (res (map2 (lambda (eq i) (sys-residual eq fns t comps i))
                    eqs (range (length eqs)))))
    (cond ((every? ode-zero? res) #t)
          ((any? ode-surely-nonzero? res) #f)
          ((every? ode-trig-zero? res) #t)
          ((every? (lambda (r) (ode-numeric-zero? r t)) res) 'numeric)
          (else #f))))


; ---------- диспетчер систем ----------

(define (sys-normalize-funcs funcs)
  (map (lambda (f)
         (cond ((and (pair? f) (= (length f) 2)) f)
               ((symbol? f) (list f 't))
               (else f)))
       funcs))

; (= (xi t0) v) → (i v); иначе #f
(define (sys-cond-parts cond fs t)
  (if (not (and (pair? cond) (equal? (car cond) '=) (= (length cond) 3)))
      #f
      (let* ((lhs (cadr cond)) (v (caddr cond))
             ; имена функций: fs = ((y t) (y1 t) …) → (y y1 …)
             (nms (map (lambda (f) (if (pair? f) (car f) f)) fs))
             (off (index-of-fn (if (pair? lhs) (car lhs) lhs) nms)))
        (if (and (pair? lhs) (= (length lhs) 2) (number? (cadr lhs)) off)
            (list off v (cadr lhs))
            #f))))

; задача Коши для системы
(define (sys-cauchy eqs fs t conds sols names inexact)
  (let ((parsed (map (lambda (c) (sys-cond-parts c fs t)) conds)))
    (if (any? (lambda (p) (not p)) parsed)
        (ode-solution 'unknown '() '() '() "условие не распознано" 'cauchy 'none)
        (let* ((eqs1 (map (lambda (p)
                            (let* ((i (car p)) (v (cadr p)) (t0 (caddr p))
                                   (gen (caddr (nth sols i)))
                                   (at0 (simplify (subst (list t t0) gen))))
                              (list '= at0 v)))
                          parsed))
               (bs (ode-quiet (lambda () (try (set->list (solve eqs1 names)) (lambda (e) #f))))))
          (if (or (not bs) (null? bs))
              (ode-solution 'unknown '() '() '()
                            "условия несовместны или система на константы не решена" 'cauchy 'none)
              (let* ((binds (car bs))
                     (rhs (map caddr sols))
                     (res (map2 (lambda (fn r) (list '= fn (ca-subst-binds r binds))) fs rhs))
                     (chk (ode-quiet (lambda () (try (dsolve-system-check eqs res fs t) (lambda (e) #f)))))
                     (cok (ode-quiet
                           (lambda ()
                             (every? (lambda (p)
                                       (let* ((i (car p)) (v (cadr p)) (t0 (caddr p))
                                              (val (simplify (expand (subst (list t t0)
                                                                            (caddr (nth res i))))))
                                              (d (simplify (together (list '- val v)))))
                                         (or (ode-zero? d)
                                             (and (not (ode-surely-nonzero? d))
                                                  (or (ode-trig-zero? d)
                                                      (ode-numeric-zero? d t))))))
                                     parsed)))))
                (if (and chk cok)
                    (begin
                      (if (step-log-enabled?)
                          (begin
                            (record-step 'ode-sy-cauchy "Начальные условия системы"
                                         "система по C1…Cn из x(t₀) = v решена; подстановка в решение проверена"
                                         conds binds 'main)
                            (record-step 'ode-sy-check "Проверка решения системы"
                                         "подстановка компонент в уравнения: остаток 0 — проверено"
                                         res chk 'main)))
                      (if inexact
                          (record-condition (list 'ode-system-quadrature eqs)
                                            "dsolve-system: интеграл не выражен — ответ с невычисленным интегралом"))
                      (ode-solution 'particular res '() '() 'ok 'system chk))
                    (ode-solution 'unknown '() '() '()
                                  (if cok "решение не прошло сертификат" "условия не выполнены")
                                  'cauchy 'none))))))))



; (dsolve-system eqs funcs t [conds]) → ode-solution
(define (dsolve-system eqs funcs t &rest conds)
  (let* ((fs (sys-normalize-funcs funcs))
         (n (length fs))
         (af (try (sys-build eqs fs t) (lambda (e) #f))))
    (if (not af)
        (ode-solution 'unknown '() '() '()
                      "система не распознана как линейная с постоянными коэффициентами" 'system 'none)
        (let* ((A (car af)) (f (cadr af))
               (names (sys-const-names n))
               (h (ode-quiet (lambda () (try (sys-hom-rows A t names) (lambda (e) #f)))))
               (part (if (every? (lambda (v) (ode-zero? v)) f)
                         (list (sys-zero-vec n) #f)
                         (ode-quiet (lambda () (try (sys-particular A f t) (lambda (e) #f))))))
               (xp (if part (car part) (sys-zero-vec n)))
               (inexact (if part (cadr part) #f))
               (type (if inexact 'quadrature 'general)))
          (if (not h)
              (ode-solution 'unknown '() '() '() "e^{At} не построена" 'system 'none)
              (let* ((gen (map (lambda (i) (simplify (list '+ (nth h i) (nth xp i)))) (range n)))
                     (sols (map2 (lambda (fn rhs) (list '= fn rhs)) fs gen)))
                (if (not (null? conds))
                    (sys-cauchy eqs fs t conds sols names inexact)
                    (let ((chk (ode-quiet (lambda () (try (dsolve-system-check eqs sols fs t) (lambda (e) #f))))))
                      (if (not chk)
                          (ode-solution 'unknown '() '() '()
                                        "решение не прошло сертификат" 'system 'none)
                          (begin
                            (if (step-log-enabled?)
                                (let ((eig (ode-quiet (lambda () (try (eigenvalues A) (lambda (e) '())))))
                                      (cols (ode-quiet (lambda () (sys-fundamental A t)))))
                                  (record-step 'ode-sy-matrix "Матрица системы"
                                               "x′ = A·x + f: коэффициенты по функциям и свободный член"
                                               eqs A 'main)
                                  (record-step 'ode-sy-basis "Собственные значения и ФСР"
                                               (string-append "λ (кратности): "
                                                              (ode-mp-join
                                                               (map (lambda (e)
                                                                      (string-append "λ = " (ode-mp (car e))
                                                                                     " (кратность " (to-string (cadr e)) ")"))
                                                                    eig))
                                                              (if (any? (lambda (e) (> (cadr e) 1)) eig)
                                                                  "; кратное λ — жорданова клетка (t·e^{λt})"
                                                                  "")
                                                              "; фундаментальный набор: "
                                                              (ode-mp-join
                                                               (map (lambda (c)
                                                                      (string-append "["
                                                                                     (ode-mp-join (map ode-mp c))
                                                                                     "]"))
                                                                    cols)))
                                               A cols 'main)
                                  (record-step 'ode-sy-solution "Решение системы"
                                               (if (every? (lambda (v) (ode-zero? v)) f)
                                                   "однородная система: x = X(t)·C"
                                                   "неоднородная: x = X(t)·C + x_p(t)")
                                               eqs sols 'main)
                                  (record-step 'ode-sy-check "Проверка решения системы"
                                               "подстановка компонент в уравнения: остаток 0 — проверено"
                                               sols chk 'main)))
                            (if inexact
                                (record-condition (list 'ode-system-quadrature eqs)
                                                  "dsolve-system: интеграл не выражен — ответ с невычисленным интегралом"))
                            (ode-solution type sols names '() 'ok 'system chk)))))))))))

; ---------- ОДУ порядка n → система первого порядка ----------

; из уравнения выразить y⁽ⁿ⁾ (коэффициент — число)
(define (ode-solve-highest eq y x n)
  (let ((r (ode-coeff-of (ode-nth-deriv y x n) (ode-normalize eq) y x)))
    (and r (number? (car r)) (not (ode-zero? (car r)))
         (simplify (list '/ (list '- (cdr r)) (car r))))))

; y⁽ᵏ⁾ → vk, (y x) → v0
(define (ode-replace-derivs e y x fs)
  (cond ((equal? e (list y x)) (car fs))
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3) (equal? (caddr e) x)
              (ode-diff-depth e y x))
         (let ((k (ode-diff-depth e y x)))
           (if (< k (length fs)) (nth fs k) e)))
        ((pair? e) (map (lambda (z) (ode-replace-derivs z y x fs)) e))
        (else e)))

; (ode->system eq (y x)) → (уравнения . функции) или #f
(define (ode->system eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      #f
      (let* ((y (car yx)) (x (cadr yx)) (n (ode-order eq y x)))
        (if (< n 1)
            #f
            (let* ((fs (map (lambda (k)
                              (if (= k 0) (list y x)
                                  (list (string->symbol (string-append (to-string y)
                                                                       (to-string k)))
                                        x)))
                            (range n)))
                   (rhs (ode-solve-highest eq y x n)))
              (if (not rhs)
                  #f
                  (list (append
                         (map2 (lambda (vi vj) (list '= (list 'diff vi x) vj))
                               (take fs (- n 1)) (drop fs 1))
                         (list (list '= (list 'diff (nth fs (- n 1)) x)
                                     (ode-replace-derivs rhs y x fs))))
                        fs)))))))
