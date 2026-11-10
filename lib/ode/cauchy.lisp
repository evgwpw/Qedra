; cauchy.lisp — задача Коши для ОДУ (шаг ODE.4a): условия поверх общего решения.
; Условия: (= (y x0) v), (= (at (diff (y x) x) (= x x0)) v) — и порядка k (вложенные diff внутри at).
; После общего решения условия подставляются → линейная система на C1…Cn (solve) → частное решение.
; Несовместные условия → :status unknown с причиной; неявные ответы — подстановка в F(x, y) = C1.
(module ode
  (export dsolve-conditions-check))

; условия формулой для пояснения: «y(0) = 1, y′(0) = 0»
(define (ca-cond-name c y)
  (let* ((k (car c)) (x0 (cadr c)) (v (caddr c))
         (d (cond ((= k 0) "") ((= k 1) "′") ((= k 2) "″") ((= k 3) "‴")
                  (else (string-append "^(" (to-string k) ")")))))
    (string-append (to-string y) d "(" (ode-mp x0) ") = " (ode-mp v))))
(define (ca-conds-text conds y)
  (ode-mp-join (map (lambda (c) (ca-cond-name c y)) conds)))

; ---------- разбор одного условия → (deriv-k x0 v); #f — не условие на (y x) ----------

; (= (y x0) v): x0 — число или простое выражение без y;
; (= (at expr (= x x0)) v): expr — k-я производная (y x). Иначе #f.
(define (ca-at-parts cond)
  ; (= (at expr (= x x0)) v) → (expr x0 v); иначе #f
  (if (and (pair? cond) (equal? (car cond) '=) (= (length cond) 3)
           (pair? (cadr cond)) (equal? (car (cadr cond)) 'at) (= (length (cadr cond)) 3)
           (pair? (caddr (cadr cond))) (equal? (car (caddr (cadr cond))) '=)
           (= (length (caddr (cadr cond))) 3))
      (let ((pt (caddr (cadr cond))))
        (list (cadr (cadr cond)) (caddr pt) (caddr cond)))
      #f))

(define (ca-condition cond y x)
  (if (and (pair? cond) (equal? (car cond) '=) (= (length cond) 3)
           (pair? (cadr cond)) (equal? (car (cadr cond)) y) (= (length (cadr cond)) 2)
           (not (equal? (cadr (cadr cond)) x))
           (not (ode-y-node-any? (caddr cond) y x)))
      (list 0 (cadr (cadr cond)) (caddr cond))
      (let ((p (ca-at-parts cond)))
        (if (not p)
            #f
            (let* ((expr (car p)) (x0 (cadr p)) (v (caddr p))
                   (k (ode-diff-depth expr y x)))
              (and k (>= k 1)
                   (not (ode-y-node-any? v y x))
                   (list k x0 v)))))))

; ---------- подстановка условий в решение ----------

; подставить x = x0 в k-ю производную правой части (выражение rhs от x)
(define (ca-eval-at rhs k x x0)
  (let loop ((j 0) (e rhs))
    (if (>= j k)
        (simplify (subst (list (list x x0)) e))
        (loop (+ j 1) (simplify (diff x e))))))

; применить условия к явному решению: вернуть список (Ci vi) или 'inconsistent/#f.
; Fallback для иррациональных уравнений на C1 (sqrt): возвести в квадрат и проверить потом
; подстановкой (ca-check-condition отсечёт ложную ветвь).
(define (ca-sq-both eqn)
  ; (= lhs v) → (= A·k² v²), если lhs = k·sqrt(A) и v — число; проверка условия отсечёт ложную ветвь
  (let ((lhs (cadr eqn)) (v (caddr eqn)))
    (if (not (number? v))
        #f
        (let ((p (ca-sqrt-parts lhs)))
          (if (not p)
              #f
              (list '= (simplify (list '* (car p) (car p) (cdr p)))
                    (list '* v v)))))))

; lhs = k·sqrt(A) → (k² . A) точнее (k . A); sqrt(A) → (1 . A); иначе #f
(define (ca-sqrt-parts lhs)
  (cond ((and (pair? lhs) (equal? (car lhs) 'sqrt) (= (length lhs) 2))
         (cons 1 (cadr lhs)))
        ((and (pair? lhs) (equal? (car lhs) '*))
         (let ((sq (filter (lambda (z) (and (pair? z) (equal? (car z) 'sqrt))) (cdr lhs)))
               (rest (filter (lambda (z) (not (and (pair? z) (equal? (car z) 'sqrt)))) (cdr lhs))))
           (if (= (length sq) 1)
               (cons (foldl * 1 rest) (cadr (car sq)))
               #f)))
        (else #f)))

(define (ca-apply-conditions sol consts conds y x)
  (let* ((rhs (if (and (pair? sol) (equal? (car sol) '=)) (caddr sol) sol))
         (eqs (map (lambda (c)
                     (let ((k (car c)) (x0 (cadr c)) (v (caddr c)))
                       (list '= (ca-eval-at rhs k x x0) v)))
                   conds)))
    (let ((ss (try (set->list (solve eqs consts)) (lambda (e) #f))))
      (cond (ss
             (cond ((null? ss) 'inconsistent)
                   (else (car ss))))
            (else
             ; fallback: в уравнениях с sqrt возвести в квадрат
             (let ((eqs2 (map (lambda (e) (or (ca-sq-both e) e)) eqs)))
               (if (equal? eqs2 eqs)
                   #f
                   (let ((ss2 (try (set->list (solve eqs2 consts)) (lambda (e) #f))))
                     (cond ((not ss2) #f)
                           ((null? ss2) 'inconsistent)
                           (else (car ss2)))))))))))


; применить уравнения-биндинги ((= Ci vi)) к выражению
(define (ca-subst-binds e binds)
  (if (null? binds)
      e
      (let* ((b (car binds))
             (lhs (cadr b)) (rhs (caddr b)))
        (if (equal? lhs rhs)
            (ca-subst-binds e (cdr binds))
            (ca-subst-binds (simplify (subst (list (list lhs rhs)) e)) (cdr binds))))))

; проверить условие (k x0 v) на rhs (после подстановки констант): сначала together/simplify
; разности; численный запасной путь — относительный допуск 1e-12 → 'numeric (не #t); иначе #f
(define (ca-check-condition rhs k x x0 v)
  (let ((z (simplify (together (list '- (ca-eval-at rhs k x x0) v)))))
    (cond ((ode-zero? z) #t)
          ((ode-surely-nonzero? z) #f)
          (else
           (let* ((val (eval-num z))
                  (vv (eval-num v)))
             (if (and (number? val) (number? vv)
                      (< (abs val) (* 1e-12 (+ 1 (abs vv)))))
                 'numeric
                 #f))))))

; ---------- главный диспетчер задачи Коши ----------

; (ca-solve eq yx conds): conds — разобранные условия (k x0 v); вызывается из dsolve
; после получения общего решения r (без условий).
(define (ca-solve eq yx conds r)
  (let* ((y (car yx)) (x (cadr yx))
         (sols (ode-solutions r))
         (sol (if (pair? sols) (car sols) #f))
         (ty (ode-field r :type)))
    (cond
      ; неявный ответ (= F C1): подставляем x0, y0 → C1; высшие условия — через производную
      ; неявной функции (не делаем — честный unknown с причиной)
      ((equal? ty 'implicit)
       (if (and (= (length conds) 1) (= (car (car conds)) 0)
                (pair? sol) (equal? (car sol) '=) (equal? (caddr sol) 'C1))
           (let* ((c0 (car conds)) (x0 (cadr c0)) (y0 (caddr c0))
                  (F (cadr sol))
                  (b (ca-implicit-value F x y x0 y0)))
             ; частное неявное решение: F(x, y) = F(x0, y0); невычисленный ∫f dy в ответе — определённый
             ; ∫_{y0}^{y} (с этой нормировкой посчитано b; неопределённый ∫ означал бы «с любой константой»)
             (ode-solution 'particular (list (list '= (ca-definite-from F y y0) b)) '() '() 'ok
                           (ode-field r :method) (ca-implicit-cert r (ca-implicit-check-value eq F b x y conds))))
           (ode-solution 'unknown '() '() '()
                         "условия порядка ≥ 1 на неявное решение не поддерживаются" 'cauchy 'none)))
      ; явное решение: возможно несколько ветвей (±√…) — берётся та, что удовлетворяет условиям
      ((and (pair? sols) (equal? (ode-status r) 'ok))
       (let lp ((ss sols) (bad #f))
         (cond
           ((null? ss)
            (ode-solution 'unknown '() '() '()
                           (if (equal? bad 'inconsistent)
                               "условия несовместны: система на C1…Cn не имеет решения"
                               "ни одна ветвь решения не удовлетворяет условиям")
                           'cauchy 'none))
           (else
            (let ((res (ca-solve-one eq yx conds r (car ss))))
              (cond ((equal? res 'inconsistent) (lp (cdr ss) 'inconsistent))
                    (res (res #f))
                    (else (lp (cdr ss) bad))))))))
      (else
       (ode-solution 'unknown '() '() '()
                     "общее решение не найдено — условия проверить нельзя"
                     'cauchy 'none)))))

; применить условия к одной ветви; #f — не подошла; 'inconsistent — система несовместна
(define (ca-solve-one eq yx conds r sol)
  (let* ((y (car yx)) (x (cadr yx))
         (consts (ode-field r :constants))
         (bs (ode-quiet (lambda () (ca-apply-conditions sol consts conds y x)))))
    (cond ((equal? bs 'inconsistent) 'inconsistent)
          ((not bs) #f)
          ((null? consts)
           ; констант нет (particular) — только проверить условия
           (let ((ok (ode-quiet
                      (lambda ()
                        (map (lambda (c) (ca-check-condition (caddr sol) (car c) x (cadr c) (caddr c)))
                             conds)))))
             (if (any? (lambda (z) (equal? z #f)) ok)
                 #f
                 (begin
                   (if (step-log-enabled?)
                       (record-step 'ode-ca-check "Проверка начальных условий"
                                    "подстановка значений и производных в решение: условия выполнены"
                                    sol ok 'main))
                   (lambda (u) (ode-solution 'particular (list sol) '() '() 'ok
                                             (ode-field r :method) (car ok)))))))
          (else
           (let* ((rhs2 (ca-subst-binds (caddr sol) bs))
                  (sol2 (list '= (list y x) rhs2)))
             (let ((chk (ode-quiet (lambda () (dsolve-check eq sol2 yx))))
                   (cok (ode-quiet
                         (lambda ()
                           (map (lambda (c) (ca-check-condition rhs2 (car c) x (cadr c) (caddr c)))
                                conds)))))
               (if (and chk (not (any? (lambda (z) (equal? z #f)) cok)))
                   (begin
                     (if (step-log-enabled?)
                         (begin
                           (record-step 'ode-ca-consts "Константы из начальных условий"
                                        (string-append "условия: " (ca-conds-text conds y)
                                                       "; подстановка x = x₀ в решение и производные → "
                                                       "линейная система по C1…Cn решена")
                                        sol bs 'main)
                           (record-step 'ode-ca-check "Проверка начальных условий"
                                        "значения решения и производных при x = x₀ совпадают с заданными"
                                        sol2 cok 'main)))
                     (lambda (u) (ode-solution 'particular (list sol2) '() '() 'ok
                                               (ode-field r :method)
                                               (if (and (equal? chk #t) (all-true? cok)) #t 'numeric))))
                   #f)))))))

; значение F(x0, y0): невычисленный integrate по y → определённый от y0 до y0 (= 0) ДО
; подстановки y = y0 (иначе subst испортит переменную интегрирования); затем подстановки
(define (ca-implicit-value F x y x0 y0)
  (let* ((Fx (subst (list (list x x0)) (ca-definite-zero F y y0)))
         (Fy (if (and (ode-mentions-sym? Fx y) (number? y0))
                 (subst (list (list y y0)) Fx)
                 Fx)))
    (simplify Fy)))

; невычисленный (integrate f y) → (integrate f[y→ode-s] ode-s y0 y) — первообразная, равная 0 при y = y0
(define (ca-definite-from e y y0)
  (cond ((and (pair? e) (equal? (car e) 'integrate) (= (length e) 3) (equal? (caddr e) y))
         (list 'integrate (subst (list (list y 'ode-s)) (cadr e)) 'ode-s y0 y))
        ((pair? e) (map (lambda (z) (ca-definite-from z y y0)) e))
        (else e)))

; невычисленный integrate по y → определённый от y0 до y0; равные пределы = 0
(define (ca-definite-zero e y y0)
  (cond ((and (pair? e) (equal? (car e) 'integrate) (= (length e) 3)
              (equal? (caddr e) y))
         (let ((v (integrate (cadr e) y y0 y0)))
           (if (and (pair? v) (equal? (car v) 'integrate)) 0 (simplify v))))
        ((pair? e) (map (lambda (z) (ca-definite-zero z y y0)) e))
        (else e)))

; сертификат неявного частного: проверка общего решения (уравнение; F отличается от ответа константой)
; и условия (значение F(x0, y0)); любая не прошла → #f; 'numeric у общего → 'numeric
(define (ca-implicit-cert r cond-ok)
  (let ((g (ode-field r :check)))
    (cond ((not (and g (not (equal? g 'none)) cond-ok)) #f)
          ((equal? g 'numeric) 'numeric)
          (else cond-ok))))

; сертификат неявного частного (= F c) с условием порядка 0: F(x0, v) = c точно;
; порядок ≥ 1 — #f (сертификата нет)
(define (ca-implicit-check-value eq F c x y conds)
  (if (any? (lambda (cnd) (> (car cnd) 0)) conds)
      #f
      (let ((z (simplify (list '- (ca-implicit-value F x y (cadr (car conds)) (caddr (car conds)))
                          c))))
        (if (ode-zero? z) #t #f))))


(define (all-true? xs)
  (cond ((null? xs) #t)
        ((not (equal? (car xs) #t)) #f)
        (else (all-true? (cdr xs)))))

; (dsolve-conditions-check eq sol yx conds) → #t | 'numeric | #f: dsolve-check + каждое условие.
; conds — условия в исходной форме ((= (y 0) 1) …) или разобранные (k x0 v); неразборное условие → #f.
; Явное решение (= (y x) rhs) — проверка всех условий (одно 'numeric → итог 'numeric, но проверяются все);
; неявное (= F C) — условиями не проверяется → #f (сертификата нет).
(define (dsolve-conditions-check eq sol yx conds)
  (let* ((y (car yx)) (x (cadr yx))
         (chk (dsolve-check eq sol yx))
         (rhs (if (and (pair? sol) (equal? (car sol) '=) (equal? (cadr sol) yx)) (caddr sol) #f))
         (parsed (map (lambda (c) (if (and (pair? c) (equal? (car c) '=)) (ca-condition c y x) c)) conds)))
    (cond ((not chk) #f)
          ((null? conds) chk)
          ((not rhs) #f)
          ((any? (lambda (c) (not c)) parsed) #f)
          (else
           (let loop ((cs parsed) (acc chk))
             (if (null? cs)
                 acc
                 (let ((one (ca-check-condition rhs (car (car cs)) x (cadr (car cs)) (caddr (car cs)))))
                   (cond ((equal? one #f) #f)
                         ((equal? one 'numeric) (loop (cdr cs) 'numeric))
                         (else (loop (cdr cs) acc))))))))))

(define *ode-cauchy-loaded* #t)
