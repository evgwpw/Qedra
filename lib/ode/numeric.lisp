; numeric.lisp — численное решение задачи Коши (шаг WEB.PLOT): адаптивный Рунге — Кутта Дорманда — Принса 5(4).
; Уравнение порядка n, разрешимое относительно старшей производной (она входит линейно), сводится к системе
; первого порядка v = (y, y′, …, y⁽ⁿ⁻¹⁾). Результат — таблица точек (x v₀ … vₙ₋₁) и честный статус: отказ
; (особенность, взрыв решения, лимит шагов, правая часть не определена) — с причиной и точками до обрыва.
; Проверка (ode-numeric-check) — по невязке: на каждом шаге приращение компоненты сверяется с трапецией по
; правой части системы; неверная «таблица решения» отвергается.
(module ode-numeric
  (export ode-numeric ode-numeric-check ode-numeric-points ode-numeric-field ode-numeric-status
          ode-numeric-reason ode-numeric-rhs-fn))

; ---------- разбор уравнения ----------

(define (on-sym k) (string->symbol (string-append "odn" (to-string k))))

; производные (y x) → odnK: свободная замена по дереву
(define (on-replace e y x)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) y) (= (length e) 2) (equal? (cadr e) x)) (on-sym 0))
        ((and (equal? (car e) 'diff) (= (length e) 3) (ode::ode-diff-depth e y x))
         (on-sym (ode::ode-diff-depth e y x)))
        (else (map (lambda (z) (on-replace z y x)) e))))

; правая часть системы: (list n F cvars), F — выражение от x и odn0 … odn(n−1)
(define (on-build eq yx)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      (error "ode_numeric: второй аргумент — y(x)")
      (let* ((y (car yx)) (x (cadr yx))
             (eq1 (ode::ode-bare-y->call eq y x))
             (n (ode-order eq1 y x)))
        (if (< n 1)
            (error "ode_numeric: в уравнении нет производной неизвестной функции")
            (let* ((e (on-replace eq1 y x))
                   (res (if (and (pair? e) (equal? (car e) '=) (= (length e) 3))
                            (simplify (list '+ (cadr e) (list '* -1 (caddr e))))
                            (simplify e)))
                   (z (on-sym n)))
              (if (not (contains-sym? res z))
                  (error "ode_numeric: старшая производная не входит в уравнение")
                  (let* ((a (simplify (diff z res))))
                    (if (or (contains-sym? a z) (equal? a 0))
                        (error "ode_numeric: уравнение должно быть линейно по старшей производной (разрешите его относительно y⁽ⁿ⁾)")
                        (let* ((b (simplify (subst (list z 0) res)))
                               (F (simplify (list '* (list '* -1 b) (list '^ a -1)))))
                          (list n F x))))))))))

(define (ode-numeric-rhs-fn eq yx)
  (let* ((b (on-build eq yx)) (n (nth b 0)) (F (nth b 1)) (x (nth b 2)))
    (list n (on-make-f n F x) x)))

; f(x, v) = (v₁ … vₙ₋₁ F(x, v)); сбой вычисления — raise
(define (on-make-f n F x)
  (lambda (xv v)
    (let* ((rules (cons (list x xv) (map (lambda (i) (list (on-sym i) (nth v i))) (range n))))
           (fv (try (eval-num (subst rules F)) (lambda (e) #f))))
      (if (and (number? fv) (= fv fv) (< (abs fv) 1e300))
          (append (cdr v) (list (* 1.0 fv)))
          (raise (list 'on-fail (string-append "правая часть не определена при x = " (on-fmt xv))))))))

; число в сообщении: 4 знака после запятой
(define (on-fmt v) (to-string (/ (floor (+ (* v 10000) 0.5)) 10000.0)))

; ---------- Дорманд — Принс ----------

(define (on-fl l) (map (lambda (q) (* 1.0 q)) l))
(define on-a2 (on-fl '(1/5)))
(define on-a3 (on-fl '(3/40 9/40)))
(define on-a4 (on-fl '(44/45 -56/15 32/9)))
(define on-a5 (on-fl '(19372/6561 -25360/2187 64448/6561 -212/729)))
(define on-a6 (on-fl '(9017/3168 -355/33 46732/5247 49/176 -5103/18656)))
(define on-b5 (on-fl '(35/384 0 500/1113 125/192 -2187/6784 11/84)))
; b5 − b4 (оценка погрешности), 7 коэффициентов
(define on-e (on-fl '(71/57600 0 -71/16695 71/1920 -17253/339200 22/525 -1/40)))

; y + h·Σ cⱼ kⱼ покомпонентно
(define (on-comb y h ks cs)
  (let ((cs1 (take cs (length ks))))
    (map (lambda (i)
           (+ (nth y i) (* h (foldl + 0.0 (map2 (lambda (c k) (* c (nth k i))) cs1 ks)))))
         (range (length y)))))

(define (on-norm err y y1 rtol atol)
  (foldl (lambda (m i)
           (let* ((sc (+ atol (* rtol (max (abs (nth y i)) (abs (nth y1 i))))))
                  (r (/ (abs (nth err i)) sc)))
             (if (> r m) r m)))
         0.0 (range (length y))))

; один шаг: k1 известен; → (ynew err k7)
(define (on-step f x y h k1 rtol atol)
  (let* ((k2 (f (+ x (* h 1/5)) (on-comb y h (list k1) on-a2)))
         (k3 (f (+ x (* h 3/10)) (on-comb y h (list k1 k2) on-a3)))
         (k4 (f (+ x (* h 4/5)) (on-comb y h (list k1 k2 k3) on-a4)))
         (k5 (f (+ x (* h 8/9)) (on-comb y h (list k1 k2 k3 k4) on-a5)))
         (k6 (f (+ x h) (on-comb y h (list k1 k2 k3 k4 k5) on-a6)))
         (y1 (on-comb y h (list k1 k2 k3 k4 k5 k6) on-b5))
         (k7 (f (+ x h) y1))
         (er (on-comb (map (lambda (i) 0.0) y) h (list k1 k2 k3 k4 k5 k6 k7) on-e)))
    (list y1 (on-norm er y y1 rtol atol) k7)))

(define (on-finite? v) (every? (lambda (c) (and (number? c) (= c c) (< (abs c) 1e10))) v))

; прогон от x0 до x1 (любое направление) → (status pts reason steps); pts — от x0 к x1
(define (on-run f x0 v0 x1 rtol atol maxit)
  (let* ((span (abs (- x1 x0)))
         (dir (if (> x1 x0) 1.0 -1.0))
         (hmax (/ span 200.0)))
    (if (= span 0)
        (list 'ok (list (cons x0 v0)) #f 0)
        (try
         (let loop ((x x0) (v v0) (k1 (f x0 v0)) (h (* dir (/ span 400.0))) (pts (list (cons x0 v0))) (it 0))
           (cond
             ((>= (* dir (- x x1)) 0) (list 'ok (reverse pts) #f it))
             ((> it maxit) (list 'failed (reverse pts) (string-append "лимит шагов (" (to-string maxit) ") исчерпан около x = " (on-fmt x)) it))
             ((< (abs h) (* 1e-13 (max 1.0 (abs x))))
              (list 'failed (reverse pts) (string-append "шаг стал слишком мал: особенность решения около x = " (on-fmt x)) it))
             (else
              (let* ((last? (>= (abs h) (abs (- x1 x))))
                     (hh (if last? (- x1 x) h))
                     (st (try (on-step f x v hh k1 rtol atol) (lambda (e) (list 'fail e))))
                     (bad? (symbol? (car st)))
                     (v1 (if bad? v (nth st 0))) (er (if bad? 0.0 (nth st 1))) (k7 (if bad? k1 (nth st 2)))
                     (fac (if (<= er 0.0) 5.0 (min 5.0 (max 0.2 (* 0.9 (eval-num (list '^ er -0.2)))))))
                     (hn (* dir (min hmax (* (abs hh) fac)))))
                (cond
                  (bad?
                   (let ((d (error-data (cadr st))))
                     (if (and (pair? d) (equal? (car d) 'on-fail))
                         (if (> (abs hh) (* 1e-6 span))
                             (loop x v k1 (* hh 0.25) pts (+ it 1))
                             (list 'failed (reverse pts) (cadr d) it))
                         (raise (cadr st)))))
                  ((not (on-finite? v1))
                   (if (> er 1.0)
                       (loop x v k1 (* hh 0.25) pts (+ it 1))
                       (list 'failed (reverse pts) (string-append "решение уходит в бесконечность около x = " (on-fmt x)) it)))
                  ((<= er 1.0)
                   (let ((xn (if last? x1 (+ x hh))))
                     (loop xn v1 k7 (if last? hh hn) (cons (cons xn v1) pts) (+ it 1))))
                  (else
                   (loop x v k1 (* hh (min 0.9 (max 0.2 fac))) pts (+ it 1))))))))
         (lambda (e)
           (let ((d (error-data e)))
             (if (and (pair? d) (equal? (car d) 'on-fail))
                 (list 'failed (list (cons x0 v0)) (cadr d) 0)
                 (raise e))))))))

; ---------- вход ----------

(define (on-range-list r)
  (cond ((tensor? r) (tensor->list r))
        ((vector? r) (vector->list r))
        ((and (pair? r) (equal? (car r) 'm-vector)) (cdr r))
        (else r)))

(define (on-kw? a) (and (symbol? a) (member? a '(:rtol :atol :max-steps))))

(define (on-split args)
  (let loop ((l args) (conds '()))
    (if (or (null? l) (on-kw? (car l)))
        (list (reverse conds) l)
        (loop (cdr l) (cons (car l) conds)))))

(define (on-opt opts key dflt)
  (cond ((or (null? opts) (null? (cdr opts))) dflt)
        ((equal? (car opts) key) (cadr opts))
        (else (on-opt (cddr opts) key dflt))))

(define (on-num e what)
  (let ((v (try (eval-num e) (lambda (er) #f))))
    (if (and (number? v) (= v v)) (* 1.0 v) (error "ode_numeric: не число:" what e))))

; условия → (x0 v₀ … vₙ₋₁) (числа с плавающей точкой)
(define (on-initial conds y x n)
  (let ((cs (map (lambda (c) (let ((r (ode::ca-condition c y x)))
                               (if r r (error "ode_numeric: условие не вида y(x0) = v, y'(x0) = w, …:" c))))
                 conds)))
    (cond
      ((not (= (length cs) n))
       (error "ode_numeric: нужно ровно" n "начальных условий (y(x0), y'(x0), …), задано" (length cs)))
      ((not (every? (lambda (c) (and (>= (car c) 0) (< (car c) n))) cs))
       (error "ode_numeric: порядок производной в условии вне 0.." (- n 1)))
      ((not (every? (lambda (c) (equal? (simplify (cadr c)) (simplify (cadr (car cs))))) cs))
       (error "ode_numeric: условия должны быть заданы в одной точке x0"))
      (else
       (let ((ks (map car cs)))
         (if (not (= (length (filter (lambda (k) (member? k ks)) (range n))) n))
             (error "ode_numeric: порядки производных в условиях повторяются")
             (cons (on-num (cadr (car cs)) 'x0)
                   (map (lambda (k) (on-num (caddr (car (filter (lambda (c) (= (car c) k)) cs))) 'value))
                        (range n)))))))))

; (ode-numeric eq (y x) (x a b) cond… [:rtol r :atol a :max-steps n]) → результат-список:
; (ode-numeric-result :status ok|failed :points ((x y y′ …) …) :reason текст|#f :method … :init x0 :range (a b) :steps n :order n)
(define (ode-numeric eq yx range &rest args)
  (let* ((rg (on-range-list range))
         (sp (on-split args)) (conds (nth sp 0)) (opts (nth sp 1)))
    (if (not (and (list? rg) (= (length rg) 3) (equal? (car rg) (cadr yx))))
        (error "ode_numeric: третий аргумент — [x, x0, x1] с той же переменной, что в y(x)")
        (let* ((b (on-build eq yx)) (n (nth b 0)) (F (nth b 1)) (x (nth b 2))
               (f (on-make-f n F x))
               (a (on-num (nth rg 1) 'a)) (bb (on-num (nth rg 2) 'b))
               (ini (on-initial conds (car yx) x n))
               (c (car ini)) (v0 (cdr ini))
               (lo (min a bb c)) (hi (max a bb c))
               (rtol (* 1.0 (on-opt opts :rtol 1e-9))) (atol (* 1.0 (on-opt opts :atol 1e-11)))
               (maxit (on-opt opts :max-steps 20000))
               (fw (if (< c hi) (on-run f c v0 hi rtol atol maxit) (list 'ok (list (cons c v0)) #f 0)))
               (bw (if (> c lo) (on-run f c v0 lo rtol atol maxit) (list 'ok (list (cons c v0)) #f 0)))
               (pts (append (reverse (cdr (nth bw 1))) (nth fw 1)))
               (bad (cond ((equal? (nth fw 0) 'failed) fw) ((equal? (nth bw 0) 'failed) bw) (else #f))))
          (list 'ode-numeric-result :status (if bad 'failed 'ok) :points pts
                :reason (if bad (nth bad 2) #f)
                :method "RK45 (Дорманд — Принс 5(4))" :init c :range (list lo hi)
                :steps (+ (nth fw 3) (nth bw 3)) :order n)))))

(define (ode-numeric-field r key) (on-opt (cdr r) key #f))
(define (ode-numeric-status r) (ode-numeric-field r :status))
(define (ode-numeric-reason r) (ode-numeric-field r :reason))
(define (ode-numeric-points r) (ode-numeric-field r :points))

; ---------- проверка по невязке ----------
; Для каждой пары соседних точек приращение компоненты vᵢ должно совпадать с квадратурой Симпсона
; h/6·(fᵢ(k) + 4·fᵢ(середина) + fᵢ(k+1)) (значение в середине — кубический Эрмит по vᵢ, fᵢ) с допуском
; tol·h·max|fᵢ|; так неверная таблица (не решение уравнения) отвергается. Ошибка Симпсона O(h⁴) — на эталонах
; отношение ≈ 1e-7…1e-5, допуск по умолчанию 1e-3.
(define (ode-numeric-check eq yx pts &rest args)
  (let* ((tol (if (pair? args) (car args) 1e-3))
         (b (on-build eq yx)) (n (nth b 0)) (F (nth b 1)) (x (nth b 2))
         (f (on-make-f n F x)))
    (if (or (not (list? pts)) (< (length pts) 2)
            (not (every? (lambda (p) (and (list? p) (= (length p) (+ n 1)) (every? number? p))) pts)))
        #f
        (try
         (let loop ((l pts))
           (if (null? (cdr l))
               #t
               (let* ((p (car l)) (q (cadr l))
                      (h (- (car q) (car p)))
                      (fp (f (car p) (cdr p))) (fq (f (car q) (cdr q)))
                      (vm (map (lambda (i) (+ (* 0.5 (+ (nth (cdr p) i) (nth (cdr q) i))) (* h 0.125 (- (nth fp i) (nth fq i)))))
                               (range n)))
                      (fm (f (+ (car p) (* 0.5 h)) vm)))
                 (if (and (> h 0)
                          (every? (lambda (i)
                                    (let ((d (- (nth (cdr q) i) (nth (cdr p) i)))
                                          (sm (* (/ h 6.0) (+ (nth fp i) (* 4.0 (nth fm i)) (nth fq i))))
                                          (sc (max (abs (nth fp i)) (abs (nth fm i)) (abs (nth fq i)))))
                                      (<= (abs (- d sm)) (+ (* tol h sc) (* 1e-9 h)))))
                                  (range n)))
                     (loop (cdr l))
                     #f))))
         (lambda (e) #f)))))
