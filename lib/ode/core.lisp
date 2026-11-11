; core.lisp — каркас ОДУ (шаг ODE.0)
; Неизвестная функция — (y x); производные — штатный вложенный (diff (y x) x).
; Результат — (ode-solution :type … :solutions … :constants … :singular … :status … :method … :check …).
; В ODE.0 решаются только квадратуры y⁽ⁿ⁾ = f(x); остальное — честный status unknown.
(module ode
  (export dsolve dsolve-check ode-solution ode-solutions ode-status ode-subst
          ode-order ode-linear? ode-const-coeff? ode-autonomous?))

; ---------- объект результата ----------

(define (ode-solution type solutions constants singular status method check)
  (list 'ode-solution :type type :solutions solutions :constants constants
        :singular singular :status status :method method :check check))

(define (ode-field r key)
  (let loop ((xs (cdr r)))
    (cond ((null? xs) #f)
          ((equal? (car xs) key) (cadr xs))
          (else (loop (cddr xs))))))

(define (ode-solutions r) (ode-field r :solutions))
(define (ode-status r) (ode-field r :status))

; ---------- шаги ST.3а: общие пометки ----------

; служебный вызов (integrate, solve, проверка) — без собственных шагов в журнале
(define (ode-quiet thunk) (if (step-log-enabled?) (call-quietly thunk) (thunk)))

; служебная производная (в данных шага она показывается результатом, а не деревом правил)
(define (ode-diff var e) (ode-quiet (lambda () (diff var e))))

; ---------- печать формул в пояснениях (ST.3а-4) ----------
; внутренние имена → привычные подписи: %l (характеристический многочлен) → λ, rr (определяющее) → r,
; %i (мнимая единица из solve) → i
(define (ode-mp-binds) (list (list '%l 'λ) (list 'rr 'r) (list '%i 'i)))

; формула входного языка (MathPrinter) после подстановки подписей; при ошибке печати — обычная запись
(define (ode-mp* binds e)
  (try (math-print (if (null? binds) e (subst binds e))) (lambda (err) (to-string e))))
(define (ode-mp e) (ode-mp* (ode-mp-binds) e))

(define (ode-mp-join ss)
  (if (null? ss) "" (foldl (lambda (acc s) (string-append acc ", " s)) (car ss) (cdr ss))))
(define (ode-mp-list es) (ode-mp-join (map ode-mp es)))

; подписи неизвестных коэффициентов пробного решения: A, B, …, Z (дальше A1, B1, …)
(define *ode-letters*
  '("A" "B" "C" "D" "E" "F" "G" "H" "I" "J" "K" "L" "M"
    "N" "O" "P" "Q" "R" "S" "T" "U" "V" "W" "X" "Y" "Z"))
(define (ode-letter k)
  (if (< k (length *ode-letters*))
      (string->symbol (nth *ode-letters* k))
      (string->symbol (string-append (nth *ode-letters* (- k (* (length *ode-letters*) (quotient k (length *ode-letters*)))))
                                     (to-string (+ 1 (quotient k (length *ode-letters*))))))))

; классификация уравнения (диспетчер): порядок, линейность, автономность
(define (ode-classify-step eq yx n)
  (if (step-log-enabled?)
      (let ((lin (ode-linear? eq yx))
            (aut (ode-autonomous? eq yx)))
        (record-step 'ode-classify "Классификация уравнения"
                     (string-append "порядок " (to-string n)
                                    (if lin "; линейное по y и производным" "; нелинейное")
                                    (if aut "; автономное" "; неавтономное"))
                     eq (ode-normalize eq) 'main)))
  #t)

; решение вида (= (y x) rhs) — проверяемое подстановкой (неявное и параметрическое не сюда)
(define (ode-checkable? ss yx)
  (cond ((null? ss) #t)
        ((and (pair? (car ss)) (equal? (car (car ss)) '=) (equal? (cadr (car ss)) yx))
         (ode-checkable? (cdr ss) yx))
        (else #f)))

; шаг проверки ответа: подстановка в уравнение (dsolve-check) — реально выполняется
(define (ode-check-step eq yx r)
  ; замечание ревью ST.3а): подстановка — только при включённом журнале (иначе dsolve-check шёл дважды)
  (if (not (and (step-log-enabled?) (pair? r) (equal? (car r) 'ode-solution)
                (equal? (ode-field r :status) 'ok)
                (pair? (ode-field r :solutions))
                (not (member? (ode-field r :method) '(series frobenius kovacic)))
                (ode-checkable? (append (ode-field r :solutions) (ode-field r :singular)) yx)))
      r
      (let* ((sols (append (ode-field r :solutions) (ode-field r :singular)))
             (res (map (lambda (s) (ode-quiet (lambda () (dsolve-check eq s yx)))) sols)))
        (if (step-log-enabled?)
            (record-step 'ode-check "Проверка решения"
                         (cond ((any? (lambda (c) (not c)) res)
                                "подстановка не даёт 0 — ответ не проверен")
                               ((any? (lambda (c) (equal? c 'numeric)) res)
                                "подстановка в уравнение: остаток 0 численно")
                               (else "подстановка в уравнение даёт 0 — проверено"))
                         sols res 'main))
        r)))

; причина отказа: какие методы пробовались и почему не подошли
(define (ode-refusal-comment eq y x n)
  (if (= n 1)
      (let* ((rhs (and *ode-first-order-loaded* (try (fo-rhs eq y x) (lambda (e) #f))))
             (f (and rhs (fo-bare rhs y x))))
        (if (not f)
            "уравнение не разрешается относительно y′: методы первого порядка не применимы"
            (let* ((lin (try (fo-linear-parts f) (lambda (e) #f)))
                   (bp (and (not lin) (try (fo-bern-parts f) (lambda (e) #f))))
                   (sp (and (not lin) (not bp) (try (fo-separable-parts f) (lambda (e) #f))))
                   (mn (and *ode-exact-loaded* (try (ex-mn-of eq y x) (lambda (e) #f))))
                   (res (and mn (try (ex-exact-residue (car mn) (cdr mn) x y) (lambda (e) #f)))))
              (string-append
               "f = " (ode-mp f)
               "; пробованы: разделение переменных, линейное, Бернулли, однородное, точное/μ, Риккати, Клеро/Лагранж; "
               (cond (lin "линейное: ответ не прошёл проверку")
                     (bp "Бернулли: интеграл не выразился")
                     ((and sp (not (fo-free-y? (cdr sp))))
                      (string-append "разделение: g = " (ode-mp (car sp)) ", h = " (ode-mp (cdr sp))
                                     " — интеграл не выразился"))
                     (else "не разделяется на g(x)·h(y)"))
               (if res (string-append "; M_y − N_x = " (ode-mp res) " ≠ 0")
                   "; критерий точности не выполнен")))))
      (string-append "порядок " (to-string n)
                     "; пробованы: постоянные коэффициенты, Эйлер–Коши, понижение порядка, квадратура, ряды — ответ не найден")))

(define (ode-refuse-step eq yx n)
  (if (step-log-enabled?)
      (record-step 'ode-refuse "Решение не найдено"
                   (ode-refusal-comment eq (car yx) (cadr yx) n)
                   eq 'не-решено 'main))
  #t)

; ---------- разбор выражения: y(x), производные, признаки ----------

(define (ode-y-node? e y x) (equal? e (list y x)))

; k, если e — это k-кратная производная (y x) по x; иначе #f
(define (ode-diff-depth e y x)
  (cond ((equal? e (list y x)) 0)
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3) (equal? (caddr e) x))
         (let ((k (ode-diff-depth (cadr e) y x)))
           (if k (+ k 1) #f)))
        (else #f)))

(define (ode-deriv? e y x)
  (let ((k (ode-diff-depth e y x))) (and k (> k 0))))

(define (ode-y-node-any? e y x)
  (cond ((ode-y-node? e y x) #t)
        ((ode-diff? e y x) #t)
        ((pair? e) (any? (lambda (z) (ode-y-node-any? z y x)) e))
        (else #f)))

(define (ode-diff? e y x)
  (and (pair? e) (equal? (car e) 'diff) (= (length e) 3)
       (equal? (caddr e) x) (ode-diff-depth e y x)))

(define (ode-contains? d e)
  (or (equal? d e) (and (pair? e) (any? (lambda (z) (ode-contains? d z)) e))))

; встречается ли символ s (язык может передать y(x) как произведение x·y)
(define (ode-mentions-sym? e s)
  (cond ((equal? e s) #t)
        ((pair? e) (any? (lambda (z) (ode-mentions-sym? z s)) e))
        (else #f)))

(define (ode-mentions-x? e y x)
  (cond ((equal? e (list y x)) #f)
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3)
              (equal? (caddr e) x) (ode-diff-depth e y x)) #f)
        ((equal? e x) #t)
        ((pair? e) (any? (lambda (z) (ode-mentions-x? z y x)) e))
        (else #f)))

; порядок уравнения: максимальная кратность производной (y x)
(define (ode-order eq y x)
  (let loop ((e eq) (best 0))
    (cond ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3) (equal? (caddr e) x))
           (let ((k (ode-diff-depth e y x)))
             (if k (max best k) (loop (cadr e) best))))
          ((pair? e) (foldl (lambda (acc z) (max acc (loop z best))) best e))
          (else best))))

(define (ode-nth-deriv y x n)
  (let loop ((k 1) (d (list 'diff (list y x) x)))
    (if (>= k n) d (loop (+ k 1) (list 'diff d x)))))

(define (ode-normalize eq)
  (if (and (pair? eq) (equal? (car eq) '=)) (simplify (list '- (cadr eq) (caddr eq))) eq))

; ---------- линейность, постоянные коэффициенты, автономность ----------

; e = a·d + b (d — выделенная производная), a и b свободны от y; иначе #f
(define (ode-coeff-of d e y x)
  (cond ((equal? e d) (cons 1 0))
        ((or (ode-y-node? e y x) (ode-deriv? e y x)) (cons 0 e))
        ((pair? e)
         (cond ((equal? (car e) '+)
                (let loop ((ts (cdr e)) (a 0) (b 0))
                  (if (null? ts) (cons a b)
                      (let ((r (ode-coeff-of d (car ts) y x)))
                        (if r (loop (cdr ts) (+ a (car r)) (+ b (cdr r))) #f)))))
               ((and (equal? (car e) '-) (= (length e) 2))
                (let ((r (ode-coeff-of d (cadr e) y x)))
                  (if r (cons (- (car r)) (- (cdr r))) #f)))
               ((equal? (car e) '-)
                (let loop ((ts (cdr e)) (a 0) (b 0))
                  (if (null? ts) (cons a b)
                      (let ((r (ode-coeff-of d (car ts) y x)))
                        (if r (loop (cdr ts) (if (null? (cdr ts)) (- a (car r)) (+ a (car r)))
                                    (- b (cdr r)))
                            #f)))))
               ((equal? (car e) '*)
                (let ((with (filter (lambda (z) (ode-contains? d z)) (cdr e)))
                      (without (filter (lambda (z) (not (ode-contains? d z))) (cdr e))))
                  (cond ((null? with) (cons 0 e))
                        ((= (length with) 1)
                         (let ((r (ode-coeff-of d (car with) y x))
                               (c (foldl * 1 without)))
                           (if r (cons (* (car r) c) (* (cdr r) c)) #f)))
                        (else #f))))
               ((and (equal? (car e) '/) (= (length e) 3))
                (if (ode-y-node-any? (caddr e) y x) #f
                    (let ((r (ode-coeff-of d (cadr e) y x)))
                      (if r (cons (/ (car r) (caddr e)) (/ (cdr r) (caddr e))) #f))))
               (else (if (ode-contains? d e) #f (cons 0 e)))))
        (else (cons 0 e))))

(define (ode-deriv-nodes e y x)
  (cond ((ode-deriv? e y x) (list e))
        ((pair? e) (append-map (lambda (z) (ode-deriv-nodes z y x)) e))
        (else '())))

(define (ode-linear? eq yx)
  (let* ((y (car yx)) (x (cadr yx)) (e (ode-normalize eq))
         (nodes (cons (list y x) (ode-deriv-nodes e y x))))
    (every? (lambda (d)
              (let ((r (ode-coeff-of d e y x)))
                (and r (not (ode-y-node-any? (car r) y x)))))
            nodes)))

(define (ode-const-coeff? eq yx)
  (let* ((y (car yx)) (x (cadr yx)) (e (ode-normalize eq))
         (nodes (cons (list y x) (ode-deriv-nodes e y x))))
    (and (ode-linear? eq yx)
         (every? (lambda (d)
                   (let ((r (ode-coeff-of d e y x)))
                     (or (not r) (not (ode-mentions-x? (car r) y x)))))
                 nodes))))

(define (ode-autonomous? eq yx)
  (let ((y (car yx)) (x (cadr yx)))
    (not (ode-mentions-x? (ode-normalize eq) y x))))

; ---------- подстановка решения и сертификат ----------

; вычислить все (diff expr x) снизу вверх (diff в Lisp-режиме: переменная, выражение)
(define (ode-eval-diffs e x)
  (cond ((pair? e)
         (if (and (equal? (car e) 'diff) (= (length e) 3) (equal? (caddr e) x))
             (diff x (ode-eval-diffs (cadr e) x))
             (map (lambda (z) (ode-eval-diffs z x)) e)))
        (else e)))

; структурная замена точного подвыражения (subst трактует (y x) как правило «y ← …», а не как узел)
(define (ode-replace e target value)
  (cond ((equal? e target) value)
        ((pair? e) (map (lambda (z) (ode-replace z target value)) e))
        (else e)))

; подставить (y x) → rhs и вычислить возникшие производные
(define (ode-subst e yx rhs)
  (let ((sub (ode-replace e (list (car yx) (cadr yx)) rhs)))
    (simplify (ode-eval-diffs sub (cadr yx)))))

; ---------- точная сертификация тригонометрических остатков ----------
; Остаток с sin/cos не всегда упрощается до 0 средствами simplify/together/trigsimp.
; Универсальная подстановка Вейерштрасса sin z = 2u/(1+u²), cos z = (1−u²)/(1+u²)
; (свой u для каждого аргумента z) переводит остаток в рациональную функцию от u, где
; simplify/together + factor дают точный ответ. Подстановка тождественна при u = tan(z/2),
; а тождество по x выполняется тогда и только тогда, когда рациональная функция равна 0
; как функция u (область u — открытое множество), поэтому проверка корректна.

(define (ode-w-replace e target value)
  (cond ((equal? e target) value)
        ((pair? e) (map (lambda (z) (ode-w-replace z target value)) e))
        (else e)))

; аргументы sin/cos в e (по одному представителю на каждое выражение)
(define (ode-trig-args e acc)
  (cond ((not (pair? e)) acc)
        ((and (or (equal? (car e) 'sin) (equal? (car e) 'cos)) (= (length e) 2))
         (if (member? (cadr e) acc) acc (ode-trig-args (cadr e) (cons (cadr e) acc))))
        (else (foldl (lambda (a z) (ode-trig-args z a)) acc e))))

(define (ode-fresh-u k)
  (string->symbol (string-append "wu" (to-string k))))

; заменить все sin/cos на рациональные функции от свежих u
(define (ode-weierstrass e args)
  (let loop ((as args) (k 0) (acc e))
    (if (null? as)
        acc
        (let* ((z (car as)) (u (ode-fresh-u k))
               (den (list '+ 1 (list '^ u 2)))
               (su (list '/ (list '* 2 u) den))
               (cu (list '/ (list '- 1 (list '^ u 2)) den)))
          (loop (cdr as) (+ k 1)
                (ode-w-replace (ode-w-replace acc (list 'sin z) su)
                               (list 'cos z) cu))))))

; остаток тождественно 0 (точно), проверка через Вейерштрасса; #t | #f
(define (ode-trig-zero? e)
  (let* ((args (ode-trig-args e '())))
    (and (pair? args)
         (let* ((w (ode-weierstrass e args))
                (z (simplify (together (expand w)))))
           (or (ode-zero? z)
               (ode-zero? (try (factor z) (lambda (err) z))))))))

; число узлов (мера «проще ли стало»)
(define (ode-node-count e)
  (if (pair? e) (+ 1 (foldl (lambda (a z) (+ a (ode-node-count z))) 0 e)) 1))

; ноль: точный 0; float — только малый float (точное ненулевое число — НЕ ноль: замечание ревью, 1/10¹³ проходил как «точно»)
(define (ode-zero? z)
  (let ((z (simplify z)))
    (or (equal? z 0) (equal? z 0.0)
        (and (number? z) (equal? (type-of z) 'float) (< (abs z) 1e-12)))))

; остаток заведомо не ноль: точное ненулевое число или одночлен без сумм (c·f₁·f₂… с точным c ≠ 0 и элементарными
; множителями — тождественно нулём быть не может); тогда численной проверке не верим (иначе 10⁻¹²·cos x проходил как numeric)
(define (ode-surely-nonzero? z)
  (and (not (ode-zero? z))
       (or (and (number? z) (not (equal? (type-of z) 'float)))
           (not (ode-has-head? z '+)))))

; численная проверка остатка в точках (не «точно», а запасной путь)
(define (ode-numeric-zero? res x)
  (let ((pts (list 1/3 2/5 7/11 -3/7 5/4 11/13)))
    (let loop ((ps pts) (n 0))
      (cond ((null? ps) (and (> n 0) #t))
            (else
             (let ((v (eval-num (subst (list x (car ps)) res))))
               (if (number? v)
                   (if (< (abs v) 1e-7) (loop (cdr ps) (+ n 1)) #f)
                   (loop (cdr ps) n))))))))

; √p·√q = √(p·q) для вещественных p, q верно, если они не могут быть оба отрицательными:
; достаточное условие — p+q положительная константа ((1−x)+(1+x)=2). Для (x−1),(x+1) сумма 2x не константа — не сворачиваем.
(define (ode-sqrt-factor f)
  (cond ((and (pair? f) (equal? (car f) 'sqrt) (= (length f) 2)) (cons (cadr f) 1))
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3) (integer? (caddr f))
              (pair? (cadr f)) (equal? (car (cadr f)) 'sqrt) (= (length (cadr f)) 2))
         (cons (cadr (cadr f)) (caddr f)))
        (else #f)))

(define (ode-sqrt-pos-const? p q)
  (let ((s (simplify (list '+ p q))))
    (and (number? s) (> s 0))))

; → (merged . остальные) | #f
(define (ode-sqrt-pair sf rest)
  (if (null? rest)
      #f
      (let ((sg (ode-sqrt-factor (car rest))))
        (if (and sg (= (cdr sg) (cdr sf)) (ode-sqrt-pos-const? (car sf) (car sg)))
            (cons (list '^ (list 'sqrt (simplify (expand (list '* (car sf) (car sg))))) (cdr sf)) (cdr rest))
            (let ((r (ode-sqrt-pair sf (cdr rest))))
              (and r (cons (car r) (cons (car rest) (cdr r)))))))))

(define (ode-merge-sqrt-prod fs)
  (let loop ((rest fs) (acc '()))
    (if (null? rest)
        (reverse acc)
        (let* ((sf (ode-sqrt-factor (car rest)))
               (r (and sf (ode-sqrt-pair sf (cdr rest)))))
          (if r
              (loop (cons (car r) (cdr r)) acc)
              (loop (cdr rest) (cons (car rest) acc)))))))

(define (ode-merge-sqrt e)
  (if (not (pair? e))
      e
      (let ((e2 (map ode-merge-sqrt e)))
        (if (equal? (car e2) '*)
            (let ((fs (ode-merge-sqrt-prod (cdr e2))))
              (if (= (length fs) 1) (car fs) (cons '* fs)))
            e2))))

; (dsolve-check уравнение решение (y x)) → #t (точно) | 'numeric | #f
(define (dsolve-check eq sol yx)
  (let* ((y (car yx)) (x (cadr yx))
         (rhs (if (and (pair? sol) (equal? (car sol) '=)) (caddr sol) sol))
         (res (ode-subst (ode-normalize eq) yx rhs))
         (z (simplify (together res))))
    (cond ((ode-zero? z) #t)
          ((ode-zero? (simplify (together (ode-merge-sqrt z)))) #t)
          ((ode-surely-nonzero? z) #f)
          ((ode-trig-zero? z) #t)
          ((ode-numeric-zero? res x) 'numeric)
          (else #f))))

; ---------- квадратуры y⁽ⁿ⁾ = f(x) ----------

(define (ode-has-head? e h)
  (or (equal? e h) (and (pair? e) (any? (lambda (z) (ode-has-head? z h)) e))))

; n-кратное интегрирование; константы C1 … Cn (после k-го шага — Ck).
; Невычисленный интеграл — не ошибка: ответ-квадратура, dsolve-check дифференцирует его формально.
(define (ode-integrate-n f x n)
  (let loop ((k n) (g f) (cs '()))
    (if (= k 0)
        (cons g (reverse cs))
        (let* ((ig (integrate g x))
               (c (string->symbol (string-append "C" (to-string k)))))
          (loop (- k 1) (simplify (list '+ ig c)) (cons c cs))))))

; квадратура y⁽ⁿ⁾ = f(x); #f — не этот случай
(define (ode-quadrature eq yx n y x)
  (let* ((d (ode-nth-deriv y x n))
         (r (ode-coeff-of d (ode-normalize eq) y x)))
    (if (not r)
        #f
        (let ((a (car r)) (b (cdr r)))
          (if (or (not (number? a)) (ode-y-node-any? b y x) (ode-mentions-sym? b y) (ode-zero? a))
              #f
              (let* ((rhs (simplify (list '/ (list '- b) a)))
                     (ints (ode-integrate-n rhs x n))
                     (sol (list '= (list y x) (car ints)))
                     (chk (dsolve-check eq sol yx))
                     (quad (ode-has-head? (car ints) 'integrate)))
                (if chk
                    (begin
                      (if quad
                          (record-condition (list 'ode-quadrature rhs)
                                            "dsolve: интеграл не выражен элементарно — ответ квадратурой"))
                      (ode-solution (cond (quad 'quadrature)
                                          ((null? (cdr ints)) 'particular)
                                          (else 'general))
                                    (list sol) (cdr ints) '() 'ok 'quadrature chk))
                    (error "dsolve: решение не прошло проверку"))))))))

; крючок ODE.1: first-order.lisp выставляет флаг и определяет fo-solve
(define *ode-first-order-loaded* #f)
; крючок ODE.2: exact.lisp выставляет флаг и определяет ex-solve
(define *ode-exact-loaded* #f)
; крючок ODE.3: linear.lisp выставляет флаг и определяет lo-solve
(define *ode-linear-loaded* #f)
; крючок ODE.4a: euler.lisp выставляет флаг и определяет eu-solve
(define *ode-euler-loaded* #f)
; крючок ODE.5b: reduction.lisp выставляет флаг и определяет reduce-order/ode-drop-y/ode-autonomous
(define *ode-reduction-loaded* #f)
; крючок ODE.4a: cauchy.lisp выставляет флаг и определяет ca-solve/ca-condition
(define *ode-cauchy-loaded* #f)
; крючок ODE.7: series.lisp выставляет флаг и определяет dsolve-series/se-dsolve-hook
(define *ode-series-loaded* #f)
(define *ode-kovacic-loaded* #f)
; крючок ODE.9: specfun-ode.lisp определяет sfo-augment (ответ через головы SFn.2)
(define *ode-sf-loaded* #f)


; входной язык может передать y(x) как голый символ y в сумме (y'' + y = 0):
; раз y — имя неизвестной функции, голый y означает (y x).
; Заменяем только «свободные» вхождения: не в узле (y x) и не как переменная diff.
(define (ode-bare-y->call e y x)
  (cond ((equal? e y) (list y x))
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3)
              (equal? (caddr e) x) (ode-diff-depth e y x)) e)
        ((and (pair? e) (equal? (length e) 2) (equal? (car e) y)) e)
        ((pair? e) (map (lambda (z) (ode-bare-y->call z y x)) e))
        (else e)))

; (dsolve eq yx [условия]): без условий — общее решение; с условиями — задача Коши.
; (dsolve eq yx :method 'laplace [условия]) — метод Лапласа (lib/laplace.lisp, laplace-dsolve); без ключа Лаплас —
; первый путь, если в уравнении есть heaviside/dirac (TR.2, замечание ревью).
(define (dsolve eq yx &rest args)
  (let* ((laplace? (and (pair? args) (equal? (car args) :method) (pair? (cdr args))
                        (member? (cadr args) '(laplace (quote laplace)))))
         (conds (if (and (pair? args) (equal? (car args) :method)) (if (pair? (cdr args)) (cddr args) '()) args))
         (eq (if (and (pair? yx) (= (length yx) 2) (symbol? (car yx))) (ode-bare-y->call eq (car yx) (cadr yx)) eq)))
    (let ((res (if laplace?
                   (ode-laplace eq yx conds)
                   ; θ/δ в уравнении: сначала Лаплас (вариация постоянных даёт невычисленные интегралы от θ)
                   (let ((rl (if (ode-mentions-impulse? eq) (ode-laplace eq yx conds) #f)))
                     (if (and rl (equal? (ode-status rl) 'ok))
                         rl
                         (ode-fold-result (ode-dsolve-main eq yx conds) eq yx))))))
      (ode-check-step eq yx res))))

(define (ode-mentions-impulse? e)
  (cond ((pair? e) (or (member? (car e) '(heaviside dirac)) (any? ode-mentions-impulse? e)))
        (else #f)))

; метод Лапласа: laplace-dsolve из lib/laplace.lisp (загружается после); нет — unknown
(define (ode-laplace eq yx conds)
  (try (laplace-dsolve eq yx conds)
       (lambda (e) (ode-solution 'unknown '() '() '() "метод Лапласа недоступен или не применим" 'laplace 'none))))

; ---------- косметика ответа: exp(k·log u) → u^k ----------

; экспонента логарифма: exp(log u) → u, exp(k·log u) → u^k (k — число);
; тождество при u > 0 — отмечаем condition
(define (ode-fold-exp e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'exp) (= (length e) 2))
         (let ((u (cadr e)))
           (cond ((and (pair? u) (equal? (car u) 'log) (= (length u) 2)) (cadr u))
                 ((and (pair? u) (equal? (car u) '*) (= (length u) 3)
                       (number? (cadr u))
                       (pair? (caddr u)) (equal? (car (caddr u)) 'log)
                       (= (length (caddr u)) 2))
                  (simplify (list '^ (cadr (caddr u)) (cadr u))))
                 (else (list 'exp (ode-fold-exp u))))))
        ((equal? (car e) 'diff) e)
        (else (map ode-fold-exp e))))

; применить свёртку к решениям объекта; новая форма принимается, только если сертификат сохраняется
(define (ode-fold-result r eq yx)
  (if (not (and (pair? r) (equal? (car r) 'ode-solution)))
      r
      (let* ((sols (ode-field r :solutions))
             (new (map (lambda (s)
                         (if (and (pair? s) (equal? (car s) '=))
                             (list '= (cadr s) (simplify (ode-fold-exp (caddr s))))
                             (simplify (ode-fold-exp s))))
                       sols)))
        (if (or (equal? new sols)
                (any? (lambda (s) (not (dsolve-check eq s yx))) new))
            r
            (begin
              (record-condition '(ode-exp-log) "exp(k·log u) → u^k (тождественно при u > 0)")
              (ode-solution (ode-field r :type) new (ode-field r :constants)
                            (ode-field r :singular) (ode-field r :status)
                            (ode-field r :method) (ode-field r :check)))))))

(define (ode-dsolve-main eq yx conds)
  (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))))
      (error "dsolve: второй аргумент — (y x)")
      (let* ((y (car yx)) (x (cadr yx))
             (eq (ode-bare-y->call eq y x))
             (n (ode-order eq y x)))
        (if (< n 1)
            (ode-solution 'general '() '() '() 'unknown 'none 'none)
            (begin
            (ode-classify-step eq yx n)
            (let ((r (cond ((and (= n 1) *ode-first-order-loaded*) (fo-solve eq yx))
                           ((and (> n 1) *ode-linear-loaded*) (lo-solve eq yx))
                           (else #f))))
              (let ((r (or r
                          (and *ode-exact-loaded* (= n 1) (ex-solve eq yx))
                          (and *ode-euler-loaded* (eu-solve eq yx))
                          (and *ode-reduction-loaded* (= n 2) (ode-drop-y eq yx))
                          (and *ode-reduction-loaded* (= n 2) (ode-autonomous eq yx))
                          (ode-quadrature eq yx n y x)
                          ; задача Коши: ряд пробуется до отказа Ковачича (ответ всё равно проверяемый)
                          (and (pair? conds) *ode-series-loaded* (se-dsolve-hook eq yx conds))
                          (and *ode-kovacic-loaded* (= n 2) (kv-solve eq yx))
                          (and *ode-series-loaded* (se-dsolve-hook eq yx conds))
                          (begin
                            (ode-refuse-step eq yx n)
                            (ode-solution 'general '() '() '() 'unknown 'none 'none)))))
                (let ((r (if (and *ode-sf-loaded* (= n 2)) (sfo-augment r eq yx) r)))
                (if (or (null? conds)
                        ; ряд уже построен по условиям Коши (se-init) — не применять их повторно
                        (and (member? (ode-field r :method) '(series frobenius))
                             (equal? (ode-field r :type) 'particular)
                             (null? (ode-field r :constants))))
                    r
                    ; задача Коши: разобрать условия и применить к r
                    (let ((cs (map (lambda (c)
                                     (if *ode-cauchy-loaded*
                                         (ca-condition c y x)
                                         (error "dsolve: условия загружены без lib/ode/cauchy.lisp")))
                                   conds)))
                      (if (any? (lambda (c) (not c)) cs)
                          (ode-solution 'unknown '() '() '()
                                        "не распознанное условие задачи Коши" 'cauchy 'none)
                          (ca-solve eq yx cs r))))))))))))
