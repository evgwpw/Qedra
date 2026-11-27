; core.lisp — каркас уравнений в частных производных (шаг PDE.0)
; Неизвестная — (u x t), (u x y z); частные производные — штатный вложенный (diff (diff (u x t) x) x).
; Входной язык пишет u_t, u_xx, u_xt (производные только объявленной неизвестной): pde-diff-form переводит их в diff.
; Условия: (= (at (u x t) (= t 0)) (f x)) — голова at из ОДУ, (= (u x 0) (f x)) — запись точкой,
; (bounded (u x t) (= x 0)) — ограниченность. Область: ((x 0 L) (t 0 inf)).
; Результат pdsolve — (pde-solution :type … :solutions … :arbitrary-functions … :eigen … :term … :coefficients …
; :constants … :status … :method … :check …). В PDE.0 методов решения нет: диспетчер классифицирует и отвечает
; status unknown с перечнем подходящих методов; доказуемая несовместность условий — status inconsistent.
; Главное в PDE.0 — pdsolve-check: проверка чужого ответа (#t | numeric | #f | unknown).
(module pde
  (export pdsolve pdsolve-check pdsolve-check-detail pde-classify pde-class-ref pde-solution pde-solutions pde-status pde-term
          pde-field pde-subst pde-diff-form))

; ---------- объект результата ----------

(define (pde-solution type solutions arbitrary eigen term coefficients constants status method check &rest extras)
  (append (list 'pde-solution :type type :solutions solutions :arbitrary-functions arbitrary
                :eigen eigen :term term :coefficients coefficients :constants constants
                :status status :method method :check check)
          extras))

(define (pde-field r key)
  (let loop ((xs (cdr r)))
    (cond ((null? xs) #f)
          ((equal? (car xs) key) (cadr xs))
          (else (loop (cddr xs))))))

(define (pde-solutions r) (pde-field r :solutions))
(define (pde-status r) (pde-field r :status))
(define (pde-term r) (pde-field r :term))

; поле результата классификации (pde-class …)
(define (pde-class-ref c key) (pde-field c key))

; ---------- общие мелочи ----------

(define (pde-quiet thunk) (if (step-log-enabled?) (call-quietly thunk) (thunk)))

(define (pde-pos x l)
  (let loop ((l l) (i 0))
    (cond ((null? l) #f)
          ((equal? (car l) x) i)
          (else (loop (cdr l) (+ i 1))))))

(define (pde-has? e s)
  (or (equal? e s) (and (pair? e) (any? (lambda (z) (pde-has? z s)) e))))

(define (pde-replace e target value)
  (cond ((equal? e target) value)
        ((pair? e) (map (lambda (z) (pde-replace z target value)) e))
        (else e)))

(define (pde-eqn? e) (and (pair? e) (equal? (car e) '=) (= (length e) 3)))

(define (pde-zero? z) (ode::ode-zero? z))

; вектор входного языка [x, 0, L]: готовый тензор или сырая форма (m-vector x 0 L)
(define (pde-as-list a)
  (cond ((tensor? a) (tensor->list a))
        ((and (pair? a) (equal? (car a) 'm-vector)) (cdr a))
        (else a)))

(define (pde-uvars-ok? uv)
  (and (pair? uv) (symbol? (car uv)) (>= (length uv) 3) (every? symbol? (cdr uv))))

(define (pde-union a b)
  (foldl (lambda (acc x) (if (member? x acc) acc (append acc (list x)))) a b))

; ---------- нотация u_t, u_xx → diff ----------

; строка индексов → список переменных дифференцирования (имена переменных могут быть длиннее одной буквы)
(define (pde-split-suffix s names)
  (if (equal? s "")
      '()
      (let loop ((ns names))
        (cond ((null? ns) #f)
              ((and (<= (string-length (car (car ns))) (string-length s))
                    (equal? (substring s 0 (string-length (car (car ns)))) (car (car ns))))
               (let ((r (pde-split-suffix (substring s (string-length (car (car ns))) (string-length s)) names)))
                 (if r (cons (cdr (car ns)) r) (loop (cdr ns)))))
              (else (loop (cdr ns)))))))

; u_xx → (x x); не индексная запись → #f
(define (pde-index-symbol sym u vars)
  (if (not (symbol? sym))
      #f
      (let* ((s (symbol->string sym)) (p (string-append (symbol->string u) "_")) (lp (string-length p)))
        (if (and (> (string-length s) lp) (equal? (substring s 0 lp) p))
            (pde-split-suffix (substring s lp (string-length s))
                              (map (lambda (v) (cons (symbol->string v) v)) vars))
            #f))))

(define (pde-diff-chain u vars ds)
  (foldl (lambda (acc v) (list 'diff acc v)) (cons u vars) ds))

; индексные символы u_xx внутри выражения → вложенный diff; вызов u_t(x, 0) остаётся (его разбирает разбор условий)
(define (pde-diff-form e u vars)
  (cond ((symbol? e)
         (let ((ds (pde-index-symbol e u vars)))
           (if ds (pde-diff-chain u vars ds) e)))
        ((pair? e)
         (if (and (symbol? (car e)) (pde-index-symbol (car e) u vars))
             (cons (car e) (map (lambda (z) (pde-diff-form z u vars)) (cdr e)))
             (map (lambda (z) (pde-diff-form z u vars)) e)))
        (else e)))

; голый u в сумме (язык пишет k²·u как символ) → (u x t); голова вызова не трогается
(define (pde-bare-u e u vars)
  (cond ((equal? e u) (cons u vars))
        ((and (pair? e) (equal? (car e) u)) e)
        ((pair? e) (cons (car e) (map (lambda (z) (pde-bare-u z u vars)) (cdr e))))
        (else e)))

(define (pde-prep e uv)
  (pde-bare-u (pde-diff-form e (car uv) (cdr uv)) (car uv) (cdr uv)))

; уравнение → левая часть (lhs − rhs), раскрытая
(define (pde-normalize eq)
  (if (pde-eqn? eq)
      (simplify (expand (list '- (cadr eq) (caddr eq))))
      (simplify (expand eq))))

; ---------- узлы-производные ----------

; (diff (diff (u x t) x) x) → мультииндекс (2 0); (u x t) → (0 0); иначе #f
(define (pde-node-index e u vars)
  (cond ((equal? e (cons u vars)) (map (lambda (v) 0) vars))
        ((and (pair? e) (equal? (car e) 'diff) (= (length e) 3) (pde-pos (caddr e) vars))
         (let ((k (pde-node-index (cadr e) u vars)))
           (and k (let ((i (pde-pos (caddr e) vars)))
                    (map2 (lambda (c j) (if (= j i) (+ c 1) c)) k (range (length vars)))))))
        (else #f)))

(define (pde-nodes e u vars acc)
  (cond ((and (pair? e) (pde-node-index e u vars))
         (if (member? e acc) acc (append acc (list e))))
        ((pair? e) (foldl (lambda (a z) (pde-nodes z u vars a)) acc e))
        (else acc)))

(define (pde-sub-nodes e nodes syms)
  (let ((i (and (pair? e) (pde-pos e nodes))))
    (cond (i (nth syms i))
          ((pair? e) (map (lambda (z) (pde-sub-nodes z nodes syms)) e))
          (else e))))

; обратно: символы узлов → узлы
(define (pde-unsub e nodes syms)
  (foldl (lambda (acc p) (pde-replace acc (car p) (cdr p))) e (map2 cons syms nodes)))

(define (pde-free-of? e syms)
  (not (any? (lambda (s) (pde-has? e s)) syms)))

(define (pde-fresh-syms n)
  (map (lambda (i) (string->symbol (string-append "pdq" (to-string i)))) (range n)))

; ---------- знак выражения ----------

; чётная степень, произведение таких с числами: 'nonnegative | 'nonpositive | #f
(define (pde-sq-sign d)
  (cond ((and (pair? d) (equal? (car d) '^) (integer? (caddr d)) (= (remainder (caddr d) 2) 0)) 'nonnegative)
        ((and (pair? d) (equal? (car d) '*))
         (let loop ((zs (cdr d)) (s 'nonnegative))
           (cond ((null? zs) s)
                 ((and (number? (car zs)) (> (car zs) 0)) (loop (cdr zs) s))
                 ((and (number? (car zs)) (< (car zs) 0))
                  (loop (cdr zs) (if (equal? s 'nonnegative) 'nonpositive 'nonnegative)))
                 ((equal? (pde-sq-sign (car zs)) 'nonnegative) (loop (cdr zs) s))
                 (else #f))))
        (else #f)))

; positive | negative | zero | unknown; «≥ 0 по квадрату» принимается как положительное с условием «≠ 0»
(define (pde-sign d)
  (cond ((number? d) (cond ((> d 0) 'positive) ((< d 0) 'negative) (else 'zero)))
        (else
         (let ((s (try (sign-of d) (lambda (e) 'unknown))))
           (cond ((member? s '(positive negative zero)) s)
                 ((equal? (pde-sq-sign d) 'nonnegative)
                  (record-condition (list 'pde-nonzero d) "pde: тип определён при условии, что коэффициент ≠ 0")
                  'positive)
                 ((equal? (pde-sq-sign d) 'nonpositive)
                  (record-condition (list 'pde-nonzero d) "pde: тип определён при условии, что коэффициент ≠ 0")
                  'negative)
                 ((equal? s 'nonnegative)
                  (record-condition (list 'pde-nonzero d) "pde: тип определён при условии, что коэффициент ≠ 0")
                  'positive)
                 ((equal? s 'nonpositive)
                  (record-condition (list 'pde-nonzero d) "pde: тип определён при условии, что коэффициент ≠ 0")
                  'negative)
                 (else 'unknown))))))

; ---------- таблица коэффициентов ----------

(define (pde-unit-idx n ps)
  (map (lambda (j) (foldl (lambda (c p) (if (= p j) (+ c 1) c)) 0 ps)) (range n)))

(define (pde-coef-at table idx)
  (let ((p (assoc idx table))) (if p (cdr p) 0)))

(define (pde-c0 table n) (pde-coef-at table (pde-unit-idx n '())))
(define (pde-c1 table n i) (pde-coef-at table (pde-unit-idx n (list i))))
(define (pde-c2 table n i j) (pde-coef-at table (pde-unit-idx n (list i j))))

(define (pde-pairs n)
  (append-map (lambda (i) (map (lambda (j) (cons i j)) (drop (range n) (+ i 1)))) (range n)))

(define (pde-nz? c) (not (pde-zero? c)))

(define (pde-all-equal? l)
  (or (null? l)
      (every? (lambda (z) (pde-zero? (simplify (list '- z (car l))))) (cdr l))))

; ---------- образцы (линейные уравнения с постоянными коэффициентами) ----------

; (имя :ключ значение …) или (none)
(define (pde-pattern-2 table n b vars)
  (let* ((idx (range n))
         (d (map (lambda (i) (pde-c2 table n i i)) idx))
         (e (map (lambda (i) (pde-c1 table n i)) idx))
         (f (pde-c0 table n))
         (hom (pde-zero? b))
         (s2 (filter (lambda (i) (pde-nz? (nth d i))) idx))
         (s1 (filter (lambda (i) (pde-nz? (nth e i))) idx)))
    (cond
      ; смешанные производные — образца нет (канонический вид — PDE.3)
      ((any? (lambda (p) (pde-nz? (pde-c2 table n (car p) (cdr p)))) (pde-pairs n)) (list 'none))
      ; Δu + λu = F: все d_i равны и не нулевые, первых производных нет
      ((and (>= n 2) (= (length s2) n) (pde-all-equal? d) (null? s1))
       (let ((k (car d)))
         (cond ((pde-nz? f) (list 'helmholtz :lambda (simplify (list '/ f k)) :homogeneous hom))
               (hom (list 'laplace))
               (else (list 'poisson :rhs (simplify (list '/ (list '- b) k)))))))
      ; e_t u_t + k Δ_x u = 0: одна первая производная по t, остальные d равны
      ((and (>= n 2) (= (length s1) 1) (= (length s2) (- n 1)) (not (member? (car s1) s2))
            (pde-all-equal? (map (lambda (i) (nth d i)) s2)))
       (let ((k (nth d (car s2))) (et (nth e (car s1))))
         (if (pde-zero? f)
             (list 'heat :time (nth vars (car s1)) :coef (simplify (list '/ (list '- k) et)) :homogeneous hom)
             (list 'reaction-diffusion :time (nth vars (car s1)) :homogeneous hom))))
      ; волновой тип: d_t противоположного знака, остальные равны
      ((and (>= n 2) (= (length s2) n))
       (let ((wt (pde-wave-time d idx vars)))
         (if (not wt)
             (list 'none)
             (let* ((ti (car wt)) (k (cdr wt)) (dt (nth d ti))
                    (c2 (simplify (list '/ (list '- k) dt))))
               (cond ((and (null? s1) (pde-zero? f))
                      (list 'wave :time (nth vars ti) :speed2 c2 :homogeneous hom))
                     ((and (null? s1))
                      (list 'klein-gordon :time (nth vars ti) :speed2 c2 :homogeneous hom))
                     ((and (= (length s1) 1) (equal? (car s1) ti))
                      (list 'telegraph :time (nth vars ti) :speed2 c2 :homogeneous hom))
                     (else (list 'none)))))))
      (else (list 'none)))))

; индекс времени и общий коэффициент остальных для волнового типа: (ti . k) или #f
(define (pde-wave-time d idx vars)
  (let* ((order (let ((tn (pde-pos 't vars)))
                  (if tn (cons tn (filter (lambda (i) (not (= i tn))) idx)) (reverse idx)))))
    (let loop ((cands order))
      (cond ((null? cands) #f)
            (else
             (let* ((ti (car cands))
                    (others (filter (lambda (i) (not (= i ti))) idx))
                    (ds (map (lambda (i) (nth d i)) others)))
               (if (and (pde-all-equal? ds)
                        (equal? (pde-sign (simplify (list '/ (nth d ti) (car ds)))) 'negative))
                   (cons ti (car ds))
                   (loop (cdr cands)))))))))

(define (pde-biharmonic? table n)
  (let ((k (pde-coef-at table (pde-unit-idx n '(0 0 0 0)))))
    (and (>= n 2) (pde-nz? k)
         (every? (lambda (p)
                   (let ((idx (car p)) (c (cdr p)))
                     (or (pde-zero? c)
                         (and (= (apply + idx) 4)
                              (or (and (= (apply max idx) 4) (pde-zero? (simplify (list '- c k))))
                                  (and (= (apply max idx) 2) (= (length (filter (lambda (z) (= z 2)) idx)) 2)
                                       (pde-zero? (simplify (list '- c (list '* 2 k))))))))))
                 table))))

(define (pde-pattern-1 table n b vars)
  (let* ((idx (range n))
         (e (map (lambda (i) (pde-c1 table n i)) idx))
         (f (pde-c0 table n))
         (s1 (filter (lambda (i) (pde-nz? (nth e i))) idx)))
    (if (and (= n 2) (= (length s1) 2) (pde-zero? f) (pde-zero? b))
        (let* ((ti (if (equal? (nth vars 1) 't) 1 0)) (xi (- 1 ti))
               (speed (simplify (list '/ (nth e xi) (nth e ti)))))
          (list 'transport :time (nth vars ti) :speed speed))
        (list 'none))))

; квазилинейное 1-го порядка: u_t + u·u_x = 0 (Бюргерс) — в любом порядке переменных
(define (pde-burgers table n vars uv)
  (if (not (= n 2))
      #f
      (let* ((e0 (pde-c1 table n 0)) (e1 (pde-c1 table n 1)))
        (cond ((and (pde-nz? e1) (pde-nz? e0)
                    (equal? (simplify (list '/ e0 e1)) uv)) (list 'burgers :time (nth vars 1)))
              ((and (pde-nz? e0) (pde-nz? e1)
                    (equal? (simplify (list '/ e1 e0)) uv)) (list 'burgers :time (nth vars 0)))
              (else #f)))))

; ---------- система координат ----------

(define (pde-infer-coords vars)
  (cond ((and (= (length vars) 3) (member? (car vars) '(r rho)) (member? (cadr vars) '(phi θ φ theta))
              (equal? (caddr vars) 'z)) 'cylindrical)
        ((and (= (length vars) 3) (member? (car vars) '(r rho)) (member? (cadr vars) '(theta θ))
              (member? (caddr vars) '(phi φ))) 'spherical)
        ((and (= (length vars) 2) (member? (car vars) '(r rho)) (member? (cadr vars) '(phi θ φ theta))) 'polar)
        (else 'cartesian)))

; ---------- разбор аргументов pdsolve/pdsolve-check: условия, область, ключи ----------

(define (pde-keyword? a) (and (symbol? a) (member? a '(:domain :coords :method :terms))))

(define (pde-domain-entry? a vars)
  (let ((l (pde-as-list a)))
    (and (list? l) (= (length l) 3) (symbol? (car l)) (member? (car l) vars) (not (equal? (car l) '=)))))

; → (условия область ключи): область — список (v lo hi)
(define (pde-split-args args vars)
  (let loop ((as args) (conds '()) (dom '()) (opts '()))
    (cond ((null? as) (list (reverse conds) dom opts))
          ((and (pde-keyword? (car as)) (pair? (cdr as)))
           (if (equal? (car as) :domain)
               (loop (cddr as) conds (append dom (pde-domain-list (cadr as) vars)) opts)
               (loop (cddr as) conds dom (append opts (list (car as) (cadr as))))))
          ((pde-domain-entry? (car as) vars)
           (loop (cdr as) conds (append dom (list (pde-as-list (car as)))) opts))
          (else (loop (cdr as) (cons (car as) conds) dom opts)))))

(define (pde-domain-list v vars)
  (let ((l (pde-as-list v)))
    (cond ((null? l) '())
          ((pde-domain-entry? l vars) (list l))
          (else (map pde-as-list l)))))

; ---------- условия ----------

; (at (at E (= v a)) (= w b)) → (E (v a) (w b))
(define (pde-peel-at e)
  (if (and (pair? e) (equal? (car e) 'at) (= (length e) 3) (pde-eqn? (caddr e)))
      (let ((inner (pde-peel-at (cadr e))))
        (cons (car inner) (append (cdr inner) (list (list (cadr (caddr e)) (caddr (caddr e)))))))
      (cons e '())))

; точка в вызове u(0, t): позиции, где аргумент не равен переменной
(define (pde-point-bindings args vars)
  (let loop ((as args) (vs vars) (acc '()))
    (cond ((null? as) (reverse acc))
          ((equal? (car as) (car vs)) (loop (cdr as) (cdr vs) acc))
          (else (loop (cdr as) (cdr vs) (cons (list (car vs) (car as)) acc))))))

(define (pde-st-add! st bs)
  (cond ((null? bs) #t)
        ((equal? (vref st 0) 'none) (vset! st 0 bs))
        ((equal? (vref st 0) bs) #t)
        (else (vset! st 1 #t))))

; вызовы u(a, b) и u_t(a, b) → узлы (u x t) / (diff (u x t) t); найденные привязки точки — в st
(define (pde-lift e uv st)
  (let* ((u (car uv)) (vars (cdr uv)) (n (length vars))
         (ds (and (pair? e) (symbol? (car e)) (= (length (cdr e)) n)
                  (if (equal? (car e) u) '() (pde-index-symbol (car e) u vars)))))
    (cond (ds
           (begin (pde-st-add! st (pde-point-bindings (cdr e) vars))
                  (pde-diff-chain u vars ds)))
          ((pair? e) (map (lambda (z) (pde-lift z uv st)) e))
          (else e))))

; левая часть условия → (выражение . привязки) или #f (это не условие в точке)
(define (pde-cond-lhs lhs uv)
  (let* ((p (pde-peel-at lhs)) (st (vector 'none #f))
         (ex (pde-lift (car p) uv st))
         (bs (append (cdr p) (if (equal? (vref st 0) 'none) '() (vref st 0)))))
    (if (or (vref st 1) (null? bs)) #f (cons ex bs))))

; условие → (eq выражение привязки правая-часть) | (bounded выражение привязки) | #f
(define (pde-parse-cond c uv)
  (cond ((and (pair? c) (equal? (car c) 'bounded) (= (length c) 3))
         (let* ((l (pde-cond-lhs (cadr c) uv))
                (b (caddr c))
                (bs (cond ((pde-eqn? b) (list (list (cadr b) (caddr b))))
                          ((and (list? b) (every? pde-eqn? b)) (map (lambda (z) (list (cadr z) (caddr z))) b))
                          (else #f))))
           (if bs
               (list 'bounded (if l (car l) (cadr c)) (append (if l (cdr l) '()) bs))
               #f)))
        ((pde-eqn? c)
         (let ((l (pde-cond-lhs (cadr c) uv)))
           (and l (list 'eq (car l) (cdr l) (caddr c)))))
        (else #f)))

(define (pde-parse-conds conds uv)
  (map (lambda (c) (pde-parse-cond (pde-diff-form c (car uv) (cdr uv)) uv)) conds))

; ---------- совместность условий ----------

(define (pde-subset-bindings? a b)
  (every? (lambda (p) (member? p b)) a))

; доказуемая несовместность: два условия на одно выражение в совпадающих (или вложенных) точках с разными числами
(define (pde-inconsistent-pair conds)
  (let ((eqs (filter (lambda (c) (and c (equal? (car c) 'eq))) conds)))
    (let loop ((as eqs))
      (if (null? as)
          #f
          (let ((hit (let inner ((bs eqs))
                       (cond ((null? bs) #f)
                             ((and (not (equal? (car as) (car bs)))
                                   (equal? (cadr (car as)) (cadr (car bs)))
                                   (pde-subset-bindings? (caddr (car as)) (caddr (car bs)))
                                   (let* ((rest (filter (lambda (p) (not (member? p (caddr (car as))))) (caddr (car bs))))
                                          (ra (simplify (subst (map (lambda (p) (list (car p) (cadr p))) rest)
                                                               (cadddr (car as)))))
                                          (dd (simplify (list '- ra (cadddr (car bs))))))
                                     (and (number? dd) (not (pde-zero? dd)))))
                              (list (car as) (car bs)))
                             (else (inner (cdr bs)))))))
            (or hit (loop (cdr as))))))))

; ---------- классификация ----------

(define (pde-type-name t)
  (cond ((equal? t 'elliptic) "эллиптическое")
        ((equal? t 'parabolic) "параболическое")
        ((equal? t 'hyperbolic) "гиперболическое")
        (else "не определён")))

(define (pde-pattern-name p)
  (cond ((equal? p 'heat) "теплопроводность")
        ((equal? p 'wave) "волновое")
        ((equal? p 'laplace) "Лаплас")
        ((equal? p 'poisson) "Пуассон")
        ((equal? p 'helmholtz) "Гельмгольц")
        ((equal? p 'biharmonic) "бигармоническое")
        ((equal? p 'transport) "перенос")
        ((equal? p 'burgers) "Бюргерс")
        ((equal? p 'telegraph) "телеграфное")
        ((equal? p 'klein-gordon) "Клейна–Гордона")
        ((equal? p 'reaction-diffusion) "реакция–диффузия")
        (else "")))

; тип по главной части: (тип . дискриминант)
(define (pde-second-order-type table n)
  (let* ((idx (range n))
         (diag (map (lambda (i) (pde-c2 table n i i)) idx))
         (mixed (map (lambda (p) (simplify (list '/ (pde-c2 table n (car p) (cdr p)) 2))) (pde-pairs n))))
    (if (= n 2)
        (let* ((a (nth diag 0)) (c (nth diag 1)) (b (car mixed))
               (disc (simplify (expand (list '- (list '^ b 2) (list '* a c)))))
               (s (pde-sign disc)))
          (cons (cond ((equal? s 'positive) 'hyperbolic)
                      ((equal? s 'negative) 'elliptic)
                      ((equal? s 'zero) 'parabolic)
                      (else 'unknown))
                disc))
        (if (every? pde-zero? mixed)
            (let* ((ss (map pde-sign diag))
                   (p (length (filter (lambda (s) (equal? s 'positive)) ss)))
                   (q (length (filter (lambda (s) (equal? s 'negative)) ss)))
                   (z (length (filter (lambda (s) (equal? s 'zero)) ss))))
              (cons (cond ((member? 'unknown ss) 'unknown)
                          ((and (= z 0) (or (= p 0) (= q 0))) 'elliptic)
                          ((and (= z 0) (or (= p 1) (= q 1))) 'hyperbolic)
                          ((and (> z 0) (or (= p 0) (= q 0))) 'parabolic)
                          (else 'unknown))
                    'diagonal))
            (cons 'unknown 'mixed)))))

(define (pde-conds-homogeneous pc)
  (cond ((null? pc) 'none)
        ((any? (lambda (c) (not c)) pc) 'unknown)
        ((every? (lambda (c) (or (equal? (car c) 'bounded) (pde-zero? (cadddr c)))) pc) #t)
        (else #f)))

(define (pde-class-comment cls)
  (let ((lin (pde-field cls :linear)) (qs (pde-field cls :quasilinear)) (pat (pde-field cls :pattern)))
    (string-append
     "независимых переменных: " (to-string (length (pde-field cls :vars)))
     "; порядок " (to-string (pde-field cls :order))
     (cond (lin "; линейное") (qs "; квазилинейное") (else "; нелинейное"))
     (if lin
         (string-append (if (pde-field cls :const-coeff) "; постоянные коэффициенты" "; переменные коэффициенты")
                        (if (pde-field cls :homogeneous) "; однородное" "; неоднородное"))
         "")
     (if (member? (pde-field cls :type) '(elliptic parabolic hyperbolic))
         (string-append "; тип: " (pde-type-name (pde-field cls :type)))
         "")
     (if (equal? pat 'none) "" (string-append "; образец: " (pde-pattern-name pat))))))

; (pde-classify eq (u x t) [условия] [:coords c]) → (pde-class :vars … :order … :linear … :type … :pattern …)
(define (pde-classify eq uv &rest args)
  (if (not (pde-uvars-ok? uv))
      (error "pde-classify: второй аргумент — (u x t) с двумя и более переменными")
      (let* ((u (car uv)) (vars (cdr uv)) (n (length vars))
             (sp (pde-split-args args vars))
             (opts (nth sp 2))
             (coords (pde-opt opts :coords (pde-infer-coords vars)))
             (pc (pde-parse-conds (car sp) uv))
             (N (pde-normalize (pde-prep eq uv)))
             (nodes (pde-nodes N u vars '()))
             (syms (pde-fresh-syms (length nodes)))
             (Ns (pde-sub-nodes N nodes syms))
             (table (map2 (lambda (nd s) (cons (pde-node-index nd u vars) (simplify (diff s Ns)))) nodes syms))
             (ord (foldl (lambda (a p) (max a (apply + (car p)))) 0 table))
             (linear (and (pair? nodes) (every? (lambda (p) (pde-free-of? (cdr p) syms)) table)))
             (hi (filter (lambda (p) (= (apply + (car p)) ord)) table))
             (hsyms (map (lambda (p) (nth syms (pde-pos p table))) hi))
             (quasi (and (pair? nodes) (every? (lambda (p) (pde-free-of? (cdr p) hsyms)) hi)))
             (b (if (null? nodes) Ns (simplify (subst (map (lambda (s) (list s 0)) syms) Ns))))
             (hom (and linear (pde-zero? b)))
             (constc (and linear (every? (lambda (p) (pde-free-of? (cdr p) vars)) table)))
             (ty (cond ((not (and quasi (pair? nodes))) (cons 'none #f))
                       ((= ord 2) (pde-second-order-type table n))
                       (else (cons 'none #f))))
             (pat (cond ((not (and linear constc))
                         (or (and quasi (= ord 1)
                                  (pde-burgers (map (lambda (p) (cons (car p) (pde-unsub (cdr p) nodes syms))) table)
                                               n vars (cons u vars)))
                             (list 'none)))
                        ((= ord 1) (pde-pattern-1 table n b vars))
                        ((= ord 2) (pde-pattern-2 table n b vars))
                        ((and (= ord 4) (pde-biharmonic? table n))
                         (list 'biharmonic :homogeneous (pde-zero? b)))
                        (else (list 'none))))
             (type (cond ((equal? (car pat) 'biharmonic) 'elliptic)
                         ((= ord 1) 'first-order)
                         ((= ord 0) 'none)
                         ((>= ord 3) 'higher-order)
                         (else (car ty))))
             (cls (list 'pde-class :unknown (cons u vars) :vars vars :order ord
                        :linear (and linear #t) :quasilinear (and quasi #t) :homogeneous (and hom #t)
                        :const-coeff (and constc #t) :type type :discriminant (cdr ty)
                        :pattern (car pat) :pattern-info (cdr pat) :coords coords
                        :bc-homogeneous (pde-conds-homogeneous pc))))
        (if (step-log-enabled?)
            (record-step 'pde-classify "Классификация уравнения" (pde-class-comment cls) eq N 'main))
        cls)))

; ---------- подстановка решения ----------

; вычислить все (diff e v) снизу вверх
(define (pde-eval-diffs e)
  (cond ((pair? e)
         (if (and (equal? (car e) 'diff) (= (length e) 3) (symbol? (caddr e)))
             (diff (caddr e) (pde-eval-diffs (cadr e)))
             (map pde-eval-diffs e)))
        (else e)))

; (pde-subst e (u x t) rhs): подставить (u x t) → rhs и вычислить все возникшие производные
(define (pde-subst e uv rhs)
  (simplify (pde-eval-diffs (pde-replace e uv rhs))))

; ---------- численные точки ----------

(define (pde-inf-sign e)
  (cond ((member? e '(inf infinity oo +inf)) 1)
        ((member? e '(-inf)) -1)
        ((and (pair? e) (equal? (car e) '*) (= (length e) 3) (equal? (cadr e) -1))
         (let ((s (pde-inf-sign (caddr e)))) (and s (- s))))
        ((and (pair? e) (equal? (car e) '-) (= (length e) 3) (equal? (cadr e) 0))
         (let ((s (pde-inf-sign (caddr e)))) (and s (- s))))
        ((and (pair? e) (equal? (car e) '-) (= (length e) 2))
         (let ((s (pde-inf-sign (cadr e)))) (and s (- s))))
        (else #f)))

(define (pde-num e rules)
  (let ((v (try (eval-num (if (null? rules) e (subst rules e))) (lambda (x) #f))))
    (if (number? v) v #f)))

; граница области: число | pinf | ninf | #f
(define (pde-bound e rules)
  (let ((s (pde-inf-sign e)))
    (cond ((equal? s 1) 'pinf)
          ((equal? s -1) 'ninf)
          (else (pde-num e rules)))))

(define (pde-point v i dom prules k)
  (let* ((found (filter (lambda (d) (equal? (car d) v)) dom))
         (ent (if (null? found) #f (car found)))
         (fr (nth '(0.31 0.57 0.77 0.43 0.67 0.23) (modulo (+ (* 2 i) k) 6)))
         (lo (and ent (pde-bound (cadr ent) prules)))
         (hi (and ent (pde-bound (caddr ent) prules))))
    (cond ((and (number? lo) (number? hi)) (+ lo (* (- hi lo) fr)))
          ((and (number? lo) (equal? hi 'pinf)) (+ lo (* 4 fr)))
          ((and (equal? lo 'ninf) (number? hi)) (- hi (* 4 fr)))
          ((and (equal? lo 'ninf) (equal? hi 'pinf)) (- (* 6 fr) 3))
          (else (+ 0.7 (* 0.37 i) (* 0.21 k))))))

(define (pde-sample-rules syms vars dom k)
  (let* ((params (filter (lambda (s) (not (member? s vars))) syms))
         (prules (map2 (lambda (p j) (list p (+ 1.3 (* 0.41 j) (* 0.17 k)))) params (range (length params))))
         (vrules (map2 (lambda (v i) (list v (pde-point v i dom prules k))) vars (range (length vars)))))
    (append prules vrules)))

(define (pde-dom-syms dom)
  (const-free-syms (cons '+ (append-map (lambda (d) (list (cadr d) (caddr d))) dom))))

; ---------- произвольные функции и пробные функции ----------

; головы неизвестных функций одного аргумента: F(x − ct), g(x)
(define (pde-heads e acc uv)
  (cond ((not (pair? e)) acc)
        (else
         (let ((acc1 (if (and (symbol? (car e)) (= (length e) 2) (not (fbound? (car e)))
                              (not (member? (car e) acc))
                              (not (equal? (car e) (car uv)))
                              (not (member? (car e) '(+ * ^ - / diff at bounded = quote))))
                         (append acc (list (car e)))
                         acc)))
           (foldl (lambda (a z) (pde-heads z a uv)) acc1 e)))))

(define (pde-replace-head e h m)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) h) (= (length e) 2))
         (let ((a (pde-replace-head (cadr e) h m)))
           (cond ((= m 0) (list 'sin a))
                 ((= m 1) (list 'exp (list '* 1/3 a)))
                 (else (list '+ 2 (list '* 1/3 a) (list '* 1/5 (list '^ a 3)))))))
        (else (map (lambda (z) (pde-replace-head z h m)) e))))

(define (pde-test-subst e heads k)
  (let loop ((hs heads) (j 0) (acc e))
    (if (null? hs)
        acc
        (loop (cdr hs) (+ j 1) (pde-replace-head acc (car hs) (modulo (+ j k) 3))))))

; ---------- вердикты ----------

(define (pde-combine vs)
  (cond ((member? #f vs) #f)
        ((member? 'unknown vs) 'unknown)
        ((member? 'numeric vs) 'numeric)
        (else #t)))

; численно: nonzero | zero | unknown; build — (λ (repl) выражение), repl подставляет пробные функции
(define (pde-numeric-verdict build heads vars dom)
  (let loop ((k 0) (zeros 0))
    (if (= k 3)
        (if (> zeros 0) 'zero 'unknown)
        (let ((e (try (build (lambda (x) (pde-test-subst x heads k))) (lambda (er) #f))))
          (if (not e)
              (loop (+ k 1) zeros)
              (let* ((syms (pde-union (const-free-syms e) (pde-dom-syms dom)))
                     (rules (pde-sample-rules syms vars dom k))
                     (v (try (eval-num (subst rules e)) (lambda (er) 'none))))
                (cond ((not (number? v)) (loop (+ k 1) zeros))
                      ((> (abs v) 1e-7) 'nonzero)
                      (else (loop (+ k 1) (+ zeros 1))))))))))

(define (pde-zero-exact? z)
  (or (pde-zero? z)
      (pde-zero? (simplify (together (ode::ode-merge-sqrt z))))))

; остаток build(тождество) → #t | numeric | #f | unknown
(define (pde-verdict build heads vars dom)
  (let ((z (try (simplify (together (build (lambda (x) x)))) (lambda (er) #f))))
    (if (not z)
        'unknown
        (if (pde-zero-exact? z)
            #t
            (let ((nv (pde-numeric-verdict build heads vars dom)))
              (cond ((equal? nv 'nonzero) #f)
                    ((try (ode::ode-trig-zero? z) (lambda (er) #f)) #t)
                    ((equal? nv 'zero) 'numeric)
                    (else 'unknown)))))))

; подставить значения в точке: (v val) по очереди; значение ±inf — предел
(define (pde-at e bs)
  (foldl (lambda (acc b)
           (let ((s (pde-inf-sign (cadr b))))
             (if s
                 (limit acc (car b) (if (> s 0) 'inf '-inf))
                 (simplify (subst (list (list (car b) (cadr b))) acc)))))
         e bs))

(define (pde-check-condition c sol uv heads dom)
  (let ((vars (cdr uv)))
    (cond ((not c) 'unknown)
          ((equal? (car c) 'eq)
           (let ((ex (cadr c)) (bs (caddr c)) (rhs (cadddr c)))
             (pde-verdict (lambda (repl)
                            (pde-at (list '- (pde-subst (repl ex) uv (repl sol)) (repl rhs)) bs))
                          heads vars dom)))
          (else (pde-check-bounded c sol uv dom)))))

; ограниченность: предел в точке конечен
(define (pde-check-bounded c sol uv dom)
  (let* ((vars (cdr uv)) (ex (cadr c)) (bs (caddr c))
         (e (try (pde-subst ex uv sol) (lambda (er) #f))))
    (if (not e)
        'unknown
        (let ((lim (try (foldl (lambda (acc b)
                                 (let ((s (pde-inf-sign (cadr b))))
                                   (limit acc (car b) (cond ((not s) (cadr b)) ((> s 0) 'inf) (else '-inf)))))
                               e bs)
                        (lambda (er) 'err))))
          (cond ((equal? lim 'err) 'unknown)
                ((or (pde-has? lim 'inf) (pde-has? lim '-inf)) #f)
                ((and (pair? lim) (equal? (car lim) 'limit)) 'unknown)
                ((pde-has? lim 'undefined) (pde-probe-unbounded e bs vars dom))
                (else #t))))))

; двусторонний предел не существует: смотрим рост вблизи точки (односторонне, 1e-3 → 1e-6)
(define (pde-probe-unbounded e bs vars dom)
  (let* ((b (car bs)) (v (car b))
         (syms (pde-union (const-free-syms e) (pde-dom-syms dom)))
         (rules (pde-sample-rules syms vars dom 0))
         (others (filter (lambda (r) (not (equal? (car r) v))) rules))
         (v0 (pde-num (cadr b) rules)))
    (if (not v0)
        'unknown
        (let ((a (try (eval-num (subst (cons (list v (+ v0 0.001)) others) e)) (lambda (er) 'none)))
              (c (try (eval-num (subst (cons (list v (+ v0 0.000001)) others) e)) (lambda (er) 'none))))
          (if (and (number? a) (number? c) (> (abs c) 1000) (> (abs c) (* 10 (abs a))))
              #f
              'unknown)))))

; ---------- pdsolve-check ----------

; (= (u x t) rhs) → rhs; голое выражение — как есть; иное равенство → #f
(define (pde-solution-rhs sol uv)
  (cond ((and (pde-eqn? sol) (equal? (cadr sol) uv)) (caddr sol))
        ((pde-eqn? sol) #f)
        (else sol)))

(define (pde-check-comment r)
  (cond ((equal? r #t) "ответ подставлен в уравнение и условия: остаток 0 точно")
        ((equal? r 'numeric) "ответ подставлен в уравнение и условия: остаток 0 численно")
        ((equal? r #f) "остаток не равен 0: ответ не проходит проверку")
        (else "проверить ответ не удалось")))

; (вердикт остаток ((условие вердикт) …)): остаток — левая часть уравнения после подстановки ответа и упрощения
; (#f, если подстановка не удалась); вердикты условий — в порядке записи
(define (pde-check-parts eq sol uv args)
  (if (not (pde-uvars-ok? uv))
      (error "pdsolve-check: третий аргумент — (u x t) с двумя и более переменными")
      (let* ((u (car uv)) (vars (cdr uv))
             (sp (pde-split-args args vars))
             (dom (cadr sp))
             (conds (map (lambda (c) (pde-diff-form c u vars)) (car sp)))
             (pc (pde-parse-conds conds uv))
             (rhs (pde-solution-rhs (pde-diff-form sol u vars) uv)))
        (cond ((any? (lambda (c) (not c)) pc)
               (error "pdsolve-check: не распознано условие (ожидается u(x, 0) = f(x), (at …) или (bounded …))"))
              ((not rhs) (list 'unknown #f '()))
              ((pde-has? rhs 'sum)
               (begin (record-condition '(pde-series) "pdsolve-check: ответ-ряд (sum …) проверяется в PDE.2")
                      (list 'unknown #f '())))
              (else
               (pde-quiet
                (lambda ()
                  (let* ((neq (pde-normalize (pde-prep eq uv)))
                         (heads (foldl (lambda (a z) (pde-heads z a uv)) '() (list neq rhs)))
                         (r0 (pde-verdict (lambda (repl) (pde-subst (repl neq) uv (repl rhs))) heads vars dom))
                         ; условия: данные f(x) — не пробные функции, сравнение только точное или числовое без голов
                         (rs (map (lambda (c) (pde-check-condition c rhs uv '() dom)) pc))
                         (z (try (simplify (together (pde-subst neq uv rhs))) (lambda (er) #f))))
                    (list (pde-combine (cons r0 rs)) z (map2 list conds rs))))))))))

; (pdsolve-check eq sol (u x t) [условия] [:domain …]) → #t | numeric | #f | unknown
(define (pdsolve-check eq sol uv &rest args)
  (let* ((p (pde-check-parts eq sol uv args)) (res (car p)))
    (if (step-log-enabled?)
        (record-step 'pde-check "Проверка решения" (pde-check-comment res) sol res 'main))
    res))

; подробности проверки для сертификата JSON/MCP: (вердикт остаток ((условие вердикт) …))
(define (pdsolve-check-detail eq sol uv &rest args)
  (pde-check-parts eq sol uv args))

; ---------- диспетчер ----------

(define (pde-method-name m)
  (cond ((equal? m 'characteristics) "метод характеристик (PDE.3)")
        ((equal? m 'dalembert) "формула Даламбера (PDE.3)")
        ((equal? m 'separation) "разделение переменных (PDE.2)")
        ((equal? m 'separation-curvilinear) "разделение переменных в криволинейных координатах (PDE.6)")
        ((equal? m 'transform) "интегральные преобразования (PDE.4)")
        ((equal? m 'green) "функция Грина (PDE.5)")
        ((equal? m 'similarity) "автомодельные решения (PDE.7)")
        ((equal? m 'polynomial) "полиномиальные и радиальные решения (PDE.7)")
        (else (to-string m))))

; бесконечна ли область по пространственным переменным (время t ∈ (0, ∞) — обычное дело)
(define (pde-infinite-domain? dom tvar)
  (any? (lambda (d) (and (not (equal? (car d) tvar))
                         (or (pde-inf-sign (cadr d)) (pde-inf-sign (caddr d)))))
        dom))

; какие методы PDE.1–PDE.7 подошли бы
(define (pde-candidates cls dom)
  (let ((ord (pde-field cls :order)) (pat (pde-field cls :pattern)) (lin (pde-field cls :linear))
        (coords (pde-field cls :coords))
        (inf? (pde-infinite-domain? dom (let ((i (pde-field cls :pattern-info)))
                                          (if (and (list? i) (pde-pos :time i)) (nth i (+ 1 (pde-pos :time i))) 't)))))
    (cond ((< ord 1) '())
          ((= ord 1) '(characteristics))
          ((not lin) '())
          ((not (equal? coords 'cartesian)) '(separation-curvilinear))
          ((equal? pat 'wave) (if inf? '(dalembert transform) '(separation dalembert)))
          ((equal? pat 'heat) (if inf? '(transform similarity green) '(separation green)))
          ((member? pat '(laplace poisson helmholtz)) '(separation green))
          ((equal? pat 'biharmonic) '(polynomial))
          ((member? pat '(telegraph klein-gordon reaction-diffusion)) '(separation transform))
          (else '()))))

(define (pde-refusal-comment cls cands)
  (string-append
   "в PDE.0 методов решения нет; "
   (if (null? cands)
       "подходящего метода среди PDE.1–PDE.7 не видно (нелинейное или нестандартное уравнение): доступна проверка ответа pdsolve-check"
       (string-append "подошли бы: "
                      (foldl (lambda (acc m) (if (equal? acc "") (pde-method-name m) (string-append acc ", " (pde-method-name m))))
                             "" cands)))))

(define (pde-opt opts key default)
  (let ((p (pde-pos key opts))) (if p (nth opts (+ p 1)) default)))

; (pdsolve eq (u x t) [условия] [:domain …] [:coords c] [:method m] [:terms N])
(define (pdsolve eq uv &rest args)
  (if (not (pde-uvars-ok? uv))
      (error "pdsolve: второй аргумент — (u x t) с двумя и более переменными")
      (let* ((u (car uv)) (vars (cdr uv))
             (sp (pde-split-args args vars))
             (dom (cadr sp)) (opts (nth sp 2))
             (conds (car sp))
             (pc (pde-parse-conds conds uv)))
        (if (any? (lambda (c) (not c)) pc)
            (pde-solution 'unknown '() '() '() '() '() '() 'unknown 'none 'none
                          :comment "не распознанное условие (ожидается u(x, 0) = f(x), (at …) или (bounded …))")
            (let* ((cls (apply pde-classify (append (list eq uv) conds (if (null? dom) '() (list :domain dom))
                                                    (if (pde-pos :coords opts) (list :coords (pde-opt opts :coords #f)) '()))))
                   (bad (pde-inconsistent-pair pc)))
              (cond (bad
                     (pde-solution 'none '() '() '() '() '() '() 'inconsistent 'none 'none
                                   :class cls
                                   :comment (string-append "условия несовместны: " (to-string (car bad)) " и " (to-string (cadr bad)))))
                    ((< (pde-field cls :order) 1)
                     (pde-solution 'unknown '() '() '() '() '() '() 'unknown 'none 'none
                                   :class cls :comment "уравнение не содержит производных неизвестной"))
                    (else
                     (let ((cands (pde-candidates cls dom)))
                       (pde-solution 'unknown '() '() '() '() '() '() 'unknown 'none 'none
                                     :class cls :hint cands :requested (pde-opt opts :method #f)
                                     :comment (pde-refusal-comment cls cands))))))))))
