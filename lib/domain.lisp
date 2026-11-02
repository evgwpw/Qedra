; domain.lisp — домены, интервалы, декларации, вывод принадлежности и знака (Шаг 16)
;
; Домены (тип domain): naturals ℕ = {0, 1, 2, ...} (С НУЛЁМ), integers ℤ, rationals ℚ, reals ℝ, complexes ℂ;
; решётка вложений ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ (внутри — ранг 0..4).
; Интервалы (тип interval) — подмножества ℝ: (interval lo hi), (interval lo hi 'open 'closed) ...;
; границы — вещественные числа или символы -inf / inf (бесконечные границы всегда открыты).
;
; Декларации: (declare 'x ℤ ...) кладёт ограничения символа в таблицу деклараций текущей сессии (подшаг 22.4);
; ограничения символа — их ПЕРЕСЕЧЕНИЕ. Необъявленный символ — элемент ℂ (#t), во всём остальном — unknown.
; (assuming ((x D ...) ...) тело...) — временные декларации с восстановлением через unwind-protect.
;
; ДОПУЩЕНИЕ ОБ ОПРЕДЕЛЁННОСТИ: все выражения считаются определёнными — деления на 0, log 0 и т. п. нет
; (поэтому x^-1 при x ∈ ℚ лежит в ℚ, а (^ x -2) положительно).

; Шаг 21h': модуль domain. Экспорт — домены и интервалы, декларации, трёхзначные предикаты знака/вещественности,
; op-expr? (используется solve/integrate/series/limit); вывод (dom-infer..., sign-atoms...) приватен
(module domain
  (export domain? make-domain domain-name naturals integers rationals reals complexes
          interval? interval-lo interval-hi interval-lo-closed? interval-hi-closed? make-interval interval empty-interval
          interval-empty? interval-point? positive nonnegative negative nonpositive interval-has? interval-intersect
          interval-subset? interval-has-integer? domain-hull disjoint? intersect-general
          declare undeclare declarations reset-declarations assuming assuming-call
          real? integer-valued? positive? negative? nonnegative? nonpositive? sign-of op-expr?
          constraints-of contains-sym? domain-rank))

; ---------- Домены ----------

(deftype 'domain 'any)
(define (make-domain name rank) (make-object 'domain name rank))
(define (domain? x) (and (object? x) (equal? (object-type x) 'domain)))
(define (domain-name d) (object-ref d 0))
(define (domain-rank d) (object-ref d 1))

(define naturals (make-domain "ℕ" 0))
(define integers (make-domain "ℤ" 1))
(define rationals (make-domain "ℚ" 2))
(define reals (make-domain "ℝ" 3))
(define complexes (make-domain "ℂ" 4))

(define (domain-of-rank r)
  (case r ((0) naturals) ((1) integers) ((2) rationals) ((3) reals) (else complexes)))

(defmethod print (domain) (d) (domain-name d))
(defmethod math-print (domain) (d) (domain-name d))

; точное членство числа в домене ранга r (по типу числа)
(define (rank-has-number? r x)
  (let ((t (type-of x)))
    (cond ((equal? t 'integer) (if (< x 0) (>= r 1) #t))
          ((equal? t 'rational) (>= r 2))
          ((or (equal? t 'float) (equal? t 'algebraic)) (>= r 3))   ; алгебраическое иррациональное; float — вещественный
          (else (>= r 4)))))                                        ; комплексное с ненулевой мнимой частью

(define (real-number? x)
  (and (number? x) (not (equal? (type-of x) 'complex))))

; ---------- Интервалы ----------

(deftype 'interval 'any)
(define (interval? x) (and (object? x) (equal? (object-type x) 'interval)))
(define (interval-lo i) (object-ref i 0))
(define (interval-hi i) (object-ref i 1))
(define (interval-lo-closed? i) (object-ref i 2))
(define (interval-hi-closed? i) (object-ref i 3))

(define (infinite-bound? b) (or (equal? b 'inf) (equal? b '-inf)))

; сравнение границ (числа и ±inf): -1, 0, 1
(define (bound-rank b) (cond ((equal? b '-inf) -1) ((equal? b 'inf) 1) (else 0)))
(define (bound-cmp a b)
  (let ((ra (bound-rank a)) (rb (bound-rank b)))
    (cond ((not (= ra rb)) (if (< ra rb) -1 1))
          ((not (= ra 0)) 0)
          ((< a b) -1)
          ((> a b) 1)
          (else 0))))

(define (interval-empty-bounds? lo hi lc hc)
  (let ((c (bound-cmp lo hi)))
    (or (> c 0) (and (= c 0) (not (and lc hc))))))

; пустой интервал — единственное каноническое представление (равенство через equal?)
(define empty-interval (make-object 'interval 0 0 #f #f))

(define (make-interval lo hi lc hc)
  (if (not (and (or (infinite-bound? lo) (real-number? lo)) (or (infinite-bound? hi) (real-number? hi))))
      (error "interval: границы — вещественные числа или -inf/inf, получено" (list lo hi))
      (let ((lc2 (and lc (not (infinite-bound? lo))))
            (hc2 (and hc (not (infinite-bound? hi)))))
        (if (interval-empty-bounds? lo hi lc2 hc2)
            empty-interval
            (make-object 'interval lo hi lc2 hc2)))))

; (interval lo hi) — закрытый; (interval lo hi 'open 'closed) — флаги левого и правого концов
(define (interval lo hi &rest flags)
  (cond ((null? flags) (make-interval lo hi #t #t))
        ((and (= (length flags) 2)
              (member? (car flags) '(open closed)) (member? (cadr flags) '(open closed)))
         (make-interval lo hi (equal? (car flags) 'closed) (equal? (cadr flags) 'closed)))
        (else (error "interval: флаги — два символа open/closed, получено" flags))))

(define (interval-empty? i) (equal? i empty-interval))
; вырожденный интервал [a, a]
(define (interval-point? i)
  (and (not (interval-empty? i)) (= (bound-cmp (interval-lo i) (interval-hi i)) 0)))

(define positive (interval 0 'inf 'open 'open))
(define nonnegative (interval 0 'inf 'closed 'open))
(define negative (interval '-inf 0 'open 'open))
(define nonpositive (interval '-inf 0 'open 'closed))

; число x (вещественное) лежит в интервале
(define (interval-has? i x)
  (let ((cl (bound-cmp (interval-lo i) x))
        (ch (bound-cmp x (interval-hi i))))
    (and (not (interval-empty? i))
         (or (< cl 0) (and (= cl 0) (interval-lo-closed? i)))
         (or (< ch 0) (and (= ch 0) (interval-hi-closed? i))))))

; пересечение интервалов (результат — интервал, возможно пустой)
(define (interval-intersect a b)
  (let* ((cl (bound-cmp (interval-lo a) (interval-lo b)))
         (ch (bound-cmp (interval-hi a) (interval-hi b)))
         (lo (if (>= cl 0) (interval-lo a) (interval-lo b)))
         (lc (cond ((> cl 0) (interval-lo-closed? a))
                   ((< cl 0) (interval-lo-closed? b))
                   (else (and (interval-lo-closed? a) (interval-lo-closed? b)))))
         (hi (if (<= ch 0) (interval-hi a) (interval-hi b)))
         (hc (cond ((< ch 0) (interval-hi-closed? a))
                   ((> ch 0) (interval-hi-closed? b))
                   (else (and (interval-hi-closed? a) (interval-hi-closed? b))))))
    (if (or (interval-empty? a) (interval-empty? b))
        empty-interval
        (make-interval lo hi lc hc))))

; A ⊆ B для интервалов
(define (interval-subset? a b)
  (cond ((interval-empty? a) #t)
        ((interval-empty? b) #f)
        (else
         (let ((cl (bound-cmp (interval-lo a) (interval-lo b)))
               (ch (bound-cmp (interval-hi a) (interval-hi b))))
           (and (or (> cl 0) (and (= cl 0) (or (interval-lo-closed? b) (not (interval-lo-closed? a)))))
                (or (< ch 0) (and (= ch 0) (or (interval-hi-closed? b) (not (interval-hi-closed? a))))))))))

(define (bound-string b)
  (cond ((equal? b 'inf) "inf") ((equal? b '-inf) "-inf") (else (to-string b))))
(define (interval-string i conv)
  (if (interval-empty? i)
      "∅"
      (string-append (if (interval-lo-closed? i) "[" "(") (bound-string (interval-lo i)) ", "
                     (bound-string (interval-hi i)) (if (interval-hi-closed? i) "]" ")"))))
(defmethod print (interval) (i) (interval-string i to-string))

; Шаг 21d: math-print интервала — запись входного языка, которая ВСЕГДА читается обратно в то же значение:
;   [a, b)  (a, b]  (a, b)  — полуоткрытые и открытые (парсер языка читает их как интервалы);
;   interval(a, b)          — закрытый (запись [a, b] — вектор, поэтому закрытый интервал печатается вызовом);
;   interval(1, 0)          — пустой (запись ∅ читалась бы как пустое множество, а не интервал).
; Границы печатаются math-print (в режиме языка бесконечности — ∞ и -∞)
(define (interval-math-string i)
  (let ((lo (math-print (interval-lo i))) (hi (math-print (interval-hi i))))
    (cond ((interval-empty? i) "interval(1, 0)")
          ((and (interval-lo-closed? i) (interval-hi-closed? i))
           (string-append "interval(" lo ", " hi ")"))
          (else (string-append (if (interval-lo-closed? i) "[" "(") lo ", " hi
                               (if (interval-hi-closed? i) "]" ")"))))))
(defmethod math-print (interval) (i) (interval-math-string i))

; есть ли в непустом интервале целое число
(define (interval-has-integer? i)
  (cond ((interval-empty? i) #f)
        ((equal? (interval-lo i) '-inf) #t)
        (else
         (let ((n (if (interval-lo-closed? i)
                      (ceiling (interval-lo i))
                      (+ (floor (interval-lo i)) 1))))
           (interval-has? i n)))))

; ---------- Включение и непересечение (домены и интервалы) ----------

; оболочка домена — интервал, содержащий весь домен (для ℂ — нет)
(define (domain-hull d)
  (let ((r (domain-rank d)))
    (cond ((= r 0) nonnegative)
          ((< r 4) (interval '-inf 'inf))
          (else #f))))

(defmethod subset? (domain domain) (a b) (<= (domain-rank a) (domain-rank b)))
(defmethod subset? (interval interval) (a b) (interval-subset? a b))
; домен ⊆ интервал: оболочка домена лежит в интервале (ℂ — нет)
(defmethod subset? (domain interval) (d i)
  (let ((h (domain-hull d))) (if h (interval-subset? h i) #f)))
; интервал ⊆ домен: пустой — да; ℝ, ℂ — да; в ℕ ℤ ℚ — только вырожденный интервал с точкой из домена
(defmethod subset? (interval domain) (i d)
  (cond ((interval-empty? i) #t)
        ((>= (domain-rank d) 3) #t)
        ((interval-point? i) (rank-has-number? (domain-rank d) (interval-lo i)))
        (else #f)))
; бесконечное множество не лежит в конечном; интервал — только если пуст или вырожден
(defmethod subset? (domain set) (d s) #f)
(defmethod subset? (interval set) (i s)
  (cond ((interval-empty? i) #t)
        ((interval-point? i) (in? (interval-lo i) s))
        (else #f)))

; домен и интервал не пересекаются (#t/#f; граница — числа)
(define (domain-interval-disjoint? d i)
  (let ((r (domain-rank d)))
    (cond ((interval-empty? i) #t)
          ((>= r 4) #f)
          ((interval-point? i) (not (rank-has-number? r (interval-lo i))))
          ((>= r 2) #f)       ; невырожденный интервал содержит рациональные числа
          (else (not (interval-has-integer? (if (= r 0) (interval-intersect i nonnegative) i)))))))

; (disjoint? a b) — пересечение пусто (#t/#f); a, b — домены или интервалы
(define (disjoint? a b)
  (cond ((and (interval? a) (interval? b)) (interval-empty? (interval-intersect a b)))
        ((and (domain? a) (domain? b)) #f)
        ((and (domain? a) (interval? b)) (domain-interval-disjoint? a b))
        ((and (interval? a) (domain? b)) (domain-interval-disjoint? b a))
        (else (error "disjoint?: ожидаются домены или интервалы"))))

; пересечение интервалов и доменов (вызывается из intersection, set.lisp)
(define (intersect2 a b)
  (cond ((and (interval? a) (interval? b)) (interval-intersect a b))
        ((and (domain? a) (domain? b)) (if (<= (domain-rank a) (domain-rank b)) a b))
        ((and (interval? a) (domain? b))
         (if (>= (domain-rank b) 3) a (error "intersection: пересечение интервала с ℕ ℤ ℚ не представимо")))
        ((and (domain? a) (interval? b)) (intersect2 b a))
        (else (error "intersection: неподдерживаемое сочетание типов" (list (type-of a) (type-of b))))))
(define (intersect-general &rest args) (foldl intersect2 (car args) (cdr args)))

; ---------- Декларации ----------

; Шаг 21c: декларации — состояние сессии; (reset-declarations) (его вызывает math-reset) снимает всё.
; Подшаг 22.4: таблица — алист ((x D ...) ...) в порядке объявления, хранится в ТЕКУЩЕЙ сессии (builtins decl-table /
; decl-table-set!, состояние окружения Env.Decls), а не в plist символа: plist общий на процесс, и две сессии
; AgentApi/MCP видели декларации друг друга. Запись (x) с пустым списком — «снято» (нужна, чтобы снять системную).
; Системные декларации (pi > 0) — *decl-system*: действуют, пока у символа нет записи в таблице; в список
; (declarations) не попадают; сброс таблицы их восстанавливает.
(define *decl-system* '())

; системные ограничения символа ('() — нет)
(define (decl-system x)
  (let ((p (assoc x *decl-system*)))
    (if p (cdr p) '())))

; записать ограничения символа: совпадают с системными — запись удаляется; иначе заменяется на месте или добавляется в конец
(define (decl-store! x ds)
  (let ((tb (decl-table)))
    (begin
      (decl-table-set!
        (if (equal? ds (decl-system x))
            (filter (lambda (e) (not (equal? (car e) x))) tb)
            (if (assoc x tb)
                (map (lambda (e) (if (equal? (car e) x) (cons x ds) e)) tb)
                (append tb (list (cons x ds))))))
      x)))

; (declarations 'x) — ограничения символа (список доменов/интервалов; пусто — нет деклараций);
; (declarations) без аргументов — все текущие пользовательские декларации: список ((x D ...) ...) в порядке объявления
(define (declarations &rest xs)
  (if (null? xs)
      (filter (lambda (e) (not (null? (cdr e)))) (decl-table))
      (let ((p (assoc (car xs) (decl-table))))
        (if p (cdr p) (decl-system (car xs))))))

(define (constraint? c) (or (domain? c) (interval? c)))

; (declare 'x D ...) — добавить ограничения; возвращает символ
(define (declare x &rest ds)
  (if (not (symbol? x))
      (error "declare: первый аргумент — символ, получено" x)
      (begin
        (map (lambda (d) (if (constraint? d) #t (error "declare: ожидается домен или интервал, получено" d))) ds)
        (decl-store! x (foldl (lambda (acc d) (if (member? d acc) acc (append acc (list d)))) (declarations x) ds)))))

; (undeclare 'x) — снять все декларации символа; возвращает символ
(define (undeclare x) (decl-store! x '()))

; снять все пользовательские декларации (системные — pi > 0 — остаются)
(define (reset-declarations)
  (begin
    (decl-table-set! '())
    #t))

; (assuming ((x D ...) ...) тело...) — временные декларации; прежние восстанавливаются при любом выходе
(define (assuming-call specs thunk)
  (let ((saved (map (lambda (s) (cons (car s) (declarations (car s)))) specs)))
    (unwind-protect
      (begin (map (lambda (s) (apply declare s)) specs)
             (thunk))
      (map (lambda (p) (decl-store! (car p) (cdr p))) saved))))

(defmacro (assuming bindings &rest body)
  `(assuming-call (list ,@(map (lambda (b) `(list ',(car b) ,@(cdr b))) bindings))
                  (lambda () ,@body)))

; эффективные ограничения: без деклараций — ℂ
(define (constraints-of x)
  (let ((cs (declarations x))) (if (null? cs) (list complexes) cs)))

; ---------- Вывод принадлежности выражения ----------

; Приведение нестандартных операторов к + * ^ (вход может быть не упрощён)
(define (basic-form e)
  (let ((h (car e)) (args (cdr e)))
    (cond ((and (equal? h '-) (= (length args) 1)) (list '* -1 (car args)))
          ((and (equal? h '-) (> (length args) 1))
           (cons '+ (cons (car args) (map (lambda (a) (list '* -1 a)) (cdr args)))))
          ((and (equal? h '/) (= (length args) 2)) (list '* (car args) (list '^ (cadr args) -1)))
          (else e))))

(define (op-expr? e) (and (list? e) (not (null? e)) (symbol? (car e))))

; символ x в домене ранга r / интервале D: по декларациям
(define (symbol-in x target)
  (if (equal? x '%i)
      ; мнимая единица (Шаг 18): элемент ℂ и только ℂ (не лежит ни в ℝ, ни в интервалах)
      (and (domain? target) (= (domain-rank target) 4))
      (let ((cs (constraints-of x)))
        (cond ((any? (lambda (c) (true? (subset? c target))) cs) #t)
              ((any? (lambda (c) (disjoint? c target)) cs) #f)
              (else unknown)))))

; Содержит ли выражение символ s
(define (contains-sym? e s)
  (cond ((equal? e s) #t)
        ((and (list? e) (not (null? e))) (any? (lambda (a) (contains-sym? a s)) e))
        (else #f)))

; Разбор выражения, линейного по %i: (re im) или #f (не умеем): %i → (0 1); (+ ...) — почленно;
; (* ... %i ...) с единственным множителем %i — вынос; без %i → (e 0)
(define (split-imag e)
  (cond ((equal? e '%i) (list 0 1))
        ((not (contains-sym? e '%i)) (list e 0))
        ((not (op-expr? e)) #f)
        ((equal? (car e) '+)
         (let ((parts (map split-imag (cdr e))))
           (if (every? (lambda (p) p) parts)
               (list (simplify (cons '+ (map car parts))) (simplify (cons '+ (map cadr parts))))
               #f)))
        ((equal? (car e) '*)
         (let ((hit (filter (lambda (a) (contains-sym? a '%i)) (cdr e))))
           (if (and (= (length hit) 1) (equal? (car hit) '%i))
               (list 0 (simplify (cons '* (filter (lambda (a) (not (equal? a '%i))) (cdr e)))))
               #f)))
        (else #f)))

; принадлежность выражения с %i домену ранга r < 4: мнимая часть вещественная и ненулевая → #f;
; нулевая → по вещественной части; иначе unknown
(define (dom-infer-imag e r)
  (let ((s (split-imag e)))
    (if (not s)
        unknown
        (let ((im (cadr s)))
          (cond ((and (number? im) (= im 0)) (dom-infer (car s) r))
                ((and (true? (dom-infer im 3)) (member? (sign-of im) '(positive negative))) #f)
                (else unknown))))))

; (dom-infer e r) — принадлежность выражения домену ранга r (трёхзначная).
; ℕ = ℤ ∩ [0, inf): если прямой вывод не дал #t, пробуем «целое и неотрицательное» (например, x ∈ ℤ, x > 0)
(define (dom-infer e r)
  (let ((v (dom-infer-basic e r)))
    (if (and (= r 0) (equal? v unknown)
             (true? (dom-infer-basic e 1)) (true? (nonnegative? e)))
        #t
        v)))

(define (dom-infer-basic e r)
  (cond ((number? e) (rank-has-number? r e))
        ((symbol? e) (symbol-in e (domain-of-rank r)))
        ((and (op-expr? e) (< r 4) (contains-sym? e '%i)) (dom-infer-imag e r))
        ((op-expr? e)
         (if (= r 4)
             #t                                    ; любое скалярное выражение — комплексное
             (let ((f (basic-form e)))
               (dom-infer-op (car f) (cdr f) r))))
        (else unknown)))

; все аргументы в домене → #t; иначе unknown (замкнутость: ℕ не замкнут по -1, поэтому #f не выводим)
(define (all-in-rank? args r) (every? (lambda (a) (true? (dom-infer a r))) args))

(define (dom-infer-op h args r)
  (cond ((or (equal? h '+) (equal? h '*))
         (if (all-in-rank? args r) #t unknown))
        ((equal? h '^) (dom-infer-pow (car args) (cadr args) r))
        ((member? h '(sin cos exp atan))             ; вещественный аргумент → вещественное значение
         (if (and (>= r 3) (true? (dom-infer (car args) 3))) #t unknown))
        ((equal? h 'log)
         (if (and (>= r 3) (true? (positive? (car args)))) #t unknown))
        ((equal? h 'sqrt)
         (if (and (>= r 3) (true? (nonnegative? (car args)))) #t unknown))
        ((equal? h 'abs)                              ; |u|: вещественное при любом u; целому u — целое
         (cond ((>= r 3) #t)
               ((true? (dom-infer (car args) (if (< r 1) 1 r))) #t)
               (else unknown)))
        (else unknown)))

(define (dom-infer-pow b e r)
  (cond ((integer? e)
         (cond ((>= e 0) (if (true? (dom-infer b r)) #t unknown))              ; целая неотрицательная степень
               ((>= r 2) (if (true? (dom-infer b r)) #t unknown))              ; отрицательная: ℚ ℝ ℂ (b ≠ 0)
               (else unknown)))
        ((and (>= r 3) (true? (nonnegative? b)) (true? (dom-infer e 3))) #t)   ; b ≥ 0, e вещественный
        (else unknown)))

; интервал как цель: числа — точно; символы — по декларациям; выражения — через знак
(define (sign->interval s)
  (case s
    ((positive) positive) ((nonnegative) nonnegative) ((negative) negative)
    ((nonpositive) nonpositive) ((zero) (interval 0 0))
    (else #f)))

(define (interval-infer x i)
  (cond ((number? x) (if (real-number? x) (interval-has? i x) #f))
        ((symbol? x) (symbol-in x i))
        ; выражение с %i, заведомо невещественное, не лежит ни в каком интервале (интервалы ⊂ ℝ)
        ((and (op-expr? x) (contains-sym? x '%i) (equal? (dom-infer x 3) #f)) #f)
        ((op-expr? x)
         (let ((s (sign->interval (sign-of x))))
           (cond ((not s) unknown)
                 ((subset? s i) #t)
                 ((disjoint? s i) #f)
                 (else unknown))))
        (else unknown)))

(defmethod in? (any domain) (x d) (dom-infer x (domain-rank d)))
(defmethod in? (any interval) (x i) (interval-infer x i))

; ---------- Знак ----------
; Внутри знак — множество возможных «атомов»: n (<0), z (=0), p (>0); все три — unknown.

(define all-atoms '(n z p))
(define (atoms-normalize l) (filter (lambda (t) (member? t l)) all-atoms))

(define (sign->atoms s)
  (case s
    ((positive) '(p)) ((negative) '(n)) ((zero) '(z))
    ((nonnegative) '(z p)) ((nonpositive) '(n z))
    (else all-atoms)))

(define (atoms->sign a)
  (let ((n (member? 'n a)) (z (member? 'z a)) (p (member? 'p a)))
    (cond ((and p (not n) (not z)) 'positive)
          ((and n (not p) (not z)) 'negative)
          ((and z (not n) (not p)) 'zero)
          ((and z p (not n)) 'nonnegative)
          ((and n z (not p)) 'nonpositive)
          (else 'unknown))))

; знак суммы / произведения пары атомов (множества возможных атомов)
(define (atom-add a b)
  (cond ((equal? a 'z) (list b))
        ((equal? b 'z) (list a))
        ((equal? a b) (list a))
        (else all-atoms)))
(define (atom-mul a b)
  (cond ((or (equal? a 'z) (equal? b 'z)) 'z)
        ((equal? a b) 'p)
        (else 'n)))

(define (atoms-add as bs)
  (atoms-normalize (append-map (lambda (a) (append-map (lambda (b) (atom-add a b)) bs)) as)))
(define (atoms-mul as bs)
  (atoms-normalize (append-map (lambda (a) (map (lambda (b) (atom-mul a b)) bs)) as)))

(define (number-atoms x)
  (cond ((not (real-number? x)) all-atoms)
        ((> x 0) '(p))
        ((< x 0) '(n))
        (else '(z))))

; атомы по ограничению: ℕ — {0,+}; интервал — по положению границ относительно 0
(define (constraint-atoms c)
  (cond ((domain? c) (if (= (domain-rank c) 0) '(z p) all-atoms))
        ((interval-empty? c) all-atoms)
        (else (atoms-normalize
               (append (if (< (bound-cmp (interval-lo c) 0) 0) '(n) '())
                       (if (interval-has? c 0) '(z) '())
                       (if (> (bound-cmp (interval-hi c) 0) 0) '(p) '()))))))

(define (symbol-atoms x)
  (let ((r (atoms-normalize
            (foldl (lambda (acc c) (filter (lambda (t) (member? t (constraint-atoms c))) acc))
                   all-atoms (declarations x)))))
    (if (null? r) all-atoms r)))      ; противоречивые декларации — ничего не выводим

(define (real-expr? e) (true? (dom-infer e 3)))

(define (sign-atoms e)
  (cond ((number? e) (number-atoms e))
        ((symbol? e) (symbol-atoms e))
        ((op-expr? e)
         (let ((f (basic-form e)))
           (sign-atoms-op (car f) (cdr f))))
        (else all-atoms)))

(define (sign-atoms-op h args)
  (cond ((equal? h '+) (foldl (lambda (acc a) (atoms-add acc (sign-atoms a))) '(z) args))
        ((equal? h '*) (foldl (lambda (acc a) (atoms-mul acc (sign-atoms a))) '(p) args))
        ((equal? h '^) (sign-atoms-pow (car args) (cadr args)))
        ((equal? h 'exp) (if (real-expr? (car args)) '(p) all-atoms))
        ((equal? h 'abs) (if (member? 'z (sign-atoms (car args))) '(z p) '(p)))
        ((equal? h 'sqrt)
         (let ((a (sign-atoms (car args))))
           (cond ((equal? a '(p)) '(p))
                 ((not (member? 'n a)) '(z p))
                 (else all-atoms))))
        (else all-atoms)))

(define (sign-atoms-pow b e)
  (let ((ab (sign-atoms b)))
    (cond ((and (integer? e) (even-integer? e))      ; чётная целая степень вещественного
           (cond ((not (real-expr? b)) all-atoms)
                 ((equal? ab '(z)) '(z))
                 ((member? 'z ab) (if (> e 0) '(z p) '(p)))
                 (else '(p))))
          ((integer? e)                              ; нечётная целая: знак основания (b ≠ 0 при e < 0)
           (let ((r (if (< e 0) (filter (lambda (t) (not (equal? t 'z))) ab) ab)))
             (if (null? r) all-atoms r)))
          ((and (real-expr? e) (equal? ab '(p))) '(p))
          ((and (real-expr? e) (not (member? 'n ab))) '(z p))
          (else all-atoms))))

(define (even-integer? n) (= (mod n 2) 0))

; (sign-of e) → positive | negative | zero | nonnegative | nonpositive | unknown
(define (sign-of e) (atoms->sign (sign-atoms e)))

; ---------- Трёхзначные предикаты ----------

(define (real? e) (in? e reals))
(define (integer-valued? e) (in? e integers))

(define (positive? e)
  (let ((s (sign-of e)))
    (cond ((equal? s 'positive) #t)
          ((member? s '(negative zero nonpositive)) #f)
          (else unknown))))
(define (negative? e)
  (let ((s (sign-of e)))
    (cond ((equal? s 'negative) #t)
          ((member? s '(positive zero nonnegative)) #f)
          (else unknown))))
(define (nonnegative? e)
  (let ((s (sign-of e)))
    (cond ((member? s '(positive zero nonnegative)) #t)
          ((equal? s 'negative) #f)
          (else unknown))))
(define (nonpositive? e)
  (let ((s (sign-of e)))
    (cond ((member? s '(negative zero nonpositive)) #t)
          ((equal? s 'positive) #f)
          (else unknown))))

; Константа pi — положительное вещественное число
(set! *decl-system* (list (cons 'pi (list positive))))
