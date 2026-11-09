; mathlang/runtime.lisp — вычислитель входного математического языка в стиле muSIMP/Derive (Шаг 21, 21a, 21b)
; Шаг 21h': бывший lib\mathlang.lisp разрезан: runtime.lisp (этот файл) — ячейки имён, присваивание, времена выполнения
; конструкций языка, встроенные функции языка, итераторы, факториал; compiler.lisp — компилятор AST → формы Lisp и входные
; точки (math-eval, math-eval-tree, load-math). Загружаются в таком порядке (см. prelude.lisp).
;
; Вход: AST от (math-read-program "строка") — формы с тегами (см. src\MathReader.fs):
;   (:= a e) (:= a) (:= (f x y) body) (:= (f x (:= s 0)) body) (:= (m-index v i ..) e)
;   (:declare x D) (:in x D) (m-vector ..) (m-set ..) (m-index v i ..)
;   (= a b) (/= a b) (< a b) (> a b) (<= a b) (>= a b) (and ..) (or ..) (not a), прочее — вызовы (f args) и арифметика.
;
; Шаг 21b: AST не интерпретируется, а КОМПИЛИРУЕТСЯ в формы Lisp (m-c...), которые вычисляет (и компилирует в замыкания)
; обычный eval. Оператор верхнего уровня — одна скомпилированная форма; определение функции f(x) := e компилируется один
; раз при определении в lambda, параметры — лексические переменные.
;
; Пространства пользователя НЕ связаны с глобальными Lisp-переменными: `:=` не затирает функции библиотек,
; а библиотека не видит пользовательских переменных. Пространство сессии — таблица *m-cells*: имя → ЯЧЕЙКА (вектор,
; см. m-new-cell): в ней и значение переменной языка, и функция языка с этим именем. Скомпилированный код держит ячейки
; прямо в формах (поздняя привязка: переопределение функции, присваивание, clear видны сразу).
; Параметры функции — лексические переменные Lisp: тело видит только свои параметры и глобальные переменные языка —
; но не переменные вызывающей функции; рекурсия работает.
;
; Семантика (как в Derive):
;   * a := e — правая часть вычисляется сразу; но при ИСПОЛЬЗОВАНИИ имени значение вычисляется заново с текущими
;     присваиваниями (y := x^2; x := 3; y → 9). Циклическое определение (x := x + 1 при неприсвоенном x) — ошибка;
;   * имя без значения — символ; вызов f(args): функция языка, иначе Lisp-функция с тем же именем (аргументы вычислены),
;     иначе невычисленная форма (f args);
;   * переменная solve/integrate/diff/limit/series/taylor не должна быть присвоена — ошибка с подсказкой (до вычисления);
;   * результат арифметики и вызовов Lisp-функций проходит через simplify (два числа — сразу Lisp-арифметика);
;   * sin(5), exp(2) от точных чисел остаются символьными (в Lisp-режиме это числа с плавающей точкой);
;     от float — считаются численно; sin(0), cos(0), exp(0), log(1) свёртываются;
;   * if(c, a, b[, u]) ленив; условие вычисляется в true/false/unknown; unknown → ветка u, а без неё —
;     невычисленный if(...); if(c, a) при ложном c — false; and/or/not — трёхзначные (logic.lisp);
;   * `=` вне условия: число/число и разность, упрощающаяся в число, дают true/false; иначе остаётся уравнением (= a b);
;   * x ∈ D — in? (true/false/unknown); x :∈ D — declare (декларации глобальны для процесса — как в Lisp-режиме);
;   * Шаг 21a — программирование: prog, loop/exit, return, локальные переменные (параметры по умолчанию),
;     присваивание элементу v[i] := e, print, итераторы vector/sum/product/select/iterate/iterates.
;   * Шаг 21b — v[i] := e меняет вектор на месте, если он принадлежит только этой переменной (иначе — копия);
;     индексы и правая часть вычисляются ДО чтения вектора; return/exit в «операторных» позициях (хвост функции,
;     оператор тела loop, ветви if в них) — обычные ветвления, без исключений; raise — только в остальных случаях.

; Шаг 21h': модуль mathlang (runtime.lisp + compiler.lisp). Математический язык видит только глобальные имена, поэтому
; экспортируются: точки входа (math-eval, math-eval-tree, load-math, math-reset, factorial, m-capture-start/-end — их зовёт
; AgentApi), времена выполнения, на которые раскрывается сгенерированный код (он вычисляется eval в глобальной области) и
; цели таблицы m-aliases. Остальное (ячейки имён, разбор параметров, вспомогательные m-...) — приватное
(module mathlang
  (export math-reset math-dsolve factorial m-capture-start m-capture-end *m-loop-limit*
          m-gslow m-arith m-arith-fin m-gset! m-gelem-slow m-clear-name m-clear m-define-fun
          m-check-global m-check-local m-arity-error m-ucall-n m-do-return m-do-exit m-ctl-boundary
          m-loop-limit-error m-loop-catch m-elem m-elem1 m-simp m-call-lisp m-and-finish m-or-finish
          m-rel-slow m-make-vector m-items m-fold-items m-iter-run m-it-iterate
          m-groebner m-normal-form m-eliminate m-crt m-binomial m-gamma m-psi m-harmonic m-bernoulli m-rf m-ff m-comb-arity m-polylog m-lambert-w
          m-diff m-solve m-sqrt m-abs m-subst m-print m-set-loop-limit m-first m-rest m-last
          m-reverse m-append m-dimension m-position
          m-interval m-certified-roots m-certified-integral m-certified-sum
          m-cfinite m-cf-term m-cf-terms m-cf-prove m-cf-gf m-guess-recurrence
          m-denest m-radsimp m-puiseux m-piecewise-rest m-inverse m-ode-check
          m-wedge m-extd m-pullback m-hodge m-interior m-grad m-div m-curl m-laplacian m-potential m-vector-potential
          m-form-potential m-integrate-form
          m-integrate m-integrate-change m-line-integral m-arc-length m-surface-integral m-surface-area
          m-region m-rect-region m-triangle-region m-disk-region m-annulus-region m-integrate-region
          m-green-check m-stokes-check m-gauss-check
          m-table-dist m-mean m-variance m-stddev m-pdf m-cdf m-prob m-mgf m-moment m-quantile m-expectation m-dist-support
          m-sample-mean m-sample-variance m-sample-stddev m-median m-quantile-sample m-covariance m-correlation
          m-linear-regression m-frequencies m-bayes m-total-probability
          m-cdf-num m-quantile-bounds m-mle m-mle-check m-moments-estimate m-confint-mean m-confint-mean-sigma
          m-confint-variance m-confint-proportion m-confint-wilson m-t-test m-t-test-two m-t-test-pooled m-t-test-paired
          m-chi2-gof m-chi2-independence m-f-test m-stat-get
          m-curve-speed m-tangent m-normal-vector m-binormal m-frenet m-curvature m-torsion m-curvature-radius
          m-first-form m-second-form m-surface-normal m-gauss-curvature m-mean-curvature m-principal-curvatures
          m-graph-surface m-gauss-bonnet-check
          m-classify-conic m-canonical-conic m-conic-elements m-conic-invariants m-conic-check
          m-classify-quadric m-canonical-quadric m-quadric-invariants m-quadric-check
          m-metric-inverse m-christoffel m-riemann m-riemann-lower m-ricci m-ricci-scalar m-einstein m-kretschmann
          m-covariant-derivative m-geodesic-equations m-curvature-check
          m-smith-form m-smith-invariants m-smith-check m-simplicial-complex m-faces m-boundary-matrix m-homology
          m-homology-text m-betti m-euler-characteristic m-homology-check m-sphere-complex m-circle-complex
          m-disk-complex m-torus-complex m-projective-plane-complex m-klein-bottle-complex
          m-symmetric-group m-alternating-group m-dihedral-group m-cyclic-group m-quaternion-group m-permutation-group
          m-group-order m-conjugacy-classes m-character-table m-character-degrees m-character-table-check
          m-decompose-character m-character-tensor m-character-dual m-character-inner m-character-sym2
          m-character-alt2 m-permutation-character m-regular-character m-character-of-representation
          m-fourier-coefficients m-fourier-series m-fourier-sine-series m-fourier-cosine-series
          m-fourier-complex-coefficients m-fourier-value-at m-fourier-coefficients-check m-parseval-check
          m-residue m-laurent m-singularity-type m-singularities m-contour-integral m-residue-check
          m-contour-integral-check m-integral-by-residues m-integral-fourier m-integral-pv m-integral-keyhole
          m-integral-residues-check m-integral-trig))

(define *m-cells* (make-table))
(define *m-loop-limit* 1000000)      ; предохранитель loop и итераций до неподвижной точки (set_loop_limit)
(define *m-ret* #f)                  ; значение, переносимое return/exit (само исключение несёт только метку)

; ---------- ячейки имён ----------
; ячейка — вектор #(имя значение состояние владение функция nпарам nобяз параметры тело):
;   состояние: () — не присвоена; #f — присвоена, значение без символов (пересчёт не нужен); #t — содержит символы
;   владение: #t — вектор-значение принадлежит только этой переменной (v[i] := e меняет его на месте)
;   функция: #f или вектор замыканий по числу аргументов (индекс = число аргументов; длина не меньше 5)

(define (m-new-cell name) (vector name '() '() #f #f 0 0 '() '()))
(define (m-cell name)
  (let ((c (*m-cells* 'get name)))
    (if (null? c)
        (let ((n (m-new-cell name))) (begin (*m-cells* 'put name n) n))
        c)))
(define (m-cell-find name) (*m-cells* 'get name))          ; ячейка или '() (без создания)

(define (m-cell-reset! c) (begin (vset! c 1 '()) (vset! c 2 '()) (vset! c 3 #f) (vset! c 4 #f) #t))

; сбросить пользовательские переменные, функции языка и декларации доменов (x :∈ D) — состояние сессии
(define (math-reset) (begin (map m-cell-reset! (*m-cells* 'values)) (reset-declarations) #t))

; запись по имени в списке записей (car записи — имя) или '()
(define (m-lookup name table)
  (cond ((null? table) '())
        ((equal? (car (car table)) name) (car table))
        (else (m-lookup name (cdr table)))))

(define m-domain-names '(naturals integers rationals reals complexes))
(define m-interval-names '(positive nonnegative negative nonpositive))
(define m-elem-funs '(sin cos tan cot sec csc sinh cosh tanh coth sech csch
                      asin acos atan acot asec acsc asinh acosh atanh acoth asech acsch exp log ln))
(define m-relations '(= /= < > <= >=))
(define m-arith-ops '(+ - * / ^))

; формы, которые вычисляются отдельно (не как вызов функции с вычисленными аргументами);
; итераторы можно переопределить функцией языка с тем же именем
(define m-iter-forms '(vector sum product select iterate iterates))

; ---------- значения переменных: повторное вычисление при использовании ----------

; значение имени без присвоенного значения: exit без скобок — выход из loop, e, домен, иначе сам символ
(define (m-unbound-value s)
  (cond ((equal? s 'exit) (m-do-exit #f))
        ((equal? s 'e) (list 'exp 1))
        ((member? s m-domain-names) (eval s))
        (else s)))

; медленный путь чтения глобального имени (быстрый — m-gread): значение с символами пересчитывается — подставляются
; ТЕКУЩИЕ значения присвоенных имён; не присвоено — m-unbound-value
(define (m-gslow c s)
  (if (null? (vref c 2))
      (m-unbound-value s)
      (m-resolve (vref c 1) 0)))

; формы, которые после подстановки нужно вычислить заново (а не только упростить)
(define m-reeval-heads '(if and or not = /= < > <= >= m-index :in sum product))

; подстановка текущих значений присвоенных имён в значение v; depth — предохранитель цепочки определений
(define (m-resolve v depth)
  (cond ((> depth 100) (error "слишком глубокая цепочка определений (циклическое определение?)"))
        ((symbol? v)
         (let ((c (m-cell-find v)))
           (if (null? c)
               v
               (let ((x (m-gread c)))
                 (cond ((not (vector? x)) x)
                       ((null? (vref c 2)) v)
                       (else (m-resolve (vref c 1) (+ depth 1))))))))
        ((tensor? v)
         (tensor-raw (tensor-shape-list v) (vector-map (lambda (c) (m-resolve c depth)) (tensor-data v))))
        ((set? v) (list->set (map (lambda (c) (m-resolve c depth)) (set->list v))))
        ((and (list? v) (not (null? v)))
         (let ((r (cons (car v) (map (lambda (a) (m-resolve a depth)) (cdr v)))))
           (cond ((equal? r v) v)
                 ((member? (car v) m-reeval-heads) (math-eval-tree r))
                 (else (m-simp r)))))
        (else v)))

; ---------- упрощение результата ----------

; simplify для выражений; объекты (множества, ряды, домены) не трогаем; ошибка упрощения — значение как есть
; содержит ли выражение tan (шаг N1: результат интегратора с половинными углами log(tan(x/2))
; не должен разворачиваться упрощателем в sin/cos)
(define (m-has-tan? v)
  (cond ((and (list? v) (not (null? v)) (member? (car v) '(tan cot))) #t)
        ((and (list? v) (not (null? v))) (any? m-has-tan? (cdr v)))
        (else #f)))

; упрощать ли выражение (шаг N1): нет — формы (= /= <...), integrate/limit/..., а также log/atan,
; содержащие tan/cot (результат интегратора с половинными углами log(tan(x/2)) не должен
; разворачиваться упрощателем в sin/cos — в том числе внутри объемлющих произведений/сумм)
(define (m-simp? v)
  (cond ((not (and (list? v) (not (null? v)))) #t)
        ((member? (car v) '(= /= < > <= >= :in not and or if integrate limit sum product)) #f)
        ((and (member? (car v) '(log atan)) (m-has-tan? v)) #f)
        ((any? (lambda (a) (and (list? a) (not (null? a)) (not (m-simp? a)))) (cdr v)) #f)
        (else #t)))

(define (m-simp v)
  (cond ((number? v) v)
        ((tensor? v) (simplify v))
        ((object? v) v)
        ((and (list? v) (not (null? v)))
         (if (m-simp? v)
             (try (simplify v) (lambda (err) v))
             v))
        (else v)))

; -∞ как значение — символ -inf (так его понимают limit и integrate): (* -1 inf) → -inf
(define (m-norm v) (if (equal? v '(* -1 inf)) '-inf v))

; арифметика + - * / ^: Lisp-операция над вычисленными аргументами, затем simplify; e^x — exp(x)
(define (m-arith h vals)
  (cond ((and (= (length vals) 2) (number? (car vals)) (number? (cadr vals)) (member? h '(+ - *)))
         (cond ((equal? h '+) (+ (car vals) (cadr vals)))
               ((equal? h '-) (- (car vals) (cadr vals)))
               (else (* (car vals) (cadr vals)))))
        ((and (equal? h '^) (= (length vals) 2) (equal? (car vals) '(exp 1)))
         (m-elem 'exp (list (cadr vals))))
        (else (m-norm (m-simp (apply (eval h) vals))))))

; результат Lisp-операции над двумя числами, не ставший числом (2^(1/2), ...): упрощение
(define (m-arith-fin r) (m-norm (m-simp r)))

; ---------- присваивание, определение, декларация (времена выполнения) ----------

; присваивание глобальной переменной значения, содержащего символы (числа — быстрый путь m-gset-closed!)
(define (m-gset! c name v)
  (begin
    (if (m-mentions? v name)
        (error (string-append "циклическое определение " (to-string name)))
        #f)
    (m-cell-store! c v (m-has-symbol? v))))

; v[i] := e для переменной, значение которой пересчитывается или не присвоено (медленный путь m-gtset!)
(define (m-gelem-slow c name val idx)
  (let* ((cur (let ((x (m-gread-idx c))) (if (vector? x) (m-gslow c name) x)))
         (new (apply m-tset (cons cur (cons #t (cons name (cons val idx)))))))
    (begin (m-gset! c name new)
           (m-cell-own! c)
           val)))

(define (m-distinct? l)
  (cond ((null? l) #t)
        ((member? (car l) (cdr l)) #f)
        (else (m-distinct? (cdr l)))))

; параметр функции — имя или (:= имя значение_по_умолчанию)
(define (m-param-ok? p)
  (or (symbol? p) (and (list? p) (= (length p) 3) (equal? (car p) ':=) (symbol? (cadr p)))))
(define (m-param-name p) (if (symbol? p) p (cadr p)))
(define (m-required params) (length (filter symbol? params)))

; параметры без значения по умолчанию не могут идти после параметров со значением
(define (m-defaults-last? ps seen)
  (cond ((null? ps) #t)
        ((symbol? (car ps)) (if seen #f (m-defaults-last? (cdr ps) #f)))
        (else (m-defaults-last? (cdr ps) #t))))

; определение функции: проверка и компиляция (один раз). Определение или снятие функции с именем итератора меняет
; смысл уже скомпилированных вызовов — тогда перекомпилируются все функции
(define (m-define-fun name params body)
  (cond ((not (every? m-param-ok? params)) (error "определение функции: параметры — имена (или имя := значение по умолчанию)"))
        ((not (m-distinct? (map m-param-name params))) (error "определение функции: имена параметров повторяются"))
        ((not (m-defaults-last? params #f))
         (error "определение функции: параметры без значения по умолчанию должны идти раньше параметров со значением"))
        (else
         (begin (m-install-fun! (m-cell name) params body)
                (m-after-fun-change name)
                (list ':= (cons name params) body)))))

(define (m-after-fun-change name)
  (if (equal? (get name 'm-kind) 'iter) (m-recompile-all) #f))

(define (m-recompile-all)
  (map (lambda (c) (if (vref c 4) (m-install-fun! c (vref c 7) (vref c 8)) #f)) (*m-cells* 'values)))

(define (m-clear-name n)
  (let ((c (m-cell-find n)))
    (begin
      (if (null? c)
          #f
          (begin (vset! c 1 '()) (vset! c 2 '()) (vset! c 3 #f)
                 (if (vref c 4) (begin (vset! c 4 #f) (m-after-fun-change n)) #f)))
      n)))

; clear(a, f, ...) — снять присваивания и определения; clear() — всё
(define (m-clear args)
  (if (null? args)
      (math-reset)
      (begin
        (map (lambda (a) (if (symbol? a) (m-clear-name a) (error "clear: аргументы — имена"))) args)
        #t)))

; ---------- переменная решения/интегрирования не должна быть присвоена ----------

(define m-var-roles '((solve "переменная решения") (integrate "переменная интегрирования")
                      (diff "переменная дифференцирования") (limit "переменная предела")
                      (series "переменная разложения") (taylor "переменная разложения")
                      (subst "переменная подстановки")))

(define (m-check-error s v role)
  (error (string-append (to-string s) " имеет значение " (math-show v) " — " role
                        " не должна быть присвоена; снимите присваивание: " (to-string s) " :=")))

; локальная x = x — не присваивание
(define (m-check-local s v role) (if (equal? v s) #f (m-check-error s v role)))
(define (m-check-global c s role) (if (null? (vref c 2)) #f (m-check-error s (vref c 1) role)))

; ---------- вызовы функций языка ----------

(define (m-arity-error cell nv)
  (let ((np (vref cell 5)) (nr (vref cell 6)))
    (error (string-append (to-string (vref cell 0)) ": ожидается аргументов "
                          (if (= nr np) (to-string np) (string-append "от " (to-string nr) " до " (to-string np)))
                          ", получено " (to-string nv)))))

; вызов с числом аргументов > 4 (до 4 индекс в векторе замыканий берётся прямо в скомпилированном коде)
(define (m-ucall-n cell n args)
  (let* ((fv (vref cell 4)) (f (if (< n (vlength fv)) (vref fv n) #f)))
    (if f (apply f args) (m-arity-error cell n))))

; переопределения имён: язык использует соглашения Derive (diff(выражение, x)), а Lisp-функции — свои
; запись: (имя функция-обёртка); обёртка получает список вычисленных аргументов
(define m-aliases '((diff m-diff) (solve m-solve) (sqrt m-sqrt) (abs m-abs) (subst m-subst)
                    (print m-print) (set_loop_limit m-set-loop-limit)
                    (first m-first) (rest m-rest) (last m-last) (reverse m-reverse) (append m-append)
                    (dimension m-dimension) (position m-position)
                    ; шаг CN.3: численность с сертификатами (ответ — векторы [lo, hi] с шагом 1e-15)
                    (interval m-interval)
                    (certified_roots m-certified-roots)
                    (certified_integral m-certified-integral)
                    (certified_sum m-certified-sum)
                    ; шаг RE.3: C-конечные последовательности
                    (cfinite m-cfinite)
                    (cf_term m-cf-term)
                    (cf_terms m-cf-terms)
                    (cf_prove m-cf-prove)
                    (cf_gf m-cf-gf)
                    (guess_recurrence m-guess-recurrence)
                    ; шаг A1.5: денестинг радикалов и нормальная форма ℚ(α)
                    (denest m-denest)
                    (radsimp m-radsimp)
                    ; шаг 21l.0: комбинаторные головы
                    (binomial m-binomial) (gamma m-gamma) (psi m-psi) (harmonic m-harmonic)
                    (bernoulli m-bernoulli) (rf m-rf) (ff m-ff)
                    ; шаг PL: полилогарифм и функция Ламберта
                    (polylog m-polylog) (lambert_w m-lambert-w)
                    ; шаг 21i: базисы Грёбнера — векторы-аргументы → списки, результат — вектор
                    (groebner m-groebner) (normal_form m-normal-form) (eliminate m-eliminate)
                    ; NT.4: КТО — остатки и модули приходят векторами, ответ — [x, M]
                    (crt m-crt)
                    ; A2.2: ряды Пюизё — puiseux(F, x, y, n) → вектор ветвей (q термы)
                    (puiseux m-puiseux)
                    ; DF.2: дифференциальные формы и векторный анализ (переменные — последним вектором)
                    (wedge m-wedge) (extd m-extd) (pullback m-pullback) (hodge m-hodge) (interior m-interior)
                    (grad m-grad) (div m-div) (curl m-curl) (laplacian m-laplacian)
                    (potential m-potential) (vector_potential m-vector-potential)
                    (form_potential m-form-potential) (integrate_form m-integrate-form)
                    ; MINT.a: кратные, замена переменных, первого рода
                    (integrate m-integrate) (integrate_change m-integrate-change)
                    (line_integral m-line-integral) (arc_length m-arc-length)
                    (surface_integral m-surface-integral) (surface_area m-surface-area)
                    ; MINT.b: области, смена порядка (Фубини), проверки Грина / Стокса / Гаусса
                    (region m-region) (rect_region m-rect-region) (triangle_region m-triangle-region)
                    (disk_region m-disk-region) (annulus_region m-annulus-region) (integrate_region m-integrate-region)
                    (green_check m-green-check) (stokes_check m-stokes-check) (gauss_check m-gauss-check)
                    ; PROB: вероятность и статистика
                    (table_dist m-table-dist) (mean m-mean) (variance m-variance) (stddev m-stddev)
                    (pdf m-pdf) (pmf m-pdf) (cdf m-cdf) (prob m-prob) (mgf m-mgf) (moment m-moment)
                    (quantile m-quantile) (expectation m-expectation) (dist_support m-dist-support)
                    (sample_mean m-sample-mean) (sample_variance m-sample-variance) (sample_stddev m-sample-stddev)
                    (median m-median) (quantile_sample m-quantile-sample) (covariance m-covariance)
                    (correlation m-correlation) (linear_regression m-linear-regression)
                    (frequencies m-frequencies) (bayes m-bayes) (total_probability m-total-probability)
                    ; PROB.b: математическая статистика
                    (cdf_num m-cdf-num) (quantile_bounds m-quantile-bounds) (mle m-mle) (mle_check m-mle-check)
                    (moments_estimate m-moments-estimate) (confint_mean m-confint-mean)
                    (confint_mean_sigma m-confint-mean-sigma) (confint_variance m-confint-variance)
                    (confint_proportion m-confint-proportion) (confint_wilson m-confint-wilson)
                    (t_test m-t-test) (t_test_two m-t-test-two) (t_test_pooled m-t-test-pooled)
                    (t_test_paired m-t-test-paired) (chi2_gof m-chi2-gof) (chi2_independence m-chi2-independence)
                    (f_test m-f-test) (stat_get m-stat-get)
                    ; DG: дифференциальная геометрия кривых и поверхностей
                    (curve_speed m-curve-speed) (tangent m-tangent) (normal_vector m-normal-vector)
                    (binormal m-binormal) (frenet m-frenet) (curvature m-curvature) (torsion m-torsion)
                    (curvature_radius m-curvature-radius) (first_form m-first-form) (second_form m-second-form)
                    (surface_normal m-surface-normal) (gauss_curvature m-gauss-curvature)
                    (mean_curvature m-mean-curvature) (principal_curvatures m-principal-curvatures)
                    (graph_surface m-graph-surface) (gauss_bonnet_check m-gauss-bonnet-check)
                    ; AG: кривые и поверхности второго порядка
                    (classify_conic m-classify-conic) (canonical_conic m-canonical-conic) (conic_elements m-conic-elements)
                    (conic_invariants m-conic-invariants) (conic_check m-conic-check)
                    (classify_quadric m-classify-quadric) (canonical_quadric m-canonical-quadric)
                    (quadric_invariants m-quadric-invariants) (quadric_check m-quadric-check)
                    ; TEN: метрика и кривизна
                    (metric_inverse m-metric-inverse) (christoffel m-christoffel) (riemann m-riemann)
                    (riemann_lower m-riemann-lower) (ricci m-ricci) (ricci_scalar m-ricci-scalar)
                    (einstein m-einstein) (kretschmann m-kretschmann) (covariant_derivative m-covariant-derivative)
                    (geodesic_equations m-geodesic-equations) (curvature_check m-curvature-check)
                    ; HOM: форма Смита и гомологии симплициальных комплексов
                    (smith_form m-smith-form) (smith_invariants m-smith-invariants) (smith_check m-smith-check)
                    (simplicial_complex m-simplicial-complex) (faces m-faces) (boundary_matrix m-boundary-matrix)
                    (homology m-homology) (homology_text m-homology-text) (betti m-betti)
                    (euler_characteristic m-euler-characteristic) (homology_check m-homology-check)
                    (sphere_complex m-sphere-complex) (circle_complex m-circle-complex) (disk_complex m-disk-complex)
                    (torus_complex m-torus-complex) (projective_plane_complex m-projective-plane-complex)
                    (klein_bottle_complex m-klein-bottle-complex)
                    ; REP: представления конечных групп
                    (symmetric_group m-symmetric-group) (alternating_group m-alternating-group)
                    (dihedral_group m-dihedral-group) (cyclic_group m-cyclic-group)
                    (quaternion_group m-quaternion-group) (permutation_group m-permutation-group)
                    (group_order m-group-order) (conjugacy_classes m-conjugacy-classes)
                    (character_table m-character-table) (character_degrees m-character-degrees)
                    (character_table_check m-character-table-check) (decompose_character m-decompose-character)
                    (character_tensor m-character-tensor) (character_dual m-character-dual)
                    (character_inner m-character-inner) (character_symmetric_square m-character-sym2)
                    (character_alternating_square m-character-alt2) (permutation_character m-permutation-character)
                    (regular_character m-regular-character) (character_of_representation m-character-of-representation)
                    ; FS: ряды Фурье на отрезке
                    (fourier_coefficients m-fourier-coefficients) (fourier_series m-fourier-series)
                    (fourier_sine_series m-fourier-sine-series) (fourier_cosine_series m-fourier-cosine-series)
                    (fourier_complex_coefficients m-fourier-complex-coefficients) (fourier_value_at m-fourier-value-at)
                    (fourier_coefficients_check m-fourier-coefficients-check) (parseval_check m-parseval-check)
                    ; CA: ТФКП — вычеты, ряд Лорана, особые точки, интеграл по окружности
                    (residue m-residue) (laurent m-laurent) (singularity_type m-singularity-type)
                    (singularities m-singularities) (contour_integral m-contour-integral)
                    (residue_check m-residue-check) (contour_integral_check m-contour-integral-check)
                    (integral_by_residues m-integral-by-residues) (integral_fourier m-integral-fourier)
                    (integral_pv m-integral-pv) (integral_keyhole m-integral-keyhole) (integral_trig m-integral-trig)
                    (integral_residues_check m-integral-residues-check)
                    ; WASM.6a Д2: inverse([[…]]) — обратная матрица в языке
                    (inverse m-inverse)))

; имена Lisp-функций с «-» в языке пишутся с «_» (минус — вычитание): poly_gcd(a, b) → (poly-gcd a b)
(define m-renames '(; преобразования Лапласа, Z и Фурье (TR.1–TR.3): имена с «_» во входном языке
                    ; PROB: распределения (данные) и проверка нормировки
                    (bernoulli_dist bernoulli-dist) (binomial_dist binomial-dist) (poisson_dist poisson-dist)
                    (geometric_dist geometric-dist) (uniform_discrete uniform-discrete)
                    (hypergeometric_dist hypergeometric-dist) (uniform_dist uniform-dist) (normal_dist normal-dist)
                    (exponential_dist exponential-dist) (gamma_dist gamma-dist) (beta_dist beta-dist)
                    (chi2_dist chi2-dist) (student_dist student-dist) (f_dist f-dist) (density_dist density-dist)
                    (dist_check dist-check) (dist_mass dist-mass)
                    (inverse_laplace inverse-laplace) (laplace_check laplace-check) (laplace_dsolve laplace-dsolve)
                    (inverse_ztransform inverse-ztransform) (ztransform_check ztransform-check)
                    (inverse_fourier inverse-fourier) (fourier_check fourier-check)
                    (poly_gcd poly-gcd) (poly_lcm poly-lcm) (poly_quotient poly-quotient)
                    (poly_remainder poly-remainder) (real_roots real-roots) (power_set power-set)
                    (set_difference set-difference) (list_to_set list->set) (set_to_list set->list)
                    (is_empty empty-set?)
                    ; шаг 21h': счётчики алгоритмов, переключатель алгоритмов, журнал шагов
                    (algo_stats algo-stats) (algo_stats_reset algo-stats-reset) (set_algorithm set-algorithm)
                    (step_log_on step-log-on) (step_log_off step-log-off) (step_log step-log)
                    (step_log_clear step-log-clear) (record_step record-step)
                    ; шаг 21k.6: алгоритм Риша без каскада и таблица спецфункций неэлементарного остатка
                     (risch_integrate risch-integrate) (risch_special risch-special)
                     ; шаг LA.4: линейная алгебра из mathlang (результат — tensor/пара tensor)
                     (jordan_form math-jordan-form) (jordan_blocks math-jordan-blocks)
                     (mat_exp math-mat-exp) (mat_power math-mat-power) (mat_fn math-mat-fn)
                     (diagonalize math-diagonalize) (is_diagonalizable math-diagonalizable?)
                     ; шаг LP.3: линейное и целочисленное программирование
                     (lp_maximize lp-maximize) (lp_minimize lp-minimize)
                      (lp_solve math-lp-solve) (ilp_solve math-ilp-solve)
                      ; шаг OPT.1: критические точки, экстремумы, гессиан, множители Лагранжа
                      (critical_points math-critical-points) (extrema math-extrema)
                      (hessian math-hessian) (lagrange math-lagrange)
                      ; A3′.7: эллиптические интегралы Лежандра — ввод заглавными именами
                      (EllipticF elliptic-f) (EllipticE elliptic-e) (EllipticPi elliptic-pi)
                      (EllipticK elliptic-k) (EllipticEC elliptic-ec)
                      ; NT.2: сертификат простоты
                      (prime_certificate pratt-certificate)
                    ; NT.4: теория чисел — простые, факторизация, конечные поля
                      (isprime prime?) (factorint factor-integer) (gf gf-field)
                      (gf_inv gf-inv) (gf_to_int gf->int)
                      (solve_linear_diophantine solve-linear-diophantine)
                      (pell_negative pell-negative) (pell_solutions pell-solutions)
                      (sum_of_two_squares sum-of-two-squares)
                      (pythagorean_triples pythagorean-triples)
                      ; ODE.0: сертификат решения ОДУ (WASM.6a Д4: в языке y и y' читаются по-разному — обёртка сводит их)
                      (ode_check m-ode-check) (dsolve math-dsolve)
                      ; WEB.PLOT: численное решение задачи Коши, график решения ОДУ, поле направлений
                      (ode_numeric ode-numeric) (plot_ode plot-ode) (plot_direction_field plot-direction-field)
                       ; A3.1: плоские алгебраические кривые — особые точки и род
                       (singular_points singular-points) (genus curve-genus)))

; dsolve(eq, y(t), …) с t ≠ x: решатель ОДУ работает по x, поэтому t → x, решаем, x → t в ответе
; (штрихи y′ по t уже поставлены читателем). Если x встречается в аргументах — без замены.
(define (m-tree-has? s e)
  (cond ((equal? e s) #t) ((pair? e) (or (m-tree-has? s (car e)) (m-tree-has? s (cdr e)))) (else #f)))
(define (math-dsolve eq yx &rest args)
  (if (and (pair? yx) (pair? (cdr yx)) (null? (cddr yx)) (symbol? (cadr yx)) (not (equal? (cadr yx) 'x))
           (not (m-tree-has? 'x (cons eq (cons yx args)))))
      (let* ((v (cadr yx))
             (r (apply dsolve (cons (subst (list v 'x) eq)
                                    (cons (subst (list v 'x) yx)
                                          (map (lambda (a) (subst (list v 'x) a)) args))))))
        (subst (list 'x v) r))
      (apply dsolve (cons eq (cons yx args)))))

(define (m-lisp-name h)
  (let ((r (get h 'm-rename))) (if (null? r) h r)))

; ---------- шаг CN.3: интервальные ответы в языке ----------

; интервал → вектор [lo, hi]; концы округлены НАРУЖУ до 1e-12 (гарантия сохраняется,
; а печать остаётся читаемой: точные дроби бывают в сотни цифр)
(define (m-iv-vec I)
  (let* ((p (^ 10 12))
         (lo (/ (floor (* (iv-lo I) p)) p))
         (hi (/ (- (floor (* (- (iv-hi I)) p))) p)))
    (vector lo hi)))

; граница отрезка в языке: число, интервал или константа (pi, e)
(define (m-iv-bound v)
  (cond ((iv? v) v) ((number? v) (iv v v)) (else (iv-eval v 'm-const (iv 0 0)))))

; interval(выражение, x, a, b) — включение выражения на [a,b]; interval(lo, hi[, флаги]) — прежний домен
(define (m-interval vals)
  (cond ((= (length vals) 2) (apply interval vals))
        ((and (= (length vals) 4)
              (member? (nth vals 2) '(open closed))
              (member? (nth vals 3) '(open closed)))
         (apply interval vals))
        ((= (length vals) 4)
         (let* ((A (m-iv-bound (nth vals 2))) (B (m-iv-bound (nth vals 3))))
           (m-iv-vec (iv-refine (car vals) (cadr vals)
                                (iv (iv-lo A) (iv-hi B)) 1/1000000000000000))))
        (else (error "interval: ожидается interval(выражение, x, a, b) или interval(lo, hi[, флаги])"))))

; certified_roots(f, x, a, b, tol) → [сертифицированные, нерешённые] (векторы интервалов)
(define (m-certified-roots vals)
  (let ((ans (certified-roots (car vals) (cadr vals) (nth vals 2) (nth vals 3) (nth vals 4))))
    (vector (apply vector (map m-iv-vec (car ans)))
            (apply vector (map m-iv-vec (cadr ans))))))

; ---------- шаг RE.3: C-конечные последовательности в языке ----------

; аргумент языка — наша cfinite (её возвращает cfinite(...))
(define (m-cf-object v)
  (if (cf? v) v (error "ожидается cfinite([коэффициенты], [начальные])")))

; cfinite([c1,…], [a0,…]) → последовательность
(define (m-cfinite vals) (cfinite (m-items (car vals)) (m-items (cadr vals))))

; cf_term(s, n) → число; cf_terms(s, k) → вектор
(define (m-cf-term vals) (cf-term (m-cf-object (car vals)) (cadr vals)))
(define (m-cf-terms vals)
  (m-list->vector (cf-terms (m-cf-object (car vals)) (cadr vals))))

; cf_prove(lhs, rhs) → (proved R) или (disproved n0 lhs rhs)
(define (m-cf-prove vals) (cf-prove (car vals) (cadr vals)))

; cf_gf(s, x) → [P, Q] (коэффициенты, младшая первой)
(define (m-cf-gf vals)
  (let ((pq (cf->gf (m-cf-object (car vals)) (cadr vals))))
    (m-list->vector (list (m-list->vector (car pq))
                          (m-list->vector (cadr pq))))))

; guess_recurrence([a0, …]) → [коэффициенты, начальные]
(define (m-guess-recurrence vals)
  (let ((s (cf-from-terms (m-items (car vals)))))
    (m-list->vector (list (m-list->vector (cf-coeffs s))
                          (m-list->vector (cf-init s))))))

; certified_integral(f, x, a, b, tol) → [lo, hi]
(define (m-certified-integral vals)
  (m-iv-vec (certified-integral (car vals) (cadr vals) (nth vals 2) (nth vals 3) (nth vals 4))))

; certified_sum(term, k, a, tol) → [lo, hi]; отказ (нет строгой оценки) — false (WASM.6a Д8)
(define (m-certified-sum vals)
  (let ((r (certified-sum (car vals) (cadr vals) (nth vals 2) (nth vals 3))))
    (if r (m-iv-vec r) #f)))

; ---------- шаг A1.5: денестинг радикалов и нормальная форма ----------

; denest(выражение) — денестинг √(a + b√r) глубины 2
(define (m-denest vals) (sqrt-denest (car vals)))

; radsimp(выражение) — нормальная форма в ℚ(α)
(define (m-radsimp vals) (alg-simplify (car vals)))

; ---------- WASM.6a Д2, Д4, Д9: обратная матрица, ode_check, piecewise ----------

; inverse(матрица) — обратная матрица (вырожденная — ошибка «матрица вырождена»)
(define (m-inverse vals)
  (if (not (= (length vals) 1)) (error "inverse: ожидается одна матрица"))
  (let ((r (inv (m-tolist (car vals)))))
    (if (tensor? r) (linalg-pretty (tensor->list r)) r)))

; замена голого символа y на (y x): в языке y' читается как (diff (y x) x), а y — просто символ
(define (m-y-fun e y yx)
  (cond ((equal? e yx) e)                 ; уже записанное (y x) не трогаем
        ((equal? e y) yx)
        ((pair? e) (map (lambda (z) (m-y-fun z y yx)) e))
        (else e)))

; ode_check(уравнение, решение, y(x)) — уравнение и решение приводятся к (y x)
(define (m-ode-check eq sol yx)
  (let ((y (and (pair? yx) (car yx))))
    (if (and (symbol? y) (symbol? (cadr yx)))
        (dsolve-check (m-y-fun eq y yx) (m-y-fun sol y yx) yx)
        (dsolve-check eq sol yx))))
; нерешённое условие: piecewise с этой ветви (условие — вычисленное значение, ответ — как записан)
(define (m-piecewise-rest c e rest) (list 'piecewise (cons (list c e) rest)))

; после подстановки числа условия piecewise становятся решаемыми: выбираем ветвь (Д9)
(define (m-pw-eval e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'piecewise) (pair? (cdr e)) (list? (cadr e)))
         (m-pw-eval-branches (cadr e)))
        (else e)))

(define (m-pw-eval-branches bs)
  (if (null? bs)
      'undefined
      (let* ((b (car bs)) (c (car b)) (v (cadr b))
             (cv (try (eval c) (lambda (err) 'unknown))))
        (cond ((equal? cv #t) (try (eval v) (lambda (err) v)))
              ((equal? cv #f) (m-pw-eval-branches (cdr bs)))
              (else (list 'piecewise (cons b (cdr bs))))))))

; вызов Lisp-функции по имени во время выполнения (имя не было связано при компиляции)
(define (m-call-lisp h vals)
  (let ((al (get h 'm-alias)) (lh (m-lisp-name h)))
    (cond ((not (null? al)) (apply (eval al) (list vals)))
          ((equal? (get h 'm-kind) 'elem) (m-elem h vals))
          ((fbound? lh) (m-simp (apply (eval lh) vals)))
          (else (cons h vals)))))                           ; неизвестная функция — невычисленная форма

; ---------- управление: return, exit, loop ----------
; return/exit — «исключения» с данными (m-ctl return|exit); само значение — в *m-ret*.
; Исключения нужны только вне «операторных» позиций (см. m-cs); обычные ветвления — без них

(define (m-do-return v) (begin (set! *m-ret* v) (raise (list 'm-ctl 'return))))
(define (m-do-exit v) (begin (set! *m-ret* v) (raise (list 'm-ctl 'exit))))

; данные управляющего «исключения» (m-ctl вид) или '() для обычной ошибки
(define (m-ctl-of err)
  (let ((d (error-data err)))
    (if (and (list? d) (not (null? d)) (equal? (car d) 'm-ctl)) d '())))

; повторный выброс перехваченной ошибки
(define (m-rethrow err)
  (let ((d (error-data err)))
    (if (null? d) (error (error-message err)) (raise d))))

; граница функции/оператора верхнего уровня: return → значение; exit вне loop — ошибка
(define (m-ctl-boundary thunk)
  (try (thunk)
       (lambda (err)
         (let ((c (m-ctl-of err)))
           (cond ((null? c) (m-rethrow err))
                 ((equal? (cadr c) 'return) *m-ret*)
                 (else (error "exit: вне цикла loop")))))))

(define (m-loop-limit-error limit)
  (error (string-append "loop: превышен лимит итераций " (to-string limit)
                        " (изменить: set_loop_limit(n); выход из цикла — exit)")))

; обработчик цикла с «исключением» exit: exit → значение цикла, прочее — дальше
(define (m-loop-catch err)
  (let ((c (m-ctl-of err)))
    (if (and (not (null? c)) (equal? (cadr c) 'exit))
        *m-ret*
        (m-rethrow err))))

(define (m-set-loop-limit vals)
  (if (and (= (length vals) 1) (integer? (car vals)) (> (car vals) 0))
      (begin (set! *m-loop-limit* (car vals)) (car vals))
      (error "set_loop_limit: ожидается положительное целое")))

; print(e1, e2, ...) — печать значений в синтаксисе языка через пробел; значение — последний аргумент.
; Вывод идёт сразу в stdout, а между (m-capture-start) и (m-capture-end) накапливается (JSON-режим: op math
; возвращает его в поле output, иначе печать сломала бы поток ответов)
(define *m-out* #f)                  ; #f — печатать сразу; иначе список накопленных строк (последняя — первой)
(define (m-capture-start) (begin (set! *m-out* '()) #t))
(define (m-capture-end)              ; накопленные строки через перевод строки; вывод снова идёт в stdout
  (let ((r *m-out*))
    (begin (set! *m-out* #f)
           (if (or (equal? r #f) (null? r)) "" (join-strings (reverse r) "\n")))))
(define (m-show-for-print v) (if (equal? (type-of v) 'string) v (math-show v)))
(define (m-print vals)
  (let ((s (join-strings (map m-show-for-print vals) " ")))
    (begin
      (if (equal? *m-out* #f)
          (begin (display s) (newline))
          (set! *m-out* (cons s *m-out*)))
      (if (null? vals) #f (last vals)))))

; ---------- элементарные функции ----------

; (Шаг 21c: значения в особых точках — sin(0), exp(0), log(1), sin(pi/6) — считает simplify; обход m-fold удалён)

; точный аргумент — символьный результат (sin(5) остаётся sin(5)); float и комплексные — численно
(define (m-elem h vals)
  (if (not (= (length vals) 1))
      (error (string-append (to-string h) ": ожидается один аргумент"))
      (m-elem1 h (eval h) (car vals))))

; f — сама Lisp-функция с именем h (в скомпилированном коде — значение глобального имени)
(define (m-elem1 h f a)
  (if (and (number? a) (member? (type-of a) '(float complex)))
      (f a)
      (simplify (list h a))))

; точные рациональные (и отрицательные) — через simplify: sqrt(8) → 2*2^(1/2), sqrt(-4) → 2%i
(define (m-sqrt vals)
  (if (not (= (length vals) 1))
      (error "sqrt: ожидается один аргумент")
      (let ((a (car vals)))
        (if (and (number? a) (member? (type-of a) '(float complex)))
            (sqrt a)
            (simplify (list 'sqrt a))))))

(define (m-abs vals)
  (if (not (= (length vals) 1))
      (error "abs: ожидается один аргумент")
      (let ((a (car vals)))
        (if (number? a) (abs a) (m-simp (list 'abs a))))))

; ---------- diff, solve ----------

(define (m-diff1 e x)
  (if (tensor? e)
      (tensor-raw (tensor-shape-list e) (vector-map (lambda (c) (m-diff1 c x)) (tensor-data e)))
      (let ((d (simplify (diff x e))))
        ; шаг PL: остатки (diff u v) после правила полилогарифма (двуарные головы) — вычисляем
        (if (contains-sym? d 'diff) (simplify (pl-resolve d)) d))))

; diff(выражение, x) и diff(выражение, x, n) — n-я производная
(define (m-diff-n e x n)
  (if (= n 0) e (m-diff-n (m-diff1 e x) x (- n 1))))
(define (m-diff vals)
  (cond ((not (and (>= (length vals) 2) (<= (length vals) 3)))
         (error "diff: ожидается diff(выражение, переменная[, порядок])"))
        ((not (symbol? (cadr vals))) (error "diff: переменная дифференцирования — имя"))
        ((and (= (length vals) 3) (not (and (integer? (caddr vals)) (>= (caddr vals) 0))))
         (error "diff: порядок — неотрицательное целое"))
        (else (m-diff-n (car vals) (cadr vals) (if (= (length vals) 3) (caddr vals) 1)))))

; subst(выражение, x, значение), subst(выражение, x = значение), subst(выражение, [x = 1, y = 2]);
; порядок Lisp-функции — subst(x = значение, выражение) — тоже принимается (если первый аргумент — уравнение)
(define (m-equation? v) (and (list? v) (not (null? v)) (equal? (car v) '=)))
(define (m-subst vals)
  (m-pw-eval
   (let ((n (length vals)))
    (cond ((= n 3) (if (symbol? (cadr vals))
                       (m-simp (subst (list '= (cadr vals) (caddr vals)) (car vals)))
                       (error "subst: вторым аргументом ожидается имя переменной")))
          ((= n 2) (let ((a (car vals)) (b (cadr vals)))
                     (if (and (m-equation? a) (not (m-equation? b)) (not (tensor? b)))
                         (m-simp (subst a b))
                         (m-simp (subst (m-tolist b) a)))))
          (else (error "subst: ожидается subst(выражение, x, значение) или subst(выражение, x = значение)"))))))

; векторы-аргументы solve (системы) → списки; решения-списки уравнений системы → векторы [x = 1, y = 2]
(define (m-tolist a) (if (tensor? a) (tensor->list a) a))
(define (m-solve-elem s)
  (if (and (list? s) (not (null? s)) (list? (car s)) (not (null? (car s))))
      (tensor-from-flat (list (length s)) s)
      s))
(define (m-solve vals)
  (if (not (= (length vals) 2))
      (error "solve: ожидается solve(уравнение, переменная) или solve([уравнения], [переменные])")
      (let ((r (solve (m-tolist (car vals)) (m-tolist (cadr vals)))))
        (if (set? r)
            (list->set (map m-solve-elem (set->list r)))
            r))))

; ---------- базисы Грёбнера (шаг 21i) ----------
; groebner([многочлены], [переменные] [, порядок]) → вектор; normal_form(f, [образующие], [переменные] [, порядок]);
; eliminate([многочлены], [исключаемые], [остальные]) → вектор
(define (m-list->vector l) (tensor-from-flat (list (length l)) l))
(define (m-groebner vals)
  (if (not (or (= (length vals) 2) (= (length vals) 3)))
      (error "groebner: ожидается groebner([многочлены], [переменные]) или groebner([многочлены], [переменные], порядок)")
      (m-list->vector (apply groebner (map m-tolist vals)))))
(define (m-normal-form vals)
  (if (not (or (= (length vals) 3) (= (length vals) 4)))
      (error "normal_form: ожидается normal_form(f, [образующие], [переменные] [, порядок])")
      (apply normal-form (map m-tolist vals))))
(define (m-eliminate vals)
  (if (not (= (length vals) 3))
      (error "eliminate: ожидается eliminate([многочлены], [исключаемые], [остальные])")
      (m-list->vector (apply eliminate (map m-tolist vals)))))

; КТО в языке: crt([остатки], [модули]) → [x, M] (оба — числа) или false при несовместности
(define (m-crt vals)
  (if (not (= (length vals) 2))
      (error "crt: ожидается crt([остатки], [модули])")
      (let ((r (crt (m-tolist (car vals)) (m-tolist (cadr vals)))))
        (if r (m-list->vector r) #f))))

; ---------- логика ----------

; and: false — сразу false; true — пропускаем; прочее (unknown, отношения) копим
(define (m-and-finish acc)
  (cond ((null? acc) #t)
        ((null? (cdr acc)) (car acc))
        (else (cons 'and acc))))

(define (m-or-finish acc)
  (cond ((null? acc) #f)
        ((null? (cdr acc)) (car acc))
        (else (cons 'or acc))))

; ---------- отношения ----------

; сравнение a = b (трёхзначное): числа — по значению; векторы — покомпонентно; множества чисел — по equal?;
; прочее — разность упрощается в число (ноль → #t, иначе #f); иначе unknown
(define (m-numeric-set? s) (every? number? (set->list s)))

(define (m-eq3 a b)
  (cond ((equal? a b) #t)
        ((or (equal? a 'unknown) (equal? b 'unknown)) unknown)
        ((and (number? a) (number? b)) (= a b))
        ((and (tensor? a) (tensor? b))
         (if (equal? (tensor-shape-list a) (tensor-shape-list b))
             (and3-all (map2 m-eq3 (vector->list (tensor-data a)) (vector->list (tensor-data b))))
             #f))
        ((and (set? a) (set? b)) (if (and (m-numeric-set? a) (m-numeric-set? b)) #f unknown))
        ((or (object? a) (object? b)) unknown)
        ((or (equal? (type-of a) 'string) (equal? (type-of b) 'string)
             (equal? (type-of a) 'bool) (equal? (type-of b) 'bool))
         #f)
        (else
         (let ((d (simplify (list '- a b))))
           (cond ((number? d) (= d 0))
                 (else unknown))))))

; знак разности для порядковых отношений; не вещественное/нечисловое — unknown
(define (m-order3 h a b)
  (if (or (object? a) (object? b) (equal? (type-of a) 'string) (equal? (type-of b) 'string)
          (equal? (type-of a) 'bool) (equal? (type-of b) 'bool))
      (error (string-append "сравнение " (to-string h) ": ожидаются числа или выражения"))
      (cond ((and (m-real? a) (m-real? b))                       ; вещественные числа — прямое сравнение (быстро)
             (cond ((equal? h '<) (< a b)) ((equal? h '>) (> a b)) ((equal? h '<=) (<= a b)) (else (>= a b))))
            ((equal? h '<) (positive? (simplify (list '- b a))))
            ((equal? h '>) (positive? (simplify (list '- a b))))
            ((equal? h '<=) (nonnegative? (simplify (list '- b a))))
            (else (nonnegative? (simplify (list '- a b)))))))

; отношение над значениями, когда быстрый путь (два вещественных числа) не подошёл
(define (m-rel-slow h a b)
  (let ((r (cond ((equal? h '=) (m-eq3 a b))
                 ((equal? h '/=) (not3 (m-eq3 a b)))
                 (else (m-order3 h a b)))))
    (if (known? r) r (list h a b))))

; ---------- векторы, матрицы ----------

(define (m-stack ts)
  (let ((sh (tensor-shape-list (car ts))))
    (if (every? (lambda (t) (equal? (tensor-shape-list t) sh)) ts)
        (tensor-from-flat (cons (length ts) sh)
                          (append-map (lambda (t) (vector->list (tensor-data t))) ts))
        (error "матрица: вложенные векторы разной формы"))))

; вектор из списка значений; пустой список — пустой вектор [] (форма (0))
(define (m-make-vector vals)
  (cond ((null? vals) (tensor-raw (list 0) (vector)))
        ((every? tensor? vals) (m-stack vals))
        ((any? tensor? vals) (error "вектор: смесь вложенных векторов и скаляров"))
        (else (tensor-from-flat (list (length vals)) vals))))

; ---------- функции над векторами: first, rest, last, reverse, append, dimension, position ----------

(define (m-vec? v) (and (tensor? v) (= (length (tensor-shape-list v)) 1)))

; элементы вектора (строки матрицы), множества — списком
(define (m-items v)
  (cond ((m-vec? v) (vector->list (tensor-data v)))
        ((tensor? v) (map (lambda (i) (tref v i)) (range (car (tensor-shape-list v)))))
        ((set? v) (set->list v))
        (else (error "ожидается вектор или множество"))))

(define (m-need-vec who vals)
  (if (and (= (length vals) 1) (m-vec? (car vals)))
      (car vals)
      (error (string-append who ": ожидается один вектор"))))

(define (m-first vals)
  (let ((items (m-items (m-need-vec "first" vals))))
    (if (null? items) (error "first: пустой вектор") (car items))))
(define (m-last vals)
  (let ((items (m-items (m-need-vec "last" vals))))
    (if (null? items) (error "last: пустой вектор") (last items))))
(define (m-rest vals)
  (let ((items (m-items (m-need-vec "rest" vals))))
    (if (null? items) (error "rest: пустой вектор") (m-make-vector (cdr items)))))
(define (m-reverse vals) (m-make-vector (reverse (m-items (m-need-vec "reverse" vals)))))
(define (m-append vals)
  (if (every? m-vec? vals)
      (m-make-vector (apply append (map m-items vals)))
      (error "append: ожидаются векторы")))

; dimension(v) — длина вектора; для матрицы — вектор [строки, столбцы]; для множества — число элементов
(define (m-dimension vals)
  (let ((v (if (= (length vals) 1) (car vals) (error "dimension: ожидается один аргумент"))))
    (cond ((m-vec? v) (car (tensor-shape-list v)))
          ((tensor? v) (m-make-vector (tensor-shape-list v)))
          ((set? v) (card v))
          (else (error "dimension: ожидается вектор, матрица или множество")))))

(define (m-pos x items i)
  (cond ((null? items) 0)
        ((m-same? x (car items)) i)
        (else (m-pos x (cdr items) (+ i 1)))))
; position(x, v) — номер (с 1) первого элемента, равного x; 0, если нет
(define (m-position vals)
  (if (and (= (length vals) 2) (m-vec? (cadr vals)))
      (m-pos (car vals) (m-items (cadr vals)) 1)
      (error "position: ожидается position(x, вектор)")))

; ---------- итераторы: vector, sum, product, select, iterate, iterates ----------
; Переменная итератора k — локальная (параметр lambda тела): глобальное k не используется и не портится.
; Тело e компилируется в (lambda (k) e) и вычисляется для каждого значения k.

(define (m-range-acc k n step acc cnt)
  (cond ((> cnt *m-loop-limit*) (error "диапазон слишком велик (больше лимита set_loop_limit)"))
        ((if (> step 0) (> k n) (< k n)) (reverse acc))
        (else (m-range-acc (+ k step) n step (cons k acc) (+ cnt 1)))))
(define (m-range-list m n step)
  (if (= step 0) (error "шаг диапазона равен нулю") (m-range-acc m n step '() 0)))

; источник значений k по вычисленным хвостовым аргументам: (n) — 1..n; (m n) — m..n; (m n step); (v) — элементы вектора/множества.
; результат: (#t . список значений) или (#f . аргументы) — границы не числа (символьные)
(define (m-iter-source vals)
  (let ((n (length vals)))
    (cond ((and (= n 1) (or (tensor? (car vals)) (set? (car vals)))) (cons #t (m-items (car vals))))
          ((and (= n 1) (m-real? (car vals))) (cons #t (m-range-list 1 (car vals) 1)))
          ((and (= n 2) (every? m-real? vals)) (cons #t (m-range-list (car vals) (cadr vals) 1)))
          ((and (= n 3) (every? m-real? vals)) (cons #t (m-range-list (car vals) (cadr vals) (caddr vals))))
          (else (cons #f vals)))))

(define (m-fold-items h items)
  (if (equal? h 'sum)
      (cond ((null? items) 0) ((null? (cdr items)) (car items)) (else (m-arith '+ items)))
      (cond ((null? items) 1) ((null? (cdr items)) (car items)) (else (m-arith '* items)))))

(define (m-same? a b) (or (equal? a b) (true? (m-eq3 a b))))

(define (m-iter-shape-ok? h n)
  (cond ((equal? h 'iterate) (or (= n 3) (= n 4)))
        ((equal? h 'iterates) (= n 4))
        (else (and (>= n 3) (<= n 5)))))

; vector/select/sum/product: f — тело (lambda (k) ...), partial — для символьных границ sum/product: (lambda () выражение
; с подставленными значениями), k — имя переменной, vals — вычисленные границы
(define (m-iter-run h f partial k vals)
  (let ((src (m-iter-source vals)))
    (cond ((not (car src))
           ; символьные границы: sum — символьное суммирование (21l.1, каскад L0–L2);
           ; product — символьное произведение (21l.8); иные итераторы — ошибка
           (cond ((and (equal? h 'sum)
                       (or (= (length vals) 2) (= (length vals) 3)))
                  (apply sum-symbolic (cons (partial) (cons k vals))))
                 ((and (equal? h 'product)
                       (or (= (length vals) 2) (= (length vals) 3)))
                  (apply product-symbolic (cons (partial) (cons k vals))))
                 ((member? h '(sum product))
                  (cons h (cons (partial) (cons k (cdr src)))))
                 (else (error (string-append (to-string h) ": границы — числа, либо вектор или множество")))))
          ((equal? h 'vector) (m-make-vector (map f (cdr src))))
          ((equal? h 'select) (m-make-vector (filter (lambda (v) (true? (f v))) (cdr src))))
          (else (m-fold-items h (map f (cdr src)))))))

(define (m-iter-n f v n)
  (if (<= n 0) v (m-iter-n f (f v) (- n 1))))
(define (m-iters-acc f v n acc)
  (if (<= n 0)
      (reverse (cons v acc))
      (m-iters-acc f (f v) (- n 1) (cons v acc))))
; до неподвижной точки: значение не меняется (после упрощения); предохранитель — лимит итераций
(define (m-iter-fix f v i limit)
  (let ((nx (f v)))
    (cond ((m-same? v nx) nx)
          ((>= i limit) (error (string-append "iterate: неподвижная точка не найдена за " (to-string limit)
                                              " итераций (set_loop_limit(n) меняет лимит)")))
          (else (m-iter-fix f nx (+ i 1) limit)))))

(define (m-it-iterate h f x0 n)
  (cond ((equal? h 'iterates)
         (if (and (integer? n) (>= n 0))
             (m-make-vector (m-iters-acc f x0 n '()))
             (error "iterates: число шагов — неотрицательное целое")))
        ((equal? n 'none) (m-iter-fix f x0 0 *m-loop-limit*))
        ((and (integer? n) (>= n 0)) (m-iter-n f x0 n))
        (else (error "iterate: число шагов — неотрицательное целое"))))

; ---------- факториал ----------

(define (m-fact n acc) (if (< n 2) acc (m-fact (- n 1) (* acc n))))
(define (factorial n)
  (cond ((and (integer? n) (>= n 0)) (m-fact n 1))
        ((integer? n) (error "factorial: аргумент — неотрицательное целое"))
        (else (list 'factorial n))))

; ---------- комбинаторные головы (шаг 21l.0) ----------
; binomial(n, k), gamma(x), psi(x[, m]), harmonic(n[, m]), bernoulli(n[, x]), rf(a, k), ff(a, k).
; Целые/рациональные аргументы упрощатель (Simplify.combinatorValue) сворачивает точно;
; float — досчитываем eval-num (в simplify числовые значения этих голов не пишутся — точность);
; символьные аргументы — невычисленная форма (правила rules.lisp).

; если simplify оставил форму (head ...) и все аргументы — числа (float), пробуем eval-num
(define (m-comb-num head vals)
  (let ((r (m-simp (cons head vals))))
    (if (and (list? r) (not (null? r)) (equal? (car r) head)
             (every? number? (cdr r)))
        (let ((n (eval-num r)))
          (if (number? n) n r))
        r)))

(define (m-comb-arity who vals lo hi)
  (if (not (and (>= (length vals) lo) (<= (length vals) hi)))
      (error (string-append who ": неверное число аргументов"))
      #t))

; шаг PL: polylog(s, x), lambert_w(x) — от точных аргументов символьно (правила rules.lisp), от float — число
; (polylog-num / lambert-w-num: x ≤ 1 для polylog, x ≥ −1/e для lambert_w; иначе значение комплексное — форма остаётся)
(define (m-sf-num head vals f)
  (let ((r (m-simp (cons head vals))))
    (if (and (pair? r) (equal? (car r) head) (every? number? (cdr r))
             (any? (lambda (a) (equal? (type-of a) 'float)) (cdr r)))
        (or (apply f (cdr r)) r)
        r)))
(define (m-polylog vals)
  (m-comb-arity "polylog" vals 2 2)
  (m-sf-num 'polylog vals polylog-num))
(define (m-lambert-w vals)
  (m-comb-arity "lambert_w" vals 1 1)
  (m-sf-num 'lambert_w vals lambert-w-num))

(define (m-binomial vals)
  (m-comb-arity "binomial" vals 2 2)
  (m-comb-num 'binomial vals))
(define (m-gamma vals)
  (m-comb-arity "gamma" vals 1 1)
  (m-comb-num 'gamma vals))
(define (m-psi vals)
  (m-comb-arity "psi" vals 1 2)
  (m-comb-num 'psi vals))
(define (m-harmonic vals)
  (m-comb-arity "harmonic" vals 1 2)
  (m-comb-num 'harmonic vals))
(define (m-bernoulli vals)
  (m-comb-arity "bernoulli" vals 1 2)
  (if (= (length vals) 1) (m-comb-num 'bernoulli vals) (m-simp (cons 'bernoulli vals))))
(define (m-rf vals)
  (m-comb-arity "rf" vals 2 2)
  (m-comb-num 'rf vals))
(define (m-ff vals)
  (m-comb-arity "ff" vals 2 2)
  (m-comb-num 'ff vals))

; A2.2: puiseux(F, x, y, n) → вектор ветвей (q ((коэф показатель) …)) ряда Ньютона–Пюизё
(define (m-puiseux vals)
  (if (not (= (length vals) 4))
      (error "puiseux: ожидается puiseux(F, x, y, n)")
      (m-list->vector (apply puiseux vals))))


; ---------- DF.2: дифференциальные формы (forms.lisp) ----------
; формы — выражения с dx, dy, …; переменные — последний аргумент-вектор; результат — выражение
(define (m-fm-args name n vals)
  (if (not (= (length vals) n))
      (error (string-append name ": неверное число аргументов (ожидается " (to-string n) ")"))
      #t))
(define (m-wedge vals)
  ; без вектора переменных — формальная запись (wedge a b …) без перестановок (в языке `*` коммутативно: dz*dx станет dx*dz)
  (if (not (tensor? (car (reverse vals))))
      (cons 'wedge vals)
      (let ((vars (m-tolist (car (reverse vals)))))
        (form->expr (apply wedge (map (lambda (a) (form a vars)) (butlast vals)))))))
(define (m-extd vals)
  (m-fm-args "extd" 2 vals)
  (form->expr (form-d (form (car vals) (m-tolist (cadr vals))))))
(define (m-pullback vals)
  (m-fm-args "pullback" 4 vals)
  (form->expr (form-pullback (form (car vals) (m-tolist (cadr vals))) (m-tolist (caddr vals)) (m-tolist (cadddr-of vals)))))
(define (cadddr-of l) (car (cdr (cdr (cdr l)))))
(define (m-hodge vals)
  (m-fm-args "hodge" 2 vals)
  (form->expr (form-hodge (form (car vals) (m-tolist (cadr vals))))))
(define (m-interior vals)
  (m-fm-args "interior" 3 vals)
  (form->expr (form-interior (m-tolist (car vals)) (form (cadr vals) (m-tolist (caddr vals))))))
(define (m-grad vals)
  (m-fm-args "grad" 2 vals)
  (m-list->vector (vf-grad (car vals) (m-tolist (cadr vals)))))
(define (m-div vals)
  (m-fm-args "div" 2 vals)
  (vf-div (m-tolist (car vals)) (m-tolist (cadr vals))))
(define (m-curl vals)
  (m-fm-args "curl" 2 vals)
  (let* ((F (m-tolist (car vals))) (vars (m-tolist (cadr vals)))
         (r (vf-curl F vars)))
    ; Д5 (WASM.6a): в ℝ² ротор — скалярное выражение, а не вектор; вектор — только в ℝ³
    (if (and (= (length vars) 3) (list? r)) (m-list->vector r) r)))
(define (m-laplacian vals)
  (m-fm-args "laplacian" 2 vals)
  (vf-laplacian (car vals) (m-tolist (cadr vals))))
(define (m-potential vals)
  (m-fm-args "potential" 2 vals)
  (vf-potential (m-tolist (car vals)) (m-tolist (cadr vals))))
(define (m-vector-potential vals)
  (m-fm-args "vector_potential" 2 vals)
  (let ((r (vf-vector-potential (m-tolist (car vals)) (m-tolist (cadr vals)))))
    (if r (m-list->vector r) #f)))
(define (m-form-potential vals)
  (m-fm-args "form_potential" 2 vals)
  (let ((r (form-potential (form (car vals) (m-tolist (cadr vals))))))
    (if r (form->expr r) #f)))
; ---------- MINT.a: кратные интегралы, замена переменных, интегралы первого рода (multiint.lisp) ----------
; integrate(f, x, a, b) — как прежде; integrate(f, [x, a, b], [y, c, d], …) — кратный (первый список — внешний)
(define (m-integrate vals)
  (if (and (pair? vals) (pair? (cdr vals)) (tensor? (cadr vals)))
      (integrate-multi (car vals) (map m-tolist (cdr vals)))
      (m-simp (apply integrate vals))))
; integrate_change(f, polar | cylindrical | spherical | [x = e₁, y = e₂, …], [u, a, b], [v, c, d], …)
(define (m-integrate-change vals)
  (if (< (length vals) 3)
      (error "integrate_change: ожидается integrate_change(f, polar, [r, 0, 1], [t, 0, 2*pi])")
      (integrate-change (car vals) (m-tolist (cadr vals)) (map m-tolist (cddr vals)))))
(define (m-line-integral vals)
  (if (not (= (length vals) 4))
      (error "line_integral: ожидается line_integral(f, [x, y, …], [φ₁, φ₂, …], [t, a, b])")
      (line-integral (car vals) (m-tolist (cadr vals)) (m-tolist (caddr vals)) (m-tolist (cadddr-of vals)))))
(define (m-arc-length vals)
  (if (not (= (length vals) 2))
      (error "arc_length: ожидается arc_length([φ₁, φ₂, …], [t, a, b])")
      (arc-length (m-tolist (car vals)) (m-tolist (cadr vals)))))
(define (m-surface-integral vals)
  (if (not (= (length vals) 5))
      (error "surface_integral: ожидается surface_integral(f, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d])")
      (surface-integral (car vals) (m-tolist (cadr vals)) (m-tolist (caddr vals))
                        (m-tolist (cadddr-of vals)) (m-tolist (nth vals 4)))))
(define (m-surface-area vals)
  (if (not (= (length vals) 3))
      (error "surface_area: ожидается surface_area([r₁, r₂, r₃], [u, a, b], [v, c, d])")
      (surface-area (m-tolist (car vals)) (m-tolist (cadr vals)) (m-tolist (caddr vals)))))

; ---------- MINT.b: области, Фубини, проверки Грина / Стокса / Гаусса (multiint.lisp) ----------
; области — списки (между, rect, triangle, disk, annulus); конструкторы region(x, a, b, y, g1, g2), rect_region([x,a,b],[y,c,d]) …
(define (m-region vals)
  (if (not (= (length vals) 6))
      (error "region: ожидается region(x, a, b, y, g1(x), g2(x))")
      (list 'between (list (nth vals 0) (nth vals 1) (nth vals 2)) (list (nth vals 3) (nth vals 4) (nth vals 5)))))
(define (m-rect-region vals)
  (if (not (= (length vals) 2))
      (error "rect_region: ожидается rect_region([x, a, b], [y, c, d])")
      (list 'rect (m-tolist (car vals)) (m-tolist (cadr vals)))))
(define (m-triangle-region vals)
  (if (not (= (length vals) 4))
      (error "triangle_region: ожидается triangle_region([x, y], [x1, y1], [x2, y2], [x3, y3])")
      (cons 'triangle (map m-tolist vals))))
(define (m-disk-region vals)
  (if (not (= (length vals) 3))
      (error "disk_region: ожидается disk_region([x, y], [cx, cy], r)")
      (list 'disk (m-tolist (car vals)) (m-tolist (cadr vals)) (caddr vals))))
(define (m-annulus-region vals)
  (if (not (= (length vals) 4))
      (error "annulus_region: ожидается annulus_region([x, y], [cx, cy], r1, r2)")
      (list 'annulus (m-tolist (car vals)) (m-tolist (cadr vals)) (caddr vals) (cadddr-of vals))))
(define (m-integrate-region vals)
  (if (not (= (length vals) 2))
      (error "integrate_region: ожидается integrate_region(f, область)")
      (m-simp (integrate-region (car vals) (cadr vals)))))
(define (m-check-result r) (m-list->vector r))
; green_check(P, Q, [x, y], [φ₁, φ₂], [t, a, b], область) → [∮, ∬, вердикт]
(define (m-green-check vals)
  (if (not (= (length vals) 6))
      (error "green_check: ожидается green_check(P, Q, [x, y], [φ₁, φ₂], [t, a, b], область)")
      (m-check-result (green-check (car vals) (cadr vals) (m-tolist (caddr vals)) (m-tolist (cadddr-of vals))
                                   (m-tolist (nth vals 4)) (nth vals 5)))))
; stokes_check(F, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d], [φ₁, φ₂, φ₃], [t, a, b])
(define (m-stokes-check vals)
  (if (not (= (length vals) 7))
      (error "stokes_check: ожидается stokes_check(F, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d], [φ₁, φ₂, φ₃], [t, a, b])")
      (m-check-result (stokes-surface-check (m-tolist (car vals)) (m-tolist (cadr vals)) (m-tolist (caddr vals))
                                            (m-tolist (cadddr-of vals)) (m-tolist (nth vals 4))
                                            (m-tolist (nth vals 5)) (m-tolist (nth vals 6))))))
; gauss_check(F, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d], spherical, [r, 0, 1], [θ, 0, pi], [φ, 0, 2*pi])
; объём — spherical | cylindrical и три диапазона, либо три диапазона x, y, z (первый внешний)
(define (m-gauss-check vals)
  (if (not (and (>= (length vals) 8) (<= (length vals) 9)))
      (error "gauss_check: ожидается gauss_check(F, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d], spherical, [r, 0, 1], [θ, 0, pi], [φ, 0, 2*pi])")
      (let ((rest (drop vals 5)))
        (m-check-result (gauss-check (m-tolist (car vals)) (m-tolist (cadr vals)) (m-tolist (caddr vals))
                                     (m-tolist (cadddr-of vals)) (m-tolist (nth vals 4))
                                     (if (symbol? (car rest))
                                         (cons (car rest) (map m-tolist (cdr rest)))
                                         (map m-tolist rest)))))))

; ---------- PROB: вероятность и статистика (prob.lisp) ----------
; распределения — выражения normal_dist(0, 1) …; данные выборки — векторы (→ списки), ответы-списки → векторы
(define (m-pb-args name n vals)
  (if (not (= (length vals) n))
      (error (string-append name ": неверное число аргументов (ожидается " (to-string n) ")"))
      (map m-tolist vals)))
(define (m-pb-vec l) (m-list->vector l))
; table_dist([значения], [вероятности]) — хранится с векторами (печать table_dist([…], […]))
(define (m-table-dist vals)
  (let ((d (apply table-dist (m-pb-args "table_dist" 2 vals))))
    (list 'table_dist (m-list->vector (cadr d)) (m-list->vector (caddr d)))))
; mean(d) — среднее распределения, mean(вектор) — выборочное среднее; variance/stddev выборки — только sample_*
(define (m-mean vals)
  (let ((a (m-pb-args "mean" 1 vals)))
    (if (dist? (car a)) (dist-mean (car a)) (sample-mean (car a)))))
(define (m-variance vals)
  (let ((a (m-pb-args "variance" 1 vals)))
    (if (dist? (car a)) (dist-variance (car a))
        (error "variance: для выборки используйте sample_variance (несмещённая, n − 1)"))))
(define (m-stddev vals)
  (let ((a (m-pb-args "stddev" 1 vals)))
    (if (dist? (car a)) (dist-stddev (car a))
        (error "stddev: для выборки используйте sample_stddev (несмещённая, n − 1)"))))
(define (m-pdf vals) (apply dist-pdf (m-pb-args "pdf" 2 vals)))
(define (m-cdf vals) (apply dist-cdf (m-pb-args "cdf" 2 vals)))
(define (m-prob vals) (apply dist-prob (m-pb-args "prob" 3 vals)))
(define (m-mgf vals) (apply dist-mgf (m-pb-args "mgf" 2 vals)))
(define (m-moment vals) (apply dist-moment (m-pb-args "moment" 2 vals)))
(define (m-quantile vals) (apply quantile-dist (m-pb-args "quantile" 2 vals)))
(define (m-expectation vals)
  (let ((a (m-pb-args "expectation" 3 vals))) (dist-expectation (car a) (cadr a) (caddr a))))
(define (m-dist-support vals) (m-pb-vec (cdr (apply dist-support (m-pb-args "dist_support" 1 vals)))))
(define (m-sample-mean vals) (apply sample-mean (m-pb-args "sample_mean" 1 vals)))
(define (m-sample-variance vals) (apply sample-variance (m-pb-args "sample_variance" 1 vals)))
(define (m-sample-stddev vals) (apply sample-stddev (m-pb-args "sample_stddev" 1 vals)))
(define (m-median vals) (apply sample-median (m-pb-args "median" 1 vals)))
(define (m-quantile-sample vals) (apply quantile-sample (m-pb-args "quantile_sample" 2 vals)))
(define (m-covariance vals) (apply sample-covariance (m-pb-args "covariance" 2 vals)))
(define (m-correlation vals) (apply sample-correlation (m-pb-args "correlation" 2 vals)))
(define (m-linear-regression vals) (m-pb-vec (apply linear-regression (m-pb-args "linear_regression" 2 vals))))
(define (m-frequencies vals)
  (m-pb-vec (map m-pb-vec (apply frequencies (m-pb-args "frequencies" 1 vals)))))
(define (m-bayes vals) (m-pb-vec (apply bayes-posterior (m-pb-args "bayes" 2 vals))))
(define (m-total-probability vals) (apply total-probability (m-pb-args "total_probability" 2 vals)))

; ---------- PROB.b: математическая статистика (stats.lisp) ----------
; запись-ответ — список пар (ключ значение) → вектор пар [[ключ, значение], …]; списки чисел в значениях — векторы
(define (m-st-vec v)
  (if (and (pair? v) (list? v))
      (if (and (pair? (car v)) (every? (lambda (r) (and (list? r) (every? number? r))) v))
          (tensor-from-flat (list (length v) (length (car v))) (apply append v))     ; матрица (expected)
          (m-list->vector (map m-st-vec v)))
      v))
(define (m-st-record r)
  (m-list->vector (map (lambda (kv)
                         (m-list->vector (list (car kv) (if (member? (car kv) '(interval df quantile expected)) (m-st-vec (cadr kv)) (cadr kv)))))
                       r)))
(define (m-st-call name lo hi f vals)
  (if (or (< (length vals) lo) (> (length vals) hi))
      (error (string-append name ": неверное число аргументов (ожидается " (to-string lo) (if (= lo hi) "" (string-append "…" (to-string hi))) ")"))
      (m-st-record (apply f (map m-tolist vals)))))
(define (m-cdf-num vals) (apply dist-cdf-num (m-pb-args "cdf_num" 2 vals)))
(define (m-quantile-bounds vals) (m-pb-vec (apply dist-quantile-bounds (m-pb-args "quantile_bounds" 2 vals))))
(define (m-mle vals) (m-st-call "mle" 2 3 mle vals))
(define (m-mle-check vals) (apply mle-check (map m-tolist vals)))
(define (m-moments-estimate vals) (m-st-call "moments_estimate" 2 3 moments-estimate vals))
(define (m-confint-mean vals) (m-st-call "confint_mean" 1 2 confint-mean vals))
(define (m-confint-mean-sigma vals) (m-st-call "confint_mean_sigma" 2 3 confint-mean-sigma vals))
(define (m-confint-variance vals) (m-st-call "confint_variance" 1 2 confint-variance vals))
(define (m-confint-proportion vals) (m-st-call "confint_proportion" 2 3 confint-proportion vals))
(define (m-confint-wilson vals) (m-st-call "confint_wilson" 2 3 confint-wilson vals))
(define (m-t-test vals) (m-st-call "t_test" 2 4 t-test vals))
(define (m-t-test-two vals) (m-st-call "t_test_two" 2 4 t-test-two vals))
(define (m-t-test-pooled vals) (m-st-call "t_test_pooled" 2 4 t-test-pooled vals))
(define (m-t-test-paired vals) (m-st-call "t_test_paired" 2 4 t-test-paired vals))
(define (m-chi2-gof vals) (m-st-call "chi2_gof" 2 4 chi2-gof vals))
(define (m-chi2-independence vals) (m-st-call "chi2_independence" 1 3 chi2-independence vals))
(define (m-f-test vals) (m-st-call "f_test" 2 3 f-test-variances vals))
; stat_get(запись, ключ): поле записи-ответа
(define (m-stat-get vals)
  (if (not (= (length vals) 2))
      (error "stat_get: ожидается stat_get(запись, ключ)")
      (let* ((rec (m-tolist (car vals)))
             (ps (filter (lambda (kv) (equal? (car (m-tolist kv)) (cadr vals))) rec)))
        (if (null? ps)
            (error (string-append "stat_get: в записи нет поля " (to-string (cadr vals))))
            (cadr (m-tolist (car ps)))))))

; ---------- DG: дифференциальная геометрия кривых и поверхностей (diffgeom.lisp) ----------
; кривая — вектор компонент, параметр — t, [t, точка] или [t, a, b]; результат-вектор — тензор
(define (m-dg-args name n vals)
  (if (= (length vals) n)
      (map (lambda (a) (if (tensor? a) (tensor->list a) a)) vals)
      (error (string-append name ": неверное число аргументов (ожидается " (to-string n) ")"))))
(define (m-dg-vec l) (m-list->vector l))
(define (m-dg-curve name f vals) (apply f (m-dg-args name 2 vals)))
(define (m-curve-speed vals) (m-simp (m-dg-curve "curve_speed" curve-speed vals)))
(define (m-tangent vals) (m-dg-vec (m-dg-curve "tangent" curve-tangent vals)))
(define (m-normal-vector vals) (m-dg-vec (m-dg-curve "normal_vector" curve-normal vals)))
(define (m-binormal vals) (m-dg-vec (m-dg-curve "binormal" curve-binormal vals)))
(define (m-frenet vals)
  (let ((fr (m-dg-curve "frenet" frenet-frame vals)))
    (tensor-from-flat (list (length fr) (length (car fr))) (apply append fr))))
(define (m-curvature vals) (m-simp (m-dg-curve "curvature" curvature vals)))
(define (m-torsion vals) (m-simp (m-dg-curve "torsion" torsion vals)))
(define (m-curvature-radius vals) (m-simp (m-dg-curve "curvature_radius" curvature-radius vals)))
(define (m-first-form vals) (m-dg-vec (apply first-form (m-dg-args "first_form" 3 vals))))
(define (m-second-form vals) (m-dg-vec (apply second-form (m-dg-args "second_form" 3 vals))))
(define (m-surface-normal vals) (m-dg-vec (apply surface-normal (m-dg-args "surface_normal" 3 vals))))
(define (m-gauss-curvature vals) (m-simp (apply gauss-curvature (m-dg-args "gauss_curvature" 3 vals))))
(define (m-mean-curvature vals) (m-simp (apply mean-curvature (m-dg-args "mean_curvature" 3 vals))))
(define (m-principal-curvatures vals) (m-dg-vec (apply principal-curvatures (m-dg-args "principal_curvatures" 3 vals))))
(define (m-graph-surface vals) (m-dg-vec (apply graph-surface (m-dg-args "graph_surface" 3 vals))))
; gauss_bonnet_check(r, [u, a, b], [v, c, d], χ [, выражение > 0 …]) → [вердикт, ∬ K dA, 2πχ]
(define (m-gauss-bonnet-check vals)
  (if (< (length vals) 4)
      (error "gauss_bonnet_check: ожидается gauss_bonnet_check(r, [u, a, b], [v, c, d], χ)")
      (m-dg-vec (apply gauss-bonnet-check (map (lambda (a) (if (tensor? a) (tensor->list a) a)) vals)))))

; ---------- AG: кривые и поверхности второго порядка (conics.lisp) ----------
; уравнение — выражение или lhs = rhs, переменные — вектор; ответ-запись — вектор пар [ключ, значение] (поле достаёт stat_get)
(define (m-ag-deep v)
  (cond ((tensor? v) (map m-ag-deep (tensor->list v)))
        ((pair? v) (map m-ag-deep v))
        (else v)))
(define (m-ag-args name n vals)
  (if (= (length vals) n)
      (map m-ag-deep vals)
      (error (string-append name ": неверное число аргументов (ожидается " (to-string n) ")"))))
; глубина вложенных списков в значениях записи: точка — 1, список точек и подстановка — 2
(define (m-ag-depth key)
  (cond ((member? key '(center vertex focus point major_axis real_axis axis_direction variables eigenvalues directrices asymptotes lines)) 1)
        ((member? key '(foci substitution rotation)) 2)
        (else 0)))
(define (m-ag-conv v depth)
  (cond ((= depth 0) v)
        ((and (list? v) (not (null? v))) (m-list->vector (map (lambda (x) (m-ag-conv x (- depth 1))) v)))
        (else v)))
(define (m-ag-record r)
  (m-list->vector (map (lambda (kv) (m-list->vector (list (car kv) (m-ag-conv (cadr kv) (m-ag-depth (car kv)))))) r)))
(define (m-classify-conic vals) (apply classify-conic (m-ag-args "classify_conic" 2 vals)))
(define (m-canonical-conic vals) (m-ag-record (apply canonical-conic (m-ag-args "canonical_conic" 2 vals))))
(define (m-conic-elements vals) (m-ag-record (apply conic-elements (m-ag-args "conic_elements" 2 vals))))
(define (m-conic-invariants vals) (m-ag-record (apply conic-invariants (m-ag-args "conic_invariants" 2 vals))))
(define (m-conic-check vals) (apply conic-check (m-ag-args "conic_check" 3 vals)))
(define (m-classify-quadric vals) (apply classify-quadric (m-ag-args "classify_quadric" 2 vals)))
(define (m-canonical-quadric vals) (m-ag-record (apply canonical-quadric (m-ag-args "canonical_quadric" 2 vals))))
(define (m-quadric-invariants vals) (m-ag-record (apply quadric-invariants (m-ag-args "quadric_invariants" 2 vals))))
(define (m-quadric-check vals) (apply quadric-check (m-ag-args "quadric_check" 3 vals)))

; ---------- TEN: метрика и кривизна (curvature.lisp) ----------
; метрика — матрица, координаты — вектор символов; тензоры-ответы возвращаются как есть (индексы с 1 в языке)
(define (m-ten-args name n vals) (m-ag-args name n vals))
(define (m-metric-inverse vals) (apply metric-inverse (m-ten-args "metric_inverse" 2 vals)))
(define (m-christoffel vals) (apply christoffel (m-ten-args "christoffel" 2 vals)))
(define (m-riemann vals) (apply riemann (m-ten-args "riemann" 2 vals)))
(define (m-riemann-lower vals) (apply riemann-lower (m-ten-args "riemann_lower" 2 vals)))
(define (m-ricci vals) (apply ricci (m-ten-args "ricci" 2 vals)))
(define (m-ricci-scalar vals) (apply ricci-scalar (m-ten-args "ricci_scalar" 2 vals)))
(define (m-einstein vals) (apply einstein (m-ten-args "einstein" 2 vals)))
(define (m-kretschmann vals) (apply kretschmann (m-ten-args "kretschmann" 2 vals)))
; covariant_derivative(T, [up, down], g, [x, y]): T — тензор (вектор/матрица…) или скаляр-выражение при пустой вариантности
(define (m-covariant-derivative vals)
  (if (= (length vals) 4)
      (covariant-derivative (car vals) (m-ag-deep (cadr vals)) (m-ag-deep (caddr vals)) (m-ag-deep (nth vals 3)))
      (error "covariant_derivative: ожидается covariant_derivative(T, [up, down, …], g, [координаты])")))
(define (m-geodesic-equations vals) (m-list->vector (apply geodesic-equations (m-ten-args "geodesic_equations" 3 vals))))
; curvature_check(g, [x, y], величина, значение): величина — christoffel, riemann, riemann_lower, ricci, ricci_scalar, einstein, kretschmann
(define (m-curvature-check vals)
  (let ((a (m-ten-args "curvature_check" 4 vals)))
    (curvature-check (car a) (cadr a)
                     (string->symbol (string-join (string-split (to-string (caddr a)) "_") "-"))
                     (nth a 3))))

; ---------- HOM: форма Смита и гомологии (homology.lisp) ----------
; комплекс в языке — вектор матриц: K[k] — матрица k-симплексов (строка — симплекс, вершины по возрастанию)
(define (m-hm-deep v)
  (cond ((tensor? v) (map m-hm-deep (tensor->list v)))
        ((pair? v) (map m-hm-deep v))
        (else v)))
(define (m-hm-n name n vals)
  (if (= (length vals) n)
      vals
      (error (string-append name ": неверное число аргументов (ожидается " (to-string n) ")"))))
(define (m-hm-matrix rows)
  (if (null? rows)
      '()
      (tensor-from-flat (list (length rows) (length (car rows))) (apply append rows))))
(define (m-hm-level simplices k)
  (if (null? simplices)
      '()
      (tensor-from-flat (list (length simplices) (+ k 1)) (apply append simplices))))
(define (m-hm-out K) (m-list->vector (map2 m-hm-level (cdr K) (range (length (cdr K))))))
(define (m-hm-in name v)
  (let ((l (m-hm-deep v)))
    (if (not (and (list? l) (not (null? l)) (every? (lambda (lv) (and (list? lv) (every? list? lv))) l)))
        (error (string-append name ": ожидается комплекс — результат simplicial_complex([[…], …])")))
    (complex-from-simplices (apply append l))))

(define (m-smith-form vals)
  (let ((S (smith-form (m-hm-deep (car (m-hm-n "smith_form" 1 vals))))))
    (m-list->vector (map m-hm-matrix S))))
(define (m-smith-invariants vals)
  (let ((r (smith-invariants (m-hm-deep (car (m-hm-n "smith_invariants" 1 vals))))))
    (if (null? r) r (m-list->vector r))))
(define (m-smith-check vals) (smith-check (m-hm-deep (car (m-hm-n "smith_check" 1 vals)))))
; simplicial_complex([[1,2,3],[3,4,5]]) — матрица симплексов одной размерности;
; simplicial_complex([1,2,3], [3,4]) — симплексы разной размерности отдельными аргументами
(define (m-simplicial-complex vals)
  (if (null? vals) (error "simplicial_complex: ожидаются максимальные симплексы"))
  (let ((l (m-hm-deep vals)))
    (m-hm-out (simplicial-complex
                (if (and (null? (cdr l)) (pair? (car l)) (pair? (car (car l)))) (car l) l)))))
(define (m-faces vals)
  (let ((v (m-hm-n "faces" 2 vals)))
    (let ((K (m-hm-in "faces" (car v))) (k (cadr v)))
      (m-hm-level (complex-faces K k) k))))
(define (m-boundary-matrix vals)
  (let ((v (m-hm-n "boundary_matrix" 2 vals)))
    (m-hm-matrix (boundary-matrix (m-hm-in "boundary_matrix" (car v)) (cadr v)))))
(define (m-homology vals)
  (m-list->vector
    (map (lambda (h) (m-list->vector (cons (car h) (cadr h))))
         (homology (m-hm-in "homology" (car (m-hm-n "homology" 1 vals)))))))
(define (m-homology-text vals) (m-list->vector (homology-text (m-hm-in "homology_text" (car (m-hm-n "homology_text" 1 vals))))))
(define (m-betti vals) (m-list->vector (betti (m-hm-in "betti" (car (m-hm-n "betti" 1 vals))))))
(define (m-euler-characteristic vals)
  (euler-characteristic (m-hm-in "euler_characteristic" (car (m-hm-n "euler_characteristic" 1 vals)))))
(define (m-homology-check vals)
  (m-list->vector (homology-check (m-hm-in "homology_check" (car (m-hm-n "homology_check" 1 vals))))))
(define (m-sphere-complex vals) (m-hm-out (sphere-complex (car (m-hm-n "sphere_complex" 1 vals)))))
(define (m-circle-complex vals) (m-hm-n "circle_complex" 0 vals) (m-hm-out (circle-complex)))
(define (m-disk-complex vals) (m-hm-n "disk_complex" 0 vals) (m-hm-out (disk-complex)))
(define (m-torus-complex vals) (m-hm-n "torus_complex" 0 vals) (m-hm-out (torus-complex)))
(define (m-projective-plane-complex vals) (m-hm-n "projective_plane_complex" 0 vals) (m-hm-out (projective-plane-complex)))
(define (m-klein-bottle-complex vals) (m-hm-n "klein_bottle_complex" 0 vals) (m-hm-out (klein-bottle-complex)))

; ---------- REP: представления конечных групп (repr.lisp) ----------
; группа в языке — вектор [n, g1, g2, …]: gi — образующая списком циклов (точки с 1), например [3, [[1,2]], [[1,2,3]]];
; характер — вектор значений по классам в порядке conjugacy_classes(G)
(define (m-rp-cycles g)
  (let ((cs (perm->cycles g)))
    (if (null? cs) (m-list->vector (list (m-list->vector (list 1))))   ; тождество — [[1]]
        (m-list->vector (map m-list->vector cs)))))
(define (m-rp-group-out G) (m-list->vector (cons (cadr G) (map m-rp-cycles (car G)))))
(define (m-rp-gen n cs)
  (let ((seen (make-hash)))
    (if (not (and (list? cs)
                  (every? (lambda (c)
                            (and (list? c)
                                 (every? (lambda (p)
                                           (and (integer? p) (>= p 1) (<= p n)
                                                (if (hash-has? seen p) #f (begin (hash-set! seen p #t) #t))))
                                         c)))
                          cs)))
        (error "permutation_group: образующая — список непересекающихся циклов с точками 1…n"))
    (perm-mul (perm-from-cycles cs) (perm-id n))))
(define (m-rp-group v)
  (let ((l (m-hm-deep v)))
    (if (not (and (list? l) (pair? l) (integer? (car l)) (>= (car l) 1)))
        (error "ожидается группа: результат symmetric_group(n), permutation_group(n, …) и т. п."))
    (let ((n (car l)))
      (list (map (lambda (cs) (m-rp-gen n cs)) (cdr l)) n))))
(define (m-rp-int name vals)
  (let ((n (car (m-hm-n name 1 vals))))
    (if (and (integer? n) (>= n 1)) n (error (string-append name ": ожидается натуральное число")))))
(define (m-symmetric-group vals) (m-rp-group-out (symmetric-group (m-rp-int "symmetric_group" vals))))
(define (m-alternating-group vals) (m-rp-group-out (alternating-group (m-rp-int "alternating_group" vals))))
(define (m-dihedral-group vals) (m-rp-group-out (dihedral-group (m-rp-int "dihedral_group" vals))))
(define (m-cyclic-group vals) (m-rp-group-out (cyclic-group (m-rp-int "cyclic_group" vals))))
(define (m-quaternion-group vals) (m-hm-n "quaternion_group" 0 vals) (m-rp-group-out (quaternion-group)))
(define (m-permutation-group vals)
  (if (null? vals) (error "permutation_group: ожидается permutation_group(n, образующая, …)"))
  (m-rp-group-out (m-rp-group (map m-hm-deep vals))))
(define (m-group-order vals) (group-order (m-rp-group (car (m-hm-n "group_order" 1 vals)))))
(define (m-conjugacy-classes vals)
  (m-list->vector
    (map (lambda (c) (m-list->vector (list (m-rp-cycles (car c)) (cadr c) (caddr c) (nth c 3))))
         (conjugacy-classes (m-rp-group (car (m-hm-n "conjugacy_classes" 1 vals)))))))
(define (m-rp-table name vals) (character-table (m-rp-group (car vals))))
(define (m-rp-out T chi) (m-list->vector (map (lambda (c) (char-value->expr (char-table-exponent T) c)) chi)))
(define (m-character-table vals)
  (let ((T (m-rp-table "character_table" (m-hm-n "character_table" 1 vals))))
    (m-hm-matrix (char-table->exprs T))))
(define (m-character-degrees vals)
  (m-list->vector (char-table-degrees (m-rp-table "character_degrees" (m-hm-n "character_degrees" 1 vals)))))
(define (m-character-table-check vals)
  (if (or (null? vals) (> (length vals) 2)) (error "character_table_check: ожидается character_table_check(G) или character_table_check(G, таблица)"))
  (let* ((G (m-rp-group (car vals)))
         (tbl (if (null? (cdr vals)) (character-table G) (m-hm-deep (cadr vals)))))
    (m-list->vector (character-table-check G tbl))))
(define (m-rp-chi name n vals)
  (m-hm-n name n vals)
  (let ((T (m-rp-table name vals)))
    (list T (map (lambda (v) (m-hm-deep v)) (cdr vals)))))
(define (m-decompose-character vals)
  (let* ((a (m-rp-chi "decompose_character" 2 vals)) (r (char-decompose (car a) (car (cadr a)))))
    (if (list? r) (m-list->vector r) r)))
(define (m-character-tensor vals)
  (let ((a (m-rp-chi "character_tensor" 3 vals)))
    (m-rp-out (car a) (char-tensor (car a) (car (cadr a)) (cadr (cadr a))))))
(define (m-character-dual vals)
  (let ((a (m-rp-chi "character_dual" 2 vals)))
    (m-rp-out (car a) (char-dual (car a) (car (cadr a))))))
(define (m-character-inner vals)
  (let ((a (m-rp-chi "character_inner" 3 vals)))
    (char-inner (car a) (car (cadr a)) (cadr (cadr a)))))
(define (m-character-sym2 vals)
  (let ((a (m-rp-chi "character_symmetric_square" 2 vals)))
    (m-rp-out (car a) (char-sym2 (car a) (car (cadr a))))))
(define (m-character-alt2 vals)
  (let ((a (m-rp-chi "character_alternating_square" 2 vals)))
    (m-rp-out (car a) (char-alt2 (car a) (car (cadr a))))))
(define (m-permutation-character vals)
  (let ((T (m-rp-table "permutation_character" (m-hm-n "permutation_character" 1 vals))))
    (m-rp-out T (char-permutation T))))
(define (m-regular-character vals)
  (let ((T (m-rp-table "regular_character" (m-hm-n "regular_character" 1 vals))))
    (m-rp-out T (char-regular T))))
(define (m-character-of-representation vals)
  (let ((a (m-rp-chi "character_of_representation" 2 vals)))
    (m-rp-out (car a) (char-from-matrices (car a) (car (cadr a))))))

; ---------- FS: ряды Фурье (fourier.lisp) ----------
(define (m-fs-args name lo hi vals)
  (if (or (< (length vals) lo) (> (length vals) hi))
      (error (string-append name ": неверное число аргументов"))
      (map (lambda (a) (if (tensor? a) (tensor->list a) a)) vals)))
(define (m-fs-out r) (if (list? r) (m-list->vector r) r))
(define (m-fourier-coefficients vals) (m-fs-out (apply fourier-coefficients (m-fs-args "fourier_coefficients" 4 4 vals))))
(define (m-fourier-series vals) (apply fourier-series (m-fs-args "fourier_series" 4 5 vals)))
(define (m-fourier-sine-series vals) (apply fourier-sine-series (m-fs-args "fourier_sine_series" 3 4 vals)))
(define (m-fourier-cosine-series vals) (apply fourier-cosine-series (m-fs-args "fourier_cosine_series" 3 4 vals)))
(define (m-fourier-complex-coefficients vals)
  (m-fs-out (apply fourier-complex-coefficients (m-fs-args "fourier_complex_coefficients" 4 4 vals))))
(define (m-fourier-value-at vals) (apply fourier-value-at (m-fs-args "fourier_value_at" 5 5 vals)))
(define (m-fourier-coefficients-check vals)
  (apply fourier-coefficients-check (m-fs-args "fourier_coefficients_check" 5 5 vals)))
(define (m-parseval-check vals) (m-fs-out (apply parseval-check (m-fs-args "parseval_check" 4 5 vals))))

; ---------- CA: ТФКП (complex-analysis.lisp) ----------
(define (m-residue vals) (apply residue (m-fs-args "residue" 3 3 vals)))
(define (m-laurent vals) (apply laurent (m-fs-args "laurent" 4 4 vals)))
(define (m-singularity-type vals) (m-fs-out (apply singularity-type (m-fs-args "singularity_type" 3 3 vals))))
(define (m-singularities vals) (m-fs-out (apply singularities (m-fs-args "singularities" 2 2 vals))))
(define (m-contour-integral vals) (apply contour-integral (m-fs-args "contour_integral" 4 4 vals)))
(define (m-residue-check vals) (apply residue-check (m-fs-args "residue_check" 4 4 vals)))
(define (m-contour-integral-check vals) (apply contour-integral-check (m-fs-args "contour_integral_check" 5 5 vals)))
(define (m-integral-by-residues vals) (apply integral-by-residues (m-fs-args "integral_by_residues" 2 2 vals)))
(define (m-integral-fourier vals) (apply integral-fourier (m-fs-args "integral_fourier" 2 2 vals)))
(define (m-integral-pv vals) (apply integral-pv (m-fs-args "integral_pv" 2 2 vals)))
(define (m-integral-keyhole vals) (apply integral-keyhole (m-fs-args "integral_keyhole" 2 2 vals)))
(define (m-integral-trig vals) (apply integral-trig (m-fs-args "integral_trig" 4 4 vals)))
(define (m-integral-residues-check vals) (apply integral-residues-check (m-fs-args "integral_residues_check" 5 5 vals)))

; integrate_form(форма, [переменные], [φ₁, …, φₙ], [u, a, b] …)
(define (m-integrate-form vals)
  (if (< (length vals) 4)
      (error "integrate_form: ожидается integrate_form(форма, [переменные], [φ…], [t, a, b] …)")
      (integrate-form (form (car vals) (m-tolist (cadr vals)))
                      (make-chain (m-tolist (caddr vals)) (map m-tolist (cdr (cdr (cdr vals))))))))
