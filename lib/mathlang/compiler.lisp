; mathlang/compiler.lisp — компилятор AST входного математического языка в формы Lisp и входные точки (часть бывшего
; lib\mathlang.lisp, шаг 21h'). Загружается после mathlang/runtime.lisp (времена выполнения m-..., ячейки имён, итераторы).

; Экспорт: точки входа (math-eval, math-eval-tree, load-math) и времена выполнения, на которые раскрывается сгенерированный код
(module mathlang
  (export math-eval math-eval-tree load-math m-set-sym m-trace-simplify m-simplify-steps m-steps m-explain m-step-list m-load m-raw-arg))

; ======================= компилятор AST → формы Lisp (Шаг 21b) =======================
; (m-c ast scope) → форма Lisp, значение которой — значение выражения языка.
; scope — список записей (имя переменная-Lisp владение): локальные переменные (параметры функции, переменные итераторов);
; владение — имя вспомогательной переменной «вектор принадлежит только мне» (только у параметров, которым присваивают v[i])
; или #f. Имена вне scope — глобальные переменные языка (ячейки).

(define *mc-counter* 0)
(define *mc-fn-raise* #f)        ; в компилируемой функции/операторе есть return/exit через raise — нужна граница
(define *mc-loop-raise* #f)      ; в компилируемом цикле есть exit через raise — нужен try
(define *mc-loop-depth* 0)       ; глубина вложенности компилируемых циклов
(define *mc-mode* 'F)            ; F — тело функции/оператор верхнего уровня (return — структурный); L — тело цикла (exit)

(define (m-gen prefix)
  (begin (set! *mc-counter* (+ *mc-counter* 1))
         (string->symbol (string-append "m%" prefix (to-string *mc-counter*)))))
(define (m-lv s) (string->symbol (string-append "m." (to-string s))))
(define (m-ov s) (string->symbol (string-append "mo." (to-string s))))

(define (m-flag-return) (begin (set! *mc-fn-raise* #t) #t))
(define (m-flag-exit)
  (begin (if (> *mc-loop-depth* 0) (set! *mc-loop-raise* #t) (set! *mc-fn-raise* #t)) #t))

(define (m-take l n) (if (or (= n 0) (null? l)) '() (cons (car l) (m-take (cdr l) (- n 1)))))
(define (m-drop l n) (if (or (= n 0) (null? l)) l (m-drop (cdr l) (- n 1))))

; размер формы (число узлов) и подсчёт/подстановка вхождений формы f
(define (m-size x)
  (if (and (list? x) (not (null? x))) (+ 1 (foldl (lambda (a y) (+ a (m-size y))) 0 x)) 1))
(define (m-count-form code f)
  (cond ((equal? code f) 1)
        ((and (list? code) (not (null? code))) (foldl (lambda (acc x) (+ acc (m-count-form x f))) 0 code))
        (else 0)))
(define (m-subst-form code f repl)
  (cond ((equal? code f) repl)
        ((and (list? code) (not (null? code))) (map (lambda (x) (m-subst-form x f repl)) code))
        (else code)))

; форма-константа: не требует временной переменной
(define (m-const-code? c)
  (or (number? c) (equal? (type-of c) 'string) (equal? c #t) (equal? c #f)
      (and (list? c) (not (null? c)) (equal? (car c) 'quote))))

; ---------- имена ----------

; чтение глобальной переменной: быстрый путь — значение «замкнутой» переменной (m-gread), иначе m-gslow
(define (m-c-gread s)
  (let ((c (m-cell s)) (v (m-gen "v")))
    `(let ((,v (m-gread ,c))) (if (vector? ,v) (m-gslow ,c (quote ,s)) ,v))))

; чтение глобальной переменной в v[i]: вектор не «выдаётся наружу», признак владения не снимается
(define (m-c-gread-idx s)
  (let ((c (m-cell s)) (v (m-gen "v")))
    `(let ((,v (m-gread-idx ,c))) (if (vector? ,v) (m-gslow ,c (quote ,s)) ,v))))

; чтение локальной переменной; значение «выдаётся наружу» — вектор больше не принадлежит только переменной
(define (m-c-local-read b)
  (if (caddr b) `(begin (set! ,(caddr b) #f) ,(cadr b)) (cadr b)))

(define (m-c-sym s scope)
  (let ((b (m-lookup s scope)))
    (if (null? b)
        (begin (if (equal? s 'exit) (m-flag-exit) #f)       ; exit без скобок: выход из loop (если имя не присвоено)
               (m-c-gread s))
        (m-c-local-read b))))

(define *m-has-pos* #f)              ; у компилируемого оператора есть позиции в исходнике (см. m-at)
(define (m-c e scope)
  (cond ((symbol? e) (m-c-sym e scope))
        ; (m-at e форма): сгенерированная форма наследует позицию формы AST (строка .mth в стеке ошибок);
        ; только если оператор прочитан с позициями (флаг ставит m-compile-top) — иначе лишний вызов на каждый узел
        ((and (list? e) (not (null? e))) (if *m-has-pos* (m-at e (m-c-form e scope)) (m-c-form e scope)))
        ((null? e) '(quote ()))
        (else e)))

(define (m-c-list args scope) (map (lambda (a) (m-c a scope)) args))

; ---------- диспетчеризация форм ----------

(define (m-c-form e scope)
  (let ((h (car e)) (args (cdr e)))
    (if (not (symbol? h))
        '(error "некорректная форма (ожидалось имя функции)")
        (let ((k (if (equal? h 'piecewise) 'piecewise (get h 'm-kind))))
          (cond ((null? k) (m-c-call h args scope))
                ((equal? k 'arith) (m-c-arith h args scope))
                ((equal? k 'rel) (m-c-rel h args scope))
                ((equal? k ':=) (m-c-assign args scope))
                ((equal? k 'if) (m-c-if args scope))
                ((equal? k 'm-index) (m-c-index args scope))
                ((equal? k 'prog) (m-c-seq-expr args scope))
                ((equal? k 'loop) (m-c-loop args scope))
                ((equal? k 'and) (m-c-and args scope))
                ((equal? k 'or) (m-c-or args scope))
                ((equal? k 'not) (m-c-not args scope))
                ((equal? k 'return) (begin (m-flag-return) `(m-do-return ,(if (null? args) #f (m-c (car args) scope)))))
                ((equal? k 'exit) (begin (m-flag-exit) `(m-do-exit ,(if (null? args) #f (m-c (car args) scope)))))
                ((equal? k 'm-vector) `(m-make-vector (list ,@(m-c-list args scope))))
                ((equal? k 'm-set) `(list->set (list ,@(m-c-list args scope))))
                ((equal? k ':declare) (m-c-declare args scope))
                ((equal? k ':in) `(in? ,(m-c (car args) scope) ,(m-c-set (cadr args) scope)))
                ((equal? k ':interval) (m-c-interval args scope))
                ((equal? k 'piecewise) (m-c-piecewise args scope))
                ((equal? k 'clear) `(m-clear (quote ,args)))
                ((or (equal? k 'trace_simplify) (equal? k 'simplify_steps)) (m-c-simp-trace k args))
                ((or (equal? k 'steps) (equal? k 'step_list)) (m-c-steps k args scope))
                ((equal? k 'explain) (m-c-explain args scope))
                ((equal? k 'm-raw) `(m-raw-arg (quote ,(car args)) (lambda () ,(m-c (car args) scope))))
                ((equal? k 'load) `(m-load (list ,@(m-c-list args scope))))
                ((and (equal? k 'iter) (not (vref (m-cell h) 4))) (m-c-iter h args scope))
                (else (m-c-call h args scope)))))))

; Шаг 21d: trace_simplify(e) печатает шаги упрощения (как print: в --json — в поле output) и возвращает результат;
; simplify_steps(e) возвращает вектор шагов [имя, до, после]. Выражение НЕ вычисляется (иначе упрощение произошло бы
; до трассировки): берётся как записано, значения присвоенных переменных не подставляются
(define (m-c-simp-trace k args)
  (if (= (length args) 1)
      `(,(if (equal? k 'trace_simplify) 'm-trace-simplify 'm-simplify-steps) (quote ,(car args)))
      `(error ,(string-append (to-string k) ": один аргумент — выражение"))))

(define (m-trace-simplify e)
  (let ((steps (simplify-steps e)))
    (begin (map (lambda (s) (m-print (list (simplify-step-text s #t)))) steps)
           (simplify e))))

(define (m-simplify-steps e)
  (m-make-vector
   (map (lambda (s)
          (if (= (length s) 3)
              (m-make-vector (list (to-string (car s)) (cadr s) (caddr s)))
              (to-string (car s))))
        (simplify-steps e))))

; Шаг S.1: steps(e [, уровень]) — вычислить e с журналом шагов, напечатать дерево (как print: в --json — в поле output),
; вернуть значение e; уровень "brief" (по умолчанию) | "full" | "trace". step_list(e [, уровень]) — шаги как данные:
; вектор записей [путь, rule, заголовок, пояснение, до, после, уровень, скрыто] в порядке обхода (путь "1", "1.1", ...
; задаёт вложенность), уровень по умолчанию "full". Выражение вычисляется (в отличие от trace_simplify) — внутри захвата
; Шаг S.5: третий аргумент — язык заголовков и пояснений: "ru" (по умолчанию) | "en"
(define (m-c-steps k args scope)
  (if (or (null? args) (> (length args) 3))
      `(error ,(string-append (to-string k) ": ожидается " (to-string k) "(выражение [, \"brief\" | \"full\" | \"trace\" [, \"ru\" | \"en\"]])"))
      `(,(if (equal? k 'steps) 'm-steps 'm-step-list)
        (lambda () ,(m-steps-body (car args) scope))
        ,(if (null? (cdr args)) #f (m-c (cadr args) scope))
        ,(if (or (null? (cdr args)) (null? (cddr args))) #f (m-c (caddr args) scope)))))

; Шаг D2a: explain(e [, "ru" | "en"]) — вычислить e с журналом, напечатать дерево ПОПЫТОК
; («стратегия — успех/отказ: причина — мс», повторы ×N; как print — в --json в поле output), вернуть значение e
(define (m-c-explain args scope)
  (if (or (null? args) (> (length args) 2))
      '(error "explain: ожидается explain(выражение [, \"ru\" | \"en\"])")
      `(m-explain (lambda () ,(m-steps-body (car args) scope))
                  ,(if (null? (cdr args)) #f (m-c (cadr args) scope)))))

; Шаг S.2: steps(simplify(e)) — выражение берётся как записано (как в trace_simplify): иначе арифметика языка упростила бы
; его до вызова simplify и шагов не было бы; остальное вычисляется как обычно
; Шаг S.4: то же для limit, series, solve (первый аргумент; уравнение — обе части)
; Шаг S.3: то же для integrate(e, x, ...) и diff(e, x, ...): первый аргумент берётся как записан (иначе шаги начинались бы
; с уже упрощённого выражения: (x+1)/(x-1) пришло бы степенью −1, правило частного не было бы видно). Подстановка значений
; присвоенных имён сохраняется (m-resolve); выражение, где есть что-то кроме арифметики и элементарных функций (функции
; пользователя, векторы, e, i), вычисляется как обычно
(define (m-steps-body e scope)
  (cond ((and (list? e) (= (length e) 2) (equal? (car e) 'simplify))
         `(step-simplify (quote ,(cadr e))))
        ((and (list? e) (>= (length e) 3) (member? (car e) '(integrate diff limit series solve)) (symbol? (caddr e)))
         (m-c (cons (car e) (cons (list 'm-raw (cadr e)) (cddr e))) scope))
        (else (m-c e scope))))

(define m-raw-heads (append '(+ - * / ^ sqrt) (filter (lambda (f) (not (equal? f 'ln))) m-elem-funs)))

(define (m-raw-safe? e)
  (cond ((number? e) #t)
        ((symbol? e) (not (member? e '(e i exit))))
        ((and (list? e) (not (null? e)))
         (and (symbol? (car e)) (member? (car e) m-raw-heads) (every? m-raw-safe? (cdr e))))
        (else #f)))

; времена выполнения формы (m-raw e): e как записано (с подстановкой значений имён) или вычисленное значение (thunk)
; Шаг S.4: уравнение (= l r) из безопасных частей (solve) тоже остаётся как записано
(define (m-raw-arg raw thunk)
  (cond ((m-raw-safe? raw) (m-resolve raw 0))
        ((and (list? raw) (= (length raw) 3) (equal? (car raw) '=) (m-raw-safe? (cadr raw)) (m-raw-safe? (caddr raw)))
         (list '= (m-resolve (cadr raw) 0) (m-resolve (caddr raw) 0)))
        (else (thunk))))

(define (m-step-level l default)
  (cond ((equal? l #f) default)
        ((symbol? l) l)
        ((equal? (type-of l) 'string) (string->symbol l))
        (else (error "steps: уровень — \"brief\", \"full\" или \"trace\", получено" l))))

(define (m-steps-lang lang)
  (cond ((equal? lang #f) 'ru)
        ((symbol? lang) lang)
        ((equal? (type-of lang) 'string) (string->symbol lang))
        (else (error "steps: язык — \"ru\" или \"en\", получено" lang))))

(define (m-steps thunk level lang)
  (let* ((lg (m-steps-lang lang))
         (r (capture-step-log thunk (m-step-level level 'brief) lg)))
    (begin (m-print (list (steps-text (cadr r) (caddr r) lg)))
           (car r))))

; Шаг D2a: explain — как steps, но дерево ПОПЫТОК (неудачные рамки with-step видны с причиной и временем)
(define (m-explain thunk lang)
  (let* ((lg (m-steps-lang lang))
         (r (capture-attempts thunk lg)))
    (begin (m-print (list (attempts-text (cadr r) (caddr r) lg)))
           (car r))))

; записи шагов в порядке обхода: (путь шаг) ...
(define (m-step-rows prefix ss i)
  (if (null? ss)
      '()
      (let ((path (if (equal? prefix "") (to-string i) (string-append prefix "." (to-string i)))))
        (append (cons (list path (car ss)) (m-step-rows path (step-children (car ss)) 1))
                (m-step-rows prefix (cdr ss) (+ i 1))))))

(define (m-step-list thunk level lang)
  (let* ((lg (m-steps-lang lang))
         (r (capture-step-log thunk (m-step-level level 'full) lg)))
    (m-make-vector
     (map (lambda (row)
            (let ((s (cadr row)))
              (m-make-vector (list (car row) (to-string (step-rule s)) (step-title s) (step-comment s)
                                   (step-before s) (step-after s) (to-string (step-level s)) (step-omitted s)))))
          (m-step-rows "" (steps-translate lg (cadr r)) 1)))))

; последовательность выражений (prog в позиции выражения)
(define (m-c-seq-expr args scope)
  (cond ((null? args) #f)
        ((null? (cdr args)) (m-c (car args) scope))
        (else `(begin ,@(m-c-list args scope)))))

; ---------- арифметика и отношения ----------

(define (m-and-tests tests)
  (cond ((null? tests) #t) ((null? (cdr tests)) (car tests)) (else (cons 'and tests))))

; два операнда: оба числа — Lisp-операция сразу (результат / и ^, не ставший числом, упрощается), иначе m-arith
(define (m-c-arith h args scope)
  (if (= (length args) 2)
      (let* ((ca (m-c (car args) scope)) (cb (m-c (cadr args) scope))
             (na (number? ca)) (nb (number? cb))
             (va (if na ca (m-gen "a"))) (vb (if nb cb (m-gen "b")))
             (tests (append (if na '() (list `(number? ,va))) (if nb '() (list `(number? ,vb)))))
             (r (m-gen "r"))
             (fast (if (member? h '(+ - * /))                  ; два числа: результат всегда число (деление на 0 — ошибка)
                       `(,h ,va ,vb)
                       `(let ((,r (,h ,va ,vb))) (if (number? ,r) ,r (m-arith-fin ,r)))))
             (body `(if ,(m-and-tests tests) ,fast (m-arith (quote ,h) (list ,va ,vb))))
             (binds (append (if na '() (list (list va ca))) (if nb '() (list (list vb cb))))))
        (if (null? binds) body `(let ,binds ,body)))
      `(m-arith (quote ,h) (list ,@(m-c-list args scope)))))

(define (m-c-rel h args scope)
  (if (not (= (length args) 2))
      '(error "отношение: ожидается два операнда")
      (let* ((ca (m-c (car args) scope)) (cb (m-c (cadr args) scope))
             (na (m-real-literal? ca)) (nb (m-real-literal? cb))
             (va (if na ca (m-gen "a"))) (vb (if nb cb (m-gen "b")))
             (tests (append (if na '() (list `(m-real? ,va))) (if nb '() (list `(m-real? ,vb)))))
             (fast (cond ((equal? h '=) `(= ,va ,vb))
                         ((equal? h '/=) `(not (= ,va ,vb)))
                         (else `(,h ,va ,vb))))
             (body `(if ,(m-and-tests tests) ,fast (m-rel-slow (quote ,h) ,va ,vb)))
             (binds (append (if na '() (list (list va ca))) (if nb '() (list (list vb cb))))))
        (if (null? binds) body `(let ,binds ,body)))))

(define (m-real-literal? c) (and (number? c) (m-real? c)))

; ---------- условие и логика ----------

; if(c, a) — без else: при ложном c значение false; if(c, a, b); if(c, a, b, u) — u при неопределённом условии
(define (m-c-if args scope)
  (let ((n (length args)))
    (if (or (< n 2) (> n 4))
        '(error "if: ожидается if(условие, then[, else[, unknown]])")
        (let ((c (m-gen "c")))
          `(let ((,c ,(m-c (car args) scope)))
             (cond ((equal? ,c #t) ,(m-c (cadr args) scope))
                   ((equal? ,c #f) ,(if (>= n 3) (m-c (caddr args) scope) #f))
                   (else ,(m-c-if-unknown c args scope))))))))

; неопределённое условие: ветка u, а без неё — невычисленный if(c, ...) с подставленными значениями
(define (m-c-if-unknown c args scope)
  (if (= (length args) 4)
      (m-c (nth args 3) scope)
      `((lambda () (list (quote if) ,c ,@(map (lambda (a) (m-c-partial a scope)) (cdr args)))))))

; подстановка значений переменных в AST без вычисления вызовов (для невычисленных веток if)
(define (m-c-partial e scope)
  (cond ((symbol? e) (if (equal? e 'exit) '(quote exit) (m-c-sym e scope)))
        ((and (list? e) (not (null? e)) (not (equal? (car e) ':=)))
         `(cons (quote ,(car e)) (list ,@(map (lambda (a) (m-c-partial a scope)) (cdr e)))))
        ((null? e) '(quote ()))
        ((list? e) `(quote ,e))
        (else e)))

; and: false — сразу false; true — пропускаем; прочее копим в acc
(define (m-c-and args scope)
  (let ((acc (m-gen "acc")))
    `(let ((,acc (quote ()))) ,(m-c-and-chain args scope acc))))
(define (m-c-and-chain args scope acc)
  (if (null? args)
      `(m-and-finish (reverse ,acc))
      (let ((v (m-gen "v")))
        `(let ((,v ,(m-c (car args) scope)))
           (if (equal? ,v #f)
               #f
               (begin (if (equal? ,v #t) #f (set! ,acc (cons ,v ,acc)))
                      ,(m-c-and-chain (cdr args) scope acc)))))))

(define (m-c-or args scope)
  (let ((acc (m-gen "acc")))
    `(let ((,acc (quote ()))) ,(m-c-or-chain args scope acc))))
(define (m-c-or-chain args scope acc)
  (if (null? args)
      `(m-or-finish (reverse ,acc))
      (let ((v (m-gen "v")))
        `(let ((,v ,(m-c (car args) scope)))
           (if (equal? ,v #t)
               #t
               (begin (if (equal? ,v #f) #f (set! ,acc (cons ,v ,acc)))
                      ,(m-c-or-chain (cdr args) scope acc)))))))

(define (m-c-not args scope)
  (let ((v (m-gen "v")))
    `(let ((,v ,(m-c (car args) scope)))
       (cond ((equal? ,v #t) #f)
             ((equal? ,v #f) #t)
             (else (list (quote not) ,v))))))

; ---------- множества-аргументы, декларации ----------

; имя положительного/неотрицательного/... интервала, не присвоенное и не локальное — готовый интервал domain.lisp
(define (m-set-sym c d)
  (let ((x (m-gread c)))
    (cond ((not (vector? x)) x)
          ((null? (vref c 2)) (eval d))
          (else (m-gslow c d)))))
(define (m-c-set d scope)
  (cond ((and (symbol? d) (member? d m-interval-names) (null? (m-lookup d scope)))
         `(m-set-sym ,(m-cell d) (quote ,d)))
        (else (m-c (m-as-domain d) scope))))

; Шаг 21d: интервалы. Литералы [a, b), (a, b], (a, b) разбирает парсер: (:interval a b левая правая), флаги — open/closed
; (не вычисляются). Литерал [a, b] — вектор; в позиции ДОМЕНА (правая часть ∈ и :∈, второй аргумент in?(x, D),
; аргументы-домены declare(x, D...)) вектор из двух элементов читается как закрытый интервал
(define (m-c-interval args scope)
  `(interval ,(m-c (car args) scope) ,(m-c (cadr args) scope) (quote ,(caddr args)) (quote ,(nth args 3))))

; Q.2: piecewise((c, e), …) — ветви берутся как записаны (не вычисляются); парсер даёт ветвь как
; (:interval условие выражение open|closed open|closed)
(define (m-c-piecewise-branch b)
  (if (and (list? b) (>= (length b) 3) (equal? (car b) ':interval))
      (list (cadr b) (caddr b))
      (list b #f)))

(define (m-c-piecewise-branches bs)
  (if (null? bs) '()
      (cons (m-c-piecewise-branch (car bs)) (m-c-piecewise-branches (cdr bs)))))

; WASM.6a Д9: условия ВЫЧИСЛЯЮТСЯ (как в if): истинное условие сразу даёт значение ветви, ложные
; отбрасываются; при нерешённом условии остаётся piecewise с этой ветви (условие — вычисленное значение,
; ответы — как записаны). Ветви не вычисляются заранее: они в cond, поэтому невыбранная не считается.
(define (m-c-piecewise args scope)
  (m-c-piecewise-chain args (m-c-piecewise-branches args) scope))

(define (m-c-piecewise-chain args bs scope)
  (if (null? args)
      `(quote undefined)
      (let* ((b (car bs)) (c (m-gen "c")))
        `(let ((,c ,(m-c (car b) scope)))
           (cond ((equal? ,c #t) ,(m-c (cadr b) scope))
                 ((equal? ,c #f) ,(m-c-piecewise-chain (cdr args) (cdr bs) scope))
                 (else (m-piecewise-rest ,c (quote ,(cadr b)) (quote ,(cdr bs)))))))))


(define (m-as-domain d)
  (if (and (m-form? d 'm-vector) (= (length (cdr d)) 2)) (cons 'interval (cdr d)) d))

(define (m-dom-args h args)
  (cond ((and (equal? h 'declare) (not (null? args))) (cons (car args) (map m-as-domain (cdr args))))
        ((and (equal? h 'in?) (= (length args) 2)) (list (car args) (m-as-domain (cadr args))))
        (else args)))

(define (m-c-declare args scope)
  (let ((x (car args)))
    (if (not (symbol? x))
        '(error ":∈: слева ожидалось имя")
        (if (null? (cdr args))
            `(undeclare (quote ,x))          ; «x :∈» без домена — снять декларации
        (let ((d (m-gen "d")))
          `(let ((,d ,(m-c-set (cadr args) scope)))
             (begin (declare (quote ,x) ,d) (list (quote :in) (quote ,x) ,d))))))))

; ---------- присваивание ----------

(define (m-c-assign args scope)
  (let ((lhs (car args)))
    (cond ((null? (cdr args))
           (if (symbol? lhs) `(m-clear-name (quote ,lhs)) '(error ":=: слева ожидалось имя, f(параметры) или v[i]")))
          ((symbol? lhs) (m-c-assign-sym lhs (cadr args) scope))
          ((and (list? lhs) (not (null? lhs)) (equal? (car lhs) 'm-index)) (m-c-assign-elem lhs (cadr args) scope))
          ((and (list? lhs) (not (null? lhs)) (symbol? (car lhs)))
           `(m-define-fun (quote ,(car lhs)) (quote ,(cdr lhs)) (quote ,(cadr args))))
          (else '(error ":=: слева ожидалось имя, f(параметры) или v[i]")))))

; локальная переменная (параметр, переменная итератора) меняется на месте, иначе — глобальная переменная языка
(define (m-c-assign-sym name rhs scope)
  (let ((b (m-lookup name scope)) (v (m-gen "v")) (code (m-c rhs scope)))
    (if (null? b)
        `(let ((,v ,code))
           (if (number? ,v) (m-gset-closed! ,(m-cell name) ,v) (m-gset! ,(m-cell name) (quote ,name) ,v)))
        `(let ((,v ,code))
           (begin (set! ,(cadr b) ,v) ,@(if (caddr b) (list `(set! ,(caddr b) #f)) '()) ,v)))))

; v[i] := e, m[i, j] := e. Индексы и правая часть вычисляются до чтения вектора. Вектор меняется на месте, если
; принадлежит только этой переменной (иначе копируется, и копия переменной принадлежит ей)
(define (m-c-assign-elem lhs rhs scope)
  (let ((name (cadr lhs)))
    (if (not (symbol? name))
        '(error ":=: слева от индекса ожидалось имя вектора")
        (let* ((idxs (cdr (cdr lhs)))
               (ivars (map (lambda (i) (m-gen "i")) idxs))
               (vv (m-gen "v"))
               (b (m-lookup name scope))
               (binds (append (map2 (lambda (iv ic) (list iv (m-c ic scope))) ivars idxs)
                              (list (list vv (m-c rhs scope))))))
          `(let* ,binds
             ,(cond ((null? b)
                     (let ((r (m-gen "r")))
                       `(let ((,r (m-gtset! ,(m-cell name) (quote ,name) ,vv ,@ivars)))
                          (if (vector? ,r) (m-gelem-slow ,r (quote ,name) ,vv (list ,@ivars)) ,r))))
                    ((caddr b)
                     `(begin (if ,(caddr b)
                                 (m-tset ,(cadr b) #f (quote ,name) ,vv ,@ivars)
                                 (begin (set! ,(cadr b) (m-tset ,(cadr b) #t (quote ,name) ,vv ,@ivars))
                                        (set! ,(caddr b) #t)))
                             ,vv))
                    (else
                     `(begin (set! ,(cadr b) (m-tset ,(cadr b) #t (quote ,name) ,vv ,@ivars)) ,vv))))))))

; v[i], m[i, j] — индексы с 1; символьный индекс (или не вектор) — невычисленная форма
(define (m-c-index args scope)
  `(m-ix ,(m-c-index-base (car args) scope) ,@(m-c-list (cdr args) scope)))
(define (m-c-index-base v scope)
  (if (symbol? v)
      (let ((b (m-lookup v scope)))
        (if (null? b) (m-c-gread-idx v) (cadr b)))
      (m-c v scope)))

; ---------- вызовы ----------

; проверка ДО вычисления остальных аргументов; функция языка с тем же именем отключает проверку
(define (m-c-check-arg a role scope)
  (cond ((symbol? a)
         (let ((b (m-lookup a scope)))
           (list (if (null? b)
                     `(m-check-global ,(m-cell a) (quote ,a) ,role)
                     `(m-check-local (quote ,a) ,(cadr b) ,role)))))
        ((and (list? a) (not (null? a)) (equal? (car a) 'm-vector))
         (append-map (lambda (x) (m-c-check-arg x role scope)) (cdr a)))
        (else '())))

(define (m-c-checks h args scope)
  (let ((role (get h 'm-role)))
    (if (and (not (null? role)) (>= (length args) 2) (or (not (equal? h 'subst)) (= (length args) 3)))
        (let ((cks (m-c-check-arg (cadr args) role scope)))
          (if (null? cks) '() (list `(if (vref ,(m-cell h) 4) #f (begin ,@cks #f)))))
        '())))

; аргументы вычисляются по порядку во временные переменные (константы подставляются), k строит форму вызова
(define (m-c-bind-args args scope k)
  (let* ((codes (m-c-list args scope))
         (vars (map (lambda (c) (if (m-const-code? c) c (m-gen "a"))) codes))
         (binds (filter (lambda (p) (not (m-const-code? (cadr p)))) (map2 list vars codes))))
    (if (null? binds) (k vars) `(let ,binds ,(k vars)))))

; вызов функции языка (поздняя привязка через ячейку) или Lisp-функции
(define (m-c-call-body h vars)
  (let* ((n (length vars)) (cell (m-cell h)) (fv (m-gen "fv")) (f (m-gen "f"))
         (user (if (<= n 4)
                   `(let ((,f (vref ,fv ,n))) (if ,f (,f ,@vars) (m-arity-error ,cell ,n)))
                   `(m-ucall-n ,cell ,n (list ,@vars)))))
    `(let ((,fv (vref ,cell 4))) (if ,fv ,user ,(m-c-lisp-call h vars)))))

(define (m-c-lisp-call h vars)
  (let ((al (get h 'm-alias)) (lh (m-lisp-name h)))
    (cond ((not (null? al)) `(,al (list ,@vars)))
          ((equal? (get h 'm-kind) 'elem)
           (if (= (length vars) 1) `(m-elem1 (quote ,h) ,h ,(car vars)) `(m-elem (quote ,h) (list ,@vars))))
          ((m-callable? lh) `(m-simp (,lh ,@vars)))
          (else `(m-call-lisp (quote ,h) (list ,@vars))))))

(define (m-c-call h args0 scope)
  (let* ((args (m-dom-args h args0))
         (checks (m-c-checks h args scope))
         (body (m-c-bind-args args scope (lambda (vars) (m-c-call-body h vars)))))
    (if (null? checks) body `(begin ,@checks ,body))))

; ---------- итераторы ----------

(define (m-c-iter h args scope)
  (let ((n (length args)))
    (cond ((and (member? h '(sum product)) (= n 1))
           `(m-fold-items (quote ,h) (m-items ,(m-c (car args) scope))))
          ((and (m-iter-shape-ok? h n) (symbol? (cadr args))) (m-c-iter-run h args scope))
          (else (m-c-bind-args args scope (lambda (vars) (m-c-call-body h vars)))))))      ; иная форма — обычный вызов

(define (m-c-iter-run h args scope)
  (let* ((body (car args)) (k (cadr args)) (kv (m-lv k))
         (f `(lambda (,kv) ,(m-c body (cons (list k kv #f) scope)))))
    (if (member? h '(iterate iterates))
        `(m-it-iterate (quote ,h) ,f ,(m-c (caddr args) scope)
                       ,(if (= (length args) 4) (m-c (nth args 3) scope) '(quote none)))
        (let ((srcs (m-c-list (cdr (cdr args)) scope))
              (partial (if (member? h '(sum product))
                           `(lambda () ,(m-c-partial body (cons (list k `(quote ,k) #f) scope)))
                           #f)))
          `(m-iter-run (quote ,h) ,f ,partial (quote ,k) (list ,@srcs))))))

; ---------- loop, структурное управление ----------
; В позициях-«операторах» (хвост тела функции/оператора верхнего уровня, оператор тела loop, ветви if в них, prog в них)
; return (режим F) и exit (режим L) — обычные ветвления: m-cs компилирует последовательность операторов с продолжением k
; (форма, выполняемая после последнего оператора; 'none — после последнего оператора значение последовательности — его значение).
; Иначе (return в цикле, exit в аргументе и т. п.) — m-do-return/m-do-exit с raise (и пометка *mc-fn-raise*/*mc-loop-raise*).

(define (m-form? s h) (and (list? s) (not (null? s)) (equal? (car s) h)))
(define (m-exit-stmt? s) (or (equal? s 'exit) (m-form? s 'exit)))
(define (m-ctl-stmt? s) (if (equal? *mc-mode* 'L) (m-exit-stmt? s) (m-form? s 'return)))

; содержит ли оператор структурный return/exit (в позициях, которые разбирает m-cs)
(define (m-has-sctl? s)
  (cond ((m-ctl-stmt? s) #t)
        ((m-form? s 'prog) (any? m-has-sctl? (cdr s)))
        ((and (m-form? s 'if) (>= (length (cdr s)) 2) (<= (length (cdr s)) 4)) (any? m-has-sctl? (cdr (cdr s))))
        (else #f)))

(define (m-cs stmts scope k)
  (cond ((null? stmts) (if (equal? k 'none) #f k))
        ((null? (cdr stmts)) (m-cs-stmt (car stmts) scope k))
        (else
         (let ((s (car stmts)))
           (if (m-has-sctl? s)
               (m-cs-stmt s scope (m-cs (cdr stmts) scope k))
               `(begin ,(m-c s scope) ,(m-cs (cdr stmts) scope k)))))))

(define (m-cs-stmt s scope k)
  (cond ((and (equal? *mc-mode* 'L) (m-exit-stmt? s))
         (if (and (list? s) (not (null? (cdr s)))) (m-c (cadr s) scope) #f))
        ((and (equal? *mc-mode* 'F) (m-form? s 'return))
         (if (null? (cdr s)) #f (m-c (cadr s) scope)))
        ((and (m-form? s 'prog) (m-has-sctl? s)) (m-cs (cdr s) scope k))
        ((and (m-form? s 'if) (m-has-sctl? s)) (m-cs-if (cdr s) scope k))
        (else (if (equal? k 'none) (m-c s scope) `(begin ,(m-c s scope) ,k)))))

(define (m-cs-branch s scope kc)
  (if (m-form? s 'prog) (m-cs (cdr s) scope kc) (m-cs-stmt s scope kc)))

; продолжение k вставляется вместо вхождений (p): если их не больше одного или k мало — подстановкой, иначе — через thunk
(define (m-place-k code p k)
  (if (equal? k 'none)
      code
      (let ((f (list p)))
        (if (or (<= (m-size k) 12) (<= (m-count-form code f) 1))
            (m-subst-form code f k)
            `(let ((,p (lambda () ,k))) ,code)))))

(define (m-cs-if args scope k)
  (let* ((n (length args)) (c (m-gen "c")) (p (m-gen "k"))
         (none (equal? k 'none))
         (kc (if none 'none (list p)))
         (a (m-cs-branch (cadr args) scope kc))
         (b (if (>= n 3) (m-cs-branch (caddr args) scope kc) (if none #f kc)))
         (u (cond ((= n 4) (m-cs-branch (nth args 3) scope kc))
                  (none (m-c-if-unknown c args scope))
                  (else kc)))
         (code (if (equal? b u)
                   `(if (equal? ,c #t) ,a ,b)
                   `(cond ((equal? ,c #t) ,a) ((equal? ,c #f) ,b) (else ,u)))))
    `(let ((,c ,(m-c (car args) scope))) ,(m-place-k code p k))))

; loop(s1, ..., sn) — бесконечный цикл; выход по exit / exit(v) (значение цикла v, иначе false); return выходит из функции.
; Цикл — хвостовая рекурсия; лимит итераций читается при входе в цикл
(define (m-c-loop args scope)
  (if (null? args)
      '(error "loop: ожидается loop(оператор, ...)")
      (let ((lp (m-gen "lp")) (n (m-gen "n")) (lim (m-gen "lim"))
            (saved-raise *mc-loop-raise*) (saved-mode *mc-mode*))
        (begin
          (set! *mc-loop-raise* #f)
          (set! *mc-loop-depth* (+ *mc-loop-depth* 1))
          (set! *mc-mode* 'L)
          (let* ((body (m-cs args scope (list lp (list '+ n 1))))
                 (raised *mc-loop-raise*)
                 (code `(let ((,lim *m-loop-limit*))
                          (letrec ((,lp (lambda (,n) (if (> ,n ,lim) (m-loop-limit-error ,lim) ,body))))
                            (,lp 0)))))
            (begin
              (set! *mc-loop-depth* (- *mc-loop-depth* 1))
              (set! *mc-mode* saved-mode)
              (set! *mc-loop-raise* saved-raise)
              (if raised `(try ,code (lambda (m%e) (m-loop-catch m%e))) code)))))))

; ---------- функции ----------

; имена векторов, которым присваивают элемент (v[i] := e) внутри AST
(define (m-elem-targets e acc)
  (if (and (list? e) (not (null? e)))
      (let ((acc2 (if (and (equal? (car e) ':=) (not (null? (cdr e))) (m-form? (cadr e) 'm-index)
                           (not (null? (cdr (cadr e)))) (symbol? (cadr (cadr e))))
                      (cons (cadr (cadr e)) acc)
                      acc)))
        (foldl (lambda (a x) (m-elem-targets x a)) acc2 e))
      acc))

(define (m-reset-flags)
  (begin (set! *mc-fn-raise* #f) (set! *mc-loop-raise* #f) (set! *mc-loop-depth* 0) (set! *mc-mode* 'F) #t))

; замыкание на каждое допустимое число аргументов: недостающие параметры по умолчанию вычисляются при вызове
; по порядку и видят предыдущие параметры (запись (имя переменная #f) — без признаков владения)
(define (m-arity-lambda params pnames main nv)
  (let ((plain (map (lambda (p) (list p (m-lv p) #f)) pnames)))
    `(lambda ,(map m-lv (m-take pnames nv))
       (let* ,(map (lambda (i)
                     (list (m-lv (nth pnames i))
                           (m-c (caddr (nth params i)) (m-take plain i))))
                   (m-drop (range (length params)) nv))
         (,main ,@(map m-lv pnames))))))

; форма, значение которой — вектор замыканий по числу аргументов (индекс = число аргументов)
(define (m-fun-form params body)
  (let* ((pnames (map m-param-name params))
         (np (length params)) (nr (m-required params))
         (tracked (filter (lambda (p) (member? p (m-elem-targets body '()))) pnames))
         (entries (map (lambda (p) (list p (m-lv p) (if (member? p tracked) (m-ov p) #f))) pnames))
         (main (m-gen "main")))
    (begin
      (m-reset-flags)
      (let* ((code (m-cs (list body) entries 'none))
             (bounded (if *mc-fn-raise* `(m-ctl-boundary (lambda () ,code)) code))
             (owned (if (null? tracked) bounded `(let ,(map (lambda (p) (list (m-ov p) #f)) tracked) ,bounded)))
             (slots (map (lambda (i)
                           (cond ((= i np) main)
                                 ((and (>= i nr) (< i np)) (m-arity-lambda params pnames main i))
                                 (else #f)))
                         (range (if (> (+ np 1) 5) (+ np 1) 5)))))
        `(let ((,main (lambda ,(map m-lv pnames) ,owned))) (vector ,@slots))))))

(define (m-install-fun! cell params body)
  (let ((fv (eval (m-fun-form params body))))
    (begin (vset! cell 4 fv) (vset! cell 5 (length params)) (vset! cell 6 (m-required params))
           (vset! cell 7 params) (vset! cell 8 body)
           #t)))

; ---------- свойства символов для диспетчеризации ----------

(define (m-install-props)
  (begin
    (map (lambda (s) (put s 'm-kind 'arith)) m-arith-ops)
    (map (lambda (s) (put s 'm-kind 'rel)) m-relations)
    (map (lambda (s) (put s 'm-kind 'elem)) m-elem-funs)
    (map (lambda (s) (put s 'm-kind 'iter)) m-iter-forms)
    (map (lambda (s) (put s 'm-kind s))
         '(:= :declare :in if and or not m-vector m-set m-index prog loop return exit clear load
           trace_simplify simplify_steps steps step_list explain :interval m-raw))
    (map (lambda (p) (put (car p) 'm-role (cadr p))) m-var-roles)
    (map (lambda (p) (put (car p) 'm-alias (cadr p))) m-aliases)
    (map (lambda (p) (put (car p) 'm-rename (cadr p))) m-renames)
    #t))
(m-install-props)

; ---------- входные точки ----------

; оператор верхнего уровня: return завершает оператор
(define (m-compile-top ast)
  (begin
    (m-reset-flags)
    (set! *m-has-pos* (m-has-pos? ast))
    (let ((code (m-cs (list ast) '() 'none)))
      (if *mc-fn-raise* `(m-ctl-boundary (lambda () ,code)) code))))

; (math-eval-tree ast) — вычислить один оператор (AST)
(define (math-eval-tree ast) (eval (m-compile-top ast)))

; (math-eval "строка") — программа языка; значение последнего оператора ('() для пустой программы)
(define (m-eval-trees asts) (foldl (lambda (acc a) (math-eval-tree a)) '() asts))
(define (math-eval s) (m-eval-trees (math-read-program s)))

; (load-math "файл.mth") — выполнить файл языка; значение последнего оператора. Ошибка разбора — с именем файла
(define (m-load vals)
  (if (and (= (length vals) 1) (equal? (type-of (car vals)) 'string))
      (load-math (car vals))
      (error "load: ожидается load(\"файл\")")))
(define (load-math path)
  (let ((text (read-text-file path)))
    (m-eval-trees (try (math-read-program text path)
                       (lambda (e) (error (string-append path ": " (error-message e))))))))
