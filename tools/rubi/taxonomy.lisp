; tools/rubi/taxonomy.lisp — RUBI.TAX: семейство/подсемейство правила Rubi по виду правой части.
;
; Разметка — на Lisp (решение пользователя 2026-11-12): читаются те же S-выражения правил, что исполняет
; движок (lib/rubi/rules/*.lisp + *.body.lisp; список файлов — тот, что грузит lib/rubi/engine.lisp), а не
; текст .m. Классификатор — (rubi-rule-family rule) -> (семейство подсемейство признаки); он не зависит от
; печати и файлов, поэтому его можно перенести в движок (метка семейства — основа дерева решений).
;
; Ввод-вывод: Lisp читает файлы (read-text-file, load), но не пишет и не перечисляет каталог; поэтому
; таблицы ПЕЧАТАЮТСЯ в stdout, а в файл их кладёт обёртка tools/rubi/taxonomy-run.mjs (spawn Lisp.exe).
;   node tools/rubi/taxonomy-run.mjs              ; research/rubi/tax/{rules,families,subfamilies}.tsv
;   node tools/rubi/taxonomy-run.mjs --only rules ; одна таблица
;   Lisp.exe tools/rubi/taxonomy.lisp -e "(rubi-tax-run \"rules\")"   ; таблица в stdout
;   Lisp.exe tools/rubi/taxonomy.lisp -e "(rubi-tax-report)"          ; сводка чисел для отчёта
;   Lisp.exe tools/rubi/taxonomy.lisp -e "(rubi-tax-gaps)"            ; пропуски в аналогичных главах
;   Lisp.exe tools/rubi/taxonomy.lisp -e "(rubi-tax-failures \"research/rubi/class2/ids.tsv\")"
;   Lisp.exe tools/rubi/taxonomy.lisp -e "(rubi-tax-sample 50 20261112)"  ; выборка для ручной сверки
; Перенаправлять вывод shell-ом нельзя (правило задания) — только через обёртку.
;
; Семейства: REDUCE (в правой части Int того же вида с изменённым показателем), SUBST (подстановка),
; EXPAND (разложение/расщепление), CONVERT (сведение к другой форме: ActivateTrig, exp-форма), DISPATCH
; (Int[u] -> Int[v] той же сложности, нормализация), BASE (терминальный ответ без Int и спецфункций),
; SPECIAL (терминальный ответ через спецфункции), UNINTEGRABLE (Unintegrable/CannotIntegrate/Integral).

; ---------- общие утилиты работы с формами ----------
(define (rubi-tax-arith? h)
  (or (equal? h '+) (equal? h '*) (equal? h '^) (equal? h '-) (equal? h '/) (equal? h 'list)
      (equal? h 'quote) (equal? h 'derivative) (equal? h 'part)))

; обход выражения без захода в (quote ...)
; элементы списка как узлы (cdr — не выражение, его не отдаём в f)
(define (rubi-tax-walk-elems l f)
  (if (pair? l)
      (begin (rubi-tax-walk (car l) f) (rubi-tax-walk-elems (cdr l) f))
      #t))

(define (rubi-tax-walk e f)
  (if (pair? e)
      (if (equal? (car e) 'quote)
          #t
          (begin (f e) (rubi-tax-walk (car e) f) (rubi-tax-walk-elems (cdr e) f)))
      #t))

; (quote x) -> x: данные правил пишут переменную интегрирования и константы кавычкой
(define (rubi-tax-norm e)
  (cond ((and (pair? e) (equal? (car e) 'quote) (pair? (cdr e)) (null? (cddr e)))
         (if (symbol? (cadr e)) (cadr e) e))
        ((pair? e) (cons (car e) (map rubi-tax-norm (cdr e))))
        (else e)))

(define (rubi-tax-text e) (format "~s" (rubi-tax-norm e)))

; то же, но f видит и атомы (символы, числа)
(define (rubi-tax-walk-all-elems l f)
  (if (pair? l)
      (begin (rubi-tax-walk-all (car l) f) (rubi-tax-walk-all-elems (cdr l) f))
      #t))

(define (rubi-tax-walk-all e f)
  (if (pair? e)
      (if (equal? (car e) 'quote)
          (f e)
          (begin (f e) (rubi-tax-walk-all (car e) f) (rubi-tax-walk-all-elems (cdr e) f)))
      (f e)))

(define (rubi-tax-some pred l)
  (cond ((null? l) #f) ((pred (car l)) #t) (else (rubi-tax-some pred (cdr l)))))

; головы вызовов (без арифметики), в порядке первого появления
(define (rubi-tax-heads e)
  (let ((acc '()))
    (rubi-tax-walk e
      (lambda (x)
        (let ((h (car x)))
          (if (and (symbol? h) (not (rubi-tax-arith? h)) (not (member? h acc)))
              (set! acc (cons h acc))))))
    (reverse acc)))

(define (rubi-tax-int-head? h) (equal? h 'rubi::rubi-int))

; аргументы Int правой части: (rubi::rubi-int u u x) — интегранд повторён, берём первый аргумент
(define (rubi-tax-int-args e)
  (let ((acc '()))
    (rubi-tax-walk e
      (lambda (x) (if (and (rubi-tax-int-head? (car x)) (pair? (cdr x))) (set! acc (cons (cadr x) acc)))))
    (reverse acc)))

(define (rubi-tax-count-int e)
  (let ((n 0))
    (rubi-tax-walk e (lambda (x) (if (rubi-tax-int-head? (car x)) (set! n (+ n 1)))))
    n))

(define (rubi-tax-exponent e)
  (if (and (pair? e) (equal? (car e) '^) (= (length e) 3)) (caddr e) #f))

(define (rubi-tax-base e)
  (if (and (pair? e) (equal? (car e) '^) (= (length e) 3)) (cadr e) #f))

(define (rubi-tax-sum-terms e)
  (if (and (pair? e) (equal? (car e) '+))
      (apply append (map rubi-tax-sum-terms (cdr e)))
      (list e)))

; Int стоит отдельным слагаемым верхнего уровня: интегрирование по частям, а не реккурентность
(define (rubi-tax-has-free-int-term rhs)
  (let ((ts (rubi-tax-sum-terms rhs)))
    (and (> (length ts) 1)
         (rubi-tax-some (lambda (t) (= 0 (rubi-tax-count-int t))) ts))))

; ---------- переменные-показатели образца ----------
(define (rubi-tax-pat-var? s)
  (and (symbol? s) (> (string-length (symbol->string s)) 1)
       (equal? (substring (symbol->string s) 0 1) "?")))

; ?n -> n: в правой части переменные образца записаны без «?» (движок подставляет значения)
(define (rubi-tax-bare s)
  (if (rubi-tax-pat-var? s)
      (let* ((str (symbol->string s)) (n (string-length str)))
        (string->symbol (substring str 1 n)))
      s))

(define (rubi-tax-strip-vars e)
  (cond ((rubi-tax-pat-var? e) (rubi-tax-bare e))
        ((pair? e) (cons (car e) (map rubi-tax-strip-vars (cdr e))))
        (else e)))

; (?n показатель основание): для отсева множителей вида d^(m-1) — это коэффициент, а не индекс интегранда
(define (rubi-tax-exp-vars pat)
  (let ((acc '()))
    (rubi-tax-walk pat
      (lambda (x)
        (let ((exp (rubi-tax-exponent x)))
          (if exp
              (rubi-tax-walk-all exp
                (lambda (y)
                  (if (and (rubi-tax-pat-var? y) (not (assoc y acc)))
                      (set! acc (cons (list y (rubi-tax-strip-vars exp) (rubi-tax-base x)) acc)))))))))
    (reverse acc)))

(define (rubi-tax-var-in? e p)
  (let ((found #f))
    (rubi-tax-walk-all e (lambda (x) (if (equal? x p) (set! found #t))))
    found))

; показатели выражения, где встречается bare-имя p — только у степеней с тем же основанием, что в образце
(define (rubi-tax-exponents-of e p base)
  (let ((acc '()))
    (rubi-tax-walk e
      (lambda (x)
        (let ((exp (rubi-tax-exponent x)))
          (if (and exp (rubi-tax-var-in? exp p)
                   (or (not base) (rubi-tax-match? base (rubi-tax-base x))))
              (set! acc (cons exp acc))))))
    (reverse acc)))

; ---------- структурное сопоставление ----------
(define (rubi-tax-flat op e)
  (if (and (pair? e) (equal? (car e) op))
      (apply append (map (lambda (x) (rubi-tax-flat op x)) (cdr e)))
      (list e)))

(define (rubi-tax-all2 f a b)
  (cond ((null? a) (null? b))
        ((null? b) #f)
        ((f (car a) (car b)) (rubi-tax-all2 f (cdr a) (cdr b)))
        (else #f)))

; мультимножество: каждому элементу образца — свой (ещё не занятый) элемент выражения
(define (rubi-tax-match-bag ps es)
  (if (null? ps)
      (null? es)
      (let loop ((rest es) (taken '()))
        (cond ((null? rest) #f)
              ((rubi-tax-match? (car ps) (car rest))
               (if (rubi-tax-match-bag (cdr ps) (append (reverse taken) (cdr rest)))
                   #t
                   (loop (cdr rest) (cons (car rest) taken))))
              (else (loop (cdr rest) (cons (car rest) taken)))))))

(define (rubi-tax-match? pat e)
  (cond ((and (symbol? pat) (rubi-tax-pat-var? pat)) #t)   ; ?n — переменная образца: с чем угодно
        ((not (pair? pat)) (equal? (rubi-tax-norm pat) (rubi-tax-norm e)))
        ((equal? (car pat) 'quote) (equal? (rubi-tax-norm pat) (rubi-tax-norm e)))
        ((rubi-tax-pat-var? (car pat)) #t)          ; (?f arg) — переменная-голова: не разбираем
        ((not (pair? e)) #f)
        ((and (equal? (car pat) '+) (equal? (car e) '+))
         (rubi-tax-match-bag (rubi-tax-flat '+ pat) (rubi-tax-flat '+ e)))
        ((and (equal? (car pat) '*) (equal? (car e) '*))
         (rubi-tax-match-bag (rubi-tax-flat '* pat) (rubi-tax-flat '* e)))
        (else
         (and (equal? (car pat) (car e))
              (= (length pat) (length e))
              (rubi-tax-all2 rubi-tax-match? (cdr pat) (cdr e))))))


; ---------- изменение показателя ----------
; same | up | down | mirror | half | double | fraction | other-change
(define (rubi-tax-delta pat-exp rhs-exp var)
  (let ((p (rubi-tax-norm pat-exp)) (r (rubi-tax-norm rhs-exp)))
    (cond ((equal? (rubi-tax-text p) (rubi-tax-text r)) 'same)
          ((not (pair? r)) 'other-change)
          ((equal? (car r) '+)
           (let ((other (filter (lambda (t) (not (equal? t var))) (cdr r))))
             (if (and (= 1 (length other)) (number? (car other)) (> (car other) 0)) 'up 'other-change)))
          ((equal? (car r) '-)
           (cond ((and (= 3 (length r)) (equal? (cadr r) var) (number? (caddr r))) 'down)
                 ((and (= 3 (length r)) (number? (cadr r)) (equal? (caddr r) var)) 'mirror)
                 ((and (= 2 (length r)) (equal? (cadr r) var)) 'mirror)
                 (else 'other-change)))
          ((equal? (car r) '*)
           (if (rubi-tax-some number? (cdr r)) 'double 'other-change))
          ((equal? (car r) '/)
           (cond ((and (= 3 (length r)) (equal? (cadr r) var) (number? (caddr r))) 'half)
                 ((and (= 3 (length r)) (pair? (cadr r)) (number? (caddr r))) 'fraction)
                 (else 'other-change)))
          (else 'other-change))))

; буквальные (числовые) показатели выражения
(define (rubi-tax-literal-exps e)
  (let ((acc '()))
    (rubi-tax-walk e
      (lambda (x)
        (let ((exp (rubi-tax-exponent x)))
          (if (and exp (number? (rubi-tax-norm exp)))
              (set! acc (cons (number->string (rubi-tax-norm exp)) acc))))))
    (reverse acc)))

(define (rubi-tax-unique l)
  (cond ((null? l) '())
        ((member? (car l) (cdr l)) (rubi-tax-unique (cdr l)))
        (else (cons (car l) (rubi-tax-unique (cdr l))))))

; ---------- словари имён (по частотам голов в lib/rubi/rules) ----------
(define (rubi-tax-name? s names) (and (symbol? s) (member? (symbol->string s) names)))

(define rubi-tax-trig '("sin" "cos" "tan" "cot" "sec" "csc"))
(define rubi-tax-hyp '("sinh" "cosh" "tanh" "coth" "sech" "csch"))
(define rubi-tax-inv '("asin" "acos" "atan" "acot" "asec" "acsc"))
(define rubi-tax-invh '("asinh" "acosh" "atanh" "acoth" "asech" "acsch"))

; спецфункции: имя -> подсемейство (порядок списка задаёт приоритет имени)
(define rubi-tax-special
  '(("elliptic-e" . "elliptic") ("elliptic-f" . "elliptic") ("elliptic-pi" . "elliptic")
    ("rubi::rubi-hypergeometric2-f1" . "hypergeometric")
    ("rubi::rubi-hypergeometric-pfq" . "hypergeometric")
    ("rubi::rubi-appell-f1" . "appell")
    ("erf" . "erf-fresnel") ("erfc" . "erf-fresnel") ("rubi::rubi-erfc" . "erf-fresnel")
    ("rubi::rubi-erfi" . "erf-fresnel") ("rubi::rubi-fresnel-s" . "erf-fresnel")
    ("rubi::rubi-fresnel-c" . "erf-fresnel")
    ("rubi::rubi-exp-integral-ei" . "exp-integral") ("rubi::rubi-exp-integral-e" . "exp-integral")
    ("rubi::rubi-log-integral" . "exp-integral") ("rubi::rubi-sin-integral" . "exp-integral")
    ("rubi::rubi-cos-integral" . "exp-integral") ("rubi::rubi-sinh-integral" . "exp-integral")
    ("rubi::rubi-cosh-integral" . "exp-integral")
    ("gamma" . "gamma") ("rubi::rubi-log-gamma" . "gamma") ("rubi::rubi-poly-gamma" . "gamma")
    ("polylog" . "polylog") ("rubi::rubi-product-log" . "product-log") ("lambert-w" . "product-log")
    ("bessel-j" . "bessel") ("bessel-y" . "bessel") ("bessel-i" . "bessel") ("bessel-k" . "bessel")
    ("zeta" . "zeta") ("floor" . "integer-part") ("ceiling" . "integer-part")
    ("rubi::rubi-mod" . "integer-part") ("rubi::rubi-fractional-part" . "integer-part")
    ("rubi::rubi-integer-part" . "integer-part") ("rubi::rubi-sign" . "integer-part")))


(define rubi-tax-subst-u
  '("rubi::rubi-subst-pat" "subst" "rubi::rubi-subst-for" "rubi::rubi-subst-power"
    "rubi::rubi-subst-for-inverse-function" "rubi::rubi-subst-for-fractional-power-q"
    "rubi::rubi-try-pure-tan-subst" "rubi::rubi-function-of-linear" "rubi::rubi-polynomial-in-subst"))

(define rubi-tax-convert-u
  '(("rubi::rubi-activate-trig" . "activate-trig") ("rubi::rubi-deactivate-trig" . "deactivate-trig")
    ("rubi::rubi-trig-simplify" . "trig-simplify") ("rubi::rubi-expand-trig-to-exp" . "to-exp")))

(define rubi-tax-expand-u
  '(("rubi::rubi-expand-integrand" . "expand-integrand") ("rubi::rubi-expand-to-sum" . "expand-to-sum")
    ("rubi::rubi-expand-trig-reduce" . "expand-trig") ("rubi::rubi-expand-trig" . "expand-trig")
    ("rubi::rubi-expand-trig-expand" . "expand-trig")
    ("rubi::rubi-polynomial-quotient" . "polynomial-division")
    ("rubi::rubi-polynomial-remainder" . "polynomial-division")
    ("rubi::rubi-polynomial-divide" . "polynomial-division")
    ("rubi::rubi-rational-function-expand" . "apart") ("apart" . "apart")
    ("rubi::rubi-expand-linear-product" . "expand-power") ("expand" . "expand-power")
    ("rubi::rubi-split-product" . "split")))

(define rubi-tax-prep-u
  '("rubi::rubi-simplify-integrand" "rubi::rubi-normalize-integrand" "rubi::rubi-remove-content"
    "rubi::rubi-dist" "rubi::rubi-int-part" "rubi::rubi-frac-part" "rubi::rubi-int-sum"
    "rubi::rubi-int-hide" "rubi::rubi-normalize-power-of-linear"
    "rubi::rubi-normalize-pseudo-binomial" "rubi::rubi-simp" "simplify" "together"))

(define rubi-tax-unintegrable-u
  '("rubi::rubi-unintegrable" "rubi::rubi-integral" "rubi::rubi-cannot-integrate"))

; ---------- строки и служебное ----------
(define (rubi-tax-trim s)
  (let* ((n (string-length s))
         (i (let loop ((i 0))
              (if (and (< i n) (equal? (substring s i (+ i 1)) " ")) (loop (+ i 1)) i)))
         (j (let loop ((j n))
              (if (and (> j i) (equal? (substring s (- j 1) j) " ")) (loop (- j 1)) j))))
    (substring s i j)))

(define (rubi-tax-digit? c) (not (equal? (string->number c) #f)))

(define (rubi-tax-join l sep) (if (null? l) "" (string-join l sep)))

(define (rubi-tax-slug r) (to-string (nth r 9)))
(define (rubi-tax-base-slug slug) (car (string-split slug "-")))
(define (rubi-tax-section slug) (rubi-tax-base-slug slug))

(define (rubi-tax-chapter slug)
  (let ((parts (string-split (rubi-tax-base-slug slug) ".")))
    (if (and (pair? parts) (> (string-length (car parts)) 0) (rubi-tax-digit? (substring (car parts) 0 1)))
        (if (> (length parts) 1) (string-append (car parts) "." (cadr parts)) (car parts))
        "misc")))

(define (rubi-tax-rule-num r)
  (let ((p (string-split (to-string (nth r 1)) "#")))
    (rubi-tax-trim (car (reverse p)))))


; ---------- класс формы образца ----------
(define (rubi-tax-x? e) (or (equal? e 'x) (equal? e '(quote x))))
(define (rubi-tax-contains-x? e)
  (cond ((rubi-tax-x? e) #t)
        ((pair? e) (rubi-tax-some rubi-tax-contains-x? (cdr e)))
        (else #f)))

; аргумент не линейный по x: x в показателе (^ … x …) или в знаменателе (/ … x)
(define (rubi-tax-nonlinear-in-x? e)
  (let ((bad #f))
    (rubi-tax-walk e
      (lambda (x)
        (cond ((and (equal? (car x) '^) (= (length x) 3) (rubi-tax-contains-x? (caddr x))) (set! bad #t))
              ((and (equal? (car x) '/) (>= (length x) 3) (rubi-tax-some rubi-tax-contains-x? (cddr x)))
               (set! bad #t))
              (else #t))))
    bad))

(define (rubi-tax-form-class pat)
  (let ((hasx #f) (args '()))
    (rubi-tax-walk-all pat
      (lambda (x)
        (cond ((rubi-tax-x? x) (set! hasx #t))
              ((and (pair? x) (symbol? (car x)) (pair? (cdr x))
                    (or (rubi-tax-name? (car x) rubi-tax-trig) (rubi-tax-name? (car x) rubi-tax-hyp)))
               (set! args (cons (cadr x) args))))))
    (cond ((not hasx) 'no-x)
          ((null? args) 'general)
          ((rubi-tax-some rubi-tax-nonlinear-in-x? args) 'general)
          (else 'linear-arg))))

; ---------- классификатор: помощники ----------
(define (rubi-tax-has? heads name)
  (rubi-tax-some (lambda (h) (and (symbol? h) (equal? (symbol->string h) name))) heads))

(define (rubi-tax-form-head? h)
  (and (symbol? h)
       (or (rubi-tax-name? h rubi-tax-trig) (rubi-tax-name? h rubi-tax-hyp)
           (rubi-tax-name? h rubi-tax-inv) (rubi-tax-name? h rubi-tax-invh)
           (rubi-tax-has? (map car rubi-tax-special) (symbol->string h))
           (rubi-tax-name? h '("exp" "log" "sqrt")))))

(define (rubi-tax-form-heads e) (filter rubi-tax-form-head? (rubi-tax-heads e)))

; цели подстановок: (rubi-subst-pat Int x цель), (subst … x цель), (rubi-subst-for … цель)
(define (rubi-tax-subst-targets rhs)
  (let ((acc '()))
    (rubi-tax-walk rhs
      (lambda (x)
        (let ((h (car x)) (len (length x)))
          (cond ((and (symbol? h) (equal? (symbol->string h) "rubi::rubi-subst-pat") (>= len 4))
                 (set! acc (cons (nth x 3) acc)))
                ((and (symbol? h) (equal? (symbol->string h) "subst") (>= len 4))
                 (set! acc (cons (nth x 3) acc)))
                ((and (symbol? h) (equal? (symbol->string h) "rubi::rubi-subst-for") (>= len 3))
                 (set! acc (cons (cadr x) acc)))
                ((and (symbol? h) (equal? (symbol->string h) "rubi::rubi-subst-power") (>= len 3))
                 (set! acc (cons (cadr x) acc)))
                (else #t)))))
    (reverse acc)))

(define (rubi-tax-all-powers e)
  (let ((acc '()))
    (rubi-tax-walk e (lambda (x) (let ((ex (rubi-tax-exponent x))) (if ex (set! acc (cons x acc))))))
    acc))

; x -> (…) ^ (1/k): показатель степени дробный (1/k, a/k, доля с переменной)
(define (rubi-tax-rational-power? node)
  (let ((ex (rubi-tax-norm (rubi-tax-exponent node))))
    (and (pair? ex)
         (or (and (equal? (car ex) '*) (rubi-tax-some rubi-tax-pat-var? (cdr ex)))
             (and (equal? (car ex) '/) (number? (car (reverse ex))))))))

(define (rubi-tax-div-has-x? t)
  (let ((bad #f))
    (rubi-tax-walk t
      (lambda (x) (if (and (equal? (car x) '/) (>= (length x) 3)
                           (rubi-tax-some rubi-tax-contains-x? (cddr x)))
                      (set! bad #t))))
    bad))

(define (rubi-tax-x-power? t)
  (let ((bad #f))
    (rubi-tax-walk t (lambda (x) (if (and (equal? (car x) '^) (= (length x) 3) (rubi-tax-x? (cadr x)))
                                     (set! bad #t))))
    bad))


; ---------- классификатор: подсемейства ----------
(define (rubi-tax-subst-sub rhs heads)
  (let ((tgts (rubi-tax-subst-targets rhs)))
    (cond ((rubi-tax-has? heads "rubi::rubi-try-pure-tan-subst") "tan-half")
          ((rubi-tax-has? heads "rubi::rubi-function-of-linear") "linear")
          ((rubi-tax-has? heads "rubi::rubi-subst-for-inverse-function") "inverse")
          ((rubi-tax-has? heads "rubi::rubi-subst-for-fractional-power-q") "radical")
          ((null? tgts) "other")
          ((rubi-tax-some (lambda (t) (or (rubi-tax-has? (rubi-tax-heads t) "tan")
                                          (rubi-tax-has? (rubi-tax-heads t) "cot"))) tgts) "tan-half")
          ((rubi-tax-some (lambda (t) (rubi-tax-some rubi-tax-rational-power? (rubi-tax-all-powers t))) tgts)
           "radical")
          ((rubi-tax-some (lambda (t) (or (rubi-tax-has? (rubi-tax-heads t) "sin")
                                          (rubi-tax-has? (rubi-tax-heads t) "cos")
                                          (rubi-tax-has? (rubi-tax-heads t) "sec")
                                          (rubi-tax-has? (rubi-tax-heads t) "csc"))) tgts) "trig")
          ((rubi-tax-some (lambda (t) (rubi-tax-some (lambda (h) (rubi-tax-name? h rubi-tax-hyp))
                                                     (rubi-tax-heads t))) tgts) "hyperbolic")
          ((rubi-tax-some (lambda (t) (rubi-tax-has? (rubi-tax-heads t) "sqrt")) tgts) "radical")
          ((rubi-tax-some (lambda (t) (rubi-tax-has? (rubi-tax-heads t) "log")) tgts) "log")
          ((rubi-tax-some (lambda (t) (rubi-tax-has? (rubi-tax-heads t) "exp")) tgts) "exp")
          ((rubi-tax-some (lambda (t) (rubi-tax-some (lambda (h) (rubi-tax-name? h rubi-tax-inv))
                                                     (rubi-tax-heads t))) tgts) "inverse")
          ((rubi-tax-some rubi-tax-div-has-x? tgts) "rational")
          ((and (= 1 (length tgts)) (symbol? (car tgts)) (not (rubi-tax-x? (car tgts)))) "composite-arg")
          ((rubi-tax-some rubi-tax-x-power? tgts) "power")
          ((rubi-tax-some rubi-tax-contains-x? tgts) "linear")
          (else "other"))))

(define (rubi-tax-base-sub heads)
  (cond ((rubi-tax-has? heads "log") "log")
        ((rubi-tax-has? heads "atan") "atan")
        ((or (rubi-tax-has? heads "atanh") (rubi-tax-has? heads "acoth")) "atanh")
        ((rubi-tax-some (lambda (h) (rubi-tax-name? h '("asin" "acos" "acot" "asec" "acsc"))) heads)
         "inverse-trig")
        ((rubi-tax-some (lambda (h) (rubi-tax-name? h '("asinh" "acosh" "asech" "acsch"))) heads)
         "inverse-hyperbolic")
        ((rubi-tax-some (lambda (h) (rubi-tax-name? h rubi-tax-hyp)) heads) "hyperbolic")
        ((rubi-tax-some (lambda (h) (rubi-tax-name? h rubi-tax-trig)) heads) "trig")
        ((rubi-tax-has? heads "exp") "exp")
        ((rubi-tax-has? heads "sqrt") "root")
        ((rubi-tax-some (lambda (h) (rubi-tax-name? h '("floor" "ceiling" "rubi::rubi-mod"
                                                        "rubi::rubi-sign"))) heads) "integer-part")
        (else "rational")))

(define (rubi-tax-special-sub heads)
  (let loop ((l rubi-tax-special))
    (cond ((null? l) #f)
          ((rubi-tax-has? heads (car (car l))) (cdr (car l)))
          (else (loop (cdr l))))))

(define (rubi-tax-first-of assoc-list heads)
  (let loop ((l assoc-list))
    (cond ((null? l) #f)
          ((rubi-tax-has? heads (car (car l))) (cdr (car l)))
          (else (loop (cdr l))))))

; изменения показателей внутри Int правой части
(define (rubi-tax-deltas pat ints)
  (let ((acc '()))
    (for-each
     (lambda (ev)
       (let ((bare (rubi-tax-bare (car ev))) (pexp (cadr ev)) (base (caddr ev)))
         (for-each
          (lambda (ia)
            (for-each (lambda (ex)
                        (let ((d (rubi-tax-delta pexp ex bare)))
                          (if (not (equal? d 'same)) (set! acc (cons (symbol->string d) acc)))))
                      (rubi-tax-exponents-of ia bare base)))
          ints)))
     (rubi-tax-exp-vars pat))
    (reverse acc)))


; ---------- классификатор: (rubi-rule-family rule) -> (семейство подсемейство признаки) ----------
; признаки: alist (nint . N) (mech . "in-part"/"recurrence")
(define (rubi-rule-family r)
  (let* ((pat (nth r 2))
         (cr (rubi::rubi-fixed r))
         (rhs (cdr cr))
         (heads (rubi-tax-heads rhs))
         (nint (rubi-tax-count-int rhs))
         (ints (rubi-tax-int-args rhs))
         (mech (cond ((= nint 0) "")
                     ((rubi-tax-has-free-int-term rhs) "in-part")
                     (else "recurrence")))
         (feat (lambda (fam sub) (list fam sub (list (cons 'nint nint) (cons 'mech mech))))))
    (cond
      ((rubi-tax-some (lambda (h) (member? (symbol->string h) rubi-tax-unintegrable-u)) heads)
       (feat 'UNINTEGRABLE "proved"))
      ((= nint 0)
       (let ((sp (rubi-tax-special-sub heads)))
         (if sp (feat 'SPECIAL sp) (feat 'BASE (rubi-tax-base-sub heads)))))
      ((rubi-tax-some (lambda (h) (member? (symbol->string h) rubi-tax-subst-u)) heads)
       (feat 'SUBST (rubi-tax-subst-sub rhs heads)))
      ((rubi-tax-first-of rubi-tax-convert-u heads)
       (feat 'CONVERT (rubi-tax-first-of rubi-tax-convert-u heads)))
      ((rubi-tax-first-of rubi-tax-expand-u heads)
       (feat 'EXPAND (rubi-tax-first-of rubi-tax-expand-u heads)))
      ; образец — тригонометрия, а Int записан через экспоненты: сведение к exp-форме
      ((and (rubi-tax-some (lambda (h) (or (rubi-tax-name? h rubi-tax-trig) (rubi-tax-name? h rubi-tax-hyp)))
                           (rubi-tax-heads pat))
            (rubi-tax-some (lambda (ia) (rubi-tax-has? (rubi-tax-heads ia) "exp")) ints))
       (feat 'CONVERT "to-exp"))
      (else
       (let ((ds (rubi-tax-unique (rubi-tax-deltas pat ints))))
         (cond
           ((pair? ds)
            (feat 'REDUCE (string-append "index-" (if (null? (cdr ds)) (car ds) "mixed"))))
           ((>= nint 2) (feat 'EXPAND "split"))
           ((and (= nint 1) (pair? pat) (rubi-tax-match? pat (car ints))) (feat 'REDUCE "index-same"))
           ((let ((lp (sort (rubi-tax-literal-exps pat) string<?))
                  (li (sort (if (pair? ints) (rubi-tax-literal-exps (car ints)) '()) string<?)))
              (and (pair? lp) (= (length lp) (length li)) (not (equal? lp li))))
            (feat 'REDUCE "index-literal"))
           ((rubi-tax-some (lambda (h) (member? (symbol->string h) rubi-tax-prep-u)) heads)
            (feat 'DISPATCH "normalize"))
           (else (feat 'DISPATCH "rewrite"))))))))


; ---------- записи для таблиц ----------
(define (rubi-tax-cond-utils cond)
  (if (not cond)
      '()
      (filter (lambda (h)
                (and (symbol? h)
                     (not (member? (symbol->string h)
                                   '("and" "or" "not" "list" "+" "*" "^" "-" "/" "quote")))))
              (rubi-tax-heads cond))))

(define (rubi-tax-record r)
  (let* ((slug (rubi-tax-slug r))
         (fam (rubi-rule-family r))
         (fam-name (symbol->string (car fam)))
         (sub (cadr fam))
         (feats (caddr fam))
         (pat (nth r 2))
         (cr (rubi::rubi-fixed r)))
    (list (cons 'id (to-string (nth r 1)))
          (cons 'slug slug)
          (cons 'num (rubi-tax-rule-num r))
          (cons 'chapter (rubi-tax-chapter slug))
          (cons 'section (rubi-tax-section slug))
          (cons 'family fam-name)
          (cons 'sub sub)
          (cons 'subkey (string-append fam-name "/" sub))
          (cons 'mech (cdr (assoc 'mech feats)))
          (cons 'nint (cdr (assoc 'nint feats)))
          (cons 'pat_heads (rubi-tax-join (map symbol->string (rubi-tax-form-heads pat)) ";"))
          (cons 'expvars (rubi-tax-join
                          (map (lambda (e) (symbol->string (rubi-tax-bare (car e))))
                               (rubi-tax-exp-vars pat)) ";"))
          (cons 'ans_heads (rubi-tax-join (map symbol->string (rubi-tax-form-heads (cdr cr))) ";"))
          (cons 'cond_utils (rubi-tax-join (map symbol->string (rubi-tax-cond-utils (car cr))) ";"))
          (cons 'form (symbol->string (rubi-tax-form-class pat))))))

(define rubi-tax-records-cache #f)

; все правила — те же данные, что исполняет движок (rubi-ensure-full грузит lib/rubi/rules/*.lisp по списку engine.lisp)
(define (rubi-tax-records)
  (if rubi-tax-records-cache
      rubi-tax-records-cache
      (begin
        (rubi::rubi-ensure)
        (rubi::rubi-ensure-full)
        (set! rubi-tax-records-cache (map rubi-tax-record rubi::*rubi-rules*))
        rubi-tax-records-cache)))

(define (rubi-tax-f rec k) (cdr (assoc k rec)))

(define (rubi-tax-count-where recs k v)
  (length (filter (lambda (r) (equal? (to-string (rubi-tax-f r k)) (to-string v))) recs)))

; 1.2 < 1.10
(define (rubi-tax-chapter-key ch)
  (if (equal? ch "misc")
      9999
      (let ((p (string-split ch ".")))
        (+ (* 1000 (string->number (car p)))
           (if (> (length p) 1) (string->number (cadr p)) 0)))))

(define (rubi-tax-chapters recs)
  (sort (rubi-tax-unique (map (lambda (r) (rubi-tax-f r 'chapter)) recs))
        (lambda (a b) (< (rubi-tax-chapter-key a) (rubi-tax-chapter-key b)))))

; ---------- таблица rules.tsv ----------
(define (rubi-tax-print-rules recs)
  (display "rule\tfile\tnum\tchapter\tsection\tfamily\tsubfamily\tmech\tnint\tpat_heads\tpat_expvars\tans_heads\tcond_utils\tform_class")
  (newline)
  (for-each
   (lambda (r)
     (display (rubi-tax-join
               (list (rubi-tax-f r 'id) (rubi-tax-f r 'slug) (rubi-tax-f r 'num) (rubi-tax-f r 'chapter)
                     (rubi-tax-f r 'section) (rubi-tax-f r 'family) (rubi-tax-f r 'sub) (rubi-tax-f r 'mech)
                     (to-string (rubi-tax-f r 'nint)) (rubi-tax-f r 'pat_heads) (rubi-tax-f r 'expvars)
                     (rubi-tax-f r 'ans_heads) (rubi-tax-f r 'cond_utils) (rubi-tax-f r 'form))
               "\t"))
     (newline))
   recs))

; ---------- таблица families.tsv: семейство x глава ----------
(define rubi-tax-families-order
  '("BASE" "REDUCE" "SUBST" "EXPAND" "CONVERT" "DISPATCH" "SPECIAL" "UNINTEGRABLE" "OTHER"))

(define (rubi-tax-print-families recs)
  (let ((chs (rubi-tax-chapters recs)))
    (display (rubi-tax-join (append (list "family") chs (list "total")) "\t"))
    (newline)
    (for-each
     (lambda (fam)
       (let ((c (rubi-tax-count-where recs 'family fam)))
         (if (> c 0)
             (begin
               (display (rubi-tax-join
                         (append (list fam)
                                 (map (lambda (ch)
                                        (number->string
                                         (length (filter (lambda (r)
                                                           (and (equal? (rubi-tax-f r 'family) fam)
                                                                (equal? (rubi-tax-f r 'chapter) ch)))
                                                         recs))))
                                      chs)
                                 (list (number->string c)))
                         "\t"))
               (newline)))))
     rubi-tax-families-order)
    (display (rubi-tax-join
              (append (list "TOTAL")
                      (map (lambda (ch) (number->string (rubi-tax-count-where recs 'chapter ch))) chs)
                      (list (number->string (length recs))))
              "\t"))
    (newline)))


; ---------- таблица subfamilies.tsv ----------
(define (rubi-tax-print-subfamilies recs)
  (display "family\tsubfamily\trules\tchapters\tsections\tmech")
  (newline)
  (for-each
   (lambda (k)
     (let* ((sel (filter (lambda (r) (equal? (rubi-tax-f r 'subkey) k)) recs))
            (parts (string-split k "/"))
            (inpart (length (filter (lambda (r) (equal? (rubi-tax-f r 'mech) "in-part")) sel)))
            (recur (length (filter (lambda (r) (equal? (rubi-tax-f r 'mech) "recurrence")) sel)))
            (mech (rubi-tax-join
                   (append (if (> recur 0) (list (string-append "recurrence=" (number->string recur))) '())
                           (if (> inpart 0) (list (string-append "in-part=" (number->string inpart))) '()))
                   ";")))
       (display (rubi-tax-join
                 (list (car parts) (if (> (length parts) 1) (cadr parts) "")
                       (number->string (length sel))
                       (rubi-tax-join (rubi-tax-chapters sel) ";")
                       (number->string (length (rubi-tax-unique (map (lambda (r) (rubi-tax-f r 'section)) sel))))
                       mech)
                 "\t"))
       (newline)))
   (sort (rubi-tax-unique (map (lambda (r) (rubi-tax-f r 'subkey)) recs)) string<?)))

; ---------- сводка чисел для отчёта ----------
(define (rubi-tax-pct n total)
  (if (= total 0)
      "0"
      (let ((pm (round (* 1000.0 (/ n (exact->inexact total))))))   ; промилле
        (string-append (number->string (quotient pm 10)) "." (number->string (modulo pm 10))))))

(define (rubi-tax-sorted-keys recs k)
  (sort (rubi-tax-unique (map (lambda (r) (to-string (rubi-tax-f r k))) recs))
        (lambda (a b) (> (rubi-tax-count-where recs k a) (rubi-tax-count-where recs k b)))))

(define (rubi-tax-take l n)
  (cond ((= n 0) '()) ((null? l) '()) (else (cons (car l) (rubi-tax-take (cdr l) (- n 1))))))

(define (rubi-tax-report-top recs n)
  (let ((subs (rubi-tax-sorted-keys recs 'subkey)))
    (display "топ-10 подсемейств:")
    (newline)
    (let loop ((l subs) (i 1))
      (if (or (null? l) (> i 10))
          (begin
            (display (string-append "  топ-10 покрывают "
                                    (rubi-tax-pct (apply + (map (lambda (s) (rubi-tax-count-where recs 'subkey s))
                                                                (rubi-tax-take subs 10)))
                                                  n)
                                    "%"))
            (newline))
          (begin
            (display (string-append "  " (number->string i) ". " (car l) " "
                                    (number->string (rubi-tax-count-where recs 'subkey (car l)))
                                    " (" (rubi-tax-pct (rubi-tax-count-where recs 'subkey (car l)) n) "%)"))
            (newline)
            (loop (cdr l) (+ i 1)))))))

(define (rubi-tax-report)
  (let* ((recs (rubi-tax-records)) (n (length recs)))
    (display (string-append "правил: " (number->string n)
                            ", разделов: " (number->string
                                            (length (rubi-tax-unique (map (lambda (r) (rubi-tax-f r 'section))
                                                                         recs))))
                            ", глав: " (number->string (length (rubi-tax-chapters recs)))))
    (newline)
    (display "семейства:")
    (newline)
    (for-each
     (lambda (fam)
       (let ((c (rubi-tax-count-where recs 'family fam)))
         (if (> c 0)
             (begin (display (string-append "  " fam " " (number->string c) " (" (rubi-tax-pct c n) "%)"))
                    (newline)))))
     rubi-tax-families-order)
    (rubi-tax-report-top recs n)
    (display "Int в правой части:")
    (newline)
    (for-each
     (lambda (k)
       (let ((c (if (equal? k "3+")
                    (length (filter (lambda (r) (>= (rubi-tax-f r 'nint) 3)) recs))
                    (rubi-tax-count-where recs 'nint k))))
         (display (string-append "  " k ": " (number->string c) " (" (rubi-tax-pct c n) "%)"))
         (newline)))
     '("0" "1" "2" "3+"))
    (display (string-append "REDUCE: in-part "
                            (number->string (length (filter (lambda (r)
                                                              (and (equal? (rubi-tax-f r 'family) "REDUCE")
                                                                   (equal? (rubi-tax-f r 'mech) "in-part")))
                                                            recs)))
                            ", recurrence "
                            (number->string (length (filter (lambda (r)
                                                              (and (equal? (rubi-tax-f r 'family) "REDUCE")
                                                                   (equal? (rubi-tax-f r 'mech) "recurrence")))
                                                            recs)))))
    (newline)
    (display "класс формы образца:")
    (newline)
    (for-each
     (lambda (fc)
       (let ((c (rubi-tax-count-where recs 'form fc)))
         (display (string-append "  " fc ": " (number->string c) " (" (rubi-tax-pct c n) "%)"))
         (newline)))
     '("linear-arg" "general" "no-x"))))



; ---------- пропуски в аналогичных главах ----------
(define rubi-tax-analog-pairs
  '(("4.1" "6.1") ("4.3" "6.3") ("4.5" "6.5") ("4.7" "6.7")
    ("5.1" "7.1") ("5.3" "7.3") ("5.5" "7.5")))

(define (rubi-tax-gaps)
  (let ((recs (rubi-tax-records)))
    (display "пропуски (подсемейства, которые есть в одной главе пары и нет в другой):")
    (newline)
    (for-each
     (lambda (pair)
       (let* ((a (car pair)) (b (cadr pair))
              (la (filter (lambda (r) (equal? (rubi-tax-f r 'chapter) a)) recs))
              (lb (filter (lambda (r) (equal? (rubi-tax-f r 'chapter) b)) recs))
              (sa (rubi-tax-unique (map (lambda (r) (rubi-tax-f r 'subkey)) la)))
              (sb (rubi-tax-unique (map (lambda (r) (rubi-tax-f r 'subkey)) lb))))
         (display (string-append "  " a " (" (number->string (length la)) ") vs " b " ("
                                 (number->string (length lb)) ")"))
         (newline)
         (for-each
          (lambda (s)
            (display (string-append "    только " a ": " s " ("
                                    (number->string (rubi-tax-count-where la 'subkey s)) ")"))
            (newline))
          (rubi-tax-take (filter (lambda (s) (not (member? s sb))) sa) 12))
         (for-each
          (lambda (s)
            (display (string-append "    только " b ": " s " ("
                                    (number->string (rubi-tax-count-where lb 'subkey s)) ")"))
            (newline))
          (rubi-tax-take (filter (lambda (s) (not (member? s sa))) sb) 12))))
     rubi-tax-analog-pairs)))

; ---------- связь с отказами: research/rubi/class2/ids.tsv ----------
(define (rubi-tax-failures-default)
  (rubi-tax-failures "research/rubi/class2/ids.tsv"))

; строки «id<TAB>причина<…>»; id — путь t_1_algebraic_functions/…/t_1_1_1_2/1739 → раздел 1.1.1.2
(define (rubi-tax-seg-nums seg)
  (filter (lambda (s) (not (equal? (string->number s) #f))) (string-split seg "_")))

(define (rubi-tax-seg-of-id id)
  (let ((toks (filter (lambda (s) (and (>= (string-length s) 2) (equal? (substring s 0 2) "t_")))
                      (string-split id "/"))))
    (if (null? toks) '() (rubi-tax-seg-nums (car (reverse toks))))))

(define (rubi-tax-section-of-id id)
  (let ((nums (rubi-tax-seg-of-id id)))
    (if (null? nums) "?" (rubi-tax-join nums "."))))

(define (rubi-tax-chapter-of-id id)
  (let ((nums (rubi-tax-seg-of-id id)))
    (if (>= (length nums) 2) (string-append (car nums) "." (cadr nums)) "?")))

(define (rubi-tax-failures path)
  (let* ((recs (rubi-tax-records))
         (text (read-text-file path))
         (lines (filter (lambda (l) (> (string-length l) 0)) (string-split text "\n")))
         (rows (map (lambda (l) (string-split (rubi-tax-trim l) "\t")) (cdr lines)))
         (sec-of (lambda (c) (rubi-tax-section-of-id (car c))))
         (reason-of (lambda (c) (if (> (length c) 1) (cadr c) "")))
         (secs (rubi-tax-unique (map sec-of rows)))
         (reasons (rubi-tax-unique (map reason-of rows)))
         (cnt (lambda (pred) (length (filter pred rows)))))
    (display (string-append "отказов в " path ": " (number->string (length rows))
                            ", разделов " (number->string (length secs))))
    (newline)
    (display "  причина отказов:")
    (newline)
    (for-each
     (lambda (r)
       (let ((c (cnt (lambda (row) (equal? (reason-of row) r)))))
         (if (> c 0)
             (begin (display (string-append "    " r ": " (number->string c))) (newline)))))
     (sort reasons (lambda (a b) (> (cnt (lambda (row) (equal? (reason-of row) a)))
                                    (cnt (lambda (row) (equal? (reason-of row) b)))))))
    (display "  разделы отказов (топ-12) и подсемейства их правил:")
    (newline)
    (for-each
     (lambda (sec)
       (let* ((c (cnt (lambda (row) (equal? (sec-of row) sec))))
              (sel (filter (lambda (r) (equal? (rubi-tax-f r 'section) sec)) recs)))
         (display (string-append "    " sec ": " (number->string c) " отказов из "
                                 (number->string (length sel)) " правил; подсемейства: "
                                 (rubi-tax-join (rubi-tax-take (rubi-tax-sorted-keys sel 'subkey) 3) ",")))
         (newline)))
     (rubi-tax-take (sort secs (lambda (a b) (> (cnt (lambda (row) (equal? (sec-of row) a)))
                                                (cnt (lambda (row) (equal? (sec-of row) b))))))
                    12))))

; ---------- выборка для ручной сверки ----------
(define (rubi-tax-iota k start)
  (if (= k 0) '() (cons start (rubi-tax-iota (- k 1) (+ start 1)))))

(define (rubi-tax-sample k seed)
  (let* ((recs (rubi-tax-records))
         (n (length recs)))
    (display (string-append "выборка " (number->string k) " правил, seed " (number->string seed)
                            " (из " (number->string n) ")"))
    (newline)
    (for-each
     (lambda (i)
       (let ((tail (drop recs (modulo (+ (* 1103515245 i) seed 12345) n))))
         (if (pair? tail)
             (begin
               (display (rubi-tax-join
                         (list (rubi-tax-f (car tail) 'id) (rubi-tax-f (car tail) 'chapter)
                               (rubi-tax-f (car tail) 'subkey) (rubi-tax-f (car tail) 'mech)
                               (to-string (rubi-tax-f (car tail) 'nint)))
                         "\t"))
               (newline)))))
     (rubi-tax-iota k 1))))

; ---------- точки входа ----------
; (rubi-tax-run) — rules.tsv в stdout (как в задании); (rubi-tax-table "families"|"subfamilies") — прочие таблицы
(define (rubi-tax-run)
  (rubi-tax-print-rules (rubi-tax-records)))

(define (rubi-tax-table what)
  (let ((recs (rubi-tax-records)))
    (cond ((equal? what "families") (rubi-tax-print-families recs))
          ((equal? what "subfamilies") (rubi-tax-print-subfamilies recs))
          (else (rubi-tax-print-rules recs)))))
