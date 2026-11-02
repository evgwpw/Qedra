; gruntz.lisp — пределы exp-log-функций при x → +∞ по алгоритму Грунца (MRV), шаг 21j.1
;
; Источники — диссертация Gruntz 1996 (приложение A — код Maple: Limit, MrvLeadTerm, Mrv, Max, Compare,
; Rewrite, MoveUp, Sign). Подшаг 21j.1 — минимальное ядро; в limit по умолчанию НЕ встроено (это 21j.3).
;
; (gruntz-limitinf e x) — lim e при x → +∞: значение | 'inf | '-inf | #f («не знаю»).
; Алгоритм (Gruntz 1996, гл. 3):
;   1. gr-tractable: sinh/cosh/… → exp, asinh/… → log, sqrt u → u^(1/2), b^c (x в c) → exp(c·log b) при b > 0;
;   2. gr-mrv: множество наиболее быстро меняющихся подвыражений (x или exp(u) с u → ±∞), сравнение классов роста
;      gr-compare: lim log f / log g (0 → «<», ±∞ → «>», иначе «=»; log(exp u) = u без упрощения);
;   3. если x ∈ mrv — подъём x → exp(x) (log(exp u) → u), mrv заново;
;   4. gr-rewrite: g = exp(h) — элемент mrv без других элементов внутри; ω = exp(∓h) → 0+ (знак h);
;      каждый f = exp(a) из mrv: c = lim a/h (константа: целая, рациональная, иррациональная), f = exp(a − c·h)·ω^(∓c);
;      нецелые рациональные показатели — ω = τ^q (gr-lead-rat); иррациональные — прямой подсчёт gr-l2 (21j.2); вложенные элементы —
;      через свежие символы %gd<i> (структурная замена replace-expr, без simplify до самого конца);
;   5. ряд по ω (ser-compute по свежей переменной %gw; x — константа), log ω → logw = ∓h; первый ненулевой
;      коэффициент c0 при ω^e0 (gr-leadterm);
;   6. e0 > 0 → 0; e0 < 0 → ±∞ по знаку c0; e0 = 0 → lim c0 (рекурсия).
; Знаки (gr-sign): константы — sign-of, затем численно (eval-num) для констант без параметров, |v| > gr-eps;
; иначе «не знаю» и условие (gruntz-sign-unknown c) в канал conditions. Структурные правила: x > 0, exp > 0,
; произведение, степень с положительным основанием или целым показателем, log u = sign(u − 1); иначе знак c0.
; «Не знаю» (#f): знак не определён, ведущий коэффициент не найден (ноль не распознан / ряд не построился),
; сокращение старших членов при прямом подсчёте (21j.2), неподдерживаемая функция (abs, floor, неизвестная,
; ограниченная осцилляция sin x), исчерпан бюджет (глубина gr-max-depth, число вызовов gr-max-calls).
; Внутри неудача — ошибка (gr-fail), на границе (gr-top) она превращается в #f; наружу ошибок нет.
; Мемоизация — таблицы по (to-string выражение) на один внешний вызов. Счётчики — (algo-stats 'gruntz).

(module gruntz
  (export gruntz-limitinf gruntz-mrv gruntz-compare gruntz-sign gruntz-leadterm))

(define gr-max-depth 40)        ; вложенность gr-limitinf
(define gr-max-calls 400)       ; число невычисленных из памяти вызовов gr-limitinf за один внешний вызов
; рабочие порядки ряда по ω: от малого (коэффициенты — выражения от x, их simplify дорог) к большому,
; повтор при «нулевом ряде» или нулевых найденных коэффициентах
(define gr-widths '(2 4 8 16))
(define gr-max-q 200)           ; наибольший знаменатель показателей ω для ряда по τ (ω = τ^q); больше — прямой подсчёт
(define gr-eps 0.0000000001)   ; численный знак константы: |v| ≤ gr-eps — «не знаю»
(define gr-smooth '(sin cos tan cot sec csc atan acot asin acos))   ; гладкие функции одного аргумента: mrv аргумента

(algo-stats-register 'gruntz '(limitinf mrv compare rewrite moveup series fail tau direct))

; ---------- состояние внешнего вызова ----------

(define gr-catch? #t)    ; #f — не глотать ошибки (отладка: (set! gruntz::gr-catch? #f))
(define *gr-tabs* #f)   ; ((lim . таблица) (mrv . таблица) (lead . таблица) (sign . таблица))
(define *gr-depth* 0)
(define *gr-calls* 0)

(define (gr-fail msg) (error (string-append "gruntz: " msg)))

(define (gr-tab k) (cdr (assoc k *gr-tabs*)))

; значение из таблицы памяти или вычисление; значение хранится обёрнутым (пустой список — тоже ответ)
(define (gr-memo k e thunk)
  (let* ((tbl (gr-tab k)) (key (string->symbol (to-string e))) (hit (tbl 'get key)))
    (if (null? hit)
        (let ((v (thunk))) (tbl 'put key (list v)) v)
        (car hit))))

(define (gr-inf? v) (or (equal? v 'inf) (equal? v '-inf)))

; внешний вызов: переменная пользователя → %gx (положительная), свежие таблицы, ошибка → #f;
; f получает подготовленные выражения (simplify + gr-tractable)
(define (gr-top x exprs f)
  (if (not (symbol? x))
      (error "gruntz: переменная — символ")
      (let ((old (list *gr-tabs* *gr-depth* *gr-calls*)))
        (set! *gr-tabs* (list (cons 'lim (make-table)) (cons 'mrv (make-table))
                              (cons 'lead (make-table)) (cons 'sign (make-table))))
        (set! *gr-depth* 0)
        (set! *gr-calls* 0)
        (unwind-protect
          (let ((run (lambda () (assuming ((%gx positive) (%gw positive))
                                  (apply f (map (lambda (e) (gr-prepare e x)) exprs))))))
            (if gr-catch?
                (try (run) (lambda (err) (algo-count 'gruntz 'fail) #f))
                (run)))
          (begin (set! *gr-tabs* (car old))
                 (set! *gr-depth* (cadr old))
                 (set! *gr-calls* (caddr old)))))))

(define (gr-prepare e x)
  (let ((e1 (simplify (replace-expr (simplify e) x '%gx))))
    (gr-norm (gr-tractable e1 '%gx))))

; обратно к переменной пользователя
(define (gr-back v x) (if (gr-inf? v) v (replace-expr v '%gx x)))

; ---------- нормализация ----------

; log(exp u) → u, log(x^p) → p·log x, (exp u)^r → exp(r·u) (u вещественно, x > 0), затем simplify;
; повтор, пока меняется
(define (gr-unlog e)
  (cond ((not (op-expr? e)) e)
        (else
         (let ((a (cons (car e) (map gr-unlog (cdr e)))))
           (cond ((and (equal? (car a) 'log) (= (length a) 2) (op-expr? (cadr a)) (equal? (car (cadr a)) 'exp))
                  (cadr (cadr a)))
                 ((and (equal? (car a) 'log) (= (length a) 2) (op-expr? (cadr a)) (equal? (car (cadr a)) '^)
                       (equal? (cadr (cadr a)) '%gx) (x-free? (caddr (cadr a)) '%gx))
                  (list '* (caddr (cadr a)) (list 'log '%gx)))
                 ((and (equal? (car a) '^) (= (length a) 3) (op-expr? (cadr a)) (equal? (car (cadr a)) 'exp)
                       (x-free? (caddr a) '%gx))
                  (list 'exp (list '* (caddr a) (cadr (cadr a)))))
                 (else a))))))

(define (gr-norm e)
  (let ((e1 (simplify e)))
    (let ((e2 (gr-unlog e1)))
      (if (equal? e2 e1) e1 (gr-norm e2)))))

; ---------- tractable: гиперболические → exp, обратные гиперболические → log, b^c → exp(c log b) ----------

(define (gr-ex u) (list 'exp u))
(define (gr-ex- u) (list 'exp (list '* -1 u)))
(define (gr-div a b) (list '* a (list '^ b -1)))

(define (gr-tractable e x)
  (if (or (x-free? e x) (not (op-expr? e)))
      e
      (let ((h (car e)) (args (map (lambda (a) (gr-tractable a x)) (cdr e))))
        (cond ((and (equal? h '^) (= (length args) 2) (not (x-free? (cadr args) x)))
               (gr-pow->exp (car args) (cadr args) x))
              ((not (= (length args) 1)) (cons h args))
              (else
               (let ((u (car args)))
                 (cond ((equal? h 'sqrt) (list '^ u 1/2))
                       ((equal? h 'sinh) (list '* 1/2 (list '+ (gr-ex u) (list '* -1 (gr-ex- u)))))
                       ((equal? h 'cosh) (list '* 1/2 (list '+ (gr-ex u) (gr-ex- u))))
                       ((equal? h 'tanh) (gr-div (list '+ (gr-ex u) (list '* -1 (gr-ex- u))) (list '+ (gr-ex u) (gr-ex- u))))
                       ((equal? h 'coth) (gr-div (list '+ (gr-ex u) (gr-ex- u)) (list '+ (gr-ex u) (list '* -1 (gr-ex- u)))))
                       ((equal? h 'sech) (gr-div 2 (list '+ (gr-ex u) (gr-ex- u))))
                       ((equal? h 'csch) (gr-div 2 (list '+ (gr-ex u) (list '* -1 (gr-ex- u)))))
                       ((equal? h 'asinh) (list 'log (list '+ u (list '^ (list '+ (list '^ u 2) 1) 1/2))))
                       ((equal? h 'acosh) (list 'log (list '+ u (list '^ (list '+ (list '^ u 2) -1) 1/2))))
                       ((equal? h 'atanh) (list '* 1/2 (list 'log (gr-div (list '+ 1 u) (list '+ 1 (list '* -1 u))))))
                       ((equal? h 'acoth) (list '* 1/2 (list 'log (gr-div (list '+ u 1) (list '+ u -1)))))
                       (else (cons h args)))))))))

; b^c с x в показателе: exp(c·log b), только при b > 0 (иначе ветви логарифма — «не знаю»)
(define (gr-pow->exp b c x)
  (let ((b1 (gr-norm b)))
    (if (equal? (gr-sign b1 x) 1)
        (list 'exp (list '* c (list 'log b1)))
        (gr-fail "основание степени с переменным показателем не положительно"))))

; ---------- знак при x → +∞: 1, -1, 0 ----------

(define (gr-sign-unknown c)
  (if (not (int-num c))
      (record-condition (list 'gruntz-sign-unknown c)
                        "gruntz: знак не определён (объявите знак параметра), предел не вычислен"))
  (gr-fail "знак не определён"))

; знак константы: sign-of (декларации), численно (без параметров), затем по структуре: произведение,
; log u = sign(u − 1) при u > 0, степень с положительным основанием; иначе «не знаю» (+ условие)
(define (gr-sign-const c0)
  (let* ((c (simplify c0))
         (s (try (sign-of c) (lambda (err) 'unknown))))
    (cond ((equal? s 'positive) 1)
          ((equal? s 'negative) -1)
          ((equal? s 'zero) 0)
          (else
           (let ((n (int-num c)))
             (cond ((and n (> n gr-eps)) 1)
                   ((and n (< n (- 0 gr-eps))) -1)
                   ((and (op-expr? c) (equal? (car c) '*))
                    (foldl (lambda (acc a) (if (= acc 0) 0 (* acc (gr-sign-const a)))) 1 (cdr c)))
                   ((and (op-expr? c) (equal? (car c) 'log) (= (length c) 2) (equal? (gr-sign-const (cadr c)) 1))
                    (gr-sign-const (list '+ (cadr c) -1)))
                   ((and (op-expr? c) (equal? (car c) '^) (= (length c) 3) (equal? (gr-sign-const (cadr c)) 1)) 1)
                   (else (gr-sign-unknown c))))))))

(define (gr-sign e x)
  (cond ((x-free? e x) (gr-sign-const e))
        ((equal? e x) 1)
        ((not (op-expr? e)) (gr-fail "знак: не выражение"))
        (else (gr-memo 'sign e (lambda () (gr-sign-raw e x))))))

(define (gr-sign-raw e x)
  (let ((h (car e)))
    (cond ((equal? h '*)
           (foldl (lambda (acc a) (if (= acc 0) 0 (* acc (gr-sign a x)))) 1 (cdr e)))
          ((equal? h 'exp) 1)
          ((and (equal? h '^) (= (length e) 3) (x-free? (caddr e) x))
           (let ((sb (gr-sign (cadr e) x)) (p (caddr e)))
             (cond ((= sb 1) 1)
                   ((= sb 0) 0)
                   ((integer? p) (if (= (mod p 2) 0) 1 -1))
                   (else (gr-fail "знак: отрицательное основание нецелой степени")))))
          ((and (equal? h 'log) (= (length e) 2) (equal? (gr-sign (cadr e) x) 1))
           (gr-sign (gr-norm (list '+ (cadr e) -1)) x))
          (else (gr-sign (car (gr-leadterm e x)) x)))))

; ---------- сравнение классов роста ----------

; log f без упрощения для exp (иначе рекурсия не завершается)
(define (gr-log-of a) (if (and (op-expr? a) (equal? (car a) 'exp)) (cadr a) (list 'log a)))

; '< (a ≺ b), '= (один класс), '> (a ≻ b)
(define (gr-compare a b x)
  (algo-count 'gruntz 'compare)
  (let ((c (gr-limitinf (gr-norm (list '* (gr-log-of a) (list '^ (gr-log-of b) -1))) x)))
    (cond ((equal? c 0) '<)
          ((gr-inf? c) '>)
          (else '=))))

; ---------- mrv-множество ----------

(define (gr-union f g) (append f (filter (lambda (b) (not (member? b f))) g)))

(define (gr-mrv-max f g x)
  (cond ((null? f) g)
        ((null? g) f)
        ((any? (lambda (a) (member? a g)) f) (gr-union f g))
        (else (let ((c (gr-compare (car f) (car g) x)))
                (cond ((equal? c '>) f)
                      ((equal? c '<) g)
                      (else (gr-union f g)))))))

(define (gr-mrv e x)
  (cond ((x-free? e x) '())
        ((equal? e x) (list x))
        ((not (op-expr? e)) (gr-fail "mrv: не выражение"))
        (else (gr-memo 'mrv e (lambda () (algo-count 'gruntz 'mrv) (gr-mrv-raw e x))))))

(define (gr-mrv-raw e x)
  (let ((h (car e)) (n (length e)))
    (cond ((member? h '(+ *))
           (foldl (lambda (acc a) (gr-mrv-max acc (gr-mrv a x) x)) '() (cdr e)))
          ((and (equal? h '^) (= n 3))
           (if (x-free? (caddr e) x)
               (gr-mrv (cadr e) x)
               (gr-fail "mrv: степень с переменным показателем")))
          ((and (equal? h 'log) (= n 2)) (gr-mrv (cadr e) x))
          ((and (equal? h 'exp) (= n 2))
           (let ((u (cadr e)))
             (if (and (op-expr? u) (equal? (car u) 'log))
                 (gr-mrv (cadr u) x)
                 (if (gr-inf? (gr-limitinf u x))
                     (gr-mrv-max (list e) (gr-mrv u x) x)
                     (gr-mrv u x)))))
          ((and (member? h gr-smooth) (= n 2)) (gr-mrv (cadr e) x))
          (else (gr-fail "mrv: неподдерживаемая функция")))))

; ---------- переписывание через ω и ведущий член ----------

(define (gr-index e l i)
  (cond ((null? l) #f)
        ((equal? e (car l)) i)
        (else (gr-index e (cdr l) (+ i 1)))))

; элементы mrv заменяются свежими символами (сверху вниз; внутрь заменённого не заходим)
(define (gr-abstract e om ds)
  (let ((i (gr-index e om 0)))
    (cond (i (nth ds i))
          ((op-expr? e) (cons (car e) (map (lambda (a) (gr-abstract a om ds)) (cdr e))))
          (else e))))

; число узлов выражения
(define (gr-size e) (if (op-expr? e) (foldl (lambda (acc a) (+ acc (gr-size a))) 1 (cdr e)) 1))

(define (gr-has-any? e ds) (any? (lambda (d) (contains-sym? e d)) ds))

; подстановка символов-заместителей их переписанными формами, пока символы остаются (вложенные элементы)
(define (gr-resolve F ds rs k)
  (cond ((not (gr-has-any? F ds)) F)
        ((= k 0) (gr-fail "rewrite: циклическая вложенность"))
        (else (gr-resolve (foldl (lambda (acc p) (replace-expr acc (car p) (cadr p))) F (map2 list ds rs))
                          ds rs (- k 1)))))

; Переписывание (как SubsSet в эталонной реализации): элементы mrv и их аргументы заменяются символами %gd<i> ДО подъёма,
; поэтому после подъёма x → exp(x) mrv заново не считается (иначе compare(exp x, x) зацикливается) и
; совпадение подвыражений не зависит от упрощателя.
;   om — mrv-множество e; возвращает (F logw): e через ω = %gw (без символов %gd), logw — выражение log ω.
; Элемент i: «настоящая» форма r_i = exp(a_i) (после подъёма — в новой переменной; элемент x становится exp(x))
; и аргумент A_i в символах-заместителях; g — элемент, у которого A_g без заместителей (внутри нет других
; элементов), самый короткий; h = a_g, ω = exp(−sign(h)·h); f_i = exp(A_i − c_i·h)·ω^(−sign(h)·c_i), c_i = lim a_i/h.
(define (gr-rewrite e om x)
  (algo-count 'gruntz 'rewrite)
  (let* ((up (member? x om))
         (ds (map (lambda (i) (string->symbol (string-append "%gd" (to-string i)))) (range (length om))))
         (F (gr-abstract e om ds))
         ; (r_i A_i): настоящий аргумент и аргумент в заместителях
         (els (map (lambda (f)
                     (cond ((equal? f x) (list x x))
                           (up (list (gr-moveup (cadr f) x) (gr-abstract (cadr f) om ds)))
                           (else (list (cadr f) (gr-abstract (cadr f) om ds)))))
                   om))
         (cands (filter (lambda (p) (not (gr-has-any? (cadr p) ds))) els))
         (ok0 (if (null? cands) (gr-fail "rewrite: нет простейшего элемента mrv") #t))
         (h (car (foldl (lambda (best p) (if (< (gr-size (car p)) (gr-size (car best))) p best)) (car cands) (cdr cands))))
         (s (gr-sign h x))
         (ok (if (or (= s 1) (= s -1)) #t (gr-fail "rewrite: знак показателя")))
         (cs (map (lambda (p) (gr-const-ratio (gr-limitinf (gr-norm (list '* (car p) (list '^ h -1))) x))) els))
         (rs (map2 (lambda (p c)
                     (list '* (list 'exp (list '+ (cadr p) (list '* (gr-neg c) h)))
                           (list '^ '%gw (gr-neg (gr-times s c)))))
                   els cs)))
    (if up (algo-count 'gruntz 'moveup))
    (list (gr-resolve F ds rs (+ (length om) 1))
          (simplify (list '* (- 0 s) h))
          (every? rational-number? cs))))

; ---------- показатели ω: c = lim a/h — рациональное или константа (log 5/log 3, 21j.2) ----------

; предел отношения показателей: конечная константа без x и ω, иначе отказ
(define (gr-const-ratio c)
  (cond ((or (gr-inf? c) (not c)) (gr-fail "rewrite: показатель ω бесконечен"))
        ((or (contains-sym? c '%gx) (contains-sym? c '%gw)) (gr-fail "rewrite: показатель ω зависит от x"))
        (else c)))
(define (gr-neg c) (if (rational-number? c) (- 0 c) (simplify (list '* -1 c))))
(define (gr-times s c) (if (rational-number? c) (* s c) (simplify (list '* s c))))

; знаменатель рационального числа
(define (gr-den-loop r d) (if (integer? (* r d)) d (gr-den-loop r (+ d 1))))
(define (gr-den r) (if (integer? r) 1 (gr-den-loop r 2)))

; знаменатели нецелых рациональных показателей степеней, основание которых содержит ω (ω → ω^q делает их целыми)
(define (gr-exp-dens F)
  (cond ((not (op-expr? F)) '())
        ((and (equal? (car F) '^) (= (length F) 3) (rational-number? (caddr F)) (not (integer? (caddr F)))
              (contains-sym? (cadr F) '%gw))
         (cons (gr-den (caddr F)) (gr-exp-dens (cadr F))))
        (else (foldl (lambda (acc a) (append acc (gr-exp-dens a))) '() (cdr F)))))

; ω → ω^q
(define (gr-subst-w F q)
  (cond ((equal? F '%gw) (list '^ '%gw q))
        ((op-expr? F) (cons (car F) (map (lambda (a) (gr-subst-w a q)) (cdr F))))
        (else F)))

(define (gr-zero? c)
  (or (equal? c 0)
      (equal? (try (together c) (lambda (err) #f)) 0)))

; первый ненулевой коэффициент ряда (после log ω → logw): (c0 e0) или #f
(define (gr-first-nonzero cs v logw)
  (if (null? cs)
      #f
      (let ((c (gr-norm (replace-expr (car cs) '(log %gw) logw))))
        (cond ((gr-zero? c) (gr-first-nonzero (cdr cs) (+ v 1) logw))
              ((contains-sym? c '%gw) (gr-fail "leadterm: ω осталась в коэффициенте"))
              (else (list c v))))))

(define (gr-series-lead F logw ws)
  (if (null? ws)
      (gr-fail "leadterm: ненулевой член ряда не найден")
      (let ((s (try (begin (algo-count 'gruntz 'series)
                           (ser-with-logx '%gw logw (lambda () (ser-compute F '%gw 0 (car ws)))))
                    (lambda (err) (if (ser-precision-err? err) 'retry (list 'err (error-message err)))))))
        (cond ((and (pair? s) (equal? (car s) 'err)) (gr-fail (string-append "leadterm: ряд не построен: " (cadr s))))
              ((equal? s 'retry) (gr-series-lead F logw (cdr ws)))
              (else (or (gr-first-nonzero (ser-cs s) (ser-val s) logw)
                        (gr-series-lead F logw (cdr ws))))))))

; (c0 e0): e = c0·ω^e0 + …, c0 — выражение от x (класса ниже ω), e0 — целое
(define (gr-leadterm e x)
  (if (x-free? e x)
      (list e 0)
      (gr-memo 'lead e (lambda () (gr-leadterm-raw e x)))))

(define (gr-moveup e x) (gr-norm (replace-expr e x (list 'exp x))))

; ряд с нецелыми рациональными показателями (подшаг 21j.2): ω = τ^q, q — НОК знаменателей; в τ все показатели целые,
; log τ = log ω / q; ведущий показатель пересчитывается обратно (e_τ / q); порядки рабочего ряда — в τ (умножаются на q)
(define (gr-lead-rat F logw)
  (let* ((q (apply lcm (cons 1 (gr-exp-dens F)))))
    (if (> q gr-max-q)
        (gr-fail "leadterm: слишком большой знаменатель показателей ω")
        (let* ((ok (if (> q 1) (algo-count 'gruntz 'tau) #t))
               (Fq (if (= q 1) F (gr-subst-w F q)))
               (lq (if (= q 1) logw (simplify (list '* (/ 1 q) logw))))
               (r (gr-series-lead Fq lq (map (lambda (w) (* w q)) gr-widths))))
          (list (car r) (/ (cadr r) q))))))

(define (gr-leadterm-raw e x)
  (let ((om (gr-mrv e x)))
    (if (null? om)
        (gr-fail "leadterm: пустое mrv")
        (let* ((fl (gr-rewrite e om x)) (F (car fl)) (logw (cadr fl)))
          (if (caddr fl)
              ; рациональные показатели: ряд; если ряд не построился — прямой подсчёт ведущего члена (ниже)
              (let ((r (try (gr-lead-rat F logw) (lambda (err) #f))))
                (or r (gr-lead-sym F logw x)))
              (gr-lead-sym F logw x))))))

; ---------- ведущий член без рядов: мономы ω^c с константными (рациональными/иррациональными) показателями ----------
; (gr-l2 F x logw) → (c0 e0): F = c0·ω^e0·(1 + o(1)), c0 без ω (выражение от x класса ниже ω), e0 — константа.
; Поддержано: ω-свободное (e0 = 0), ω, +, ·, степень с постоянным показателем, log, exp. Сокращение старших членов
; суммы (нулевая сумма коэффициентов при наименьшем показателе) — отказ: следующие порядки не считаются.

(define (gr-e-sign d)
  (let ((v (simplify d)))
    (cond ((rational-number? v) (cond ((> v 0) 1) ((< v 0) -1) (else 0)))
          (else (gr-sign-const v)))))

(define (gr-e+ a b) (simplify (list '+ a b)))
(define (gr-e- a b) (simplify (list '+ a (list '* -1 b))))

(define (gr-l2 F x logw)
  (cond ((not (contains-sym? F '%gw)) (list F 0))
        ((equal? F '%gw) (list 1 1))
        ((not (op-expr? F)) (gr-fail "leadterm: неожиданный атом"))
        (else
         (let ((h (car F)) (n (length F)))
           (cond ((equal? h '*)
                  (foldl (lambda (acc a)
                           (let ((l (gr-l2 a x logw)))
                             (list (simplify (list '* (car acc) (car l))) (gr-e+ (cadr acc) (cadr l)))))
                         (list 1 0) (cdr F)))
                 ((equal? h '+) (gr-l2-sum (map (lambda (a) (gr-l2 a x logw)) (cdr F))))
                 ((and (equal? h '^) (= n 3)) (gr-l2-pow (cadr F) (caddr F) x logw))
                 ((and (equal? h 'log) (= n 2)) (gr-l2-log (cadr F) x logw))
                 ((and (equal? h 'exp) (= n 2)) (gr-l2-exp (cadr F) x logw))
                 (else (gr-fail "leadterm: неподдерживаемая функция от ω")))))))

(define (gr-l2-sum ls)
  (let* ((emin (foldl (lambda (m l) (if (= (gr-e-sign (gr-e- (cadr l) m)) -1) (cadr l) m)) (cadr (car ls)) (cdr ls)))
         (tops (filter (lambda (l) (= (gr-e-sign (gr-e- (cadr l) emin)) 0)) ls))
         (c (gr-norm (cons '+ (map car tops)))))
    (if (gr-zero? c)
        (gr-fail "leadterm: старшие члены сократились")
        (list c emin))))

(define (gr-l2-pow b p x logw)
  (if (or (contains-sym? p '%gw) (not (x-free? p x)))
      (gr-fail "leadterm: показатель степени зависит от ω или x")
      (let* ((l (gr-l2 b x logw)) (c (car l)))
        (if (and (not (integer? p)) (not (equal? (gr-sign c x) 1)))
            (gr-fail "leadterm: нецелая степень выражения с неположительным коэффициентом")
            (list (gr-norm (list '^ c p)) (gr-e+ 0 (simplify (list '* (cadr l) p))))))))

(define (gr-l2-log a x logw)
  (let* ((l (gr-l2 a x logw)) (c (car l)))
    (if (not (equal? (gr-sign c x) 1))
        (gr-fail "leadterm: логарифм выражения с неположительным коэффициентом")
        (list (gr-norm (list '+ (list 'log c) (list '* (cadr l) logw))) 0))))

(define (gr-l2-exp u x logw)
  (let* ((l (gr-l2 u x logw)) (s (gr-e-sign (cadr l))))
    (cond ((= s 1) (list 1 0))
          ((= s 0) (list (gr-norm (list 'exp (car l))) 0))
          (else (gr-fail "leadterm: exp от растущего по ω аргумента")))))

(define (gr-lead-sym F logw x)
  (algo-count 'gruntz 'direct)
  (let ((l (gr-l2 F x logw)))
    (if (or (gr-zero? (car l)) (contains-sym? (car l) '%gw))
        (gr-fail "leadterm: ведущий коэффициент нулевой или содержит ω")
        l)))

; ---------- предел при x → +∞ ----------

(define (gr-limitinf e x)
  (cond ((x-free? e x) e)
        ((equal? e x) 'inf)
        (else (gr-memo 'lim e (lambda () (gr-limitinf-raw e x))))))

(define (gr-limitinf-raw e x)
  (algo-count 'gruntz 'limitinf)
  (set! *gr-calls* (+ *gr-calls* 1))
  (if (or (> *gr-calls* gr-max-calls) (>= *gr-depth* gr-max-depth)) (gr-fail "бюджет исчерпан"))
  (set! *gr-depth* (+ *gr-depth* 1))
  (unwind-protect
    (let* ((lt (gr-leadterm e x)) (c0 (car lt)) (e0 (cadr lt)) (se (gr-e-sign e0)))
      (cond ((= se 1) 0)
            ((= se -1) (let ((s (gr-sign c0 x)))
                        (cond ((= s 1) 'inf)
                              ((= s -1) '-inf)
                              (else (gr-fail "ведущий коэффициент равен нулю")))))
            ((equal? c0 e) (gr-fail "нет продвижения"))
            (else (gr-limitinf c0 x))))
    (set! *gr-depth* (- *gr-depth* 1))))

; ---------- экспорт ----------

; exp(k·log b) → b^k для рационального k (ответ 3^(−1), а не e^(−log 3)); simplify сам это не делает
(define (gr-fold-exp e)
  (if (not (op-expr? e))
      e
      (let ((a (cons (car e) (map gr-fold-exp (cdr e)))))
        (if (and (equal? (car a) 'exp) (= (length a) 2))
            (let ((u (cadr a)))
              (cond ((and (op-expr? u) (equal? (car u) 'log) (= (length u) 2)) (cadr u))
                    ((and (op-expr? u) (equal? (car u) '*) (= (length u) 3) (rational-number? (cadr u))
                          (op-expr? (caddr u)) (equal? (car (caddr u)) 'log) (= (length (caddr u)) 2))
                     (simplify (list '^ (cadr (caddr u)) (cadr u))))
                    (else a)))
            a))))

; lim e при x → +∞: значение | 'inf | '-inf | #f («не знаю»)
(define (gruntz-limitinf e x)
  (gr-top x (list e)
          (lambda (e1)
            (let ((v (gr-limitinf e1 '%gx)))
              (cond ((gr-inf? v) v)
                    ((or (contains-sym? v '%gx) (contains-sym? v '%gw)) #f)
                    (else (gr-fold-exp (simplify v))))))))

; mrv-множество (список элементов: x или exp(u)) или #f
(define (gruntz-mrv e x)
  (gr-top x (list e) (lambda (e1) (map (lambda (f) (gr-back f x)) (gr-mrv e1 '%gx)))))

; '< '= '> или #f
(define (gruntz-compare a b x)
  (gr-top x (list a b) (lambda (a1 b1) (gr-compare a1 b1 '%gx))))

; знак при x → +∞: 1, -1, 0 или #f
(define (gruntz-sign e x)
  (gr-top x (list e) (lambda (e1) (gr-sign e1 '%gx))))

; ведущий член (c0 e0) или #f; c0 — в переменной x после подъёмов (x → exp x), если они были
(define (gruntz-leadterm e x)
  (gr-top x (list e) (lambda (e1) (let ((lt (gr-leadterm e1 '%gx))) (list (gr-back (car lt) x) (cadr lt))))))
