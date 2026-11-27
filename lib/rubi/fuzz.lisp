; lib/rubi/fuzz.lisp — RUBI.FUZZ: генератор примеров и классификация правил Rubi (самопроверка «живо ли
; правило и верна ли правая часть»). Для каждого правила строится пример (образец + условие), движок делает
; один шаг, правило классифицируется; отдельно проверяется правая часть.
; Запуск пакетом — tools/rubi/fuzz.lisp (+ обёртка tools/rubi/fuzz.mjs); правило по id — (fuzz-one-id "…").
; Статусы: self | earlier | base | later | none | cond-unsat | error (см. fuzz-rule); rhs: rhs-ok | rhs-bad |
; rhs-warn (спецфункции: численно не проверяется) | rhs-skip | rhs-err.
(module rubi)

; ---------- мелкие утилиты ----------

(define (fuzz-lines path)
  (filter (lambda (l) (> (string-length l) 0))
          (string-split (read-text-file path) (format "~%"))))

; убрать табуляции и переводы строк из поля (в диалекте нет "\r" — концы строк Windows здесь не встречаются:
; список файлов пишет обёртка с "\n", поля собираются из format)
(define (fuzz-clean s)
  (let loop ((i 0) (acc '()))
    (if (>= i (string-length s))
        (apply string-append (reverse acc))
        (let ((c (substring s i (+ i 1))))
          (loop (+ i 1) (cons (if (or (equal? c "\t") (equal? c "\n")) " " c) acc))))))

(define (fuzz-take l n) (if (or (null? l) (= n 0)) '() (cons (car l) (fuzz-take (cdr l) (- n 1)))))

; ---------- пример по образцу правила ----------

(define (fz-pvars p acc)
  (cond ((null? p) acc)
        ((symbol? p) (if (and (rubi-pvar? p) (not (member? p acc))) (append acc (list p)) acc))
        ((pair? p) (if (equal? (car p) 'quote) acc (fz-pvars (cdr p) (fz-pvars (car p) acc))))
        (else acc)))

(define (fz-name v)                          ; ?a. -> "a", ?m -> "m"
  (let* ((s (to-string v)) (n (string-length s)))
    (if (and (> n 0) (equal? (substring s (- n 1) n) ".")) (substring s 1 (- n 1)) (substring s 1 n))))

(define (fz-strip-dot v)                     ; ?m. -> ?m (так переменная названа в условии и правой части)
  (if (symbol? v)
      (let* ((s (to-string v)) (n (string-length s)))
        (if (and (> n 1) (equal? (substring s (- n 1) n) ".")) (string->symbol (substring s 0 (- n 1))) v))
      v))

(define (fz-subst p alst)
  (cond ((null? p) '())
        ((symbol? p) (let ((b (assoc (fz-strip-dot p) alst))) (if b (cadr b) p)))
        ((pair? p) (if (equal? (car p) 'quote) p (cons (fz-subst (car p) alst) (fz-subst (cdr p) alst))))
        (else p)))


; Подсказка по условию: утилиты Rubi ограничивают вид значения (IGtQ — целое > 0, FractionQ — дробь).
; Поиск по тексту условия — грубо, но условия записаны единообразно (rubi-<утилита> ?v).
(define (fz-hint v cond0)
  (if (not cond0)
      #f
      (let* ((s (format "~s" cond0))
             (n (to-string v))
             (g (lambda (u) (string-contains? s (string-append "rubi-" u " " n)))))
        (cond ((g "igtq") 'posint)
              ((g "iltq") 'negint)
              ((g "ilttq") 'negint)
              ((g "integerq") 'int)
              ((g "fractionq") 'frac)
              ((g "negq") 'neg)
              ((g "posq") 'pos)
              (else #f)))))

; сдвиг пула по номеру переменной: разные параметры получают разные значения (a=2, b=3, c=a ...),
; иначе произведение одинаковых множителей сворачивается и пример вырождается
(define (fz-rotate l k)
  (if (or (null? l) (= k 0)) l (fz-rotate (append (cdr l) (list (car l))) (- k 1))))

(define (fz-pool v cond0)
  (let ((n (fz-name v)) (h (fz-hint (fz-strip-dot v) cond0)))
    (cond ((equal? n "x") '(x))
          ((equal? h 'posint) '(2 1 3 4 5 6 8))
          ((equal? h 'negint) '(-1 -2 -3 -4))
          ((equal? h 'int) '(2 1 3 -1 -2 0 4 -3 5))
          ((equal? h 'frac) '(1/2 -1/2 1/3 3/2 -3/2 2/3))
          ((equal? h 'neg) '(-1 -2 -1/2 -3 a))
          ((equal? h 'pos) '(1 2 1/2 3 a b))
          ((member? n '("u" "v" "w" "y" "z" "s" "t" "U" "V" "W"))
           '((^ x 2) x (sin x) (exp x) (log x) (+ 1 x) (^ x 1/2) (* 2 x) (cos x) (atan x)))
          ((member? n '("m" "n" "p" "q" "r" "k" "j" "i" "l"))
           '(2 1 3 -1 -2 1/2 -1/2 1/3 0 4 5/2 -3 3/2))
          (else '(2 3 a b c 1/2 -1 1 -2 0 4 1/3 -1/2 5 2/3 -3)))))

; декартово произведение пулов, не больше n вариантов (порядок: первый вариант каждого пула — первым)
(define (fz-combos vars pools n)
  (let loop ((l vars) (ps pools) (acc (list '())))
    (if (null? l)
        acc
        (let ((next (apply append
                           (map (lambda (pref)
                                  (map (lambda (v) (append pref (list (list (fz-strip-dot (car l)) v)))) (car ps)))
                                acc))))
          (loop (cdr l) (cdr ps) (if (> (length next) n) (fuzz-take next n) next))))))

; Оценка условия правила с привязками + причина лжи: #t | (false . "conj:util") | (err . "текст").
; Причина берётся из журнала движка (rubi-trace-cond пишет первый ложный конъюнкт и его утилиту) — так
; видно, какая утилита не подтверждает условие и какие условия падают с ошибкой.
(define (fz-cond-eval r cf binds)
  (let* ((key (list 'fuzz (nth r 1)))
         (old-t *rubi-trace*) (old-ne *rubi-trace-ne*))
    (set! *rubi-trace* #t)
    (set! *rubi-trace-ne* key)
    (let ((v (try (cf binds) (lambda (e) (list 'err (to-string e))))))
      (set! *rubi-trace* old-t)
      (set! *rubi-trace-ne* old-ne)
      (cond ((equal? v #t) #t)
            ((and (pair? v) (equal? (car v) 'err)) v)
            (else
             (let ((fl (hash-ref *rubi-trace-cf* key '())))
               (if (pair? fl)
                   (list 'false (string-append "conj" (to-string (cadr (car fl))) ":"
                                               (to-string (caddr (car fl)))))
                   (list 'false "false"))))))))

; --- уточнение привязок: условия Rubi часто связывают параметры (b*c + a*d = 0, m > n), независимый
; перебор такие не удовлетворяет. Счёт — номер первого ложного конъюнкта (глубже = лучше); меняем по одной
; переменной, входящей в этот конъюнкт: hill-climbing до истины.

(define (fz-score r cf binds)               ; 999 — истина, -1 — ошибка, k — первый ложный конъюнкт
  (let ((v (fz-cond-eval r cf binds)))
    (cond ((equal? v #t) 999)
          ((and (pair? v) (equal? (car v) 'err)) -1)
          (else
           (let* ((s (cadr v)) (cp (string-index s ":")))
             (if (and (string-contains? s "conj") cp (> cp 4))
                 (let ((n (string->number (substring s 4 cp))))
                   (if n n 0))
                 0))))))

(define (fz-cond-nth cond0 i)
  (let ((cs (rubi-conjuncts cond0)))
    (if (or (null? cs) (< i 1) (> i (length cs))) #f (nth cs (- i 1)))))

(define (fz-set binds v val)
  (map (lambda (b) (if (equal? (car b) v) (list v val) b)) binds))

(define (fz-best-change r cf binds pools vars)
  (let loop ((vs vars) (best binds) (bs (fz-score r cf binds)))
    (if (null? vs)
        (list best bs)
        (let* ((v (fz-strip-dot (car vs)))
               (p (assoc v pools))
               (pool (if p (cdr p) '())))
          (let inner ((l pool) (bb best) (ss bs))
            (if (null? l)
                (loop (cdr vs) bb ss)
                (let* ((cand (fz-set binds v (car l)))
                       (s (fz-score r cf cand)))
                  (if (> s ss) (inner (cdr l) cand s) (inner (cdr l) bb ss)))))))))

(define (fz-refine r cond0 cf binds pools vars)
  (let loop ((b binds) (s (fz-score r cf binds)) (k 3))
    (if (or (>= s 999) (= k 0))
        (list b s)
        (let* ((ci (if (> s 0) s 1))
               (sc (fz-cond-nth cond0 ci))
               (vs (let ((v (if sc (fz-pvars sc '()) '())))
                     (if (pair? v) v (map car pools))))
               (cand (fz-best-change r cf b pools vs)))
          (if (> (cadr cand) s)
              (loop (car cand) (cadr cand) (- k 1))
              (list b s))))))
(define (fz-accept pat want-x binds n)
  (let ((ex (fz-subst pat binds)))
    (if (or (not want-x) (contains-sym? ex 'x)) (list 'ok ex binds n) #f)))

(define (fz-example r)
  (let* ((pat (nth r 2))
         (body (rubi-fixed r))
         (cond0 (car body))
         (vars (fz-pvars pat '()))
         (palst (map (lambda (v) (cons (fz-strip-dot v) (fz-pool v cond0))) vars))
         (cf (rubi-cond-fn r))
         (want-x (contains-sym? pat 'x))
         (combos (fz-combos vars (map cdr palst) 60)))
    (let loop ((l combos) (n 0) (why "-") (nerr 0))
      (if (null? l)
          (list 'cond-unsat n (if (> nerr n) (string-append "all-err:" why) why))
          (let* ((b (car l)) (sc (fz-score r cf b)))
            (cond ((>= sc 999)
                   (let ((ok (fz-accept pat want-x b n)))
                     (if ok ok (loop (cdr l) (+ n 1) why nerr))))
                  ((= sc -1)
                   (let ((v (fz-cond-eval r cf b)))
                     (loop (cdr l) (+ n 1)
                           (string-append "err:" (fuzz-clean (substring (cadr v) 0 (min 50 (string-length (cadr v))))))
                           (+ nerr 1))))
                  ((> sc 0)
                   ; часть конъюнктов пройдена — уточняем привязки перебором по одной переменной
                   (let* ((ref (fz-refine r cond0 cf b palst vars))
                          (ok (and (>= (cadr ref) 999) (fz-accept pat want-x (car ref) n))))
                     (if ok
                         ok
                         (loop (cdr l) (+ n 1)
                               (let ((v (fz-cond-eval r cf (car ref))))
                                 (if (and (pair? v) (cadr v)) (cadr v) "false"))
                               nerr))))
                  (else
                   (let ((v (fz-cond-eval r cf b)))
                     (loop (cdr l) (+ n 1) (if (and (pair? v) (cadr v)) (cadr v) "false") nerr)))))))))

; ---------- прогон движка: один шаг с журналом ----------

(define (fz-step ne)
  (let ((old *rubi-trace*) (oldlog *rubi-trace-log*))
    ; кэши движка живут на процесс: без сброса следующий пример с тем же выражением получил бы
    ; готовый ответ из кэша, и в журнале не было бы ни «seen», ни «fire» (ложный статус base/none)
    (rubi-bt-reset)
    (set! *rubi-memo* (make-hash))
    (set! *rubi-cands2* (make-hash))
    (set! *rubi-failed* (make-hash))
    (set! *rubi-tries* 0)
    (set! *rubi-trace* #t)
    (set! *rubi-trace-log* '())
    (let* ((r (try (rubi-int ne ne 'x) (lambda (e) 'error)))
           (log (reverse *rubi-trace-log*)))
      (set! *rubi-trace* old)
      (set! *rubi-trace-log* oldlog)
      (list r log))))

(define (fz-fires log) (filter (lambda (rec) (and (pair? rec) (equal? (car rec) 'fire) (= (nth rec 3) 0))) log))

(define (fz-rec-of log kind id ne)
  (filter (lambda (rec) (and (pair? rec) (equal? (car rec) kind) (equal? (cadr rec) id)
                             (or (not ne) (equal? (nth rec 3) ne))))
          log))

(define (fz-ord-of id)
  (let loop ((l *rubi-rules*))
    (cond ((null? l) 999999)
          ((equal? (nth (car l) 1) id) (nth (car l) 0))
          (else (loop (cdr l))))))

; правая часть правила с привязками: производная против примера (int-check-rubi-formal).
; Ответы со спецфункциями (эллиптика, AppellF1, 2F1, полилогарифмы) численно проверяются плохо (ветви) —
; такие «не сошлось» помечаются rhs-warn (ручной разбор), а не rhs-bad.
(define fz-special-heads '(elliptic-e elliptic-f appell-f1 hypergeometric-2f1 hypergeometric-pfq
                           fresnel-s fresnel-c polylog polylog2 erf erfi gamma li ei))

(define (fz-rhs-check r ex binds)
  (let* ((body (rubi-fixed r))
         (rhs (try (rubi-eval (cdr body) binds) (lambda (e) 'rhs-error))))
    (cond ((equal? rhs 'rhs-error) 'rhs-err)
          ((equal? rhs 'unknown) 'rhs-skip)
          ((contains-sym? rhs 'integrate) 'rhs-skip)
          ; спецфункции — до численной проверки: у polylog численное Li₂ уходит в бесконечную рекурсию
          ; (SolveNum.li2Complex — переполнение стека, процесс падает), а ветви всё равно не проверить
          ((any? (lambda (h) (rubi-has-head? rhs h)) fz-special-heads) 'rhs-warn)
          (else
           (let ((how (try (integrate::int-check-rubi-formal rhs (simplify ex) 'x)
                           (lambda (e) 'rhs-err))))
             (cond ((or (equal? how 'simplify) (equal? how 'numeric) (equal? how 'together)) 'rhs-ok)
                   ((equal? how 'bad) 'rhs-bad)
                   (else 'rhs-skip)))))))

; ---------- классификация правила ----------

(define (fuzz-rule r)
  (let* ((id (nth r 1)) (ord (nth r 0)) (gen (fz-example r)))
    (if (not (equal? (car gen) 'ok))
        (list id 'cond-unsat (fuzz-clean (to-string (if (nth gen 2) (nth gen 2) "-")))
              "-" (to-string ord) "-" "-" "-")
        (let* ((ex (cadr gen)) (binds (caddr gen))
               (ne (try (rubi-norm-form ex) (lambda (e) ex)))
               (m (try (ac-match-prepared
                        (rubi-prepared r) ne
                        (rubi-cond-fn r))
                       (lambda (e) #f)))
               (st0 (fz-step ne))
               (st (if (and (pair? st0) (>= (length st0) 2)) st0 'timeout))
               (res (if (pair? st) (car st) 'timeout))
               (log (if (pair? st) (cadr st) '()))
               (fires (if (pair? log) (fz-fires log) '()))
               (fire1 (if (pair? fires) (car fires) #f))
               (same (and fire1 (equal? (cadr fire1) id)))
               (status (cond ((equal? res 'timeout) 'error)
                             (same 'self)
                             ; ответ дали базовые определения Int ядра (константа, линейность, sin/cos линейного
                             ; аргумента) — до перебора правил дело не дошло, как и в исходнике Rubi
                             ((and (not fire1) (not (equal? res 'unknown))) 'base)
                             ((not fire1) 'none)
                             ((< (fz-ord-of (cadr fire1)) ord) 'earlier)
                             (else 'later)))
               (reason
                (cond ((or (equal? status 'self) (equal? status 'error) (equal? status 'base)) "-")
                      ((equal? status 'earlier) (cadr fire1))
                      ; исчерпан бюджет попыток движка: «мёртвым» правилу быть не обязательно —
                      ; это ограничение фаззера, а не дефект порта (класс отдельный)
                      ((and (not fire1) (>= *rubi-tries* *rubi-tries-limit*)) "tries-limit")
                      ((not m) "normalized")
                      ((pair? (fz-rec-of log 'cond-fail id ne))
                       (let ((cf (car (fz-rec-of log 'cond-fail id ne))))
                         (string-append "cond:" (to-string (nth cf 2)) ":" (to-string (nth cf 3)))))
                      ((pair? (fz-rec-of log 'rhs-fail id ne))
                       (string-append "rhs-fail:" (to-string (nth (car (fz-rec-of log 'rhs-fail id ne)) 2))))
                      ((pair? (fz-rec-of log 'rhs-fail id #f))
                       (string-append "sub-rhs-fail:" (to-string (nth (car (fz-rec-of log 'rhs-fail id #f)) 2))))
                      (else "index")))
               (rhs (if (equal? status 'self)
                        (try (fz-rhs-check r ex (or (nth fire1 4) binds)) (lambda (e) 'rhs-err))
                        "-")))
          (list id status reason (if fire1 (cadr fire1) "-") (to-string ord)
                (fuzz-clean (format "~s" ex)) (fuzz-clean (format "~s" ne)) (to-string rhs))))))

; отладка условия: (fuzz-cond-dbg "1.1.1.1" 1)
; отладка образца: (fuzz-match-dbg "1.1.1.1" 3)
(define (fuzz-match-dbg file idx)
  (rubi-integrate 1 'x)
  (let* ((rs (fuzz-file-rules file)) (r (nth rs idx))
         (prep (rubi-prepared r))
         (gen (fz-example r)))
    (display (string-append "id=" (nth r 1) " prep=" (format "~s" prep))) (newline)
    (display (string-append "ex=" (format "~s" (cadr gen)))) (newline)
    (display (string-append "match(ex)=" (format "~s" (try (ac-match-prepared prep (cadr gen) (rubi-cond-fn r)) (lambda (e) (string-append "ERR " (to-string e))))))) (newline)
    (display (string-append "match(ne)=" (format "~s" (try (ac-match-prepared prep (rubi-norm-form (cadr gen)) (rubi-cond-fn r)) (lambda (e) (string-append "ERR " (to-string e))))))) (newline)))

(define (fuzz-cond-dbg file idx)
  (rubi-integrate 1 'x)
  (let* ((rs (fuzz-file-rules file)) (r (nth rs idx)) (pat (nth r 2))
         (body (rubi-fixed r)) (cf (rubi-cond-fn r))
         (vars (fz-pvars pat '()))
         (binds (map (lambda (v) (list v 2)) vars)))
    (display (string-append "id=" (nth r 1) " pat=" (format "~s" pat) " vars=" (format "~s" vars)
                            " cond=" (format "~s" (car body)))) (newline)
    (display (string-append "cf=" (to-string cf) " binds=" (format "~s" binds))) (newline)
    (display (format "res=~s" (try (if cf (cf binds) 'no-cond)
                                   (lambda (e) (string-append "ERR: " (to-string e))))))
    (newline)))

; отладка одного правила по id: (fuzz-one-id "Rubi 1.1.2.8 #116")
(define (fuzz-one-id id)
  (rubi-integrate 1 'x)
  (let ((r (car (filter (lambda (q) (equal? (nth q 1) id)) *rubi-rules*))))
    (display (string-join (map (lambda (x) (if (string? x) x (to-string x))) (fuzz-rule r)) "\t"))
    (newline)))

; отладка отсева правила индексом: (fuzz-index-dbg "Rubi 1.1.1.2 #3")
(define (fuzz-index-dbg id)
  (rubi-integrate 1 'x)
  (let* ((r (car (filter (lambda (q) (equal? (nth q 1) id)) *rubi-rules*)))
         (gen (fz-example r)))
    (if (not (equal? (car gen) 'ok))
        (begin (display (string-append "cond-unsat: " (to-string (nth gen 2)))) (newline))
        (let* ((ex (cadr gen))
               (ne (try (rubi-norm-form ex) (lambda (e) ex)))
               (heads (rubi-expr-heads ne '()))
               (hs (rubi-head-set heads))
               (xc (rubi-expr-xfactors ne 'x))
               (exps (rubi-expr-exponents ne '()))
               (ifeats (and *rubi-index* (rubi-expr-feats ne)))
               (all (rubi-candidates ne heads))
               (in? (any? (lambda (q) (equal? (nth q 1) id)) all)))
          (display (string-append "id=" id " ex=" (format "~s" ex))) (newline)
          (display (string-append "ne=" (format "~s" ne))) (newline)
          (display (string-append "pat=" (format "~s" (nth r 2)) " req=" (format "~s" (nth r 6)))) (newline)
          (display (string-append "heads=" (format "~s" heads) " in-candidates=" (to-string in?) " ncand=" (to-string (length all)))) (newline)
          (display (string-append "prefilter=" (to-string (try (rubi-prefilter-set? (nth r 6) hs) (lambda (e) 'err)))
                                  " root=" (to-string (try (rubi-root-ok? (rubi-rule-root-key r) ne) (lambda (e) 'err)))
                                  " shape=" (to-string (try (rubi-shape-ok? r xc exps) (lambda (e) 'err)))
                                  " feats=" (to-string (try (rubi-feats-ok? r ifeats) (lambda (e) 'err))))) (newline)
          (let ((st (fz-step ne)))
            (display (string-append "ans=" (format "~s" (car st)) " tries-limit=" (to-string *rubi-tries-limit*)
                                    " reason=" (to-string *rubi-last-reason*))) (newline)
            (for-each (lambda (rec)
                        (if (and (pair? rec) (equal? (cadr rec) id))
                            (begin (display (format "  id-rec ~s" rec)) (newline))))
                      (cadr st)))))))

(define (fuzz-file-rules file)
  (reverse (filter (lambda (r) (and (nth r 9) (equal? (nth r 9) file))) *rubi-rules*)))

; отладка: одно правило файла без перехвата ошибок — (fuzz-one "1.1.1.1" 0)
(define (fuzz-one file idx)
  (rubi-integrate 1 'x)
  (let ((rs (fuzz-file-rules file)))
    (display (string-join (map (lambda (x) (if (string? x) x (to-string x)))
                               (fuzz-rule (nth rs idx))) "\t"))
    (newline)))

(define (fuzz-run files-path)
  (rubi-integrate 1 'x)                     ; загрузка всех правил
  ; Бюджет попыток движка на один пример ограничивается детерминированно (rubi-tries-limit), а не
  ; call-with-time-limit: таймаут бросает поток и оставляет глобальные флаги журнала в чужом состоянии —
  ; после первого таймаута все следующие правила выглядят «мёртвыми» (проверено: гл. 1.2 давала self=0).
  (set! *rubi-tries-limit* 6000)
  (let ((files (fuzz-lines files-path)))
    (for-each
     (lambda (file)
       (let ((rs (fuzz-file-rules file)))
         (if (null? rs)
             (begin (display (string-append file "\tNOFILE")) (newline))
             (begin
               ; ход прогона — строкой «# файл …» (fuzz.mjs такие строки пропускает)
               (display (string-append "# файл " file " правил " (to-string (length rs)))) (newline)
               (for-each
                (lambda (r)
                  (let ((res (try (fuzz-rule r)
                                  (lambda (e)
                                    (list (nth r 1) 'error
                                          (string-append "fuzz-error:" (fuzz-clean (to-string e)))
                                          "-" (to-string (nth r 0)) "-" "-" "-" "-")))))
                    (if (or (not (pair? res)) (< (length res) 8))
                        (set! res (list (nth r 1) 'error "fuzz-shape" "-" (to-string (nth r 0)) "-" "-" "-")))
                    (display (string-join (map (lambda (x) (if (string? x) x (to-string x))) res) "\t"))
                    (display "\t")
                    (display file)
                    (newline)))
                rs)))))
     files)
    'ok))



