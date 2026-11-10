; rubi/engine.lisp — движок правил Rubi (RUBI.1): порядок правил, индексация, int-check.
; Правила генерируются tools/rubi в lib/rubi/rules и грузятся лениво при первом вызове.
(module rubi
  (export rubi-integrate rubi-integrate-form rubi-trace-run))

; общий бюджет вызова (с загрузкой правил), с: стенд убивает задачу на 5 с и перезапускает процесс,
; поэтому движок должен вернуть unknown раньше — иначе каждая отказная задача = TIMEOUT + холодный старт.
(define rubi-time-limit 4.0)
(define rubi-max-depth 32)
(define *rubi-rules* '())
(define *rubi-index* (make-hash))
(define *rubi-prepared* (make-hash))  ; id → (np ip vars): образец компилируется при первом использовании
(define *rubi-fixed* (make-hash))     ; id → (cond . rhs) с переписанными именами Mathematica
(define *rubi-cond-fns* (make-hash))  ; id → замыкание условия: (lambda (binds) ...) без eval на кандидата
(define *rubi-failed* (make-hash))    ; выражение → (таблица id → #t): неудачи одного вызова rubi-integrate
(define *rubi-cache-hits* 0)          ; сколько раз кэш неудач сэкономил попытку
(define *rubi-cands2* (make-hash))    ; выражение → кандидаты, прошедшие отсев по головам и форме (RUBI.S8)
(define *rubi-cands* (make-hash))     ; выражение → список кандидатов (в пределах вызова)
(define *rubi-errors* (make-hash))    ; текст ошибки вычисления правила → число (диагностика)
(define *rubi-loaded* #f)
(define *rubi-depth* 0)
(define *rubi-stack* '())
(define *rubi-last-reason* #f)
(define *rubi-last-rule* #f)
(define *rubi-tries* 0)
(define *rubi-ord* 0)
(define rubi-rule-files '())

; RUBI.9: профиль по фазам. Включается флагом *rubi-prof*; в обычной работе цена — одна проверка #f.
; Времена инклюзивные: eval включает вложенные вызовы, match и check — листовые фазы.
; eval-self считается как «своё время минус вложенные вызовы»; у вызова, прерванного бюджетом,
; стек не разматывается и self выходит отрицательным — такие замеры годны только для завершённых задач.
(define *rubi-prof* #f)
(define *rubi-p-match* 0)
(define *rubi-p-eval* 0)
(define *rubi-p-check* 0)
(define *rubi-p-matches* 0)
(define *rubi-p-evals* 0)
(define *rubi-p-checks* 0)
(define *rubi-p-calls* 0)
; для eval: сумма времени всех вызовов (sum) и своё время за вычетом вложенных (self)
(define *rubi-p-eval-sum* 0)
(define *rubi-p-eval-self* 0)
; RUBI.13: учёт вычислений условий правил — сколько вызовов, сколько времени, самые медленные.
(define *rubi-p-cond* 0)
(define *rubi-cond-calls* 0)
(define *rubi-cond-slow* '())
(define *rubi-cond-slow-limit* 5)
(define *rubi-matched* '())
; Этап C: мемоизация «выражение → результат | unknown» в пределах вызова, журнал причин отказа;
; настенные 5 с — единственный реальный бюджет (см. ниже про предел попыток).
(define *rubi-memo* (make-hash))
(define *rubi-fail-reasons* '())
; Предел попыток сопоставления на задачу — только страховка от бесконечного перебора, а не бюджет.
; Замер (2026-11-08): задача t_1_1_1_3/34 берётся после **6 215** попыток за 414 мс — прежние 5 000
; отсекали готовый ответ, а 3 000 на пилоте стоили 61 OK. Самая быстрая наблюдённая скорость —
; ≈15 000 попыток/с, значит 5 с настенного бюджета позволяют ≈75 000 попыток: 100 000 заведомо
; выше и внутри бюджета не срабатывает.
(define *rubi-tries-limit* 100000)
; Семантика Rubi: первое правило, чьи образец и условие подошли, окончательное — даже если его правая
; часть дала `unknown` (вложенный Int отказал). Перебор следующего кандидата — только после ошибки правой
; части или провала int-check. Флаг оставлен, чтобы сравнивать с прежним поведением одним set!.
(define *rubi-first-rule-final* #t)

; Журнал причин отказа: alist (причина . число), чтобы гистограмму можно было напечатать в профиле.
(define (rubi-note-reason why)
  (let* ((old (assoc why *rubi-fail-reasons*))
         (n (+ 1 (if old (cdr old) 0))))
    (set! *rubi-fail-reasons*
          (cons (cons why n)
                (filter (lambda (p) (not (equal? (car p) why))) *rubi-fail-reasons*)))))

(define (rubi-prof-reset)
  (set! *rubi-p-match* 0)
  (set! *rubi-p-eval* 0)
  (set! *rubi-p-check* 0)
  (set! *rubi-p-matches* 0)
  (set! *rubi-p-evals* 0)
  (set! *rubi-p-checks* 0)
  (set! *rubi-p-calls* 0)
  (set! *rubi-p-eval-sum* 0)
  (set! *rubi-p-eval-self* 0)
  (set! *rubi-p-cond* 0)
  (set! *rubi-p-prep* 0)
  (set! *rubi-p-norm* 0)
  (set! *rubi-p-step* 0)
  (set! *rubi-p-inner* 0)
  (set! *rubi-p-rhs* 0)
  (set! *rubi-p-err* 0)
  (set! *rubi-p-scan* 0)
  (set! *rubi-p-int-acc* 0)
  (set! *rubi-cond-calls* 0)
  (set! *rubi-cond-timeouts* 0)
  (set! *rubi-cond-slow* '())
  (set! *rubi-matched* '()))

; Топ частот по хэш-таблице «ключ → число»: ошибки правил и вызовы заглушек — гистограммы
; для выбора того, что реализовывать следующим (этап D).
(define (rubi-hist-top h n)
  (take (sort (map (lambda (k) (cons (hash-ref h k 0) k)) (hash-keys h))
              (lambda (a b) (> (car a) (car b))))
        n))

(define (rubi-error-top n) (rubi-hist-top *rubi-errors* n))

(define (rubi-prof-data)
  (list (cons 'calls *rubi-p-calls*)
        (cons 'matches *rubi-p-matches*)
        (cons 'match-us *rubi-p-match*)
        (cons 'evals *rubi-p-evals*)
        (cons 'eval-us *rubi-p-eval*)
        (cons 'eval-self *rubi-p-eval-self*)
        (cons 'checks *rubi-p-checks*)
        (cons 'check-us *rubi-p-check*)
        (cons 'prep-us *rubi-p-prep*)
        (cons 'norm-us *rubi-p-norm*)
        (cons 'step-us *rubi-p-step*)
        (cons 'inner-us *rubi-p-inner*)
        (cons 'rhs-us *rubi-p-rhs*)
        (cons 'err-us *rubi-p-err*)
        (cons 'scan-us *rubi-p-scan*)
        (cons 'cond-calls *rubi-cond-calls*)
        (cons 'cond-us *rubi-p-cond*)
        (cons 'cond-timeouts *rubi-cond-timeouts*)
        (cons 'cond-slow *rubi-cond-slow*)
        (cons 'fail-reasons *rubi-fail-reasons*)
        (cons 'tries *rubi-tries*)
        (cons 'errors (rubi-error-top 20))
        (cons 'stubs (rubi-hist-top rubi::*rubi-stub-calls* 20))
        (cons 'matched *rubi-matched*)))

; RUBI.S16: образцы с Sqrt/Exp приводятся к степеням так же, как выражение (rubi-int-body: головы, (u^p)^q,
; ac-norm): раньше образец (/ 1 (sqrt (+ a (* b x^2)))) оставался с головой sqrt, а выражение к тому времени уже
; было (^ u -1/2) - 505 правил главы 1 (1.1.2.1 #16-#18 = ∫1/sqrt(a + b x^2) и др.) не срабатывали никогда;
; головы sqrt/exp также попадали в обязательные головы индекса, которых в выражении нет.
(define (rubi-pat-normalize pat)
  (if (rubi-sqrt-head? pat)
      (ac-strip-units (rubi-collapse-pow (ac-norm (rubi-normalize-heads pat))))
      pat))

(define (rubi-add-rule id pat0 cond rhs)
  (set! *rubi-rules*
        (let ((pat (rubi-pat-normalize pat0)))
          (cons (list *rubi-ord* id pat cond rhs #f (rubi-pat-heads pat '())
                      (rubi-pat-min-factors pat) (rubi-pat-exponents pat '()))
                *rubi-rules*)))
  (set! *rubi-ord* (+ *rubi-ord* 1)))


; Имена Mathematica, попавшие в сгенерированные условия и правые части без перевода:
; not-equal (!=), part ([[i]]), diff (D[u,x] — у нас порядок аргументов обратный).
; Переписываются в приватные обёртки Rubi; (quote ...) не трогается.
(define (rubi-fix-names f)
  (cond ((symbol? f)
         (cond ((equal? f 'not-equal) 'rubi::rubi-not-equal)
               ((equal? f 'part) 'rubi::rubi-part)
               ((equal? f 'diff) 'rubi::rubi-diff)
               ((equal? f 'Apart) 'rubi::rubi-apart)
               ((equal? f 'SmartApart) 'rubi::rubi-smart-apart)
               (else f)))
        ((pair? f)
         (cond
           ; Ветвь `If[условие, результат, неприменимо]` правой части: генератор записал её как 'unknown.
           ; Это «правило не сработало» (пробуем следующее), а не отказ вложенного Int — иначе правила
           ; 1.4.1 #19/#21/#22 (проверка Pp, Qq) обрывают перебор раньше 1.1.1.5–1.1.1.7: ∫(a+b*x)(a*c-b*c*x)^4.
           ((equal? f '(quote unknown)) '(quote rubi-no-rule))
           ((equal? (car f) 'quote) f)
           (else (cons (rubi-fix-names (car f)) (map rubi-fix-names (cdr f))))))
        (else f)))

; RUBI.2c: компиляция образца при загрузке занимала заметную долю старта — теперь при первом обращении.
; профиль: время первой подготовки правила (компиляция образца, условия, переписывание имён)
(define *rubi-p-prep* 0)
(define *rubi-p-norm* 0)    ; профиль: нормализация выражения в rubi-int
(define *rubi-p-step* 0)    ; профиль: рамка with-step за вычетом тела
(define *rubi-p-inner* 0)   ; профиль: тело with-step (вызов правой части)
(define (rubi-prep-note t0)
  (if t0 (set! *rubi-p-prep* (+ *rubi-p-prep* (- (clock-us) t0)))))

(define (rubi-prepared r)
  (let ((id (nth r 1)))
    (or (hash-ref *rubi-prepared* id #f)
        (let* ((t0 (and *rubi-prof* (clock-us)))
               (p (ac-build-prepared (nth r 2))))
          (hash-set! *rubi-prepared* id p)
          (rubi-prep-note t0)
          p))))

; RUBI.S8: файлы правил уже содержат переписанные имена (tools/rubi/generate.mjs, fixNames) —
; обход условия и правой части при первом применении (561 тыс. вызовов rubi-fix-names на задачу,
; до 3 с) не нужен. rubi-fix-names остаётся для правил, написанных вручную (применять к условию и правой части самому).
(define (rubi-fixed r) (cons (nth r 3) (nth r 4)))

; Замена ?a -> a только для переменных образца; (quote ...) не трогается.
(define (rubi-strip-vars f alst)
  (cond ((symbol? f) (let ((p (assoc f alst))) (if p (cdr p) f)))
        ((pair? f)
         (if (equal? (car f) 'quote) f
             (cons (car f) (map (lambda (e) (rubi-strip-vars e alst)) (cdr f)))))
        (else f)))

; RUBI.13: дешёвые конъюнкты условия проверяются до полного тела. В условиях Rubi порядок
; конъюнктов исходный, и дорогие вычисления (деление многочленов, дифференцирование) могут стоять
; раньше дешёвых проверок вроде (rubi-integerq ?p) или (rubi-ltq (* ?p ?q) 0); предпроверка
; отсекает кандидата, не трогая порядок самого тела (оно считается как раньше, если прошла).
(define (rubi-form-size e)
  (if (pair? e)
      (let loop ((l (cdr e)) (n 1))
        (if (null? l) n (loop (cdr l) (+ n (rubi-form-size (car l))))))
      1))

; RUBI.S8: ответ по голове кэшируется (одни и те же головы повторяются в тысячах условий)
(define *rubi-exp-heads* (make-hash))
(define (rubi-expensive-head? h)
  (and (symbol? h)
       (let ((c (hash-ref *rubi-exp-heads* h 'none)))
         (if (equal? c 'none)
             (let* ((s (to-string h))
                    (v (or (string-contains? s "polynomial")
                           (string-contains? s "algebraic-function")
                           (string-contains? s "poly-q")
                           (and (member? s '("diff" "simplify" "expand" "factor" "apart" "together" "solve")) #t))))
               (hash-set! *rubi-exp-heads* h v)
               v)
             c))))

; Ранний выход: после первой дорогой головы остальные не смотрим; без рекурсии по хвосту-атомам
(define (rubi-form-expensive? e)
  (and (pair? e)
       (or (rubi-expensive-head? (car e))
           (let loop ((l (cdr e)))
             (cond ((null? l) #f)
                   ((and (pair? (car l)) (rubi-form-expensive? (car l))) #t)
                   (else (loop (cdr l))))))))

(define (rubi-cheap-conjunct? e)
  (and (<= (rubi-form-size e) 10) (not (rubi-form-expensive? e))))

; конъюнкты верхнего уровня, вложенные and разворачиваются
(define (rubi-conjuncts e)
  (if (and (pair? e) (equal? (car e) 'and))
      (let flat ((l (cdr e)) (acc '()))
        (if (null? l) acc (flat (cdr l) (append acc (rubi-conjuncts (car l))))))
      (list e)))

; Замер одного вычисления условия правила: при выключенном профиле — прямой вызов без накладных.
; Лимит на одно условие (этап B): превышение считается ложью — тяжёлое условие
; (expand/poly-q на большом Px) иначе съедает сотни миллисекунд бюджета одной попытки.
; ВЫКЛЮЧЕН по умолчанию (#f): на Linux-раннере call-with-time-limit на каждом условии привёл к
; регрессии пилота (OK 46 % -> 15,6 %, 83 % таймаутов). Включать только после замера на стенде.
(define *rubi-cond-limit* #f)
(define *rubi-cond-timeouts* 0)
(define *rubi-cond-errors* 0)   ; сколько условий упало с ошибкой (диагностика)

(define (rubi-cond-check id f binds)
  (let* ((t0 (and *rubi-prof* (clock-us)))
         ; Ошибка вычисления условия (неподдержанная утилита, «Не число») = условие ложно для этих привязок.
         ; Перехват здесь, у места броска: исключение, прошедшее через весь стек сопоставителя (CPS,
         ; тысячи кадров), стоило ≈ 60 мс — по 10–15 таких условий на каждое подвыражение.
         (g (lambda ()
              (try (f binds)
                   (lambda (err)
                     (set! *rubi-cond-errors* (+ *rubi-cond-errors* 1))
                     (let ((m (string-append id " | cond | " (substring (to-string err) 0 (min 80 (string-length (to-string err)))))))
                       (hash-set! *rubi-errors* m (+ 1 (hash-ref *rubi-errors* m 0))))
                     #f))))
         (w (if *rubi-cond-limit*
                (call-with-time-limit *rubi-cond-limit* g)
                (list 'ok (g))))
         (v (if (and (pair? w) (equal? (car w) 'ok))
                (cadr w)
                (begin (set! *rubi-cond-timeouts* (+ *rubi-cond-timeouts* 1)) #f))))
    (if t0
        (let ((us (- (clock-us) t0)))
          (set! *rubi-p-cond* (+ *rubi-p-cond* us))
          (set! *rubi-cond-calls* (+ *rubi-cond-calls* 1))
          (set! *rubi-cond-slow*
                (take-n (insert-sorted (cons us id) *rubi-cond-slow*) *rubi-cond-slow-limit*))))
    v))

(define (insert-sorted x l)
  (cond ((null? l) (list x))
        ((> (car x) (car (car l))) (cons x l))
        (else (cons (car l) (insert-sorted x (cdr l))))))

(define (take-n l n)
  (if (or (null? l) (= n 0)) '() (cons (car l) (take-n (cdr l) (- n 1)))))

; RUBI.D2: журнал отказов для диагностики (tools/rubi/diagnose.mjs). Выключен (#f): в обычной работе цена -
; одна проверка флага на ложное условие и на шаг цикла. Записи (в *rubi-trace-log*, новые в голове):
;   (cond-fail id conj util expr)  - образец подошёл, условие ложно; conj - номер первого ложного конъюнкта (с 1),
;                                    util - первая утилита rubi:: в нём или #f; пишется только для тупикового expr
;   (rhs-fail id reason expr)      - правая часть не дала ответа (error/tainted/check/nested-unknown/no-rule/unknown)
;   (dead expr ncands nmatched)    - подвыражение, для которого перебраны все кандидаты и ни один не дал ответа
;   (seen expr)                    - нормализованное подвыражение дошло до цикла правил
(define *rubi-trace* #f)
(define *rubi-trace-log* '())
(define *rubi-trace-ne* #f)                 ; выражение, для которого сейчас сопоставляется правило
(define *rubi-trace-cf* (make-hash))        ; expr -> (alist id -> (conj . util)): ложные условия при подошедшем образце
(define *rubi-trace-nc* (make-hash))        ; expr -> число кандидатов после отсева
(define *rubi-trace-conjs* (make-hash))     ; id -> список (util . замыкание конъюнкта)
(define *rubi-trace-err* #f)

(define (rubi-trace-add rec) (set! *rubi-trace-log* (cons rec *rubi-trace-log*)))

(define (rubi-trace-reset)
  (set! *rubi-trace-log* '())
  (set! *rubi-trace-ne* #f)
  (set! *rubi-trace-cf* (make-hash))
  (set! *rubi-trace-nc* (make-hash)))

; первая утилита rubi:: в конъюнкте (обход в глубину слева направо)
(define (rubi-trace-util c)
  (cond ((not (pair? c)) #f)
        ((and (symbol? (car c)) (string-contains? (to-string (car c)) "rubi::")) (car c))
        (else (let loop ((l (cdr c)))
                (cond ((null? l) #f)
                      ((rubi-trace-util (car l)) (rubi-trace-util (car l)))
                      (else (loop (cdr l))))))))

(define (rubi-trace-cond id cs alst binds)
  (let* ((fns (or (hash-ref *rubi-trace-conjs* id #f)
                  (let* ((bindings (map (lambda (v) (list (cdr (assoc v alst)) (list 'cadr (list 'assoc (list 'quote v) 'binds)))) (map car alst)))
                         (l (map (lambda (c)
                                   (cons (rubi-trace-util c)
                                         (eval (list 'lambda '(binds) (cons 'let (cons bindings (list (rubi-strip-vars c alst))))))))
                                 cs)))
                    (hash-set! *rubi-trace-conjs* id l)
                    l)))
         (hit (let loop ((l fns) (i 1))
                (cond ((null? l) (cons 0 #f))
                      ((not (try ((cdr (car l)) binds) (lambda (e) #f))) (cons i (car (car l))))
                      (else (loop (cdr l) (+ i 1))))))
         (tbl (hash-ref *rubi-trace-cf* *rubi-trace-ne* '()))
         (old (assoc id tbl)))
    ; из нескольких попыток одного правила на одном выражении - та, что дошла дальше
    (if (or (not old) (> (car hit) (cadr old)))
        (hash-set! *rubi-trace-cf* *rubi-trace-ne*
                   (cons (list id (car hit) (cdr hit)) (filter (lambda (p) (not (equal? (car p) id))) tbl))))))

; Компиляция условия правила в замыкание от привязок: на каждого кандидата больше нет
; ни ac-where-sub, ни eval — только let и вызов готовой лямбды.
(define (rubi-cond-fn r)
  (let ((id (nth r 1)) (cd (car (rubi-fixed r))))
    (if (null? cd)
        #f
        (or (hash-ref *rubi-cond-fns* id #f)
            (let* ((vars (caddr (rubi-prepared r)))
                   (alst (map (lambda (v)
                                (let ((s (to-string v)))
                                  (cons v (string->symbol (substring s 1 (string-length s))))))
                              vars))
                   (body0 (rubi-strip-vars cd alst))
                   (cs (rubi-conjuncts body0))
                   (cheap (filter rubi-cheap-conjunct? cs))
                   (body (if (or (null? cheap) (equal? (length cheap) (length cs)))
                             body0
                             (cons 'and (append cheap (filter (lambda (c) (not (rubi-cheap-conjunct? c))) cs)))))
                   (bindings (map (lambda (v)
                                    (list (cdr (assoc v alst))
                                          (list 'cadr (list 'assoc (list 'quote v) 'binds))))
                                  vars))
                   (t0 (and *rubi-prof* (clock-us)))
                   (f (eval (list 'lambda '(binds)
                                  (cons 'let (cons bindings (list body))))))
                   (_ (rubi-prep-note t0)))
              (let ((g (lambda (binds)
                         (let ((v (rubi-cond-check id f binds)))
                           (if (and *rubi-trace* (not v)) (rubi-trace-cond id cs alst binds))
                           v))))
                (hash-set! *rubi-cond-fns* id g)
                g))))))

(define (rubi-pvar? x)
  (and (symbol? x)
       (let* ((s (to-string x)) (n (string-length s)))
         (and (> n 0) (equal? (substring s 0 1) "?")))))

; Этап B, п.3: форма образца. Правило требует не меньше x-зависимых множителей, чем в образце
; конкретных (не голых `?u`) множителей, и содержит литеральные показатели (1/3, 3/2, 9/4 …),
; которых в выражении нет — тогда правило не совпадёт и его можно не перебирать.
(define *rubi-shape-index* #t)
; Диагностика: если это список — в него попадают все нормализованные выражения, дошедшие до rubi-int
; (проверка индекса на подвыражениях настоящих задач). В обычной работе #f.
(define *rubi-seen* #f)

(define (rubi-expr-xfactors e x)
  (cond ((not (contains-sym? e x)) 0)
        ((and (pair? e) (equal? (car e) '*))
         (let loop ((fs (cdr e)) (n 0))
           (if (null? fs)
               n
               (loop (cdr fs) (if (contains-sym? (car fs) x) (+ n 1) n)))))
        (else 1)))

(define (rubi-pat-min-factors pat)
  (if (and (pair? pat) (equal? (car pat) '*))
      (let loop ((fs (cdr pat)) (n 0))
        (if (null? fs)
            n
            (loop (cdr fs) (if (rubi-pvar? (car fs)) n (+ n 1)))))
      0))

(define (rubi-expr-exponents e acc)
  (if (pair? e)
      (let ((acc (if (and (equal? (car e) '^) (= (length (cdr e)) 2) (number? (nth e 2)))
                     (cons (nth e 2) acc)
                     acc)))
        (let loop ((l (cdr e)) (a acc))
          (if (null? l) a (loop (cdr l) (rubi-expr-exponents (car l) a)))))
      acc))

(define (rubi-pat-exponents p acc)
  (if (pair? p)
      (let* ((h (car p))
             (literal (and (symbol? h) (not (rubi-pvar? h))))
             (acc (if (and literal (equal? h '^) (= (length (cdr p)) 2) (number? (nth p 2)))
                      (cons (nth p 2) acc)
                      acc)))
        (let loop ((l (cdr p)) (a acc))
          (if (null? l) a (loop (cdr l) (rubi-pat-exponents (car l) a)))))
      acc))

(define (rubi-exps-subset? need have)
  (let loop ((l need))
    (cond ((null? l) #t)
          ((member? (car l) have) (loop (cdr l)))
          (else #f))))

; Правило r (элемент *rubi-rules*) допускается формой выражения: xc — число x-зависимых множителей
; верхнего уровня, exps — числовые показатели степеней выражения.
(define (rubi-shape-ok? r xc exps)
  (or (not *rubi-shape-index*)
      (and (>= xc (nth r 7)) (rubi-exps-subset? (nth r 8) exps))))

; Диагностика корректности индекса: правила, которые индекс по форме отсёк, хотя по головам
; они проходили, но образец структурно подходит к выражению (условие не проверяется — это
; надмножество настоящих совпадений). Пусто — индекс ничего не потерял. Обязательные головы
; здесь не проверяются повторно: берутся правила из rubi-candidates, то есть уже отобранные.
(define (rubi-shape-lost e x)
  (set! *rubi-cands* (make-hash))
  (let* ((ne (ac-strip-units (ac-norm (if (rubi-sqrt-head? e) (rubi-normalize-heads e) e))))
         (heads (rubi-expr-heads ne '()))
         (xc (rubi-expr-xfactors ne x))
         (exps (rubi-expr-exponents ne '())))
    (filter (lambda (r)
              (and (rubi-prefilter? (nth r 6) heads)
                   (not (rubi-shape-ok? r xc exps))
                   (let ((b (try (ac-match-prepared (rubi-prepared r) ne #f) (lambda (err) #f))))
                     (and b #t))))
            (rubi-candidates ne heads))))

(define (rubi-head-key pat)
  (if (and (pair? pat) (symbol? (car pat)) (not (rubi-pvar? (car pat))))
      (car pat)
      '*))

(define (rubi-pat-heads p acc)
  (cond ((symbol? p) acc)
        ((pair? p)
         (let* ((h (car p))
                (acc (if (and (symbol? h) (not (rubi-pvar? h))
                              (not (member? h '(* ^ / -))))
                         (cons h acc)
                         acc)))
           (rubi-pat-heads-list (cdr p) acc)))
        (else acc)))

(define (rubi-pat-heads-list l acc)
  (if (null? l) acc (rubi-pat-heads-list (cdr l) (rubi-pat-heads (car l) acc))))

(define (rubi-expr-heads e acc)
  (if (pair? e)
      (let ((acc (if (symbol? (car e)) (cons (car e) acc) acc)))
        (rubi-expr-heads-list (cdr e) acc))
      acc))

(define (rubi-expr-heads-list l acc)
  (if (null? l) acc (rubi-expr-heads-list (cdr l) (rubi-expr-heads (car l) acc))))

(define (rubi-prefilter? req heads)
  (every? (lambda (h) (member? h heads)) req))

; RUBI.S8: то же по хеш-множеству голов (одно на выражение, а не member? по списку на каждое правило)
(define (rubi-head-set heads)
  (let ((h (make-hash)))
    (for-each (lambda (k) (hash-set! h k #t)) heads)
    h))

(define (rubi-prefilter-set? req hs)
  (let loop ((l req))
    (cond ((null? l) #t)
          ((hash-ref hs (car l) #f) (loop (cdr l)))
          (else #f))))

(define (rubi-unique l acc)
  (cond ((null? l) (reverse acc))
        ((member? (car l) acc) (rubi-unique (cdr l) acc))
        (else (rubi-unique (cdr l) (cons (car l) acc)))))

(define (rubi-bucket k) (hash-ref *rubi-index* k '()))

; списки правил в корзинах идут по убыванию номера порядка (cons при сборке индекса);
; слияние итеративное — рекурсия на 7.5 тыс. правил давала переполнение стека.
(define (rubi-merge2 a b)
  (let loop ((a a) (b b) (acc '()))
    (cond ((null? a) (append (reverse acc) b))
          ((null? b) (append (reverse acc) a))
          ((> (car (car a)) (car (car b))) (loop (cdr a) b (cons (car a) acc)))
          (else (loop a (cdr b) (cons (car b) acc))))))

(define (rubi-merge-lists ls)
  (cond ((null? ls) '())
        ((null? (cdr ls)) (car ls))
        (else (rubi-merge-lists (cons (rubi-merge2 (car ls) (cadr ls)) (cddr ls))))))

; Кандидаты — объединение корзин по головам, которые требует образец: правило с непустым
; набором обязательных голов может подойти, только если все они есть в выражении (rubi-prefilter?).
; Правила без таких голов (чистая алгебра) лежат в корзине none и перебираются всегда.
(define (rubi-candidates e heads)
  (or (hash-ref *rubi-cands* e #f)
      (let* ((hs (rubi-unique heads '()))
             (ls (cons (rubi-bucket 'none) (map rubi-bucket hs)))
             (ls (filter (lambda (l) (not (null? l))) ls))
             (v (reverse (rubi-merge-lists ls))))
        (hash-set! *rubi-cands* e v)
        v)))

(define (rubi-build-index)
  (set! *rubi-index* (make-hash))
  (set! *rubi-prepared* (make-hash))
  (set! *rubi-fixed* (make-hash))
  (set! *rubi-cond-fns* (make-hash))
  (for-each (lambda (r)
              (let ((hs (rubi-unique (nth r 6) '())))
                (if (null? hs)
                    (hash-set! *rubi-index* 'none (cons r (rubi-bucket 'none)))
                    (for-each (lambda (h)
                                (hash-set! *rubi-index* h (cons r (rubi-bucket h))))
                              hs))))
            *rubi-rules*))

(define (rubi-rules-loaded?) *rubi-loaded*)

; Двухступенчатая загрузка. Полная загрузка 199 файлов (5 МБ) занимает 4–6 с и на стенде (таймаут задачи
; 5 с) первая же задача убивалась, процесс перезапускался, и всё повторялось: пилот 6d19a5f дал 83 %
; таймаутов. Глава 1 (алгебра, 67 файлов, 2 МБ) — префикс общего порядка правил, ей хватает ≈1,7 с.
; Остальные главы грузятся только для входа с неалгебраическими головами (rubi-ensure-full).
(define *rubi-stage* 0)   ; 0 — правила заданы вручную (тесты), 1 — только глава 1, 2 — всё

(define (rubi-stage1-file? f)
  (and (> (string-length f) 2) (equal? (substring f 0 2) "1.")))

; RUBI.CH: утилиты, нужные только своим главам, живут в lib/rubi/utils-<буква>.lisp:
; a — 1.1.2–1.1.4, b — 1.2–1.4, c — 4, d — 2–3. Файл грузится перед правилами своей главы один раз; отсутствующий файл —
; не ошибка (глава ещё без своих утилит), любая другая ошибка загрузки — пробрасывается.
(define rubi-chapter-utils
  '(("1.1.2" "a") ("1.1.3" "a") ("1.1.4" "a") ("1.2" "b") ("1.3" "b") ("1.4" "b") ("4." "c") ("2." "d") ("3." "d")))
(define *rubi-chapter-utils-loaded* '())
(define (rubi-chapter-letter f)
  (let loop ((l rubi-chapter-utils))
    (cond ((null? l) #f)
          ((let ((p (car (car l))))
             (and (>= (string-length f) (string-length p)) (equal? (substring f 0 (string-length p)) p)))
           (cadr (car l)))
          (else (loop (cdr l))))))
(define (rubi-load-chapter-utils files)
  (for-each
   (lambda (f)
     (let ((c (rubi-chapter-letter f)))
       (if (and c (not (member? c *rubi-chapter-utils-loaded*)))
           (begin
             (set! *rubi-chapter-utils-loaded* (cons c *rubi-chapter-utils-loaded*))
             (try (load (string-append lib-dir "rubi/utils-" c ".lisp"))
                  (lambda (e)
                    (if (string-contains? (to-string e) "файл не найден") #f (error (to-string e)))))))))
   files))

(define (rubi-load-files files)
  ; *rubi-rules* хранится по возрастанию порядка; add-rule добавляет в голову — разворачиваем туда и обратно
  (rubi-load-chapter-utils files)
  (set! *rubi-rules* (reverse *rubi-rules*))
  (for-each (lambda (f) (load (string-append lib-dir "rubi/rules/" f ".lisp"))) files)
  (set! *rubi-rules* (reverse *rubi-rules*))
  (rubi-build-index))

(define (rubi-ensure)
  (if *rubi-loaded*
      #t
      (begin
        (load (string-append lib-dir "rubi/rules/order.lisp"))
        (rubi-load-files (filter rubi-stage1-file? rubi-rule-files))
        (set! *rubi-stage* 1)
        (set! *rubi-loaded* #t)
        #t)))

(define (rubi-ensure-full)
  (rubi-ensure-full-until #f))

; RUBI.S16: полная загрузка (≈ 4,3 с на стенде) не помещается в 5 с задачи: процесс убивался, а следующая
; задача снова платила холодный старт. Теперь догрузка идёт по файлам и останавливается, когда часы
; (clock-us) дошли до until (#f - без предела); недогруженное доделывает следующий вызов, индекс
; перестраивается один раз в конце. Результат: #t - загружено всё, #f - вызывающий возвращает unknown.
(define *rubi-pending-files* #f)
(define (rubi-ensure-full-until until)
  (if (not (equal? *rubi-stage* 1))
      #t
      (begin
        (if (not *rubi-pending-files*)
            (set! *rubi-pending-files* (filter (lambda (f) (not (rubi-stage1-file? f))) rubi-rule-files)))
        (set! *rubi-rules* (reverse *rubi-rules*))
        (let loop ()
          (if (and (pair? *rubi-pending-files*) (or (not until) (< (clock-us) until)))
              (begin
                (rubi-load-chapter-utils (list (car *rubi-pending-files*)))
                (load (string-append lib-dir "rubi/rules/" (car *rubi-pending-files*) ".lisp"))
                (set! *rubi-pending-files* (cdr *rubi-pending-files*))
                (loop))))
        (set! *rubi-rules* (reverse *rubi-rules*))
        (if (null? *rubi-pending-files*)
            (begin (rubi-build-index)
                   (set! *rubi-stage* 2)
                   #t)
            #f))))

; вход целиком из алгебраических операций (глава 1 правил достаточна); подвыражения без x - константы
; (exp(2), pi) и голов не требуют: ∫pi/sqrt(16 - exp(2)) не должен грузить остальные главы (4,3 с)
(define (rubi-algebraic? e)
  (cond ((not (pair? e)) #t)
        ((member? (car e) '(+ * ^ / - sqrt)) (every? rubi-algebraic? (cdr e)))
        (else #f)))
(define (rubi-algebraic-in? e x)
  (cond ((not (pair? e)) #t)
        ((not (contains-sym? e x)) #t)
        ((member? (car e) '(+ * ^ / - sqrt)) (every? (lambda (a) (rubi-algebraic-in? a x)) (cdr e)))
        (else #f)))

(define (rubi-bind-pair b)
  (let* ((s (to-string (car b))) (n (string-length s)))
    (list (string->symbol (substring s 1 n))
          (list 'quote (cadr b)))))

; профиль: собственное время правых частей по правилам (за вычетом вложенных вычислений)
(define *rubi-eval-by-id* (make-hash))
(define *rubi-cur-id* #f)
(define *rubi-last-dt* 0)
; Sqrt[число] в правой части: встроенный sqrt даёт алгебраическое число root(...), которое не печатается радикалом
; и не вычисляется оракулом; Rubi держит Sqrt[3] как 3^(1/2) - так и здесь.
(define (rubi-num-sqrt u) (if (number? u) (simplify (list '^ u 1/2)) (sqrt u)))
(define (rubi-eval-binds binds) (cons (list 'sqrt (list 'quote rubi-num-sqrt)) (map rubi-bind-pair binds)))
(define (rubi-eval rhs binds)
  (if (not *rubi-prof*)
      (eval (list 'let (rubi-eval-binds binds) rhs))
      (let* ((c0 *rubi-p-eval-sum*)
             (id *rubi-cur-id*)
             (acc0 *rubi-p-int-acc*)
             (_a (set! *rubi-p-int-acc* 0))
             (t0 (clock-us))
             (v (eval (list 'let (rubi-eval-binds binds) rhs)))
             (dt (- (clock-us) t0))
             (_b (begin (set! *rubi-p-rhs* (+ *rubi-p-rhs* (- dt *rubi-p-int-acc*)))
                        (set! *rubi-p-int-acc* acc0)))
             (nested (- *rubi-p-eval-sum* c0)))
        (hash-set! *rubi-eval-by-id* id (+ (hash-ref *rubi-eval-by-id* id 0) (- dt nested)))
        (set! *rubi-last-dt* dt)
        (set! *rubi-p-eval-self* (+ *rubi-p-eval-self* (- dt nested)))
        (set! *rubi-p-eval-sum* (+ *rubi-p-eval-sum* dt))
        v)))

; Отказ с причиной: причина идёт в журнал (гистограмма — в профиле), результат просто unknown.
(define (rubi-fail why)
  (set! *rubi-last-reason* why)
  (rubi-note-reason why)
  'unknown)

; свежий символ base1, base2, ... которого нет в выражении
(define (rubi-fresh-sym e base)
  (let loop ((i 1))
    (let ((s (string->symbol (string-append base (to-string i)))))
      (if (contains-sym? e s) (loop (+ i 1)) s))))

; одновременная замена символов по списку (старый . новый); головы выражений не трогаются
(define (rubi-rename e alist)
  (cond ((symbol? e) (let ((p (assoc e alist))) (if p (cdr p) e)))
        ((pair? e) (cons (car e) (map (lambda (a) (rubi-rename a alist)) (cdr e))))
        (else e)))

; Головы входного языка приводятся к степеням, как в Mathematica: Sqrt[u] — это Power[u,1/2],
; Exp[u] — Power[E,u]. Без этого правила Rubi не видят радикалов вовсе: `(^ (sqrt u) -1)` не
; сопоставляется с образцом `(^ (+ a (* b x)) 1/2)` — на замере 400 тяжёлых отказов таких 144.
(define (rubi-sqrt-head? e)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) 'sqrt) #t)
        ((equal? (car e) 'exp) #t)
        (else (any? rubi-sqrt-head? (cdr e)))))

(define (rubi-normalize-heads u)
  (cond ((not (pair? u)) u)
        ((equal? (car u) 'sqrt) (list '^ (rubi-normalize-heads (cadr u)) 1/2))
        ((equal? (car u) 'exp) (list '^ 'E (rubi-normalize-heads (cadr u))))
        (else (cons (car u) (rubi-normalize-heads-list (cdr u))))))

(define (rubi-normalize-heads-list l)
  (if (null? l) '() (cons (rubi-normalize-heads (car l)) (rubi-normalize-heads-list (cdr l)))))

; (u^p)^q = u^(p*q) при целом q — верно всегда; simplify оставляет 1/sqrt(u) как (^ (^ u 1/2) -1), и образцы
; вида (^ v n) его не видят.
(define (rubi-collapse-pow e)
  (if (not (pair? e))
      e
      (let ((a (map rubi-collapse-pow (cdr e))))
        (cond
          ((and (equal? (car e) (quote ^)) (= (length a) 2) (integer? (cadr a))
                (pair? (car a)) (equal? (car (car a)) (quote ^)) (= (length (car a)) 3) (number? (caddr (car a))))
           (list (quote ^) (cadr (car a)) (* (caddr (car a)) (cadr a))))
          ; RUBI.E1: (u v)^n = u^n v^n при целом n — верно всегда. Образцы 1/(Sqrt[a+b x] Sqrt[c+d x] Sqrt[e+f x])
          ; (1.1.1.3 #43-#48 и др., EllipticF/E) после sqrt -> ^ 1/2 имели вид (^ (* u^1/2 v^1/2 w^1/2) -1)
          ; и не сопоставлялись со степенями выражения.
          ((and (equal? (car e) (quote ^)) (= (length a) 2) (integer? (cadr a))
                (pair? (car a)) (equal? (car (car a)) (quote *)))
           (cons (quote *) (map (lambda (f) (rubi-collapse-pow (list (quote ^) f (cadr a)))) (cdr (car a)))))
          (else (cons (car e) a))))))

; RUBI.J1: сомножители с одинаковым основанием склеиваются, u^a u^b = u^(a+b) (a, b - числа): Mathematica делает это
; автоматически (Times - Flat/Orderless), а ac-norm - нет: 1/((x^2+c) Sqrt[x^2+c] Sqrt[x^2+c]) оставался
; произведением (u^-1)(u^-1) вместо u^-2. Верно на любой ветви: оба множителя - exp(показатель*Log u) с одним и тем же Log u.
; Числа и числовые основания не трогаются; нечисловой показатель - сомножитель остаётся как есть.
(define *rubi-merge-bases* #t)
(define (rubi-mb-split f)
  (cond ((number? f) (cons #f f))
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3))
         (if (and (number? (caddr f)) (not (number? (cadr f)))) (cons (cadr f) (caddr f)) (cons #f f)))
        ((pair? f) (if (equal? (car f) '*) (cons #f f) (cons f 1)))
        ((symbol? f) (cons f 1))
        (else (cons #f f))))
(define (rubi-mb-add es b r)
  (cond ((null? es) (list (cons b r)))
        ((and (car (car es)) (equal? (car (car es)) b)) (cons (cons b (+ (cdr (car es)) r)) (cdr es)))
        (else (cons (car es) (rubi-mb-add (cdr es) b r)))))
(define (rubi-merge-prod fs)
  (let ((es (let loop ((l fs) (acc '()))
              (if (null? l)
                  acc
                  (let ((s (rubi-mb-split (car l))))
                    (loop (cdr l) (if (car s) (rubi-mb-add acc (car s) (cdr s)) (append acc (list s)))))))))
    (if (= (length es) (length fs))
        (cons '* fs)
        (let ((out (let loop ((l es) (acc '()))
                     (cond ((null? l) (reverse acc))
                           ((not (car (car l))) (loop (cdr l) (cons (cdr (car l)) acc)))
                           ((equal? (cdr (car l)) 0) (loop (cdr l) acc))
                           ((equal? (cdr (car l)) 1) (loop (cdr l) (cons (car (car l)) acc)))
                           (else (loop (cdr l) (cons (list '^ (car (car l)) (cdr (car l))) acc)))))))
          (cond ((null? out) 1)
                ((null? (cdr out)) (car out))
                (else (cons '* out)))))))
(define (rubi-merge-bases e)
  (if (not (pair? e))
      e
      (let ((a (map rubi-merge-bases (cdr e))))
        (if (equal? (car e) '*) (rubi-merge-prod a) (cons (car e) a)))))

; Сомножители с противоположными основаниями u и -u: основание -u записывается как (* -1 u).
; Тождество -a-b*x = (-1)(a+b*x) — просто перезапись, ветви не меняются; образцы 1.4.1 #29/#30
; (^ (* a v) m) (^ (* b v) n) требуют общего v. Правило применяется только к произведению, где пара есть.
(define (rubi-neg-sum? b1 b2 x)
  (and (pair? b1) (equal? (car b1) (quote +)) (pair? b2) (equal? (car b2) (quote +))
       (contains-sym? b1 x) (contains-sym? b2 x) (not (equal? b1 b2))
       (equal? (simplify (list (quote +) b1 b2)) 0)))

(define (rubi-factor-base f) (if (and (pair? f) (equal? (car f) (quote ^)) (= (length f) 3)) (cadr f) f))

(define (rubi-pair-neg-bases ne x)
  (if (and (pair? ne) (equal? (car ne) (quote *)))
      (let loop ((fs (cdr ne)) (done (quote ())) (changed #f))
        (if (null? fs)
            (if changed (cons (quote *) (reverse done)) ne)
            (let* ((f (car fs))
                   (b2 (rubi-factor-base f))
                   (g (and (pair? f) (equal? (car f) (quote ^))
                           (let find ((l done))
                             (cond ((null? l) #f)
                                   ((rubi-neg-sum? (rubi-factor-base (car l)) b2 x) (rubi-factor-base (car l)))
                                   (else (find (cdr l))))))))
              (if g
                  (loop (cdr fs) (cons (list (quote ^) (list (quote *) -1 g) (caddr f)) done) #t)
                  (loop (cdr fs) (cons f done) changed)))))
      ne))

; RUBI.S8: профиль в собственном времени. *rubi-p-int-acc* копит время прямых вложенных rubi-int
; внутри текущей правой части; rhs-us = время правой части за вычетом вложенных rubi-int
; (её утилиты: simplify, expand, деление многочленов). Включающее eval-us двойным счётом
; считало вложенное сопоставление в «правые части».
(define *rubi-p-int-acc* 0)
(define *rubi-p-rhs* 0)
(define *rubi-p-err* 0)   ; профиль: время от начала вычисления правой части до перехвата ошибки (включая вложенное)
(define (rubi-int ne orig x)
  (if *rubi-prof*
      (let ((saved *rubi-p-int-acc*) (t0 (clock-us)))
        (set! *rubi-p-int-acc* 0)
        (let ((r (rubi-int-body ne orig x)))
          (set! *rubi-p-int-acc* (+ saved (- (clock-us) t0)))
          r))
      (rubi-int-body ne orig x)))

; RUBI.S15: переменная образца ?b в (* ?b x) и в Mathematica (Flat) берёт ВСЕ x-свободные множители, а ac-match -
; ровно один (match.lisp: ?x - один аргумент). Поэтому в слагаемых суммы x-свободные множители группируются во
; вложенное произведение: (+ a (* -1 r x)) -> (+ a (* (* -1 r) x)); без этого a + b*x с b = -r*s, c - a*d/b + ...
; (все подзадачи после подстановок) не находили ни одного правила.
(define *rubi-group-free* #t)
(define *rubi-group-free-sum* #t)   ; RUBI.D3: то же для слагаемых суммы (флаг - для сравнения до/после)
(define (rubi-group-term t x)
  (if (and (pair? t) (equal? (car t) '*))
      (let ((free (filter (lambda (f) (not (contains-sym? f x))) (cdr t)))
            (dep (filter (lambda (f) (contains-sym? f x)) (cdr t))))
        (if (and (pair? free) (pair? (cdr free)) (pair? dep))
            (cons '* (cons (cons '* free) dep))
            t))
      t))
(define (rubi-group-free e x)
  (cond ((not (pair? e)) e)
        ((not (contains-sym? e x)) e)
        ((equal? (car e) '+)
         (let* ((ts (map (lambda (t) (rubi-group-term (rubi-group-free t x) x)) (cdr e)))
                (free (filter (lambda (t) (not (contains-sym? t x))) ts))
                (dep (filter (lambda (t) (contains-sym? t x)) ts)))
           ; RUBI.D3: Plus в Mathematica - Flat: `a_ + b_.*x_^2` берёт ВСЕ x-свободные слагаемые как a_
           ; (c - a*d/b + d*x^2/b: a = c - a*d/b); ac-match связывает ?a с одним слагаемым - группируем
           ; x-свободные слагаемые во вложенную сумму, как x-свободные множители выше
           (if (and *rubi-group-free-sum* (pair? free) (pair? (cdr free)) (pair? dep))
               (cons '+ (cons (cons '+ free) dep))
               (cons '+ ts))))
        (else (cons (car e) (map (lambda (a) (rubi-group-free a x)) (cdr e))))))
(define (rubi-int-body ne orig x)
  (if *rubi-prof* (set! *rubi-p-calls* (+ *rubi-p-calls* 1)))
  (let* ((tn (and *rubi-prof* (clock-us)))
         (ne (let ((n0 (rubi-pair-neg-bases (ac-strip-units (ac-norm (let ((cp (rubi-collapse-pow (if (rubi-sqrt-head? ne) (rubi-normalize-heads ne) ne))))
                                                                         (if *rubi-merge-bases* (rubi-merge-bases cp) cp)))) x)))
               (if *rubi-group-free* (rubi-group-free n0 x) n0)))
         (_ (if tn (set! *rubi-p-norm* (+ *rubi-p-norm* (- (clock-us) tn))))))
    (cond
      ; детерминированный бюджет: предел числа попыток сопоставления на задачу
      ((> *rubi-tries* *rubi-tries-limit*) (rubi-fail 'tries))
      ((> *rubi-depth* rubi-max-depth) (rubi-fail 'depth))
      (#t
       (let ((memo (hash-ref *rubi-memo* ne #f)))
         (if memo
             (cdr memo)
             (let ((r (let ((base (rubi-base-int ne x)))
                        (if base
                            base
                            (let ((heads (rubi-expr-heads ne '())))
                              (if *rubi-seen* (set! *rubi-seen* (cons ne *rubi-seen*)))
                              (rubi-loop (rubi-candidates ne heads) ne orig x heads))))))
               ; unknown зависит от контекста (глубина, бюджет), поэтому в кэш не пишется
               (if (not (equal? r 'unknown))
                   (hash-set! *rubi-memo* ne (cons #t r)))
               r)))))))

; Базовые определения Int из ядра Rubi (Kernel/*.mx, в .m-правилах их нет):
; константа, линейность суммы, вынесение множителя, не зависящего от x.
(define (rubi-base-int e x)
  (cond ((not (contains-sym? e x)) (list '* e x))
        ((and (pair? e) (equal? (car e) '+)) (rubi-sum-int (cdr e) x))
        ((and (pair? e) (equal? (car e) '*)) (rubi-prod-int (cdr e) x))
        ((and (pair? e) (equal? (car e) 'sin)) (rubi-base-trig e x 'cos -1))
        ((and (pair? e) (equal? (car e) 'cos)) (rubi-base-trig e x 'sin 1))
        (else #f)))

; ∫sin(u) = -cos(u)/d и ∫cos(u) = sin(u)/d при линейном u = c + d*x, c и d не зависят от x.
; В Rubi это правила инертных функций после DeactivateTrig (cos сводится к sin(u + Pi/2));
; прямого правила Int[Cos[c_. + d_.*x_]] в IntegrationRules нет.
(define (rubi-base-trig e x res sign)
  (and (= (length (cdr e)) 1)
       (let* ((u (cadr e))
              (b (ac-match '(+ ?c (* ?d x)) u :identities #t)))
         (and b
              (let ((c (cadr (assoc '?c b)))
                    (d (cadr (assoc '?d b))))
                (and (not (contains-sym? c x))
                     (not (contains-sym? d x))
                     (not (equal? d 0))
                     (list '* (list '/ sign d) (list res u))))))))

(define (rubi-sum-int terms x)
  (if (null? terms)
      0
      (let ((r (rubi-int (car terms) (car terms) x)))
        (if (equal? r 'unknown)
            'unknown
            (let ((rest (rubi-sum-int (cdr terms) x)))
              (cond ((equal? rest 'unknown) 'unknown)
                    ((equal? rest 0) r)
                    (else (list '+ r rest))))))))

; (b*x^n)^p при дробном рациональном p: (b x^n)^p = b^IntPart(p) (b x^n)^FracPart(p) / x^(n FracPart(p)) * x^(n p).
; Правило Rubi 1.1.2.1 #1 / 1.1.2.3, но для сомножителя произведения (образцы правил видят только голую степень).
; Множитель перед интегралом постоянен по x (кусочно), int-check проверяет итог дифференцированием.
(define (rubi-xpow-parts f x)
  (and (pair? f) (equal? (car f) (quote ^)) (= (length f) 3) (rubi-fractionq (caddr f))
       (pair? (cadr f)) (equal? (car (cadr f)) (quote *))
       (let* ((ts (cdr (cadr f)))
              (xs (filter (lambda (t) (contains-sym? t x)) ts))
              (bs (filter (lambda (t) (not (contains-sym? t x))) ts)))
         (and (= (length xs) 1)
              (let ((xp (car xs)))
                (cond ((equal? xp x) #f)   ; (b*x)^p уже берут правила 1.1.1.x
                      ((and (pair? xp) (equal? (car xp) (quote ^)) (equal? (cadr xp) x) (integer? (caddr xp)) (> (caddr xp) 1))
                       (list (if (null? bs) 1 (if (null? (cdr bs)) (car bs) (cons (quote *) bs))) (caddr xp)))
                      (else #f)))))))

(define (rubi-xpow-hit? rest x)
  (any? (lambda (f) (rubi-xpow-parts f x)) rest))

(define (rubi-try-xpow const rest x)
  (let ((hit (let find ((l rest)) (cond ((null? l) #f) ((rubi-xpow-parts (car l) x) (car l)) (else (find (cdr l)))))))
    (and hit
         (let* ((parts (rubi-xpow-parts hit x)) (b (car parts)) (n (cadr parts)) (p (caddr hit))
                (ip (floor p)) (fp (- p (floor p)))
                (others (filter (lambda (f) (not (equal? f hit))) rest))
                (inner (cons (quote *) (cons (list (quote ^) x (* n p)) others)))
                (inner (if (null? others) (list (quote ^) x (* n p)) inner))
                (r (rubi-int inner inner x)))
           (if (equal? r (quote unknown))
               (quote unknown)
               (cons (quote *)
                     (append const
                             (list (list (quote /) (list (quote *) (list (quote ^) b ip) (list (quote ^) (list (quote *) b (list (quote ^) x n)) fp))
                                         (list (quote ^) x (* n fp)))
                                   r))))))))

(define (rubi-prod-int factors x)
  (let loop ((fs factors) (const '()) (rest '()))
    (cond ((null? fs)
           (cond ((null? rest) #f)
                 ((and (pair? rest) (rubi-xpow-hit? rest x)) (rubi-try-xpow const rest x))
                 ; множитель, не зависящий от x, выносится при любом числе x-зависимых:
                 ; иначе ∫3x√(1+x) уходил в перебор правил по всему произведению
                 ((null? const)
                  (if (= (length rest) 1)
                      (rubi-int (car rest) (car rest) x)
                      #f))
                 (else
                  (let* ((inner (if (= (length rest) 1) (car rest) (cons '* rest)))
                         (r (rubi-int inner inner x)))
                    (if (equal? r 'unknown) 'unknown
                        (list '* (cons '* const) r))))))
          ((contains-sym? (car fs) x) (loop (cdr fs) const (cons (car fs) rest)))
          (else (loop (cdr fs) (cons (car fs) const) rest)))))

; профиль: время отсева кандидатов (головы, форма, стек, таблица неудач) без сопоставления
(define *rubi-p-scan* 0)
(define (rubi-scan-skip ts v)
  (if (and v ts) (set! *rubi-p-scan* (+ *rubi-p-scan* (- (clock-us) ts))))
  v)

; RUBI.S8: отсев по головам и форме зависит только от выражения; список прошедших кэшируется на выражение
; (одно и то же подвыражение ищется повторно, а отсев 2,7 тыс. кандидатов стоил 20-70 мс на проход)
(define (rubi-loop cands ne orig x heads)
  (let* ((xc (rubi-expr-xfactors ne x)) (exps (rubi-expr-exponents ne '()))
         (hs (rubi-head-set heads))
         (cs (or (hash-ref *rubi-cands2* ne #f)
                 (let ((v (filter (lambda (r) (and (rubi-prefilter-set? (nth r 6) hs) (rubi-shape-ok? r xc exps))) cands)))
                   (hash-set! *rubi-cands2* ne v)
                   v))))
    (if *rubi-trace*
        (begin (if (not (hash-ref *rubi-trace-nc* ne #f))
                   (begin (rubi-trace-add (list 'seen ne))
                          ; RUBI.C1: цепочка - правило и родительское выражение, породившие подзадачу
                          (rubi-trace-add (list 'chain ne (if (pair? *rubi-stack*) (car *rubi-stack*) #f)))))
               (hash-set! *rubi-trace-nc* ne (length cs))))
    ; в loop* параметр heads — таблица неудач для этого выражения (id -> #t): хешируется только строка id
    (rubi-loop* cs ne orig x
                (or (hash-ref *rubi-failed* ne #f)
                    (let ((h (make-hash))) (hash-set! *rubi-failed* ne h) h))
                xc exps)))

; Правило id уже трижды на стеке, и размеры (rubi-leaf-count) его выражений вместе с текущим строго растут, причём
; текущее больше самого раннего из трёх не меньше чем в 1,5 раза. Стек: новые в голове, элемент (id выражение).
(define *rubi-growth-fuse* #t)
(define (rubi-growth-cycle? id ne)
  (and *rubi-growth-fuse*
       (let loop ((l *rubi-stack*) (es '()))
         (cond ((null? l)
                (and (>= (length es) 3)
                     (let* ((e1 (car es)) (e2 (cadr es)) (e3 (caddr es))
                            (n (rubi-leaf-count ne)) (l1 (rubi-leaf-count e1))
                            (l2 (rubi-leaf-count e2)) (l3 (rubi-leaf-count e3)))
                       (and (> n l1) (> l1 l2) (> l2 l3) (>= (* 2 n) (* 3 l3))))))
               ((equal? (car (car l)) id) (loop (cdr l) (if (< (length es) 3) (append es (list (cadr (car l)))) es)))
               (else (loop (cdr l) es))))))

(define (rubi-loop* cands ne orig x heads xc exps)
  (if (null? cands)
      (begin
        (if *rubi-trace*
            (let ((cf (hash-ref *rubi-trace-cf* ne '())))
              (rubi-trace-add (list 'dead ne (hash-ref *rubi-trace-nc* ne 0) (length cf)))
              (for-each (lambda (c) (rubi-trace-add (list 'cond-fail (car c) (cadr c) (caddr c) ne))) cf)))
        (rubi-fail 'no-rule))
      (let* ((r (car cands))
             (id (nth r 1)) (fixed (rubi-fixed r))
             (cond (car fixed)) (rhs (cdr fixed)) (req (nth r 6))
             (key (list id ne)) (ts (and *rubi-prof* (clock-us))))
        (cond
          ; отсев по головам и форме сделан в rubi-loop (кэш на выражение): здесь только стек и таблица неудач
          
          ; пара «правило + выражение» уже на стеке — правило зацикливается
          ((rubi-scan-skip ts (member? key *rubi-stack*)) (rubi-loop* (cdr cands) ne orig x heads xc exps))
          ; предохранитель RUBI.C1 (не исправление причины): то же правило в четвёртый раз по цепочке с монотонно
          ; растущей формой (коэффициенты вида b c/(b c - a d) без сокращения: 1.1.1.3 #69/#72, 1.1.1.2 #39, ...)
          ((rubi-scan-skip ts (rubi-growth-cycle? id ne))
           (if *rubi-trace* (rubi-trace-add (list 'growth id ne)))
           (rubi-loop* (cdr cands) ne orig x heads xc exps))
          ; детерминированная неудача этого правила на этом выражении в текущем вызове
          ((rubi-scan-skip ts (hash-ref heads id #f))
           (set! *rubi-cache-hits* (+ *rubi-cache-hits* 1))
           (rubi-loop* (cdr cands) ne orig x heads xc exps))
          (#t
           (set! *rubi-tries* (+ *rubi-tries* 1))
           (if *rubi-trace* (set! *rubi-trace-ne* ne))
           (let* ((tm (and *rubi-prof* (clock-us)))
                  (binds (try (ac-match-prepared (rubi-prepared r) ne (rubi-cond-fn r))
                              (lambda (err) 'rubi-match-error))))
             (if tm
                 (begin (set! *rubi-p-match* (+ *rubi-p-match* (- (clock-us) tm)))
                        (set! *rubi-p-matches* (+ *rubi-p-matches* 1))))
             (if (and binds (not (equal? binds 'rubi-match-error)))
                 (begin (set! *rubi-last-rule* id)
                        (if *rubi-prof* (set! *rubi-matched* (cons id *rubi-matched*)))))
             (if (not (and binds (not (equal? binds 'rubi-match-error))))
                 (begin (hash-set! heads id #t)
                        (rubi-loop* (cdr cands) ne orig x heads xc exps))
                 (let* ((te (and *rubi-prof* (clock-us)))
                        (ans
                         (with-step ('rubi-step (string-append "Rubi " id) orig)
                           (try
                            (begin
                              (set! *rubi-stack* (cons key *rubi-stack*))
                              (set! *rubi-depth* (+ *rubi-depth* 1))
                              (let ((v (begin (set! *rubi-cur-id* id) (rubi-eval rhs binds))))
                                (set! *rubi-depth* (- *rubi-depth* 1))
                                (set! *rubi-stack* (cdr *rubi-stack*))
                                v))
                            (lambda (err)
                              ; причина привязывается к правилу: по одной ошибке не видно, чья она
                              (if te (set! *rubi-p-err* (+ *rubi-p-err* (- (clock-us) te))))
                              (if *rubi-trace* (set! *rubi-trace-err* (to-string err)))
                              (let ((m (string-append id " | " (to-string err))))
                                (hash-set! *rubi-errors* m (+ 1 (hash-ref *rubi-errors* m 0))))
                              (set! *rubi-depth* (if (> *rubi-depth* 0) (- *rubi-depth* 1) 0))
                              (if (pair? *rubi-stack*) (set! *rubi-stack* (cdr *rubi-stack*)))
                              'rubi-eval-error)))))
                   (if te
                       (begin (set! *rubi-p-eval* (+ *rubi-p-eval* (- (clock-us) te)))
                              (set! *rubi-p-step* (+ *rubi-p-step* (max 0 (- (- (clock-us) te) *rubi-last-dt*))))
                              (set! *rubi-p-evals* (+ *rubi-p-evals* 1))))
                   (cond ((and (pair? ans) (rubi-tainted? ans))
                          ; unknown/unintegrable внутри суммы/произведения правой части: отказ вложенного
                          ; Int, ответом это быть не может (int-check пропускал `F + unknown`, d/dx = F').
                          ; Как и провал int-check — пробуем следующий кандидат (поведение до RUBI.S1).
                          (rubi-note-reason 'nested-unknown)
                          (if *rubi-trace* (rubi-trace-add (list 'rhs-fail id 'tainted ne)))
                          (hash-set! heads id #t)
                          (rubi-loop* (cdr cands) ne orig x heads xc exps))
                         ((and (not (equal? ans 'unknown))
                               (not (equal? ans 'unintegrable))
                               (not (equal? ans 'rubi-no-rule))
                               (not (equal? ans 'rubi-eval-error)))
                          (let* ((tc (and *rubi-prof* (clock-us)))
                                 (ok (rubi-int-check (if (rubi-has-ell? ans) (rubi-ell-convert ans) ans) orig x)))
                            (if tc
                                (begin (set! *rubi-p-check* (+ *rubi-p-check* (- (clock-us) tc)))
                                       (set! *rubi-p-checks* (+ *rubi-p-checks* 1))))
                            (if ok
                                ans
                                (begin (if *rubi-trace* (rubi-trace-add (list 'rhs-fail id 'check ne)))
                                       (hash-set! heads id #t)
                                       (rubi-loop* (cdr cands) ne orig x heads xc exps)))))
                         ; «Первое правило окончательное» (флаг): unknown вложенного Int — окончательный.
                         ; По умолчанию — старое поведение: пробуем следующий кандидат.
                         ((equal? ans 'unknown)
                          (if *rubi-trace* (rubi-trace-add (list 'rhs-fail id 'unknown ne)))
                          (if *rubi-first-rule-final*
                              'unknown
                              (rubi-loop* (cdr cands) ne orig x heads xc exps)))
                         (#t (begin (if *rubi-trace*
                                        (rubi-trace-add (list 'rhs-fail id
                                                              (if (equal? ans 'rubi-eval-error)
                                                                  (list 'error (substring *rubi-trace-err* 0 (min 70 (string-length *rubi-trace-err*))))
                                                                  ans)
                                                              ne)))
                                    (hash-set! heads id #t)
                                      (rubi-loop* (cdr cands) ne orig x heads xc exps))))))))))))

; RUBI.J3: int-check проверяет в точках x = 0.3 ... 2.2 и параметрах 1.1 ... 3.1; AppellF1 вне единичного круга
; (|b x/a| > 1) eval-num не считает (оставляет форму невычисленной - 'skip), и верный ответ с AppellF1 (1.1.1.2 #39, 1.1.3.3 #61:
; x AppellF1[1,-p,-q,2,-b x/a,-d x/c]) отвергался (1.1.1.2 #39 - первое по частоте «check», 71 задача). Запасная проверка
; ТОЛЬКО для ответов с appell-f1: тот же численный критерий (невязка производной <= 1e-7 (1 + |e|), не менее двух вычислимых
; точек) в точках x = 0.05 ... 0.2, где аргументы AppellF1 внутри круга для отношений параметров до ~ 3.
(define rubi-hyp-points '(1/20 1/10 3/20 1/5 1/4))
(define (rubi-has-head? e h)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) h) #t)
        (else (any? (lambda (a) (rubi-has-head? a h)) (cdr e)))))
(define (rubi-int-check f e x)
  (or (int-check f e x)
      (and (rubi-has-head? f 'appell-f1)
           (let ((e1 (simplify e)))
             (equal? (try (integrate::int-numeric-status-at (list '- (integrate::int-diff x f) e1) e1 x 0.0000001 rubi-hyp-points)
                          (lambda (err) 'skip))
                     'ok)))))

; Ответ, в котором где-либо есть метка отказа (unknown вложенного Int, unintegrable), — не ответ.
; int-check такого не отвергал: символ-метка для int-diff — константа, и слагаемое `+ unknown` или
; множитель `0·unknown` проходили проверку.
(define (rubi-tainted? e)
  (cond ((symbol? e) (or (equal? e 'unknown) (equal? e 'unintegrable) (equal? e 'rubi-no-rule)))
        ((pair? e) (any? rubi-tainted? e))
        (else #f)))

; Вход из математического языка (integrate_rubi): отказ — невычисленная форма integrate, как у integrate,
; иначе статус ответа JSON/MCP принимал голый символ unknown за answer (pretty = "unknown").
(define (rubi-integrate-form e x)
  (let ((r (rubi-integrate e x)))
    (if (equal? r 'unknown) (list 'integrate e x) r)))

; RUBI.S16: E, появившееся при нормализации голов (exp u -> E^u, rubi-normalize-heads), возвращается к exp:
; int-check считает свободный символ E параметром (значение 1,7), и ответ ∫pi/sqrt(16 - exp(2)) = (* ... x) с E^2
; не проходил проверку против входа с (exp 2) - 2,6 с в проверке и отказ. Если E есть во входе (параметр) - не трогаем.
(define (rubi-restore-e r)
  (cond ((equal? r 'E) '(exp 1))
        ((not (pair? r)) r)
        ((and (equal? (car r) '^) (= (length r) 3) (equal? (cadr r) 'E)) (list 'exp (rubi-restore-e (caddr r))))
        (else (map rubi-restore-e r))))

; RUBI.S16: ВЕСЬ вызов (simplify входа, поиск, simplify и int-check ответа) укладывается в один бюджет;
; раньше simplify/int-check после поиска шли вне лимита (int-check ложного ответа - до секунд) и стенд убивал
; задачу на 5 с. Поиск получает бюджет минус запас на обработку ответа; не уложились - unknown.
(define rubi-post-reserve 0.4)
(define (rubi-integrate e x)
  (let ((t0 (clock-us)))
    (rubi-ensure)
    ; догрузка остальных глав - только для входа с неалгебраическими головами (по x) и в пределах бюджета:
    ; не успели - unknown сразу, следующий вызов продолжит загрузку
    (let ((loaded (or (rubi-algebraic-in? e x)
                      (rubi-ensure-full-until (+ t0 (* 1000000.0 (- rubi-time-limit 1.0)))))))
      (if (not loaded)
          (rubi-fail 'load)
          ; загрузка правил входит в бюджет вызова: стенд убивает процесс по общему времени задачи
          (let* ((budget (max 1.0 (- rubi-time-limit (/ (- (clock-us) t0) 1000000.0))))
                 (rr (call-with-time-limit
                      budget
                      (lambda () (rubi-integrate* e x (max (* 0.5 budget) (- budget rubi-post-reserve)))))))
            (set! match::ac-id-skip #f)
            (if (and (pair? rr) (equal? (car rr) 'ok))
                (cadr rr)
                (rubi-fail 'budget)))))))

; RUBI.D5: решение с журналом одной строкой для JSON-хоста (пилот с журналом в qedra-bench, вход rubi_trace).
; input - строка входного языка, var - имя переменной (строка), limit - бюджет движка, с. Возвращает строку без
; id задачи: первая строка «T<TAB>verdict<TAB>мс<TAB>попыток<TAB>причина», далее «R<TAB>запись журнала» (~s) в
; хронологическом порядке - формат tools/rubi/diagnose-run.lisp без первой колонки id. Флаги и бюджет
; восстанавливаются, журнал очищается (воркер стенда долгоживущий).
(define (rubi-trace-run input var limit)
  (let ((e (try (math-read input) (lambda (err) #f)))
        (old-limit rubi-time-limit)
        (old-trace *rubi-trace*))
    (if (not e)
        "T\tparse-error\t0\t0\t-"
        (begin
          (set! rubi-time-limit limit)
          (set! *rubi-trace* #t)
          (let* ((t0 (clock-us))
                 (r (try (rubi-integrate e (string->symbol var)) (lambda (err) 'unknown)))
                 (ms (quotient (- (clock-us) t0) 1000))
                 (head (string-append "T\t" (if (equal? r 'unknown) "unknown" "ok") "\t" (to-string ms) "\t"
                                      (to-string *rubi-tries*) "\t" (to-string *rubi-last-reason*)))
                 (recs (map (lambda (rec) (string-append "R\t" (format "~s" rec))) (reverse *rubi-trace-log*))))
            (set! rubi-time-limit old-limit)
            (set! *rubi-trace* old-trace)
            (set! *rubi-trace-log* '())
            (string-join (cons head recs) (format "~%")))))))

; RUBI.D2: нормализованный вход задачи (как его видит rubi-int) - для форм корпуса в диагностике
(define (rubi-norm-form e)
  (let ((e0 (simplify e)))
    (rubi-group-free
     (rubi-pair-neg-bases (ac-strip-units (ac-norm (rubi-collapse-pow (if (rubi-sqrt-head? e0) (rubi-normalize-heads e0) e0)))) 'x)
     'x)))

(define (rubi-integrate* e x budget)
  (let* ((xx 'x)
         (e0 (simplify e))
         ; правила Rubi записаны для переменной x; чтобы переменная интегрирования не слилась
         ; с параметром x (∫x·y dy), параметр x получает свежий символ, которого нет в выражении
         (collide (and (not (equal? x xx)) (contains-sym? e0 xx)))
         (fresh (and collide (rubi-fresh-sym e0 "x")))
         (ee (cond ((equal? x xx) e0)
                   (collide (rubi-rename e0 (list (cons xx fresh) (cons x xx))))
                   (else (rubi-rename e0 (list (cons x xx))))))
         (back (cond ((equal? x xx) '())
                     (collide (list (cons fresh xx) (cons xx x)))
                     (else (list (cons xx x)))))
         (_skip (set! match::ac-id-skip #t))
         (rr (call-with-time-limit
              budget
              (lambda ()
                (set! *rubi-depth* 0)
                (set! *rubi-stack* '())
                (set! *rubi-failed* (make-hash))
                (set! *rubi-cands* (make-hash))
                (set! *rubi-cands2* (make-hash))
                (set! rubi::*rubi-polyq-cache* (make-hash))
                (set! rubi::*rubi-expand-cache* (make-hash))
                (set! *rubi-memo* (make-hash))
                (set! *rubi-fail-reasons* '())
                (if *rubi-trace* (rubi-trace-reset))
                (set! rubi::*rubi-stub-calls* (make-hash))
                (set! *rubi-errors* (make-hash))
                ; счётчик попыток — на задачу, а не на процесс (воркер стенда долгоживущий)
                (set! *rubi-tries* 0)
                (rubi-int ee ee xx)))))
    (set! match::ac-id-skip #f)
    (if (not (and (pair? rr) (equal? (car rr) 'ok)))
        (rubi-fail 'budget)
        (let ((r (cadr rr)))
          (cond ((equal? r 'unknown) 'unknown)
                ((rubi-tainted? r) (rubi-fail 'tainted))
                (else
                 (let ((r2 (simplify (rubi-rename (let ((r1 (if (contains-sym? e0 'E) r (rubi-restore-e r))))
                                                    (if (rubi-has-ell? r1) (rubi-ell-convert r1) r1))
                                                  back))))
                   (if (rubi-int-check r2 e x)
                       r2
                       (rubi-fail 'check)))))))))
