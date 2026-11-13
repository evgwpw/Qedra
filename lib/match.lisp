; match.lisp — AC-сопоставление с образцом (шаг AC.1).
;
; Отличие от builtin match/match-bindings (PatternMatching.fs, структурное, одно решение, горячий путь упрощателя):
; здесь + и * — ассоциативно-коммутативные n-арные операции. Аргументы + и * сопоставляются как МУЛЬТИМНОЖЕСТВО,
; решений может быть несколько, порядок слагаемых/множителей и длина не важны.
;
;   ?x       обычная переменная: ровно один аргумент (под + и *) или любое подвыражение (в других местах)
;   ?r...    сегментная переменная: остаток аргументов + или * (>= 0 штук; не более одной на узел, только под + и *);
;            значение — (+ ...)/(* ...) из остатка, один аргумент — он сам, пустой остаток — 0 для + и 1 для *
;   прочее   операции кроме + и * (sin, ^, =, ...) — позиционно (голова и число аргументов совпадают), AC — внутри
;
; Образец и выражение НЕ упрощаются simplify (он свернул бы sin^2+cos^2 в 1 и собрал бы подобные члены, т. е. разрушил бы
; то, что ищут); только структурная нормализация: (- a b) и (/ a b) сводятся к +, *, ^, вложенные + и * разворачиваются.
; Выражение разумно подавать в канонической форме (результат simplify). Части образца без переменных упрощаются.
; Повторная переменная — согласованность по equal?. Лимит перебора — счётчик попыток; превышение — это не «нет
; совпадения», а «не знаю»: #f и условие (ac-match-limit лимит) в канал record-condition.
; Опции (шаг AC.2; ключевые слова :имя самовычисляются, квотированная запись ':имя тоже принимается):
;   :identities #t — обычная переменная без аргумента получает нейтральный элемент (под + это 0, под * это 1,
;                    в показателе (^ ?x ?n) против не-степени e это e^1), но только когда аргументов не осталось;
;   :where условие — условие на привязки, проверяется на каждом кандидате; принимается только #t, unknown фиксируется;
;   :limit n или просто число — лимит перебора.
; Внутренний образец: ('K выражение) константа, ('V ?x) переменная, ('N голова п...) позиционный узел,
; ('A оп фиксированные ?r...|#f) AC-узел; сопоставитель идёт в стиле продолжений: (k привязки) → #f = искать дальше.

(module match (export ac-match ac-match-all ac-subst ac-pattern-var? ac-segment-var?
                      ac-match-sub ac-replace-sub pattern-from-dag lean-heads
                      ac-build-prepared ac-match-prepared ac-norm ac-strip-units))

(define ac-default-limit 10000)

; Профиль сопоставления (RUBI.11): сколько «тиков» перебора тратит попытка и как часто упирается в лимит.
(define ac-prof #f)
(define ac-p-attempts 0)
(define ac-p-ticks 0)
(define ac-p-limit 0)
(define ac-p-max 0)

(define (ac-prof-reset)
  (set! ac-p-attempts 0)
  (set! ac-p-ticks 0)
  (set! ac-p-limit 0)
  (set! ac-p-max 0))

(define (ac-prof-data)
  (list (cons 'attempts ac-p-attempts)
        (cons 'ticks ac-p-ticks)
        (cons 'max-ticks ac-p-max)
        (cons 'limit-hits ac-p-limit)))

(define (ac-prof-note ticks limited)
  (if ac-prof
      (begin
        (set! ac-p-attempts (+ ac-p-attempts 1))
        (set! ac-p-ticks (+ ac-p-ticks ticks))
        (if limited (set! ac-p-limit (+ ac-p-limit 1)))
        (if (> ticks ac-p-max) (set! ac-p-max ticks)))))
; --- Кэш скомпилированных образцов (шаг AC-CACHE) ---
; ac-run/ac-subst/ac-sub-setup на каждый вызов делали (ac-norm pat) + (ac-compile np) + (ac-vars …);
; образцы правил и таблиц постоянны — компиляция кэшируется по самому образцу (поиск через assoc/equal?,
; встроенного eq? и хэш-таблиц по значениям в языке нет: make-table — только имена-символы).
; Лимит 256 записей; при переполнении — сброс (не LRU: просто, без утечки памяти на потоке разных образцов).
; ВАЖНО: ac-compile для подобразцов без переменных зовёт simplify, чей результат зависит от текущих правил
; упрощения (defrule/remove-rule). Поэтому при каждой вставке сверяется снимок (rule-names) — набор имён всех
; правил: изменился (добавление/удаление) — кэш сбрасывается. Переопределение правила с тем же именем снимок
; не меняет — редкий случай, принят как риск (см. журнал замеров). Значение кэша — не #f (тройка/список).
(define ac-cache-limit 256)
(define ac-cache '())          ; ((ключ . значение) ...) — ключ: образец либо (образец partial)
(define ac-cache-rules '())    ; снимок (rule-names) на момент последней вставки

(define (ac-cache-flush) (set! ac-cache '()))

(define (ac-cache-check-rules)
  (let ((ns (rule-names)))
    (if (not (equal? ns ac-cache-rules))
        (begin (set! ac-cache-rules ns) (ac-cache-flush)))))

; ключ → значение либо #f (поиск по equal? — eq? в языке нет)
(define (ac-cache-get key)
  (let ((r (assoc key ac-cache)))
    (and r (cdr r))))

(define (ac-cache-put key val)
  (ac-cache-check-rules)
  (if (>= (length ac-cache) ac-cache-limit) (set! ac-cache '()))
  (set! ac-cache (cons (cons key val) ac-cache)))

; образец → (np ip vars) с кэшированием: нормализация, компиляция и переменные.
; Снимок правил сверяется на КАЖДОМ вызове: get тоже может попасть в устаревший кэш
; (defrule после кэширования меняет упрощение константных подобразцов — K-узлы).
; Цена (rule-names) — список имён (~десятки символов), замер при разработке
(define (ac-compiled pat)
  (ac-cache-check-rules)
  (or (ac-cache-get pat)
      (let* ((np (ac-norm pat))
             (v (list np (ac-compile np) (reverse (ac-vars np '())))))
        (ac-cache-put pat v)
        v)))

; --- Переменные образца ---
; ?x — символ с первым знаком «?» (как в PatternMatching.isPatternVar; проверяем через match-bindings), ?r... — с «...»
(define (ac-pattern-var? s) (and (symbol? s) (pair? (match-bindings s 0))))
(define (ac-segment-var? s) (and (ac-pattern-var? s) (string-contains? (to-string s) "...")))

(define (ac-has-var? p)
  (cond ((symbol? p) (ac-pattern-var? p))
        ((pair? p) (any? ac-has-var? (cdr p)))
        (else #f)))

; переменные образца в порядке первого появления (в обратном порядке накопителя)
(define (ac-vars p acc)
  (cond ((symbol? p) (if (and (ac-pattern-var? p) (not (member? p acc))) (cons p acc) acc))
        ((pair? p) (foldl (lambda (a x) (ac-vars x a)) acc (cdr p)))
        (else acc)))

; --- Структурная нормализация (без simplify) ---
(define (ac-negate x) (list '* -1 x))
(define (ac-flatten op args)
  (append-map (lambda (a) (if (and (pair? a) (equal? (car a) op)) (cdr a) (list a))) args))

(define (ac-norm e)
  (if (not (pair? e))
      e
      (let ((h (car e)))
        (cond ((and (equal? h '-) (pair? (cdr e)))
               (if (null? (cddr e))
                   (ac-norm (ac-negate (cadr e)))
                   (ac-norm (cons '+ (cons (cadr e) (map ac-negate (cddr e)))))))
              ((and (equal? h '/) (pair? (cdr e)))
               (if (null? (cddr e))
                   (ac-norm (list '^ (cadr e) -1))
                   (ac-norm (cons '* (cons (cadr e) (map (lambda (x) (list '^ x -1)) (cddr e)))))))
              ((or (equal? h '+) (equal? h '*))
               (cons h (ac-flatten h (map ac-norm (cdr e)))))
              (else (cons h (map ac-norm (cdr e))))))))

; --- Компиляция образца ---
(define (ac-rank ip) (cond ((equal? (car ip) 'K) 0) ((equal? (car ip) 'V) 2) (else 1)))

(define (ac-compile p)
  (cond ((symbol? p)
         (cond ((ac-segment-var? p) (error "ac-match: сегментная переменная допустима только под + и *:" p))
               ((ac-pattern-var? p) (list 'V p))
               (else (list 'K p))))
        ((not (pair? p)) (list 'K p))
        ((not (ac-has-var? p)) (list 'K (simplify p)))
        ((or (equal? (car p) '+) (equal? (car p) '*)) (ac-compile-node p))
        ((ac-has-var? (car p)) (list 'NV (ac-compile (car p)) (map ac-compile (cdr p))))
        (else (cons 'N (cons (car p) (map ac-compile (cdr p)))))))

; жёсткие аргументы (константы, затем составные) первыми — они находят пару среди аргументов выражения быстро;
; обычные переменные после; сегментная — последней (берёт остаток)
(define (ac-compile-node p)
  (let ((segs (filter ac-segment-var? (cdr p))))
    (if (> (length segs) 1) (error "ac-match: две сегментные переменные в одном узле:" p))
    (list 'A (car p)
          (sort (map ac-compile (filter (lambda (a) (not (ac-segment-var? a))) (cdr p)))
                (lambda (a b) (< (ac-rank a) (ac-rank b))))
          (if (null? segs) #f (car segs)))))

; --- Сопоставление ---
; ctx — вектор #(счётчик лимит превышен?)
(define (ac-tick ctx)
  (vset! ctx 0 (+ (vref ctx 0) 1))
  (if (> (vref ctx 0) (vref ctx 1)) (vset! ctx 2 #t))
  (not (vref ctx 2)))

(define (ac-bind name v binds k)
  (let ((b (assoc name binds)))
    (if b
        (and (equal? (cadr b) v) (k binds))
        (k (cons (list name v) binds)))))

(define (ac-build op items)
  (cond ((null? items) (if (equal? op '+) 0 1))
        ((null? (cdr items)) (car items))
        (else (cons op items))))

; единицы (AC.2): (vref ctx 3) — флаг :identities
(define (ac-identities? ctx) (vref ctx 3))

(define (ac-mt ip e binds ctx k)
  (if (not (ac-tick ctx))
      #f
      (let ((tag (car ip)))
        (cond ((equal? tag 'K) (and (equal? (cadr ip) e) (k binds)))
              ((equal? tag 'V) (ac-bind (cadr ip) e binds k))
              ((equal? tag 'N)
               (if (and (pair? e) (equal? (car e) (cadr ip)))
                   (and (= (length (cddr ip)) (length (cdr e)))
                        (ac-mt-seq (cddr ip) (cdr e) binds ctx k))
                   ; единица степени: (^ ?x ?n) против не-степени e — это e^1
                   (and (ac-identities? ctx) (equal? (cadr ip) '^) (= (length (cddr ip)) 2)
                        (not (and (pair? e) (equal? (car e) '^)))
                        (ac-mt-seq (cddr ip) (list e 1) binds ctx k))))
              ((equal? tag 'NV)
               ; голова-переменная: F_[...] — голова выражения связывается с ?F
               (and (pair? e)
                    (ac-mt (cadr ip) (car e) binds ctx
                           (lambda (b) (and (= (length (cddr ip)) (length (cdr e)))
                                            (ac-mt-seq (cddr ip) (cdr e) b ctx k))))))
              (else (ac-mt-ac ip e binds ctx k))))))

(define (ac-mt-seq ips es binds ctx k)
  (if (null? ips)
      (k binds)
      (ac-mt (car ips) (car es) binds ctx (lambda (b) (ac-mt-seq (cdr ips) (cdr es) b ctx k)))))

; AC-узел: выражение, не являющееся узлом той же операции, — мультимножество из одного аргумента (тогда сегментная
; переменная пуста, а при ровно одном фиксированном аргументе узел вырожден)
(define (ac-mt-ac ip e binds ctx k)
  (let ((op (cadr ip)) (fixed (caddr ip)) (seg (nth ip 3)))
    (let ((items (if (and (pair? e) (equal? (car e) op)) (cdr e) (list e))))
      (if (if (ac-identities? ctx)
              ; с единицами обычные переменные могут остаться без аргумента: хватает аргументов для остальных
              (or (< (length items) (length (filter (lambda (f) (not (equal? (car f) 'V))) fixed)))
                  (and (not seg) (> (length items) (length fixed))))
              (if seg (< (length items) (length fixed)) (not (= (length items) (length fixed)))))
          #f
          (ac-fixed op fixed items seg binds ctx k)))))

; единицы: аргументов не осталось — оставшиеся обычные переменные получают нейтральный элемент (0 для +, 1 для *)
(define (ac-bind-identities op fixed binds k)
  (if (null? fixed)
      (k binds)
      (ac-bind (cadr (car fixed)) (ac-build op '()) binds
               (lambda (b) (ac-bind-identities op (cdr fixed) b k)))))

(define (ac-fixed op fixed items seg binds ctx k)
  (cond ((null? fixed)
         (cond (seg (ac-bind seg (ac-build op items) binds k))
               ((null? items) (k binds))
               (else #f)))
        ((and (null? items) (ac-identities? ctx))
         (and (every? (lambda (f) (equal? (car f) 'V)) fixed)
              (ac-bind-identities op fixed binds
                                  (lambda (b) (if seg (ac-bind seg (ac-build op '()) b k) (k b))))))
        ((and (not (ac-identities? ctx)) (< (length items) (length fixed))) #f)
        (else (ac-try op (car fixed) (cdr fixed) '() items seg binds ctx k))))

; before — уже перебранные аргументы выражения (в обратном порядке), after — ещё не перебранные;
; равный уже пробованному аргумент пропускается (нет дублей решений)
; RUBI.S7: при :identities обычная переменная может остаться без аргумента не только в хвосте: (* ?a ?v) против
; одного множителя даёт и (?a=u, ?v=1), и (?a=1, ?v=u). Второй вариант включается флагом ac-id-skip (по умолчанию #f —
; результаты ac-match для прочих пользователей не меняются) и пробуется после перебора всех аргументов.
(define ac-id-skip #f)
(define (ac-try-skip op p rest before seg binds ctx k)
  (and ac-id-skip (ac-identities? ctx) (equal? (car p) (quote V)) (not (vref ctx 2))
       (ac-bind (cadr p) (ac-build op (quote ())) binds
                (lambda (b) (ac-fixed op rest (reverse before) seg b ctx k)))))

(define (ac-try op p rest before after seg binds ctx k)
  (cond ((null? after) (ac-try-skip op p rest before seg binds ctx k))
        ((member? (car after) before) (ac-try op p rest before (cdr after) seg binds ctx k))
        (else
         (or (ac-mt p (car after) binds ctx
                    (lambda (b) (ac-fixed op rest (append (reverse before) (cdr after)) seg b ctx k)))
             (and (not (vref ctx 2))
                  (ac-try op p rest (cons (car after) before) (cdr after) seg binds ctx k))))))

(define (ac-order vars binds) (map (lambda (v) (assoc v binds)) vars))

(define (ac-dedupe l acc)
  (cond ((null? l) (reverse acc))
        ((member? (car l) acc) (ac-dedupe (cdr l) acc))
        (else (ac-dedupe (cdr l) (cons (car l) acc)))))

; --- Условия (:where) ---
; выражение: ?x заменяются на (quote значение), результат eval; (lambda (привязки) ...) или функция — вызывается от привязок
(define (ac-where-sub w binds)
  (cond ((symbol? w) (let ((b (assoc w binds))) (if b (list 'quote (cadr b)) w)))
        ((pair? w) (if (equal? (car w) 'quote) w (cons (car w) (map (lambda (x) (ac-where-sub x binds)) (cdr w)))))
        (else w)))

; → значение условия (#t, #f или unknown) и, для unknown, условие для записи
(define (ac-where-value w binds)
  (cond ((equal? w #t) #t)
        ((and (pair? w) (equal? (car w) 'lambda)) ((eval w) binds))
        ((or (pair? w) (symbol? w)) (eval (ac-where-sub w binds)))
        (else (w binds))))

(define (ac-where-ok? w binds)
  (if (not w)
      #t
      (let ((r (ac-where-value w binds)))
        (cond ((equal? r #t) #t)
              ((equal? r 'unknown)
               (record-condition (list 'ac-where-unknown (if (or (pair? w) (symbol? w)) (ac-where-sub-plain w binds) binds))
                                 "ac-match: условие :where не определено (unknown), решение отброшено")
               #f)
              (else #f)))))

; условие с подставленными значениями без quote — читаемая запись для conditions: (positive? (+ x 1))
(define (ac-where-sub-plain w binds)
  (cond ((symbol? w) (let ((b (assoc w binds))) (if b (cadr b) w)))
        ((pair? w) (cons (car w) (map (lambda (x) (ac-where-sub-plain x binds)) (cdr w))))
        (else w)))

; --- Опции: [лимит] [:limit n] [:identities флаг] [:where условие] ---
(define (ac-parse-opts opts limit ident where)
  (cond ((null? opts) (list limit ident where))
        ((number? (car opts)) (ac-parse-opts (cdr opts) (car opts) ident where))
        ((not (and (pair? (cdr opts)) (member? (car opts) '(:limit :identities :where))))
         (error "ac-match: ожидалось [лимит] [:limit n] [:identities флаг] [:where условие], получено:" (car opts)))
        ((equal? (car opts) ':limit) (ac-parse-opts (cddr opts) (cadr opts) ident where))
        ((equal? (car opts) ':identities) (ac-parse-opts (cddr opts) limit (cadr opts) where))
        (else (ac-parse-opts (cddr opts) limit ident (cadr opts)))))

; сопоставление уже подготовленного образца (ip, vars) с нормализованным выражением ne в контексте ctx
(define (ac-search ip vars where ne ctx all?)
  (let* ((found '())
         (r (ac-mt ip ne '() ctx
                   (lambda (b)
                     (let ((ob (ac-order vars b)))
                       (cond ((not (ac-where-ok? where ob)) #f)
                             (all? (set! found (cons ob found)) #f)
                             (else ob)))))))
    (if all? (ac-dedupe (reverse found) '()) r)))

(define (ac-limit-condition limit)
  (record-condition (list 'ac-match-limit limit) "ac-match: превышен предел перебора, совпадение не установлено"))

(define (ac-run pat e opts all?)
  (let* ((o (ac-parse-opts opts ac-default-limit #f #f))
         (limit (car o))
         (ident (cadr o))
         (where (caddr o))
         (cc (ac-compiled pat))                     ; AC-CACHE: np/ip/vars по кэшу
         (np (car cc))
         (ip (cadr cc))
         (vars (caddr cc))
         (ctx (vector 0 limit #f (if ident #t #f)))
         (r (ac-search ip vars where (ac-norm e) ctx all?)))
    (ac-prof-note (vref ctx 0) (vref ctx 2))
    (cond ((vref ctx 2) (ac-limit-condition limit) #f)
          (else r))))

; (ac-prepared образец) → (np ip vars) без кэша; для правил Rubi компиляция при загрузке.
; Единицы 1 в произведении и 0 в сумме убираются: ac-norm превращает (/ 1 X) в (* 1 (^ X -1)),
; а выражение после simplify такой единицы уже не содержит.
(define (ac-strip-units e)
  (if (not (pair? e))
      e
      (let ((op (car e)) (args (map ac-strip-units (cdr e))))
        (cond ((equal? op '*)
               (let ((a (filter (lambda (x) (not (equal? x 1))) args)))
                 (cond ((null? a) 1) ((null? (cdr a)) (car a)) (else (cons '* a)))))
              ((equal? op '+)
               (let ((a (filter (lambda (x) (not (equal? x 0))) args)))
                 (cond ((null? a) 0) ((null? (cdr a)) (car a)) (else (cons '+ a)))))
              (else (cons op args))))))

(define (ac-build-prepared pat)
  (let ((np (ac-strip-units (ac-norm pat))))
    (list np (ac-compile np) (reverse (ac-vars np '())))))

; (ac-match-prepared prepared выражение where) — выражение уже нормализовано (ac-norm) вызывающим.
(define (ac-match-prepared prepared ne where)
  (let* ((ctx (vector 0 ac-default-limit #f #t))
         (r (ac-search (cadr prepared) (caddr prepared) where ne ctx #f)))
    (ac-prof-note (vref ctx 0) (vref ctx 2))
    (cond ((vref ctx 2) (ac-limit-condition ac-default-limit) #f)
          (else r))))

; (ac-match образец выражение [лимит]) → привязки ((?x значение) ...) в порядке появления переменных в образце,
; () — совпало без переменных, #f — не совпало (или превышен лимит: тогда ещё и условие ac-match-limit)
(define (ac-match pat e &rest opts)
  (ac-run pat e opts #f))

; (ac-match-all образец выражение [лимит]) → список всех решений без дублей (порядок фиксирован), () — решений нет,
; #f — превышен лимит (список не отдаётся: он был бы неполным)
(define (ac-match-all pat e &rest opts)
  (ac-run pat e opts #t))

; --- Подстановка ---
(define (ac-splice op v)
  (cond ((and (pair? v) (equal? (car v) op)) (cdr v))
        ((equal? v (if (equal? op '+) 0 1)) '())
        (else (list v))))

(define (ac-sub p binds)
  (cond ((symbol? p) (let ((b (assoc p binds))) (if b (cadr b) p)))
        ((pair? p) (cons (car p) (ac-sub-args (car p) (cdr p) binds)))
        (else p)))

; сегментная переменная под + и * разворачивается в аргументы узла
(define (ac-sub-args op args binds)
  (append-map (lambda (a)
                (if (and (ac-segment-var? a) (assoc a binds) (or (equal? op '+) (equal? op '*)))
                    (ac-splice op (cadr (assoc a binds)))
                    (list (ac-sub a binds))))
              args))

; (ac-subst образец привязки) → образец с подставленными значениями, упрощённый simplify;
; непривязанные переменные остаются как есть. AC-CACHE: нормализация образца — по кэшу (ac-compiled)
(define (ac-subst pat binds)
  (simplify (ac-sub (car (ac-compiled pat)) binds)))

; --- Поиск образца в подвыражениях (шаг AC.5) ---
; (ac-match-sub образец выражение [опции]) → ((путь привязки) ...) — по одному (первому) решению на каждый узел, где образец
; подошёл; обход в глубину сверху вниз, слева направо (узел раньше своих аргументов), вложенные вхождения тоже входят.
; Путь — список индексов аргументов от корня, с нуля: () — само выражение, (1 0) — первый аргумент второго аргумента.
; Голова узла в путь не входит (аргумент i — (nth узел (+ i 1))). Пути относятся к выражению «как есть» (до ac-norm).
; Опции — как у ac-match плюс :partial (по умолчанию #t) и, для ac-replace-sub, :all.
;
; Под-сумма и под-произведение. Если образец — + или * (после нормализации), он может занимать лишь часть узла той же
; операции: к образцу автоматически добавляется сегментная ?ac-rest... (остаток), так что (+ ?a ?b) находится в (+ x y z)
; с остатком z. Узел другой головы (в том числе одиночный аргумент) такой образец не принимает — иначе ac-match
; «видел» бы в любом выражении сумму из одного слагаемого и (+ ?a ?r...) совпадал бы с каждой вершиной. По умолчанию это
; включено (поиск в подвыражениях ради этого и нужен), :partial #f — образец точно по ac-match: целиком узел, на каждом
; узле, включая одиночные. Своя сегментная переменная на верхнем узле образца отключает автоматическую (остаток —
; она), но ограничение «узел той же операции» остаётся. Остаток из привязок результата убран, замена его хранит.
(define ac-rest-var '?ac-rest...)
(define ac-opt-keys '(:limit :identities :where :partial :all))

(define (ac-opt-get opts key default)
  (cond ((null? opts) default)
        ((and (equal? (car opts) key) (pair? (cdr opts))) (cadr opts))
        ((and (pair? (cdr opts)) (member? (car opts) ac-opt-keys)) (ac-opt-get (cddr opts) key default))
        (else (ac-opt-get (cdr opts) key default))))

(define (ac-opt-drop opts keys)
  (cond ((null? opts) '())
        ((and (pair? (cdr opts)) (member? (car opts) keys)) (ac-opt-drop (cddr opts) keys))
        ((and (pair? (cdr opts)) (member? (car opts) ac-opt-keys))
         (cons (car opts) (cons (cadr opts) (ac-opt-drop (cddr opts) keys))))
        (else (cons (car opts) (ac-opt-drop (cdr opts) keys)))))

; подготовка поиска: вектор #(образец vars where ctx операция-узла авто-остаток?)
; AC-CACHE: компиляция образца (с учётом auto-остатка) кэшируется по ключу (образец partial)
(define (ac-sub-setup pat opts)
  (let* ((partial (ac-opt-get opts :partial #t))
         (o (ac-parse-opts (ac-opt-drop opts '(:partial :all)) ac-default-limit #f #f))
         (cc (begin (ac-cache-check-rules) (ac-cache-get (list 'ac-sub pat partial))))
         (cc (or cc
                 (let* ((np0 (ac-norm pat))
                        (need (and partial (pair? np0) (or (equal? (car np0) '+) (equal? (car np0) '*)) (car np0)))
                        (auto (and need (not (any? ac-segment-var? (cdr np0)))))
                        (np (if auto (append np0 (list ac-rest-var)) np0))
                        (v (list need auto (ac-compile np) (reverse (ac-vars np '())))))
                   (ac-cache-put (list 'ac-sub pat partial) v)
                   v)))
         (need (car cc))
         (auto (cadr cc)))
    (vector (caddr cc) (nth cc 3) (caddr o)
            (vector 0 (car o) #f (if (cadr o) #t #f)) need auto)))

; узел → #f или (привязки остаток), остаток — значение ?ac-rest... или #f
(define (ac-sub-try s n)
  (let ((ctx (vref s 3)))
    (if (vref ctx 2)
        #f
        (let ((nn (ac-norm n)) (need (vref s 4)))
          (if (and need (not (and (pair? nn) (equal? (car nn) need))))
              #f
              (let ((ob (ac-search (vref s 0) (vref s 1) (vref s 2) nn ctx #f)))
                (and ob
                     (let ((r (assoc ac-rest-var ob)))
                       (list (filter (lambda (b) (not (equal? (car b) ac-rest-var))) ob)
                             (if r (cadr r) #f))))))))))

(define (ac-collect s e rpath acc)
  (let* ((m (ac-sub-try s e))
         (acc2 (if m (cons (list (reverse rpath) (car m)) acc) acc)))
    (if (pair? e) (ac-collect-args s (cdr e) 0 rpath acc2) acc2)))

(define (ac-collect-args s args i rpath acc)
  (if (null? args)
      acc
      (ac-collect-args s (cdr args) (+ i 1) rpath (ac-collect s (car args) (cons i rpath) acc))))

; общий лимит перебора на весь обход: превышен — #f и условие (ac-match-limit n), неполный список не отдаётся
(define (ac-match-sub pat e &rest opts)
  (let* ((s (ac-sub-setup pat opts))
         (r (reverse (ac-collect s e '() '()))))
    (if (vref (vref s 3) 2)
        (begin (ac-limit-condition (vref (vref s 3) 1)) #f)
        r)))

; замена вхождения: подстановка в замену и, для авто-остатка, пришивание остатка к замене в узле той же операции
(define (ac-apply-repl s repl m)
  (let ((r (ac-subst repl (car m))) (rest (cadr m)) (op (vref s 4)))
    (if rest
        (simplify (ac-build op (append (ac-splice op r) (ac-splice op rest))))
        r)))

; предки заменённого узла не пересчитываются simplify, только разворачиваются вложенные + и *
(define (ac-rebuild e new-args)
  (if (equal? new-args (cdr e))
      e
      (cons (car e) (if (or (equal? (car e) '+) (equal? (car e) '*)) (ac-flatten (car e) new-args) new-args))))

(define (ac-replace-walk s repl e all? st)
  (if (and (not all?) (> (vref st 0) 0))
      e
      (let ((m (ac-sub-try s e)))
        (cond (m (vset! st 0 (+ (vref st 0) 1)) (ac-apply-repl s repl m))
              ((pair? e) (ac-rebuild e (ac-replace-args s repl (cdr e) all? st '())))
              (else e)))))

(define (ac-replace-args s repl args all? st acc)
  (if (null? args)
      (reverse acc)
      (ac-replace-args s repl (cdr args) all? st (cons (ac-replace-walk s repl (car args) all? st) acc))))

; (ac-replace-sub образец замена выражение [опции]) → выражение с заменённым первым (или, с :all #t, каждым из
; непересекающихся, сверху вниз) вхождением. Замена — ac-subst (simplify только заменённого узла); остаток под-суммы
; сохраняется: (+ новое остаток). Нет вхождений — выражение без изменений. Лимит — общий; превышен — #f и условие.
(define (ac-replace-sub pat repl e &rest opts)
  (let* ((s (ac-sub-setup pat opts))
         (st (vector 0))
         (r (ac-replace-walk s repl e (ac-opt-get opts :all #f) st)))
    (if (vref (vref s 3) 2)
        (begin (ac-limit-condition (vref (vref s 3) 1)) #f)
        r)))

; --- Образец теоремы из DAG фактов mathlib (задел для шага M) ---
; Таблица голов Lean → наши операции (ассоциативный список «голова строкой» → символ). Неизвестная голова остаётся символом
; с тем же именем. Числовые литералы — головы-числа (Datalog-движок типизирует ячейку 2 как число); OfNat не разворачивается.
(define lean-heads
  '(("Eq" =) ("Ne" !=) ("LT.lt" <) ("LE.le" <=) ("GT.gt" >) ("GE.ge" >=)
    ("HAdd.hAdd" +) ("HSub.hSub" -) ("HMul.hMul" *) ("HDiv.hDiv" /) ("HPow.hPow" ^) ("Neg.neg" -)
    ("Real.sqrt" sqrt) ("Real.exp" exp) ("Real.log" log) ("Real.sin" sin) ("Real.cos" cos) ("Real.tan" tan)
    ("Real.arctan" atan) ("Real.pi" pi) ("abs" abs) ("Inv.inv" inv)))

(define (ac-head-name h) (if (symbol? h) (to-string h) h))

(define (ac-translate-head h heads)
  (if (number? h)
      h
      (let ((r (assoc (ac-head-name h) heads)))
        (cond (r (cadr r))
              ((symbol? h) h)
              (else (string->symbol h))))))

; (pattern-from-dag корень node-fn arg-fn heads [var-fn]) → S-выражение образца для ac-match/ac-match-sub.
;   (node-fn id) → (голова арность), как строка node(Id, Head, Arity); (arg-fn id поз) → id дочернего, как arg(Id, Pos, Child),
;   позиции с 0; heads — таблица (lean-heads или своя); (var-fn id) → K, номер переменной телескопа (по умолчанию сам id).
; Голова #var → ?v<K>; одна переменная телескопа — одно имя (повторная переменная образца). Бинарные + и * сливаются в n-арные.
; Равные поддеревья DAG разворачиваются в равные подобразцы. Голова #bvar (связанные переменные) не поддерживается:
; остаётся символом (образцы с binder'ами — вне AC.5).
(define (pattern-from-dag root node-fn arg-fn heads &rest more)
  (ac-dag-build root node-fn arg-fn heads (if (null? more) (lambda (id) id) (car more))))

(define (ac-dag-build id node-fn arg-fn heads var-fn)
  (let* ((nd (node-fn id)) (h (car nd)) (n (cadr nd)))
    (if (equal? (ac-head-name h) "#var")
        (string->symbol (string-append "?v" (to-string (var-fn id))))
        (if (= n 0)
            (ac-translate-head h heads)
            (let* ((op (ac-translate-head h heads))
                   (kids (map (lambda (i) (ac-dag-build (arg-fn id i) node-fn arg-fn heads var-fn)) (range n))))
              (cons op (if (or (equal? op '+) (equal? op '*)) (ac-flatten op kids) kids)))))))
