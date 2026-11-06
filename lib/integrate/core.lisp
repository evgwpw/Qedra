; integrate/core.lisp — Шаг 19: символьное интегрирование. Каскад эвристик в духе Derive
; поверх F#-примитивов (simplify, diff, together, apart, factor, coeff/degree, solve, subst).
; Алгоритм Риша и интегралы специальных функций — вне рамок: «не умею» даёт НЕВЫЧИСЛЕННУЮ форму.
;
; Шаг 21h': бывший lib\integrate.lisp разрезан на каталог lib\integrate\ (порядок загрузки — в prelude.lisp):
;   core.lisp     — вспомогательное, приведение входа, таблица интегралов, стратегии (линейность, подстановка), каскад
;   rational.lisp — рациональные функции: простейшие дроби и Эрмит + ЛРТ
;   trig.lisp     — степени sin/cos, корни квадратного трёхчлена, произведения sin/cos
;   parts.lisp    — по частям (LIATE), раскрытие скобок
;   check.lisp    — проверка дифференцированием, численные вспомогательные
;   api.lisp      — публичный интерфейс integrate, определённые и несобственные интегралы
;
; API:
;   (integrate e x)       — неопределённый интеграл по x (без константы интегрирования)
;   (integrate e x a b)   — определённый: F(b) − F(a); если подынтегральная функция имеет особенность
;                           в [a, b] (вещественный корень знаменателя) — невычисленная форма (несобственные вне рамок)
;   Устаревший порядок (integrate 'x выражение) (шаги 7–18) принимается: если первый аргумент — символ,
;   а второй — не символ, аргументы меняются местами.
;   Объекты (тензоры): диспетчеризация по методу integrate (defmethod integrate (тип) (obj x) ...).
;   (int-check F e x)     — F' − e равно нулю (точно через simplify/together, иначе численно в нескольких точках).
;
; Соглашения: ∫ 1/x = (log x) без модуля (как в Mathematica); константы интегрирования нет;
;   параметры (символы без x) считаются положительными там, где это нужно (a в 1/(x²+a²), sqrt(a²−x²));
;   ∫ 1/sqrt(x²+c) = log(x + sqrt(x²+c)) (для любого c; asinh не используется).
;
; Каскад int-go: константа → x → таблица → стратегии (список int-strategies, расширяемый через int-add-strategy).
; Все внутренние имена имеют префикс int- (все определения lib\*.lisp глобальные).
; Зависимости: x-free?, op-expr?, replace-expr, real-numeric?, rational-number?, numeric-poly? — из domain/solve.lisp.

; Шаг 21h': модуль integrate из шести файлов (в каждом — (module integrate ...); экспорт накапливается).
; Экспорт: integrate, int-check, int-rule, int-add-strategy (документированный API) и int-num, int-guard (их использует
; limit). Остальные int-... приватны; тесты обращаются к ним как integrate::int-...
(module integrate
  (export int-rule int-add-strategy int-guard))

; ---------- вспомогательное ----------

(define int-catch? #t)            ; #f — ошибки внутри интегратора не скрываются (отладка)
(define int-max-depth 8)        ; общий предел глубины каскада (подстановки, по частям, повторные редукции)

; размер выражения (число узлов) — для упорядочивания кандидатов
(define (int-size e)
  (if (op-expr? e) (+ 1 (foldl (lambda (acc t) (+ acc (int-size t))) 0 (cdr e))) 1))

(define (int-first f l)
  (cond ((null? l) #f)
        (else (or (f (car l)) (int-first f (cdr l))))))

(define (int-dedupe l)
  (foldl (lambda (acc a) (if (member? a acc) acc (append acc (list a)))) '() l))

; сортировка по убыванию размера (вставками)
(define (int-insert a l)
  (cond ((null? l) (list a))
        ((>= (int-size a) (int-size (car l))) (cons a l))
        (else (cons (car l) (int-insert a (cdr l))))))
(define (int-sort-by-size l) (foldl (lambda (acc a) (int-insert a acc)) '() l))

; подстановочная переменная для глубины d: %u0, %u1, ...
(define (int-uvar d) (string->symbol (string-append "%u" (to-string d))))

; наклон a линейного по x выражения u = a·x + b (a без x, не 0); иначе #f
(define (int-slope u x)
  (if (and (not (x-free? u x)) (polynomial? u x) (equal? (degree u x) 1))
      (coeff u x 1)
      #f))

; ---------- шаги (Шаг S.3) ----------
; Каждая стратегия каскада — рамка with-step (rule int-...): неудача (#f) отбрасывает рамку вместе с вложенными шагами.
; «До» — невычисленный интеграл (int/dx f) (печатается «∫ f dx», определённый — (int/dx f a b), «∫_a^b f dx»; голова
; кодирует переменную). Вспомогательные переменные подстановок %u0, %u1, ... в шагах переименовываются в u, v, w, ... (int-p);
; все аргументы with-step вычисляются лишь при включённом журнале (нулевая стоимость при выключенном).

(define int-avoid '())                          ; символы входа (переменная и параметры): новые имена u, v, ... не должны совпасть
(define int-pnames '(u v w t s p q r))

(define (int-pname k)
  (let ((cs (filter (lambda (s) (not (member? s int-avoid))) int-pnames)))
    (if (< k (length cs)) (nth cs k) (int-uvar k))))

(define (int-p-from k e)
  (if (>= k 8)
      e
      (let ((s (int-uvar k)))
        (int-p-from (+ k 1) (if (contains-sym? e s) (replace-expr e s (int-pname k)) e)))))

; выражение с красивыми именами подстановочных переменных (только для шагов)
(define (int-p e) (int-p-from 0 e))

(define (int-head x) (string->symbol (string-append "int/d" (to-string (int-p x)))))
(define (int-form e x) (list (int-head x) (int-p e)))
(define (int-form-def e x a b) (list (int-head x) (int-p e) a b))
(define (int-mp e) (math-print (int-p e)))      ; строка для пояснений

; производная для внутренних нужд интегратора: шаги дифференцирования в журнал не пишутся
(define (int-diff x e)
  (if (step-log-enabled?) (call-quietly (lambda () (diff x e))) (diff x e)))

; Ключевые шаги алгебраического, смешанного, параметрического путей и рода 0 (шаг «Шаги алгебраического Риша»).
; Расчёт идёт под call-quietly (alg-run): внутренности — diff, simplify, int-check, разложения, поиск функций, внутренние
; integrate — журнал не пишут (как в risch/driver.lisp). Ключевые шаги алгоритм сообщает макросом
; (alg-step 'имя-приёма "Заголовок" "пояснение" до после) — они копятся в alg-notes (только если журнал был включён при входе,
; alg-log?) и переносятся в журнал после расчёта (alg-flush-notes!) внутрь рамки пути. rule ключевых шагов начинаются
; с alg-/mx-/gn-/pc-: такие main-шаги видны и в 'brief (StepLog.isKeyRule), остальное — только в 'full.
(define alg-log? #f)
(define alg-notes '())
(define alg-refused #f)                  ; доказанный отказ пути: ответ #f, но рамка шагов остаётся (см. alg-int-strategy)
(define alg-why "")                      ; причина доказанного отказа (по-русски)
(define (alg-note rule title comment before after)
  (set! alg-notes (cons (list rule title comment before after) alg-notes)))
(defmacro (alg-step rule &rest args)
  `(if alg-log? (try (alg-note ,rule ,@args) (lambda (err) #f))))
(define (alg-flush-notes!)
  (map (lambda (n) (record-step (car n) (cadr n) (caddr n) (nth n 3) (nth n 4) 'main)) (reverse alg-notes))
  (set! alg-notes '()))
; (alg-run thunk) → значение thunk; при включённом журнале — тихо, затем заметки в журнал. Вложенный вызов (журнал уже
; выключен внешним alg-run) просто выполняет thunk: заметки идут в общую очередь
(define (alg-run thunk)
  (if (step-log-enabled?)
      (begin
        (set! alg-log? #t)
        (set! alg-notes '())
        (let ((r (unwind-protect (call-quietly thunk) (set! alg-log? #f))))
          (alg-flush-notes!)
          r))
      (thunk)))
; попытка, после неудачи ('unknown) стирающая свои заметки: (alg-attempt (lambda () … 'unknown|результат))
(define (alg-attempt thunk)
  (let* ((saved alg-notes) (why alg-why) (v (thunk)))
    (if (equal? v 'unknown) (begin (set! alg-notes saved) (set! alg-why why)))
    v))
; сокращение длинной строки для пояснений
(define (alg-cut s) (if (> (string-length s) 180) (string-append (substring s 0 180) " …") s))
(define (alg-mp e) (alg-cut (math-print e)))
(define (alg-join strs sep)
  (if (null? strs) "" (foldl (lambda (acc s) (string-append acc sep s)) (car strs) (cdr strs))))

; ---------- приведение входа ----------
; sqrt → степень 1/2; (exp u)^n → exp(n·u); произведение экспонент → одна экспонента.
; Это нужно, чтобы одно и то же выражение имело одну форму (иначе шаблоны таблицы не совпадут).

(define (int-exp? e) (and (op-expr? e) (equal? (car e) 'exp) (= (length e) 2)))

(define (int-merge-exps prod)
  (let ((es (filter int-exp? (cdr prod))) (rest (filter (lambda (f) (not (int-exp? f))) (cdr prod))))
    (if (< (length es) 2)
        prod
        (cons '* (cons (list 'exp (cons '+ (map cadr es))) rest)))))

(define (int-norm1 e)
  (if (op-expr? e)
      (let ((args (map int-norm1 (cdr e))) (h (car e)))
        (cond ((and (equal? h 'sqrt) (= (length args) 1)) (list '^ (car args) 1/2))
              ((and (equal? h '^) (= (length args) 2) (number? (cadr args)) (int-exp? (car args)))
               (list 'exp (list '* (cadr args) (cadr (car args)))))
              ((equal? h '*) (int-merge-exps (cons h args)))
              ; sech/csch/coth → через cosh/sinh (как simplify делает для sec/csc/cot): шаблоны и подстановки — в этих формах
              ((and (equal? h 'sech) (= (length args) 1)) (list '^ (list 'cosh (car args)) -1))
              ((and (equal? h 'csch) (= (length args) 1)) (list '^ (list 'sinh (car args)) -1))
              ((and (equal? h 'coth) (= (length args) 1)) (list '* (list 'cosh (car args)) (list '^ (list 'sinh (car args)) -1)))
              (else (cons h args))))
      e))

(define (int-norm e) (simplify (int-norm1 (simplify e))))

; ---------- таблица интегралов ----------
; Запись: (шаблон результат условие ...). ?u — аргумент, ЛИНЕЙНЫЙ по x (u = a·x + b); результат записан
; как первообразная по u: ∫ f(u) dx = F(u)/a. Прочие ?-переменные: ?c ?n ?a — константы (без x), условия:
;   (const ?v)      — v не содержит x
;   (pos ?v)        — v > 0 для числа; нечисловой параметр считается положительным
;   (not-num ?v k)  — v не равно числу k
; Шаблоны с бинарными + и * сопоставляются в обоих порядках слагаемых (int-variants).
; Расширение из Lisp: (int-rule 'шаблон 'результат '(условие) ...).

(define int-pvars '(?u ?c ?n ?a ?b ?c... ?k))
(define (int-pvar? p) (and (symbol? p) (member? p int-pvars)))

(define (int-cartesian ls)
  (if (null? ls)
      (list '())
      (let ((rest (int-cartesian (cdr ls))))
        (append-map (lambda (a) (map (lambda (r) (cons a r)) rest)) (car ls)))))

(define (int-variants p)
  (if (op-expr? p)
      (let* ((vs (int-cartesian (map int-variants (cdr p))))
             (base (map (lambda (args) (cons (car p) args)) vs)))
        (if (and (or (equal? (car p) '+) (equal? (car p) '*)) (= (length (cdr p)) 2))
            (append base (map (lambda (args) (list (car p) (cadr args) (car args))) vs))
            base))
      (list p)))

(define int-table '())
(define int-base-rows '())      ; строки как записаны, без перестановок (для проверки покрытия AC-сопоставлением)

(define (int-rule pattern result &rest conds)
  (set! int-base-rows (append int-base-rows (list (cons pattern (cons result conds)))))
  (set! int-table
        (append int-table
                (map (lambda (p) (cons p (cons result conds))) (int-variants pattern)))))

; привязки — список (переменная значение); (%ok #t) — признак успеха (пустой список не ложь)
(define (int-lookup p b)
  (cond ((null? b) #f)
        ((equal? (car (car b)) p) (car b))
        (else (int-lookup p (cdr b)))))
(define (int-bval b v) (cadr (int-lookup v b)))

(define (int-match p e b)
  (cond ((not b) #f)
        ((int-pvar? p)
         (let ((old (int-lookup p b)))
           (cond ((not old) (cons (list p e) b))
                 ((equal? (cadr old) e) b)
                 (else #f))))
        ((and (op-expr? p) (op-expr? e) (= (length p) (length e)) (equal? (car p) (car e)))
         (int-match-list (cdr p) (cdr e) b))
        (else (if (equal? p e) b #f))))
(define (int-match-list ps es b)
  (cond ((not b) #f)
        ((null? ps) b)
        (else (int-match-list (cdr ps) (cdr es) (int-match (car ps) (car es) b)))))

(define (int-fill t b)
  (cond ((int-pvar? t) (int-bval b t))
        ((op-expr? t) (cons (car t) (map (lambda (a) (int-fill a b)) (cdr t))))
        (else t)))

(define (int-cond-ok? c b x)
  (let ((h (car c)) (v (int-bval b (cadr c))))
    (cond ((equal? h 'const) (x-free? v x))
          ((equal? h 'pos) (or (not (number? v)) (and (real-numeric? v) (> v 0))))
          ((equal? h 'not-num) (not (equal? v (caddr c))))
          (else #f))))

; правило применено: нечисловой параметр в условии (pos ?v) считался положительным — это условие применимости ответа
(define (int-record-pos-conditions conds b)
  (map (lambda (c)
         (if (equal? (car c) 'pos)
             (let ((v (int-bval b (cadr c))))
               (if (not (or (number? v) (equal? v 'pi)))
                   (record-condition (list '> v 0) "integrate: параметр считается положительным")))))
       conds)
  #t)

(define (int-apply-rule r b x)
  (let ((a (int-slope (int-bval b '?u) x)))
    (and a
         (every? (lambda (c) (int-cond-ok? c b x)) (cdr (cdr r)))
         (begin (int-record-pos-conditions (cdr (cdr r)) b) #t)
         (simplify (list '* (list '^ a -1) (int-fill (cadr r) b))))))

; пояснение шага «Табличный интеграл»: формула строки таблицы ∫ f(u) du = F(u) (?-переменные → u, c, n, a, b), условия
; применимости и, если u = a·x + b не x, — пересчёт на dx
(define int-plain-names '((?u u) (?c c) (?n n) (?a a) (?b b) (?c... c) (?k k)))
(define (int-plain t)
  (cond ((int-pvar? t) (cadr (int-lookup t int-plain-names)))
        ((op-expr? t) (cons (car t) (map int-plain (cdr t))))
        (else t)))

(define (int-cond-text c)
  (cond ((equal? (car c) 'not-num) (string-append (to-string (int-plain (cadr c))) " ≠ " (to-string (caddr c))))
        ((equal? (car c) 'pos) (string-append (to-string (int-plain (cadr c))) " > 0"))
        (else "")))

(define (int-table-comment r b x)
  (let* ((u (int-bval b '?u)) (a (int-slope u x))
         (conds (filter (lambda (s) (not (equal? s ""))) (map int-cond-text (cdr (cdr r)))))
         (formula (string-append "∫ " (math-print (int-plain (car r))) " du = " (math-print (int-plain (cadr r)))
                                 (if (null? conds) "" (string-append " (" (join-strings conds ", ") ")")))))
    (if (equal? u x)
        formula
        (string-append formula "; здесь u = " (int-mp u) ", du = " (int-mp a) " dx"
                       (if (equal? a 1) "" (string-append ", поэтому результат делится на " (int-mp a)))))))

(define (int-table-try rules e x)
  (if (null? rules)
      #f
      (let ((b (int-match (car (car rules)) e (list (list '%ok #t)))))
        (or (and b
                 (with-step ('int-table "Табличный интеграл" (int-form e x)
                             :comment (lambda (r) (int-table-comment (car rules) b x)) :after int-p)
                   (let ((r (int-apply-rule (car rules) b x)))
                     (if r r (begin (attempt-fail "условия табличной формулы не выполнены") #f)))))
            (int-table-try (cdr rules) e x)))))

; степени, показательная и логарифм
(int-rule '(^ ?u ?n) '(* (^ (+ ?n 1) -1) (^ ?u (+ ?n 1))) '(const ?n) '(not-num ?n -1))
(int-rule '(^ ?u -1) '(log ?u))
(int-rule '(exp ?u) '(exp ?u))
(int-rule '(^ ?a ?u) '(* (^ (log ?a) -1) (^ ?a ?u)) '(const ?a))
(int-rule '(log ?u) '(+ (* ?u (log ?u)) (* -1 ?u)))
; тригонометрия (simplify сводит tan/cot/sec/csc к sin/cos — шаблоны в этих формах)
(int-rule '(sin ?u) '(* -1 (cos ?u)))
(int-rule '(cos ?u) '(sin ?u))
(int-rule '(* (^ (cos ?u) -1) (sin ?u)) '(* -1 (log (cos ?u))))                         ; tan
(int-rule '(* (cos ?u) (^ (sin ?u) -1)) '(log (sin ?u)))                                ; cot
(int-rule '(^ (cos ?u) -1) '(log (* (+ 1 (sin ?u)) (^ (cos ?u) -1))))                   ; sec
(int-rule '(^ (sin ?u) -1) '(log (* (+ 1 (* -1 (cos ?u))) (^ (sin ?u) -1))))            ; csc
(int-rule '(^ (cos ?u) -2) '(* (^ (cos ?u) -1) (sin ?u)))                               ; sec²
(int-rule '(^ (sin ?u) -2) '(* -1 (cos ?u) (^ (sin ?u) -1)))                            ; csc²
; гиперболические
(int-rule '(sinh ?u) '(cosh ?u))
(int-rule '(cosh ?u) '(sinh ?u))
(int-rule '(tanh ?u) '(log (cosh ?u)))
(int-rule '(^ (cosh ?u) -2) '(tanh ?u))
(int-rule '(^ (cosh ?u) -1) '(atan (sinh ?u)))                                          ; sech
(int-rule '(^ (sinh ?u) -1) '(log (* (+ -1 (cosh ?u)) (^ (sinh ?u) -1))))               ; csch
(int-rule '(^ (sinh ?u) -2) '(* -1 (cosh ?u) (^ (sinh ?u) -1)))                         ; csch²
; обратные тригонометрические (по частям, готовые формулы)
(int-rule '(asin ?u) '(+ (* ?u (asin ?u)) (^ (+ 1 (* -1 (^ ?u 2))) 1/2)))
(int-rule '(acos ?u) '(+ (* ?u (acos ?u)) (* -1 (^ (+ 1 (* -1 (^ ?u 2))) 1/2))))
(int-rule '(atan ?u) '(+ (* ?u (atan ?u)) (* -1/2 (log (+ 1 (^ ?u 2))))))
; 1/(c+u²) → atan; 1/sqrt(c−u²) → asin; 1/sqrt(c+u²) → log(u + sqrt(u²+c))
(int-rule '(^ (+ ?c (^ ?u 2)) -1) '(* (^ ?c -1/2) (atan (* ?u (^ ?c -1/2)))) '(const ?c) '(pos ?c))
(int-rule '(^ (+ ?c (* -1 (^ ?u 2))) -1/2) '(asin (* ?u (^ ?c -1/2))) '(const ?c) '(pos ?c))
(int-rule '(^ (+ ?c (^ ?u 2)) -1/2) '(log (+ ?u (^ (+ ?c (^ ?u 2)) 1/2))) '(const ?c))
; INT.FIX2.e: (c + (p·u)²)^(-1/2) — форма из переписывания exp(k·i·atan(p·x))
(int-rule (quote (^ (+ ?c (^ (* ?p ?u) 2)) -1/2))
          (quote (* (^ ?p -1) (log (+ (* ?p ?u) (^ (+ ?c (^ (* ?p ?u) 2)) 1/2)))))
          (quote (const ?c)) (quote (const ?p)))

; ---------- таблица на AC-сопоставлении (шаг AC.4) ----------
; Вторая попытка после int-table-try: строки int-ac-table сопоставляются через ac-match (lib\match.lisp): + и * — n-арные,
; порядок не важен, сегментная ?c... — остаток слагаемых (сумма параметров a + b + … целиком), условия — как у int-rule
; (const/pos/not-num) плюс «?u линеен по x», проверяются на каждом кандидате (?u = x, c = y² отбрасывается, если c зависит от x).
; Строка того же вида (шаблон результат условие ...); имена переменных результата те же (?c... — значение остатка).
; Попытка идёт только если прежняя таблица не нашла правило, и только по строкам с той же головой, что у подынтегрального.
(define int-ac-table '())
(define (int-ac-rule pattern result &rest conds)
  (set! int-ac-table (append int-ac-table (list (cons pattern (cons result conds))))))

(define (int-ac-where r x)
  (lambda (b)
    (if (and (int-slope (int-bval b '?u) x)
             (every? (lambda (c) (int-cond-ok? c b x)) (cdr (cdr r))))
        #t
        #f)))

; пояснение: формула строки, привязки (кроме u) и пересчёт на dx
(define (int-ac-comment r b x)
  (let ((others (filter (lambda (p) (not (equal? (car p) '?u))) b)))
    (string-append (int-table-comment r b x)
                   (if (null? others)
                       ""
                       (string-append "; "
                                      (join-strings (map (lambda (p) (string-append (to-string (int-plain (car p))) " = " (int-mp (cadr p))))
                                                         others)
                                                    ", "))))))

(define (int-table-ac-try rules e x)
  (if (null? rules)
      #f
      (let* ((r (car rules))
             (b (and (equal? (car (car r)) (car e))
                     (ac-match (car r) e :identities #t :where (int-ac-where r x)))))
        (or (and b
                 (with-step ('int-table "Табличный интеграл" (int-form e x)
                             :comment (lambda (res) (int-ac-comment r b x)) :after int-p)
                   (int-apply-rule r b x)))
            (int-table-ac-try (cdr rules) e x)))))

; 1/(c + k·u²)^(3/2) = u / (c·sqrt(c + k·u²)); c — сумма параметров (≠ 0), k — коэффициент (≠ 0, любого знака;
; единица коэффициента берётся :identities: k = 1 для (c + u²), k = −1 для (c − u²))
(int-ac-rule '(^ (+ ?c... (* ?k (^ ?u 2))) -3/2) '(* ?u (^ ?c... -1) (^ (+ ?c... (* ?k (^ ?u 2))) -1/2))
             '(const ?c...) '(not-num ?c... 0) '(const ?k) '(not-num ?k 0))
; (c + u²)^(3/2) = u(c+u²)^(3/2)/4 + 3c·u·sqrt(c+u²)/8 + 3c²/8 · log(u + sqrt(c+u²))
(int-ac-rule '(^ (+ ?c... (^ ?u 2)) 3/2)
             '(+ (* 1/4 ?u (^ (+ ?c... (^ ?u 2)) 3/2)) (* 3/8 ?c... ?u (^ (+ ?c... (^ ?u 2)) 1/2))
                 (* 3/8 (^ ?c... 2) (log (+ ?u (^ (+ ?c... (^ ?u 2)) 1/2)))))
             '(const ?c...) '(not-num ?c... 0))
; (c − u²)^(3/2) = u(c−u²)^(3/2)/4 + 3c·u·sqrt(c−u²)/8 + 3c²/8 · asin(u/sqrt(c)), c > 0
(int-ac-rule '(^ (+ ?c... (* -1 (^ ?u 2))) 3/2)
             '(+ (* 1/4 ?u (^ (+ ?c... (* -1 (^ ?u 2))) 3/2)) (* 3/8 ?c... ?u (^ (+ ?c... (* -1 (^ ?u 2))) 1/2))
                 (* 3/8 (^ ?c... 2) (asin (* ?u (^ ?c... -1/2)))))
             '(const ?c...) '(pos ?c...) '(not-num ?c... 0))

; ---------- стратегии ----------

; линейность: сумма — почленно; множители без x выносятся
(define (int-linear e x d)
  ; INT.FIX3.c: почленная сумма и вынесение множителя — короткий бюджет приёма
  (int-with-combinatorial-limit d (lambda () (int-linear-body e x d))))

(define (int-linear-body e x d)
  (cond ((and (op-expr? e) (equal? (car e) '+))
         (with-step ('int-linearity "Интеграл суммы: интегрируем почленно" (int-form e x)
                     :comment "∫ (f + g) dx = ∫ f dx + ∫ g dx" :after int-p)
           (let ((rs (map (lambda (t) (int-go t x d)) (cdr e))))
             (if (every? (lambda (r) r) rs)
                 (simplify (cons '+ rs))
                 (begin (attempt-fail "одно из слагаемых не интегрируется") #f)))))
        ((and (op-expr? e) (equal? (car e) '*))
         (let ((cs (filter (lambda (f) (x-free? f x)) (cdr e)))
               (vs (filter (lambda (f) (not (x-free? f x))) (cdr e))))
           (if (null? cs)
               #f
               (with-step ('int-linearity "Вынесение постоянного множителя" (int-form e x)
                           :comment (lambda (r) (string-append "∫ c·f dx = c·∫ f dx, где c = " (int-mp (simplify (cons '* cs)))))
                           :after int-p)
                 (let ((r (int-go (simplify (cons '* vs)) x d)))
                   (if r (simplify (list '* (cons '* cs) r))
                       (begin (attempt-fail "оставшийся множитель не интегрируется") #f)))))))
        (else #f)))

; x-зависимые составные подвыражения (кандидаты для подстановки), без самого e
(define (int-subexprs e x)
  (if (op-expr? e)
      (append-map (lambda (a)
                    (if (and (op-expr? a) (not (x-free? a x)))
                        (cons a (int-subexprs a x))
                        '()))
                  (cdr e))
      '()))

; подстановка g → u в e; дополнительно: exp(n·w) при g = exp(w) → u^n, b^m при g = b^k и целом m/k → u^(m/k)
; (так exp(x)/(1 + exp(2x)) и x³/(1 + x⁴)... приводятся к рациональным функциям от u)
(define (int-subst-ratio e g)
  (cond ((and (int-exp? g) (int-exp? e))
         (let ((r (simplify (list '* (cadr e) (list '^ (cadr g) -1)))))
           (and (number? r) (rational-number? r) r)))
        ((and (op-expr? g) (equal? (car g) '^) (number? (caddr g)) (op-expr? e) (equal? (car e) '^)
              (equal? (cadr e) (cadr g)) (number? (caddr e)))
         (let ((r (/ (caddr e) (caddr g)))) (and (integer? r) r)))
        (else #f)))

(define (int-subst e g u)
  (cond ((equal? e g) u)
        ((not (op-expr? e)) e)
        (else (let ((r (int-subst-ratio e g)))
                (if r
                    (list '^ u r)
                    (cons (car e) (map (lambda (a) (int-subst a g u)) (cdr e))))))))

; «производная делит»: g — кандидат, q = e / g'(x); если после замены g → u от x ничего не зависит —
; интегрируем по u и возвращаем g на место u
(define (int-try-usub e g x d)
  (let ((dg (int-diff x g)))
    (if (equal? dg 0)
        #f
        (let ((u (int-uvar d)))
          (int-first
           (lambda (q)
             (let ((q2 (int-subst q g u)))
               (and (x-free? q2 x)
                    (with-step ('int-substitution "Метод подстановки" (int-form e x)
                                :comment (lambda (r) (string-append "u = " (int-mp g) ", du = " (int-mp dg) " dx"))
                                :after int-p)
                      (let* ((cc (capture-conditions
                                   (lambda ()
                                     (begin
                                       (if (step-log-enabled?)
                                           (record-step 'int-substitution-change "Замена переменной"
                                                        (string-append "подынтегральное выражение через u: " (int-mp q2) " du")
                                                        (int-form e x) (int-form q2 u)))
                                       (int-go q2 u (+ d 1))))))
                             (r (car cc)))
                        ; INT.FIX2.d: условия, найденные в переменной подстановки u, возвращаем в x
                        ; (иначе в ответе остаётся (> %u0 0) и условие бесполезно)
                        (for-each (lambda (c)
                                    (record-condition
                                     (if (pair? (car c)) (replace-expr (car c) u g) g)
                                     (cadr c)))
                                  (cadr cc))
                        (if r
                            (let ((res (simplify (replace-expr r u g))))
                              (if (step-log-enabled?)
                                  (record-step 'int-back-substitution "Обратная замена"
                                               (string-append "u = " (int-mp g))
                                               (int-p r) (int-p res)))
                              res)
                            (begin (attempt-fail "не удалось проинтегрировать выражение через u") #f)))))))
           (list (simplify (list '* e (list '^ dg -1)))
                 (together (list '* e (list '^ dg -1)))))))))

; линейный g = c + d·x — только переименование переменной (подынтегральное то же, глубина больше): такие кандидаты
; отбрасываем сразу — иначе (a + b·(c+dx)^(3/2))^p уходит в рекурсию на ≈ 20–45 с (шаг INT.SQ)
(define (int-usub e x d)
  (and (< d 3)
       (int-first (lambda (g) (int-guard (lambda () (int-try-usub e g x d))))
                  (take (filter (lambda (g) (not (int-slope g x)))
                                (int-sort-by-size (int-dedupe (int-subexprs e x))))
                        10))))

; вызов thunk с перехватом ошибок (результат #f при ошибке, если int-catch?)
(define (int-guard thunk)
  (cond (int-in-budget (int-guard-raw thunk))
        ((not int-time-limit) (int-guard-raw thunk))
        (else (int-budgeted thunk))))

(define (int-guard-raw thunk)
  (if int-catch? (try (thunk) (lambda (err) #f)) (thunk)))

; Бюджет времени на верхний вызов (call-with-time-limit): исчерпан — #f и условие (timeout ...); ответ не подменяется.
; int-time-limit — секунды или #f (без ограничения); тест подменяет через set! и восстанавливает в finally.
(define int-time-limit 20)
(define int-in-budget #f)
(define int-phase #f)   ; (форма x) на время предпроверки Риша, иначе #f (журнал попыток при исчерпании бюджета)
(define (int-budgeted thunk)
  (set! int-in-budget #t)
  (let ((r (unwind-protect
             (call-with-time-limit int-time-limit (lambda () (int-guard-raw thunk)))
             (set! int-in-budget #f))))
    (if (equal? (car r) 'ok)
        (cadr r)
        (begin
          (if int-phase
              (let ((ph int-phase))
                (set! int-phase #f)
                (with-step ('risch-precheck "Предпроверка Риша: элементарна ли первообразная" (int-form (car ph) (cadr ph)))
                  (attempt-fail (string-append "не уложилась в бюджет времени " (to-string int-time-limit) " с"))
                  #f)))
          (attempt-fail (string-append "превышен бюджет времени " (to-string int-time-limit) " с"))
          (record-condition (list 'timeout 'integrate int-time-limit)
                            (string-append "integrate: исчерпан бюджет времени " (to-string int-time-limit)
                                           " с — возвращена невычисленная форма"))
          #f))))

; ---------- каскад ----------

(define int-strategies '())
(define (int-add-strategy f) (set! int-strategies (append int-strategies (list f))))

; R1.1: верхняя форма текущего integrate и признак доказанной неэлементарности
; (стратегия записала risch-nonelementary для всей формы — ответ не подменяем
; частичным, а возвращаем невычисленную форму, как для y² = P)
(define int-top-form #f)
(define int-none-proved #f)

(define (int-try-strategies fs e x d)
  (cond ((null? fs) #f)
        (else (or (int-strategy (car fs) e x d) (int-try-strategies (cdr fs) e x d)))))

; INT.FIX3.c: у стратегии каскада свой бюджет. Атрибуция 182 таймаутов выборки 300:
; Риш 38, по частям (с «выбором u и dv») 49, алгебраика 33, вынесение множителя и суммы 39 —
; одна стратегия съедала весь бюджет integrate, и каскад до остальных не доходил.
; Общий бюджет стратегии — 6 с (медленные верные ответы не теряются: регрессия 3000 OK
; без потерь), у переборных приёмов свой, короткий — см. int-combinatorial-limit.
(define int-strategy-limit 6)
(define (int-strategy f e x d)
  (if (and int-in-budget (= d 0))
      (let ((r (unwind-protect
                 (call-with-time-limit int-strategy-limit
                                       (lambda () (int-guard (lambda () (f e x d)))))
                 #f)))
        (if (and (pair? r) (equal? (car r) 'ok))
            (cadr r)
            (begin (attempt-fail (string-append "стратегия не уложилась в "
                                                (to-string int-strategy-limit) " с")) #f)))
      (int-guard (lambda () (f e x d)))))

; Бюджет переборных приёмов (по частям, раскрытие скобок, почленная сумма, подстановки):
; на раздутых выражениях они уходят в комбинаторный перебор (88 из 182 таймаутов выборки).
; Исчерпан — приём отказывается, каскад пробует следующий. Только на верхнем уровне (d = 0):
; int-linear вызывается на каждом шаге рекурсии, и таймер на каждый вызов заметно замедляет обычные задачи.
(define int-combinatorial-limit 3)
(define (int-with-combinatorial-limit d thunk)
  (if (and int-in-budget (= d 0))
      (let ((r (unwind-protect (call-with-time-limit int-combinatorial-limit thunk) #f)))
        (if (and (pair? r) (equal? (car r) 'ok))
            (cadr r)
            (begin (attempt-fail (string-append "переборный приём не уложился в "
                                                (to-string int-combinatorial-limit) " с")) #f)))
      (thunk)))

; A5.7: подынтегральное с двумя различными квадратными радикалами отдаём
; алгебраической стратегии первой — в каскаде она последняя, и перебор
; int-parts/int-expand на раздутых выражениях уходит в минуты.
(define (int-rad-bases e)
  (cond ((not (op-expr? e)) '())
        ((and (equal? (car e) '^) (= (length e) 3) (number? (caddr e))
              (equal? (denom (caddr e)) 2))
         (list (expand (cadr e))))
        ((and (equal? (car e) 'sqrt) (= (length e) 2))
         (list (expand (cadr e))))
        (else (append-map int-rad-bases (cdr e)))))

(define (int-two-rad? e)
  (>= (length (int-dedupe (int-rad-bases e))) 2))

; R1.1: сумма, целиком алгебраическая относительно одного квадратного радикала
; (√P + рациональные слагаемые). Эрмит на всей сумме видит сокращения, которые
; теряются при почленном разборе int-linear (пример: (x√(x³+1))′).
(define (int-alg-only? e)
  (cond ((not (pair? e)) #t)
        ((member? (car e) '(+ - * / ^ sqrt)) (every? int-alg-only? (cdr e)))
        (else #f)))

(define (int-alg-sum? e)
  (and (op-expr? e) (equal? (car e) '+)
       (let ((bs (int-rad-bases e)))
         (and (pair? bs)
              (every? (lambda (b) (equal? b (car bs))) bs)
              (int-alg-only? e)))))

; есть ли уже доказательство risch-nonelementary ровно для этой формы
(define (int-none-cond? e x)
  (any? (lambda (c)
          (and (pair? (car c))
               (equal? (car (car c)) 'risch-nonelementary)
               (equal? (cadr (car c)) (int-unevaluated e x '()))))
        (conditions)))

(define (int-go e x d)
  (cond ((x-free? e x)
         (with-step ('int-table "Интеграл постоянной" (int-form e x) :comment "∫ c dx = c·x" :after int-p)
           (simplify (list '* e x))))
        ((equal? e x)
         (with-step ('int-table "Табличный интеграл" (int-form e x) :comment "∫ x dx = x²/2" :after int-p)
           (list '* 1/2 (list '^ x 2))))
        (else (or (int-table-try int-table e x)
                  (and (op-expr? e) (int-guard (lambda () (int-table-ac-try int-ac-table e x))))
                  (and (= d 0) (or (int-two-rad? e) (int-alg-sum? e))
                       (let ((r (int-strategy integrate::alg-int-strategy e x d)))
                         (if r r
                             (begin
                               (if (and (equal? e int-top-form) (int-none-cond? e x))
                                   (set! int-none-proved #t))
                               #f))))
                  ; R3 (mixed.lisp): радикал над exp/log — смешанный случай до каскада; доказанный отказ
                  ; верхней формы (int-none-proved) каскад не гоняет — ответ всё равно невычисленная форма
                  (and (= d 0) (int-guard (lambda () (int-mixed e x d))))
                  (and (not (and (= d 0) int-none-proved (equal? e int-top-form)))
                       (int-try-strategies int-strategies e x d))))))
