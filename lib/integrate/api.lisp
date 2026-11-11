; integrate/api.lisp — публичный интерфейс integrate, несобственные и определённые интегралы (часть бывшего lib\integrate.lisp,
; шаг 21h'). Загружается последним из частей integrate (после integrate/check.lisp).
(module integrate
  (export integrate))

; ---------- публичный интерфейс ----------

; (a²)^(±1/2) → a^(±1) для параметра a без x (параметры считаются положительными — см. соглашения)
; чётность: cos(−2x) → cos(2x), sin(−2x) → −sin(2x)
(define (int-neg-arg? a)
  (and (op-expr? a) (equal? (car a) '*) (real-numeric? (cadr a)) (< (cadr a) 0)))
(define (int-neg-arg a) (cons '* (cons (- 0 (cadr a)) (cdr (cdr a)))))

(define (int-tidy e x)
  (if (op-expr? e)
      (let ((args (map (lambda (a) (int-tidy a x)) (cdr e))))
        (cond ; Шаг 21k.6: log(exp u) → u, exp(u)^k → exp(k·u) для числа k (u вещественно: интегратор — вещественный анализ)
              ((and (equal? (car e) 'log) (= (length args) 1) (op-expr? (car args)) (equal? (car (car args)) 'exp)
                    (= (length (car args)) 2))
               (cadr (car args)))
              ((and (equal? (car e) '^) (= (length args) 2) (real-numeric? (cadr args)) (op-expr? (car args))
                    (equal? (car (car args)) 'exp) (= (length (car args)) 2))
               (list 'exp (list '* (cadr args) (cadr (car args)))))
              ((and (equal? (car e) '^) (= (length args) 2) (member? (cadr args) '(1/2 -1/2))
                    (op-expr? (car args)) (equal? (car (car args)) '^) (equal? (caddr (car args)) 2)
                    (x-free? (cadr (car args)) x))
               (list '^ (cadr (car args)) (* 2 (cadr args))))
              ((and (member? (car e) '(cos cosh)) (= (length args) 1) (int-neg-arg? (car args)))
               (list (car e) (int-neg-arg (car args))))
              ((and (member? (car e) '(sin sinh tanh atan asin)) (= (length args) 1) (int-neg-arg? (car args)))
               (list '* -1 (list (car e) (int-neg-arg (car args)))))
              (else (cons (car e) args))))
      e))

; Шаг S.3: перестановка слагаемых/множителей или иная запись той же печати — не шаг (шум): совпадают печать или наборы
; листьев и голов
(define (int-leaves e) (if (op-expr? e) (cons (car e) (append-map int-leaves (cdr e))) (list e)))
(define (int-trivial-rewrite? a b)
  (or (equal? (int-mp a) (int-mp b))
      (let ((la (int-leaves a)) (lb (int-leaves b)))
        (and (every? (lambda (t) (member? t lb)) la) (every? (lambda (t) (member? t la)) lb)))))

; Свёртка знака логарифма: башня Риша выносит знак из аргумента (log(−P) → log(−1)+log P).
; Как значение log(−1) = iπ — константа, но внутри другого логарифма или знаменателя
; разница константой не является, и ответ верен только на одной ветви (hebisch, 44 и 794).
; Свёртка возвращает знак в аргумент: k·log(−1) + log u → log((−1)^k·u).
(define (int-neg-log-coef t)
  (cond ((and (pair? t) (equal? (car t) 'log) (equal? (cadr t) -1)) 1)
        ((and (pair? t) (equal? (car t) '*))
         (let ((k (simplify (list '/ t (list 'log -1)))))
           (and (integer? k) k)))
        (else #f)))

(define (int-log-arg? t)
  (and (pair? t) (equal? (car t) 'log) (not (equal? (cadr t) -1))))

; Знак вынесен из аргумента одного логарифма — партнёр должен быть ровно один; при нескольких
; кандидатах неизвестно, к какому из них относится знак, и свёртка отказывается (INT.FIX2.a).
; Убираются ВСЕ члены log(−1): коэффициент k — их сумма, иначе свёртка меняет значение на iπ.
(define (int-fold-log-sum e)
  (let* ((ts (cdr e))
         (ks (filter (lambda (t) (int-neg-log-coef t)) ts))
         (ls (filter int-log-arg? ts)))
    (if (or (null? ks) (not (pair? ls)) (pair? (cdr ls)))
        e
        (let* ((k (foldl + 0 (map int-neg-log-coef ks)))
               (lg (car ls))
               (u (cadr lg))
               (folded (if (even? k) (list 'log u) (list 'log (list '* -1 u))))
               (rest (filter (lambda (t) (not (int-neg-log-coef t))) ts))
               (rest2 (filter (lambda (t) (not (equal? t lg))) rest)))
          (simplify (cons '+ (cons folded rest2)))))))

(define (int-fold-log-sign e)
  (if (not (pair? e))
      e
      (let ((e2 (cons (car e) (map int-fold-log-sign (cdr e)))))
        (if (equal? (car e2) '+) (int-fold-log-sum e2) e2))))

; INT.FIX2.c: страховка — ответ не зависит от x (константа, в том числе 0), а подынтегральное
; не равно нулю тождественно. Проверка численная: точка годится, если f вычислилось и ≠ 0.
(define int-guard-pts '(1/2 3/4 -1/3 2 7/5))
(define (int-integrand-nonzero? e x)
  (any? (lambda (p)
          (let ((v (try (eval-num (subst (list (list x p)) e)) (lambda (err) #f))))
            (and (number? v) (not (= v 0)))))
        int-guard-pts))

; INT.FIX3.c: у предпроверки Риша свой бюджет времени. Без него `rs-precheck-ne` съедал весь бюджет
; integrate (20 с, в корпусе — 5 с), каскад не запускался и задача падала в TIMEOUT. Не уложилась —
; считаем «не доказано» (#f) и идём обычным каскадом: верный ответ не теряется, NE не подменяется.
(define int-precheck-limit 2.5)
(define (int-precheck n x)
  (let ((r (unwind-protect
             (call-with-time-limit int-precheck-limit
                                   (lambda () (int-guard-raw (lambda () (risch::rs-precheck-ne n x)))))
             #f)))
    (if (and (pair? r) (equal? (car r) 'ok))
        (cadr r)
        (begin (attempt-fail (string-append "предпроверка Риша не уложилась в "
                                            (to-string int-precheck-limit) " с"))
               #f))))

; INT.FIX3.b: логарифмическая ветвь. Ответ с логарифмом может быть верен только при x > 0
; (log(x²) → 2log x, log(a·b) → log a + log b, знак из аргумента). Проверяем невязку F′ − f численно:
;   отрицательные точки — есть ли ветвь; положительные — верен ли ответ хоть на одной стороне.
; Возвращает #t — ответ верен (условие не нужно), 'cond — верен только при x > 0, #f — неверен и там:
; тогда ответ не выдаётся (unknown), иначе в корпус уходит заведомо неверная ветвь.
(define int-branch-neg-pts '(-267/100 -17/10 -123/100 -41/50 -3/4 -1/3))
(define int-branch-pos-pts '(1/3 3/4 41/50 123/100 17/10 267/100))
(define (int-log-has-neg-one? e)
  (or (and (pair? e) (equal? (car e) 'log) (equal? (cadr e) -1))
      (and (pair? e) (any? int-log-has-neg-one? (cdr e)))))
(define (int-log-branch-state F e0 x)
  (if (not (contains-sym? F 'log))
      #t
      (let ((d (list '- (int-diff x F) e0))
            (pos (int-numeric-status-at (list '- (int-diff x F) e0) e0 x 1e-6 int-branch-pos-pts)))
        (cond ; log(−1) в ответе при невязке — заведомо неверная ветвь на вещественной оси: отказ
              ((and (equal? pos 'bad) (int-log-has-neg-one? F)) #f)
              ((and (equal? pos 'ok)
                    (equal? (int-numeric-status-at d e0 x 1e-6 int-branch-neg-pts) 'bad))
               (record-condition (list '> x 0)
                                 "integrate: ответ верен при x > 0 (ветвь логарифма)")
               'cond)
              (else #t)))))

; Шаг N1: финальная доводка первообразной — форма короче и привычнее, значения не меняются:
;   1) expand + simplify (сбор подобных), если результат короче (по узлам);
;   2) trigsimp, если короче;
;   3) половинные углы внутри log/atan (только если int-check нового ответа проходит — иначе прежний).
; F — первообразная (после int-tidy), e0 — подынтегральное (для проверки), x — переменная
(define (int-final F e0 x)
  ; частичный ответ Риша (с невычисленным интегралом) — как прежде: expand ломает его структуру
  (if (int-has-integrate? F)
      (simplify F)
      (let* ((base (int-fold-log-sign (simplify F)))
             (ex (int-fold-log-sign (simplify (expand base))))
             (c1 (if (< (trigsimp-size ex) (trigsimp-size base)) ex base))
             (c2 (trigsimp c1))
             (best (if (< (trigsimp-size c2) (trigsimp-size c1)) c2 c1))
             (ha (trigsimp-half-angle best))
             (res (cond ((and (x-free? best x) (int-integrand-nonzero? e0 x))
                         ; константа при ненулевом подынтегральном — ошибка интегратора: ответ не выдаётся,
                         ; причина остаётся в журнале попыток
                         (attempt-fail "ответ — константа при ненулевом подынтегральном (ошибка интегратора)")
                         #f)
                        ((equal? ha best) best)
                        ((int-check ha e0 x) ha)
                        (else best))))
        (cond ((not res) #f)
              ((not (int-log-branch-state res e0 x))
               (attempt-fail "ответ не проходит численную проверку (ветвь логарифма) — отказ")
               #f)
              (else res)))))

; Доказанный отказ верхней формы стратегией, не входившей в int-go напрямую (кружной путь каскада: Чебышёв, алгебраика
; из int-try-strategies): условие risch-nonelementary для ровно этой формы уже записано. Только при включённом журнале:
; int-refusal-kept — рамка integration (с ключевыми шагами причины отказа) остаётся в журнале; результат рамки —
; 'int%refused, снаружи int-antiderivative возвращает #f (ответ integrate тот же, что и без журнала)
(define int-refusal-kept #f)
(define (int-note-refusal n x)
  (set! int-refusal-kept (and (step-log-enabled?) (not integrate::int-none-proved) (int-none-cond? n x) #t)))

; Шаг S.3: верхняя рамка integration («Интегрирование по x»: ∫ f dx ⇒ F); внутри — приведение входа (simplify-integrand),
; применённая стратегия каскада и упрощение результата (simplify-result); нет первообразной — рамка отбрасывается
(define (int-antiderivative e x)
  (if (step-log-enabled?) (set! int-avoid (cons x (int-symbols e x))))
  (let ((f (lambda ()
             (let* ((n (int-norm e))
                    (r (begin
                         (if (and (step-log-enabled?) (not (equal? n e)) (not (int-trivial-rewrite? e n)))
                             (record-step 'simplify-integrand "Упрощение подынтегральной функции" ""
                                          (int-form e x) (int-form n x) 'detail))
                         (set! integrate::int-top-form n)
                         (set! integrate::int-none-proved #f)
                         (set! integrate::int-refusal-kept #f)
                         ; INT.UX: пока идёт предпроверка, int-phase помнит форму — при исчерпании бюджета int-budgeted
                         ; запишет в журнал попыток рамку «Предпроверка Риша» с причиной (шаги самой предпроверки
                         ; остаются на своём месте в дереве)
                         (let ((pc (begin (set! integrate::int-phase (list n x))
                                          ; шаг PL: формы с Li_s/W — до предпроверки (Риш доказывает неэлементарность
                                          ; log(1+x)/x, а ответ через Li₂ проверяется дифференцированием)
                                          (let ((v (or (int-polylog-first n x) (int-precheck n x))))
                                            (set! integrate::int-phase #f)
                                            v))))   ; 21k.7b: #t | частичный ответ | #f
                           (cond ((equal? pc #t) (begin (attempt-fail "интеграл неэлементарен: доказано алгоритмом Риша") #f)) (pc pc) (else (let ((r (int-go n x 0))) (if r r (begin (int-note-refusal n x) (attempt-fail "нет подходящего приёма интегрирования") #f)))))))))
              ; R1.1: алгебраическая стратегия доказала неэлементарность всей формы —
              ; частичный ответ (elliptic-f и т. п.) не подменяет вердикт
              (and (or r integrate::int-none-proved integrate::int-refusal-kept)
                   (cond ((and (not r) integrate::int-refusal-kept) 'int%refused)
                         (integrate::int-none-proved
                          (int-unevaluated-final n x))
                         (else
                          (or (let ((res (int-final (int-tidy (simplify r) x) e x)))
                                (if (and (step-log-enabled?) res (not (equal? res r)) (not (int-trivial-rewrite? r res)))
                                    (record-step 'simplify-result "Упрощение результата" "" r res 'detail))
                                res)
                              ; INT.FIX2.c: страховка int-final сработала — константа при ненулевом f
                              (int-unevaluated-final n x)))))))))
    (let ((r (with-step ('integration (string-append "Интегрирование по " (to-string x)) (int-form e x)
                         :after (lambda (v) (if (equal? v 'int%refused) (int-unevaluated e x '()) (int-p v))))
               (int-guard f))))
      (if (equal? r 'int%refused) #f r))))

(define (int-unevaluated e x lims)
  (append (list 'integrate (simplify e) x) lims))

; Шаг 21k.4: невычисленная форма неопределённого интеграла; если алгоритм Риша доказал неэлементарность подынтегральной
; (таблица risch::rs-ne-known?), пишется условие (risch-nonelementary форма) — по нему статус JSON/MCP «nonelementary»
(define (int-unevaluated-final f x)
  (let ((u (int-unevaluated f x '())))
    (if (int-guard (lambda () (risch::rs-ne-known? (int-norm f) x)))
        (record-condition (list 'risch-nonelementary u)
                          (string-append "интеграл неэлементарен: алгоритм Риша (теорема Лиувилля) доказал, что первообразной в элементарных функциях нет"
                                         (or (int-guard (lambda () (risch::rs-special-hint (int-norm f) x))) ""))))
    u))

; Q.1: доказанный отказ Риша виден при вызове через integrate — верхняя рамка risch
; (рамка интегрирования и дерево попыток не трогаются, ответ не меняется)
; в определённых интегралах шаг не пишется: там свои рамки int-definite/int-limits (П2 карточки)
(define int-no-refusal-steps #f)
(define (int-note-refusal-steps f x)
  (if (and (step-log-enabled?) (not int-no-refusal-steps)
           (int-guard (lambda () (risch::rs-ne-known? (int-norm f) x))))
      (with-step ('risch "Алгоритм Риша" (int-form f x)
                         :comment "проверка на элементарную первообразную (теорема Лиувилля)"
                         :after int-p)
        (record-step 'risch-nonelementary "Алгоритм Риша: интеграл неэлементарен"
                     (string-append "интеграл неэлементарен: теорема Лиувилля — элементарной первообразной нет"
                                    (or (int-guard (lambda () (risch::rs-special-hint (int-norm f) x))) ""))
                     (int-form f x) 'неэлементарно 'main)
        'неэлементарно)
      #f))

; частичный ответ Риша F + (integrate r x): определённый интеграл подстановкой пределов не берётся
(define (int-has-integrate? e)
  (and (op-expr? e) (or (equal? (car e) 'integrate) (any? int-has-integrate? (cdr e)))))

; ---------- несобственные интегралы (Шаг 20): пределы первообразной ----------

; числовое значение границы (±inf — очень большие числа) или #f (символ)
(define (int-bound-num v)
  (cond ((equal? v 'inf) 1000000000000) ((equal? v '-inf) -1000000000000) (else (int-num v))))

(define (int-inf? v) (or (equal? v 'inf) (equal? v '-inf)))

; вещественный корень знаменателя СТРОГО внутри (a, b) (для символьных границ — любой корень)
(define (int-singular-inside? e x a b)
  (let ((den (try (denom e) (lambda (err) 1))) (na (int-bound-num a)) (nb (int-bound-num b)))
    (and (not (x-free? den x))
         (numeric-poly? den x)
         (any? (lambda (r) (or (not (and na nb))
                               (and (< (int-lo na nb) r) (< r (int-hi na nb)))))
               (real-roots den x)))))
(define (int-lo a b) (if (< a b) a b))
(define (int-hi a b) (if (> a b) a b))

; шаги S.4: внутренние пределы интеграла (int-improper) в журнал не пишутся
(define (int-lim-end F x p side)
  (let ((r (int-guard (lambda () (if (step-log-enabled?) (call-quietly (lambda () (limit F x p side))) (limit F x p side))))))
    ; шаг PL: предел F с полилогарифмом на конце — подстановка (limit не знает polylog), см. ipl-endpoint
    (if (and (not (int-lim-ok? r)) (contains-sym? F 'polylog))
        (or (int-guard (lambda () (ipl-endpoint F x p side))) r)
        r)))
(define (int-lim-ok? r) (and r (not (equal? r 'undefined)) (not (and (op-expr? r) (equal? (car r) 'limit)))))
(define (int-neg-lim v) (if (int-inf? v) (if (equal? v 'inf) '-inf 'inf) (simplify (list '* -1 v))))

; F(hi) − F(lo) через пределы (hi — слева, lo — справа); нижняя граница больше верхней — меняем местами
; Расходящийся интеграл по конечному отрезку (особенность в конце) — невычисленная форма (#f)
(define (int-by-limits F x a b)
  (let* ((na (int-bound-num a)) (nb (int-bound-num b))
         (swap (and na nb (> na nb)))
         (lo (if swap b a)) (hi (if swap a b))
         (Fh (int-lim-end F x hi 'minus)) (Fl (int-lim-end F x lo 'plus)))
    (if (and (int-lim-ok? Fh) (int-lim-ok? Fl))
        (let ((d (lim-add Fh (int-neg-lim Fl))))
          (cond ((not d) #f)
                ((int-bad-log? d) #f)
                ((and (int-inf? d) (not (int-inf? a)) (not (int-inf? b))) #f)
                (else (if swap (int-neg-lim d) d))))
        #f)))

(define (int-direct F e x a b)
  (let ((r (int-guard (lambda ()
                        (simplify (list '+ (subst (list '= x b) F)
                                        (list '* -1 (subst (list '= x a) F))))))))
    (and r (not (int-bad-log? r)) r)))

; ---------- первообразная с суммой по корням (root-sum): определённый интеграл F(b) − F(a) ----------
; Σ α·log S(α, x) — комплексные логарифмы главной ветви; разность F(b) − F(a) верна, лишь если путь x ∈ [a, b] не пересекает
; разрез (отрицательную полуось) для каждого корня α. Если коэффициенты S при x^k (k ≥ 1) от t не зависят (например S = x + c(t),
; x² − 12t), то Im S(α, x) — константа ≠ 0 для невещественных α (для вещественных α особенность — нуль знаменателя, её
; отсекает проверка особенностей) — безопасно. Иначе, при числовых Q и границах, непрерывность Im(log S(α, x)) проверяется
; по 200 точкам; в прочих случаях — невычисленная форма.

(define (int-log-args e)
  (cond ((not (op-expr? e)) '())
        ((and (equal? (car e) 'log) (= (length e) 2)) (cons (cadr e) (int-log-args (cadr e))))
        (else (append-map int-log-args (cdr e)))))

(define (int-rootsums e)
  (cond ((not (op-expr? e)) '())
        ((equal? (car e) 'root-sum) (list e))
        (else (append-map int-rootsums (cdr e)))))

; мнимая часть результата eval-num: число, (+ re (* im %i)) или (* im %i)
(define (int-imag-of z)
  (cond ((not (list? z)) 0)
        ((equal? (car z) '*) (cadr z))
        ((equal? (car z) '+) (int-imag-of (caddr z)))
        (else 0)))

; мнимый коэффициент значения eval-num, если он выделяется в простой форме (* im %i) | (+ re (* im %i)); иначе #f
(define (int-imag-part z)
  (cond ((and (op-expr? z) (equal? (car z) '*) (= (length z) 3)
              (equal? (caddr z) '%i) (real-numeric? (cadr z)))
         (cadr z))
        ((and (op-expr? z) (equal? (car z) '+) (= (length z) 3)
              (op-expr? (caddr z)) (equal? (car (caddr z)) '*) (= (length (caddr z)) 3)
              (equal? (caddr (caddr z)) '%i) (real-numeric? (cadr (caddr z))))
         (cadr (caddr z)))
        (else #f)))

; значение численно комплексное с ЗАМЕТНОЙ мнимой частью. Малый мнимый остаток округления комплексностью не считаем:
; в WASM Math.Log/Math.Atan2 отличаются от настольных на 1 ulp, и мнимые части сопряжённых слагаемых суммы по корням
; не сокращаются точно (5e-17 вместо 0), из-за чего верный вещественный ответ отбрасывался как комплексный
(define (int-complex-valued? r)
  (let* ((z (try (eval-num r) (lambda (er) 0)))
         (im (int-imag-part z))
         (m (try (num-abs z) (lambda (er) #f))))
    (cond ((not (contains-sym? z '%i)) #f)
          ((not im) #t)                     ; форма не разобрана — считаем комплексным (осторожно)
          ((not m) #t)
          (else (>= (abs im) (* 1e-12 (+ 1 m)))))))   ; замечание ревью: порог — шум округления (~1e-16), не 1e-6

; Im S(α, x) постоянна по x: все коэффициенты при x^k, k ≥ 1, не зависят от t (вещественны)
(define (int-rs-const-im? u tv x)
  (let* ((tg (together u)) (n (numer tg)) (dn (denom tg)))
    (and (x-free? dn x) (polynomial? n x)
         (every? (lambda (k) (x-free? (together (list '/ (coeff n x k) dn)) tv))
                 (map (lambda (k) (+ k 1)) (range (degree n x)))))))

(define (int-rs-arg-ok? u tv Q x na nb)
  (or (int-rs-const-im? u tv x)
      (and na nb (numeric-poly? Q tv)
           (every? (lambda (r)
                     (let ((vals (map (lambda (j)
                                        (int-imag-of (eval-num (list 'log (replace-expr (replace-expr u tv r) x
                                                                                       (+ na (* (- nb na) (/ j 200.0))))))))
                                      (range 201))))
                       (every? (lambda (pr) (< (abs (- (car pr) (cadr pr))) 3.0))
                               (map2 list (take vals 200) (cdr vals)))))
                   (nroots Q tv)))))

(define (int-rootsum-ok? F x a b)
  (let ((na (if (int-inf? a) #f (int-num a))) (nb (if (int-inf? b) #f (int-num b))))
    (every? (lambda (rs)
              (every? (lambda (u) (int-rs-arg-ok? u (cadr rs) (caddr rs) x na nb))
                      (int-log-args (nth rs 3))))
            (int-rootsums F))))

; Шаг S.3: определённый интеграл — рамка int-definite: первообразная (рамка integration), затем подстановка пределов
; (int-limits: F(b) − F(a)) либо пределы первообразной (int-improper); невычисленная форма — рамка отбрасывается
(define (int-unevaluated? v) (and (op-expr? v) (equal? (car v) 'integrate)))

(define (int-direct-step F e x a b)
  (with-step ('int-limits "Подстановка пределов: F(b) − F(a)"
              (list '+ (replace-expr F x b) (list '* -1 (replace-expr F x a)))
              :comment "формула Ньютона–Лейбница: ∫_a^b f dx = F(b) − F(a)")
    (int-direct F e x a b)))

(define (int-limits-step F x a b)
  (with-step ('int-improper "Несобственный интеграл: пределы первообразной"
              (list '+ (list 'limit F x b) (list '* -1 (list 'limit F x a)))
              :comment "∫_a^b f dx = lim F(x) при x → b − lim F(x) при x → a (с односторонними пределами у особых точек)")
    (int-by-limits F x a b)))

; INT.DEF2: первообразная с функциями, дающими скачок/деление на нуль (atan, tan, …) — проверяется на разрывы внутри [a, b]
(define (int-jump-gate? F a b)
  (and (not (int-inf? a)) (not (int-inf? b))
       (any? (lambda (h) (contains-sym? F h)) '(atan acot tan cot sec csc))))

; сумма односторонних пределов по частям [a, p1], [p1, p2], …, [pn, b]: F — первообразная на каждой открытой части
(define (int-jump-sum F x a b pts)
  (with-step ('int-improper "Несобственный интеграл: пределы первообразной"
              (list '+ (list 'limit F x b) (list '* -1 (list 'limit F x a)))
              :comment "первообразная разрывна внутри отрезка: отрезок разбит в точках разрыва, на каждой части — односторонние пределы")
    (let loop ((ps (append (list a) pts (list b))) (acc 0))
      (if (null? (cdr ps))
          (simplify acc)
          (let ((v (int-by-limits F x (car ps) (cadr ps))))
            (and v (not (int-inf? v)) (not (int-bad-log? v))
                 (loop (cdr ps) (+ acc v))))))))

(define (int-definite-core e x a b)
  (let* ((F (begin (int-guard (lambda () (risch::rs-tan-flag-clear!))) (int-antiderivative e x)))
         (tanf (and F (int-guard (lambda () (risch::rs-tan-flag?)))))
         (gate (and F (not (int-has-integrate? F)) (int-jump-gate? F a b)))
         (pts (if gate (or (int-guard (lambda () (definite::definite-split-points F x a b))) '()) '()))
         ; (Ньютон — Лейбниц) первообразная годна, если непрерывна на [a, b]: closed — подстановка, open — пределы
         (cont (and F (not (int-has-integrate? F)) (or tanf gate) (null? pts)
                    (int-guard (lambda () (definite::definite-continuous? F x a b))))))
    (cond ((not F) (int-unevaluated e x (list a b)))
          ((int-has-integrate? F) (int-unevaluated e x (list a b)))
          ; INT.DEF2: разрыв первообразной внутри отрезка — разбиение и односторонние пределы (иначе скачок теряется)
          ((and (pair? pts) (not (int-guard (lambda () (int-singular-inside? e x a b)))))
           (or (int-guard (lambda () (int-jump-sum F x a b pts))) (int-unevaluated e x (list a b))))
          ; 21k″: первообразная через tan(w) разрывна — подстановка пределов может дать неверное число
          ((and tanf (not cont)) (int-unevaluated e x (list a b)))
          ((not (int-guard (lambda () (int-rootsum-ok? F x a b)))) (int-unevaluated e x (list a b)))
          ((int-guard (lambda () (int-singular-inside? e x a b))) (int-unevaluated e x (list a b)))
          (else
           (or (and (not (int-inf? a)) (not (int-inf? b)) (not (equal? cont 'open))
                    (not (int-guard (lambda () (int-singular? e x a b))))
                    (int-direct-step F e x a b))
               (int-limits-step F x a b)
               (int-unevaluated e x (list a b)))))))

; классический путь: первообразная + подстановка пределов / пределы первообразной (его же зовёт definite как запасной)
(define (int-definite-classic e x a b)
  (if (step-log-enabled?) (set! int-avoid (cons x (int-symbols e x))))
  (let ((r (with-step ('int-definite "Определённый интеграл" (int-form-def e x a b)
                       :comment "∫_a^b f dx = F(b) − F(a), где F — первообразная f" :after int-p)
             (let ((v (int-definite-core e x a b))) (and (not (int-unevaluated? v)) v)))))
    (or r (int-unevaluated e x (list a b)))))

; DI.3: модуль definite — бесконечные пределы (сначала он), особенность внутри промежутка / отказ первообразной (после классики).
; (divergent …) → невычисленная форма + условие (divergent форма причина) (MCP: статус unknown, note «интеграл расходится»);
; unknown → классический результат / невычисленная форма. Рекурсии нет: definite зовёт (integrate f x a b 'classic).
(define (int-definite-new e x a b)
  (let ((v (int-guard (lambda () (definite-integral e x a b)))))
    (cond ((not v) #f)
          ((equal? v 'unknown) #f)
          ((and (pair? v) (equal? (car v) 'divergent))
           ; расходимость к ±∞ классика отдаёт значением inf/-inf (прежнее поведение: ∫₁^∞ 1/x = inf) — оно сохранено
           (let ((c (int-definite-classic e x a b)))
             (if (member? c '(inf -inf))
                 c
                 (let ((u (int-unevaluated e x (list a b))))
                   (record-condition (list 'divergent u (cadr v)) (string-append "интеграл расходится: " (cadr v)))
                   u))))
          (else v))))

; особые точки: шаги пробных пределов пишутся лишь при успехе (значение); пусто / unknown / divergent — рамка отброшена
(define (int-scan e x a b)
  (let ((res #f))
    (with-step ('int-scan "Особые точки внутри отрезка" (int-form-def e x a b)
                :comment "нули знаменателя, ветви log и степеней; интегрируемые — разбиение отрезка")
      (set! res (int-guard (lambda () (definite-interior e x a b))))
      (and res (not (equal? res 'unknown)) (not (and (pair? res) (equal? (car res) 'divergent))) res))
    res))

;; DEFINT (перенесён из ветки ds/DEFINT, только первый механизм): нет элементарной первообразной — пробуем
;; risch-special (сам проверяет производную) и подставляем пределы. Только конечные пределы и без особых точек
;; внутри отрезка; расходящееся не подменяется. Численный интервал как ответ integrate НЕ возвращается
;; (для гарантированного числа — certified_integral).
(define (int-definite-special e x a b)
  (and (not (int-inf? a)) (not (int-inf? b))
       (not (int-guard (lambda () (int-singular-inside? e x a b))))
       (not (int-guard (lambda () (int-singular? e x a b))))
       (let ((G (int-guard (lambda () (risch-special e x)))))
         (and G
              (not (int-has-integrate? G))
              (let ((v (int-guard (lambda () (int-direct-step G e x a b)))))
                (and v
                     (not (int-unevaluated? v))
                     (or (contains-sym? e '%i) (not (int-complex-valued? v)))
                     v))))))

;; Шаг CA.b: запасной путь для (−inf, inf) и (0, inf) — Жордан / замочная скважина (complex-analysis); ответ только после
;; численной сверки (definite-by-residues), полюса на вещественной оси без устранимости (главное значение) → #f
;; Шаг CA.c: ещё (−inf, 0) и период тригонометрии ([0, 2π], [−π, π], [0, π] при чётности) — те же правила: ответ только после сверки
(define (int-definite-residues e x a b)
  (and (or (and (equal? a '-inf) (equal? b 'inf)) (and (equal? a 0) (equal? b 'inf)) (and (equal? a '-inf) (equal? b 0))
           (and (not (int-inf? a)) (not (int-inf? b))))
       (let ((v (int-guard (lambda () (definite-by-residues e x a b)))))
         (and v (not (equal? v 'unknown)) v))))

(define (int-definite-raw e x a b)
  (let ((r (int-definite-raw1 e x a b)))
    (if (and (not (int-inf? a)) (not (int-inf? b)) (int-unevaluated? r))
        (or (int-definite-residues e x a b) r)
        r)))

(define (int-definite-raw1 e x a b)
  (if (or (int-inf? a) (int-inf? b))
      ; доказанно сходящийся (definite-convergence = convergent: абсолютно, без особенностей) — классика даёт верное значение
      ; пределами первообразной (и шаги int-improper); иначе (условная сходимость, параметры, расходимость) — definite первым
      (let ((r (if (equal? (int-guard (lambda () (definite-convergence e x a b))) 'convergent)
                   (let ((r0 (int-definite-classic e x a b)))
                     (if (int-unevaluated? r0) (or (int-definite-new e x a b) r0) r0))
                   (or (int-definite-new e x a b) (int-definite-classic e x a b)))))
        (if (int-unevaluated? r) (or (int-definite-residues e x a b) r) r))
      ; DI.4: сначала особые точки внутри отрезка (тригонометрия, ветви, нули знаменателя): без них — классика
      (let ((sp (int-scan e x a b)))
        (cond ((not sp)
               (let ((r (int-definite-classic e x a b)))
                 (cond ((int-unevaluated? r)
                        (or (int-definite-new e x a b)
                            ; элементарной первообразной нет — форма со специальными функциями (li, Ei, erf, Si, Ci)
                            (int-definite-special e x a b)
                            r))
                       ; вещественная подынтегральная, а значение комплексное (главная ветвь (-1)^{2/3} и т. п.) — не значение
                       ((and (not (contains-sym? e '%i)) (int-complex-valued? r))
                        (int-unevaluated e x (list a b)))
                       (else r))))
              ((equal? sp 'unknown) (int-unevaluated e x (list a b)))
              ((and (pair? sp) (equal? (car sp) 'divergent))
               (let ((u (int-unevaluated e x (list a b))))
                 (record-condition (list 'divergent u (cadr sp)) (string-append "интеграл расходится: " (cadr sp)))
                 u))
              (else sp)))))

; Q.1: в определённых интегралах шаг отказа Риша не пишется (свои рамки int-definite/int-limits)
(define (int-definite e x a b)
  (let ((old int-no-refusal-steps))
    (set! int-no-refusal-steps #t)
    (unwind-protect (int-definite-raw e x a b)
                    (set! int-no-refusal-steps old))))

(define (int-parse-args e more)
  (if (and (symbol? e) (not (null? more)) (not (symbol? (car more))))
      (cons (car more) (cons e (cdr more)))
      (cons e more)))

(define (integrate e &rest more)
  (let* ((args (int-parse-args e more)) (f (car args)) (x (cadr args)) (lims (cdr (cdr args))))
    (cond ((not (symbol? x)) (error "integrate: переменная интегрирования — символ"))
          ((object? f) (let ((r (try-method 'integrate (list f) (list f x)))) (if r (car r) (list 'integrate f x))))
          ((null? lims) (or (int-param-integrate f x)
                            (let ((F (int-antiderivative f x)))
                              (if F F (begin (int-note-refusal-steps f x)
                                             (int-unevaluated-final f x))))))
          ((= (length lims) 2) (int-definite f x (car lims) (cadr lims)))
          ; внутренний пятый аргумент 'classic (его ставит definite): только первообразная и пределы, без обращения к definite
          ((and (= (length lims) 3) (equal? (nth lims 2) 'classic)) (int-definite-classic f x (car lims) (cadr lims)))
          (else (error "integrate: ожидается (integrate e x) или (integrate e x a b)")))))
