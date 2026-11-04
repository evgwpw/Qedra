; risch/driver.lisp — драйвер алгоритма Риша: стратегия int-risch, log-случай (примитивный монома), три исхода: подшаг 21k.4
;
; Источники — Бронштейн, Symbolic Integration I, гл. 5–6 (драйвер, log-случай, порядок уровней башни).
; Башня, K[θ] — field.lisp/tower.lisp, Эрмит и ЛРТ — reduce.lisp. Эта часть — порядок действий по уровням.
;
; ---------- Исходы ----------
; Внутренние rs-int возвращают (F R): ∫ f = F + ∫ R, F — выражение (элементарная часть), R — остаток, ДОКАЗАННО неэлементарный
; (0 — остатка нет, ответ элементарен), либо #f — «не знаю» (алгебраика, тригонометрия, exp-уровни — подшаг 5, бюджет).
; «Не знаю» никогда не превращается в «неэлементарно». Три исхода int-risch:
;   * ответ F (элементарно, проверено int-check) или частичный F + (integrate R x) (F проверено, R записан в таблицу и в условие
;     (risch-nonelementary (integrate R x)));
;   * #f — каскад идёт дальше и даёт невычисленную форму как раньше;
;   * доказано неэлементарно (F = 0): int-risch возвращает #f, а подынтегральное попадает в таблицу rs-ne-table; api.lisp при
;     невычисленной форме пишет условие (risch-nonelementary (integrate f x)) — по нему статус JSON/MCP nonelementary (AgentApi.classify).
;
; ---------- Уровень (log, f ∈ K(θ), D θ ∈ K) ----------
; f = a/d: Эрмит f = Dg + h + r, r = P ∈ K[θ]. Логарифмическая часть h — ЛРТ: все вычеты константы → Σ c·log S (элементарно);
; иначе ∫ h неэлементарен (остаток h − D(явные логарифмы) — частичный ответ). Многочлен P = Σ aᵢθⁱ, сверху вниз: ∫ aₘ в K —
; результат обязан быть q + c′·log u (θ = log u), c′ константа: Q = q·θᵐ + (c′/(m+1))·θᵐ⁺¹, P ← P − DQ (степень падает).
; Другие логарифмы в ∫ aₘ или неэлементарный ∫ aₘ — остаток P целиком неэлементарен. aₘ ∈ K интегрируется тем же rs-int на башне ниже;
; база ℚ(x) — rat-integrate-log (21h). Нулевой коэффициент a₀ — просто rs-int по K.

(module risch
  (export risch-integrate risch-nonelementary?))

(algorithm-register 'risch '(on off) 'on)

(define rs-tv '%rst)                                                 ; связанная переменная root-sum до переименования
(define rs-cur-table '())                                            ; таблица башни текущего запуска (для шагов)
(define rs-ne-table '())                                             ; доказанно неэлементарные ((выражение x) …), не более 64

; ---------- кандидаты ----------
(define (rs-has-kernel? e x)
  (and (pair? e) (contains-sym? e x)
       (or (member? (car e) '(exp log ln sinh cosh tanh atan sin cos tan cot sec csc))
           (and (equal? (car e) '^) (= (length e) 3) (contains-sym? (caddr e) x))
           (any? (lambda (a) (rs-has-kernel? a x)) (cdr e)))))

(define (rs-has-nontrig-kernel? e x)
  (and (pair? e) (contains-sym? e x)
       (or (member? (car e) '(exp log ln sinh cosh tanh atan))
           (and (equal? (car e) '^) (= (length e) 3) (contains-sym? (caddr e) x))
           (any? (lambda (a) (rs-has-nontrig-kernel? a x)) (cdr e)))))

; ---------- шаги ----------
(define (rs-show e) (if (equal? e 0) 0 (rs-back-subst e rs-cur-table)))

; ---------- печать формул в шагах (ST.3д) ----------
; MathPrinter с подстановкой подписей уровней (%t1 → θ1) и символа вычетов; при ошибке — обычная печать
(define (rs-mp* binds e)
  (try (math-print (if (null? binds) e (subst binds e))) (lambda (err) (to-string e))))
(define (rs-mp e) (rs-mp* '() e))
(define (rs-mp-join ss)
  (if (null? ss) "" (foldl (lambda (acc s) (string-append acc ", " s)) (car ss) (cdr ss))))

(define (rs-theta-name k) (string->symbol (string-append "θ" (to-string (+ k 1)))))
(define (rs-theta-binds tw)
  (map2 (lambda (lv k) (list (rs-level-theta lv) (rs-theta-name k)))
        (rs-levels tw) (range (length (rs-levels tw)))))
(define (rs-mp-tower tw e) (rs-mp* (rs-theta-binds tw) e))
(define (rs-th-subst tw e) (if (null? (rs-levels tw)) e (subst (rs-theta-binds tw) e)))

(define (rs-kind-ru k)
  (cond ((equal? k 'log) "логарифмическое")
        ((equal? k 'exp) "экспоненциальное")
        ((equal? k 'atan) "арктангенс")
        ((equal? k 'tan) "тангенс")
        (else (to-string k))))

; случай уровня для пояснения: база ℚ(x), примитивный, экспоненциальный, тангенс
(define (rs-case-ru c)
  (cond ((equal? c 'base) "база ℚ(x)")
        ((equal? c 'primitive) "примитивное расширение")
        ((equal? c 'exp) "экспоненциальное расширение")
        ((equal? c 'tan) "тангенс-расширение")
        (else (to-string c))))

; определение уровня: θ = log u / exp η / atan u / tan u
(define (rs-level-def lv)
  (let ((k (rs-level-kind lv)) (a (rs-level-arg lv)))
    (cond ((equal? k 'log) (list 'log a))
          ((equal? k 'exp) (list 'exp a))
          ((equal? k 'atan) (list 'atan a))
          ((equal? k 'tan) (list 'tan a))
          (else a))))

; «ℚ(x)(θ1 = log x)(θ2 = exp(x))»
(define (rs-tower-str tw)
  (let ((bs (rs-theta-binds tw)))
    (string-append "ℚ(" (to-string (rs-tower-x tw)) ")"
                   (apply string-append
                          (map2 (lambda (lv b)
                                  (string-append "(" (to-string (cadr b)) " = "
                                                 (rs-mp* bs (rs-level-def lv)) ")"))
                                (rs-levels tw) bs)))))

; «θ1 — логарифмическое, Dθ1 = 1/x» для каждого уровня
(define (rs-tower-types tw)
  (let ((bs (rs-theta-binds tw)))
    (rs-mp-join (map2 (lambda (lv b)
                        (string-append (to-string (cadr b)) " — " (rs-kind-ru (rs-level-kind lv))
                                       ", D" (to-string (cadr b)) " = "
                                       (rs-mp* bs (rs-level-dtheta lv))))
                      (rs-levels tw) bs))))

; замены уровней по таблице башни: «θ1 → log x, θ2 → exp(x)»
(define (rs-tower-subst tw)
  (rs-mp-join
   (map (lambda (b)
          (let ((en (assoc (car b) rs-cur-table)))
            (string-append (to-string (cadr b)) " → "
                           (if en (integrate::int-mp (cadr en)) "?"))))
        (rs-theta-binds tw))))

; ---------- пояснения к шагам (ST.3д) ----------
; дробь K(θ) формулой (θ-символы заменяются на θ1, θ2, …)
(define (rs-frac-mp tw f)
  (if (null? (car f)) "0" (rs-mp-tower tw (rs-frac-expr tw f))))

; знаменатель, разложение Сквайра, алгебраическая часть g, остаток h + r
(define (rs-hermite-comment tw d g h r)
  (let* ((sp (try (rs-splitfactor tw d) (lambda (err) '(() (1)))))
         (dn (car sp))
         (sq (and (pair? dn) (try (cdr (rs-sqfree dn)) (lambda (err) '())))))
    (string-append "знаменатель d = " (rs-mp-tower tw (rs-to-expr d (rs-top-theta tw)))
                   (if (null? sq)
                       "; d бесквадратен — алгебраической части нет"
                       (string-append "; разложение Сквайра: "
                                      (rs-mp-join (map (lambda (fm)
                                                         (string-append "(" (rs-mp-tower tw (rs-to-expr (car fm) (rs-top-theta tw)))
                                                                        ")^" (to-string (cadr fm))))
                                                       sq))))
                   "; алгебраическая часть g = " (rs-frac-mp tw g)
                   "; остаток: h = " (rs-frac-mp tw h)
                   ", r = " (rs-mp-tower tw (rs-frac-expr tw r)))))

; корни множителя резольвенты (степень 1 — явно, 2 — solve, иначе не выписываются)
(define (rs-lrt-roots-str f)
  (let ((d (rs-deg f)))
    (cond ((= d 1) (list (rs-nf (list '* -1 (nth f 1) (list '^ (nth f 0) -1)))))
          ((= d 2) (try (set->list (solve (list '= (rs-to-expr f rs-z) 0) rs-z)) (lambda (err) '())))
          (else '()))))

; резольвента R(z) = res_θ(D, A − z·D′), её корни и постоянство (R | κ(R)) — метод ЛРТ
(define (rs-lrt-comment tw)
  (if (null? rs-lrt-last)
      "вычетов нет: числитель после редукции Эрмита нулевой или знаменатель постоянен"
      (let* ((R (car rs-lrt-last)) (fs (cadr rs-lrt-last)) (bs (rs-theta-binds tw))
             (allconst (every? (lambda (p) (= (nth p 2) (nth p 3))) fs))
             (parts (map (lambda (p)
                           (let* ((f (car p)) (m (cadr p)) (dq (nth p 2)) (df (nth p 3))
                                  (rts (rs-lrt-roots-str f)))
                             (string-append (if (null? rts)
                                                (string-append "множитель степени " (to-string df)
                                                               " (кратность " (to-string m) ")")
                                                (rs-mp-join (map (lambda (r) (string-append "z = " (rs-mp* bs r)))
                                                                 rts)))
                                            (if (= dq df) " — корни постоянны"
                                                " — корень не постоянен"))))
                         fs)))
        (string-append "резольвента R(z) = res_θ(d, a − z·Dd) = "
                       (rs-mp* bs (subst (list (list rs-z 'z)) R))
                       "; корни: " (rs-mp-join parts)
                       (if allconst
                           "; все корни — константы ⇒ вычеты постоянны (R | κ(R)), логарифмическая часть элементарна"
                           "; корень не константа ⇒ вычет не константа: логарифмическая часть неэлементарна (теорема Лиувилля)")))))

; правила, которые попадают в brief (остальные — detail: полное дерево)
(define rs-main-rules '(risch-tower risch-hermite risch-lrt risch-check risch-nonelementary
                        risch-poly risch-rde risch-prde risch-tan))

; причина последнего отказа уровня (RDE/prde) — попадает в шаг отказа
(define rs-ne-reason-last #f)
; шаг «многочленная часть» пишется один раз на уровень (вложенные вызовы не дублируют)
(define rs-poly-noted #f)
(define rs-poly-depth 0)

; отказ виден и в журнале: рамка неудачи отбрасывается steps, поэтому шаг пишется снаружи,
; когда доказано, что интеграл неэлементарен
(define (rs-note-refusal e x)
  (if (step-log-enabled?)
      (record-step 'risch-nonelementary "Алгоритм Риша: интеграл неэлементарен"
                   (if rs-ne-reason-last
                       (string-append rs-ne-reason "; " rs-ne-reason-last)
                       rs-ne-reason)
                   (integrate::int-form e x) 'неэлементарно 'main))
  #f)

; Расчёт идёт под call-quietly (diff и int-check не пишут свои шаги в рамку risch): заметки копятся в rs-notes только при rs-log?
; (журнал был включён при входе в int-risch) и переносятся в журнал после расчёта — rs-flush-notes!
(define rs-log? #f)
(define rs-notes '())
(define (rs-note rule title comment before after)
  (if rs-log? (set! rs-notes (cons (list rule title comment before after) rs-notes))))
(define (rs-flush-notes!)
  (map (lambda (n) (record-step (car n) (cadr n) (caddr n) (nth n 3) (nth n 4)
                                (if (member? (car n) rs-main-rules) 'main 'detail)))
       (reverse rs-notes))
  (set! rs-notes '()))

; ---------- разбор логарифмов результата нижнего уровня ----------
(define (rs-terms e) (let ((s (simplify e))) (if (and (pair? s) (equal? (car s) '+)) (cdr s) (list s))))

; слагаемое с логарифмом/атаном/суммой по корням от неконстанты (константа относительно башни lo — не считается)
(define (rs-nonconst-log? t lo)
  (cond ((not (pair? t)) #f)
        ((rs-const? t lo) #f)
        ((member? (car t) '(atan root-sum)) #t)
        ((and (equal? (car t) 'log) (not (rs-const? (cadr t) lo))) #t)
        (else (any? (lambda (a) (rs-nonconst-log? a lo)) (cdr t)))))

(define (rs-log-head? f lo) (and (pair? f) (equal? (car f) 'log) (not (rs-const? (cadr f) lo))))
; c·log v с константным c → (c v), иначе #f
(define (rs-log-term t lo)
  (cond ((rs-log-head? t lo) (list 1 (cadr t)))
        ((and (pair? t) (equal? (car t) '*))
         (let ((ls (filter (lambda (f) (rs-log-head? f lo)) (cdr t)))
               (os (filter (lambda (f) (not (rs-log-head? f lo))) (cdr t))))
           (and (= (length ls) 1) (rs-const? (cons '* os) lo)
                (list (if (null? os) 1 (simplify (cons '* os))) (cadr (car ls))))))
        (else #f)))

(define (rs-first f l) (cond ((null? l) #f) (else (or (f (car l)) (rs-first f (cdr l))))))

; log v как элемент K башни lo: log v = k + log r (r — константа): θ уровня log с аргументом ~ v или аргумент уровня exp с θ ~ v;
; результат (k r) либо #f
(define (rs-log-in-k lo v)
  (rs-first (lambda (lv)
              (let ((ra (rs-ratio v (rs-level-arg lv))) (rt (rs-ratio v (rs-level-theta lv))))
                (cond ((and (equal? (rs-level-kind lv) 'log) (rs-const? ra lo)) (list (rs-level-theta lv) ra))
                      ((and (equal? (rs-level-kind lv) 'exp) (rs-const? rt lo)) (list (rs-level-arg lv) rt))
                      (else #f))))
            (rs-levels lo)))

; логарифмы элементов K (log x при θ = log x) заменяются на θ + log(константа); аргументы переписываются раньше самого log
; (21k.5′) atan v как q·θⱼ + const для уровня atan θⱼ башни lo: D(atan v) = q·Dθⱼ, q — рациональная константа → (θⱼ q) или #f
(define (rs-atan-q lo v dtheta)
  (let* ((w (rs-nf (list '* (rs-deriv lo v) (list '^ (list '+ 1 (list '^ v 2)) -1))))
         (q (rs-ratio w dtheta)))
    (and (rs-const? q lo) (rational-number? q) q)))
(define (rs-atan-in-k lo v)
  (rs-first (lambda (lv) (and (equal? (rs-level-kind lv) 'atan)
                              (let ((q (rs-atan-q lo v (rs-level-dtheta lv)))) (and q (list (rs-level-theta lv) q)))))
            (rs-levels lo)))

(define (rs-subst-logs e lo)
  (if (not (pair? e))
      e
      (let ((args (map (lambda (a) (rs-subst-logs a lo)) (cdr e))))
        (cond ((and (equal? (car e) 'log) (= (length args) 1) (not (rs-const? (car args) lo)))
               (let ((k (rs-log-in-k lo (car args))))
                 (if k (list '+ (car k) (list 'log (cadr k))) (cons 'log args))))
              ((and (equal? (car e) 'atan) (= (length args) 1) (not (rs-const? (car args) lo)))
               (let ((k (rs-atan-in-k lo (car args))))
                 (if k (list '* (cadr k) (car k)) (cons 'atan args))))
              (else (cons (car e) args))))))

; c·atan v (v неконстанта) → c·q, где D(atan v) = q·Dθ верхнего уровня atan; иначе #f
(define (rs-atan-head? f lo) (and (pair? f) (equal? (car f) 'atan) (= (length f) 2) (not (rs-const? (cadr f) lo))))
(define (rs-atan-term t lo top)
  (let ((one (lambda (f) (rs-atan-q lo (cadr f) (rs-level-dtheta top)))))
    (cond ((rs-atan-head? t lo) (one t))
          ((and (pair? t) (equal? (car t) '*))
           (let ((as (filter (lambda (f) (rs-atan-head? f lo)) (cdr t)))
                 (os (filter (lambda (f) (not (rs-atan-head? f lo))) (cdr t))))
             (and (= (length as) 1) (rs-const? (cons '* os) lo)
                  (let ((q (one (car as)))) (and q (simplify (list '* q (if (null? os) 1 (cons '* os)))))))))
          (else #f))))

; вклад слагаемого в коэффициент при θ верхнего уровня (log: c·log v, v ~ u; atan: c·atan v, D atan v ~ Dθ) или #f
(define (rs-top-term t lo top)
  (if (equal? (rs-level-kind top) 'atan)
      (rs-atan-term t lo top)
      (let ((lt (rs-log-term t lo)))
        (and lt (rs-const? (rs-ratio (cadr lt) (rs-level-arg top)) lo) (car lt)))))

; слагаемые F (после rs-subst-logs): вклад в θ верхнего уровня → c′; другие логарифмы/атаны/суммы по корням от неконстант → #f
(define (rs-split-loop ts top lo qs c)
  (if (null? ts)
      (list (if (null? qs) 0 (simplify (cons '+ qs))) c)
      (let ((lt (rs-top-term (car ts) lo top)))
        (cond (lt (rs-split-loop (cdr ts) top lo qs (simplify (list '+ c lt))))
              ((rs-nonconst-log? (car ts) lo) #f)
              (else (rs-split-loop (cdr ts) top lo (cons (car ts) qs) c))))))

; F = q + c′·θ (θ = log u или atan u верхнего уровня tw; + слагаемые без логарифмов/атанов от неконстант) → (q c′); иначе #f
(define (rs-split-logs F tw)
  (let ((lo (rs-lower tw))) (rs-split-loop (rs-terms (rs-subst-logs F lo)) (rs-top tw) lo '() 0)))

; ---------- многочленная часть (log) ----------
(define (rs-ne-all tw P) (list 0 (rs-to-expr P (rs-top-theta tw))))     ; остаток — весь P

(define (rs-poly-step tw P m sp)
  (let* ((th (rs-top-theta tw)) (c (rs-nf (list '* (cadr sp) (/ 1 (+ m 1)))))
         (Q (rs-add (rs-shift (list c) (+ m 1)) (rs-shift (list (car sp)) m)))
         (P2 (rs-sub P (rs-deriv-poly tw Q))))
    (if (>= (rs-deg P2) m)
        (rs-unknown "многочленная часть: старший коэффициент не сократился" P)
        (let ((rest (rs-int-poly tw P2)))
          (and rest (list (simplify (list '+ (rs-to-expr Q th) (car rest))) (cadr rest)))))))

; (21k.7a) Условие Бронштейна для старшего коэффициента: aₘ = Dv + c·Dθ, v ∈ K, c — константа (ограниченное интегрирование,
; prde.lisp). Быстрый путь прежний — ∫ aₘ в K и разбор q + c′θ (rs-split-logs); ограниченное интегрирование решает там, где
; быстрый путь не смог: ∫ aₘ не взят («не знаю») или в нём есть логарифмы/атаны, не распознанные как c′θ (раньше это сразу
; объявлялось неэлементарным). none — доказано (остаток P целиком), unknown — «не знаю».
(define (rs-poly-limited tw P)
  (let* ((lo (rs-lower tw)) (dth (rs-level-dtheta (rs-top tw)))
         (lr (rs-limited-integrate lo (car P) (list dth))))
    (if rs-log?
        (rs-note 'risch-limited "Алгоритм Риша: ограниченное интегрирование"
                 (cond ((equal? (car lr) 'ok) "старший коэффициент aₘ = Dv + c·Dθ: найдены v в поле ниже и константа c")
                       ((equal? (car lr) 'none) "aₘ ≠ Dv + c·Dθ ни при каких v и c — многочлен по θ неэлементарен")
                       (else "aₘ = Dv + c·Dθ: задача не решена"))
                 (integrate::int-form (rs-show (car P)) (rs-tower-x tw))
                 (if (equal? (car lr) 'ok)
                     (simplify (list '+ (rs-show (cadr lr)) (list '* (car (caddr lr)) (rs-show (rs-top-theta tw)))))
                     (integrate::int-form (rs-show (car P)) (rs-tower-x tw)))))
    (cond ((equal? (car lr) 'ok) (rs-poly-step tw P (rs-deg P) (list (cadr lr) (car (caddr lr)))))
          ((equal? (car lr) 'none) (rs-ne-all tw P))
          (else #f))))

(define (rs-int-poly-top tw P)
  (set! rs-poly-depth (+ rs-poly-depth 1))
  (let* ((lo (rs-lower tw)) (th (rs-top-theta tw)) (r (rs-int lo (car P)))
         (res (cond ((not r) (rs-poly-limited tw P))
                    ((not (equal? (cadr r) 0)) (rs-ne-all tw P))
                    (else (let ((sp (rs-split-logs (car r) tw)))
                            (if sp (rs-poly-step tw P (rs-deg P) sp) (rs-poly-limited tw P)))))))
    (set! rs-poly-depth (- rs-poly-depth 1))
    (if (and rs-log? (= rs-poly-depth 0))
        (rs-note 'risch-poly "Алгоритм Риша: многочленная часть"
                 (string-append "P = " (rs-mp-tower tw (rs-to-expr P th))
                                "; deg P = " (to-string (rs-deg P))
                                "; старший коэффициент a" (to-string (rs-deg P)) " = "
                                (rs-mp-tower tw (rs-lc P))
                                "; коэффициенты интегрируются сверху вниз, aₘ — уровнем ниже (q + c·log u или граница Бронштейна)")
                 (rs-th-subst tw (rs-to-expr P th))
                 (cond ((not res) 'не-решено)
                       ((equal? (cadr res) 0) (rs-show (car res)))
                       (else (list '+ (rs-show (car res))
                                   (integrate::int-form (rs-show (cadr res)) (rs-tower-x tw)))))))
    res))

(define (rs-int-poly tw P)
  (cond ((null? P) (list 0 0))
        ((= (rs-deg P) 0) (rs-int (rs-lower tw) (car P)))
        (else (rs-int-poly-top tw P))))

; ---------- логарифмическая часть h = hn/hd (знаменатель бесквадратный, нормальный) ----------
; все вычеты константы → (Σ c·log S, 0); иначе (явные логарифмы, h − их производная); #f — ЛРТ не смогла
(define (rs-explicit-terms tw entries)
  (append-map (lambda (en) (filter (lambda (t) (not (contains-sym? t 'root-sum))) (rs-entry-terms tw en rs-tv))) entries))

(define (rs-int-log-part tw hn hd)
  (let ((rr (rs-residue-reduce tw hn hd)))
    (if rs-log?
        (let ((ts (and rr (rs-explicit-terms tw (car rr)))))
          (rs-note 'risch-lrt "Алгоритм Риша: логарифмическая часть (резольвента)"
                   (rs-lrt-comment tw)
                   (rs-th-subst tw (rs-frac-expr tw (list hn hd)))
                   (cond ((not rr) 'не-решено)
                         ((null? ts) (rs-th-subst tw (rs-frac-expr tw (list hn hd))))
                         (else (rs-th-subst tw (simplify (cons '+ ts))))))))
    (cond ((not rr) #f)
          ((cadr rr) (list (rs-log-part tw (car rr) rs-tv) 0))
          (else
           (let* ((ts (rs-explicit-terms tw (car rr))) (L (if (null? ts) 0 (simplify (cons '+ ts))))
                  (rem (rs-nf (list '+ (rs-frac-expr tw (list hn hd)) (list '* -1 (rs-deriv tw L))))))
             (list L rem))))))

; ---------- дробь на примитивном уровне ----------
(define (rs-int-frac tw a d)
  (let* ((x (rs-tower-x tw)) (hm (rs-hermite tw a d)) (g (car hm)) (h (cadr hm)) (r (caddr hm))
         (gx (if (null? (car g)) 0 (rs-frac-expr tw g)))
         (P (rs-scale (car r) (rs-inv (car (cadr r))))))                   ; для log знаменатель r — 1
    (if rs-log?
        (rs-note 'risch-hermite "Алгоритм Риша: редукция Эрмита"
                 (rs-hermite-comment tw d g h r)
                 (rs-th-subst tw (rs-frac-expr tw (list a d)))
                 (rs-th-subst tw (simplify (list '+ gx (rs-frac-expr tw h) (rs-to-expr P (rs-top-theta tw)))))))
    (let* ((hres (if (null? (car h)) (list 0 0) (rs-int-log-part tw (car h) (cadr h))))
           (pres (and hres (rs-int-poly tw P))))
      (cond ((not hres) #f)
            ((and (not pres) (equal? (cadr hres) 0)) #f)
            (else
             (let* ((F (simplify (list '+ gx (car hres) (if pres (car pres) 0))))
                    (R0 (list '+ (cadr hres) (if pres (cadr pres) (rs-to-expr P (rs-top-theta tw)))))
                    (R (if (rs-zero? R0) 0 R0)))
               (if rs-log?
                   (rs-note 'risch-log-part "Алгоритм Риша: логарифмическая и многочленная части"
                            (if (equal? R 0) "вычеты постоянны (метод Лазара–Риобу–Трагера), многочлен по θ интегрируется сверху вниз"
                                "найден неконстантный вычет или нет подходящего q + c·log u: остаток неэлементарен")
                            (integrate::int-form (rs-show (rs-frac-expr tw (list a d))) x)
                            (if (equal? R 0) (rs-show F) (list '+ (rs-show F) (integrate::int-form (rs-show R) x)))))
               (list F R)))))))

; ---------- exp-уровень (θ = exp η, Dθ = Dη·θ): Лорановы многочлены K[θ, 1/θ] ----------
; f = a/d: d = dₙ·θᵏ. Эрмит по нормальной части → g, h, r = P/θᵐ (Лоранов многочлен). ЛРТ для h: у унитарного S полиномиальная
; часть DS/S равна deg S·Dη, поэтому h − D(Σ α·log S) = Dη·Σ deg S·q_{k−1} (Σ корней Q = −q_{k−1}) — добавка к θ⁰.
; Каждый aᵢθⁱ (i ≠ 0): RDE Dyᵢ + i·Dη·yᵢ = aᵢ в K (rs-rde); нет решения — доказательство неэлементарности слагаемого
; (интегратор Риша для exp: ∫ f элементарен ⇔ все эти RDE разрешимы в K и ∫ a₀ элементарен в K). a₀ — rs-int уровнем ниже.
(define (rs-eta tw) (rs-deriv (rs-lower tw) (rs-level-arg (rs-top tw))))

; Лоранов многочлен — список (i aᵢ) с ненулевыми aᵢ; из num/θᵐ
(define (rs-laurent-of num m)
  (filter (lambda (p) (not (rs-zero? (cadr p))))
          (map2 (lambda (c k) (list (- k m) c)) num (reverse (range (length num))))))
(define (rs-laurent-expr L th)
  (if (null? L) 0 (simplify (cons '+ (map (lambda (p) (list '* (cadr p) (list '^ th (car p)))) L)))))

(define (rs-exp-log-shift tw entries)
  (rs-nf (list '* (rs-eta tw)
               (cons '+ (cons 0 (map (lambda (en) (let ((Q (car en))) (list '* (rs-deg (cadr en)) (if (> (length Q) 1) (cadr Q) 0))))
                                     entries))))))

; логарифмическая часть на exp-уровне → (L остаток добавка-к-θ⁰) | #f
(define (rs-int-exp-log tw hn hd)
  (let ((rr (rs-residue-reduce tw hn hd)))
    (if rs-log?
        (let ((ts (and rr (rs-explicit-terms tw (car rr)))))
          (rs-note 'risch-lrt "Алгоритм Риша: логарифмическая часть (резольвента)"
                   (rs-lrt-comment tw)
                   (rs-th-subst tw (rs-frac-expr tw (list hn hd)))
                   (cond ((not rr) 'не-решено)
                         ((null? ts) (rs-th-subst tw (rs-frac-expr tw (list hn hd))))
                         (else (rs-th-subst tw (simplify (cons '+ ts))))))))
    (cond ((not rr) #f)
          ((cadr rr) (list (rs-log-part tw (car rr) rs-tv) 0 (rs-exp-log-shift tw (car rr))))
          (else
           (let* ((ts (rs-explicit-terms tw (car rr))) (L (if (null? ts) 0 (simplify (cons '+ ts))))
                  (rem (rs-nf (list '+ (rs-frac-expr tw (list hn hd)) (list '* -1 (rs-deriv tw L))))))
             (list L rem 0))))))

; параметры в Dη (exp(a·x)): ответ RDE верен при генерических значениях — условие и заметка
(define (rs-note-generic lo e)
  (let ((ps (filter (lambda (s) (not (member? s (rs-vars lo)))) (variables e))))
    (if (pair? ps)
        (record-condition (list 'risch-generic e) "risch: параметры в показателе экспоненты считаются генерическими (показатель не вырождается)"))))

; один член aᵢθⁱ → (ok y) | (partial y r) | (none причина) | (unknown причина)
; (21k.7b) none — частичное решение (rs-rde-partial): aᵢ = Dy + i·Dη·y + r, ∫ aᵢθⁱ = y·θⁱ + ∫ r·θⁱ, остаток неэлементарен
(define (rs-exp-term tw p)
  (let* ((lo (rs-lower tw)) (i (car p)) (th (rs-top-theta tw)) (fi (rs-mulc i (rs-eta tw))) (r0 (rs-rde lo fi (cadr p)))
         (pp (and (equal? (car r0) 'none) rs-rde-partials? (rs-rde-partial lo fi (cadr p))))
         (r (if (and pp (not (rs-zero? (car pp)))) (list 'partial (car pp) (cadr pp)) r0)))
    (rs-note-generic lo fi)
    (if (and (equal? (car r) 'none) (cadr r)) (set! rs-ne-reason-last (cadr r)))
    (if rs-log?
        (rs-note 'risch-rde "Алгоритм Риша: уравнение Риша"
                 (string-append "Dy + i·Dη·y = aᵢ: f = " (rs-mp-tower tw fi)
                                ", g = " (rs-mp-tower tw (cadr p))
                                ", поле ниже — " (rs-case-ru (rs-case lo))
                                (cond ((equal? (car r) 'ok) "; найдено решение y в поле ниже, ∫ aᵢθⁱ = y·θⁱ")
                                      ((equal? (car r) 'partial) "; решения нет; частичное y: aᵢ = Dy + i·Dη·y + r, остаток неэлементарен")
                                      ((equal? (car r) 'none) (string-append "; решения нет: " (cadr r) " ⇒ слагаемое неэлементарно"))
                                      (else (string-append "; не решено: " (cadr r)))))
                 (integrate::int-form (rs-show (list '* (cadr p) (list '^ th i))) (rs-tower-x tw))
                 (cond ((equal? (car r) 'ok) (rs-show (list '* (cadr r) (list '^ th i))))
                       ((equal? (car r) 'partial)
                        (list '+ (rs-show (list '* (cadr r) (list '^ th i)))
                              (integrate::int-form (rs-show (list '* (caddr r) (list '^ th i))) (rs-tower-x tw))))
                       (else (rs-show (cadr p))))))
    r))

; (rs-int-laurent tw L) → (F R) | #f
(define (rs-int-laurent tw L)
  (let* ((th (rs-top-theta tw)) (lo (rs-lower tw))
         (a0 (rs-nf (cons '+ (cons 0 (map cadr (filter (lambda (p) (= (car p) 0)) L))))))
         (terms (filter (lambda (p) (not (= (car p) 0))) L))
         (res (map (lambda (p) (list p (rs-exp-term tw p))) terms))
         (r0 (rs-int lo a0))
         (pick (lambda (kind) (map car (filter (lambda (pr) (equal? (car (cadr pr)) kind)) res))))
         (oks (filter (lambda (pr) (member? (car (cadr pr)) '(ok partial))) res))
         (parts (map (lambda (pr) (list (car (car pr)) (caddr (cadr pr)))) (filter (lambda (pr) (equal? (car (cadr pr)) 'partial)) res)))
         (F (simplify (cons '+ (cons (if r0 (car r0) 0)
                                     (map (lambda (pr) (list '* (cadr (cadr pr)) (list '^ th (car (car pr))))) oks)))))
         (Rn (list '+ (rs-laurent-expr (pick 'none) th) (rs-laurent-expr parts th) (if r0 (cadr r0) 0)))
         (U (list '+ (rs-laurent-expr (pick 'unknown) th) (if r0 0 a0))))
    (cond ((rs-zero? U) (list F (if (rs-zero? Rn) 0 Rn)))
          ((rs-zero? Rn) #f)
          (else (list F (list '+ Rn U))))))

(define (rs-int-exp-frac tw a d)
  (let* ((x (rs-tower-x tw)) (th (rs-top-theta tw)) (hm (rs-hermite tw a d)) (g (car hm)) (h (cadr hm)) (r (caddr hm))
         (gx (if (null? (car g)) 0 (rs-frac-expr tw g)))
         (m (rde-ord (cadr r))))
    (if (not (= m (rs-deg (cadr r))))
        (rs-unknown "exp-уровень: знаменатель остатка Эрмита не степень θ" (cadr r))
        (let* ((rn (rs-scale (car r) (rs-inv (car (cadr r))))))
          (if rs-log?
              (rs-note 'risch-hermite "Алгоритм Риша: редукция Эрмита"
                       (rs-hermite-comment tw d g h r)
                       (rs-th-subst tw (rs-frac-expr tw (list a d)))
                       (rs-th-subst tw (simplify (list '+ gx (rs-frac-expr tw h)
                                                       (rs-laurent-expr (rs-laurent-of rn m) th))))))
          (let* ((hres (if (null? (car h)) (list 0 0 0) (rs-int-exp-log tw (car h) (cadr h))))
                 (L (and hres (append (rs-laurent-of rn m) (if (rs-zero? (caddr hres)) '() (list (list 0 (caddr hres))))))))
            (let ((pres (and hres (rs-int-laurent tw L))))
            (cond ((not hres) #f)
                  ((and (not pres) (equal? (cadr hres) 0)) #f)
                  (else
                   (let* ((F (simplify (list '+ gx (car hres) (if pres (car pres) 0))))
                          (R0 (list '+ (cadr hres) (if pres (cadr pres) (rs-laurent-expr L th))))
                          (R (if (rs-zero? R0) 0 R0)))
                     (if rs-log?
                         (rs-note 'risch-exp-part "Алгоритм Риша: экспоненциальная часть"
                                  (if (equal? R 0) "вычеты постоянны, для каждого aᵢθⁱ решено уравнение Риша, a₀ проинтегрировано уровнем ниже"
                                      "неконстантный вычет или уравнение Риша без решения: остаток неэлементарен")
                                  (integrate::int-form (rs-show (rs-frac-expr tw (list a d))) x)
                                  (if (equal? R 0) (rs-show F) (list '+ (rs-show F) (integrate::int-form (rs-show R) x)))))
                     (list F R))))))))))

(define (rs-int-exp tw f)
  (let* ((th (rs-top-theta tw)) (tg (together f))
         (a (rs-from-expr (numer tg) th)) (d (rs-from-expr (denom tg) th))
         (k (rde-ord d)) (dn (rs-quo d (rde-mono 1 k))))
    (if (< (rs-deg dn) 1)
        (let* ((L (rs-laurent-of (rs-scale a (rs-inv (car dn))) k)) (res (rs-int-laurent tw L)))
          (if (and res rs-log?)
              (rs-note 'risch-exp-part "Алгоритм Риша: экспоненциальная часть"
                       (if (equal? (cadr res) 0) "для каждого aᵢθⁱ решено уравнение Риша, a₀ проинтегрировано уровнем ниже"
                           "уравнение Риша без решения: остаток неэлементарен")
                       (integrate::int-form (rs-show f) (rs-tower-x tw))
                       (if (equal? (cadr res) 0) (rs-show (car res))
                           (list '+ (rs-show (car res)) (integrate::int-form (rs-show (cadr res)) (rs-tower-x tw))))))
          res)
        (rs-int-exp-frac tw a d))))

; ---------- уровень башни ----------
(define (rs-int-prim tw f)
  (let* ((th (rs-top-theta tw)) (tg (together f))
         (a (rs-from-expr (numer tg) th)) (d (rs-from-expr (denom tg) th)))
    (if (< (rs-deg d) 1)
        (rs-int-poly tw (rs-scale a (rs-inv (car d))))
        (rs-int-frac tw a d))))

; (rs-int tw f) → (F R) | #f: f — элемент K башни tw (выражение от x, θ)
(define (rs-int tw f)
  (cond ((rs-zero? f) (list 0 0))
        ((null? (rs-levels tw)) (list (simplify (rat-integrate-log f (rs-tower-x tw) rs-tv (integrate::int-all-real? f (rs-tower-x tw)))) 0))
        ((not (contains-sym? f (rs-top-theta tw))) (rs-int (rs-lower tw) f))
        ((equal? (rs-case tw) 'primitive) (rs-int-prim tw f))
        ((equal? (rs-case tw) 'tan) (rs-int-tan tw f))
        (else (rs-int-exp tw f))))

; ---------- запуск ----------
; Шаг 21k.6: финальное упрощение ответа после обратной подстановки: log(exp u) → u, log(exp(u)^k) → k·u (u вещественно: ответ
; Риша — вещественная первообразная на интервале), exp(log u) → u, exp(k·log u + …) → u^k·exp(…). Остальное — simplify (подобные).
(define (rs-split-log-factor t)               ; слагаемое показателя → (основание степень) для k·log u, иначе #f
  (cond ((and (pair? t) (equal? (car t) 'log) (= (length t) 2)) (list (cadr t) 1))
        ((and (pair? t) (equal? (car t) '*))
         (let ((ls (filter (lambda (f) (and (pair? f) (equal? (car f) 'log) (= (length f) 2))) (cdr t)))
               (os (filter (lambda (f) (not (and (pair? f) (equal? (car f) 'log) (= (length f) 2)))) (cdr t))))
           (and (= (length ls) 1) (pair? os) (list (cadr (car ls)) (simplify (cons '* os))))))
        (else #f)))

(define (rs-tidy-exp a)
  (let* ((ts (if (and (pair? a) (equal? (car a) '+)) (cdr a) (list a)))
         (lg (filter (lambda (t) (rs-split-log-factor t)) ts))
         (rest (filter (lambda (t) (not (rs-split-log-factor t))) ts)))
    (if (null? lg)
        (list 'exp a)
        (simplify (cons '* (append (map (lambda (t) (let ((p (rs-split-log-factor t))) (list '^ (car p) (cadr p)))) lg)
                                   (if (null? rest) '() (list (list 'exp (simplify (cons '+ rest)))))))))))

(define (rs-tidy-log a)
  (cond ((and (pair? a) (equal? (car a) 'exp) (= (length a) 2)) (cadr a))
        ((and (pair? a) (equal? (car a) '^) (= (length a) 3) (pair? (cadr a)) (equal? (car (cadr a)) 'exp) (= (length (cadr a)) 2))
         (simplify (list '* (caddr a) (cadr (cadr a)))))
        (else (list 'log a))))

(define (rs-tidy e)
  (if (not (pair? e))
      e
      (let ((args (map rs-tidy (cdr e))))
        (cond ((and (equal? (car e) 'log) (= (length args) 1)) (rs-tidy-log (car args)))
              ((and (equal? (car e) 'exp) (= (length args) 1)) (rs-tidy-exp (car args)))
              (else (cons (car e) args))))))

(define (rs-finish-plain e table x k)
  (simplify (rs-tidy (replace-expr (if (equal? k 0) (rs-back-subst e table) (rs-subst-tan-variant e table k))
                                   rs-tv (integrate::int-fresh-t e x)))))
; 21k″: башня с tan — из нескольких равных обратных подстановок (tan w; sin 2w/(1+cos 2w); (1−cos 2w)/sin 2w) берётся самая короткая
(define (rs-finish-expr e table x)
  (cond ((equal? e 0) 0)
        ((any? (lambda (en) (and (pair? (cadr en)) (equal? (car (cadr en)) 'tan))) table)
         (let* ((e1 (rs-tan-pre-tidy e table))
                (cs (map (lambda (k) (rs-finish-plain e1 table x k)) '(0 1 2))))
           (foldl (lambda (best c) (if (< (rs-size c) (rs-size best)) c best)) (car cs) (cdr cs))))
        (else (rs-finish-plain e table x 0))))

; R2.4: полевой сертификат — D(F) = f ТОЧНО в башне. Нужен для tan-ответов: int-check не сводит
; полуугловые формы (log cos x), хотя D(F) = f в поле проверяется алгебраически. Действует только
; при нулевом остатке и сбрасывается на каждом запуске.
(define rs-field-cert #f)

; (rs-solve e x) → (F R) в выражениях по x или #f; условия — в канал
(define (rs-solve e x)
  (let ((bt (rs-build-tower e x)))
    (and bt (not (equal? (rs-case (car bt)) 'base))
         (begin
           (set! rs-cur-table (caddr bt))
           (set! rs-field-cert #f)
           (if rs-log?
               (rs-note 'risch-tower "Алгоритм Риша: башня exp-log"
                        (string-append "башня: " (rs-tower-str (car bt))
                                       "; типы: " (rs-tower-types (car bt))
                                       "; структурная проверка: каждый Dθᵢ лежит в нижнем поле, связей между уровнями нет — "
                                       "система структурной теоремы Риша без решения, уровни трансцендентны"
                                       "; замены: " (rs-tower-subst (car bt)))
                        (integrate::int-form e x)
                        (subst (rs-theta-binds (car bt)) (cadr bt))))
           (let* ((res (rs-int (car bt) (cadr bt)))
                  (tls (if res
                           (filter (lambda (lv) (equal? (rs-level-kind lv) 'tan)) (rs-levels (car bt)))
                           '())))
             (and res
                  (begin
                    (set! rs-field-cert
                          (and (rs-zero? (cadr res))
                               (try (rs-zero? (list '- (rs-deriv (car bt) (car res)) (cadr bt)))
                                    (lambda (err) #f))))
                    ; R2.4 шаг 3: только для tan-башен — свёртка логов и переписка аргумента;
                    ; чисто логарифмические башни идут прежним путём (иначе регрессии лог-ответов)
                    (let* ((tb (caddr bt))
                           (F1 (if (pair? tls)
                                   (rs-lsum (foldl (lambda (acc en)
                                                     (if (and (pair? (cadr en)) (equal? (car (cadr en)) 'log))
                                                         (replace-expr acc (car en) (cadr en))
                                                         acc))
                                                   (car res) tb))
                                   (car res)))
                           (F2 (if (pair? tls)
                                   (rs-tan-cos-log F1 (car (car tls)) (rs-level-arg (car tls)))
                                   F1)))
                      (list (rs-finish-expr F2 tb x)
                            (rs-finish-expr (cadr res) tb x))))))))))

(define (rs-ne-known? e x) (any? (lambda (p) (and (equal? (car p) e) (equal? (cadr p) x))) rs-ne-table))
(define (rs-ne-add! e x)
  (let ((e2 (simplify e)))
    (if (not (rs-ne-known? e2 x))
        (set! rs-ne-table (take (cons (list e2 x) rs-ne-table) (min 64 (+ 1 (length rs-ne-table))))))))

(define (rs-replay cs) (map (lambda (c) (record-condition (car c) (cadr c))) cs))

(define rs-ne-reason "интеграл неэлементарен: алгоритм Риша (теорема Лиувилля) доказал, что первообразной в элементарных функциях нет")

; R = c·R′ с множителем c без x → (c R′): ответ F + c·(integrate R′ x), а не (integrate c·R′ x)
(define (rs-const-split R x)
  (if (and (pair? R) (equal? (car R) '*))
      (let ((cs (filter (lambda (f) (x-free? f x)) (cdr R))) (vs (filter (lambda (f) (not (x-free? f x))) (cdr R))))
        (if (or (null? cs) (null? vs))
            (list 1 R)
            (list (simplify (cons '* cs)) (simplify (cons '* vs)))))
      (list 1 R)))

; (rs-conclude e x F R) → ответ, либо #f (неэлементарно целиком или проверка не прошла)
(define (rs-conclude e x F R0)
  (let* ((cl (const-clean R0 x)) (R (car cl)))                          ; R4: остаток c·∫… с c = 0 — скрытый нуль
    (if (cadr cl) (set! rs-zero-unknown #t))
    (rs-conclude-1 e x F R)))
(define (rs-conclude-1 e x F R)
  (cond (rs-zero-unknown #f)                                            ; нуль константы не решён — ни ответа, ни «неэлементарно»
        ((equal? R 0)
         (let ((ok (or rs-field-cert (int-check F e x))))
           (and ok
                (begin
                  (if rs-log?
                      (rs-note 'risch-check "Алгоритм Риша: проверка первообразной"
                               (if rs-field-cert
                                   "D(F) = f — проверено точно в башне (полевой сертификат)"
                                   "D(F) = f — проверено дифференцированием и упрощением")
                               F e))
                  F))))
        ((equal? (simplify F) 0)
         (rs-ne-add! e x)
         (if rs-log?
             (rs-note 'risch-nonelementary "Алгоритм Риша: интеграл неэлементарен" rs-ne-reason
                      (integrate::int-form e x) 'неэлементарно)
             #f)
         #f)
        (else
         (let* ((Rs (simplify R)) (cs (rs-const-split Rs x)) (c (car cs)) (Rr (cadr cs)))
           (and (int-check F (simplify (list '+ e (list '* -1 Rs))) x)
                (begin
                  (rs-ne-add! Rs x)
                  (rs-ne-add! Rr x)
                  (rs-ne-add! e x)
                  (record-condition (list 'risch-nonelementary (list 'integrate Rr x))
                                    (string-append rs-ne-reason (rs-special-hint Rr x)))
                  (if rs-log?
                      (begin
                        (rs-note 'risch-check "Алгоритм Риша: проверка первообразной"
                                 "D(F) = f − R — проверено дифференцированием и упрощением"
                                 F (simplify (list '- e Rs)))
                        (rs-note 'risch-nonelementary "Алгоритм Риша: остаток неэлементарен" rs-ne-reason
                                 (integrate::int-form Rs x) 'неэлементарно))
                      #f)
                  (simplify (list '+ F (list '* c (list 'integrate Rr x))))))))))

; построение башни и весь расчёт — под capture-conditions: отказ ничего не оставляет в условиях; при результате условия переносятся
; R4: скрытые нули констант (log 6 − log 2 − log 3, √(3+2√2) − 1 − √2) убираются из входа const-clean; решение, в котором
; нуль константы остался unknown, не выдаётся (rs-zero-unknown): «не знаю», в таблицу неэлементарных не пишется.
(define (rs-run e x)
  (let* ((saved rs-zero-unknown)
         (cl (begin (set! rs-zero-unknown #f) (const-clean e x)))
         (e1 (car cl)))
    (if (cadr cl) (set! rs-zero-unknown #t))
    (let ((r (cond ((equal? e1 0) 0)
                   ((and (not (equal? e1 e)) (not (rs-has-kernel? e1 x)))
                    (let ((v (integrate e1 x))) (and (not (contains-sym? v 'integrate)) v)))
                   (else (rs-run-core e1 x)))))
      (let ((unk rs-zero-unknown))
        (set! rs-zero-unknown saved)
        (and r (not unk) r)))))

(define (rs-run-core e x)
  (let* ((cc (capture-conditions (lambda () (rs-solve e x)))) (r (car cc)))
    (and r (begin (rs-replay (cadr cc)) (rs-conclude e x (car r) (cadr r))))))

; стратегия каскада: последняя, только d = 0 и только если есть exp/log/степень с x в показателе
(define (int-risch e x d)
  (and (= d 0) (equal? (algorithm 'risch) 'on) (rs-has-kernel? e x) (not (rs-hyp-log? e))
       (with-step ('risch "Алгоритм Риша" (integrate::int-form e x)
                   :comment "подынтегральная функция переписывается в башне exp-log, затем редукция Эрмита, логарифмическая и многочленная части"
                   :after integrate::int-p)
         (begin
           (set! rs-log? (step-log-enabled?))
           (set! rs-notes '())
           (set! rs-tan-used #f)
           (set! rs-ne-reason-last #f)
           (let ((r (call-quietly (lambda () (rs-run e x)))))
             (set! rs-log? #f)
             (if (and r rs-tan-used) (set! rs-tan-flag #t))
             (if r (rs-flush-notes!))
             (if (not r)
                 (begin
                   (if (rs-ne-known? (simplify e) x) (rs-note-refusal e x))
                   (attempt-fail (if (rs-ne-known? (simplify e) x)
                                     "доказано: интеграл неэлементарен"
                                     "Риш не решил: не знаю"))))
             r)))))

(int-add-strategy int-risch)

; Шаг 21k.6: предпроверка на верхнем уровне integrate — ДОКАЗАННО неэлементарное не гонять по всему каскаду (прежние стратегии
; перебирают подстановки/по частям: log x/(a x² + b x³ + c x⁴) — 92 с, Риш — 0.3 с). #t только при полном доказательстве (F = 0,
; запись в rs-ne-table); во всех прочих исходах (ответ, частичный, «не знаю») каскад идёт как раньше, ответы прежних стратегий
; не меняются. Журнал и условия предпроверки отбрасываются.
; (21k.7b) Частичные решения RDE: интеграл, который без них был бы «неэлементарен целиком», теперь получает частичный ответ
; (∫eˣ/x² = −eˣ/x + ∫eˣ/x). Чтобы каскад для таких по-прежнему не гонялся, предпроверка идёт без частичных решений; при
; полном доказательстве — второй запуск с ними: частичный ответ возвращается сразу (int-antiderivative), иначе #t.
(define (rs-run-partials e x on?)
  (let ((old rs-rde-partials?))
    (set! rs-rde-partials? on?)
    (unwind-protect (rs-run e x) (set! rs-rde-partials? old))))
; R2.4: порядок каскада — если в подынтегральном есть log и тригонометрия, а предпроверка нашла ПОЛНЫЙ
; ответ (без невычисленных интегралов), отдаём его сразу: иначе int-parts/int-expand тянут такие формы
; минутами (H2 = eˣ·log cos x − eˣ·tan x: 265 с → доли секунды). Остальные классы — как раньше.
(define (rs-has-log-fn? e)
  (and (pair? e) (or (equal? (car e) 'log) (any? rs-has-log-fn? (cdr e)))))
; sech/csch от логарифма: башня превращает их в рациональную функцию от exp(b·log u),
; и доказательство неэлементарности срабатывает ложно (rubi t_6_5_3/190, t_6_6_3/163,
; первообразная там элементарна: atan/atanh от степени x). Честный ответ — «не знаю».
(define (rs-hyp-log? e)
  (and (pair? e)
       (or (and (member? (car e) '(sech csch)) (pair? (cadr e)) (rs-has-log-fn? (cadr e)))
           ; int-norm переписывает sech/csch в cosh^(-1)/sinh^(-1)
           (and (equal? (car e) '^) (= (length e) 3) (pair? (cadr e))
                (member? (car (cadr e)) '(cosh sinh)) (rs-has-log-fn? (cadr (cadr e))))
           (any? rs-hyp-log? (cdr e)))))
(define (rs-precheck-ne e x)
  (and (equal? (algorithm 'risch) 'on) (rs-has-kernel? e x) (not (rs-hyp-log? e))
       ; 21k″: чисто тригонометрическое — только последней стратегией (каскад быстр, предпроверка удвоила бы работу);
       ; смесь тригонометрии с exp/log/atan — предпроверка нужна: каскад на eˣ·tan x идёт ≈ 4 мин, Риш доказывает за 0.2 с
       (or (null? (rs-trig-apps e x)) (rs-has-nontrig-kernel? e x))
       (begin
         (set! rs-log? #f)
         (let* ((cc (capture-conditions (lambda () (call-quietly (lambda () (rs-run-partials e x #f))))))
                (r (car cc)))
           (cond ((and r (not (contains-sym? r 'integrate))
                       (rs-has-log-fn? e) (pair? (rs-trig-apps e x)))
                  ; ответ отдаём только сертифицированным: полуугловая форма H2 int-check не проходит,
                  ; тогда работает прежний каскад (чистую форму даёт другая стратегия)
                  (let ((F (integrate::int-final (integrate::int-tidy (simplify r) x) e x)))
                    (and (int-check F e x)
                         (begin (rs-replay (cadr cc)) F))))
                 ((rs-ne-known? (simplify e) x)
                  (or (and rs-rde-partials? (rs-precheck-partial e x)) #t))
                 (else #f))))))

; частичный ответ при полном доказательстве: прямой запуск int-risch (журнал шагов и условия — как у стратегии каскада)
(define (rs-precheck-partial e x)
  (let ((r (int-risch e x 0)))
    (and r (contains-sym? r 'integrate) r)))

; ---------- публичные функции ----------
; (risch-integrate e x) → первообразная F либо F + (integrate R x) (R доказанно неэлементарен), либо #f — «не знаю»/неэлементарно целиком
; ST.3д: при включённом журнале пишутся шаги башни, Эрмита, резольвенты и проверки (ответы те же)
(define (risch-integrate e x)
  (set! rs-log? #f)
  (let ((en (integrate::int-norm e)))
    (if (rs-hyp-log? en)
        #f   ; sech/csch от логарифма: доказательство неэлементарности здесь ложно
        (if (step-log-enabled?)
        (let ((res (with-step ('risch "Алгоритм Риша" (integrate::int-form en x)
                              :comment "подынтегральная функция переписывается в башне exp-log, затем редукция Эрмита, логарифмическая и многочленная части"
                              :after integrate::int-p)
                     (begin
                       (set! rs-log? #t)
                       (set! rs-notes '())
                       (set! rs-tan-used #f)
                       (set! rs-ne-reason-last #f)
                       (let ((r (call-quietly (lambda () (int-guard (lambda () (rs-run en x)))))))
                         (set! rs-log? #f)
                         (if (and r rs-tan-used) (set! rs-tan-flag #t))
                         (if r (rs-flush-notes!))
                         r)))))
          (if (and (not res) (rs-ne-known? (simplify en) x))
              (rs-note-refusal en x)
              res))
        (int-guard (lambda () (rs-run en x)))))))

; (risch-nonelementary? e x) → #t: доказано, что элементарной первообразной нет (в том числе при частичном ответе);
; #f: найдена элементарная первообразная; unknown: алгоритм не решил
(define (risch-nonelementary? e x)
  (let ((n (integrate::int-norm e)))
    (cond ((rs-ne-known? n x) #t)
          (else
           (let ((r (risch-integrate n x)))
             (cond ((rs-ne-known? n x) #t)
                   (r (if (contains-sym? r 'integrate) #t #f))
                   (else 'unknown)))))))
