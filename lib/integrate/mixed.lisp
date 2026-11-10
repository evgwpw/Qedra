; mixed.lisp — смешанный случай Риша: радикал над башней exp/log (шаг R3.1)
; Подстановка θ → t (θ = e^{ax} | log(ax+b)): ∫f dx = ∫g dt. Если g x-free (нет x, exp, log), g ∈ ℚ(t)(y) —
; алгебраический случай в t (A3–A5; гладкие коники рода 0 — int-genus0-conic); ответ — обратной подстановкой t = θ(x)
; и проверкой gn-ok? по исходному f; отказ A4/A5 для g переносится на f по лемме §1.3 — только через чекер
; mx-transfer-ne! (флаги: g x-free, константы ℚ, доказанный внутренний вердикт; плюс численная проверка отображения).
; θ = x^{1/n} (root): x = tⁿ делает башню чисто трансцендентной над ℚ(t) — Риш по t, вердикт тем же чекером.
; R3.2: g не x-free (x·√(eˣ+1), log x/√(1+log x)) либо радикал от x под башней (eˣ√(x+1)): кривая рода 0 рационализуется
; (gn-param, параметр 't), log t и eᵗ остаются башней над ℚ(s) — Риш по s (mx-risch); ответ — обратной подстановкой
; s = inv(t, y); вердикт — тем же чекером (флаг «доказано» — таблица Риша, с разбором знака аргументов логарифмов:
; log(1−s²) = log(s²−1) + L, L — константа вида iπ). Бюджет времени mx-time-limit: исчерпан — #f, ответ не подменяется.
(module integrate)

(define mx-v '%t)           ; переменная θ-подстановки
(define mx-refused #f)      ; доказанный отказ: ответ #f, но рамка шагов mx-integration остаётся
(define mx-why "")          ; его причина
(define mx-busy #f)         ; защита от вложенного входа (внутренний integrate)
(define mx-max-size 400)    ; гейт размера подынтегрального для Риша в s
(define mx-time-limit 10)   ; секунд на Риш в s (включая доказательство вердикта)

; ---------- нормализация и атомы ----------

(define (mx-exp? z) (and (pair? z) (equal? (car z) 'exp) (= (length z) 2)))
(define (mx-log? z) (and (pair? z) (equal? (car z) 'log) (= (length z) 2)))

; sinh/cosh/tanh → exp; √(e^u), (e^u)^r → e^{u/2}, e^{r u}
(define (mx-norm1 e)
  (if (not (pair? e))
      e
      (let ((h (car e)) (as (map mx-norm1 (cdr e))))
        (cond ((and (equal? h 'sinh) (= (length as) 1))
               (list '* 1/2 (list '+ (list 'exp (car as)) (list '* -1 (list 'exp (list '* -1 (car as)))))))
              ((and (equal? h 'cosh) (= (length as) 1))
               (list '* 1/2 (list '+ (list 'exp (car as)) (list 'exp (list '* -1 (car as))))))
              ((and (equal? h 'tanh) (= (length as) 1))
               (let ((t2 (list 'exp (list '* 2 (car as)))))
                 (list '* (list '+ t2 -1) (list '^ (list '+ t2 1) -1))))
              ((and (equal? h 'sqrt) (= (length as) 1) (mx-exp? (car as)))
               (list 'exp (list '* 1/2 (cadr (car as)))))
              ((and (equal? h '^) (= (length as) 2) (mx-exp? (car as)) (number? (cadr as)))
               (list 'exp (list '* (cadr as) (cadr (car as)))))
              (else (cons h as))))))

(define (mx-norm e) (simplify (mx-norm1 e)))

(define (mx-frac? p) (and (number? p) (rational-number? p) (not (integer? p))))

; (mx-kernels e x) → список (вид узел): exp, log, root (x^{p/q}), rad (P^{k/q}, P ≠ x), other
(define (mx-kernels e x)
  (cond ((not (pair? e)) '())
        ((not (contains-sym? e x)) '())
        (else
         (let ((h (car e)))
           (cond ((mx-exp? e) (cons (list 'exp e) (mx-kernels (cadr e) x)))
                 ((mx-log? e) (cons (list 'log e) (mx-kernels (cadr e) x)))
                 ((and (equal? h 'sqrt) (= (length e) 2))
                  (cons (list (if (equal? (cadr e) x) 'root 'rad) (list '^ (cadr e) 1/2))
                        (mx-kernels (cadr e) x)))
                 ((and (equal? h '^) (= (length e) 3))
                  (let ((b (cadr e)) (p (caddr e)))
                    (cond ((and (number? p) (integer? p)) (mx-kernels b x))
                          ((mx-frac? p)
                           (cons (list (if (equal? b x) 'root 'rad) e) (mx-kernels b x)))
                          (else (list (list 'other e))))))
                 ((or (equal? h '+) (equal? h '*))
                  (append-map (lambda (a) (mx-kernels a x)) (cdr e)))
                 (else (list (list 'other e))))))))

(define (mx-of-kind ks k) (map cadr (filter (lambda (p) (equal? (car p) k)) ks)))

(define (mx-has-head? e hs)
  (and (pair? e) (or (member? (car e) hs) (any? (lambda (a) (mx-has-head? a hs)) (cdr e)))))

; листья — символы из vs или точные рациональные; головы — + * ^ sqrt exp log;
; дробная степень — только от выражения с переменной (√2 и т. п. — константа вне ℚ)
(define (mx-leaves-ok? e vs)
  (cond ((symbol? e) (member? e vs))
        ((number? e) (rational-number? e))
        ((pair? e)
         (and (member? (car e) '(+ * ^ sqrt exp log))
              (every? (lambda (a) (mx-leaves-ok? a vs)) (cdr e))
              (or (not (equal? (car e) 'sqrt)) (not (mx-leaves-ok? (cadr e) '())))
              (or (not (equal? (car e) '^)) (not (mx-frac? (caddr e)))
                  (not (mx-leaves-ok? (cadr e) '())))))
        (else #f)))

; ---------- θ-подстановка (§1.1) ----------
; th = (kind θ inv dxdt a): kind exp — θ = e^{a x}, x = log(t)/a, dx/dt = 1/(a t), e^{aᵢx+bᵢ} → e^{bᵢ}·t^{aᵢ/a};
; kind log — θ = log(a x + b), x = (eᵗ − b)/a, dx/dt = eᵗ/a; kind root — θ = x^{1/n}, x = tⁿ, dx/dt = n t^{n−1}

(define (mx-qgcd a b)
  (let ((g (gcd (* (numer a) (denom b)) (* (numer b) (denom a)))))
    (/ (if (< g 0) (- g) g) (* (denom a) (denom b)))))

(define (mx-lin-ab u x)
  (let ((a (int-slope u x)))
    (and a (number? a) (rational-number? a)
         (let ((b (simplify (subst (list x 0) u))))
           (and (number? b) (rational-number? b)
                (equal? (simplify (list '- u (list '+ (list '* a x) b))) 0)
                (list a b))))))

(define (mx-theta-exp exps x)
  (let ((ls (map (lambda (z) (mx-lin-ab (cadr z) x)) exps)))
    (and (every? (lambda (p) p) ls)
         (let ((a (foldl (lambda (acc p) (mx-qgcd acc (car p))) (car (car ls)) (cdr ls))))
           (list 'exp (simplify (list 'exp (list '* a x)))
                 (simplify (list '* (/ 1 a) (list 'log mx-v)))
                 (simplify (list '/ 1 (list '* a mx-v)))
                 a)))))

(define (mx-theta-log logs x)
  (let ((ls (int-dedupe logs)))
    (and (= (length ls) 1)
         (let ((ab (mx-lin-ab (cadr (car ls)) x)))
           (and ab
                (let ((a (car ab)) (b (cadr ab)))
                  (list 'log (car ls)
                        (simplify (list '* (/ 1 a) (list '+ (list 'exp mx-v) (- b))))
                        (simplify (list '* (/ 1 a) (list 'exp mx-v)))
                        a)))))))

(define (mx-theta-root roots x)
  (let ((n (foldl (lambda (acc z) (lcm acc (denom (caddr z)))) 1 roots)))
    (list 'root (simplify (list '^ x (/ 1 n))) (list '^ mx-v n)
          (simplify (list '* n (list '^ mx-v (- n 1)))) n)))

(define (mx-th-kind th) (nth th 0))
(define (mx-th-theta th) (nth th 1))
(define (mx-th-inv th) (nth th 2))
(define (mx-th-dxdt th) (nth th 3))
(define (mx-th-a th) (nth th 4))

; (mx-sub e x th): атомы → степени t (e^{b} — постоянный множитель), голый x → inv(t)
(define (mx-sub e x th)
  (cond ((equal? e x) (mx-th-inv th))
        ((not (pair? e)) e)
        ((not (contains-sym? e x)) e)
        ((and (equal? (mx-th-kind th) 'exp) (mx-exp? e))
         (let ((ab (mx-lin-ab (cadr e) x)))
           (list '* (list 'exp (cadr ab)) (list '^ mx-v (/ (car ab) (mx-th-a th))))))
        ((and (equal? (mx-th-kind th) 'log) (equal? e (mx-th-theta th))) mx-v)
        ((and (equal? (mx-th-kind th) 'root) (equal? (car e) '^) (equal? (cadr e) x) (mx-frac? (caddr e)))
         (list '^ mx-v (* (caddr e) (mx-th-a th))))
        ((and (equal? (mx-th-kind th) 'root) (equal? (car e) 'sqrt) (equal? (cadr e) x))
         (list '^ mx-v (* 1/2 (mx-th-a th))))
        (else (cons (car e) (map (lambda (z) (mx-sub z x th)) (cdr e))))))

; (mx-substitute e x th) → (g . x-free?): g = f(inv(t))·dx/dt; x-free — в g нет x, exp, log от t (g ∈ k(t)(y))
(define (mx-substitute e x th)
  (let ((g (int-norm (simplify (together (list '* (mx-sub e x th) (mx-th-dxdt th)))))))
    (cons g (and (not (contains-sym? g x))
                 (not (mx-has-head? (cdr (mx-const-split g mx-v)) '(exp log)))))))

; g = c·g₁: c — произведение множителей без v (e^{b}, числа), g₁ — остальное → (c . g₁)
(define (mx-const-split g v)
  (if (and (pair? g) (equal? (car g) '*))
      (let ((cs (filter (lambda (f) (not (contains-sym? f v))) (cdr g)))
            (vs (filter (lambda (f) (contains-sym? f v)) (cdr g))))
        (cons (simplify (cons '* (cons 1 cs))) (simplify (cons '* (cons 1 vs)))))
      (cons 1 g)))

; план: (theta e1 th) | (root e1 th) | #f
(define (mx-plan e x)
  (let* ((e1 (mx-norm e)) (ks (mx-kernels e1 x))
         (exps (mx-of-kind ks 'exp)) (logs (mx-of-kind ks 'log))
         (roots (mx-of-kind ks 'root)) (rads (mx-of-kind ks 'rad)))
    (cond ((pair? (mx-of-kind ks 'other)) #f)
          ((not (mx-leaves-ok? e1 (list x))) #f)            ; символьные параметры, √2, pi — не наш случай
          ((and (null? exps) (null? logs)) #f)               ; чисто алгебраическое — прежние стратегии
          ((and (null? rads) (null? roots)) #f)              ; без радикала — Риш
          ((and (pair? roots) (null? rads)) (list 'root e1 (mx-theta-root roots x)))
          ((pair? roots) #f)
          ; вариант A (R3.2): основания радикалов — многочлены от x без атомов; кривая рода 0 по x
          ((every? (lambda (r) (not (mx-has-head? (cadr r) '(exp log)))) rads) (list 'curve e1))
          ; вариант B: основания всех радикалов — от θ
          ((every? (lambda (r) (mx-has-head? (cadr r) '(exp log))) rads)
           (let ((th (cond ((null? logs) (mx-theta-exp exps x))
                           ((null? exps) (mx-theta-log logs x))
                           (else #f))))
             (and th (list 'theta e1 th))))
          (else #f))))

; ---------- перенос вердикта (лемма §1.3) — отдельный чекер ----------
; (mx-transfer-ne! e x c g v sx kind iv conds) → #t (условие записано) | #f.
; e — исходное по x; c·g — внутреннее по v (c — постоянный множитель, e^{b} и т. п.); sx — v как функция x;
; kind: alg (A4/A5 в ℚ(v)(y), прогон по переменной iv) | risch (Риш над ℚ(v)); conds — условия внутреннего прогона.
; Флаги: (a) g x-free (для alg — и без exp/log); (b) константы ℚ в e и g, c — ненулевая константа;
; (c) внутренний вердикт — доказательство для ровно этой формы g; плюс численная проверка отображения
; e(x₀) = c·g(sx(x₀))·sx′(x₀) — ловит подменённую подстановку и спрятанный x.
(define (mx-flag-xfree? g v x kind)
  (and (not (equal? v x)) (not (contains-sym? g x))
       (or (equal? kind 'risch) (not (mx-has-head? g '(exp log))))))

(define (mx-flag-consts? e x c g v)
  (and (mx-leaves-ok? e (list x)) (mx-leaves-ok? g (list v))
       (not (contains-sym? c x)) (not (contains-sym? c v))
       (equal? (const-zero? c) #f)))                         ; c ≠ 0 — доказано (R4), не «unknown»

(define (mx-flag-proved? g v kind iv conds)
  (cond ((equal? kind 'alg)
         ; внутренний прогон шёл по переменной iv (алгебраический код надёжен только по x)
         (let ((key (list 'risch-nonelementary (int-unevaluated (int-norm (subst (list v iv) g)) iv '()))))
           (any? (lambda (cd) (equal? (car cd) key)) conds)))
        ((equal? kind 'risch)
         (and (equal? iv v) (mx-risch-proved? g v)))
        (else #f)))

(define (mx-map-ok? e x c g v sx)
  (let ((dsx (diff x sx)))
    (let loop ((xs (list 1/3 3/4 7/5 2 5 11 -1/3 -3/4 -7/5 -2 -5)) (n 0))
      (if (null? xs)
          (>= n 2)
          (let* ((x0 (car xs))
                 (ev (gn-real-num (subst (list x x0) e)))
                 (s0 (gn-real-num (subst (list x x0) sx)))
                 (d0 (gn-real-num (subst (list x x0) dsx)))
                 (gv (and s0 (gn-real-num (list '* c (subst (list v s0) g))))))
            (if (and ev d0 gv)
                (if (< (abs (- ev (* gv d0))) (* 1e-7 (+ 1 (abs ev))))
                    (loop (cdr xs) (+ n 1))
                    #f)
                (loop (cdr xs) n)))))))

(define (mx-transfer-ne! e x c g v sx kind iv conds)
  (and (mx-flag-xfree? g v x kind)
       (mx-flag-consts? e x c g v)
       (mx-flag-proved? g v kind iv conds)
       (mx-map-ok? e x c g v sx)
       (begin
         (set! mx-refused #t)
         (set! mx-why (string-append "интеграл по t (t = " (alg-mp sx) ") неэлементарен (внутренний вердикт: "
                                     (if (equal? kind 'alg) "алгебраический Трагер" "алгоритм Риша")
                                     "), по лемме Розенлихта исходной первообразной тоже нет"))
         (alg-step 'mx-transfer "Перенос отказа на исходный интеграл"
                   (string-append "флаги: g без x, константы в ℚ, внутренний вердикт доказан, отображение проверено численно; " mx-why)
                   (int-form (subst (list v 't) g) 't) 'nonelementary)
         (record-condition
          (list 'risch-nonelementary (int-unevaluated e x '()))
          (string-append "смешанный случай (R3, перенос вердикта): подстановка t = " (to-string sx)
                         ", ∫ сведён к " (if (equal? c 1) "" (string-append (to-string c) "·"))
                         "∫ " (to-string (subst (list v 't) g)) " dt"
                         (if (equal? kind 'alg)
                             "; внутренний вердикт — алгебраический (A4/A5) в поле ℚ(t, y)"
                             "; внутренний вердикт — алгоритм Риша над ℚ(t) (R3.2: после рационализации кривой рода 0, либо x = tⁿ)")
                         "; x-free, константы ℚ, отображение проверено — элементарной первообразной нет (Розенлихт)"))
         #t)))

; ---------- внутреннее интегрирование ----------

(define (mx-ok ans e x)
  (and ans (not (contains-sym? ans 'integrate)) (gn-ok? ans e x) ans))

(define (mx-note! sx)
  (record-condition (list 'mixed-substitution sx)
                    "смешанный случай: подстановка t = θ(x), интеграл по t; ответ проверен дифференцированием"))

; g x-free — алгебраический случай в t; внутренний прогон — по переменной x (алгебраический код
; A4/A5 надёжен только по x: по другой переменной вердикт A5 теряется)
(define (mx-alg e x g th)
  (let* ((cg (mx-const-split g mx-v)) (c (car cg)) (g1 (cdr cg))
         (gx (int-norm (subst (list mx-v 'x) g1)))
         ; таблица (короткие формы: asinh-логарифм), затем гладкая коника — сразу параметризацией
         ; (каскад до неё ≈ 2 с), затем весь каскад с A4/A5
         (saved-notes alg-notes)
         (cc (capture-conditions (lambda () (or (int-table-try int-table gx 'x)
                                                (int-genus0-conic gx 'x 0)
                                                (int-go gx 'x 0)))))
         ; шаги внутреннего прогона (там переменная t названа x) в журнал не идут: интеграл по t показывает mx-transformed
         (dropped (set! alg-notes saved-notes))
         (G (car cc)))
    (cond (G
           (let ((ans (try (simplify (list '* c (subst (list 'x (mx-th-theta th)) G))) (lambda (err) #f))))
             (alg-step 'mx-transformed "Интеграл по t"
                       "g(t) — алгебраическая функция от t без x: интегрируем алгебраическим путём (кривая рода 0 или Эрмит–Трагер)"
                       (int-form (subst (list mx-v 't) g1) 't) (subst (list 'x 't) G))
             (and (mx-ok ans e x)
                  (begin
                    (alg-step 'mx-back-substitution "Обратная подстановка и проверка"
                              (string-append "t = " (alg-mp (mx-th-theta th)) "; производная ответа совпадает с подынтегральной функцией")
                              (subst (list 'x 't) G) ans)
                    (mx-note! (mx-th-theta th))
                    ans))))
          ((mx-leaves-ok? g1 (list mx-v))
           (begin (mx-transfer-ne! e x c g1 mx-v (mx-th-theta th) 'alg 'x (cadr cc)) #f))
          (else #f))))

; root: g ∈ ℚ(t)-башня exp/log без радикалов — Риш по t
(define (mx-risch-root e x g th)
  (and (null? (gn-rad-nodes g))
       (let* ((cc (capture-conditions (lambda () (risch-integrate g mx-v))))
              (G (car cc)))
         (if (and G (not (contains-sym? G 'integrate)))
             (let ((ans (try (simplify (subst (list mx-v (mx-th-theta th)) G)) (lambda (err) #f))))
               (alg-step 'mx-transformed "Интеграл по t"
                         "g(t) — функция башни exp/log от t без радикалов: алгоритм Риша по t"
                         (int-form (subst (list mx-v 't) g) 't) (subst (list mx-v 't) G))
               (and (mx-ok ans e x)
                    (begin
                      (alg-step 'mx-back-substitution "Обратная подстановка и проверка"
                                (string-append "t = " (alg-mp (mx-th-theta th)) "; производная ответа совпадает с подынтегральной функцией")
                                (subst (list mx-v 't) G) ans)
                      (mx-note! (mx-th-theta th))
                      ans)))
             (begin (mx-transfer-ne! e x 1 g mx-v (mx-th-theta th) 'risch mx-v (cadr cc)) #f)))))

; ---------- R3.2: рационализация кривой рода 0 и Риш по параметру ----------

; P = a·v + b (a, b ∈ ℚ): y^q = P — v = (s^q − b)/a, y = s (главная ветвь, обратная s = y): самая короткая параметризация
; (пучок через точку из gn-param даёт громоздкие аргументы логарифмов, на которых Риш отказывает) → (xt yt inv mode) | #f
(define (mx-linear-param P q v)
  (let ((pe (expand P)))
    (and (polynomial? pe v) (equal? (try (degree pe v) (lambda (e) #f)) 1)
         (let ((a (coeff pe v 1)) (b (coeff pe v 0)))
           (and (number? a) (rational-number? a) (not (= a 0)) (number? b) (rational-number? b)
                (list (simplify (list '* (/ 1 a) (list '+ (list '^ 't q) (- b)))) 't 'y 'principal))))))

; (mx-rationalize g v sx) → (gs w sxs) | #f: g по v (θ, x^{1/n} или сам x) с exp/log; радикал (если есть) — кривая
; y^q = P(v) рода 0 (коника или кратный корень; gn-param: x = xt(s), y = yt(s), обратная s = inv(v, y)) → параметр
; w = 't, gs = g(xt, yt)·xt′ — рациональная по s с башней log/exp над ℚ(s); sxs — w как функция x (sx — v как функция x).
(define (mx-rationalize g v sx)
  (if (null? (gn-rad-nodes g))
      (list g v sx)
      (let ((sr (gn-single-radical g)))
        (and sr
             (let ((P (car sr)) (q (cadr sr)))
               (and (polynomial? P v) (not (mx-has-head? P '(exp log)))
                    (let ((pp (or (mx-linear-param P q v)
                                  (and (or (gn-repeated? P v) (gn-conic? P q v)) (gn-param P q v)))))
                      (and pp
                           (let* ((xt (nth pp 0)) (yt (nth pp 1)) (inv (nth pp 2))
                                  (gs (int-norm (simplify (together (list '* (gn-subst g v xt P q yt)
                                                                         (diff 't xt))))))
                                  (u (list '^ P (/ 1 q)))
                                  (sxs (simplify (subst (list v sx) (subst (list 'y u) inv)))))
                             (and (not (contains-sym? gs 'y)) (not (contains-sym? gs v))
                                  (list gs 't sxs)))))))))))

; ---------- знак аргументов логарифмов ----------
; Риш раскладывает log N на множители; при lc(N) < 0 появляется константа log(−1), на которой лог-часть отказывает
; (∫log(1−s²)/(s²−1) — «не знаю», ∫log(s²−1)/(s²−1) — доказано). (mx-log-sign-split g w) → (g0 h): каждый log(N/D)
; заменён на log(±N) − log(±D) со старшими коэффициентами > 0 плюс k·L (L = %L — константа вида iπ, не из ℚ),
; g = g0 + L·h. Вердикт: ∫g0 неэлементарен (доказано Ришем) и ∫h элементарен ⇒ ∫g неэлементарен (иначе
; ∫g0 = ∫g − L∫h элементарен над ℚ(L); доказательство для g0 не использует L — оно над ℚ(s), а Розенлихт-Лиувилль
; сохраняется при расширении констант). Ответ — только если L не входит (h = 0): g0 и g — одна функция.
(define (mx-lc p w)
  (let ((pe (expand p)))
    (try (coeff pe w (degree pe w)) (lambda (err) #f))))

(define (mx-pos-log a w)
  (let* ((tg (together a)) (N (numer tg)) (D (denom tg))
         (lN (mx-lc N w)) (lD (mx-lc D w)))
    (and (number? lN) (number? lD)
         (list (list '+ (list 'log (if (< lN 0) (list '* -1 N) N))
                     (list '* -1 (list 'log (if (< lD 0) (list '* -1 D) D))))
               (- (if (< lN 0) 1 0) (if (< lD 0) 1 0))))))

(define (mx-log-sign-walk e w)
  (cond ((not (pair? e)) e)
        ((and (mx-log? e) (contains-sym? (cadr e) w))
         (let ((r (mx-pos-log (cadr e) w)))
           (if r (list '+ (car r) (list '* (cadr r) '%L)) e)))
        (else (cons (car e) (map (lambda (z) (mx-log-sign-walk z w)) (cdr e))))))

(define (mx-log-sign-split g w)
  (let ((gl (mx-log-sign-walk g w)))
    (list (int-norm (simplify (subst (list '%L 0) gl)))
          (simplify (together (diff '%L gl))))))

; ∫h элементарен: ответ без невычисленных интегралов и с int-check (h без x — переименование w → x)
(define (mx-elementary? h w)
  (or (equal? h 0)
      (let* ((hx (subst (list w 'x) h))
             (H (try (integrate hx 'x) (lambda (err) #f))))
        (and H (not (contains-sym? H 'integrate)) (int-check H hx 'x)))))

; доказательство Риша для g по w: прямо (таблица rs-ne) или через расщепление знака логарифмов
(define (mx-risch-proved? g w)
  (or (and (risch::rs-ne-known? (simplify (int-norm g)) w) #t)
      (let* ((sp (mx-log-sign-split g w)) (g0 (car sp)) (h (cadr sp)))
        (and (not (contains-sym? h '%L))
             (risch::rs-ne-known? (simplify (int-norm g0)) w)
             (mx-elementary? h w)))))

; (mx-risch-split-run gs w) → (G . conds)|#f: после отказа на g — Риш для g0 (прогон заполняет таблицу rs-ne)
; и, если L не входит (h = 0) — ответ для g0 (g0 = g как функции)
(define (mx-risch-split-run gs w)
  (let* ((sp (mx-log-sign-split gs w)) (g0 (car sp)) (h (cadr sp)))
    (if (equal? g0 (int-norm gs))
        #f
        (let ((cc (capture-conditions (lambda () (risch-integrate g0 w)))))
          (if (and (car cc) (equal? h 0) (not (contains-sym? (car cc) 'integrate)))
              cc
              #f)))))

; слияние логарифмов с одинаковым множителем: r·log A + r·log B → r·log(A·B) (после обратной подстановки
; log(√u−1) + log(√u+1) = log(u−1) и т. п.); результат — кандидат, проверяется как любой ответ
(define (mx-log-term t)
  (cond ((mx-log? t) (cons 1 (cadr t)))
        ((and (pair? t) (equal? (car t) '*))
         (let ((ls (filter mx-log? (cdr t))))
           (and (= (length ls) 1)
                (cons (simplify (cons '* (filter (lambda (z) (not (mx-log? z))) (cdr t)))) (cadr (car ls))))))
        (else #f)))

; log(e^u) → u (вещественная ось)
(define (mx-log-exp e)
  (cond ((not (pair? e)) e)
        ((and (mx-log? e) (mx-exp? (cadr e))) (cadr (cadr e)))
        (else (cons (car e) (map mx-log-exp (cdr e))))))

(define (mx-merge-logs ans)
  (if (and (pair? ans) (equal? (car ans) '+))
      (simplify (mx-log-exp (mx-merge-logs1 ans)))
      (let ((ex (expand ans)))
        (if (and (pair? ex) (equal? (car ex) '+)) (mx-merge-logs ex) ans))))

(define (mx-merge-logs1 ans)
  (if (and (pair? ans) (equal? (car ans) '+))
      (let loop ((ts (cdr ans)) (groups '()) (rest '()))
        (if (null? ts)
            (simplify
             (cons '+ (append rest
                              (map (lambda (g)
                                     (list '* (car g)
                                           (list 'log (if (= (length (cdr g)) 1)
                                                          (cadr g)
                                                          (simplify (expand (cons '* (cdr g))))))))
                                   (reverse groups)))))
            (let ((p (mx-log-term (car ts))))
              (if (not p)
                  (loop (cdr ts) groups (append rest (list (car ts))))
                  (let ((g (assoc (car p) groups)))
                    (loop (cdr ts)
                          (if g
                              (map (lambda (h) (if (equal? (car h) (car p)) (append h (list (cdr p))) h)) groups)
                              (cons (list (car p) (cdr p)) groups))
                          rest))))))
      ans))

; (mx-risch e x c g v sx): c·g по v → рационализация → Риш по w → обратная подстановка | вердикт | #f
(define (mx-risch-run e x c g v sx)
  (let ((rz (mx-rationalize g v sx)))
    (and rz (<= (int-size (car rz)) mx-max-size)
         (let* ((gs (car rz)) (w (cadr rz)) (sxs (caddr rz))
                (rz-note (alg-step 'mx-rationalization "Рационализация кривой рода 0"
                                   (string-append "параметр w = " (alg-mp sxs) ": радикал исчезает, log t и eᵗ остаются башней над ℚ(w) — Риш по w")
                                   (if (equal? v x) (int-form g x) (int-form (subst (list v 't) g) 't))
                                   (int-form gs w)))
                (cc (capture-conditions (lambda () (risch-integrate gs w))))
                (cc (if (and (car cc) (not (contains-sym? (car cc) 'integrate)))
                        cc
                        (or (mx-risch-split-run gs w) cc)))
                (G (car cc)))
           (if (and G (not (contains-sym? G 'integrate)))
               (let* ((ans0 (try (simplify (list '* c (subst (list w sxs) G))) (lambda (err) #f)))
                      (ansm (and ans0 (try (mx-merge-logs ans0) (lambda (err) #f))))
                      (ans (if (and ansm (not (equal? ansm ans0)) (mx-ok ansm e x)) ansm ans0)))
                 (and (mx-ok ans e x)
                      (begin
                        (alg-step 'mx-back-substitution "Обратная подстановка и проверка"
                                  (string-append "w = " (alg-mp sxs) "; производная ответа совпадает с подынтегральной функцией")
                                  (subst (list w 't) G) ans)
                        (record-condition (list 'mixed-substitution sxs)
                                          "смешанный случай: рационализация кривой рода 0 и алгоритм Риша по параметру; ответ проверен дифференцированием")
                        ans)))
               (begin
                 (mx-transfer-ne! e x c gs w sxs 'risch w (cadr cc))   ; таблица rs-ne заполнена прогонами выше
                 #f))))))

(define (mx-risch e x c g v sx)
  (let ((r (call-with-time-limit mx-time-limit (lambda () (mx-risch-run e x c g v sx)))))
    (if (equal? (car r) 'ok)
        (cadr r)
        (begin
          (record-condition (list 'timeout 'mixed mx-time-limit)
                            (string-append "смешанный случай: исчерпан бюджет времени " (to-string mx-time-limit)
                                           " с (Риш по параметру) — ответ и вердикт не выдаются"))
          #f))))

(define (mx-run e x plan)
  (let ((kind (car plan)) (e1 (cadr plan)))
    (cond ((equal? kind 'curve) (mx-risch e x 1 e1 x x))
          (else
           (let* ((th (caddr plan)) (gx (mx-substitute e1 x th)))
             (alg-step 'mx-substitution "Подстановка t = θ(x)"
                       (string-append "t = " (alg-mp (mx-th-theta th)) ", dx = (dx/dt) dt; g(t) = f·dx/dt"
                                      (if (cdr gx) ": g не содержит x, exp, log — алгебраический случай по t"
                                          ": в g остаются x, exp или log — после рационализации Риш по параметру"))
                       (int-form e1 x) (int-form (subst (list mx-v 't) (car gx)) 't))
             (cond ((and (equal? kind 'theta) (cdr gx)) (mx-alg e x (car gx) th))
                   ((equal? kind 'theta)                      ; не x-free: x = log t / eᵗ остаётся — Риш по параметру
                    (let ((cg (mx-const-split (car gx) mx-v)))
                      (mx-risch e x (car cg) (cdr cg) mx-v (mx-th-theta th))))
                   ((equal? kind 'root) (mx-risch-root e x (car gx) th))
                   (else #f)))))))

; Шаги: рамка mx-integration с ключевыми шагами (подстановка/рационализация, интеграл по t, обратная подстановка,
; перенос отказа); расчёт тихий (alg-run). Доказанный отказ (mx-refused) — рамка остаётся: внутри 'mx%refused, снаружи #f.
(define (mx-run-framed e x plan)
  (set! mx-refused #f)
  (set! mx-why "")
  (let ((r (with-step ('mx-integration "Смешанный случай: радикал над башней exp/log" (int-form e x)
                       :after (lambda (v) (if (equal? v 'mx%refused) 'nonelementary v)))
             (alg-run (lambda () (let ((v (mx-run e x plan))) (or v (and mx-refused 'mx%refused))))))))
    (if (equal? r 'mx%refused) #f r)))

; ---------- стратегия ----------

; дешёвый синтаксический фильтр: радикал и exp/log/sinh/cosh/tanh от x
(define (mx-candidate? e x)
  (and (pair? (gn-rad-nodes e)) (mx-has-head? e '(exp log sinh cosh tanh))))

; (int-mixed e x d): ответ | #f; при доказанном отказе — условие risch-nonelementary для e
; (и int-none-proved, если e — верхняя форма integrate). Вход из int-go при d = 0 и стратегия при d = 1.
; Внутренний integrate (int-genus0) переписывает int-top-form — восстанавливаем.
(define (int-mixed e x d)
  (and (not mx-busy) (< d 2) (not (member? x '(t y %t)))
       (mx-candidate? e x)
       (let ((plan (mx-plan e x)))
         (and plan
              (let ((top int-top-form) (np int-none-proved))
                (set! mx-busy #t)
                (let ((r (unwind-protect (try (mx-run-framed e x plan) (lambda (err) #f))
                                         (begin (set! mx-busy #f)
                                                (set! int-top-form top)
                                                (set! int-none-proved np)))))
                  (if (and (not r) (equal? e int-top-form) (int-none-cond? e x))
                      (set! int-none-proved #t))
                  r))))))

(define (int-mixed-strategy e x d) (and (> d 0) (int-mixed e x d)))

(int-add-strategy int-genus0-conic)
(int-add-strategy int-mixed-strategy)
