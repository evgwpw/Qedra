; risch/field.lisp — арифметика многочленов K[θ] над дифференциальным полем K = ℚ(x, θ₁ … θₖ₋₁): подшаг 21k.1
;
; Источники — Бронштейн, Symbolic Integration I, гл. 5 (арифметика K[θ], MONOTOOL, SUBRESP). Модуль risch
; продолжат tower.lisp (21k.2), reduce.lisp (21k.3), driver.lisp (21k.4), rde.lisp (21k.5); приватные имена файлов модуля общие,
; экспорт добавится в driver.lisp вместе с описанием в docs\lisp-library-guide.md. Тесты обращаются как risch::rs-….
;
; ---------- Представление ----------
; БАШНЯ — список (x уровень₁ … уровеньₖ), снизу вверх; x — главная переменная (Dx = 1, остальные символы-параметры — константы).
; УРОВЕНЬ — список (θ вид аргумент Dθ):
;   θ — свежий символ (%t1, %t2 …), вид — log | exp, аргумент — u (θ = log u) или η (θ = exp η), оба — элементы K = нижней башни;
;   Dθ — выражение над K и θ: для log Du/u (элемент K), для exp Dη·θ (степени 1 по θ). Строится rs-extend, не вручную.
; Элемент K — обычное выражение от x и θ₁ … θₖ₋₁ (рациональная функция); нормальная форма — (together e): в ней сокращено всё общее,
; нуль — ровно число 0 (rs-zero?). Каждый коэффициент после каждой операции проходит rs-nf, иначе выражения растут.
; МНОГОЧЛЕН ИЗ K[θ] — список коэффициентов, СТАРШАЯ СТЕПЕНЬ ПЕРВАЯ (как poly-add), без ведущих нулей; нуль — ().
; Свой список, а не выражение, потому что poly-gcd / poly-remainder / coeff принимают только многочлены (проверено в 21k.1:
; «ожидается многочлен» на x⁻¹ в коэффициентах), а poly-gcd к тому же считает ВСЕ символы переменными, т. е. НОД в ℚ[x, θ] ≠ НОД в K[θ].
; Для ПРС (rs-prs) кольцо коэффициентов — K[z] (z — переменная вычетов ЛРТ): операции тех же rs-nf, деления точные.
; rs-from-expr / rs-to-expr — переходы «выражение ↔ список».

(module risch)

; ---------- башня ----------
(define (rs-tower x) (list x))
(define (rs-tower-x tw) (car tw))
(define (rs-levels tw) (cdr tw))
(define (rs-top tw) (if (null? (cdr tw)) #f (last tw)))             ; верхний уровень или #f (башня без мономов — база ℚ(x))
(define (rs-lower tw) (if (null? (cdr tw)) tw (take tw (- (length tw) 1))))
(define (rs-level-theta lv) (car lv))
(define (rs-level-kind lv) (cadr lv))
(define (rs-level-arg lv) (nth lv 2))
(define (rs-level-dtheta lv) (nth lv 3))

; нормальная форма элемента K и проверка нуля (together: общий знаменатель, НОД сокращён)
(define (rs-nf e) (together e))
; R4: together = 0 — нуль; рациональная функция с точными числами и ≠ 0 — не нуль (together каноничен). Иначе (коэффициенты
; с log 6 − log 2 − log 3, √(3+2√2) − 1 − √2, …) коэффициенты при x и θ проверяет const-zero? (constzero.lisp): доказанный нуль — нуль,
; доказанный не-нуль — не нуль, unknown — ответ не зависит от догадки: флаг rs-zero-unknown, rs-run тогда отказывает («не знаю»).
(define rs-zero-unknown #f)
(define (rs-zero? e)
  (let ((t (together e)))
    (cond ((equal? t 0) #t)
          ((const-plain? t) #f)
          (else (rs-zero-deep t)))))
(define (rs-zero-deep t)
  (let ((vs (const-free-syms t)))
    (if (null? vs)
        (rs-zero-verdict (list (const-zero? t)))
        (let ((cs (try (rs-coeffs-all (numer t) vs) (lambda (err) #f))))
          (if (not cs)
              #f
              (rs-zero-verdict (map rs-zero-coef cs)))))))
; вердикт коэффициента: #t нуль, #f не нуль, unknown
(define (rs-zero-coef c)
  (cond ((equal? c 0) #t)
        ((const-plain? c) #f)
        ((const-closed? c) (const-zero? c))
        (else #f)))                                                       ; с параметрами: генерический ≠ 0 (как раньше)
(define (rs-zero-verdict vs)
  (cond ((any? (lambda (v) (equal? v #f)) vs) #f)
        ((any? (lambda (v) (equal? v 'unknown)) vs) (set! rs-zero-unknown #t) #f)
        (else #t)))
(define (rs-mulc a b) (rs-nf (list '* a b)))
(define (rs-inv c) (rs-nf (list '^ c -1)))

; Производная элемента K по башне: D e = ∂e/∂x + Σ Dθᵢ·∂e/∂θᵢ (цепное правило; параметры — константы)
(define (rs-deriv tw e)
  (rs-nf (cons '+ (cons (diff (car tw) e)
                        (map (lambda (lv)
                               (if (contains-sym? e (car lv)) (list '* (rs-level-dtheta lv) (diff (car lv) e)) 0))
                             (cdr tw))))))

; Новый уровень над башней: log — Dθ = Du/u, exp — Dθ = Dη·θ
(define (rs-extend tw th kind arg)
  (let ((d (cond ((equal? kind 'log) (rs-mulc (rs-deriv tw arg) (rs-inv arg)))
                 ((equal? kind 'exp) (rs-mulc (rs-deriv tw arg) th))
                 ((equal? kind 'atan) (rs-mulc (rs-deriv tw arg) (rs-inv (list '+ 1 (list '^ arg 2)))))   ; 21k.5′: θ = atan u
                 ((equal? kind 'tan) (rs-mulc (rs-deriv tw arg) (list '+ 1 (list '^ th 2))))      ; 21k″: θ = tan u, Dθ = Du·(1+θ²) — степень 2 по θ
                 (else (error "risch: вид монома — log, atan, tan или exp")))))
    (append tw (list (list th kind arg d)))))

; Случай верхнего монома: base — K = ℚ(x) (мономов нет), primitive — log (Dθ ∈ K), exp — Dθ = (Dη)·θ
(define (rs-case tw)
  (let ((lv (rs-top tw)))
    (cond ((not lv) 'base)
          ((member? (rs-level-kind lv) '(log atan)) 'primitive)      ; atan u: Dθ = Du/(1+u²) ∈ K — тоже примитивный
          ((equal? (rs-level-kind lv) 'tan) 'tan)                    ; 21k″: Dθ = Du·(1+θ²), специальный множитель θ²+1
          (else 'exp))))

; ---------- многочлены K[θ] как списки ----------
(define (rs-trim p) (cond ((null? p) p) ((rs-zero? (car p)) (rs-trim (cdr p))) (else p)))
(define (rs-deg p) (- (length p) 1))                                 ; deg () = −1
(define (rs-lc p) (car p))
(define (rs-zeros n) (if (<= n 0) '() (cons 0 (rs-zeros (- n 1)))))
(define (rs-shift p n) (if (null? p) p (append p (rs-zeros n))))     ; p·θⁿ

; выражение, рациональное по x, θ₁…, многочлен по θ (знаменатель от θ не зависит) → список
(define (rs-from-expr e th)
  (let* ((tg (together e)) (n (numer tg)) (d (denom tg)))
    (if (contains-sym? d th)
        (error "risch: знаменатель зависит от θ — не многочлен из K[θ]")
        (let ((di (rs-inv d)))
          (rs-trim (map (lambda (c) (rs-mulc c di)) (reverse (coefficients n th))))))))

(define (rs-to-expr p th)
  (if (null? p)
      0
      (simplify (cons '+ (map2 (lambda (c k) (list '* c (list '^ th k))) p (reverse (range (length p))))))))

(define (rs-neg p) (map (lambda (c) (rs-mulc -1 c)) p))
(define (rs-scale p c) (if (rs-zero? c) '() (map (lambda (a) (rs-mulc c a)) p)))
(define (rs-add p q)
  (let ((lp (length p)) (lq (length q)))
    (if (< lp lq)
        (rs-add q p)
        (rs-trim (map2 (lambda (a b) (rs-nf (list '+ a b))) p (append (rs-zeros (- lp lq)) q))))))
(define (rs-sub p q) (rs-add p (rs-neg q)))
(define (rs-mul p q)
  (if (null? p)
      '()
      (rs-add (rs-shift (rs-scale q (car p)) (- (length p) 1)) (rs-mul (cdr p) q))))
(define (rs-monic p) (if (null? p) p (rs-scale p (rs-inv (car p)))))

; ---------- деление, НОД, расширенный Евклид (над полем K) ----------
; (rs-divmod a b) → (q r), a = q·b + r, deg r < deg b; b ≠ 0
(define (rs-divmod-loop r q b db ib)
  (if (< (rs-deg r) db)
      (list q r)
      (let ((m (rs-shift (list (rs-mulc (car r) ib)) (- (rs-deg r) db))))
        (rs-divmod-loop (rs-sub r (rs-mul m b)) (rs-add q m) b db ib))))
(define (rs-divmod a b)
  (if (null? b)
      (error "risch: деление на нулевой многочлен")
      (rs-divmod-loop a '() b (rs-deg b) (rs-inv (car b)))))
(define (rs-quo a b) (car (rs-divmod a b)))
(define (rs-rem a b) (cadr (rs-divmod a b)))

; НОД — унитарный (gcd(0, 0) = 0)
(define (rs-gcd a b)
  (if (null? b) (rs-monic a) (rs-gcd b (rs-rem a b))))

; (rs-gcdex a b) → (s t g): s·a + t·b = g = НОД (унитарный)
(define (rs-gcdex-loop r0 s0 t0 r1 s1 t1)
  (if (null? r1)
      (if (null? r0)
          (list '() '() '())
          (let ((c (rs-inv (car r0)))) (list (rs-scale s0 c) (rs-scale t0 c) (rs-scale r0 c))))
      (let* ((qr (rs-divmod r0 r1)) (q (car qr)))
        (rs-gcdex-loop r1 s1 t1 (cadr qr) (rs-sub s0 (rs-mul q s1)) (rs-sub t0 (rs-mul q t1))))))
(define (rs-gcdex a b) (rs-gcdex-loop a (list 1) '() b '() (list 1)))

; Диофантово уравнение s·a + t·b = c: (s t) с deg s < deg b (b ≠ 0), или #f, если НОД(a, b) не делит c
(define (rs-diophantine a b c)
  (if (null? b)
      (and (not (null? a)) (null? (rs-rem c a)) (list (rs-quo c a) '()))
      (let* ((e (rs-gcdex a b)) (g (caddr e)))
        (if (null? g)
            (and (null? c) (list '() '()))
            (let ((qr (rs-divmod c g)))
              (and (null? (cadr qr))
                   (let* ((s0 (rs-mul (car qr) (car e))) (t0 (rs-mul (car qr) (cadr e)))
                          (sq (rs-divmod s0 b)))
                     (list (cadr sq) (rs-add t0 (rs-mul (car sq) a))))))))))

; ---------- бесквадратное разложение (Юн) ----------
; формальная производная по θ (не D!)
(define (rs-dtheta-loop l k acc)
  (if (<= k 0)
      (rs-trim (reverse acc))
      (rs-dtheta-loop (cdr l) (- k 1) (cons (rs-mulc k (car l)) acc))))
(define (rs-dtheta p) (rs-dtheta-loop p (rs-deg p) '()))

; (rs-sqfree p) → (lc (f₁ m₁) … (fₖ mₖ)): p = lc·∏ fᵢ^mᵢ, fᵢ унитарные, бесквадратные, попарно взаимно простые, mᵢ возрастают
(define (rs-sqfree-loop c d i acc lc)
  (if (< (rs-deg c) 1)
      (cons lc (reverse acc))
      (let* ((a (rs-gcd c d)) (c2 (rs-quo c a)) (d2 (rs-sub (rs-quo d a) (rs-dtheta c2))))
        (rs-sqfree-loop c2 d2 (+ i 1) (if (> (rs-deg a) 0) (cons (list a i) acc) acc) lc))))
(define (rs-sqfree p)
  (if (null? p)
      (list 0)
      (let* ((m (rs-monic p)) (dm (rs-dtheta m)))
        (if (null? dm)
            (list (car p))
            (let* ((g (rs-gcd m dm)) (c (rs-quo m g)) (d (rs-sub (rs-quo dm g) (rs-dtheta c))))
              (rs-sqfree-loop c d 1 '() (car p)))))))

; ---------- субрезультантная ПРС (по псевдоостаткам) ----------
; Кольцо коэффициентов — K[z]: все деления точные. Для ЛРТ: a = d, b = a − z·Dd (многочлены по θ с коэффициентами из K[z]).
; Псевдоостаток prem(a, b) = остаток от lc(b)^(δ+1)·a при делении на b, δ = deg a − deg b.
(define (rs-prem a b)
  (let ((delta (- (rs-deg a) (rs-deg b))))
    (rs-rem (rs-scale a (rs-nf (list '^ (car b) (+ delta 1)))) b)))

; (rs-prs a b) → список многочленов a, b, r₁, r₂ … по убыванию степени (deg a ≥ deg b ≥ 0). Алгоритм Коллинза–Брауна (Cohen 3.3.1):
; r = prem(a, b) / (g·h^δ), g = lc(b), h ← h^(1−δ)·g^δ. Члены — субрезультанты с точностью до знака и множителя из K[z]
; (для НОД и для Sᵢ в ЛРТ этого достаточно). Член степени i — rs-prs-member.
(define (rs-prs-loop a b g h acc)
  (let* ((delta (- (rs-deg a) (rs-deg b))) (r (rs-prem a b)))
    (if (null? r)
        (reverse acc)
        (let* ((den (rs-nf (list '* g (list '^ h delta))))
               (r2 (rs-scale r (rs-inv den)))
               (g2 (car b))
               (h2 (rs-nf (list '* (list '^ h (- 1 delta)) (list '^ g2 delta)))))
          (rs-prs-loop b r2 g2 h2 (cons r2 acc))))))
(define (rs-prs a b) (rs-prs-loop a b 1 1 (list b a)))

; член ПРС степени i или #f (степени в ПРС могут пропускаться)
(define (rs-prs-member prs i)
  (cond ((null? prs) #f) ((= (rs-deg (car prs)) i) (car prs)) (else (rs-prs-member (cdr prs) i))))

; ---------- производная многочлена по башне ----------
; D(Σ cₖ θᵏ) = Σ (D cₖ) θᵏ + (d/dθ p)·Dθ; θ — верхний моном башни, коэффициенты — из нижней башни
; (21k.7a) база ℚ(x) — «моном» x над константами: D p = dp/dx (для Эрмита над ℚ(x) в prde.lisp)
(define (rs-deriv-poly tw p)
  (if (null? (rs-levels tw))
      (rs-dtheta p)
      (let* ((lv (rs-top tw)) (lower (rs-lower tw)))
        (rs-add (rs-trim (map (lambda (c) (rs-deriv lower c)) p))
                (rs-mul (rs-dtheta p) (rs-from-expr (rs-level-dtheta lv) (rs-level-theta lv)))))))

; ---------- порядки ----------
; (rs-order-at a p): кратность неприводимого p ∈ K[θ] в a ∈ K[θ] (a = 0 → inf)
(define (rs-order-at-loop a p n)
  (let ((qr (rs-divmod a p)))
    (if (null? (cadr qr)) (rs-order-at-loop (car qr) p (+ n 1)) n)))
(define (rs-order-at a p) (if (null? a) 'inf (rs-order-at-loop a p 0)))

; порядок в бесконечности дроби a/d ∈ K(θ): deg d − deg a (a = 0 → inf)
(define (rs-order-at-oo a d) (if (null? a) 'inf (- (rs-deg d) (rs-deg a))))
