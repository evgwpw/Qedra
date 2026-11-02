; risch/prde.lisp — линейные системы над константами и параметрическое (ограниченное) интегрирование: подшаг 21k.7a
;
; Источники — Бронштейн, Symbolic Integration I, гл. 6 (параметрическое RDE, ограниченное интегрирование),
; гипотеза Шануэля.
; 21k.7b (в конце файла): параметрическое RDE prde-solve / rs-param-rde и частичные решения RDE rs-rde-partial
; (частичные ответы exp-случая драйвера).
;
; ---------- rs-constant-system ----------
; (rs-constant-system A u syms) → (particular basis): решения A·c = u в КОНСТАНТАХ c₁…cₙ. A — список строк (элементы — выражения
; над K), u — вектор, syms — неконстантные символы (x и θ башни), всё остальное — константы (параметры, log 2 …).
; Каждая строка Σ Aᵢⱼ·%rscj − uᵢ → together → числитель → коэффициенты по всем мономам syms (rs-coeffs-all) → линейные уравнения
; над ℚ(константы) → исключение Гаусса (rs-gauss-elim из tower.lisp). particular — частное решение (свободные = 0) или #f
; (несовместно); basis — базис однородной системы. Каждый ответ проверяется подстановкой (rs-zero? A·c − u): не прошёл —
; отбрасывается, флаг rs-lim-uncertain и заметка в журнал. Флаг ставится и при «нестандартных» константах (не число, не символ-
; параметр, не log простого числа: sin 1, exp 1, √2 …) — между ними возможны скрытые соотношения (§8.5 п. 4), и тогда пустой
; базис/несовместность не доказаны.
;
; ---------- Параметрическое интегрирование ----------
; (rs-pi tw gs) → базис ((v (c₁ … cₘ)) …) пространства {(v, c): Dv = Σ cᵢgᵢ, v ∈ K, cᵢ — константы} по модулю констант в v
; (эталонная схема extendedint; знак обратный). Внутри — raise (lim-unknown причина).
;   база ℚ(x) и примитивный уровень θ (log, atan; на базе — «моном» x, Dx = 1, поле ниже — константы):
;     1. Эрмит каждого gᵢ: gᵢ = D aᵢ + hᵢ + Pᵢ, hᵢ — правильная дробь с бесквадратным нормальным знаменателем, Pᵢ ∈ K₀[θ].
;        У Dv простых полюсов нет ⇒ Σ cᵢhᵢ = 0 — rs-constant-system (базис B).
;     2. Многочленная часть сверху вниз (primextint): кандидаты (λ, W, R), Σλ·P − DW = R, deg R ≤ j. Уровень j: rs-pi поля ниже
;        для (ρ₁ … ρₛ, Dθ), ρₖ — коэффициент Rₖ при θʲ: Dw = Σαₖρₖ + μ·Dθ → W ← ΣαW + w·θʲ − μ/(j+1)·θʲ⁺¹ (константа при θʲ⁺¹
;        определялась прошлым уровнем с точностью до константы — она и есть μ). deg v ≤ deg P + 1 (θ трансцендентен).
;   exp-уровень θ = exp η: g без θ — спуск ниже (Dv ∈ K₀ ⇒ v ∈ K₀); иначе Эрмит, Σ cᵢhᵢ = 0, Лоранова часть: коэффициент при θʲ,
;     j ≠ 0 — уравнение Dvⱼ + j·Dη·vⱼ = Σλρⱼ: (а) j ≠ 0 нет — спуск для θ⁰; (б) один кандидат (λ ∈ {0, 1}) — обычное rs-rde
;     по каждому j; (в) несколько (21k.7b) — параметрическое RDE по каждому j, базис λ сужается последовательно (expextint).
; (rs-limited-integrate tw f ws) → (ok v (c₁ … cₘ)) | (none причина) | (unknown причина): f = Dv + Σ cᵢwᵢ (Бронштейн limited_integrate,
;   эталонная схема — то же параметрическое интегрирование по списку (f, w₁ … wₘ)). none — только без флага неуверенности; ok — проверено
;   подстановкой.

(module risch)

(define rs-lim-uncertain #f)
(define (lim-unknown why) (raise (list 'lim-unknown why)))
(define (lim-uncertain!) (set! rs-lim-uncertain #t))

; ---------- векторы и линейные комбинации ----------
(define (rs-unit n k) (map (lambda (i) (if (= i k) 1 0)) (range n)))
(define (rs-lin cs es) (rs-nf (cons '+ (cons 0 (map2 (lambda (c e) (list '* c e)) cs es)))))       ; Σ cₖ·eₖ
(define (rs-vec-lin cs vs)                                           ; Σ cₖ·vₖ (векторы одной длины)
  (if (null? vs) '() (map (lambda (i) (rs-lin cs (map (lambda (v) (nth v i)) vs))) (range (length (car vs))))))
(define (rs-poly-lin cs ps) (foldl (lambda (acc p) (rs-add acc p)) '() (map2 (lambda (c p) (rs-scale p c)) cs ps)))

; ---------- константы: допустимые атомы (§8.5 п. 4) ----------
(define (rs-prime? n) (let ((f (rs-int-factors n 2 '()))) (and f (= (length f) 1) (= (cadr (car f)) 1))))
(define (rs-plain-const? e)
  (cond ((number? e) (rational-number? e))
        ((symbol? e) #t)
        ((not (pair? e)) #f)
        ((member? (car e) '(+ *)) (every? rs-plain-const? (cdr e)))
        ((and (equal? (car e) '^) (= (length e) 3)) (and (integer? (caddr e)) (rs-plain-const? (cadr e))))
        ((and (equal? (car e) 'log) (= (length e) 2)) (and (integer? (cadr e)) (> (cadr e) 1) (rs-prime? (cadr e))))
        (else #f)))

; ---------- rs-constant-system ----------
(define (rs-cs-unknowns n) (map (lambda (i) (string->symbol (string-append "%rsc" (to-string (+ i 1))))) (range n)))

; строки линейной системы над константами из уравнений Σ Aᵢⱼcⱼ = uᵢ
(define (rs-cs-rows A u cs syms)
  (append-map
   (lambda (ru)
     (let* ((e (rs-nf (cons '+ (cons (list '* -1 (cadr ru)) (map2 (lambda (a c) (list '* a c)) (car ru) cs)))))
            (coefs (filter (lambda (c) (not (rs-zero? c))) (rs-coeffs-all (numer e) syms))))
       (map (lambda (c)
              (if (any? (lambda (s) (contains-sym? c s)) syms) (lim-unknown "система над константами: коэффициент не константа"))
              (if (not (rs-plain-const? c)) (lim-uncertain!))
              (rs-eq-row c cs))
            coefs)))
   (map2 list A u)))

(define (rs-cs-check A u c hom?)                                    ; A·c = u (hom? — A·c = 0) подстановкой
  (every? (lambda (ru) (rs-zero? (list '+ (rs-lin c (car ru)) (if hom? 0 (list '* -1 (cadr ru)))))) (map2 list A u)))

(define (rs-cs-fail! what)
  (lim-uncertain!)
  (rs-note 'risch-limited "Алгоритм Риша: система над константами" (string-append "проверка подстановкой не прошла: " what) 0 0))

(define (rs-cs-solve A u syms)
  (let* ((n (if (null? A) 0 (length (car A)))) (cs (rs-cs-unknowns n))
         (el (rs-gauss-elim (rs-cs-rows A u cs syms) '() 0 n))
         (pivots (cadr el)) (free (filter (lambda (k) (not (assoc k pivots))) (range n)))
         (part (and (every? (lambda (r) (rs-zero? (last r))) (car el))
                    (map (lambda (k) (let ((p (assoc k pivots))) (if p (last (cadr p)) 0))) (range n))))
         (basis (map (lambda (f)
                       (map (lambda (k) (let ((p (assoc k pivots)))
                                          (cond ((= k f) 1) (p (rs-nf (list '* -1 (nth (cadr p) f)))) (else 0))))
                            (range n)))
                     free))
         (part2 (if (and part (not (rs-cs-check A u part #f))) (begin (rs-cs-fail! "частное решение") #f) part))
         (basis2 (filter (lambda (b) (or (rs-cs-check A u b #t) (begin (rs-cs-fail! "базисный вектор") #f))) basis)))
    (list part2 basis2)))

; (rs-constant-system A u syms) → (particular basis); при внутренней ошибке — (#f ()) и флаг rs-lim-uncertain
(define (rs-constant-system A u syms)
  (try (rs-cs-solve A u syms)
       (lambda (err) (lim-uncertain!) (list #f '()))))

(define (rs-cs-nullspace hs syms)                                   ; базис {c : Σ cᵢhᵢ = 0}
  (if (every? rs-zero? hs)
      (map (lambda (k) (rs-unit (length hs) k)) (range (length hs)))
      (cadr (rs-constant-system (list hs) (list 0) syms))))

; ---------- уровни для параметрического интегрирования ----------
; поле ниже базы — константы: (rs-const x)
(define (rs-pi-const? tw) (and (pair? tw) (equal? (car tw) 'rs-const)))
(define (rs-pi-down tw) (if (null? (rs-levels tw)) (list 'rs-const (rs-tower-x tw)) (rs-lower tw)))
(define (rs-pi-dmono tw) (if (null? (rs-levels tw)) 1 (rs-level-dtheta (rs-top tw))))

; g = D a + h + остаток: проверка разложения Эрмита подстановкой (ошибка здесь дала бы ложное «нет решения»)
(define (rs-pi-check tw g a h rest)
  (if (not (rs-zero? (list '+ g (list '* -1 (rs-deriv tw a)) (list '* -1 h) (list '* -1 rest))))
      (lim-unknown "параметрическое интегрирование: разложение Эрмита не прошло проверку")))

; база/примитивный уровень: g → (a h P), g = Da + h + P, P ∈ K₀[θ] (список)
(define (rs-pi-split-prim tw g)
  (let* ((th (rs-top-theta tw)) (fr (rde-frac tw g)) (num (car fr)) (d (cadr fr)))
    (if (< (rs-deg d) 1)
        (list 0 0 (rs-scale num (rs-inv (car d))))
        (let* ((hm (rs-hermite tw num d)) (gg (car hm)) (h (cadr hm)) (r (caddr hm)))
          (if (> (rs-deg (cadr r)) 0) (lim-unknown "Эрмит: многочленная часть со знаменателем"))
          (let ((a (if (null? (car gg)) 0 (rs-frac-expr tw gg)))
                (he (if (null? (car h)) 0 (rs-frac-expr tw h)))
                (P (rs-scale (car r) (rs-inv (car (cadr r))))))
            (rs-pi-check tw g a he (rs-to-expr P th))
            (list a he P))))))

; поле констант: Dv = 0 ⇒ Σ cᵢgᵢ = 0
(define (rs-pi-const tw gs)
  (if (any? (lambda (g) (contains-sym? g (cadr tw))) gs) (lim-unknown "параметрическое интегрирование: не константа на уровне констант"))
  (map (lambda (b) (list 0 b)) (rs-cs-nullspace gs '())))

; многочленная часть примитивного уровня: кандидаты (λ W R)
(define (rs-pi-poly-step tw j cands s)
  (let* ((w (car s)) (cv (cadr s)) (al (take cv (length cands))) (mu (last cv))
         (kappa (rs-nf (list '* -1 mu (/ 1 (+ j 1)))))
         (Wn (rs-add (rde-mono w j) (rde-mono kappa (+ j 1))))
         (R (rs-sub (rs-poly-lin al (map caddr cands)) (rs-deriv-poly tw Wn))))
    (if (>= (rs-deg R) j) (lim-unknown "параметрическое интегрирование: старший коэффициент не сократился"))
    (list (rs-vec-lin al (map car cands)) (rs-add (rs-poly-lin al (map cadr cands)) Wn) R)))

(define (rs-pi-poly-loop tw j cands)
  (cond ((null? cands) '())
        ((< j 0) (map (lambda (c) (list (rs-to-expr (cadr c) (rs-top-theta tw)) (car c))) cands))
        (else
         (let* ((rhos (map (lambda (c) (rde-coef (caddr c) j)) cands))
                (sols (rs-pi (rs-pi-down tw) (append rhos (list (rs-pi-dmono tw))))))
           (rs-pi-poly-loop tw (- j 1) (map (lambda (s) (rs-pi-poly-step tw j cands s)) sols))))))

(define (rs-pi-poly tw ps)
  (let ((r (length ps)))
    (rs-pi-poly-loop tw (foldl max -1 (map rs-deg ps)) (map2 (lambda (k p) (list (rs-unit r k) '() p)) (range r) ps))))

; общая сборка: Σ cᵢhᵢ = 0 (базис B), затем задача для «остатков» Σ bᵢ·(Pᵢ) и сдвиг v на Σ λ·Σ bᵢaᵢ
(define (rs-pi-assemble tw sp solve-rest)
  (let ((B (rs-cs-nullspace (map cadr sp) (rs-vars tw))))
    (if (null? B)
        '()
        (let ((as (map (lambda (b) (rs-lin b (map car sp))) B)))
          (map (lambda (s) (list (rs-nf (list '+ (car s) (rs-lin (cadr s) as))) (rs-vec-lin (cadr s) B)))
               (solve-rest B))))))

(define (rs-pi-prim tw gs)
  (let ((sp (map (lambda (g) (rs-pi-split-prim tw g)) gs)))
    (rs-pi-assemble tw sp (lambda (B) (rs-pi-poly tw (map (lambda (b) (rs-poly-lin b (map caddr sp))) B))))))

; ---------- exp-уровень ----------
; g → (a h L), L — Лоранов многочлен ((j aⱼ) …) (rs-laurent-of, driver.lisp)
(define (rs-pi-split-exp tw g)
  (let* ((th (rs-top-theta tw)) (fr (rde-frac tw g)) (num (car fr)) (d (cadr fr))
         (k (rde-ord d)) (dn (rs-quo d (rde-mono 1 k))))
    (if (< (rs-deg dn) 1)
        (list 0 0 (rs-laurent-of (rs-scale num (rs-inv (car dn))) k))
        (let* ((hm (rs-hermite tw num d)) (gg (car hm)) (h (cadr hm)) (r (caddr hm)) (m (rde-ord (cadr r))))
          (if (not (= m (rs-deg (cadr r)))) (lim-unknown "exp-уровень: знаменатель остатка Эрмита не степень θ"))
          (let* ((a (if (null? (car gg)) 0 (rs-frac-expr tw gg)))
                 (he (if (null? (car h)) 0 (rs-frac-expr tw h)))
                 (L (rs-laurent-of (rs-scale (car r) (rs-inv (car (cadr r)))) m)))
            (rs-pi-check tw g a he (rs-laurent-expr L th))
            (list a he L))))))

(define (rs-laurent-coef L j) (let ((p (assoc j L))) (if p (cadr p) 0)))
(define (rs-laurent-lin cs Ls)
  (let ((js (rs-unique (append-map (lambda (L) (map car L)) Ls))))
    (filter (lambda (p) (not (rs-zero? (cadr p))))
            (map (lambda (j) (list j (rs-lin cs (map (lambda (L) (rs-laurent-coef L j)) Ls)))) js))))

; один кандидат L (λ ∈ {0, 1}): обычные RDE по j ≠ 0 и интегрирование θ⁰ уровнем ниже → v (Dv = L) | #f (доказано: нет) | unknown
(define (rs-pi-laurent-one tw L)
  (let* ((lo (rs-lower tw)) (th (rs-top-theta tw))
         (rs (map (lambda (p) (list (car p) (rs-rde lo (rs-mulc (car p) (rde-eta tw)) (cadr p))))
                  (filter (lambda (p) (not (= (car p) 0))) L))))
    (cond ((any? (lambda (r) (equal? (car (cadr r)) 'none)) rs) #f)
          ((any? (lambda (r) (equal? (car (cadr r)) 'unknown)) rs) 'unknown)
          (else
           (let ((s0 (rs-first (lambda (s) (and (not (rs-zero? (car (cadr s)))) s)) (rs-pi lo (list (rs-laurent-coef L 0))))))
             (and s0 (rs-nf (cons '+ (cons (rs-mulc (car s0) (rs-inv (car (cadr s0))))
                                           (map (lambda (r) (list '* (cadr (cadr r)) (list '^ th (car r)))) rs))))))))))

(define (rs-pi-laurent tw Ls)
  (let ((a0s (map (lambda (L) (rs-laurent-coef L 0)) Ls)))
    (cond ((every? (lambda (L) (every? (lambda (p) (= (car p) 0)) L)) Ls) (rs-pi (rs-lower tw) a0s))
          ((= (length Ls) 1)
           (let ((v (rs-pi-laurent-one tw (car Ls))))
             (cond ((equal? v 'unknown) (lim-unknown "exp-уровень: уравнение Риша не решено"))
                   (v (list (list v (list 1))))
                   (else '()))))
          (else (rs-pi-laurent-param tw Ls)))))

; (21k.7b) несколько кандидатов: по каждому j ≠ 0 — параметрическое RDE Dvⱼ + j·Dη·vⱼ = Σλₖρₖⱼ уровнем ниже (prde-solve),
; базис λ сужается последовательно (expextint); θ⁰ — параметрическое интегрирование уровнем ниже. Элемент — (κ v).
(define (rs-pi-laurent-param tw Ls)
  (let* ((lo (rs-lower tw)) (th (rs-top-theta tw)) (n (length Ls))
         (js (filter (lambda (j) (not (= j 0))) (rs-unique (append-map (lambda (L) (map car L)) Ls))))
         (els (foldl (lambda (els j)
                       (let* ((rhs (map (lambda (e) (rs-lin (car e) (map (lambda (L) (rs-laurent-coef L j)) Ls))) els))
                              (sub (rs-pi-prde lo (rs-mulc j (rde-eta tw)) rhs)))
                         (map (lambda (s) (list (prde-kappa (cadr s) (map car els) n)
                                                (rs-nf (list '+ (rs-lin (cadr s) (map cadr els)) (list '* (car s) (list '^ th j))))))
                              sub)))
                     (map (lambda (k) (list (rs-unit n k) 0)) (range n))
                     js))
         (rhs0 (map (lambda (e) (rs-lin (car e) (map (lambda (L) (rs-laurent-coef L 0)) Ls))) els))
         (sub0 (if (null? els) '() (rs-pi lo rhs0))))
    (map (lambda (s) (list (rs-nf (list '+ (rs-lin (cadr s) (map cadr els)) (car s))) (prde-kappa (cadr s) (map car els) n)))
         sub0)))

(define (rs-pi-exp tw gs)
  (let ((sp (map (lambda (g) (rs-pi-split-exp tw g)) gs)))
    (rs-pi-assemble tw sp (lambda (B) (rs-pi-laurent tw (map (lambda (b) (rs-laurent-lin b (map caddr sp))) B))))))

; ---------- вход ----------
(define (rs-pi tw gs)
  (cond ((rs-pi-const? tw) (rs-pi-const tw gs))
        ((every? rs-zero? gs) (map (lambda (k) (list 0 (rs-unit (length gs) k))) (range (length gs))))
        ((equal? (rs-case tw) 'exp)
         (if (any? (lambda (g) (contains-sym? g (rs-top-theta tw))) gs) (rs-pi-exp tw gs) (rs-pi (rs-lower tw) gs)))
        (else (rs-pi-prim tw gs))))

; (rs-limited-integrate tw f ws) → (ok v cs) | (none причина) | (unknown причина)
(define (rs-limited-integrate tw f ws)
  (let ((saved rs-lim-uncertain))
    (set! rs-lim-uncertain #f)
    (let* ((r (try (list 'ok (rs-pi tw (cons f ws)))
                   (lambda (err)
                     (let ((d (error-data err)))
                       (if (and (pair? d) (equal? (car d) 'lim-unknown))
                           (list 'unknown (cadr d))
                           (list 'unknown (string-append "ошибка: " (error-message err))))))))
           (unc rs-lim-uncertain))
      (set! rs-lim-uncertain saved)
      (if (equal? (car r) 'unknown)
          r
          (let ((s (rs-first (lambda (s) (and (not (rs-zero? (car (cadr s)))) s)) (cadr r))))
            (cond (s (let* ((ic (rs-inv (car (cadr s)))) (v (rs-mulc (car s) ic))
                            (cs (map (lambda (c) (rs-nf (list '* -1 c ic))) (cdr (cadr s)))))
                       (if (rs-zero? (cons '+ (cons f (cons (list '* -1 (rs-deriv tw v)) (map2 (lambda (c w) (list '* -1 c w)) cs ws)))))
                           (list 'ok v cs)
                           (list 'unknown "проверка подстановкой не прошла"))))
                  (unc (list 'unknown "решения не найдено, но константы не нормализованы или система не проверена"))
                  (else (list 'none "f − Σ cᵢwᵢ не является производной элемента поля ни при каких константах cᵢ"))))))))

; ======================================================================================================================
; ---------- 21k.7b: параметрическое уравнение Риша (параметрическое RDE: param_rde/do_param_rde) ----------
; (prde-solve tw f gs) → базис ((y κ) …) пространства {(y, κ): Dy + f·y = Σ κᵢgᵢ, y ∈ K, κᵢ — константы} вместе с однородными
; решениями (y, 0). Внутренний: raise (rde-unknown …); флаг rs-rde-uncertain — базис, возможно, неполон (тогда «нет решения»
; не утверждается). Каждый элемент базиса проверяется подстановкой (не прошёл — отброшен, флаг).
; Схема — та же, что у rs-rde (rde.lisp), но со списком правых частей:
;   1. слабый нормализатор f (rde-weak), gᵢ ← p·gᵢ;
;   2. нормальный знаменатель (get_denom 910-916): e — нормальная часть НОК знаменателей gᵢ, h = НОД(e, e′)/НОД(p, p′),
;      a = dₙ·h, cᵢ = a·h·gᵢ; у a·Dq + b·q нормальных полюсов нет ⇒ Σκᵢ·(нормальная часть cᵢ) = 0 — система над константами
;      (базис N, как reducedSystem + nullSpace), дальше правые части — Σ Nⱼᵢ·(многочлен + специальная часть cᵢ);
;   3. специальный знаменатель (exp): порядок в θ = 0 — минимум по cᵢ (нулевая правая часть — +∞);
;   4. граница степени — rde-bound-d по max deg cᵢ;
;   5. параметрическое SPDE (multi_SPDE/param_SPDE 955-1001): n < 0 — только q = 0 (Σκc = 0); НОД(a, b) ≠ 1 — остатки по
;      модулю НОД обнуляются комбинацией; иначе диофантово r·b + z·a = c по каждой правой части, q = a·s + Σμr;
;   6. a = 1: «большой» b — старшие члены (SPDE1) по каждой правой части, остатки обнуляются комбинацией (решение единственно);
;      deg b = 0 — покоэффициентно уровнем ниже (do_SPDE_exp0/prim0): exp — по j (κ общие), primitive — сверху вниз со степени
;      max deg c + 1: однородное решение w уровня ниже — отдельный элемент базиса, его множитель определяется следующим
;      уровнем (выше max deg c + 1 решений нет: иначе θ ∈ K₀); b = 0 — параметрическое интегрирование rs-pi и константа (1, 0).

(define (prde-zero-vec n) (map (lambda (i) 0) (range n)))
(define (prde-kappa mu vs n) (if (null? vs) (prde-zero-vec n) (rs-vec-lin mu vs)))   ; Σ μⱼ·vⱼ (векторы длины n)

(define (prde-err-msg err)
  (let ((d (error-data err)))
    (if (and (pair? d) (member? (car d) '(rde-unknown rde-none lim-unknown))) (cadr d) (error-message err))))

; вызов кода ограниченного интегрирования: его флаг/исключение → флаг/исключение RDE
(define (prde-lim-call thunk what)
  (let ((saved rs-lim-uncertain))
    (set! rs-lim-uncertain #f)
    (let* ((r (try (list 'ok (thunk)) (lambda (err) (list 'err (prde-err-msg err)))))
           (unc rs-lim-uncertain))
      (set! rs-lim-uncertain saved)
      (if unc (rde-uncertain!))
      (if (equal? (car r) 'ok) (cadr r) (rde-unknown (string-append "PRDE: " what ": " (cadr r)))))))

; базис {κ : Σ κᵢeᵢ = 0} над константами (eᵢ — выражения над K)
(define (prde-null tw es) (prde-lim-call (lambda () (rs-cs-nullspace es (rs-vars tw))) "система над константами"))
(define (prde-null-polys tw ps) (prde-null tw (map (lambda (p) (rs-to-expr p (rde-theta tw))) ps)))

; Dy = Σ κᵢgᵢ: параметрическое интегрирование (по модулю констант) и константа — однородное решение
(define (prde-integrate tw gs)
  (cons (list 1 (prde-zero-vec (length gs)))
        (prde-lim-call (lambda () (rs-pi tw gs)) "параметрическое интегрирование")))

(define (prde-lcm a b) (rs-quo (rs-mul a b) (rs-gcd a b)))

; дробь c (знаменатель унитарен) → (нормальная-часть-выражение остаток-дробь): c = A/N + (многочлен + B/S)
(define (prde-decompose tw c)
  (let* ((sp (rde-split tw (cadr c))) (nn (car sp)) (ss (cadr sp)))
    (if (< (rs-deg nn) 1)
        (list 0 c)
        (let* ((qr (rs-divmod (car c) (cadr c)))
               (st (or (rs-diophantine ss nn (cadr qr)) (rde-unknown "PRDE: разложение на нормальную и специальную части"))))
          (list (rde-fexpr tw (list (car st) nn))
                (rs-frac-cancel (rs-frac-add (list (car qr) (list 1)) (list (cadr st) ss))))))))

(define (prde-frac-lin v fracs)                                      ; Σ vᵢ·fracᵢ
  (rs-frac-cancel (foldl (lambda (acc pr) (rs-frac-add acc (list (rs-scale (car (cadr pr)) (car pr)) (cadr (cadr pr)))))
                         (list '() (list 1)) (map2 list v fracs))))

; → (a b N cs h): y = q/h, a·Dq + b·q = Σ μⱼ·csⱼ, κ = Σ μⱼNⱼ; b, csⱼ — дроби со специальными знаменателями
(define (prde-normal-denom tw fa fd gfr)
  (let* ((dn (car (rde-split tw fd)))
         (en (car (rde-split tw (foldl prde-lcm (list 1) (map cadr gfr)))))
         (p (rs-gcd dn en))
         (h (rs-quo (rs-gcd en (rs-dtheta en)) (rs-gcd p (rs-dtheta p))))
         (a (rs-mul dn h)) (ah (rs-mul a h))
         (bf (rs-frac-cancel (list (rs-sub (rs-mul a fa) (rs-mul dn (rs-mul (rde-dp tw h) fd))) fd)))
         (parts (map (lambda (g) (prde-decompose tw (rs-frac-cancel (list (rs-mul ah (car g)) (cadr g))))) gfr))
         (N (prde-null tw (map car parts))))
    (list a bf N (map (lambda (v) (prde-frac-lin v (map cadr parts))) N) h)))

; специальный знаменатель (rde-special-denom со списком правых частей) → (A B Cs hs), q = r/hs, A·Dr + B·r = Σμ·Csⱼ
(define (prde-ord-frac cf) (if (null? (car cf)) 'inf (- (rde-ord (car cf)) (rde-ord (cadr cf)))))
(define (prde-special-denom tw a bf cfs)
  (if (not (equal? (rs-case tw) 'exp))
      (list a (rde-poly-of bf) (map rde-poly-of cfs) (list 1))
      (let* ((ba (car bf)) (bd (cadr bf)) (nb (prde-ord-frac bf))
             (fin (filter number? (map prde-ord-frac cfs)))
             (nc (if (null? fin) 'inf (foldl min (car fin) fin)))
             (n0 (if (equal? nc 'inf) 0 (min 0 (- nc (if (equal? nb 'inf) 0 (min 0 nb))))))
             (n (if (equal? nb 0) (rde-cancel-lower tw a ba bd n0) n0))
             (N (max 0 (max (if (equal? nb 'inf) 0 (- 0 nb)) (if (equal? nc 'inf) 0 (- n nc)))))
             (tN (rde-mono 1 N)) (aN (rs-mul a tN)))
        (list aN
              (rs-add (if (null? ba) '() (rde-exact-quo (rs-mul ba tN) bd)) (rs-scale aN (rs-mulc n (rde-eta tw))))
              (map (lambda (cf) (if (null? (car cf)) '() (rde-exact-quo (rs-mul (car cf) (rde-mono 1 (- N n))) (cadr cf)))) cfs)
              (rde-mono 1 (- 0 n))))))

; ---------- параметрическое SPDE: a·Dq + b·q = Σ κᵢcᵢ, deg q ≤ n → базис ((q κ) …) ----------
(define (prde-spde tw a b cs n)
  (let ((m (length cs)))
    (cond ((= (rs-deg a) 0)
           (let ((ia (rs-inv (car a))))
             (prde-poly tw (rs-scale b ia) (map (lambda (c) (rs-scale c ia)) cs) n)))
          ((< n 0) (map (lambda (v) (list '() v)) (prde-null-polys tw cs)))
          (else
           (let ((g (rs-gcd a b)))
             (if (> (rs-deg g) 0)
                 (let* ((qrs (map (lambda (c) (rs-divmod c g)) cs))
                        (Nv (prde-null-polys tw (map cadr qrs)))
                        (sub (prde-spde tw (rs-quo a g) (rs-quo b g) (map (lambda (v) (rs-poly-lin v (map car qrs))) Nv) n)))
                   (map (lambda (s) (list (car s) (prde-kappa (cadr s) Nv m))) sub))
                 (let* ((rzs (map (lambda (c) (or (rs-diophantine b a c) (rde-unknown "PRDE: SPDE — диофантово уравнение не решилось"))) cs))
                        (sub (prde-spde tw a (rs-add b (rde-dp tw a)) (map (lambda (rz) (rs-sub (cadr rz) (rde-dp tw (car rz)))) rzs)
                                        (- n (rs-deg a)))))
                   (map (lambda (s) (list (rs-add (rs-mul a (car s)) (rs-poly-lin (cadr s) (map car rzs))) (cadr s))) sub))))))))

; «большой» b: c = Dq + b·q + rem, deg rem < deg b — разложение единственно и линейно по c
(define (prde-spde1-one tw b c q)
  (if (or (null? c) (< (rs-deg c) (rs-deg b)))
      (list q c)
      (let* ((qq (rde-mono (rs-mulc (rs-lc c) (rs-inv (rs-lc b))) (- (rs-deg c) (rs-deg b))))
             (c2 (rs-sub c (rs-add (rs-mul b qq) (rde-dp tw qq)))))
        (if (>= (rs-deg c2) (rs-deg c)) (rde-unknown "PRDE: старшие члены не сократились"))
        (prde-spde1-one tw b c2 (rs-add q qq)))))
(define (prde-spde1 tw b cs)
  (let* ((qr (map (lambda (c) (prde-spde1-one tw b c '())) cs))
         (Nv (prde-null-polys tw (map cadr qr))))
    (map (lambda (v) (list (rs-poly-lin v (map car qr)) v)) Nv)))

; b = 0 на примитивном уровне: Dq = Σκc, q ∈ K₀[θ]
(define (prde-int-poly tw cs)
  (let ((th (rde-theta tw)))
    (map (lambda (s)
           (let ((p (try (rs-from-expr (car s) th) (lambda (err) 'fail))))
             (if (equal? p 'fail) (rde-unknown "PRDE: первообразная не многочлен по θ") (list p (cadr s)))))
         (prde-integrate tw (map (lambda (c) (rs-to-expr c th)) cs)))))

; exp: степени j = dc … 0 и, если решение может быть выше dc, единственный j > dc с однородным решением
; (b₀ + j·Dη = −Dw/w ⇔ −b₀ = Dw/w + j·Dη — параметрическая лог-производная rde-plogd)
(define (prde-exp-levels tw b0 dc n)
  (append (reverse (range (+ dc 1)))
          (cond ((<= n dc) '())
                ((<= (- n dc) 4) (map (lambda (k) (+ dc 1 k)) (range (- n dc))))
                (else (let ((m (rde-plogd (rs-lower tw) (rs-nf (list '* -1 b0)) (rde-eta tw))))
                        (if (and m (> m dc) (<= m n)) (list m) '()))))))

; последовательный спуск по коэффициентам: элемент (κ q w), на уровне j правые части rhs(e) → prde-solve lo f → новые элементы
(define (prde-down-step lo f els j m rhs-of)
  (let ((sub (prde-solve lo f (map rhs-of els))))
    (map (lambda (s) (let ((u (rs-nf (car s))))
                       (list (prde-kappa (cadr s) (map car els) m) (rs-add (rs-poly-lin (cadr s) (map cadr els)) (rde-mono u j)) u)))
         sub)))
(define (prde-start m) (map (lambda (k) (list (rs-unit m k) '() 0)) (range m)))

(define (prde-degrade-exp tw b0 cs n)
  (let* ((m (length cs)) (lo (rs-lower tw)) (eta (rde-eta tw)) (dc (foldl max -1 (map rs-deg cs))))
    (map (lambda (e) (list (cadr e) (car e)))
         (foldl (lambda (els j)
                  (prde-down-step lo (rs-nf (list '+ b0 (list '* j eta))) els j m
                                  (lambda (e) (rs-lin (car e) (map (lambda (c) (rde-coef c j)) cs)))))
                (prde-start m) (prde-exp-levels tw b0 dc n)))))

; primitive, deg b = 0, b₀ ≠ 0: сверху вниз Dqⱼ + b₀qⱼ = Σκcⱼ − (j+1)·Dθ·qⱼ₊₁, j = max deg c + 1 … 0 → базис ((q κ) …)
(define (prde-degrade-prim tw b0 cs)
  (let* ((m (length cs)) (lo (rs-lower tw)) (dth (rs-level-dtheta (rs-top tw))) (dc (foldl max -1 (map rs-deg cs))))
    (map (lambda (e) (list (cadr e) (car e)))
         (foldl (lambda (els j)
                  (prde-down-step lo b0 els j m
                                  (lambda (e) (rs-nf (list '+ (rs-lin (car e) (map (lambda (c) (rde-coef c j)) cs))
                                                           (list '* -1 (+ j 1) dth (caddr e)))))))
                (prde-start m) (reverse (range (+ dc 2)))))))

; a = 1: Dq + b·q = Σκc
(define (prde-poly tw b cs n)
  (let ((m (length cs)))
    (cond ((and (null? b) (rde-base? tw))
           (cons (list (list 1) (prde-zero-vec m)) (map (lambda (k) (list (rde-pint (nth cs k)) (rs-unit m k))) (range m))))
          ((and (not (null? b)) (or (rde-base? tw) (> (rs-deg b) 0))) (prde-spde1 tw b cs))
          ((equal? (rs-case tw) 'exp) (prde-degrade-exp tw (if (null? b) 0 (car b)) cs n))
          ((null? b) (prde-int-poly tw cs))
          (else (prde-degrade-prim tw (car b) cs)))))

(define (prde-solve-nz tw f gs)
  (let* ((m (length gs))
         (fr (rde-frac tw f))
         (wn (rde-weak tw (car fr) (cadr fr)))
         (P (rs-prod-factors wn))
         (fr1 (rde-sub-logd tw fr wn))
         (gfr (map (lambda (g) (let ((gr (rde-frac tw g))) (rs-frac-cancel (list (rs-mul P (car gr)) (cadr gr))))) gs))
         (nd (prde-normal-denom tw (car fr1) (cadr fr1) gfr))
         (N (caddr nd))
         (sd (prde-special-denom tw (car nd) (cadr nd) (nth nd 3)))
         (A (car sd)) (B (cadr sd)) (Cs (caddr sd))
         (n (if (> (rs-deg A) 0) (rde-bound-d tw A B (foldl max -1 (map rs-deg Cs))) rde-unbounded))
         (den (rs-mul P (rs-mul (nth nd 4) (nth sd 3)))))
    (filter (lambda (s) s)
            (map (lambda (s)
                   (let ((y (rde-fexpr tw (list (car s) den))) (kap (prde-kappa (cadr s) N m)))
                     (if (rs-zero? (list '+ (rs-deriv tw y) (list '* f y) (list '* -1 (rs-lin kap gs))))
                         (list y kap)
                         (begin (rde-uncertain!) #f))))
                 (prde-spde tw A B Cs n)))))

(define (prde-solve tw f gs)
  (if (rs-zero? f)
      (prde-integrate tw gs)
      (let* ((r (prde-solve-nz tw f gs))
             (found (filter (lambda (s) s) r)))
        (if rs-log?
            (rs-note 'risch-prde "Алгоритм Риша: параметрическое уравнение"
                     (string-append "Dy + f·y = Σ κᵢ·gᵢ: f = " (rs-mp-tower tw f)
                                    "; правых частей " (to-string (length gs))
                                    "; решений базиса " (to-string (length found))
                                    (if (null? found) " (решений нет)" ""))
                     (rs-th-subst tw f)
                     (cond ((null? found) 'решений-нет)
                           (else (rs-th-subst tw (car (car found))))))
            r))))

; (rs-param-rde tw f gs) → (ok базис) | (incomplete базис) | (unknown причина): базис ((y (κ₁ … κₘ)) …) решений
; Dy + f·y = Σ κᵢgᵢ; incomplete — найденные решения верны, но базис, возможно, неполон (флаг неуверенности)
(define (rs-param-rde tw f gs)
  (let ((saved rs-rde-uncertain))
    (set! rs-rde-uncertain #f)
    (let* ((r (try (list 'ok (prde-solve tw f gs)) (lambda (err) (list 'unknown (prde-err-msg err)))))
           (unc rs-rde-uncertain))
      (set! rs-rde-uncertain saved)
      (cond ((equal? (car r) 'unknown) r)
            (unc (list 'incomplete (cadr r)))
            (else r)))))

; для параметрического интегрирования: флаг/исключение PRDE → флаг/исключение ограниченного интегрирования
(define (rs-pi-prde lo f gs)
  (let ((r (rs-param-rde lo f gs)))
    (cond ((equal? (car r) 'ok) (cadr r))
          ((equal? (car r) 'incomplete) (lim-uncertain!) (cadr r))
          (else (lim-unknown (string-append "PRDE: " (cadr r)))))))

; ======================================================================================================================
; ---------- 21k.7b: частичное решение RDE (вид Бронштейна) ----------
; (rs-rde-partial tw f g) → (y r): g = Dy + f·y + r. Вызывается, когда rs-rde ДОКАЗАЛ, что решения в K нет; тогда и у
; Dz + f·z = r решения нет (z ↦ z − y), т. е. остаток r·θⁱ неэлементарен при любом y — выбор y влияет только на вид ответа.
; y строится тем же конвейером, что rs-rde, но вместо «нет решения» берётся достигнутое: нормальный знаменатель — нормальная
; часть c отбрасывается (уходит в остаток); SPDE при n < 0 или НОД(a, b) ∤ c — q = 0 на этом шаге (остаётся β); старшие
; члены — до первого несокращаемого; покоэффициентный спуск — частичные решения уровнем ниже. Шаг принимается, только если
; остаток «проще» (степени по θ сверху вниз, затем по x, затем размер); повторяется, пока остаток упрощается (≤ 4 раз).
; Примеры: eˣ/x² → y = −1/x, r = 1/x; x²·e^{x²} → y = x/2, r = −1/2; eˣ·log x → y = log x, r = −1/x.
(define rs-rde-partials? #t)

(define (rdp-normal-denom tw fa fd ga gd)
  (let* ((dn (car (rde-split tw fd))) (en (car (rde-split tw gd)))
         (p (rs-gcd dn en))
         (h (rs-quo (rs-gcd en (rs-dtheta en)) (rs-gcd p (rs-dtheta p))))
         (a (rs-mul dn h)))
    (list a
          (rs-frac-cancel (list (rs-sub (rs-mul a fa) (rs-mul dn (rs-mul (rde-dp tw h) fd))) fd))
          (cadr (prde-decompose tw (rs-frac-cancel (list (rs-mul (rs-mul a h) ga) gd))))
          h)))

; → (go b c α β) | (stop α β): q = α·r + β, Dr + b·r = c
(define (rdp-spde tw a b c n alpha beta)
  (if (or (null? c) (< n 0))
      (list 'stop alpha beta)
      (let ((g (rs-gcd a b)))
        (if (not (null? (rs-rem c g)))
            (list 'stop alpha beta)
            (let ((a1 (rs-quo a g)) (b1 (rs-quo b g)) (c1 (rs-quo c g)))
              (if (= (rs-deg a1) 0)
                  (let ((ia (rs-inv (car a1)))) (list 'go (rs-scale b1 ia) (rs-scale c1 ia) alpha beta))
                  (let ((rz (rs-diophantine b1 a1 c1)))
                    (if (not rz)
                        (list 'stop alpha beta)
                        (rdp-spde tw a1 (rs-add b1 (rde-dp tw a1)) (rs-sub (cadr rz) (rde-dp tw (car rz))) (- n (rs-deg a1))
                                  (rs-mul alpha a1) (rs-add beta (rs-mul alpha (car rz))))))))))))

(define (rdp-spde1 tw b c q)
  (if (or (null? c) (< (rs-deg c) (rs-deg b)))
      q
      (let* ((qq (rde-mono (rs-mulc (rs-lc c) (rs-inv (rs-lc b))) (- (rs-deg c) (rs-deg b))))
             (c2 (rs-sub c (rs-add (rs-mul b qq) (rde-dp tw qq)))))
        (if (>= (rs-deg c2) (rs-deg c)) q (rdp-spde1 tw b c2 (rs-add q qq))))))

; уровнем ниже: полное решение, если есть, иначе частичное
(define (rdp-sub tw f g)
  (if (rs-zero? g)
      0
      (let ((r (try (list 'ok (rde-solve tw f g)) (lambda (err) #f))))
        (rs-nf (if r (cadr r) (try (rdp-solve tw f g) (lambda (err) 0)))))))

(define (rdp-prim-loop tw b0 c j qprev acc)
  (if (< j 0)
      (rs-trim (reverse acc))
      (let* ((rhs (rs-nf (list '+ (rde-coef c j) (list '* -1 (+ j 1) (rs-level-dtheta (rs-top tw)) qprev))))
             (qj (if (rs-zero? rhs) 0 (rdp-sub (rs-lower tw) b0 rhs))))
        (rdp-prim-loop tw b0 c (- j 1) qj (cons qj acc)))))

(define (rdp-poly tw b c)
  (cond ((null? c) '())
        ((rde-base? tw) (if (null? b) (rde-pint c) (rdp-spde1 tw b c '())))
        ((and (not (null? b)) (> (rs-deg b) 0)) (rdp-spde1 tw b c '()))
        ((equal? (rs-case tw) 'exp)
         (let ((lo (rs-lower tw)) (eta (rde-eta tw)) (b0 (if (null? b) 0 (car b))))
           (rs-trim (map (lambda (j) (let ((cj (rde-coef c j)))
                                       (if (rs-zero? cj) 0 (rdp-sub lo (rs-nf (list '+ b0 (list '* j eta))) cj))))
                         (reverse (range (+ (rs-deg c) 1)))))))
        ((null? b) (let ((r (try (rde-integrate-poly tw c) (lambda (err) 'fail)))) (if (equal? r 'fail) '() r)))
        (else (rdp-prim-loop tw (car b) c (rs-deg c) 0 '()))))

(define (rdp-solve tw f g)
  (cond ((rs-zero? g) 0)
        ((rs-zero? f) (let ((r (try (list 'ok (rde-integrate-in tw g)) (lambda (err) #f)))) (if r (cadr r) 0)))
        (else
         (let* ((fr (rde-frac tw f)) (gr (rde-frac tw g))
                (wn (rde-weak tw (car fr) (cadr fr))) (P (rs-prod-factors wn))
                (fr1 (rde-sub-logd tw fr wn))
                (gr1 (rs-frac-cancel (list (rs-mul P (car gr)) (cadr gr))))
                (nd (rdp-normal-denom tw (car fr1) (cadr fr1) (car gr1) (cadr gr1)))
                (sd (prde-special-denom tw (car nd) (cadr nd) (list (caddr nd))))
                (A (car sd)) (B (cadr sd)) (C (car (caddr sd)))
                (n (if (> (rs-deg A) 0) (rde-bound tw A B C) rde-unbounded))
                (sp (rdp-spde tw A B C n (list 1) '()))
                (go? (equal? (car sp) 'go))
                (q (if go? (rdp-poly tw (cadr sp) (caddr sp)) '()))
                (al (if go? (nth sp 3) (cadr sp)))
                (be (if go? (nth sp 4) (caddr sp))))
           (rde-fexpr tw (list (rs-add (rs-mul al q) be) (rs-mul P (rs-mul (nth nd 3) (nth sd 3)))))))))

; «сложность» элемента K: степени числителя + знаменателя по θ сверху вниз, затем по x, затем размер выражения
(define (rdp-deg e s) (if (contains-sym? e s) (degree e s) 0))
(define (rdp-measure tw e)
  (let* ((tg (together e)) (nu (numer tg)) (de (denom tg)))
    (append (map (lambda (s) (+ (rdp-deg nu s) (rdp-deg de s))) (reverse (rs-vars tw))) (list (rs-size tg)))))
(define (rdp-less? a b)
  (cond ((null? a) #f) ((< (car a) (car b)) #t) ((> (car a) (car b)) #f) (else (rdp-less? (cdr a) (cdr b)))))

(define (rdp-iterate tw f ytot r k)
  (if (= k 0)
      (list ytot r)
      (let* ((y (rs-nf (try (rdp-solve tw f r) (lambda (err) 0))))
             (r2 (if (rs-zero? y) r (rs-nf (list '+ r (list '* -1 (rs-deriv tw y)) (list '* -1 f y))))))
        (if (and (not (rs-zero? y)) (rdp-less? (rdp-measure tw r2) (rdp-measure tw r)))
            (rdp-iterate tw f (rs-nf (list '+ ytot y)) r2 (- k 1))
            (list ytot r)))))

(define (rs-rde-partial tw f g)
  (let* ((saved rs-rde-uncertain)
         (res (try (rdp-iterate tw f 0 (rs-nf g) 4) (lambda (err) (list 0 g)))))
    (set! rs-rde-uncertain saved)
    res))
