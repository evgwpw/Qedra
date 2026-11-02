; risch/rde.lisp — уравнение Риша Dy + f·y = g над башней exp-log: подшаг 21k.5
;
; Источники — Бронштейн, Symbolic Integration I, гл. 6 (RDE: слабый нормализатор, нормальный и специальный
; знаменатели, граница степени, SPDE, ветки сокращения). Здесь одна правая часть (не параметрическое РДУ);
; параметрическое РДУ — prde.lisp.
; Представление — field.lisp (многочлен K[θ] — список коэффициентов, старшая степень первой), дробь — пара (числитель знаменатель).
; База ℚ(x) — та же схема с «мономом» x: D x = 1, коэффициенты — константы.
;
; ---------- Исходы ----------
; (rs-rde tw f g) → (ok y) | (none причина) | (unknown причина); f, g, y — элементы K (выражения от x и θ башни tw).
;   none — ДОКАЗАНО: решения в K нет (граница степени, нормальный знаменатель, старшие члены, коэффициент уровнем ниже);
;   unknown — не решено (нужна параметрическая лог-производная / PRDE / is_log_deriv — подшаг 7, проверка не прошла).
; Внутри — raise (rde-none …)/(rde-unknown …). Если хоть одна граница взята без доказательства (флаг rs-rde-uncertain), то
; «нет решения» превращается в unknown: найденное решение остаётся верным (оно проверяется подстановкой), а отказ — нет.
;
; ---------- Схема (Бронштейн, гл. 6) ----------
; 1. Слабый нормализатор: вычеты f в простых нормальных множителях знаменателя — положительные целые m (корни резольвенты
;    res(a − z·Dd₁, d₁)) → p = НОД(a − m·Dd₁, d₁), f ← f − m·Dp/p, g ← p·g, y = z/p.
; 2. Нормальный знаменатель: y = q/h, h = НОД(e, e′)/НОД(p, p′) (e — нормальная часть знаменателя g, p = НОД(dₙ, e));
;    e ∤ dₙ·h² — решения нет. Уравнение a·Dq + b·q = c, a = dₙ·h — многочлен, у b, c знаменатели специальные.
; 3. Специальный знаменатель (exp): q = r·θ⁻ⁿ, n = min(0, ord c − min(0, ord b)); при ord b = 0 возможное сокращение —
;    n = min(n, m), где −b(0)/a(0) = Dv/v + m·Dη (параметрическая лог-производная, частный случай).
; 4. Граница степени (base / primitive / exp) — только если deg a > 0 (нужна SPDE); 5. SPDE (Ротштейн) понижает deg a до 0.
; 6. Dq + b·q = c: b «большой» (база, b ≠ 0, или deg b > 0) — старшие члены (SPDE1: цикл без границы, остаток ≠ 0 ⇒ нет
;    решения); deg b = 0 — покоэффициентная рекурсия уровнем ниже: exp — Dqⱼ + (b + j·Dη)·qⱼ = cⱼ (независимо по j);
;    primitive — сверху вниз Dqⱼ + b·qⱼ = cⱼ − (j+1)·Dθ·qⱼ₊₁ (единственность при отсутствии однородных решений; иначе —
;    21k.7b — параметрический спуск prde-degrade-prim со степени deg c + 1);
;    b = 0 — интегрирование в K (rs-int, результат обязан лежать в K).

(module risch)

(define rs-rde-uncertain #f)
(define rde-unbounded 1000000)                                       ; «граница не нужна» (deg a = 0 — SPDE её не проверяет)

(define (rde-none why) (raise (list 'rde-none why)))
(define (rde-unknown why) (raise (list 'rde-unknown why)))
(define (rde-uncertain!) (set! rs-rde-uncertain #t))

; ---------- уровень: «моном» θ (на базе — x), производная многочлена, Dη ----------
(define (rde-base? tw) (null? (rs-levels tw)))
(define (rde-theta tw) (if (rde-base? tw) (rs-tower-x tw) (rs-top-theta tw)))
(define (rde-dp tw p) (if (rde-base? tw) (rs-dtheta p) (rs-deriv-poly tw p)))
(define (rde-eta tw) (rs-deriv (rs-lower tw) (rs-level-arg (rs-top tw))))   ; exp: Dθ = Dη·θ

(define (rde-mono c k) (if (rs-zero? c) '() (rs-shift (list c) k)))   ; c·θᵏ
(define (rde-coef p j)                                               ; коэффициент при θʲ
  (if (or (< j 0) (> j (rs-deg p))) 0 (nth p (- (rs-deg p) j))))
(define (rde-ord-loop l n) (if (rs-zero? (car l)) (rde-ord-loop (cdr l) (+ n 1)) n))
(define (rde-ord p) (if (null? p) 'inf (rde-ord-loop (reverse p) 0)))    ; порядок в θ = 0

; специальная часть: exp — θᵏ, log и база — только константы. → (нормальная специальная)
(define (rde-split tw p)
  (if (equal? (rs-case tw) 'exp)
      (let ((s (rde-mono 1 (rde-ord p)))) (list (rs-quo p s) s))
      (list p (list 1))))

(define (rde-exact-quo p q)
  (let ((qr (rs-divmod p q)))
    (if (null? (cadr qr)) (car qr) (rde-unknown "внутренняя ошибка: деление не нацело"))))

; выражение ↔ дробь (числитель знаменатель), знаменатель унитарен
(define (rde-frac tw e)
  (let* ((th (rde-theta tw)) (tg (together e)))
    (rs-frac-cancel (list (rs-from-expr (numer tg) th) (rs-from-expr (denom tg) th)))))
(define (rde-fexpr tw fr)
  (let ((th (rde-theta tw)))
    (simplify (list '* (rs-to-expr (car fr) th) (list '^ (rs-to-expr (cadr fr) th) -1)))))

; формальная первообразная многочлена (база: Dq = c)
(define (rde-pint-loop l k acc)
  (if (null? l) (append (reverse acc) (list 0)) (rde-pint-loop (cdr l) (- k 1) (cons (rs-mulc (car l) (/ 1 (+ k 1))) acc))))
(define (rde-pint p) (if (null? p) '() (rde-pint-loop p (rs-deg p) '())))

; интеграл нижнего уровня без заметок в журнал шагов (заметки — только у внешнего уровня)
(define (rs-int-quiet tw e)
  (let ((old rs-log?))
    (set! rs-log? #f)
    (unwind-protect (rs-int tw e) (set! rs-log? old))))

; ---------- 1. слабый нормализатор (эталонная схема weak_normalizer) ----------
; положительные целые корни многочлена r(z) (список коэффициентов): линейные множители factor-list с целым корнем
(define (rde-int-roots tw r)
  (let* ((e (together (rs-to-expr r rs-z)))
         (fl (try (cdr (factor-list (numer e))) (lambda (err) (rde-uncertain!) '()))))
    (filter (lambda (m) m)
            (map (lambda (fm)
                   (let ((f (car fm)))
                     (and (equal? (degree f rs-z) 1)
                          (let ((root (rs-nf (list '* -1 (coeff f rs-z 0) (list '^ (coeff f rs-z 1) -1)))))
                            (and (integer? root) (> root 0) root)))))
                 fl))))

; f = fa/fd → ((p m) …): f − Σ m·Dp/p слабо нормализовано
(define (rde-weak tw fa fd)
  (let ((d (car (rde-split tw fd))))
    (if (< (rs-deg d) 1)
        '()
        (let* ((g (rs-gcd d (rs-dtheta d))) (d0 (rs-quo d g)) (d1 (rs-quo d0 (rs-gcd d0 g))))
          (if (< (rs-deg d1) 1)
              '()
              (let* ((st (rs-diophantine (rs-quo fd d1) d1 fa)) (a (car st)) (dd1 (rde-dp tw d1))
                     (res (rs-resultant d1 (rs-sub a (rs-scale dd1 rs-z)))))
                (if (rs-zero? res)
                    (begin (rde-uncertain!) '())
                    (map (lambda (m) (list (rs-gcd (rs-sub a (rs-scale dd1 m)) d1) m))
                         (rde-int-roots tw (rs-from-expr res rs-z))))))))))

(define (rde-sub-logd tw fr wn)                                      ; f − Σ m·Dp/p
  (foldl (lambda (acc pm) (rs-frac-cancel (rs-frac-add acc (list (rs-scale (rde-dp tw (car pm)) (- 0 (cadr pm))) (car pm)))))
         fr wn))

; ---------- 2. нормальный знаменатель (эталонная схема normal_denom/get_denom) ----------
; → (a (ba bd) (ca cd) h): y = q/h, a·Dq + b·q = c
(define (rde-normal-denom tw fa fd ga gd)
  (let* ((dn (car (rde-split tw fd))) (en (car (rde-split tw gd)))
         (p (rs-gcd dn en))
         (h (rs-quo (rs-gcd en (rs-dtheta en)) (rs-gcd p (rs-dtheta p))))
         (a (rs-mul dn h)) (c (rs-mul a h)))
    (if (not (null? (rs-rem c en))) (rde-none "нормальный знаменатель: знаменатель g не делит a·h — у y лишний полюс"))
    (list a
          (rs-frac-cancel (list (rs-sub (rs-mul a fa) (rs-mul dn (rs-mul (rde-dp tw h) fd))) fd))
          (rs-frac-cancel (list (rs-mul c ga) gd))
          h)))

; ---------- параметрическая лог-производная (R2.2 — общий случай в базе) ----------
; целое m: α = Dv/v + m·η (v ∈ K₀) — кандидат для границы (лишний кандидат безопасен: граница только шире);
; #f — такого m нет (доказано) или не решено (тогда флаг). m единственно: иначе exp((m−m′)η) ∈ K₀.
;
; R2.2: v — не только моном. В базе ℚ(x) Dv/v — правильная дробь с ПРОСТЫМИ полюсами, вычеты в которых — целые
; (кратности множителей v); поэтому полиномиальная часть α равна m·(полиномиальная часть η), а все вычеты α − m·η целые.
; Обратно, по целым вычетам nᵢ строится v = ∏pᵢ^{nᵢ} и проверяется подстановкой.
(define (rde-frac-parts e x)                                         ; → (полиномиальная часть остаток знаменатель)
  (let* ((tg (together e)) (n (rs-from-expr (numer tg) x)) (d (rs-from-expr (denom tg) x))
         (qr (rs-divmod n d)))
    (list (car qr) (cadr qr) d)))

(define (rde-plogd-m-of pa pe eta)
  (cond ((not (null? pa))
         (if (null? pe)
             #f                                                      ; полиномиальной части у η нет — решения нет
             (let ((qr (rs-divmod pa pe)))
               (cond ((or (not (null? (cadr qr))) (not (= (rs-deg (car qr)) 0))) #f)
                     ((not (rational-number? (car (car qr)))) (rde-uncertain!) #f)
                     ((integer? (car (car qr))) (car (car qr)))
                     (else #f)))))
        ((null? pe) (if (rs-zero? eta) 0 (begin (rde-uncertain!) #f)))
        (else 0)))                                                   ; m·pe даёт нулевую полиномиальную часть ⇒ m = 0

; вычет α = a/d в неприводимом p (d = p·q): a·(q·p′)⁻¹ mod p; 'no — вычет не рационален
(define (rde-residue-at a q p x)
  (let* ((qq (rs-rem (rs-mul q (rs-deriv-poly (rs-tower x) p)) p))
         (g (rs-gcdex qq p)))
    (if (not (= (rs-deg (caddr g)) 0))
        'no
        (let ((rp (rs-rem (rs-scale (rs-mul a (car g)) (rs-inv (car (caddr g)))) p)))
          (if (> (rs-deg rp) 0) 'no (if (null? rp) 0 (car rp)))))))

; ((p n) …) — целые вычеты, 'no — v ∈ ℚ(x) нет (доказано), 'uncertain — вычет не число
(define (rde-log-deriv-residues a d x)
  (let loop ((fs (cdr (factor-list (rs-to-expr d x)))) (acc '()))
    (if (null? fs)
        acc
        (let* ((ex (car (car fs))) (e (cadr (car fs))) (p (rs-from-expr ex x)))
          (cond ((not (= e 1)) 'no)                                  ; у Dv/v полюсы только простые
                ((not (= (rs-deg (rs-gcd (rs-quo d p) p)) 0)) 'no)
                (else
                 (let ((n (rde-residue-at a (rs-quo d p) p x)))
                   (cond ((equal? n 'no) 'no)
                         ((not (rational-number? n)) 'uncertain)
                         ((not (integer? n)) 'no)
                         (else (loop (cdr fs) (cons (cons p n) acc)))))))))))

; α = Dv/v + m·η в ℚ(x) → (m v) | #f
(define (rde-log-deriv-base alpha eta x)
  (let* ((pa (car (rde-frac-parts alpha x))) (pe (car (rde-frac-parts eta x)))
         (m (rde-plogd-m-of pa pe eta)))
    (and m
         (let* ((ap (rs-nf (list '- alpha (list '* m eta))))
                (parts (rde-frac-parts ap x)) (pp (car parts)) (a (cadr parts)) (d (caddr parts))
                (res (and (null? pp) (rde-log-deriv-residues a d x))))
           (and (pair? res)
                (let ((ve (simplify (cons '* (cons 1 (map (lambda (pn) (list '^ (rs-to-expr (car pn) x) (cdr pn))) res))))))
                  (and (rs-zero? (rs-nf (list '- alpha (list '+ (list '* m eta)
                                                             (list '* (diff x ve) (list '^ ve -1))))))
                       (list m ve))))))))

(define (rde-plogd-base lo alpha eta)                                ; K₀ = ℚ(x): v — любая рациональная функция
  (let ((r (rde-log-deriv-base alpha eta (rs-tower-x lo))))
    (and r (car r))))
; Шаг 21k.6: v — моном нижней башни, v = x^kₓ·∏θⱼ^kⱼ: Dv/v = kₓ/x + Σ kⱼ·wⱼ (wⱼ = Dηⱼ для exp, Dθⱼ/θⱼ для log).
; Линейная система α = m·η + kₓ/x + Σ kⱼwⱼ над константами (rs-gauss): совместна с целыми m, kₓ, kⱼ — m; несовместна или
; дробное решение — не доказано (флаг). Так берутся башни высоты 3 (eˣe^{eˣ}e^{e^{eˣ}}: α = −1 − θ₁ = −Dη₁ − η₂ → m = −1).
(define (rde-plogd-monomial lo alpha eta)
  (let* ((lvs (rs-rel-levels lo)) (n (+ 2 (length lvs)))
         (qs (map (lambda (i) (string->symbol (string-append "%pq" (to-string i)))) (range n)))
         (ws (cons eta (cons (list '^ (rs-tower-x lo) -1)
                             (map (lambda (lv) (if (equal? (rs-level-kind lv) 'exp)
                                                   (rs-deriv lo (rs-level-arg lv))
                                                   (list '* (rs-level-dtheta lv) (list '^ (car lv) -1))))
                                  lvs))))
         (e (rs-nf (cons '+ (cons alpha (map2 (lambda (q w) (list '* -1 q w)) qs ws)))))
         (eqs (filter (lambda (c) (not (rs-zero? c))) (rs-coeffs-all (numer e) (rs-vars lo))))
         (sol (rs-gauss (map (lambda (c) (rs-eq-row c qs)) eqs) n)))
    (cond ((and sol (every? integer? sol)) (car sol))
          (else (rde-uncertain!) #f))))
(define (rde-plogd lo alpha eta)
  (let ((r (rs-ratio alpha eta)))
    (cond ((rs-const? r lo) (and (integer? r) r))                    ; параметры — генерически не целое
          ((rde-base? lo) (rde-plogd-base lo alpha eta))
          (else (rde-plogd-monomial lo alpha eta)))))

; ограниченное интегрирование (primitive, deg b = deg a − 1): α = Dz + m·Dθ, m ∈ ℤ → m | #f
; (21k.7a) быстрый путь не решил — ограниченное интегрирование (prde.lisp): m = c, none — доказано (без флага)
(define (rde-limited-full tw alpha)
  (let ((lr (rs-limited-integrate (rs-lower tw) alpha (list (rs-level-dtheta (rs-top tw))))))
    (cond ((equal? (car lr) 'ok) (let ((m (car (caddr lr)))) (and (integer? m) m)))
          ((equal? (car lr) 'none) #f)
          (else (rde-uncertain!) #f))))
(define (rde-limited tw alpha)
  (let* ((lo (rs-lower tw)) (r (rs-int-quiet lo alpha)))
    (cond ((not r) (rde-limited-full tw alpha))
          ((not (equal? (cadr r) 0)) #f)
          (else (let ((sp (rs-split-logs (car r) tw)))
                  (cond ((not sp) (rde-limited-full tw alpha))
                        ((integer? (cadr sp)) (cadr sp))
                        (else #f)))))))

; ---------- 3. специальный знаменатель (exp; эталонная схема special_denom/do_SPDE_exp) ----------
(define (rde-poly-of fr)                                             ; знаменатель — константа из K
  (if (> (rs-deg (cadr fr)) 0)
      (rde-unknown "внутренняя ошибка: специальный знаменатель на уровне без специальных многочленов")
      (rs-scale (car fr) (rs-inv (car (cadr fr))))))

; −b(0)/a(0) = Dv/v + m·η → n = min(n, m)
(define (rde-cancel-lower tw a ba bd n)
  (let* ((alpha (rs-nf (list '* -1 (rde-coef ba 0) (list '^ (list '* (rde-coef bd 0) (rde-coef a 0)) -1))))
         (m (rde-plogd (rs-lower tw) alpha (rde-eta tw))))
    (if m (min n m) n)))

; → (A B C hs): q = r/hs, A·Dr + B·r = C — многочлены
(define (rde-special-denom tw a bf cf)
  (if (not (equal? (rs-case tw) 'exp))
      (list a (rde-poly-of bf) (rde-poly-of cf) (list 1))
      (let* ((ba (car bf)) (bd (cadr bf)) (ca (car cf)) (cd (cadr cf))
             (nb (if (null? ba) 'inf (- (rde-ord ba) (rde-ord bd))))
             (nc (- (rde-ord ca) (rde-ord cd)))
             (n0 (min 0 (- nc (if (equal? nb 'inf) 0 (min 0 nb)))))
             (n (if (equal? nb 0) (rde-cancel-lower tw a ba bd n0) n0))
             (N (max 0 (max (if (equal? nb 'inf) 0 (- 0 nb)) (- n nc))))
             (tN (rde-mono 1 N)) (aN (rs-mul a tN)))
        (list aN
              (rs-add (rde-exact-quo (rs-mul ba tN) bd) (rs-scale aN (rs-mulc n (rde-eta tw))))
              (rde-exact-quo (rs-mul ca (rde-mono 1 (- N n))) cd)
              (rde-mono 1 (- 0 n))))))

; ---------- 4. граница степени (эталонная схема bound_degree / do_SPDE_prim / exp_upper_bound) ----------
; (21k.7b) primitive, deg b = deg a = d > 0 (эталонная схема do_SPDE_prim): у решения степени n выше границы старшие члены
; сокращаются: lc(a)·Dqₙ + lc(b)·qₙ = 0 и (коэффициент при θⁿ⁺ᵈ⁻¹) Du + n·Dθ = f₁, u = qₙ₋₁/qₙ, f₁ = −lc(b₁)/lc(a),
; b₁ = b − (lc b/lc a)·a. Отсюда n — целое m из ограниченного интегрирования f₁ = Dz + m·Dθ; deg b₁ < d − 1 ⇒ Du = −n·Dθ,
; т. е. n = 0 (θ трансцендентен) — кандидата нет. Раньше здесь был флаг «не доказано».
(define (rde-bound-prim-eq tw a b)
  (let* ((f0 (rs-nf (list '* -1 (rs-lc b) (list '^ (rs-lc a) -1))))
         (b1 (rs-add b (rs-scale a f0))))
    (and (= (rs-deg b1) (- (rs-deg a) 1))
         (rde-limited tw (rs-nf (list '* -1 (rs-lc b1) (list '^ (rs-lc a) -1)))))))

(define (rde-bound tw a b c) (rde-bound-d tw a b (rs-deg c)))
; (21k.7b) граница по deg c = dc (для параметрического случая — максимум по правым частям)
(define (rde-bound-d tw a b dc)
  (let* ((da (rs-deg a)) (db (rs-deg b)) (cs (rs-case tw))
         (alpha (lambda () (rs-nf (list '* -1 (rs-lc b) (list '^ (rs-lc a) -1))))))
    (cond ((equal? cs 'base)
           (let ((n (max 0 (- dc (max db (- da 1))))))
             (if (and (>= db 0) (= db (- da 1)))
                 (let ((al (alpha))) (if (integer? al) (max n al) n))
                 n)))
          ((equal? cs 'primitive)
           (let ((n (if (> db da) (max 0 (- dc db)) (max 0 (+ (- dc da) 1)))))
             (cond ((and (>= db 0) (= db (- da 1))) (let ((m (rde-limited tw (alpha)))) (if m (max n m) n)))
                   ((= db da) (let ((m (rde-bound-prim-eq tw a b))) (if m (max n m) n)))
                   (else n))))
          (else
           (let ((n (max 0 (- dc (max db da)))))
             (if (= db da)
                 (let ((m (rde-plogd (rs-lower tw) (alpha) (rde-eta tw)))) (if m (max n m) n))
                 n))))))

; ---------- 5. SPDE (Ротштейн): a·Dq + b·q = c, deg q ≤ n → (b c n α β), q = α·r + β, Dr + b·r = c ----------
(define (rde-spde tw a b c n alpha beta)
  (cond ((null? c) (list '() '() 0 '() beta))
        ((< n 0) (rde-none "SPDE: граница степени отрицательна"))
        (else
         (let ((g (rs-gcd a b)))
           (if (not (null? (rs-rem c g))) (rde-none "SPDE: НОД(a, b) не делит c"))
           (let ((a1 (rs-quo a g)) (b1 (rs-quo b g)) (c1 (rs-quo c g)))
             (if (= (rs-deg a1) 0)
                 (let ((ia (rs-inv (car a1)))) (list (rs-scale b1 ia) (rs-scale c1 ia) n alpha beta))
                 (let ((rz (rs-diophantine b1 a1 c1)))                ; r·b + z·a = c, deg r < deg a
                   (if (not rz) (rde-unknown "SPDE: диофантово уравнение не решилось"))
                   (rde-spde tw a1 (rs-add b1 (rde-dp tw a1)) (rs-sub (cadr rz) (rde-dp tw (car rz))) (- n (rs-deg a1))
                             (rs-mul alpha a1) (rs-add beta (rs-mul alpha (car rz)))))))))))

; ---------- 6. Dq + b·q = c ----------
; b «большой»: старший член q определён однозначно (deg Dq < deg b·q); остаток степени < deg b — решения нет
(define (rde-spde1-loop tw b c q)
  (if (null? c)
      q
      (let ((k (- (rs-deg c) (rs-deg b))))
        (if (< k 0) (rde-none "старшие члены: deg c < deg b — многочлена-решения нет"))
        (let* ((qq (rde-mono (rs-mulc (rs-lc c) (rs-inv (rs-lc b))) k))
               (c2 (rs-sub c (rs-add (rs-mul b qq) (rde-dp tw qq)))))
          (if (>= (rs-deg c2) (rs-deg c)) (rde-unknown "старшие члены не сократились"))
          (rde-spde1-loop tw b c2 (rs-add q qq))))))

; y ∈ K с Dy = g: ∫ g уровнем tw обязан быть элементом K (логарифмы элементов K заменяются на θ)
; (21k.7a) быстрый путь не решил — ограниченное интегрирование с пустым списком (is_deriv_in_field): g = Dv, v ∈ K
(define (rde-integrate-limited tw g why)
  (let ((lr (rs-limited-integrate tw g '())))
    (cond ((equal? (car lr) 'ok) (simplify (cadr lr)))
          ((equal? (car lr) 'none) (rde-none "g не является производной элемента K (ограниченное интегрирование)"))
          (else (rde-unknown why)))))
(define (rde-integrate-in tw g)
  (let ((r (rs-int-quiet tw g)))
    (cond ((not r) (rde-integrate-limited tw g "∫ g в K: алгоритм не решил"))
          ((not (equal? (cadr r) 0)) (rde-none "∫ g неэлементарен — решения в K нет"))
          (else
           (let ((F (if (rde-base? tw) (car r) (rs-subst-logs (car r) tw))))
             (if (rs-nonconst-log? F tw)
                 (rde-integrate-limited tw g "∫ g содержит логарифмы, ограниченное интегрирование не решило")
                 (simplify F)))))))

(define (rde-integrate-poly tw c)
  (let* ((th (rde-theta tw)) (y (rde-integrate-in tw (rs-to-expr c th))))
    (if (contains-sym? (denom (together y)) th)
        (rde-unknown "∫ c в K не многочлен по θ")
        (rs-from-expr y th))))

; exp, deg b = 0: Dqⱼ + (b + j·Dη)·qⱼ = cⱼ — уравнения по j независимы
(define (rde-degrade-exp tw b0 c)
  (let ((lo (rs-lower tw)) (eta (rde-eta tw)))
    (rs-trim (map (lambda (j)
                    (let ((cj (rde-coef c j)))
                      (if (rs-zero? cj) 0 (rde-solve lo (rs-nf (list '+ b0 (list '* j eta))) cj))))
                  (reverse (range (+ (rs-deg c) 1)))))))

; у Dy + b₀·y = 0 нет ненулевых решений в K₀ (доказано): только база — ∫ b₀ неэлементарен или рационален и не константа
(define (rde-hom-free? lo b0)
  (and (rde-base? lo)
       (let ((r (rs-int-quiet lo (rs-nf (list '* -1 b0)))))
         (and r (or (not (equal? (cadr r) 0))
                    (and (not (rs-nonconst-log? (car r) lo)) (not (rs-const? (car r) lo))))))))

; primitive, deg b = 0: сверху вниз Dqⱼ + b₀·qⱼ = cⱼ − (j+1)·Dθ·qⱼ₊₁
(define (rde-degrade-prim-loop tw b0 c j qprev acc)
  (if (< j 0)
      (rs-trim (reverse acc))
      (let* ((rhs (rs-nf (list '+ (rde-coef c j) (list '* -1 (+ j 1) (rs-level-dtheta (rs-top tw)) qprev))))
             (qj (if (rs-zero? rhs) 0 (rde-solve (rs-lower tw) b0 rhs))))
        (rde-degrade-prim-loop tw b0 c (- j 1) qj (cons qj acc)))))
; (21k.7b) однородные решения не исключены (вне базы): сначала прежний цикл (его решение верно и форма ответа прежняя), при
; неудаче — параметрический спуск prde-degrade-prim (prde.lisp) со степени deg c + 1: однородное решение w уровня ниже входит
; в базис и учитывается как параметр (Бронштейн; do_SPDE_prim0 — там этот случай «need transform»). Был флаг.
(define (rde-degrade-prim-param tw b0 c)
  (let* ((saved rs-rde-uncertain)
         (old (try (list 'ok (rde-degrade-prim-loop tw b0 c (rs-deg c) 0 '())) (lambda (err) #f))))
    (if old
        (cadr old)
        (begin
          (set! rs-rde-uncertain saved)
          (let ((s (rs-first (lambda (s) (and (not (rs-zero? (car (cadr s)))) s)) (prde-degrade-prim tw b0 (list c)))))
            (if s
                (rs-scale (car s) (rs-inv (car (cadr s))))
                (rde-none "покоэффициентный спуск (с однородными решениями): решения нет")))))))
(define (rde-degrade-prim tw b0 c)
  (cond ((rs-zero? b0) (rde-integrate-poly tw c))
        ((rde-hom-free? (rs-lower tw) b0) (rde-degrade-prim-loop tw b0 c (rs-deg c) 0 '()))
        (else (rde-degrade-prim-param tw b0 c))))

(define (rde-poly-solve tw b c)
  (cond ((null? c) '())
        ((rde-base? tw) (if (null? b) (rde-pint c) (rde-spde1-loop tw b c '())))
        ((and (not (null? b)) (> (rs-deg b) 0)) (rde-spde1-loop tw b c '()))
        ((equal? (rs-case tw) 'exp) (rde-degrade-exp tw (if (null? b) 0 (car b)) c))
        (else (rde-degrade-prim tw (if (null? b) 0 (car b)) c))))

; ---------- rischDE ----------
(define (rde-solve tw f g)
  (cond ((rs-zero? g) 0)
        ((rs-zero? f) (rde-integrate-in tw g))
        (else
         (let* ((fr (rde-frac tw f)) (gr (rde-frac tw g))
                (wn (rde-weak tw (car fr) (cadr fr)))
                (P (rs-prod-factors wn))
                (fr1 (rde-sub-logd tw fr wn))
                (gr1 (rs-frac-cancel (list (rs-mul P (car gr)) (cadr gr))))
                (nd (rde-normal-denom tw (car fr1) (cadr fr1) (car gr1) (cadr gr1)))
                (sd (rde-special-denom tw (car nd) (cadr nd) (caddr nd)))
                (A (car sd)) (B (cadr sd)) (C (caddr sd))
                (n (if (> (rs-deg A) 0) (rde-bound tw A B C) rde-unbounded))
                (sp (rde-spde tw A B C n (list 1) '()))
                (q (rde-poly-solve tw (car sp) (cadr sp)))
                (y (rde-fexpr tw (list (rs-add (rs-mul (nth sp 3) q) (nth sp 4))
                                       (rs-mul P (rs-mul (nth nd 3) (nth sd 3)))))))
           (if (rs-zero? (list '+ (rs-deriv tw y) (list '* f y) (list '* -1 g)))
               y
               (rde-unknown "проверка решения подстановкой не прошла"))))))

; (rs-rde tw f g) → (ok y) | (none причина) | (unknown причина)
(define (rs-rde tw f g)
  (let ((saved rs-rde-uncertain))
    (set! rs-rde-uncertain #f)
    (let* ((r (try (list 'ok (rde-solve tw f g))
                   (lambda (err)
                     (let ((d (error-data err)))
                       (cond ((and (pair? d) (equal? (car d) 'rde-none)) (list 'none (cadr d)))
                             ((and (pair? d) (equal? (car d) 'rde-unknown)) (list 'unknown (cadr d)))
                             (else (list 'unknown (string-append "ошибка: " (error-message err)))))))))
           (unc rs-rde-uncertain))
      (set! rs-rde-uncertain saved)
      (cond ((equal? (car r) 'ok) r)
            ((and (equal? (car r) 'none) (not unc)) r)
            ((equal? (car r) 'none)
             (list 'unknown (string-append "граница взята без доказательства (параметрическая лог-производная / PRDE — подшаг 7); " (cadr r))))
            (else r)))))
