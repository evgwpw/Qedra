; risch/tan.lisp — тригонометрия в алгоритме Риша: вещественный tan-моном (Dθ = Du·(1 + θ²)), подшаг 21k″
;
; Источники — туториал Бронштейна ISSAC'98 §3.3, §3.7 (стр. 22–29), книга гл. 5.10, 6–8.
; Здесь — вещественный вариант tan-монома (башни tan эталонная схема не использует: идёт через exp(ix) над ℚ(i)).
;
; ---------- Преобразование тригонометрии (rs-trig-rewrite) ----------
; sin/cos/tan/cot/sec/csc с x в аргументе → рациональные функции θ = tan w. Все аргументы обязаны быть «кратны» первому:
; uⱼ = rⱼ·u₁ + eⱼ (rⱼ ∈ ℚ, eⱼ — константа); иначе — «не знаю» (независимость разных tan не проверяется). Q — НОК знаменателей rⱼ,
; w = u₁/(2Q), если есть sin/cos/sec/csc (половинный угол: sin u = 2θ/(1+θ²), cos u = (1−θ²)/(1+θ²)), иначе w = u₁/Q;
; кратные углы — (1 + iθ)ᵏ = aₖ + i·bₖ: sin kw = bₖ/(1+θ²)^{k/2}, cos kw = aₖ/(1+θ²)^{k/2} (k чётно), tan kw = bₖ/aₖ.
; Выражения строятся на символе-заместителе %tt (simplify превращает tan в sin/cos), в конце %tt → (tan w).
;
; ---------- Уровень tan (θ = tan b, Dθ = Db·(1+θ²), √−1 ∉ K) ----------
; Специальные многочлены — только a·(θ²+1)ᵐ (S = θ²+1). Дробь f = a/d = P + an/dn + as/Sᵐ (dn нормален):
;  1. normal: Эрмит (rs-hermite-normal), ЛРТ (константные вычеты, иначе неэлементарно); D(log S(α,θ)) имеет многочленную часть
;     степени 1 по θ — остаток rem = h − D(логарифмы) многочлен, он идёт в многочленную часть;
;  2. special: A/Sᵏ, A ≡ aθ + b (mod S): система (19) c′ − 2kDb·d = a, d′ + 2kDb·c = b, c, d ∈ K; нет решения — неэлементарно;
;     решение v = (cθ + d)/Sᵏ, (A − N)/S — на ступень ниже (k = 1 — в многочленную часть); система решается только над K = ℚ(x)
;     (анзац по ограниченным степеням, границы — по полюсам и порядку в ∞), над башнями — «не знаю»;
;  3. polynomial: степень e ≥ 2 понижается (Dp_e/((e−1)Db) θ^{e−1}); остаток r₁θ + r₀: r₁/Db обязано быть константой c
;     (∫ r₁θ = (c/2)·log S, иначе неэлементарно), r₀ — рекурсивно в K.
; Любое доказательство неэлементарности — ответ «целиком неэлементарно» (F = 0, R = f), без частичных ответов.
; tan разрешён только верхним уровнем башни и в единственном числе; рядом с atan — «не знаю» (atan(tan u) = u).

(module risch)

; ---------- преобразование тригонометрии ----------
(define rs-trig-names '(sin cos tan cot sec csc))
(define rs-tt '%tt)
(define (rs-trig-app? e) (and (pair? e) (member? (car e) rs-trig-names) (= (length e) 2)))
(define (rs-trig-apps e x)
  (if (not (pair? e))
      '()
      (let ((inner (apply append (map (lambda (a) (rs-trig-apps a x)) (cdr e)))))
        (if (and (rs-trig-app? e) (contains-sym? e x)) (cons e inner) inner))))

; (a_k b_k) = (1 + iθ)^k, k ≥ 0, на символе %tt
(define (rs-trig-ab k)
  (if (= k 0)
      (list 1 0)
      (let ((p (rs-trig-ab (- k 1))))
        (list (expand (list '+ (car p) (list '* -1 rs-tt (cadr p))))
              (expand (list '+ (cadr p) (list '* rs-tt (car p))))))))

(define (rs-trig-lcm l) (foldl (lambda (acc q) (lcm acc q)) 1 l))

; выражение (на %tt) для одного применения: head, k — целое кратное w, e — константный сдвиг
(define (rs-trig-one head k e)
  (let* ((kk (abs k)) (sg (if (< k 0) -1 1)) (ab (rs-trig-ab kk)) (a (car ab)) (b (list '* sg (cadr ab)))
         (den (if (= (remainder kk 2) 0)(list '^ (list '+ 1 (list '^ rs-tt 2)) (- 0 (/ kk 2))) 1))
         (S (list '* b den)) (C (list '* a den))
         (se (if (equal? e 0) 0 (list 'sin e))) (ce (if (equal? e 0) 1 (list 'cos e)))
         (S2 (if (equal? e 0) S (list '+ (list '* S ce) (list '* C se))))
         (C2 (if (equal? e 0) C (list '+ (list '* C ce) (list '* -1 S se))))
         (T (list '* b (list '^ a -1)))
         (T2 (if (equal? e 0) T (list '* (list '+ T (list 'tan e)) (list '^ (list '+ 1 (list '* -1 T (list 'tan e))) -1)))))
    (cond ((equal? head 'sin) S2)
          ((equal? head 'cos) C2)
          ((equal? head 'tan) T2)
          ((equal? head 'cot) (list '^ T2 -1))
          ((equal? head 'sec) (list '^ C2 -1))
          (else (list '^ S2 -1)))))

; (rs-trig-rewrite e x) → выражение без тригонометрии от x (появляется (tan w)); не-тригонометрическое выражение не меняется
(define (rs-trig-rewrite e x)
  (let ((apps (rs-unique (rs-trig-apps e x))))
    (if (null? apps)
        e
        (let* ((u1 (cadr (car apps))) (du1 (diff x u1))
               (rs (map (lambda (ap) (rs-ratio (diff x (cadr ap)) du1)) apps))
               (es (map2 (lambda (ap r) (simplify (expand (list '+ (cadr ap) (list '* -1 r u1))))) apps rs)))
          (cond ((any? (lambda (ap) (pair? (rs-trig-apps (cadr ap) x))) apps)
                 (rs-fail "вложенная тригонометрия — не знаю" e))
                ((not (every? (lambda (r) (and (rational-number? r) (not (equal? r 0)))) rs))
                 (rs-fail "аргументы тригонометрических функций не кратны друг другу — не знаю" e))
                ((not (every? (lambda (c) (x-free? c x)) es))
                 (rs-fail "аргументы тригонометрических функций отличаются неконстантой — не знаю" e))
                (else
                 (let* ((q (rs-trig-lcm (map denom rs)))
                        (half (any? (lambda (ap) (member? (car ap) '(sin cos sec csc))) apps))
                        (w (simplify (list '* (/ 1 (* q (if half 2 1))) u1)))
                        (th (list 'tan w))
                        (kmax (foldl max 0 (map (lambda (r) (abs (* r q (if half 2 1)))) rs)))
                        (shifted (any? (lambda (c) (not (equal? c 0))) es)))
                   (if (> kmax (if shifted 4 12))
                       (rs-fail "кратность угла слишком велика для tan-подстановки — не знаю" e))
                   (foldl (lambda (acc pr)
                            (replace-expr acc (car pr) (replace-expr (cadr pr) rs-tt th)))
                          e
                          (map2 (lambda (ap rc) (list ap (rs-trig-one (car ap) (* (car rc) q (if half 2 1)) (cadr rc))))
                                apps (map2 list rs es))))))))))

; ---------- башня: уровень tan ----------
(define (rs-tan-kernel st k a)
  (let ((tw (car st)))
    (if (any? (lambda (lv) (member? (rs-level-kind lv) '(tan atan))) (rs-levels tw))
        (rs-fail "второй tan/atan в башне — независимость не проверяется, не знаю" k)
        (let ((nl (rs-new-level st 'tan a))) (rs-st-map (car nl) k (cadr nl))))))

; ---------- система (19) над K = ℚ(x) ----------
(define (rs-tan-ord-at e x p) (rs-order-at (rs-from-expr e x) (rs-from-expr p x)))

; порядок полюса в ∞ как степень: deg числителя − deg знаменателя; 0 → #f
(define (rs-tan-rdeg e x)
  (if (rs-zero? e) #f (let ((tg (together e))) (- (degree (numer tg) x) (degree (denom tg) x)))))

; (Q степень-Q): знаменатель решения y = c + i·d: порядок полюса k = max(0, r − max(ν, 1)) в каждом неприводимом p
(define (rs-tan-poles x a b f)
  (let* ((da (denom (together a))) (db (denom (together b))) (df (denom (together f)))
         (fl (cdr (factor-list (simplify (list '* da db)))))
         (ps (filter (lambda (pm) (contains-sym? (car pm) x)) fl))
         (ks (map (lambda (pm)
                    (let* ((p (car pm))
                           (r (max (rs-tan-ord-at da x p) (rs-tan-ord-at db x p)))
                           (nu (rs-tan-ord-at df x p)))
                      (list p (max 0 (- r (max nu 1))))))
                  ps)))
    (list (if (null? ks) 1 (simplify (cons '* (map (lambda (pk) (list '^ (car pk) (cadr pk))) ks))))
          (foldl + 0 (map (lambda (pk) (* (cadr pk) (degree (car pk) x))) ks)))))

(define (rs-tan-syms name n) (map (lambda (i) (string->symbol (string-append name (to-string i)))) (range (+ n 1))))
(define (rs-tan-poly-of syms x)
  (cons '+ (map2 (lambda (s i) (list '* s (list '^ x i))) syms (range (length syms)))))

; c′ − f·d = a, d′ + f·c = b в ℚ(x): (c d) | none
(define (rs-tan-ansatz x f a b)
  (let* ((pl (rs-tan-poles x a b f)) (Q (car pl)) (dq (cadr pl))
         (al (filter (lambda (v) v) (list (rs-tan-rdeg a x) (rs-tan-rdeg b x))))
         (N (max 0 (+ 1 (foldl max (car al) al))))
         (n (+ dq N)) (cs (rs-tan-syms "%tc" n)) (ds (rs-tan-syms "%td" n)) (qs (append cs ds))
         (c (list '* (rs-tan-poly-of cs x) (list '^ Q -1)))
         (d (list '* (rs-tan-poly-of ds x) (list '^ Q -1)))
         (e1 (list '+ (diff x c) (list '* -1 f d) (list '* -1 a)))
         (e2 (list '+ (diff x d) (list '* f c) (list '* -1 b)))
         (rows (append-map (lambda (e)
                             (map (lambda (co) (rs-eq-row co qs))
                                  (filter (lambda (co) (not (rs-zero? co))) (rs-coeffs-all (numer (rs-nf e)) (list x)))))
                           (list e1 e2)))
         (sol (rs-gauss rows (length qs))))
    (if (not sol)
        'none
        (let* ((cv (simplify (list '* (rs-tan-poly-of (take sol (+ n 1)) x) (list '^ Q -1))))
               (dv (simplify (list '* (rs-tan-poly-of (drop sol (+ n 1)) x) (list '^ Q -1)))))
          (if (and (rs-zero? (list '+ (diff x cv) (list '* -1 f dv) (list '* -1 a)))
                   (rs-zero? (list '+ (diff x dv) (list '* f cv) (list '* -1 b))))
              (list cv dv)
              (rs-unknown "tan: решение системы не прошло проверку" (list a b)))))))

; R2.1: система (19) над башней = комплексное RDE; guard по размеру и кэш.
(define (rs-tan-expr-size e)
  (if (pair? e)
      (+ 1 (foldl + 0 (map rs-tan-expr-size (cdr e))))
      1))

(define (rs-tan-rde-guard? tw lo a b)
  (and (<= (length (rs-levels lo)) 1)
       (<= (rs-tan-expr-size a) 12)
       (<= (rs-tan-expr-size b) 12)))

(define rs-tan-solve-cache (make-hash))

(define (rs-tan-cache-key tw k a b)
  (list k (length (rs-levels (rs-lower tw)))
        (to-string (rs-level-arg (rs-top tw))) a b))

; ---------- точное разложение по i: e = A + B·i (i² = −1) ----------
; simplify не знает i² = −1 и не сокращает дроби с i в знаменателе, поэтому c и d из комплексного RDE
; берём как вещественную и мнимую части y, а не через (y ± ȳ)/2.
(define (rs-i-add p q) (cons (simplify (list '+ (car p) (car q))) (simplify (list '+ (cdr p) (cdr q)))))
(define (rs-i-mul p q)
  (cons (simplify (list '- (list '* (car p) (car q)) (list '* (cdr p) (cdr q))))
        (simplify (list '+ (list '* (car p) (cdr q)) (list '* (cdr p) (car q))))))
(define (rs-i-inv p)
  (let ((n (simplify (list '+ (list '^ (car p) 2) (list '^ (cdr p) 2)))))
    (cons (simplify (list '* (car p) (list '^ n -1)))
          (simplify (list '* -1 (cdr p) (list '^ n -1))))))
(define (rs-i-pow p n)
  (cond ((= n 0) (cons 1 0))
        ((< n 0) (rs-i-pow (rs-i-inv p) (- 0 n)))
        (else (rs-i-mul p (rs-i-pow p (- n 1))))))
; (A . B); '%i внутри функций (log, exp, …) не разбирается — останется в B, вызывающий это проверит
(define (rs-i-split e)
  (cond ((equal? e '%i) (cons 0 1))
        ((not (pair? e)) (cons e 0))
        ((equal? (car e) '+) (foldl rs-i-add (cons 0 0) (map rs-i-split (cdr e))))
        ((equal? (car e) '*) (foldl rs-i-mul (cons 1 0) (map rs-i-split (cdr e))))
        ((and (equal? (car e) '^) (integer? (caddr e))) (rs-i-pow (rs-i-split (cadr e)) (caddr e)))
        (else (cons e 0))))

(define (rs-tan-solve-rde tw lo f a b)
  (let ((r (try (rs-rde lo (rs-nf (list '* '%i f))
                        (rs-nf (list '+ a (list '* '%i b))))
                (lambda (e) #f))))
    (cond
      ((and (pair? r) (equal? (car r) 'ok))
       (let* ((y (cadr r)) (sp (rs-i-split y)) (c (car sp)) (d (cdr sp))
              (dc (rs-deriv lo c)) (dd (rs-deriv lo d)))
         (if (and (not (contains-sym? c '%i)) (not (contains-sym? d '%i))
                  (rs-zero? (list '+ dc (list '* -1 f d) (list '* -1 a)))
                  (rs-zero? (list '+ dd (list '* f c) (list '* -1 b))))
             (list c d)
             (rs-unknown "tan: решение RDE не прошло проверку" (list a b)))))
      ((and (pair? r) (equal? (car r) 'none)) 'none)
      (else #f))))

; (rs-tan-solve tw k a b) → (c d) | none | #f (не знаю)
(define (rs-tan-solve tw k a b)
  (let* ((lo (rs-lower tw)) (db (rs-deriv lo (rs-level-arg (rs-top tw))))
         (f (rs-nf (list '* 2 k db))))
    (cond ((and (rs-zero? a) (rs-zero? b)) (list 0 0))
          ((pair? (rs-levels lo))
           (if (not (rs-tan-rde-guard? tw lo a b))
               (rs-unknown "tan: система над башней вне бюджета" (list a b))
               (let* ((key (rs-tan-cache-key tw k a b))
                      (hit (hash-ref rs-tan-solve-cache key #f)))
                 (if hit
                     (car hit)
                     (let ((res (rs-tan-solve-rde tw lo f a b)))
                       (hash-set! rs-tan-solve-cache key (list res))
                       res)))))
          (else (rs-tan-ansatz (rs-tower-x tw) f a b)))))

; ---------- нормальная часть ----------
; ∫ hn/hd (hd унитарен, бесквадратен, нормален) → (L R poly) | #f; R — остаток (0 или неэлементарный, выражение), poly — многочлен K[θ]
(define (rs-tan-log-part tw hn hd)
  (let ((rr (rs-residue-reduce tw hn hd)) (th (rs-top-theta tw)))
    (cond ((not rr) #f)
          ((cadr rr)
           (let ((L (rs-log-part tw (car rr) rs-tv)))
             (if (contains-sym? L 'root-sum)
                 (rs-unknown "tan: вычеты — корни неприводимого Q без вещественной формы" hd)
                 (let ((rem (rs-nf (list '+ (rs-frac-expr tw (list hn hd)) (list '* -1 (rs-deriv tw L))))))
                   (if (contains-sym? (denom rem) th)
                       (rs-unknown "tan: остаток после логарифмической части не многочлен" rem)
                       (list L 0 (rs-from-expr rem th)))))))
          (else (let ((r (rs-int-log-part tw hn hd))) (list (car r) (cadr r) '()))))))

; ---------- специальная часть ----------
(define rs-tan-S (list 1 0 1))
(define (rs-tan-split d m)
  (let ((qr (rs-divmod d rs-tan-S)))
    (if (null? (cadr qr)) (rs-tan-split (car qr) (+ m 1)) (list m d))))
(define (rs-tan-ab r)
  (cond ((null? r) (list 0 0)) ((null? (cdr r)) (list 0 (car r))) (else (list (car r) (cadr r)))))

; A/Sᵏ → (F R P): F — выражение, R — 0 или неэлементарный остаток (выражение), P — многочлен K[θ] (добавка к многочленной части); #f — не знаю
(define (rs-tan-special tw k A Facc P)
  (if (or (= k 0) (null? A))
      (list (simplify (cons '+ Facc)) 0 P)
      (let* ((lo (rs-lower tw)) (th (rs-top-theta tw)) (db (rs-deriv lo (rs-level-arg (rs-top tw))))
             (ab (rs-tan-ab (rs-rem A rs-tan-S))) (sol (rs-tan-solve tw k (car ab) (cadr ab))))
        (cond ((not sol) #f)
              ((equal? sol 'none) (list (simplify (cons '+ Facc)) (rs-frac-expr tw (list A (rs-pow rs-tan-S k))) P))
              (else
               (let* ((c (car sol)) (dd (cadr sol)) (V (rs-trim (list c dd)))
                      (N (rs-add (rs-add (rs-trim (list (rs-deriv lo c) (rs-deriv lo dd)))
                                         (rs-scale rs-tan-S (rs-mulc c db)))
                                 (rs-scale (rs-shift V 1) (rs-nf (list '* (* -2 k) db)))))
                      (qr (rs-divmod (rs-sub A N) rs-tan-S)))
                 (if (not (null? (cadr qr)))
                     (rs-unknown "tan: числитель после вычитания Dv не делится на θ²+1" A)
                     (let ((Fv (rs-frac-expr tw (list V (rs-pow rs-tan-S k)))))
                       (if (= k 1)
                           (list (simplify (cons '+ (cons Fv Facc))) 0 (rs-add P (car qr)))
                           (rs-tan-special tw (- k 1) (car qr) (cons Fv Facc) P))))))))))

; ---------- многочленная часть ----------
(define (rs-tan-poly-reduce tw db P Facc)
  (if (< (rs-deg P) 2)
      (list P Facc)
      (let* ((e (rs-deg P)) (q (rs-nf (list '* (car P) (list '^ (list '* (- e 1) db) -1))))
             (Q (rs-shift (list q) (- e 1))) (P2 (rs-sub P (rs-deriv-poly tw Q))))
        (if (>= (rs-deg P2) e)
            (rs-unknown "tan: старший коэффициент многочлена не сократился" P)
            (rs-tan-poly-reduce tw db P2 (cons (rs-to-expr Q (rs-top-theta tw)) Facc))))))

; (F R) | ne | #f
(define (rs-tan-poly tw P)
  (let* ((lo (rs-lower tw)) (th (rs-top-theta tw)) (db (rs-deriv lo (rs-level-arg (rs-top tw))))
         (red (rs-tan-poly-reduce tw db P '())))
    (if (not red)
        #f
        (let* ((P2 (car red)) (r1 (if (>= (rs-deg P2) 1) (car P2) 0)) (r0 (if (null? P2) 0 (last P2)))
               (c (if (rs-zero? r1) 0 (rs-nf (list '* r1 (list '^ db -1))))))
          (if (not (rs-zero? (rs-deriv lo c)))
              'ne
              (let ((r0i (rs-int lo r0)))
                (and r0i
                     (list (simplify (cons '+ (cons (car r0i)
                                                    (cons (if (rs-zero? c) 0 (list '* c 1/2 (list 'log (list '+ 1 (list '^ th 2)))))
                                                          (cadr red)))))
                           (cadr r0i)))))))))

; ---------- R2.4 шаг 3: свёртка суммы логарифмов (только tan-башни) ----------
; слагаемое C·k·log(u) → (C k u), иначе #f (k — рациональное, C — общий нечисловой множитель)
(define (rs-lsum-term t)
  (let* ((fs (if (and (pair? t) (equal? (car t) '*)) (cdr t) (list t)))
         (lg (filter (lambda (f) (and (pair? f) (equal? (car f) 'log) (= (length f) 2))) fs)))
    (and (= (length lg) 1)
         (let* ((os (filter (lambda (f) (not (and (pair? f) (equal? (car f) 'log)))) fs))
                (num (filter number? os)) (sym (filter (lambda (f) (not (number? f))) os))
                (k (simplify (cons '* (cons 1 num))))
                (c (simplify (cons '* (cons 1 sym)))))
           (and (rational-number? k) (list c k (cadr (car lg))))))))

; C·Σkᵢ·log(uᵢ) → C·log(∏uᵢ^kᵢ) при общем C; иначе e не меняется
(define (rs-lsum e)
  (let* ((ts (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e)))
         (ls (map rs-lsum-term ts)))
    (if (or (< (length ls) 2)
            (not (every? (lambda (x) x) ls))
            (not (every? (lambda (x) (equal? (car x) (car (car ls)))) (cdr ls))))
        e
        (let* ((c (car (car ls)))
               (prod (simplify (cons '* (map (lambda (x) (list '^ (caddr x) (cadr x))) ls))))
               (lg (list 'log prod)))
          (simplify (if (equal? c 1) lg (list '* c lg)))))))

; log((1−θ²)/(1+θ²)) = log(cos 2w): θ-форма по многочленам и x-форма cos²w − sin²w
(define rs-cos-num '(-1 0 1))
(define rs-cos-den '(1 0 1))
(define (rs-cos-arg? u th w)
  (or (let* ((tg (together u)) (n (rs-from-expr (numer tg) th)) (d (rs-from-expr (denom tg) th)))
        (and (not (null? n)) (not (null? d))
             (null? (rs-sub (rs-mul n rs-cos-den) (rs-mul d rs-cos-num)))))
      (let ((tg (together u)))
        (and (equal? (denom tg) 1)
             (rs-zero? (list '- (numer tg)
                             (list '- (list '^ (list 'cos w) 2) (list '^ (list 'sin w) 2))))))))

(define (rs-tan-cos-log e th w)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'log) (= (length e) 2))
         (let ((u (cadr e)))
           (if (rs-cos-arg? u th w)
               (list 'log (simplify (list 'cos (list '* 2 w))))
               (list 'log (rs-tan-cos-log u th w)))))
        (else (cons (car e) (map (lambda (a) (rs-tan-cos-log a th w)) (cdr e))))))

; ---------- драйвер уровня tan ----------
; (rs-int-tan tw f) → (F R) | #f; доказанная неэлементарность — (0 f)
; ST.3д: шаг журнала — тангенс-уровень, нормальная и специальная части, результат
(define (rs-int-tan tw f)
  (let ((res (rs-int-tan-core tw f)))
    (if rs-log?
        (rs-note 'risch-tan "Алгоритм Риша: тангенс-уровень"
                 (string-append "θ = " (rs-mp-tower tw (rs-level-def (rs-top tw)))
                                "; Dθ = Du·(1 + θ²); нормальная часть знаменателя отделена от специальной (1 + θ²)^m"
                                (cond ((not res) "; не решено")
                                      ((equal? (car res) 0) "; остаток неэлементарен")
                                      (else "; редукция Эрмита и специальная часть дали ответ")))
                 (rs-th-subst tw f)
                 (cond ((not res) 'не-решено)
                       ((equal? (car res) 0) 'неэлементарно)
                       (else (rs-th-subst tw (car res))))))
    res))

(define (rs-int-tan-core tw f)
  (let* ((th (rs-top-theta tw)) (tg (together f))
         (a0 (rs-from-expr (numer tg) th)) (d0 (rs-from-expr (denom tg) th))
         (sp (rs-tan-split d0 0)) (m (car sp)) (dn0 (cadr sp))
         (c0 (rs-inv (car dn0))) (dn (rs-scale dn0 c0)) (a (rs-scale a0 c0))
         (ds (rs-pow rs-tan-S m)) (d (rs-mul ds dn))
         (qr (rs-divmod a d)) (r (cadr qr))
         (e (if (null? r) (list '() '()) (rs-diophantine ds dn r)))
         (an (car e)) (as (cadr e))
         (hm (if (and (pair? an) (> (rs-deg dn) 0))
                 (rs-hermite-normal tw an dn (list '() (list 1)))
                 (list (list '() (list 1)) (list '() (list 1)))))
         (g (rs-frac-cancel (car hm))) (h (cadr hm))
         (hq (rs-divmod (car h) (cadr h)))
         (gx (if (null? (car g)) 0 (rs-frac-expr tw g)))
         (hres (if (null? (cadr hq)) (list 0 0 '()) (rs-tan-log-part tw (cadr hq) (cadr h)))))
    (cond ((not hres) #f)
          ((not (rs-zero? (cadr hres))) (list 0 f))
          (else
           (let ((sres (rs-tan-special tw m as '() (rs-add (rs-add (car qr) (car hq)) (caddr hres)))))
             (cond ((not sres) #f)
                   ((not (rs-zero? (cadr sres))) (list 0 f))
                   (else
                    (let ((pres (rs-tan-poly tw (caddr sres))))
                      (cond ((not pres) #f)
                            ((equal? pres 'ne) (list 0 f))
                            (else (begin (rs-tan-note-used! tw)
                                         (list (simplify (list '+ gx (car hres) (car sres) (car pres)))
                                               (cadr pres)))))))))))))

; ---------- обратная подстановка ----------
; log(1+θ²) = −2·log cos w: до подстановки (simplify раскрывает tan в sin/cos и форма теряется)
(define (rs-tan-pre-tidy e table)
  (foldl (lambda (acc en)
           (let ((v (cadr en)))
             (if (and (pair? v) (equal? (car v) 'tan))
                 (replace-expr acc (list 'log (list '+ 1 (list '^ (car en) 2))) (list '* -2 (list 'log (list 'cos (cadr v)))))
                 acc)))
         e table))

; k = 1: tan w = sin 2w/(1+cos 2w); k = 2: tan w = (1−cos 2w)/sin 2w — без половинных углов в ответе
(define (rs-subst-tan-variant e table k)
  (simplify (foldl (lambda (acc en)
                     (let ((v (cadr en)))
                       (replace-expr acc (car en)
                                     (if (and (pair? v) (equal? (car v) 'tan))
                                         (let ((a2 (simplify (list '* 2 (cadr v)))))
                                           (if (= k 1)
                                               (list '* (list 'sin a2) (list '^ (list '+ 1 (list 'cos a2)) -1))
                                               (list '* (list '+ 1 (list '* -1 (list 'cos a2))) (list '^ (list 'sin a2) -1))))
                                         v))))
                   e table)))

; ---------- условие ветви и определённые интегралы ----------
; Ответ в tan(w) (w = половинный угол) разрывен там, где tan w бесконечен (cos w = 0): верен на интервалах. Определённый интеграл
; подстановкой пределов через такой F может дать неверное число (∫₀^{2π} dx/(2+cos x) → 0), поэтому int-definite-core
; (integrate/api.lisp) отказывается от ответов, полученных через tan-уровень (флаг ставит int-risch).
(define rs-tan-used #f)                                              ; расчёт прошёл через rs-int-tan и дал ответ
(define rs-tan-flag #f)                                              ; последний ответ стратегии int-risch использует tan-уровень
(define (rs-tan-flag?) rs-tan-flag)
(define (rs-tan-flag-clear!) (set! rs-tan-flag #f))
(define (rs-tan-note-used! tw)
  (set! rs-tan-used #t)
  (record-condition (list 'risch-tan-branch (rs-level-arg (rs-top tw)))
                    "risch: первообразная получена через tan(w); верна на интервалах, где cos w ≠ 0 (разрывы в нулях cos w)"))
