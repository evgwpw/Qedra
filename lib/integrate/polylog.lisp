; polylog.lisp — интегралы через полилогарифм Li_s и функцию Ламберта W (шаг PL)
;
; Стратегия int-polylog (c — множитель без x; u = k·xⁿ, k без x, n рациональное ≠ 0):
;   ∫ c·log(1 + u)/x dx       = −(c/n)·Li₂(−u)                       (log(1 − a t)/t → −Li₂(a t))
;   ∫ c·atanh(u)/x dx         = (c/(2n))·(Li₂(u) − Li₂(−u))
;   ∫ c·Li_s(u)/x dx          = (c/n)·Li_{s+1}(u)
;   ∫ c·log(x)/(1 − x) dx     = c·Li₂(1 − x)       (и log(x)/(x − 1) → −c·Li₂(1 − x))
;   ∫ c·W(a·x + b) dx         = (c/a)·(u·(W − 1) + e^W) = (c/a)·u·(W − 1 + 1/W),  u = a·x + b  (W·e^W = u)
;   ∫ c·W(a·x)/x dx          = c·(W + W²/2)
; Сумма почленно (c·(a + b·atanh(k x²))/x) раскрывается каскадом (int-linear/int-expand). Ответ выдаётся только после
; проверки дифференцированием (int-check; остатки (diff u v) двуарной головы polylog вычисляет int-diff через pl-resolve).
; Без проверки или при x вне допущений ответ не выдаётся. Внутренние имена: ipl-.

(module integrate
  (export))

; разбор множителей: (c vs) — c без x, vs — множители с x
(define (ipl-split e x)
  (let* ((s (simplify e))
         (fs (if (and (pair? s) (equal? (car s) '*)) (cdr s) (list s)))
         (cs (filter (lambda (f) (x-free? f x)) fs))
         (vs (filter (lambda (f) (not (x-free? f x))) fs)))
    (list (if (null? cs) 1 (simplify (cons '* cs))) vs)))

(define (ipl-xpow f x)       ; f = x^n (n число ≠ 0) → n | #f
  (cond ((equal? f x) 1)
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3) (equal? (cadr f) x) (number? (caddr f))
              (not (equal? (caddr f) 0)))
         (caddr f))
        ((and (pair? f) (equal? (car f) 'sqrt) (= (length f) 2) (equal? (cadr f) x)) 1/2)
        (else #f)))

; u = k·xⁿ → (k n) | #f
(define (ipl-kxn u x)
  (cond ((x-free? u x) #f)
        ((ipl-xpow u x) (list 1 (ipl-xpow u x)))
        ((and (pair? u) (equal? (car u) '*))
         (let ((vs (filter (lambda (f) (not (x-free? f x))) (cdr u)))
               (cs (filter (lambda (f) (x-free? f x)) (cdr u))))
           (and (= (length vs) 1) (ipl-xpow (car vs) x)
                (list (simplify (cons '* cs)) (ipl-xpow (car vs) x)))))
        (else #f)))

(define (ipl-head? f h n) (and (pair? f) (equal? (car f) h) (= (length f) n)))
(define (ipl-inv-x? f x) (and (pair? f) (equal? (car f) '^) (= (length f) 3) (equal? (cadr f) x) (equal? (caddr f) -1)))

(define (ipl-u k n x) (simplify (list '* k (list '^ x n))))
(define (ipl-neg e) (simplify (list '* -1 e)))
(define (ipl-li s u) (list 'polylog s u))

; ответ для c·h(u)/x
(define (ipl-over-x c h x)
  (cond ((ipl-head? h 'log 2)
         (let ((w (cadr h)))
           (and (ipl-head? w '+ 3) (equal? (cadr w) 1)
                (let ((p (ipl-kxn (caddr w) x)))
                  (and p (let ((u (ipl-u (car p) (cadr p) x)))
                           (simplify (list '* c (/ -1 (cadr p)) (ipl-li 2 (ipl-neg u))))))))))
        ((ipl-head? h 'atanh 2)
         (let ((p (ipl-kxn (cadr h) x)))
           (and p (let ((u (ipl-u (car p) (cadr p) x)))
                    (simplify (list '* c (/ 1 (* 2 (cadr p))) (list '+ (ipl-li 2 u) (list '* -1 (ipl-li 2 (ipl-neg u))))))))))
        ((and (ipl-head? h 'polylog 3) (x-free? (cadr h) x))
         (let ((p (ipl-kxn (caddr h) x)))
           (and p (simplify (list '* c (/ 1 (cadr p)) (ipl-li (simplify (list '+ (cadr h) 1)) (caddr h)))))))
        ((ipl-head? h 'lambert_w 2)
         (let ((p (ipl-kxn (cadr h) x)))
           (and p (equal? (cadr p) 1)
                (let ((w h)) (simplify (list '* c (list '+ w (list '* 1/2 (list '^ w 2)))))))))
        (else #f)))

; log(x)/(1 − x), log(x)/(x − 1)
(define (ipl-log-over-one-minus c vs x)
  (and (= (length vs) 2)
       (let ((lg (filter (lambda (f) (equal? f (list 'log x))) vs))
             (dn (filter (lambda (f) (and (pair? f) (equal? (car f) '^) (equal? (caddr f) -1))) vs)))
         (and (= (length lg) 1) (= (length dn) 1)
              (let ((q (cadr (car dn))) (one-minus (list '+ 1 (list '* -1 x))) (minus-one (list '+ -1 x)))
                (cond ((equal? q one-minus) (simplify (list '* c (ipl-li 2 (simplify (list '+ 1 (list '* -1 x)))))))
                      ((equal? q minus-one) (simplify (list '* -1 c (ipl-li 2 (simplify (list '+ 1 (list '* -1 x)))))))
                      (else #f)))))))

; c·W(u), u = a·x + b (линейно)
(define (ipl-lambert c vs x)
  (and (= (length vs) 1) (ipl-head? (car vs) 'lambert_w 2)
       (let ((u (simplify (cadr (car vs)))))
         (and (polynomial? u x) (= (degree u x) 1)
              (let ((a (simplify (coeff u x 1))))
                (and (x-free? a x) (not (equal? a 0))
                     (let ((w (car vs)))
                       ; u(W − 1 + 1/W) = u(W − 1) + e^W (W·e^W = u): без деления на W, чтобы F(0) не терялось в 0·∞
                       (simplify (list '* c (list '^ a -1)
                                       (list '+ (list '* u (list '+ w -1)) (list 'exp w)))))))))))

; ---------- шаг INT.GAPS.3: log(p)ⁿ/q, atanh(p)/q, atanh(√p)/q при линейных p, q ----------
; Формулы (t = α + βu, q = γ + δu, t₁ = α − γβ/δ — значение t в корне q, w = t/t₁; dx/q = dt/(δ(t − t₁))):
;   ∫ log(t)ⁿ/q du = (1/δ)·Jₙ,  Jₙ = logⁿ(t)·log(1 − w) − n·Kₙ₋₁,
;   Kₘ = ∫ logᵐ(t)·log(1 − w)/t dt = −Σⱼ₌₀ᵐ (−1)ʲ·m!/(m−j)!·logᵐ⁻ʲ(t)·Li_{j+2}(w)   (d Li₂(w)/dt = −log(1 − w)/t);
;   t₁ = 0 (p ∝ q):  ∫ log(t)ⁿ/q du = logⁿ⁺¹(t)/((n+1)·δ·β)·β = logⁿ⁺¹(t)/((n+1)·δ).
;   atanh(p) = ½(log(1 + p) − log(1 − p)); atanh(√p)/q: u = √p, dx/q = (1/δ)(1/(u − s) + 1/(u + s)) du, s² = a − γb/δ
;   (p = a + b·x), атанг = ½(log(1 + u) − log(1 − u)); s² = 0: ∫ atanh(u)/u du = ½(Li₂(u) − Li₂(−u)).
; Ответ — главные значения (log(1 − w) при w > 1 комплексен; вещественная часть — первообразная), проверка — ipl-F-status:
; численно по самому ответу (значения Li_s при аргументе ≤ 1; при > 1 — вещественная часть по инверсии для s = 2, 3).

(define (ipl-lin u x)        ; u = α + β·x → (α β) | #f
  (and (not (x-free? u x)) (polynomial? u x) (= (degree u x) 1)
       (let ((b (simplify (coeff u x 1))) (a (simplify (coeff u x 0))))
         (and (x-free? a x) (x-free? b x) (not (equal? b 0)) (list a b)))))

(define (ipl-sqrt-arg f)     ; √p → p | #f
  (cond ((and (pair? f) (equal? (car f) 'sqrt) (= (length f) 2)) (cadr f))
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3) (equal? (caddr f) 1/2)) (cadr f))
        (else #f)))

(define (ipl-lg t) (list 'log t))
(define (ipl-powl t m) (if (= m 0) 1 (list '^ (ipl-lg t) m)))
(define (ipl-fact m) (if (<= m 1) 1 (* m (ipl-fact (- m 1)))))

; Kₘ (w = t/t₁)
(define (ipl-K m t w)
  (list '* -1
        (cons '+ (map (lambda (j)
                        (list '* (* (if (ipl-even-int? j) 1 -1) (/ (ipl-fact m) (ipl-fact (- m j))))
                              (ipl-powl t (- m j)) (ipl-li (+ j 2) w)))
                      (range (+ m 1))))))

(define (ipl-even-int? j) (= (remainder j 2) 0))

; ∫ log(α + β·u)ⁿ/(γ + δ·u) du, u — выражение (x или √p); α, β, γ, δ без x; n ≥ 1; β, δ ≠ 0 | #f
(define (ipl-logpow-over-lin n al be ga de u)
  (let* ((t (simplify (list '+ al (list '* be u))))
         (t1 (simplify (list '+ al (list '* -1 ga be (list '^ de -1))))))
    (cond ((or (equal? t1 0) (and (contains-sym? t1 '%i) (equal? (simplify (expand t1)) 0)))
           (simplify (list '* (list '^ (list '* (+ n 1) de) -1) (ipl-powl t (+ n 1)))))
          ; γ = 0, α = 1, n = 1: ∫ log(1 + β·u)/(δ·u) du = −Li₂(−β·u)/δ (без log(1 − w))
          ((and (= n 1) (equal? ga 0) (equal? al 1))
           (simplify (list '* -1 (list '^ de -1) (ipl-li 2 (simplify (list '* -1 be u))))))
          (else
           (let* ((w (simplify (list '* t (list '^ t1 -1))))
                  (l1w (list 'log (simplify (list '+ 1 (list '* -1 w)))))
                  (jn (list '+ (list '* (ipl-powl t n) l1w) (list '* (- n) (ipl-K (- n 1) t w)))))
             (simplify (list '* (list '^ de -1) jn)))))))

; ---------- численная проверка самого ответа ----------
; Re Li_s(z): z ≤ 1 — polylog-num; z > 1 — по инверсии (s = 2: π²/3 − ½L² − Li₂(1/z); s = 3: Li₃(1/z) − L³/6 + π²L/3)
(define (ipl-re-li s z)
  (cond ((<= z 1.0) (polylog-num s z))
        ((= s 2) (let ((l (eval-num (list 'log z))) (i (polylog-num 2 (/ 1.0 z))))
                   (and i (- (/ (* (eval-num 'pi) (eval-num 'pi)) 3.0) (* 0.5 l l) i))))
        ((= s 3) (let ((l (eval-num (list 'log z))) (i (polylog-num 3 (/ 1.0 z))))
                   (and i (+ i (/ (* l l l) -6.0) (/ (* (eval-num 'pi) (eval-num 'pi) l) 3.0)))))
        (else #f)))

; числа вместо polylog (ошибка, если аргумент не вещественный число или значение не посчитано)
(define (ipl-subst e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'polylog) (= (length e) 3))
         (let* ((z (eval-num (ipl-subst (caddr e)))))
           (if (and (real-numeric? z) (not (and (equal? (cadr e) 2) (> z 1))))
               (let ((v (ipl-re-li (cadr e) (* 1.0 z))))
                 (if v v (error "polylog: нет значения")))
               ; комплексный аргумент (шаг INT.GAPS.3b): Li₂ — polylog2-cx, значение (re + im·i)
               (let ((cz (int-cx-parts z)))
                 (if (and cz (equal? (cadr e) 2))
                     (let ((v (polylog2-cx (car cz) (cdr cz)))) (list '+ (car v) (list '* (cdr v) '%i)))
                     (error "polylog: нет значения"))))))
        (else (cons (car e) (map ipl-subst (cdr e))))))

(define (ipl-val-at e x p vals)
  (try (int-cx-parts (eval-num (int-hyp (ipl-subst (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                                          (replace-expr e x p) vals)))))
       (lambda (er) #f)))

(define (ipl-param-sets)
  (list int-test-params
        (map (lambda (v) (/ v 10)) int-test-params)
        (reverse int-test-params)))

; вердикт по точке: 'skip (не посчиталось, либо f комплексно — вне вещественной области), 'ok, 'bad
(define (ipl-point-verdict F f x p vals)
  (let* ((h 1/10000)
         (fv (ipl-val-at f x p vals))
         (fp (and fv (ipl-val-at F x (+ p h) vals)))
         (fm (and fp (ipl-val-at F x (- p h) vals))))
    (cond ((or (not fv) (not fp) (not fm)) 'skip)
          ((> (abs (cdr fv)) 0.000000001) 'skip)
          (else (let ((d (/ (- (car fp) (car fm)) (* 2 h))))
                  (if (<= (abs (- d (car fv))) (* 0.0001 (+ 1 (abs (car fv))))) 'ok 'bad))))))

; (ipl-F-ok? F f x) → #t: F′ = f численно по самому F не меньше чем в трёх точках × наборах и без расхождений
(define (ipl-F-ok? F f x)
  (let* ((ps (int-symbols (list '+ F f) x))
         (rs (append-map (lambda (pset)
                           (let ((vals (map2 list ps pset)))
                             (map (lambda (p) (ipl-point-verdict F f x p vals)) '(3/10 71/100 137/100 -3/10 23/10 -23/10))))
                         (ipl-param-sets))))
    (and (not (any? (lambda (r) (equal? r 'bad)) rs))
         (>= (length (filter (lambda (r) (equal? r 'ok)) rs)) 3))))

; ---------- разбор форм ----------
(define (ipl-lin-inv f x)    ; f = q⁻¹, q линейно → (γ δ) | #f
  (and (pair? f) (equal? (car f) '^) (= (length f) 3) (equal? (caddr f) -1) (ipl-lin (cadr f) x)))

(define (ipl-log-pow f x)    ; f = log(p)ⁿ, p линейно, n ≥ 1 целое → (n α β) | #f
  (cond ((and (ipl-head? f 'log 2) (ipl-lin (cadr f) x)) (cons 1 (ipl-lin (cadr f) x)))
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3) (integer? (caddr f)) (>= (caddr f) 2)
              (ipl-head? (cadr f) 'log 2) (ipl-lin (cadr (cadr f)) x))
         (cons (caddr f) (ipl-lin (cadr (cadr f)) x)))
        (else #f)))

(define (ipl-partition vs x pred)  ; (found . rest) для единственного множителя, удовлетворяющего pred
  (let ((hit (filter (lambda (f) (pred f)) vs)))
    (and (= (length hit) 1) (cons (car hit) (filter (lambda (f) (not (pred f))) vs)))))

; c·logⁿ(p)/q ; c·atanh(p)/q ; c·atanh(√p)/q
(define (ipl-parts c vs x)
  (and (= (length vs) 2)
       (let ((qp (ipl-partition vs x (lambda (f) (ipl-lin-inv f x)))))
         (and qp
              (let* ((gd (ipl-lin-inv (car qp) x)) (ga (car gd)) (de (cadr gd)) (h (cadr qp))
                     (lp (ipl-log-pow h x)))
                (cond
                  (lp (simplify (list '* c (ipl-logpow-over-lin (car lp) (cadr lp) (caddr lp) ga de x))))
                  ((and (ipl-head? h 'atanh 2) (ipl-lin (cadr h) x))
                   (let* ((ab (ipl-lin (cadr h) x)) (a (car ab)) (b (cadr ab)))
                     (simplify (list '* c 1/2
                                     (list '+ (ipl-logpow-over-lin 1 (simplify (list '+ 1 a)) b ga de x)
                                           (list '* -1 (ipl-logpow-over-lin 1 (simplify (list '+ 1 (list '* -1 a))) (simplify (list '* -1 b)) ga de x)))))))
                  ((and (ipl-head? h 'atanh 2) (ipl-sqrt-arg (cadr h)) (ipl-lin (ipl-sqrt-arg (cadr h)) x))
                   (ipl-atanh-sqrt c (ipl-sqrt-arg (cadr h)) ga de x))
                  ((and (ipl-head? h 'atan 2) (ipl-lin (cadr h) x))
                   (let ((ab (ipl-lin (cadr h) x)))
                     (ipl-atan-over-lin c (car ab) (cadr ab) ga de x)))
                  (else #f)))))))

; ---------- шаг INT.GAPS.3b: arctg(p)/q через комплексные Li₂ ----------
; atan(p) = (i/2)(log(1 − i·p) − log(1 + i·p)); ∫ log(α + β·u)/(γ + δ·u) du при комплексных α, β — те же формулы
; (ipl-logpow-over-lin). Ответ вещественен при вещественном x (слагаемые сопряжены); главные значения, проверка — ipl-F-ok?.
; ∫ c·atan(a + b·x)/(γ + δ·x) dx
(define (ipl-atan-over-lin c a b ga de x)
  (let ((ia (list '* '%i a)) (ib (list '* '%i b)))
    (simplify
     (list '* c '%i 1/2
           (list '+ (ipl-logpow-over-lin 1 (simplify (list '+ 1 (list '* -1 ia))) (simplify (list '* -1 ib)) ga de x)
                 (list '* -1 (ipl-logpow-over-lin 1 (simplify (list '+ 1 ia)) (simplify ib) ga de x)))))))

; ∫ c·atan(a + b·x)²/(γ + δ·x)² dx. По частям: = c·(−atan²/(δ·q) + (2b/δ)·I), I = ∫ atan(u)/((1 + u²)(m + n·u)) du,
; u = a + b·x, m = b·γ − a·δ, n = δ. Разложение: 1/((1 + u²)(m + n·u)) = Σ Rᵣ/(u − r), r ∈ {−m/n, i, −i},
; R₋ₘ/ₙ = 1/(n(1 + r²)), Rᵢ = 1/(2i·n·(i − r₁)), R₋ᵢ = −1/(2i·n·(−i − r₁)); ∫ atan(u)/(u − r) du = ∫ atan(p)/(x + (a − r)/b) dx.
(define (ipl-atan-sq-over-lin2 c a b ga de x)
  (let* ((p (simplify (list '+ a (list '* b x))))
         (q (simplify (list '+ ga (list '* de x))))
         (m (simplify (list '+ (list '* b ga) (list '* -1 a de))))
         (r1 (simplify (list '* -1 m (list '^ de -1))))
         (res (list (list r1 (list '^ (list '* de (list '+ 1 (list '^ r1 2))) -1))
                    (list '%i (list '^ (list '* 2 '%i de (list '+ '%i (list '* -1 r1))) -1))
                    (list (list '* -1 '%i) (list '* -1 (list '^ (list '* 2 '%i de (list '+ (list '* -1 '%i) (list '* -1 r1))) -1))))))
    (simplify
     (list '* c
           (list '+ (list '* -1 (list '^ (list '* de q) -1) (list '^ (list 'atan p) 2))
                 (list '* 2 b (list '^ de -1)
                       (cons '+ (map (lambda (rr)
                                       (list '* (cadr rr)
                                             (ipl-atan-over-lin 1 a b (simplify (list '* (list '+ a (list '* -1 (car rr))) (list '^ b -1))) 1 x)))
                                     res))))))))

; c·atan(p)²/q²: p, q линейны → (c a b γ δ) | #f
(define (ipl-atan-sq-parse c vs x)
  (and (= (length vs) 2)
       (let ((qp (ipl-partition vs x (lambda (f) (and (pair? f) (equal? (car f) '^) (= (length f) 3) (equal? (caddr f) -2) (ipl-lin (cadr f) x))))))
         (and qp
              (let ((h (cadr qp)) (gd (ipl-lin (cadr (car qp)) x)))
                (and (pair? h) (equal? (car h) '^) (= (length h) 3) (equal? (caddr h) 2) (ipl-head? (cadr h) 'atan 2)
                     (ipl-lin (cadr (cadr h)) x)
                     (let ((ab (ipl-lin (cadr (cadr h)) x)))
                       (ipl-atan-sq-over-lin2 c (car ab) (cadr ab) (car gd) (cadr gd) x))))))))

; ∫ c·atanh(k/x²)² dx. По частям: = x·atanh² + 2k·∫ atanh(k/x²)·(1/(x² − k) + 1/(x² + k)) dx  (atanh(k/x²)′ = −2k·x/(x⁴ − k²)),
; atanh(k/x²) = ½(log(x² + k) − log(x² − k)), x² ± k = (x − r₁)(x − r₂) с r = ±s (x² − k), ±i·s (x² + k), s = √k;
; 1/(x² − k) = (1/(2s))(1/(x − s) − 1/(x + s)), 1/(x² + k) = (1/(2i·s))(1/(x − i·s) − 1/(x + i·s)); каждое ∫ log(x − r₁)/(x − r₂) dx — Li₂.
; Верно при k > 0 и x² > k (иначе atanh(k/x²) комплексен; ветви главные), условие записывается при символьном k.
(define (ipl-atanh-sq-xm2 c k x)
  (and (or (not (number? k)) (> k 0))
       (let* ((s (simplify (list 'sqrt k)))
              (is (simplify (list '* '%i s)))
              (r2s (list (list s (list '^ (list '* 2 s) -1))
                         (list (ipl-neg s) (list '* -1 (list '^ (list '* 2 s) -1)))
                         (list is (list '^ (list '* 2 '%i s) -1))
                         (list (ipl-neg is) (list '* -1 (list '^ (list '* 2 '%i s) -1)))))
              (r1s (list (list is 1) (list (ipl-neg is) 1) (list s -1) (list (ipl-neg s) -1))))
         (if (number? k) #f (set! *ipl-pending-cond* (list '> k 0)))
         (simplify
          (list '* c
                (list '+ (list '* x (list '^ (list 'atanh (list '* k (list '^ x -2))) 2))
                      (list '* k
                            (cons '+ (append-map
                                      (lambda (r2w)
                                        (map (lambda (r1sg)
                                               (list '* (cadr r2w) (cadr r1sg)
                                                     (ipl-logpow-over-lin 1 (ipl-neg (car r1sg)) 1 (ipl-neg (car r2w)) 1 x)))
                                             r1s))
                                      r2s)))))))))

; c·atanh(k·x⁻²)²
(define (ipl-atanh-sq-parse c vs x)
  (and (= (length vs) 1)
       (let ((h (car vs)))
         (and (pair? h) (equal? (car h) '^) (= (length h) 3) (equal? (caddr h) 2) (ipl-head? (cadr h) 'atanh 2)
              (let ((p (ipl-kxn (cadr (cadr h)) x)))
                (and p (equal? (cadr p) -2) (ipl-atanh-sq-xm2 c (car p) x)))))))

; atanh(√(a + b·x))/(γ + δ·x)
(define (ipl-atanh-sqrt c p ga de x)
  (let* ((ab (ipl-lin p x)) (a (car ab)) (b (cadr ab))
         (s2 (simplify (list '+ a (list '* -1 ga b (list '^ de -1)))))
         (u (list 'sqrt p)))
    (cond ((equal? s2 0)
           (simplify (list '* c (list '^ de -1) (list '+ (ipl-li 2 u) (list '* -1 (ipl-li 2 (ipl-neg u)))))))
          ((and (number? s2) (< s2 0)) #f)
          (else
           (let ((s (simplify (list 'sqrt s2))))
             (if (number? s2) #f (set! *ipl-pending-cond* (list '> s2 0)))
             (simplify
              (list '* c 1/2 (list '^ de -1)
                    (cons '+ (map (lambda (r)
                                    ; ∫ atanh(u)/(u − r) du = ½(∫ log(1 + u)/(u − r) − ∫ log(1 − u)/(u − r))
                                    (list '+ (ipl-logpow-over-lin 1 1 1 (ipl-neg r) 1 u)
                                          (list '* -1 (ipl-logpow-over-lin 1 1 -1 (ipl-neg r) 1 u))))
                                  (list s (ipl-neg s)))))))))))

; условие s² > 0 (корень s = √(a − γb/δ) вещественен) — записывается только после проверки ответа
(define *ipl-pending-cond* #f)

(define (ipl-answer-checked c vs x e)
  (set! *ipl-pending-cond* #f)
  (let ((ans (try (or (ipl-parts c vs x) (ipl-atan-sq-parse c vs x) (ipl-atanh-sq-parse c vs x)) (lambda (er) #f))))
    (and ans (not (contains-sym? ans 'integrate))
         (try (ipl-F-ok? ans e x) (lambda (er) #f))
         (begin (if *ipl-pending-cond*
                    (record-condition *ipl-pending-cond*
                                      "полилогарифм: ответ — вещественная часть главных значений; верен при указанном условии на параметры (вещественный корень s, k > 0) и x в области, где подынтегральное вещественно (0 < a + b·x < 1, x² > k)")
                    #f)
                ans))))

; ---------- шаг PL.2: интегралы от самого полилогарифма ----------
; ∫ x^m·Li_s(α + β·x) dx: подстановка u = α + βx даёт (1/β^{m+1})·Σ_{k=0}^{m} C(m,k)·(−α)^{m−k}·J(k,s),
; J(k,s) = u^{k+1}·Li_s(u)/(k+1) − J(k,s−1)/(k+1)   (d Li_s/du = Li_{s−1}/u), база J(k,1) — элементарна:
; J(k,1) = −u^{k+1}·log(1−u)/(k+1) + (Σ_{j=1}^{k+1} u^j/j)/(k+1) + log(1−u)/(k+1).
; Второе семейство: ∫ Li_s(a·xⁿ) dx = x·Li_s(a·xⁿ) − n·∫ Li_{s−1}(a·xⁿ) dx, база ∫ log(1 − a·xⁿ) dx
; (n = 1, 2 раскрываются в элементарные). Проверка — int-check в int-polylog.

(define (ipl-bin k j)                                            ; C(k,j) — биномиальный коэффициент
  (if (or (< j 0) (> j k)) 0                                     ; вне треугольника — нуль
      (let loop ((i 1) (acc 1))                                  ; накопление произведения
        (if (> i j) acc                                          ; дошли до j — готово
            (loop (+ i 1) (/ (* acc (+ (- k j) i)) i))))))       ; C(k,i) = C(k,i−1)·(k−j+i)/i

(define (ipl-hsum k u)                                           ; Σ_{j=1}^{k+1} u^j/j
  (let loop ((j 1) (acc '()))                                    ; собираем слагаемые
    (if (> j (+ k 1)) (simplify (cons '+ acc))                    ; все j — складываем
        (loop (+ j 1) (cons (list '* (list '^ u j) (list '^ j -1)) acc))))) ; u^j/j

(define (ipl-log1m u) (list 'log (simplify (list '+ 1 (list '* -1 u))))) ; log(1 − u)

(define (ipl-li-j k s u)                                         ; J(k,s) = ∫ u^k·Li_s(u) du
  (if (= s 1)                                                    ; база: Li_1(u) = −log(1 − u)
      (simplify (list '+ (list '* -1 (list '^ u (+ k 1)) (ipl-log1m u) (list '^ (+ k 1) -1)) ; −u^{k+1}log(1−u)/(k+1)
                       (list '* (ipl-hsum k u) (list '^ (+ k 1) -1))                          ; +Σu^j/j/(k+1)
                       (list '* (ipl-log1m u) (list '^ (+ k 1) -1))))                         ; +log(1−u)/(k+1)
      (simplify (list '- (list '* (list '^ u (+ k 1)) (ipl-li s u) (list '^ (+ k 1) -1))          ; u^{k+1}Li_s/(k+1)
                      (list '* (ipl-li-j k (- s 1) u) (list '^ (+ k 1) -1))))))                    ; −J(k,s−1)/(k+1)

(define (ipl-log1m-pow a n x)                                    ; ∫ log(1 − a·xⁿ) dx, n = 1, 2
  (cond ((= n 1)                                                 ; n = 1: ((1−ax)/a)·log(1−ax) + x
         (let ((u (simplify (list '* a x))))                      ; u = a·x
           (simplify (list '+ (list '* (simplify (list '* (list '+ 1 (list '* -1 u)) (list '^ a -1))) (ipl-log1m u)) x))))
        ((= n 2)                                                 ; n = 2: x·log(1−ax²) + 2(artanh(√a·x)/√a − x)
         (let* ((u (simplify (list '* a (list '^ x 2)))) (r (simplify (list 'sqrt a))))
           (simplify (list '+ (list '* x (ipl-log1m u))
                           (list '* 2 (list '+ (list '* (list '^ r -1) (list 'atanh (simplify (list '* r x)))) (list '* -1 x)))))))
        (else #f)))                                              ; n > 2 не раскрываем

(define (ipl-li-pow s a n x)                                     ; ∫ Li_s(a·xⁿ) dx
  (if (= s 1)                                                    ; база: Li_1 = −log(1 − u)
      (ipl-neg (ipl-log1m-pow a n x))                            ; ∫ Li_1 = −∫ log(1 − a·xⁿ)
      (simplify (list '- (list '* x (ipl-li s (simplify (list '* a (list '^ x n))))) ; x·Li_s(a xⁿ)
                      (list '* n (ipl-li-pow (- s 1) a n x)))))) ; −n·∫Li_{s−1}

(define (ipl-term-li e x)                                        ; c·P(x)·Li_s(u) → (c P s u) | #f
  (let* ((sp (ipl-split e x)) (c (car sp)) (vs (cadr sp))         ; множитель без x и множители с x
         (pls (filter (lambda (f) (ipl-head? f 'polylog 3)) vs))  ; полилогарифм
         (rest (filter (lambda (f) (not (ipl-head? f 'polylog 3))) vs))) ; остальные множители
    (and (= (length pls) 1)                                       ; ровно один полилогарифм
         (let ((p (simplify (cons '* rest))))                     ; P(x) — произведение остальных
           (and (try (polynomial? p x) (lambda (er) #f))           ; P — многочлен по x
                (list c p (cadr (car pls)) (caddr (car pls)))))))) ; c, P, s, аргумент

; ∫ P(x)·Li_s(α+βx) dx = (c/β)·Σ_j [Σ_{k≥j} p_k·C(k,j)·(−α)^{k−j}/β^k]·J(j,s),
; где P(x) = Σ p_k·x^k. Коэффициенты берутся по x, без подстановки и раскрытия дробей.
(define (ipl-li-poly c p s al be x)
  (let* ((cs (try (coefficients p x) (lambda (er) #f)))           ; p_k по x, от младшей степени
         (n (if cs (length cs) 0))                                ; сколько коэффициентов
         (u (list '+ al (list '* be x))))                          ; u = α + β·x
    (and cs (not (= n 0))                                          ; P разложился
         (let ((terms (filter (lambda (t) (not (equal? (cadr t) 0))) ; выбрасываем нулевые J
                              (map (lambda (j)                     ; J(j,s) с коэффициентом
                                     (list (cons '+                 ; Σ_{k≥j} p_k·C(k,j)·(−α)^{k−j}/β^k
                                                 (filter (lambda (t) (not (equal? t 0)))
                                                         (map2 (lambda (pk k)
                                                                 (if (>= k j)
                                                                     (list '* pk (ipl-bin k j)
                                                                           (list '^ (simplify (list '* -1 al)) (- k j))
                                                                           (list '^ be (- k)))
                                                                     0))
                                                               cs (range n))))
                                           (ipl-li-j j s u)))
                                   (range n)))))
           (and (pair? terms)                                      ; есть что складывать
                (simplify (list '* c (list '^ be -1)           ; c/β
                                (cons '+ (map (lambda (t) (list '* (car t) (cadr t))) terms)))))))))

(define (ipl-li-term-ans e x)                                    ; ответ для одного слагаемого
  (let ((t (ipl-term-li e x)))                                   ; разбор слагаемого
    (and t
         (let* ((c (car t)) (p (cadr t)) (s (caddr t)) (u (nth t 3))) ; c, P, порядок, аргумент
           (cond ((ipl-lin u x)                                   ; аргумент линейный: α + βx
                  (let* ((ab (ipl-lin u x)) (al (car ab)) (be (cadr ab))) ; α, β
                    (ipl-li-poly c p s al be x)))                 ; c/β·Σ p_k·J(k,s)
                 ((and (x-free? p x) (ipl-kxn u x)                ; P постоянен, аргумент a·xⁿ
                       (integer? (cadr (ipl-kxn u x))) (>= (cadr (ipl-kxn u x)) 1) (<= (cadr (ipl-kxn u x)) 2))
                  (let* ((q (ipl-kxn u x)) (a (car q)) (n (cadr q))) ; a, n
                    (simplify (list '* c (ipl-li-pow s a n x)))))  ; c·∫Li_s(a xⁿ)
                 (else #f))))))                                   ; остальное — не наше

(define (ipl-has-polylog? e)                                     ; в выражении есть голова polylog
  (and (pair? e)                                                  ; не атом
       (or (equal? (car e) 'polylog)                              ; сама голова
           (any? ipl-has-polylog? (cdr e)))))                     ; или внутри

(define (ipl-li-sum e x)                                          ; ∫ Σ c·P(x)·Li_s(u): почленно
  (let* ((ex (expand e))                                          ; раскрываем скобки
         (ts (if (and (pair? ex) (equal? (car ex) '+)) (cdr ex) (list ex)))) ; слагаемые
    (and (ipl-has-polylog? e)                                     ; в форме есть полилогарифм
         (let ((ans (map (lambda (t) (ipl-li-term-ans t x)) ts)))  ; ответ по каждому слагаемому
           (and (every? (lambda (a) a) ans)                       ; все слагаемые разобраны
                (simplify (cons '+ ans)))))))                     ; сумма ответов

(define (ipl-answer e x)
  (let* ((sp (ipl-split e x)) (c (car sp)) (vs (cadr sp)))        ; множитель без x и множители с x
    (or (ipl-li-sum e x)                                          ; P(x)·Li_s(u) — новый шаг PL.2
        (ipl-lambert c vs x)                                      ; функция Ламберта
        (ipl-log-over-one-minus c vs x)                           ; log(x)/(1 − x)
        (and (= (length vs) 2) (any? (lambda (f) (ipl-inv-x? f x)) vs) ; h(u)/x
             (let ((h (filter (lambda (f) (not (ipl-inv-x? f x))) vs))) ; числитель
               (and (= (length h) 1) (ipl-over-x c (car h) x))))  ; c·h(u)/x
        (ipl-answer-checked c vs x e))))                          ; остальные формы таблицы

(define (int-polylog e x d)
  (and (op-expr? e)
       (ipl-has-head? e '(polylog lambert_w log atanh atan))
       (let ((ans (try (ipl-answer e x) (lambda (err) #f))))
         (and ans (not (contains-sym? ans 'integrate))
              (try (int-check ans e x) (lambda (err) #f))
              (with-step ('int-polylog "Интеграл через полилогарифм или функцию Ламберта" (int-form e x)
                          :comment "подстановка u = k·xⁿ, dx/x = du/(n·u): "
                          :after int-p)
                ans)))))

(define (ipl-has-head? e hs)
  (and (pair? e)
       (or (member? (car e) hs) (any? (lambda (a) (ipl-has-head? a hs)) (cdr e)))))

; Вызов из int-antiderivative до предпроверки Риша: вся форма, либо сумма, где хотя бы одно слагаемое — форма из таблицы,
; а остальные берутся каскадом (глубина 1) без остатков integrate; итог проверяется дифференцированием. #f — не наш случай.
(define (int-polylog-first e x)
  (try
   (or (int-polylog e x 0)
       (let ((ex (simplify (expand e))))
         (and (op-expr? ex) (equal? (car ex) '+)
              (ipl-has-head? ex '(polylog lambert_w log atanh atan))
              (any? (lambda (t) (try (ipl-answer t x) (lambda (er) #f))) (cdr ex))
              (let ((parts (map (lambda (t)
                                  (or (try (ipl-answer t x) (lambda (er) #f))
                                      (let ((r (int-go t x 1))) (and r (not (contains-sym? r 'integrate)) r))))
                                (cdr ex))))
                (and (every? (lambda (p) p) parts)
                     (let ((ans (simplify (cons '+ parts))))
                       (and (try (int-check ans e x) (lambda (er) #f))
                            (with-step ('int-polylog "Интеграл через полилогарифм или функцию Ламберта" (int-form e x)
                                        :comment "подстановка u = k·xⁿ, dx/x = du/(n·u): "
                                        :after int-p)
                              ans))))))))
   (lambda (er) #f)))

; ---------- значение первообразной с Li_s на конце отрезка ----------
; limit не знает polylog (как и erf/Ei: непрерывность спецфункций пределом не берётся), поэтому для F с polylog на
; конце p подставляем: Li_s (s ≥ 2) непрерывна на (−∞, 1], значит подстановка верна, если каждый аргумент при x → p
; (со стороны side) остаётся ≤ 1, а остальное F при подстановке конечно (иначе — особенность, #f).
(define (ipl-polylogs e)
  (cond ((not (pair? e)) '())
        ((and (equal? (car e) 'polylog) (= (length e) 3)) (cons e (ipl-polylogs (caddr e))))
        (else (append-map ipl-polylogs (cdr e)))))

(define (ipl-num-at u x p)
  (let ((v (try (eval-num (subst (list '= x p) u)) (lambda (er) #f))))
    (and v (number? v) v)))

(define (ipl-arg-ok? pl x p side)
  (let ((s (cadr pl)) (u (caddr pl)))
    (and (integer? s) (>= s 2)
         (let ((u0 (ipl-num-at u x p)))
           (and u0 (<= u0 1.000000000001)
                (or (< u0 0.999999999999)
                    (let ((u1 (ipl-num-at u x (if (equal? side 'minus) (- p 1/1000000) (+ p 1/1000000)))))
                      (and u1 (< u1 1)))))))))

(define (ipl-endpoint F x p side)
  (and (number? p) (< (abs p) 1000000000)
       (let ((pls (ipl-polylogs F)))
         (and (pair? pls) (every? (lambda (pl) (ipl-arg-ok? pl x p side)) pls)
              (let ((r (try (simplify (subst (list '= x p) F)) (lambda (er) #f))))
                (and r (not (contains-sym? r 'limit)) (polylog-evalf r) r))))))

(int-add-strategy int-polylog)
