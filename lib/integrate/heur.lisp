; integrate/heur.lisp — приёмы «как у модели» (шаг INT.HEUR): e^(n·обратная гиперболическая) → алгебраическое,
; подстановка обратной функцией x = φ(t), анзац по структуре знаменателя
;
; Ступень каскада после скрытой подстановки (И4), до анзаца (int-heur-fallback в api.lisp). Каждый ответ принимается только
; после int-check по ИСХОДНОМУ f и численной проверки самой F (int-check-F-status = 'ok, в точках по обе стороны нуля).
; Переписывания — только тождествами, верными на всей области определения (см. int-ahyp-full в core.lisp).
;
; Ход 3 (e^(n·g(u))): f переписывается int-exp-ahyp-full, ∫ берёт обычный каскад (рекурсия, he-depth = 1).
; Ход 2 (обратная функция): f содержит g(x), g ∈ {atan, acot, asin, acos, asinh, acosh, atanh, acoth}; x = φ(t), t = g(x);
;   φ выражена через S, C (sin/cos или sinh/cosh t) и dx/dt — тоже; радикалы √(1±x²) заменяются на 1/C, 1/S, C, S (знак корня
;   на области t известен), результат приводится к рациональному виду C² = 1 ± S² (he-reduce-c); интеграл по t — каскад,
;   обратная подстановка: S(x), C(x) для голов sin t, cos t, … от t; остальные вхождения t — просто g(x) (подстановка точная).
; Внутренние имена: he-.
(module integrate
  (export int-heur int-heur-stats int-heur-reset without-heur))

(define int-heur-enabled #t)
(define int-heur-time-limit 8)
(define he-depth 0)
(define he-info '())
(define he-t 'he-t)
(define he-s 'he-s)
(define he-c 'he-c)

(define (without-heur thunk)
  (let ((old int-heur-enabled))
    (set! int-heur-enabled #f)
    (unwind-protect (thunk) (set! int-heur-enabled old))))

(define (he-same? a b) (equal? (try (expand (list '+ a (list '* -1 b))) (lambda (e) 'err)) 0))

; ---------- общие проверки ----------
; численная проверка самой F как функции: F′ = f в ≥ 3 точках из he-pts (0 расхождений); там, где f вещественно при x < 0,
; хотя бы одна такая точка должна подтвердиться (точки по всей оси, не только x > 0 и не только внутри области, как в int-numchk-points)
(define he-pts '(-10 -5 -3 -2 -3/2 -7/10 -3/10 3/10 71/100 137/100 2 3 5 10 6/5 -6/5 11/10 -11/10 4 -4))
(define (he-num-ok? F f x)
  (let* ((ps (int-symbols (list '+ F f) x)) (vals (map2 list ps int-test-params))
         (rs (map (lambda (p) (cons p (try (int-F-point-verdict F f x p vals) (lambda (e) 'skip)))) he-pts))
         (cnt (lambda (s) (length (filter (lambda (r) (equal? (cdr r) s)) rs))))
         (neg-real (filter (lambda (p) (and (< p 0) (let ((v (int-cx-at f x p vals))) (and v (< (abs (cdr v)) 0.000000000001))))) he-pts))
         (neg-ok (filter (lambda (r) (and (< (car r) 0) (equal? (cdr r) 'ok))) rs)))
    (and (= (cnt 'bad) 0) (= (cnt 'gross) 0) (>= (cnt 'ok) 3)
         (or (null? neg-real) (pair? neg-ok)))))

; F принимается: без интегралов; формально верна по исходному f (или по g — f, переписанному тождеством, верным на области f:
; упроститель не знает, что exp(acoth x) = √((x+1)/(x−1)), и по f символьная проверка падает, а численная — нет) И численно
; (int-check-F-status = 'ok) по ИСХОДНОМУ f — в точках по обе стороны нуля, где f вещественно
(define (he-accept F f x &rest more)
  (and F (not (equal? F 'unknown)) (not (int-has-integrate? F))
       (let ((G (try (simplify F) (lambda (e) F))))
         (and (or (int-check G f x) (and (pair? more) (try (int-check G (car more) x) (lambda (e) #f))))
              (he-num-ok? G f x) G))))

(define (he-recurse g v)
  (set! he-depth (+ he-depth 1))
  (unwind-protect
    (let ((r (integrate g v)))
      (and r (not (equal? r 'unknown)) (not (int-has-integrate? r)) r))
    (set! he-depth (- he-depth 1))))

; ---------- ход 3: e^(n·обратная) ----------
(define (he-ahyp f x)
  (let ((g (try (int-exp-ahyp-full f) (lambda (e) f))))
    (and (not (equal? g f))
         (let ((r (try (he-recurse (simplify g) x) (lambda (e) #f))))
           (and r (he-accept r f x g))))))

; ---------- ход 2: подстановка обратной функцией ----------
; (голова S C x(S,C) dx/dt(S,C) ε S(x) C(x) радикалы) ; радикалы — список (B корень(S,C)), B — многочлен от x
(define (he-table g x)
  (let* ((s (list '^ (list '+ 1 (list '^ x 2)) -1/2))        ; (1+x²)^(-1/2)
         (m (list '^ (list '+ 1 (list '* -1 (list '^ x 2))) 1/2))   ; √(1−x²)
         (mi (list '^ (list '+ 1 (list '* -1 (list '^ x 2))) -1/2)) ; (1−x²)^(-1/2)
         (p1 (list '+ 1 (list '^ x 2)))
         (m1 (list '+ 1 (list '* -1 (list '^ x 2))))
         (S he-s) (C he-c))
    (cond ((equal? g 'atan)  (list 'sin 'cos (list '* S (list '^ C -1)) (list '^ C -2) -1 (list '* x s) s
                                   (list (list p1 (list '^ C -1)))))
          ((equal? g 'acot)  (list 'sin 'cos (list '* C (list '^ S -1)) (list '* -1 (list '^ S -2)) -1 s (list '* x s)
                                   (list (list p1 (list '^ S -1)))))
          ((equal? g 'asin)  (list 'sin 'cos S C -1 x m (list (list m1 C))))
          ((equal? g 'acos)  (list 'sin 'cos C (list '* -1 S) -1 m x (list (list m1 S))))
          ((equal? g 'asinh) (list 'sinh 'cosh S C 1 x (list '^ p1 1/2) (list (list p1 C))))
          ((equal? g 'acosh) (list 'sinh 'cosh C S 1 (list '* (list '^ (list '+ x -1) 1/2) (list '^ (list '+ x 1) 1/2)) x
                                   (list (list (list '+ (list '^ x 2) -1) S))))
          ((equal? g 'atanh) (list 'sinh 'cosh (list '* S (list '^ C -1)) (list '^ C -2) 1 (list '* x mi) mi
                                   (list (list m1 (list '^ C -1)))))
          ((equal? g 'acoth) (list 'sinh 'cosh (list '* C (list '^ S -1)) (list '* -1 (list '^ S -2)) 1
                                   (list '^ (list '* x (list '^ (list '+ 1 (list '* -1 (list '^ x -2))) 1/2)) -1)
                                   (list '^ (list '+ 1 (list '* -1 (list '^ x -2))) -1/2) '()))
          (else #f))))

(define (he-rad e B rt)
  (cond ((not (op-expr? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2) (he-same? (cadr e) B)) rt)
        ((and (equal? (car e) '^) (= (length e) 3) (equal? (type-of (caddr e)) 'rational) (= (denom (caddr e)) 2) (he-same? (cadr e) B))
         (list '^ rt (* 2 (caddr e))))
        (else (cons (car e) (map (lambda (a) (he-rad a B rt)) (cdr e))))))

; p — многочлен от c (прочее — коэффициенты): c² → 1 + ε·s²
(define (he-reduce-c p c s eps)
  (let ((cs (coefficients (expand p) c)))
    (and (list? cs)
         (expand (cons '+ (map2 (lambda (ci i)
                                  (list '* ci (list '^ c (remainder i 2))
                                        (list '^ (list '+ 1 (list '* eps (list '^ s 2))) (quotient i 2))))
                                cs (range (length cs))))))))

(define (he-pyth h eps)
  (let* ((g (together h)) (n (numer g)) (d (denom g))
         (n2 (he-reduce-c n he-c he-s eps)) (d2 (he-reduce-c d he-c he-s eps)))
    (and n2 d2 (not (equal? d2 0)) (together (list '/ n2 d2)))))

(define (he-trig-sub e t Sx Cx hyp?)
  (cond ((equal? e t) 'he-keep)
        ((not (op-expr? e)) e)
        ((and (= (length e) 2) (equal? (cadr e) t) (member? (car e) (if hyp? '(sinh cosh tanh coth sech csch) '(sin cos tan cot sec csc))))
         (let ((h (car e)))
           (cond ((member? h '(sin sinh)) Sx) ((member? h '(cos cosh)) Cx)
                 ((member? h '(tan tanh)) (list '* Sx (list '^ Cx -1)))
                 ((member? h '(cot coth)) (list '* Cx (list '^ Sx -1)))
                 ((member? h '(sec sech)) (list '^ Cx -1))
                 (else (list '^ Sx -1)))))
        (else (cons (car e) (map (lambda (a) (he-trig-sub a t Sx Cx hyp?)) (cdr e))))))

; аргумент g: x или k·x (k без x) → k, иначе #f
(define (he-lin-arg a x)
  (cond ((equal? a x) 1)
        ((and (op-expr? a) (equal? (car a) '*) (member? x (cdr a))
              (every? (lambda (t) (or (equal? t x) (not (contains-sym? t x)))) (cdr a))
              (= (length (filter (lambda (t) (equal? t x)) (cdr a))) 1))
         (simplify (cons '* (filter (lambda (t) (not (equal? t x))) (cdr a)))))
        (else #f)))

(define he-inv-heads '(atan acot asin acos asinh acosh atanh acoth))
(define (he-head-nodes e x)
  (cond ((not (op-expr? e)) '())
        ((and (= (length e) 2) (member? (car e) he-inv-heads) (he-lin-arg (cadr e) x))
         (list (cons (car e) (he-lin-arg (cadr e) x))))
        (else (foldl append '() (map (lambda (a) (he-head-nodes a x)) (cdr e))))))
(define (he-find-heads f x) (su-dedup (he-head-nodes f x)))   ; ((g . k) …)

(define (he-inverse-one f x g k)
  (if (equal? k 1)
      (let ((F (he-inverse-core f x g))) (and F (he-accept F f x)))
      ; g(k·x): y = k·x, f(x) dx = f(y/k)/k dy
      (let* ((y 'he-y) (fy (simplify (list '/ (replace-expr f x (list '/ y k)) k)))
             (Fy (he-inverse-core fy y g)))
        (and Fy (he-accept (replace-expr Fy y (list '* k x)) f x)))))

(define (he-inverse-core f x g)
  (let ((tb (he-table g x)))
    (and tb
         (let* ((sn (nth tb 0)) (cn (nth tb 1)) (xs (nth tb 2)) (dxs (nth tb 3)) (eps (nth tb 4))
                (Sx (nth tb 5)) (Cx (nth tb 6)) (rads (nth tb 7)) (hyp? (equal? sn 'sinh))
                (f1 (replace-expr f (list g x) he-t))
                (f2 (foldl (lambda (acc pr) (he-rad acc (car pr) (cadr pr))) f1 rads))
                (f3 (replace-expr f2 x xs))
                (h0 (list '* f3 dxs))
                (h1 (try (he-pyth h0 eps) (lambda (e) #f))))
           (and h1 (not (contains-sym? h1 x))
                (let* ((h2 (replace-expr (replace-expr h1 he-s (list sn he-t)) he-c (list cn he-t)))
                       (r (try (he-recurse h2 he-t) (lambda (e) #f))))
                  (set! he-info (list g h2))
                  (and r
                       (let* ((G (he-trig-sub r he-t Sx Cx hyp?))
                              (F (replace-expr G 'he-keep (list g x))))
                         (and (not (contains-sym? F he-t)) F)))))))))

(define (he-inverse f x)
  (let loop ((gs (he-find-heads f x)))
    (and (pair? gs)
         (or (he-inverse-one f x (car (car gs)) (cdr (car gs))) (loop (cdr gs))))))

; ---------- подстановка экспоненты: u = e^w (гиперболические от w = c + d·x) и u = N^x (степени с числовым основанием) ----------
; Все тождества верны на всей оси: sinh w = (u − 1/u)/2, cosh w = (u + 1/u)/2 при u = e^w > 0; N^(k·x+c) = N^c·u^(m·k) при N = N₀^m.
; Остаток по x не допускается (всё подынтегральное — функция u). dx = du/(λ·u), λ = d (u = e^w) или ln N₀ (u = N₀^x).
(define he-u 'he-u)
(define (he-hyp-nodes e x)
  (cond ((not (op-expr? e)) '())
        ((and (= (length e) 2) (member? (car e) '(sinh cosh tanh coth sech csch)) (contains-sym? (cadr e) x)) (list e))
        (else (su-dedup (foldl append '() (map (lambda (a) (he-hyp-nodes a x)) (cdr e)))))))
(define (he-hyp-rw e w u)
  (cond ((equal? e (list 'exp w)) u)
        ((not (op-expr? e)) e)
        ((and (= (length e) 2) (member? (car e) '(sinh cosh tanh coth sech csch)) (equal? (cadr e) w))
         (let ((s2 (list '* 1/2 (list '+ u (list '* -1 (list '^ u -1)))))
               (c2 (list '* 1/2 (list '+ u (list '^ u -1)))))
           (case (car e)
             ((sinh) s2) ((cosh) c2)
             ((tanh) (list '* s2 (list '^ c2 -1))) ((coth) (list '* c2 (list '^ s2 -1)))
             ((sech) (list '^ c2 -1)) (else (list '^ s2 -1)))))
        (else (cons (car e) (map (lambda (a) (he-hyp-rw a w u)) (cdr e))))))
(define (he-hyp f x)
  (let ((ns (he-hyp-nodes f x)))
    (and (pair? ns)
         (let* ((w (cadr (car ns))) (d (simplify (int-diff x w))))
           (and (not (contains-sym? d x)) (not (equal? d 0))
                (let ((ft (he-hyp-rw f w he-u)))
                  (and (not (contains-sym? ft x))
                       (let* ((h (simplify (list '/ ft (list '* d he-u))))
                              (G (try (he-recurse h he-u) (lambda (e) #f))))
                         (and G (he-accept (replace-expr G he-u (list 'exp w)) f x))))))))))

; u = tan w, w = c + d·x: tan w = u, cot w = 1/u, чётные степени sec/csc/cos/sin — рационально через u (знак cos/sin не нужен);
; нечётные степени и другие тригонометрические головы от w остаются → отказ. dx = du/(d(1+u²)).
; Реализация без знака cos: sin w → u·C, cos w → C (C — формальный символ), tan → u, cot → 1/u, sec → 1/C, csc → 1/(u·C);
; после упрощения C должен сократиться; остаток по C — рациональная функция с C² = 1/(1+u²) (he-parity), нужна ОДНА чётность
; в числителе и знаменателе (иначе функция от u не определяется знаком — отказ). Тождество верно при любом знаке cos.
(define he-cc 'he-cc)
(define (he-tan-nodes e x)
  (cond ((not (op-expr? e)) '())
        ((and (= (length e) 2) (member? (car e) '(tan cot sin cos sec csc)) (contains-sym? (cadr e) x)) (list e))
        (else (su-dedup (foldl append '() (map (lambda (a) (he-tan-nodes a x)) (cdr e)))))))
(define (he-tan-rw e w u c)
  (cond ((not (op-expr? e)) e)
        ((and (= (length e) 2) (equal? (cadr e) w) (member? (car e) '(tan cot sin cos sec csc)))
         (case (car e)
           ((tan) u) ((cot) (list '^ u -1)) ((sin) (list '* u c)) ((cos) c)
           ((sec) (list '^ c -1)) (else (list '^ (list '* u c) -1))))
        (else (cons (car e) (map (lambda (a) (he-tan-rw a w u c)) (cdr e))))))
; Σ cᵢ·Cⁱ (все i одной чётности p) → (p, Σ cᵢ·(1+u²)^(−(i−p)/2))
(define (he-parity p c u)
  (let ((cs (coefficients (expand p) c)))
    (and (list? cs)
         (let* ((nz (filter (lambda (i) (not (equal? (nth cs i) 0))) (range (length cs)))))
           (and (pair? nz)
                (every? (lambda (i) (= (remainder i 2) (remainder (car nz) 2))) nz)
                (let ((par (remainder (car nz) 2)))
                  (cons par (cons '+ (map (lambda (i) (list '* (nth cs i) (list '^ (list '+ 1 (list '^ u 2)) (quotient (- par i) 2)))) nz)))))))))
(define (he-tan-clean ft u c)
  (let ((g (simplify ft)))
    (if (not (contains-sym? g c))
        g
        (let* ((tg (together g)) (n (numer tg)) (d (denom tg)))
          (and (polynomial? n c) (polynomial? d c)
               (let ((pn (he-parity n c u)) (pd (he-parity d c u)))
                 (and pn pd (= (car pn) (car pd))
                      (let ((r (simplify (list '/ (cdr pn) (cdr pd))))) (and (not (contains-sym? r c)) r)))))))))
(define (he-tan f x)
  (let ((ns (he-tan-nodes f x)))
    (and (pair? ns)
         (let* ((w (cadr (car ns))) (d (simplify (int-diff x w))))
           (and (not (contains-sym? d x)) (not (equal? d 0))
                (let ((ft (try (he-tan-clean (he-tan-rw f w he-u he-cc) he-u he-cc) (lambda (e) #f))))
                  (and ft (not (contains-sym? ft x))
                       (let* ((h (simplify (list '/ ft (list '* d (list '+ 1 (list '^ he-u 2))))))
                              (G (try (he-recurse h he-u) (lambda (e) #f))))
                         (and G (he-accept (replace-expr G he-u (list 'tan w)) f x))))))))))

(define (he-pow-nodes e x)
  (cond ((not (op-expr? e)) '())
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (cadr e)) (> (cadr e) 1) (contains-sym? (caddr e) x)) (list e))
        (else (su-dedup (foldl append '() (map (lambda (a) (he-pow-nodes a x)) (cdr e)))))))
(define (he-log-int n b)   ; m с b^m = n (целое m ≥ 1) или #f
  (let loop ((v b) (m 1))
    (cond ((= v n) m) ((> v n) #f) (else (loop (* v b) (+ m 1))))))
(define (he-pow-rw e x n0 u)
  (cond ((not (op-expr? e)) e)
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (cadr e)) (> (cadr e) 1) (contains-sym? (caddr e) x))
         (let* ((m (he-log-int (cadr e) n0)) (k (simplify (int-diff x (caddr e)))))
           (if (and m (not (contains-sym? k x)) (number? k))
               (list '* (list '^ (cadr e) (simplify (replace-expr (caddr e) x 0))) (list '^ u (* m k)))
               'he-bad)))
        (else (let ((r (map (lambda (a) (he-pow-rw a x n0 u)) (cdr e))))
                (if (member? 'he-bad r) 'he-bad (cons (car e) r))))))
(define (he-pow f x)
  (let ((ns (he-pow-nodes f x)))
    (and (pair? ns)
         (let* ((n0 (foldl min (cadr (car ns)) (map cadr ns))) (ft (he-pow-rw f x n0 he-u)))
           (and (not (equal? ft 'he-bad)) (not (contains-sym? ft x))
                (let* ((h (simplify (list '/ ft (list '* (list 'log n0) he-u))))
                       (G (try (he-recurse h he-u) (lambda (e) #f))))
                  (and G (he-accept (replace-expr G he-u (list '^ n0 x)) f x))))))))

; ---------- ход 4: анзац по структуре ----------
; f = R(x)·Πexp(uᵢ)·ΠBⱼ^rⱼ (R рациональна): кандидат F = P·W, W = Πexp(uᵢ)·ΠBⱼ^(rⱼ+1) (rⱼ < 0) или Bⱼ^rⱼ (rⱼ > 0),
; P = Pn/Dt, Dt = Π gᵢ^(mᵢ−1) по множителям gᵢ^mᵢ знаменателя R (оценка Риша: полюс P на порядок ниже полюса f).
; Тогда F′ = f ⇔ P′ + P·L = R′, L = W′/W = Σuᵢ′ + Σeⱼ·Bⱼ′/Bⱼ — линейное уравнение на многочлен Pn (система над ℚ(параметры)).
; Если f = A·e^u + B (сумма по степеням одного exp), то ∫A·e^u — так же, ∫B — каскадом.
(define (he-pure? e x)
  (cond ((not (contains-sym? e x)) #t)
        ((not (op-expr? e)) #t)
        ((equal? (car e) '^) (and (= (length e) 3) (integer? (caddr e)) (he-pure? (cadr e) x)))
        ((member? (car e) '(+ * /)) (every? (lambda (a) (he-pure? a x)) (cdr e)))
        (else #f)))

(define (he-sym i) (string->symbol (string-append "he-p" (number->string i))))

(define (he-ode-try R L Dt x n)
  (let* ((idx (range (+ n 1))) (ps (map he-sym idx))
         (Pn (cons '+ (map2 (lambda (p i) (list '* p (list '^ x i))) ps idx)))
         (M (list '+ L (list '* -1 (int-diff x Dt) (list '^ Dt -1))))
         (E (list '+ (int-diff x Pn) (list '* Pn M) (list '* -1 R Dt)))
         (cs (coefficients (expand (numer (together E))) x)))
    (and (list? cs)
         (let* ((eqs (filter (lambda (c) (not (equal? c 0))) cs))
                (sols (solve eqs ps))
                (sl (if (equal? (type-of sols) 'set) (set->list sols) '())))
           (and (pair? sl)
                (let* ((P1 (foldl (lambda (acc eq) (if (equal? (cadr eq) (caddr eq)) acc (replace-expr acc (cadr eq) (caddr eq))))
                                  Pn (car sl)))
                       (P2 (foldl (lambda (acc p) (replace-expr acc p 0)) P1 ps)))
                  (list '* P2 (list '^ Dt -1))))))))

(define (he-ode-solve R L x)
  (let* ((dn (try (denom (together R)) (lambda (e) #f)))
         (fl (and dn (try (factor-list dn) (lambda (e) #f)))))
    (and fl
         (let ((Dt (cons '* (map (lambda (p) (list '^ (car p) (- (cadr p) 1)))
                                 (filter (lambda (p) (and (contains-sym? (car p) x) (> (cadr p) 1))) (cdr fl))))))
           ; один solve при верхней оценке степени Pn (лишние старшие коэффициенты сами станут нулями);
           ; предотсев: степень > 12 или больше 3 параметров — не пробовать (система над ℚ(параметры) дорогая)
           (let ((nb (try (+ 1 (degree (expand (numer (together (list '* R Dt)))) x)) (lambda (e) #f))))
             (and nb (<= nb 12) (<= (length (int-symbols (list '+ R L) x)) 3)
                  (try (he-ode-try R L Dt x nb) (lambda (e) #f))))))))

(define (he-struct-prod f0 x)
  (let* ((fs (if (and (op-expr? f0) (equal? (car f0) '*)) (cdr f0) (list f0)))
         (exps (filter (lambda (a) (and (op-expr? a) (equal? (car a) 'exp) (contains-sym? a x))) fs))
         (rads (filter (lambda (a) (and (op-expr? a) (equal? (car a) '^) (= (length a) 3) (equal? (type-of (caddr a)) 'rational)
                                        (contains-sym? (cadr a) x))) fs))
         (rest (filter (lambda (a) (not (or (member? a exps) (member? a rads)))) fs)))
    ; только со множителем exp: для чистого радикала то же делают анзац и ansatz-cert (INT.ANSATZ.3/8)
    (and (pair? exps)
         (let* ((ev (lambda (a) (if (< (caddr a) 0) (+ (caddr a) 1) (caddr a))))
                (W (cons '* (append exps (map (lambda (a) (list '^ (cadr a) (ev a))) rads))))
                (L (cons '+ (append (map (lambda (e) (int-diff x (cadr e))) exps)
                                    (map (lambda (a) (list '* (ev a) (int-diff x (cadr a)) (list '^ (cadr a) -1))) rads))))
                (R (cons '* (append rest (map (lambda (a) (if (< (caddr a) 0) (list '^ (cadr a) -1) 1)) rads)))))
           (and (he-pure? R x) (he-pure? L x)
                (let ((P (he-ode-solve R L x)))
                  (and P (list '* P W))))))))

; f = A·e^u + B (одно exp по x): ∫A·e^u — анзац по структуре, ∫B — каскад
(define (he-exp-nodes e x)
  (cond ((not (op-expr? e)) '())
        ((and (equal? (car e) 'exp) (contains-sym? (cadr e) x)) (list e))
        (else (su-dedup (foldl append '() (map (lambda (a) (he-exp-nodes a x)) (cdr e)))))))

(define (he-struct-split f0 x)
  (let ((es (he-exp-nodes f0 x)))
    (and (= (length es) 1)
         (let* ((ts 'he-tt) (g (together (replace-expr f0 (car es) ts))) (N (expand (numer g))) (D (denom g)))
           (and (not (contains-sym? D ts)) (polynomial? N ts)
                (let ((cs (coefficients N ts)))
                  (and (= (length cs) 2)
                       (let* ((A (list '* (cadr cs) (list '^ D -1))) (B (list '* (car cs) (list '^ D -1)))
                              (u (cadr (car es))) (L (int-diff x u))
                              (P (and (he-pure? A x) (he-ode-solve A L x)))
                              (FB (and P (if (equal? (simplify B) 0) 0 (he-recurse B x)))))
                         (and P FB (list '+ (list '* P (car es)) FB))))))))))

; f = Nr(x)/(Dr(x)·√P), Dr = Q² + (m·x^k…)²·P: Dr − x^(2k)·P — полный квадрат Q² ⇒ 1 + u² = Dr/Q² при u = x^k·√P/Q,
; кандидат F = c·atan(u), c — константа (подбор численно в двух точках и рационализация; решает int-check)
(define (he-square-root S x)   ; многочлен S → Q с Q² = S (рациональный коэффициент) или #f
  (let ((fl (try (factor-list S) (lambda (e) #f))))
    (and fl (pair? fl) (> (car fl) 0)
         (every? (lambda (p) (even? (cadr p))) (cdr fl))
         (let ((s (sqrt (car fl))))
           (and (or (integer? s) (equal? (type-of s) 'rational)) (not (= s 0))
                (cons '* (cons s (map (lambda (p) (list '^ (car p) (quotient (cadr p) 2))) (cdr fl)))))))))
(define (he-atan f0 x)
  (let* ((fs (if (and (op-expr? f0) (equal? (car f0) '*)) (cdr f0) (list f0)))
         (rads (filter (lambda (a) (and (op-expr? a) (equal? (car a) '^) (= (length a) 3) (equal? (caddr a) -1/2)
                                        (polynomial? (cadr a) x))) fs)))
    (and (= (length rads) 1)
         (let* ((P (cadr (car rads)))
                (R (cons '* (filter (lambda (a) (not (equal? a (car rads)))) fs)))
                (Dr (expand (denom (together R)))))
           (and (polynomial? Dr x)
                (let loop ((ks '(0 1 2 3)))
                  (and (pair? ks)
                       (or (let* ((m (list '^ x (car ks)))
                                  (S (expand (list '+ Dr (list '* -1 (list '^ m 2) P))))
                                  (Q (and (not (equal? S 0)) (he-square-root S x))))
                             (and Q
                                  (let* ((u (list '* m (list '^ P 1/2) (list '^ Q -1)))
                                         (F0 (list 'atan u))
                                         (d (int-diff x F0))
                                         (c1 (he-ratio f0 d x 7/10)) (c2 (he-ratio f0 d x 19/10)))
                                    (and c1 c2 (< (abs (- c1 c2)) 0.000000001)
                                         (let ((c (su-ratz c1)))
                                           (and c (not (= c 0)) (list '* c F0)))))))
                           (loop (cdr ks))))))))))
(define (he-ratio f d x p)
  (try (let ((a (eval-num (replace-expr f x p))) (b (eval-num (replace-expr d x p))))
         (and (real-numeric? a) (real-numeric? b) (> (abs b) 0.000000001) (/ a b)))
       (lambda (e) #f)))

(define (he-norm-sqrt e)   ; √u → u^(1/2) (тождество на всей области: оба — неотрицательный корень)
  (cond ((not (op-expr? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2)) (list '^ (he-norm-sqrt (cadr e)) 1/2))
        (else (cons (car e) (map he-norm-sqrt (cdr e))))))

(define (he-struct f x)
  (let ((f0 (simplify (he-norm-sqrt f))))
    (or (let ((F (try (he-struct-prod f0 x) (lambda (e) #f)))) (and F (he-accept F f x)))
        (let ((F (try (he-struct-split f0 x) (lambda (e) #f)))) (and F (he-accept F f x)))
        (let ((F (try (he-atan f0 x) (lambda (e) #f)))) (and F (he-accept F f x))))))

; ---------- вход ----------
; ступень применима, только если у f есть форма хода (дёшево): g(k·x), exp(n·обратная гиперболическая), гиперболические от
; одного w, tan/cot от w, N^x, exp(u(x)) или радикал −1/2 (атангенс-кандидат); на остальных отказах ступень не тратит времени
(define (he-applicable? f x)
  (and (= he-depth 0) (= su-depth 0)
       (or (pair? (he-find-heads f x))
           (pair? (he-hyp-nodes f x)) (pair? (he-tan-nodes f x)) (pair? (he-pow-nodes f x))
           (pair? (he-exp-nodes f x))
           (not (equal? (try (int-exp-ahyp-full f) (lambda (e) f)) f)))))

; журнал ступени: he-cur — ветка, которая работает сейчас (при исчерпании бюджета видно, какая съела время), he-log — ((ветка мс итог) …)
(define he-cur #f)
(define he-log '())
(define (he-branch name limit thunk)
  (set! he-cur name)
  (let* ((t0 (clock-us))
         (r (let ((q (call-with-time-limit limit (lambda () (try (thunk) (lambda (e) #f))))))
              (and (pair? q) (equal? (car q) 'ok) (cadr q)))))
    (set! he-log (cons (list name (quotient (- (clock-us) t0) 1000) (if r 'ok 'no)) he-log))
    r))
(define (int-heur-stats) (list he-cur he-log he-info))
(define (int-heur-reset) (set! he-cur #f) (set! he-log '()) (set! he-info '()))

; (int-heur f x) → F (проверено) или #f; бюджет каждой ветки — int-heur-time-limit, struct (решение линейной системы) — 3 с
(define (int-heur f x)
  (set! he-info '()) (set! he-log '()) (set! he-cur #f)
  (let* ((lim int-heur-time-limit)
         (q (call-with-time-limit (* 2 lim)
              (lambda ()
                (or (he-branch 'ahyp lim (lambda () (he-ahyp f x)))
                    (he-branch 'inverse lim (lambda () (he-inverse f x)))
                    (he-branch 'hyp lim (lambda () (he-hyp f x)))
                    (he-branch 'tan lim (lambda () (he-tan f x)))
                    (he-branch 'pow lim (lambda () (he-pow f x)))
                    (he-branch 'struct 3 (lambda () (he-struct f x))))))))
    (and (pair? q) (equal? (car q) 'ok) (cadr q))))
