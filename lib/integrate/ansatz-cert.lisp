; integrate/ansatz-cert.lisp — строгая часть параллельного метода Блейка для f = S(x)·√q(x) (шаг INT.ANSATZ.8)
;
; Источник идей: S. Blake, «The parallel Risch–Norman method» I–III (arXiv 2608.29482, 2609.13643, 2610.04477),
; реализация автора — github.com/stblake/parallel_integrate_mixed (MIT, Copyright (c) 2026 Sam Blake; текст лицензии —
; THIRD-PARTY-NOTICES.md). Не построчный перевод: перенесены два факта части II — точная оценка знаменателя рациональной части
; (эрмитова форма: порядок полюса v ровно на 1 меньше порядка полюса f) и сертификат неэлементарности «ненулевой остаток при
; нулевых вычетах» — для простого радикала y² = q (q ∈ ℚ[x] без квадратов, deg q = n), f = S(x)·y, S ∈ ℚ(x).
;
; Теория. Над K = ℚ̄(x, y) по теореме Лиувилля f dx = dv + Σ cᵢ dlog uᵢ (cᵢ ℚ-независимы). Если у f dx все вычеты равны 0, то
; Σ cᵢ ord_P(uᵢ) = 0 при каждом месте P, значит ord_P(uᵢ) = 0 всюду, uᵢ — константы и логарифмов нет: f = v′, v = B·y,
; B ∈ ℚ̄(x) (усреднением по Галуа — над ℚ). Это ОДНО линейное дифференциальное уравнение B′ + (q′/2q)·B = S над ℚ(x):
;   ord_a(B′ + pB) = ord_a(B) − 1 в каждой конечной точке (p имеет простой полюс с вычетом 1/2 в корнях q), поэтому знаменатель B
;   — W = Π d^(k−1) по неприводимым d | знаменателя S кратности k ≥ 1 (в корнях q при k = 1 — B регулярна, но не равна 0);
;   S = (B′ + pB) + C/Π(d) + P: P — многочлен, C — степени < deg Π(d) по простым полюсам вне корней q — вычеты f dx
;   (C(a)·y(a)/d′(a)); ненулевой C — вычет ≠ 0 (возможны логарифмы, Пелль: сертификата нет);
;   P приводится оператором L(B₂) = (3/2)q′B₂ + qB₂′ (старший член a_n(3n/2 + j)·x^(n+j−1) ≠ 0) до степени ≤ n − 2;
;   P_red = 0 — ответ F = (B + qB₂)·y; P_red ≠ 0 при нулевых вычетах (в конечных корнях q они нулевые по чётности степеней,
;   при n нечётном и на ∞; при n чётном остаток на ∞ — линейная форма по коэффициентам ряда √(q̃(t)), t = 1/x) — первообразной
;   в элементарных функциях НЕТ: v = B₃·y, B₃ без конечных полюсов — многочлен, q | B₃, B₃ = qB₂, L(B₂) = P_red — степени ≥ n−1
;   при B₂ ≠ 0 — противоречие. Любое сомнение (параметры, не рациональный коэффициент, система не единственна) — «не знаю».
; Внутренние имена: ce-. Вызывается из integrate-api (int-unevaluated-final) и int-ansatz (ответ F).
(module integrate
  (export int-ansatz-ne int-ansatz-hermite int-ansatz-ne-info))

(define int-ansatz-cert-enabled #t)
(define ce-info '())
(define (int-ansatz-ne-info) ce-info)

; ---------- многочлены — списки коэффициентов по возрастанию (поверх bk-*) ----------
(define (ce-zeros k) (map (lambda (i) 0) (range k)))
(define (ce-xpow k) (append (ce-zeros k) '(1)))
(define (ce-add a b) (bk-trim (bk-padd a b)))
(define (ce-sub a b) (ce-add a (bk-pscale -1 b)))
(define (ce-mul a b) (bk-trim (bk-pmul a b)))
(define (ce-scale c a) (bk-trim (bk-pscale c a)))
(define (ce-coef p k) (if (< k (length p)) (nth p k) 0))
(define (ce-pow a k) (if (= k 0) '(1) (ce-mul a (ce-pow a (- k 1)))))
(define (ce-divmod a b)
  (let ((db (bk-deg b)) (lb (bk-lc b)))
    (let loop ((r (bk-trim a)) (q '()))
      (if (< (bk-deg r) db)
          (cons (bk-trim q) r)
          (let* ((sh (- (bk-deg r) db)) (c (/ (bk-lc r) lb))
                 (term (append (ce-zeros sh) (list c))))
            (loop (ce-sub r (ce-mul term b)) (ce-add q term)))))))
(define (ce-gcd a b)
  (if (null? (bk-trim b)) (bk-trim a) (ce-gcd b (cdr (ce-divmod a b)))))
(define (ce-rat-list? l) (every? bk-rat? l))

(define (ce-note! tag) (set! ce-info (list tag)) #f)

; разбор f = S·√r: (N D r n) — списки коэффициентов N, D (взаимно просты), r (без квадратов, deg n ≥ 3) или #f
(define (ce-parse f x)
  (let ((p (or (ce-parse-flat f x) (ce-parse-conj f x))))
    (cond ((not p) (ce-note! 'not-radical))
          (else
           (let* ((rat (car p)) (r (cadr p)) (n (caddr p)))
             (cond ((< n 1) (ce-note! 'degree))
                   (else
                    (let* ((t (together rat))
                           (N0 (bk-coefs (numer t) x)) (D0 (bk-coefs (denom t) x))
                           (q (bk-coefs r x)))
                      (cond ((not (and (ce-rat-list? N0) (ce-rat-list? D0) (ce-rat-list? q))) (ce-note! 'coefficients))
                            ((null? (bk-trim N0)) (ce-note! 'zero))
                            (else
                             (let* ((g (ce-gcd N0 D0))
                                    (N (car (ce-divmod N0 g))) (D (car (ce-divmod D0 g))))
                               (list N D q n))))))))))))

; путь 1: f = R(x)·r^(1/2) по bk-parse → (R r n)
(define (ce-parse-flat f x)
  (let ((p (try (bk-parse (simplify f) x) (lambda (e) #f))))
    (and (pair? p) (not (equal? (car p) 'reduced))
         (= (caddr p) 2) (= (cadddr p) 1)
         (list (car p) (cadr p) (nth p 4)))))

; путь 2 (суммы радикалов, ответ diff): половинные степени (^ u k/2) → u^((k−1)/2)·y, y² = u; together, приведение по y² = u,
; f = (a + b·y)/(c + d·y) = [(ac − bd·u) + (bc − ad)·y]/(c² − d²·u): рациональная часть обязана быть 0; S = (bc − ad)/(c² − d²u);
; √u = g·√r (r без квадратов): (S·g, r, deg r)
(define (ce-halves e x)
  (cond ((not (pair? e)) '())
        ((and (equal? (car e) '^) (= (length e) 3) (bk-rat? (nth e 2)) (not (integer? (nth e 2))))
         (if (and (= (denom (nth e 2)) 2) (bk-polyq? (nth e 1) x)) (list (expand (nth e 1))) 'bad))
        (else (foldl (lambda (acc u) (let ((h (ce-halves u x))) (if (or (equal? acc 'bad) (equal? h 'bad)) 'bad (append acc h)))) '() (cdr e)))))
(define (ce-subst-y e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) '^) (= (length e) 3) (bk-rat? (nth e 2)) (not (integer? (nth e 2))))
         (list '* (list '^ (nth e 1) (/ (- (numer (* 2 (nth e 2))) 1) 2)) 'ce-y))
        (else (cons (car e) (map ce-subst-y (cdr e))))))
; только +, *, целые степени, половинные степени многочленов, рациональные числа и x
(define (ce-alg? e x)
  (cond ((number? e) (bk-rat? e))
        ((symbol? e) (equal? e x))
        ((and (op-expr? e) (member? (car e) '(+ *))) (every? (lambda (u) (ce-alg? u x)) (cdr e)))
        ((and (op-expr? e) (equal? (car e) '^) (= (length e) 3))
         (and (bk-rat? (nth e 2))
              (or (integer? (nth e 2)) (and (= (denom (nth e 2)) 2) (bk-polyq? (nth e 1) x)))
              (ce-alg? (nth e 1) x)))
        (else #f)))
(define (ce-parse-conj f0 x)
  (let* ((f (simplify (bk-unsqrt f0))) (hs (if (ce-alg? f x) (ce-halves f x) 'bad)))
    (and (pair? hs) (not (equal? hs 'bad))
         (every? (lambda (u) (equal? u (car hs))) hs)
         (let* ((u (car hs))
                (t (together (simplify (ce-subst-y f))))
                (rel (list '+ (list '^ 'ce-y 2) (list '* -1 u)))
                (red (lambda (e) (poly-remainder (expand e) rel 'ce-y)))
                (cf (lambda (e) (let ((c (coefficients (red e) 'ce-y))) (list (if (null? c) 0 (car c)) (if (or (null? c) (null? (cdr c))) 0 (cadr c))))))
                (an (cf (numer t))) (cd (cf (denom t)))
                (a (car an)) (b (cadr an)) (c (car cd)) (d (cadr cd))
                (rat0 (expand (list '+ (list '* a c) (list '* -1 b d u))))
                (den (expand (list '+ (list '* c c) (list '* -1 d d u)))))
           (and (equal? rat0 0) (not (equal? den 0))
                (let* ((S (together (list '* (list '+ (list '* b c) (list '* -1 a d)) (list '^ den -1))))
                       (fl (factor-list u)) (cc (car fl)) (fs (cdr fl))
                       (r (expand (cons '* (cons cc (map (lambda (fk) (list '^ (car fk) (modulo (cadr fk) 2))) fs)))))
                       (g (cons '* (map (lambda (fk) (list '^ (car fk) (quotient (cadr fk) 2))) fs)))
                       (n (bk-deg (bk-coefs r x))))
                  (and (every? (lambda (fk) (bk-rat? (cadr fk))) fs)
                       (list (simplify (list '* S g)) r n))))))))

; ряд σ(t) = √(q̃(t)/a_n), q̃(t) = tⁿ·q(1/t): коэффициенты s₀ … s_K (рациональные)
(define (ce-sigma q K)
  (let* ((n (bk-deg q)) (an (bk-lc q))
         (g (lambda (k) (if (<= k n) (/ (ce-coef q (- n k)) an) 0)))
         (s (make-vector (+ K 1) 0)))
    (vset! s 0 1)
    (let loop ((k 1))
      (if (<= k K)
          (begin
            (vset! s k (/ (- (g k) (let sl ((i 1) (acc 0)) (if (< i k) (sl (+ i 1) (+ acc (* (vref s i) (vref s (- k i))))) acc))) 2))
            (loop (+ k 1)))))
    s))

; вычет f dx на ∞ (с точностью до общего множителя √a_n): −Σ pᵢ·s_{i+n/2+1}, n чётное
(define (ce-res-inf P q)
  (let* ((n (bk-deg q)) (h (quotient n 2)) (K (+ (bk-deg P) h 2)) (s (ce-sigma q K)))
    (let loop ((i 0) (acc 0))
      (if (> i (bk-deg P)) (- acc)
          (loop (+ i 1) (+ acc (* (ce-coef P i) (vref s (+ i h 1)))))))))

; приведение P оператором L до степени ≤ n − 2: (P_red . B₂)
(define (ce-reduce P q)
  (let* ((n (bk-deg q)) (an (bk-lc q)) (qd (bk-pder q)))
    (let loop ((P (bk-trim P)) (B2 '()))
      (if (< (bk-deg P) (- n 1))
          (cons P B2)
          (let* ((j (- (bk-deg P) (- n 1)))
                 (c (/ (bk-lc P) (* an (+ (/ (* 3 n) 2) j))))
                 (xj (ce-xpow j))
                 (L (ce-add (ce-scale 3/2 (ce-mul qd xj)) (ce-mul q (bk-pder xj)))))
            (loop (ce-sub P (ce-scale c L)) (ce-add B2 (ce-scale c xj))))))))

; Эрмитова редукция: (status . данные); status: elementary (F) | nonelementary | residue | unknown
; дёшево: есть ли в f корень (sqrt …) или половинная степень (быстрый отказ для остальных подынтегральных)
(define (ce-has-half? e)
  (and (pair? e)
       (or (equal? (car e) 'sqrt)
           (and (equal? (car e) '^) (= (length e) 3) (bk-rat? (nth e 2)) (not (integer? (nth e 2))) (= (denom (nth e 2)) 2))
           (any? ce-has-half? (cdr e)))))

(define (ce-hermite f x)
  (let ((ps (if (ce-has-half? f) (ce-parse f x) #f)))
    (if (not ps)
        '(unknown . parse)
        (let* ((N (car ps)) (D (cadr ps)) (q (caddr ps)) (n (cadddr ps))
               (qd (bk-pder q))
               (fl (factor-list (bk-poly-expr D x)))
               (facs (map (lambda (fk) (cons (bk-coefs (car fk) x) (cadr fk))) (cdr fl)))
               (branch? (lambda (d) (null? (cdr (ce-divmod q d)))))
               (W (foldl (lambda (acc fk) (ce-mul acc (ce-pow (car fk) (max 0 (- (cdr fk) 1))))) '(1) facs))
               (dprod (foldl (lambda (acc fk) (if (branch? (car fk)) acc (ce-mul acc (car fk)))) '(1) facs))
               (dw (bk-deg W)) (dc (bk-deg dprod))
               (degS (- (bk-deg N) (bk-deg D)))
               (e (+ (max degS 0) n))
               (nB (+ dw n))
               (W2 (ce-mul W W))
               (twoqW2 (ce-scale 2 (ce-mul q W2)))
               (Zd (ce-divmod (ce-mul twoqW2 dprod) D)))
          (cond
            ((not (null? (cdr Zd))) '(unknown . denominator))
            (else
             (let* ((rhs (ce-mul N (car Zd)))
                    (Wd (bk-pder W))
                    (colB (map (lambda (i)
                                 (let* ((xi (ce-xpow i)) (xd (bk-pder xi))
                                        (t1 (ce-mul (ce-sub (ce-mul xd W) (ce-mul xi Wd)) (ce-scale 2 q)))
                                        (t2 (ce-mul qd (ce-mul xi W))))
                                   (ce-mul (ce-add t1 t2) dprod)))
                               (range nB)))
                    (colC (map (lambda (i) (ce-mul twoqW2 (ce-xpow i))) (range dc)))
                    (colP (map (lambda (i) (ce-mul (ce-mul twoqW2 dprod) (ce-xpow i))) (range (+ e 1))))
                    (cols (append colB colC colP))
                    (maxlen (foldl (lambda (a c) (max a (length c))) (length rhs) cols))
                    (rows (map (lambda (k) (append (map (lambda (c) (ce-coef c k)) cols) (list (- (ce-coef rhs k)))))
                               (range maxlen)))
                    (ns (nullspace rows))
                    (nu (length cols)))
               (cond
                 ((> (length ns) 1) '(unknown . nonunique))
                 ((or (null? ns) (= (nth (car ns) nu) 0)) '(unknown . inconsistent))
                 (else
                  (let* ((v (car ns)) (v (map (lambda (c) (/ c (nth v nu))) v))
                         (Bn (bk-trim (take v nB)))
                         (C (take (drop v nB) dc))
                         (P (bk-trim (drop (take v nu) (+ nB dc)))))
                    (cond
                      ((any? (lambda (c) (not (= c 0))) C) '(residue . finite))
                      (else
                       (let* ((red (ce-reduce P q)) (Pr (car red)) (B2 (cdr red)))
                         (cond
                           ((null? Pr)
                            ; F = (Bn/W + q·B2)·√q
                            (cons 'elementary
                                  (list '* (list '+ (list '* (bk-poly-expr Bn x) (list '^ (bk-poly-expr W x) -1))
                                                 (list '* (bk-poly-expr q x) (bk-poly-expr B2 x)))
                                        (list '^ (bk-poly-expr q x) 1/2))))
                           ((and (ce-even? n) (not (= (ce-res-inf Pr q) 0))) '(residue . infinity))
                           (else '(nonelementary . holomorphic))))))))))))))))

(define (ce-even? n) (= (modulo n 2) 0))

; #t — ДОКАЗАНО: первообразной в элементарных функциях нет (только описанный класс); иначе #f
(define (int-ansatz-ne f x)
  (and int-ansatz-cert-enabled
       (let ((r (try (ce-hermite f x) (lambda (e) '(unknown . error)))))
         (set! ce-info (list (car r) (cdr r)))
         (equal? (car r) 'nonelementary))))

; F (F′ = f, int-check) или #f
(define (int-ansatz-hermite f x)
  (and int-ansatz-cert-enabled
       (let ((r (try (ce-hermite f x) (lambda (e) '(unknown . error)))))
         (set! ce-info (list (car r)))
         (and (equal? (car r) 'elementary)
              (let ((F (simplify (cdr r))))
                (and (int-check F f x) F))))))
