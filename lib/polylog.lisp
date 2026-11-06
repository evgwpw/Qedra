; polylog.lisp — полилогарифм Li_s(x) и функция Ламберта W₀(x): численные значения, сведение производных (шаг PL)
;
; Головы выражений: (polylog s x) — Li_s(x) = Σ xᵏ/kˢ, (lambert_w x) — главная ветвь W₀ (W e^W = x, W ≥ −1).
; Символьные тождества (значения, Li₁, s ≤ 0, производные, W(0), W(e), W(x eˣ)) — правила в lib/rules.lisp.
; Численно (в самом F#-ядре eval-num этих голов нет — решение шага: F# не менялся):
;   (polylog-num s x)    — Li_s(x) для целого s ≥ 1 и вещественного x ≤ 1 (число с плавающей точкой) | #f (x > 1: значение
;                          комплексное; s не целое или < 1). Ряд при |x| ≤ 1/2; 1/2 < x ≤ 1 — разложение Li_s(eᵘ) через ζ;
;                          −1 ≤ x < −1/2 — формула удвоения Li_s(x) + Li_s(−x) = 2^(1−s) Li_s(x²); x < −1 — инверсия
;                          Жонкьера (многочлен Бернулли от ln(−x)).
;   (lambert-w-num x)    — W₀(x) для x ≥ −1/e (итерации Галлея) | #f (x < −1/e: значение комплексное)
;   (polylog-evalf e)    — число для выражения с головами polylog / lambert_w (eval-num + подстановка значений) | #f
; Производная: правило polylog даёт (diff u v) под знаком — (pl-diff e) / (pl-resolve e) вычисляют остатки (diff u v).
; Внутренние имена: pl-.
(module polylog
  (export polylog-num lambert-w-num polylog-evalf pl-resolve pl-diff))

; ---------- вещественные числа ----------

; число (в том числе точное) или вычисляемая константа → float | #f
(define (pl-real x)
  (cond ((number? x) (* 1.0 x))
        ((pair? x) (let ((v (try (eval-num x) (lambda (err) #f)))) (and v (number? v) (* 1.0 v))))
        ((symbol? x) (let ((v (try (eval-num x) (lambda (err) #f)))) (and v (number? v) (* 1.0 v))))
        (else #f)))

(define (pl-ipow x n)
  (if (< n 0) (/ 1.0 (pl-ipow x (- n)))
      (let loop ((k n) (b x) (acc 1.0))
        (cond ((= k 0) acc)
              ((= (remainder k 2) 1) (loop (quotient k 2) (* b b) (* acc b)))
              (else (loop (quotient k 2) (* b b) acc))))))

(define (pl-fact n) (let loop ((i 2) (acc 1)) (if (> i n) acc (loop (+ i 1) (* acc i)))))
(define (pl-ln x) (eval-num (list 'log x)))
(define (pl-exp x) (eval-num (list 'exp x)))
(define (pl-pi) (eval-num 'pi))
(define (pl-binom n k) (/ (pl-fact n) (* (pl-fact k) (pl-fact (- n k)))))

; ---------- ζ(m) для целого m ≥ 2: Эйлер–Маклорен, N = 12 ----------
(define (pl-zeta m)
  (let ((n 12))
    (let loop ((k 1) (s 0.0))
      (if (< k n)
          (loop (+ k 1) (+ s (pl-ipow (/ 1.0 k) m)))
          (let ((nm (pl-ipow (/ 1.0 n) m)))
            (let tail ((j 1) (s (+ s (/ (* n nm) (- m 1)) (* 0.5 nm))) (poch m) (np (/ nm n)))
              ; poch = m(m+1)…(m+2j−2), np = N^(−m−2j+1)
              (if (> j 9)
                  s
                  (let ((term (* (* 1.0 (/ (bernoulli (* 2 j)) (pl-fact (* 2 j)))) poch np)))
                    (tail (+ j 1) (+ s term) (* poch (+ m (* 2 j) -1) (+ m (* 2 j))) (/ np (* n n)))))))))))

; ζ(−n), n ≥ 0 (точная рациональная): ζ(0) = −1/2, ζ(−n) = −B_{n+1}/(n+1)
(define (pl-zeta-neg n) (if (= n 0) -1/2 (- (/ (bernoulli (+ n 1)) (+ n 1)))))

; ---------- Li_s ----------

; Σ xᵏ/kˢ при |x| ≤ 1/2
(define (pl-li-series s x)
  (let loop ((k 1) (p x) (sum 0.0))
    (let ((term (/ p (pl-ipow (* 1.0 k) s))))
      (if (or (< (abs term) 1e-18) (> k 200))
          (+ sum term)
          (loop (+ k 1) (* p x) (+ sum term))))))

; x = eᵘ, u < 0, |u| ≤ ln 2: Li_s = u^(s−1)/(s−1)! (H_{s−1} − ln(−u)) + Σ_{k ≠ s−1} ζ(s−k) uᵏ/k!
(define (pl-li-mu s u)
  (let ((h (let loop ((i 1) (acc 0)) (if (> i (- s 1)) acc (loop (+ i 1) (+ acc (/ 1 i)))))))
    (let loop ((k 0) (uk 1.0) (sum 0.0))
      (cond ((> k (+ s 34)) sum)
            ((= k (- s 1))
             (loop (+ k 1) (* uk u)
                   (+ sum (* (/ uk (pl-fact k)) (- (* 1.0 h) (pl-ln (- u)))))))
            (else
             (let ((z (if (< k (- s 1)) (pl-zeta (- s k)) (* 1.0 (pl-zeta-neg (- k s))))))
               (loop (+ k 1) (* uk u) (+ sum (* z (/ uk (pl-fact k)))))))))))

; Li_s(x) для x < −1 через x⁻¹ (Жонкьер): Li_s(x) = −(−1)ˢ Li_s(1/x) − Σ_{j чётное} B_j(1/2)(−1)^{j/2}(2π)^j Lˢ⁻ʲ/(j!(s−j)!), L = ln(−x)
(define (pl-li-invert s x)
  (let ((l (pl-ln (- x))) (tp (* 2.0 (pl-pi))) (inner (pl-li-real s (/ 1.0 x))))
    (let loop ((j 0) (acc 0.0))
      (if (> j s)
          (- (* (if (pl-even? s) -1.0 1.0) inner) acc)
          (let* ((bj (* (- (pl-ipow-q 2 (- 1 j)) 1) (bernoulli j)))
                 (sg (if (= (remainder (quotient j 2) 2) 0) 1.0 -1.0))
                 (term (/ (* 1.0 bj sg (pl-ipow tp j) (pl-ipow l (- s j))) (* (pl-fact j) (pl-fact (- s j))))))
            (loop (+ j 2) (+ acc term)))))))

(define (pl-even? n) (= (remainder n 2) 0))
; 2^e для целого e (точное рациональное)
(define (pl-ipow-q b e) (if (< e 0) (/ 1 (^ b (- e))) (^ b e)))

; Li_s(x), целое s ≥ 2, вещественный x ≤ 1 → float
(define (pl-li-real s x)
  (cond ((= x 0.0) 0.0)
        ((= x 1.0) (pl-zeta s))
        ((<= (abs x) 0.5) (pl-li-series s x))
        ((> x 0.0) (pl-li-mu s (pl-ln x)))
        ((>= x -1.0)
         ; Li_s(x) = 2^(1−s) Li_s(x²) − Li_s(−x)
         (- (* 1.0 (pl-ipow-q 2 (- 1 s)) (pl-li-real s (* x x))) (pl-li-real s (- x))))
        (else (pl-li-invert s x))))

(define (polylog-num s x)
  (let ((xr (pl-real x)) (sr (pl-real s)))
    (cond ((not (and xr sr)) #f)
          ((not (= sr (floor sr))) #f)
          ((> xr 1.0) #f)
          ((= sr 1.0) (and (< xr 1.0) (- (pl-ln (- 1.0 xr)))))
          ((< sr 1.0) #f)
          (else (pl-li-real (floor sr) xr)))))

; ---------- W₀ ----------

(define (pl-w-guess x)
  (cond ((< x -0.25)
         (let ((p (eval-num (list 'sqrt (* 2.0 (+ (* (exp 1.0) x) 1.0))))))
           (+ -1.0 p (/ (* p p) -3.0) (* 0.1527777777777778 p p p))))
        ((< x 3.0)
         (let ((l (pl-ln (+ 1.0 x)))) (* l (- 1.0 (/ (pl-ln (+ 1.0 l)) (+ 2.0 l))))))
        (else (let* ((l1 (pl-ln x)) (l2 (pl-ln l1))) (+ (- l1 l2) (/ l2 l1))))))

(define (lambert-w-num x)
  (let ((xr (pl-real x)))
    (cond ((not xr) #f)
          ((= xr 0.0) 0.0)
          ((< xr (- (- (/ 1.0 (exp 1.0))) 1e-15)) #f)
          ((< xr (+ (- (/ 1.0 (exp 1.0))) 1e-14)) -1.0)
          (else
           (let loop ((w (pl-w-guess xr)) (i 0))
             (let* ((ew (pl-exp w)) (f (- (* w ew) xr))
                    (den (- (* ew (+ w 1.0)) (/ (* (+ w 2.0) f) (+ (* 2.0 w) 2.0))))
                    (w2 (- w (/ f den))))
               (if (or (> i 60) (< (abs (- w2 w)) (* 1e-16 (+ 1.0 (abs w2)))))
                   w2
                   (loop w2 (+ i 1)))))))))

; ---------- числа для выражений ----------

(define (pl-subst e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'polylog) (= (length e) 3))
         (let ((v (polylog-num (pl-subst (cadr e)) (pl-subst (caddr e))))) (or v e)))
        ((and (equal? (car e) 'lambert_w) (= (length e) 2))
         (let ((v (lambert-w-num (pl-subst (cadr e))))) (or v e)))
        (else (cons (car e) (map pl-subst (cdr e))))))

(define (polylog-evalf e)
  (let ((r (try (eval-num (pl-subst e)) (lambda (err) #f))))
    (and r (number? r) r)))

; ---------- производные: остатки (diff u v) после правила polylog ----------
; (pl-resolve e) — каждый (diff u v) с символом v заменяется вычисленной производной; затем simplify
(define (pl-resolve e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'diff) (= (length e) 3) (symbol? (caddr e)))
         (let ((d (diff (caddr e) (cadr e))))
           (if (equal? d e) e (pl-resolve d))))   ; неразрешимый остаток остаётся (без зацикливания)
        (else (cons (car e) (map pl-resolve (cdr e))))))

; (pl-diff x e) — производная с вычисленными остатками (для выражений с polylog)
(define (pl-diff x e)
  (let ((d (diff x e)))
    (if (contains-sym? d 'diff) (simplify (pl-resolve d)) d)))
