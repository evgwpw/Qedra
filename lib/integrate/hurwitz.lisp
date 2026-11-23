; integrate/hurwitz.lisp — ∫ Σ cᵢ·x^mᵢ·ζ(σᵢ, a+bx) dx: интегрирование по частям по сумме целиком (шаг ZETA.HURWITZ)
;
; Правила Rubi 8.7 (#4, #5) разбирают слагаемые по одному: сумма b·s·ζ(s+1, u)/x + ζ(s, u)/x² даёт два «неберущихся»
; ∫ζ/x, которые взаимно уничтожаются (ответ −ζ(s, u)/x). Здесь слагаемые приводятся к виду c·x^m·ζ(σ, u) (c без x, m целое,
; u = a + b·x одно для всех; ψ^(n)(u) — через ζ(n+1, u)) и редуцируются по частям, пока не останутся только m = −1:
;   m ≤ −2:  ∫x^m ζ(σ, u) = x^(m+1)·ζ(σ, u)/(m+1) + (b·σ/(m+1))·∫x^(m+1)·ζ(σ+1, u)
;   m ≥ 0, σ ≠ 2:  ∫x^m ζ(σ, u) = −x^m·ζ(σ−1, u)/(b(σ−1)) + (m/(b(σ−1)))·∫x^(m−1)·ζ(σ−1, u)
;   σ = 2 (ζ(2, u) = ψ'(u), ζ(1, ·) нет):  m = 0 → ψ(u)/b;  m = 1 → x·ψ(u)/b − log Γ(u)/b²; m ≥ 2 — отказ (нужна ψ^(−2))
; (производная d/du ζ(σ, u) = −σ·ζ(σ+1, u)). Остаток с m = −1 должен сократиться полностью (иначе первообразной в этом классе
; нет — ∫ζ(s, u)/x не берётся), ответ принимается только после int-check. Внутренние имена: ihz-.
(module integrate
  (export))

(define (ihz-find-u e x)         ; первый аргумент u двуарной (zeta σ u) с x
  (cond ((not (pair? e)) #f)
        ((and (equal? (car e) 'zeta) (= (length e) 3) (not (x-free? (caddr e) x))) (simplify (caddr e)))
        (else (let loop ((l (cdr e)))
                (if (null? l)
                    #f
                    (or (ihz-find-u (car l) x) (loop (cdr l))))))))

; слагаемое → (c m σ) | #f
(define (ihz-term t x u)
  (let ((fs (if (and (pair? t) (equal? (car t) '*)) (cdr t) (list t))))
    (let loop ((fs fs) (c 1) (m 0) (s #f))
      (cond ((null? fs) (and s (list c m s)))
            ((x-free? (car fs) x) (loop (cdr fs) (* c (car fs)) m s))
            ((equal? (car fs) x) (loop (cdr fs) c (+ m 1) s))
            ((and (pair? (car fs)) (equal? (car (car fs)) '^) (equal? (cadr (car fs)) x) (integer? (caddr (car fs))))
             (loop (cdr fs) c (+ m (caddr (car fs))) s))
            ((and (pair? (car fs)) (equal? (car (car fs)) 'zeta) (= (length (car fs)) 3) (not s)
                  (x-free? (cadr (car fs)) x) (equal? (simplify (caddr (car fs))) u))
             (loop (cdr fs) c m (cadr (car fs))))
            (else #f)))))

(define (ihz-z s u) (list 'zeta s u))
(define (ihz-xm x m) (if (= m 0) 1 (list '^ x m)))

; один шаг по слагаемому (c m σ): (граница . новые-слагаемые) | #f (отказ); m = −1 здесь не бывает
(define (ihz-step term x u b)
  (let ((c (car term)) (m (cadr term)) (s (caddr term)))
    (cond ((<= m -2)
           (cons (/ (* c (ihz-xm x (+ m 1)) (ihz-z s u)) (+ m 1))
                 (list (list (/ (* c b s) (+ m 1)) (+ m 1) (+ s 1)))))
          ((equal? s 1) #f)
          ((equal? s 2)
           (cond ((= m 0) (cons (/ (* c (list 'psi u)) b) '()))
                 ((= m 1) (cons (- (/ (* c x (list 'psi u)) b) (/ (* c (list 'log (list 'gamma u))) (* b b))) '()))
                 (else #f)))
          (else (cons (- (/ (* c (ihz-xm x m) (ihz-z (- s 1) u)) (* b (- s 1))))
                      (if (= m 0) '() (list (list (/ (* c m) (* b (- s 1))) (- m 1) (- s 1)))))))))

; → первообразная | #f
(define (ihz-run f x)
  (let* ((f1 (expand (hz-psi->zeta f))) (u (ihz-find-u f1 x)))
    (and u (polynomial? u x) (= (degree u x) 1)
         (let* ((b (coeff u x 1))
                (ts (map (lambda (t) (ihz-term t x u)) (if (and (pair? f1) (equal? (car f1) '+)) (cdr f1) (list f1)))))
           (and (every? (lambda (t) t) ts)
                (let loop ((work ts) (bound '()) (rest '()) (steps 0))
                  (cond ((> steps 200) #f)
                        ((null? work) (ihz-finish bound rest f x))
                        ((= (cadr (car work)) -1) (loop (cdr work) bound (cons (car work) rest) steps))
                        (else (let ((r (ihz-step (car work) x u b)))
                                (and r (loop (append (cdr r) (cdr work)) (cons (car r) bound) rest (+ steps 1))))))))))))

; остаток m = −1 по σ: все коэффициенты сокращаются
(define (ihz-finish bound rest f x)
  (let ((groups (foldl (lambda (acc t)
                         (let ((hit (assoc (caddr t) acc)))
                           (if hit
                               (map (lambda (g) (if (equal? (car g) (caddr t)) (cons (car g) (+ (cdr g) (car t))) g)) acc)
                               (cons (cons (caddr t) (car t)) acc))))
                       '() rest)))
    (and (every? (lambda (g) (equal? (simplify (cdr g)) 0)) groups)
         (let ((F (simplify (apply + bound))))
           (and (not (equal? F 0)) F)))))

(define (int-hz-fallback f x)
  (and (or (contains-sym? f 'zeta) (contains-sym? f 'psi) (contains-sym? f 'poly_gamma))
       (let ((F (int-guard (lambda () (ihz-run f x)))))
         (and F (not (int-has-integrate? F))
              (int-guard (lambda () (int-check F f x)))
              F))))
