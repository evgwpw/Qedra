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

(define (ipl-answer e x)
  (let* ((sp (ipl-split e x)) (c (car sp)) (vs (cadr sp)))
    (or (ipl-lambert c vs x)
        (ipl-log-over-one-minus c vs x)
        (and (= (length vs) 2) (any? (lambda (f) (ipl-inv-x? f x)) vs)
             (let ((h (filter (lambda (f) (not (ipl-inv-x? f x))) vs)))
               (and (= (length h) 1) (ipl-over-x c (car h) x)))))))

(define (int-polylog e x d)
  (and (op-expr? e)
       (ipl-has-head? e '(polylog lambert_w log atanh))
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
              (ipl-has-head? ex '(polylog lambert_w log atanh))
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
