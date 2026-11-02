; genus0.lisp — ∫R(x, u) dx, u = P(x)^{1/q}, кривая y^q = P(x) рода 0 (шаг A3′.2)
; Параметризация (штатная или суперэллиптический fallback) → рациональная функция от t →
; integrate по t → обратная подстановка t = t(x, u); сертификат производной.
(module integrate)

; ---------- выделение единственного радикала ----------

(define (gn-rad-nodes e)
  (cond ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (number? (caddr e)) (not (integer? (caddr e))))
         (list e))
        ((and (pair? e) (equal? (car e) 'sqrt) (= (length e) 2))
         (list (list '^ (cadr e) 1/2)))
        ((pair? e) (append-map gn-rad-nodes e))
        (else '())))

; (base q) или #f: все радикалы — степени P^{k/q} с одним q > 1
(define (gn-single-radical e)
  (let ((ns (gn-rad-nodes e)))
    (if (null? ns)
        #f
        (let* ((b (nth (car ns) 1))
               (q (denom (nth (car ns) 2))))
          (if (and (> q 1)
                   (every? (lambda (n) (and (equal? (nth n 1) b)
                                            (= (denom (nth n 2)) q)))
                           ns))
              (list b q)
              #f)))))

; ---------- суперэллиптический fallback: P = (x-a)^2 R(x), R линейна ----------

(define (gn-linear? p x)
  (and p (not (and (pair? p) (equal? (car p) '/)))
       (let ((d (try (degree p x) (lambda (e) #f))))
         (and d (= d 1)))))

(define (gn-superelliptic P x y q)
  (let ((rs (try (set->list (solve (list '= P 0) x)) (lambda (e) '()))))
    (let loop ((ps rs))
      (if (null? ps)
          #f
          (let ((a (car ps)))
            (if (not (number? a))
                (loop (cdr ps))
                (let* ((u (list '- x a))
                       (R (try (simplify (cancel (list '/ P (list '^ u 2))))
                               (lambda (e) #f))))
                  (if (not (and R (gn-linear? R x)))
                      (loop (cdr ps))
                      (let* ((r1 (try (coeff R x 1) (lambda (e) #f)))
                             (r0 (try (coeff R x 0) (lambda (e) #f)))
                             (xt (if (and (number? r1) (number? r0))
                                     (cond ((= q 2) (simplify (list '/ (list '- (list '^ 't 2) r0) r1)))
                                           ((= q 3) (simplify (list '/ (list '+ r0 (list '* a (list '^ 't 3)))
                                                                     (list '- (list '^ 't 3) r1))))
                                           (else #f))
                                     #f)))
                        (if (not xt)
                            (loop (cdr ps))
                            (let* ((yt (simplify (list '* 't (list '- xt a))))
                                   (F (list '- (list '^ y q) P))
                                   (par (list xt yt)))
                              (if (parametrization-check F x y par 't)
                                  (list xt yt (list '/ y u) a)
                                  (loop (cdr ps))))))))))))))

; ---------- подстановка и проверка ----------

(define (gn-subst e x xt P q yt)
  (cond ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (equal? (nth e 1) P) (number? (nth e 2))
              (not (integer? (nth e 2))) (= (denom (nth e 2)) q))
         (let ((k (numer (nth e 2))))
           (if (= k 1) yt (list '^ yt k))))
        ((and (pair? e) (equal? (car e) 'sqrt) (= (length e) 2) (equal? (nth e 1) P))
         yt)
        ((equal? e x) xt)
        ((pair? e) (map (lambda (z) (gn-subst z x xt P q yt)) e))
        (else e)))

(define (gn-real-num v)
  (let ((z (try (eval-num v) (lambda (e) #f))))
    (and (number? z) z)))

; численная проверка ветви: u(x0) = y(t0), t0 = inv(x0, u0)
; числовое выражение (может быть комплексным) и его части
(define (gn-num-expr v)
  (try (eval-num v) (lambda (e) #f)))

(define (gn-comp-parts v)
  (let ((z (gn-num-expr v)))
    (cond ((number? z) (list z 0))
          ((and (pair? z) (equal? (car z) '*) (number? (nth z 1)) (equal? (nth z 2) '%i))
           (list 0 (nth z 1)))
          ((and (pair? z) (equal? (car z) '+) (number? (nth z 1))
                (pair? (nth z 2)) (equal? (car (nth z 2)) '*) (equal? (nth (nth z 2) 2) '%i))
           (list (nth z 1) (nth (nth z 2) 1)))
          (else #f))))

(define (gn-comp-close? p u0)
  (and p (< (abs (- (car p) u0)) 1e-7) (< (abs (cadr p)) 1e-7)))

(define (gn-branch-ok? P q xt yt inv x)
  (let loop ((xs (list 1/2 3/4 2 5/3)) (n 0))
    (cond ((null? xs) (> n 0))
          (else
           (let* ((u0 (gn-real-num (subst (list x (car xs)) (list '^ P (/ 1 q)))))
                  (t0 (and u0 (gn-num-expr (subst (list 'y u0) (subst (list x (car xs)) inv))))))
             (if (and u0 t0)
                 (let ((v (gn-comp-parts (subst (list 't t0) yt))))
                   (if (and v (gn-comp-close? v u0)) (loop (cdr xs) (+ n 1)) #f))
                 (loop (cdr xs) n)))))))

; режим ветви: principal, flip (−y(t), только чётное q) или #f
(define (gn-branch-mode P q xt yt inv x)
  (if (gn-branch-ok? P q xt yt inv x)
      'principal
      (if (even? q)
          (let ((yt2 (simplify (list '- yt))))
            (if (gn-branch-ok? P q xt yt2 inv x) 'flip #f))
          (let loop ((k 1))
            (if (>= k q)
                #f
                (let* ((w (list 'exp (list '/ (list '* 2 '%i 'pi k) q)))
                       (yt2 (simplify (list '* yt w))))
                  (if (gn-branch-ok? P q xt yt2 inv x)
                      (list 'root k)
                      (loop (+ k 1)))))))))
(define (gn-num-check-at ans e x t)
  (let* ((h 1/100000)
         (v1 (gn-real-num (subst (list x (+ t h)) ans)))
         (v0 (gn-real-num (subst (list x (- t h)) ans)))
         (ref (gn-real-num (subst (list x t) e))))
    (and (number? v1) (number? v0) (number? ref)
         (< (abs (- (/ (- v1 v0) (* 2 h)) ref)) 1/1000))))

(define (gn-ok? ans e x)
  (and ans (or (int-check ans e x)
               (and (gn-num-check-at ans e x 1/2)
                    (gn-num-check-at ans e x 3/4)
                    (gn-num-check-at ans e x 2)))))

; есть ли у P кратный корень (иначе кривая гладкая: род 0 только у коники — gn-conic?)
(define (gn-repeated? P x)
  (try (any? (lambda (fm) (> (cadr fm) 1)) (cdr (factor-list P)))
       (lambda (e) #f)))

; R3.1: гладкая коника y² = P, deg P ∈ {1, 2} без кратных корней — тоже род 0 (подстановки Эйлера =
; параметризация пучком через рациональную точку; нет точки над ℚ — parametrize-curve отказывает → #f)
(define (gn-conic? P q x)
  (and (= q 2) (polynomial? P x)
       (let ((dg (try (degree (expand P) x) (lambda (e) #f))))
         (and dg (or (= dg 1) (= dg 2))))))

; ---------- параметризация с обратной и ветвью ----------

; R3.1: (gn-param P q x) → (xt yt inv mode) | #f — кривая y^q = P(x) рода 0 по параметру 't:
; x = xt(t), u = P^{1/q} = yt(t) (ветвь уже выбрана: mode principal | flip | (root k)), t = inv(x, y)
(define (gn-param P q x)
  (let* ((Pe (expand P)) (y 'y)
         (F (list '- (list '^ y q) Pe))
         (par (try (parametrize-curve F x y 't) (lambda (err) #f)))
         (fb (if (and (list? par) (= (length par) 2)
                      (parametrization-check F x y par 't))
                 par
                 (gn-superelliptic Pe x y q))))
    (if (not fb)
        #f
        (let* ((xt (nth fb 0)) (yt (nth fb 1))
               (inv (if (= (length fb) 4) (nth fb 2) 'unknown))
               (inv (if (equal? inv 'unknown)
                        (parametrize-curve-inverse F x y 't (list xt yt))
                        inv))
               (mode (and (not (equal? inv 'unknown))
                          (gn-branch-mode P q xt yt inv x)))
               (root (and (list? mode) (equal? (car mode) 'root)))
               (k (if root (cadr mode) 0))
               (w (if root (list 'exp (list '/ (list '* 2 '%i 'pi k) q)) 1))
               (yt2 (cond ((equal? mode 'flip) (simplify (list '- yt)))
                          (root (simplify (list '* yt w)))
                          (else yt))))
          (if (not mode) #f (list xt yt2 inv mode))))))

(define (gn-record-branch! mode P q)
  (cond ((equal? mode 'flip)
         (record-condition (list 'genus0-branch-flip P q)
                           "интеграл рода 0: выбрана ветвь −y(t)"))
        ((and (list? mode) (equal? (car mode) 'root))
         (record-condition (list 'genus0-branch-root (cadr mode) q)
                           "интеграл рода 0: выбрана ветвь y(t)·ω^k"))
        (else #t)))

; ---------- стратегия ----------

; кратный корень — здесь (до алгебраической стратегии); гладкая коника — int-genus0-conic
; (mixed.lisp, после alg-int-strategy: её ответы для коник короче). Коника — только при d = 0: внутри
; подстановок/по частям (d ≥ 1) её успех перебивает более короткие формы Чебышёва (∫x³√(1+x²), ∫dx/(x√(1+x³)))
; и кормит int-parts новыми v (каскад уходит в минуты)
(define (int-genus0 e x d)
  (let ((sr (gn-single-radical e)))
    (and sr (gn-repeated? (car sr) x) (gn-integrate e x sr))))

(define (int-genus0-conic e x d)
  (let ((sr (and (= d 0) (gn-single-radical e))))
    (and sr (not (gn-repeated? (car sr) x)) (gn-conic? (car sr) (cadr sr) x)
         (gn-integrate e x sr))))

; sr = (P q): параметризация → рациональная функция от t → integrate по t → обратная подстановка; сертификат gn-ok?
; Шаги: рамка gn-integration; параметризация, интеграл по t и сертификат — ключевые шаги (расчёт тихий, alg-run)
(define (gn-integrate e x sr)
  (with-step ('gn-integration "Кривая рода 0: параметризация и интеграл по параметру" (int-form e x)
              :comment "рациональная параметризация кривой, интеграл рациональной функции от t, обратная подстановка, проверка"
              :after int-p)
    (alg-run (lambda () (gn-integrate-raw e x sr)))))

(define (gn-integrate-raw e x sr)
  (let* ((P (car sr)) (q (cadr sr)) (y 'y)
         (pp (gn-param P q x))
         (u (list '^ P (/ 1 q))))
    (if (not pp)
        #f
        (let* ((xt (nth pp 0)) (yt2 (nth pp 1)) (inv2 (nth pp 2)) (mode (nth pp 3))
               (sub (gn-subst e x xt P q yt2))
               (dx (diff 't xt))
               (g (simplify (together (list '* sub dx)))))
          (alg-step 'gn-parametrization "Параметризация кривой рода 0"
                    (string-append "x = " (alg-mp xt) ", y = " (alg-mp yt2) "; обратно t = " (alg-mp inv2))
                    (list '= (list '^ 'y q) (int-p P)) (list 'list xt yt2))
          (if (not (contains-sym? g 'y))
              (let* ((G (try (integrate g 't) (lambda (err) #f))))
                (if (not G) #f
                    (let* ((ans (try (simplify (subst (list 't (subst (list y u) inv2)) G))
                                     (lambda (err) #f))))
                      (alg-step 'gn-rational-integral "Интеграл по параметру t"
                                "подынтегральная функция рациональна по t: интегрируем (Эрмит, ЛРТ), затем обратная подстановка t = t(x, y)"
                                (int-form g 't) G)
                      (if (and ans (gn-ok? ans e x))
                          (begin
                            (gn-record-branch! mode P q)
                            (record-condition (list 'genus0-param P q)
                                              "интеграл рода 0: параметризация и обратная подстановка")
                            (alg-note-cert ans e 'diff)
                            ans)
                          #f))))
              #f)))))

(int-add-strategy int-genus0)
