; cantor.lisp — Шаг R5.3a: арифметика Кантора (представление Мамфорда) якобиана y² = P(x), deg P = 2g + 1.
; Шаг R5.3b (в конце файла): cantor-torsion-check — «кручение / не кручение» для дивизора вычетов δ (используется в hyp-torsion-order).
; Шаг R5.3c2: тот же код над K = ℚ(√d): p = (d) — «поле» K, элемент — пара (a b); места над K — cantor-torsion-check P x D d [B].
;
; Кривая — (cantor-curve P x [p]): над ℚ без p, над 𝔽_p с простым нечётным p.  Одна точка O на ∞.
; Класс D − deg(D)·O  ↔  пара (u v) списков коэффициентов по возрастанию степени:
;   u монический, deg u ≤ g, deg v < deg u, u | v² − P.  Нуль группы — ((1) ()).
; Старший коэффициент P может быть ≠ 1: формулы Кантора не требуют монической модели
; (y − v(x) имеет нули в точках (x, v(x)), x — корни v² − P; приведение u′ = (P − v²)/u делается монической).
; Чётная степень P (две точки на ∞) — вне этого файла (R5.3c): понятная ошибка.

(module integrate
  (export cantor-curve cantor-curve-mod-p cantor-valid? cantor-zero? cantor-neg cantor-add cantor-double
          cantor-mul cantor-reduce cantor-from-points cantor-mod-p cantor-order-upto cantor-order-mod-p
          cantor-torsion-check cantor-multiples))

; ---------- многочлены над ℚ (p = 0) или 𝔽_p: списки коэффициентов по возрастанию, без хвостовых нулей ----------

(define (cn-nrm p c) (if (= p 0) c (modulo c p)))

; R5.3c2: p = (d) — поле K = ℚ(√d), элемент — пара рациональных (a b) = a + b√d (нуль — (0 0)); тот же код Кантора над K
(define (cn-k? p) (pair? p))
(define ck-zero '(0 0))
(define ck-one '(1 0))
(define (ck+ x y) (list (+ (car x) (car y)) (+ (cadr x) (cadr y))))
(define (ck- x y) (list (- (car x) (car y)) (- (cadr x) (cadr y))))
(define (ck* p x y)
  (let ((a (car x)) (b (cadr x)) (c (car y)) (e (cadr y)))
    (list (+ (* a c) (* (car p) b e)) (+ (* a e) (* b c)))))
(define (ck-inv p x)
  (let ((nm (- (* (car x) (car x)) (* (car p) (cadr x) (cadr x)))))
    (if (= nm 0) (error "cantor: элемент K не обратим" x) (list (/ (car x) nm) (/ (- (cadr x)) nm)))))
(define (cn-ez? c) (if (pair? c) (and (= (car c) 0) (= (cadr c) 0)) (= c 0)))
(define (cn-one? c) (if (pair? c) (and (= (car c) 1) (= (cadr c) 0)) (= c 1)))
(define (cn-one-of p) (if (pair? p) ck-one 1))

(define (cn-inv p c)
  (cond
    ((pair? p) (ck-inv p c))
    ((= p 0) (/ 1 c))
    (else
      (let loop ((r0 p) (r1 (modulo c p)) (t0 0) (t1 1))
        (if (= r1 0)
            (if (= r0 1) (modulo t0 p) (error "cantor: элемент не обратим по модулю" p))
            (let ((q (quotient r0 r1)))
              (loop r1 (- r0 (* q r1)) t1 (- t0 (* q t1)))))))))

; рациональное число → элемент поля; знаменатель, кратный p, — ошибка
(define (cn-in p c)
  (cond ((pair? p) (list c 0))
        ((= p 0) c)
        ((integer? c) (modulo c p))
        (else
         (let ((d (denom c)))
           (if (= 0 (modulo d p))
               (error "cantor: знаменатель делится на p" c p)
               (modulo (* (numer c) (cn-inv p d)) p))))))

(define (cn-trim l)
  (let loop ((r (reverse l)))
    (if (and (pair? r) (cn-ez? (car r))) (loop (cdr r)) (reverse r))))

(define (cn-deg a) (- (length a) 1))
(define (cn-lc a) (car (reverse a)))

(define (cn-add p a b)
  (let loop ((a a) (b b) (acc '()))
    (cond ((null? a) (cn-trim (append (reverse acc) b)))
          ((null? b) (cn-trim (append (reverse acc) a)))
          (else (loop (cdr a) (cdr b)
                      (cons (if (pair? p) (ck+ (car a) (car b)) (cn-nrm p (+ (car a) (car b)))) acc))))))

(define (cn-neg p a) (map (lambda (c) (if (pair? p) (ck- ck-zero c) (cn-nrm p (- c)))) a))
(define (cn-sub p a b) (cn-add p a (cn-neg p b)))
(define (cn-scale p a k) (cn-trim (map (lambda (c) (if (pair? p) (ck* p c k) (cn-nrm p (* c k)))) a)))
(define (cn-monic p a) (cn-scale p a (cn-inv p (cn-lc a))))

; произведение многочленов над K (элементы — пары)
(define (ck-mul p a b)
  (if (or (null? a) (null? b))
      '()
      (let* ((nb (length b)) (r (make-vector (+ (length a) nb -1) ck-zero)) (bv (list->vector b)))
        (let loop ((i 0) (as a))
          (if (null? as)
              (cn-trim (vector->list r))
              (let ((ai (car as)))
                (if (not (cn-ez? ai))
                    (let inner ((j 0))
                      (if (< j nb)
                          (begin
                            (vset! r (+ i j) (ck+ (vref r (+ i j)) (ck* p ai (vref bv j))))
                            (inner (+ j 1)))
                          '()))
                    '())
                (loop (+ i 1) (cdr as))))))))

; (q . r) над K
(define (ck-divmod p a b)
  (let ((na (length a)) (nb (length b)))
    (if (< na nb)
        (cons '() a)
        (let* ((r (list->vector a)) (bv (list->vector b))
               (ilb (ck-inv p (vref bv (- nb 1))))
               (q (make-vector (+ (- na nb) 1) ck-zero)))
          (let loop ((k (- na 1)))
            (if (< k (- nb 1))
                (cons (cn-trim (vector->list q)) (cn-trim (take (vector->list r) (- nb 1))))
                (let ((rk (vref r k)))
                  (if (cn-ez? rk)
                      (loop (- k 1))
                      (let ((c (ck* p rk ilb)) (s (- k (- nb 1))))
                        (vset! q s c)
                        (let inner ((j 0))
                          (if (< j nb)
                              (begin
                                (vset! r (+ s j) (ck- (vref r (+ s j)) (ck* p c (vref bv j))))
                                (inner (+ j 1)))
                              '()))
                        (loop (- k 1)))))))))))

(define (cn-mul p a b)
  (if (pair? p)
      (ck-mul p a b)
      (cn-mul-fp p a b)))

(define (cn-mul-fp p a b)
  (if (or (null? a) (null? b))
      '()
      (let* ((nb (length b)) (r (make-vector (+ (length a) nb -1) 0)) (bv (list->vector b)))
        (let loop ((i 0) (as a))
          (if (null? as)
              (cn-trim (vector->list r))
              (let ((ai (car as)))
                (if (not (= ai 0))
                    (let inner ((j 0))
                      (if (< j nb)
                          (begin
                            (vset! r (+ i j) (cn-nrm p (+ (vref r (+ i j)) (* ai (vref bv j)))))
                            (inner (+ j 1)))
                          '()))
                    '())
                (loop (+ i 1) (cdr as))))))))

; (q . r), b ≠ 0
(define (cn-divmod p a b)
  (if (pair? p) (ck-divmod p a b) (cn-divmod-fp p a b)))

(define (cn-divmod-fp p a b)
  (let ((na (length a)) (nb (length b)))
    (if (< na nb)
        (cons '() a)
        (let* ((r (list->vector a)) (bv (list->vector b))
               (ilb (cn-inv p (vref bv (- nb 1))))
               (q (make-vector (+ (- na nb) 1) 0)))
          (let loop ((k (- na 1)))
            (if (< k (- nb 1))
                (cons (cn-trim (vector->list q)) (cn-trim (take (vector->list r) (- nb 1))))
                (let ((rk (vref r k)))
                  (if (= rk 0)
                      (loop (- k 1))
                      (let ((c (cn-nrm p (* rk ilb))) (s (- k (- nb 1))))
                        (vset! q s c)
                        (let inner ((j 0))
                          (if (< j nb)
                              (begin
                                (vset! r (+ s j) (cn-nrm p (- (vref r (+ s j)) (* c (vref bv j)))))
                                (inner (+ j 1)))
                              '()))
                        (loop (- k 1)))))))))))

(define (cn-mod p a b) (cdr (cn-divmod p a b)))

(define (cn-quot-exact p a b)
  (let ((qr (cn-divmod p a b)))
    (if (null? (cdr qr)) (car qr) (error "cantor: деление не точное (неверное представление)"))))

; расширенный Евклид (g s t): g = s·a + t·b, g монический (g = 0 при a = b = 0)
(define (cn-egcd p a b)
  (let loop ((r0 a) (r1 b) (s0 (list (cn-one-of p))) (s1 '()) (t0 '()) (t1 (list (cn-one-of p))))
    (if (null? r1)
        (if (null? r0)
            (list '() '() '())
            (let ((c (cn-inv p (cn-lc r0))))
              (list (cn-scale p r0 c) (cn-scale p s0 c) (cn-scale p t0 c))))
        (let* ((qr (cn-divmod p r0 r1)) (q (car qr)))
          (loop r1 (cdr qr) s1 (cn-sub p s0 (cn-mul p q s1)) t1 (cn-sub p t0 (cn-mul p q t1)))))))

(define (cn-deriv p a)
  (if (null? a)
      '()
      (cn-trim (let loop ((cs (cdr a)) (i 1) (acc '()))
                 (if (null? cs) (reverse acc) (loop (cdr cs) (+ i 1) (cons (cn-nrm p (* i (car cs))) acc)))))))

(define (cn-eval p a x)
  (let loop ((cs (reverse a)) (acc 0))
    (if (null? cs) acc (loop (cdr cs) (cn-nrm p (+ (* acc x) (car cs)))))))

; ---------- кривая ----------

; (cantor-curve P x) — над ℚ; (cantor-curve P x p) — над 𝔽_p.  Ошибка: P не многочлен над ℚ, степень чётная или < 3,
; P не бесквадратен (над данным полем), p чётное/составное/делит старший коэффициент или знаменатель.
(define (cantor-curve P x &rest ps)
  (let ((p (if (null? ps) 0 (car ps))))
    (if (not (or (= p 0) (and (integer? p) (> p 2) (true? (prime? p)))))
        (error "cantor-curve: p должно быть нечётным простым (или опущено)" p))
    (let ((pl (try (ib-poly-parse P x) (lambda (e) #f))))
      (if (not (pair? pl))
          (error "cantor-curve: P — не многочлен от x с рациональными коэффициентами" P))
      (let* ((n (cn-deg pl)) (co (cn-trim (map (lambda (c) (cn-in p c)) pl))))
        (cond
          ((even? n) (error "cantor-curve: степень P чётная (две точки на ∞) — не поддерживается (R5.3c)" P))
          ((< n 3) (error "cantor-curve: степень P < 3, род 0" P))
          ((not (= (cn-deg co) n)) (error "cantor-curve: старший коэффициент делится на p" P p))
          ((not (= 0 (cn-deg (car (cn-egcd p co (cn-deriv p co))))))
           (error "cantor-curve: P не бесквадратен (кривая особая)" P))
          (else (list 'cantor-curve co p (quotient (- n 1) 2) P x)))))))

(define (cn-curve? C) (and (pair? C) (= 6 (length C)) (equal? (car C) 'cantor-curve)))
(define (cn-co C) (nth C 1))
(define (cn-p C) (nth C 2))
(define (cn-g C) (nth C 3))

(define (cn-need-curve C who)
  (if (cn-curve? C) C (error (string-append who ": ожидается кривая из cantor-curve") C)))

; та же кривая над 𝔽_p или #f (плохая редукция: p = 2, p | lc P, знаменатели, особая)
(define (cantor-curve-mod-p C p)
  (cn-need-curve C "cantor-curve-mod-p")
  (if (not (= (cn-p C) 0))
      (error "cantor-curve-mod-p: кривая уже над 𝔽_p"))
  (try (cantor-curve (nth C 4) (nth C 5) p) (lambda (e) #f)))

; ---------- представление ----------

(define cn-zero '((1) ()))

; нуль группы: u = 1 (монический степени 0), v = 0; для K и 𝔽_p/ℚ одинаково (u монический, значит u = (1) ⇔ степень 0)
(define (cn-zero-raw? D) (and (pair? (car D)) (null? (cdr (car D))) (null? (cadr D))))
(define (cn-zero-of p) (if (pair? p) (list (list ck-one) '()) cn-zero))

(define (cn-coef-ok? p c)
  (cond ((pair? p) (and (list? c) (= 2 (length c)) (cn-coef-ok? 0 (car c)) (cn-coef-ok? 0 (cadr c))))
        ((= p 0) (and (number? c) (or (integer? c) (equal? (type-of c) 'rational))))
        (else (and (integer? c) (>= c 0) (< c p)))))

(define (cn-poly-ok? p l)
  (and (list? l) (every? (lambda (c) (cn-coef-ok? p c)) l) (equal? l (cn-trim l))))

; (cantor-valid? C D) → #t, если D = (u v) — приведённое представление: u монический, deg u ≤ g, deg v < deg u, u | v² − P
(define (cantor-valid? C D)
  (cn-need-curve C "cantor-valid?")
  (let ((p (cn-p C)))
    (and (list? D) (= 2 (length D))
         (let ((u (car D)) (v (cadr D)))
           (and (cn-poly-ok? p u) (cn-poly-ok? p v)
                (pair? u) (cn-one? (cn-lc u))
                (<= (cn-deg u) (cn-g C))
                (< (cn-deg v) (cn-deg u))
                (null? (cn-mod p (cn-sub p (cn-mul p v v) (cn-co C)) u)))))))

(define (cn-need-valid C D who)
  (if (cantor-valid? C D) D (error (string-append who ": неверное представление Мамфорда (u монический, deg u ≤ g, deg v < deg u, u | v² − P)") D)))

; нуль группы (1, 0); любой недопустимый ввод — #f
(define (cantor-zero? D)
  (and (list? D) (= 2 (length D)) (equal? (car D) '(1)) (null? (cadr D))))

; приведение: u | v² − P, deg u любая → u′ = (P − v²)/u монический, v′ = −v mod u′, пока deg u > g
(define (cn-reduce-raw C u v)
  (let ((p (cn-p C)) (g (cn-g C)))
    (let loop ((u u) (v (cn-mod p v u)))
      (if (<= (cn-deg u) g)
          (list u v)
          (let ((u2 (cn-monic p (cn-quot-exact p (cn-sub p (cn-co C) (cn-mul p v v)) u))))
            (loop u2 (cn-mod p (cn-neg p v) u2)))))))

; (cantor-reduce C u v) — класс по произвольной паре: u ≠ 0 (нормируется), u | v² − P, иначе ошибка
(define (cantor-reduce C u v)
  (cn-need-curve C "cantor-reduce")
  (let ((p (cn-p C)))
    (if (not (and (list? u) (list? v) (pair? (cn-trim u))))
        (error "cantor-reduce: u и v — списки коэффициентов, u ≠ 0" u v))
    (let* ((u1 (cn-monic p (cn-trim (map (lambda (c) (cn-in p c)) u))))
           (v1 (cn-mod p (cn-trim (map (lambda (c) (cn-in p c)) v)) u1)))
      (if (not (null? (cn-mod p (cn-sub p (cn-mul p v1 v1) (cn-co C)) u1)))
          (error "cantor-reduce: u не делит v² − P" u v))
      (cn-reduce-raw C u1 v1))))

(define (cn-neg-raw C D) (list (car D) (cn-neg (cn-p C) (cadr D))))

; композиция Кантора (h = 0, f = P) и приведение
(define (cn-add-raw C D1 D2)
  (cond
    ((cn-zero-raw? D1) D2)
    ((cn-zero-raw? D2) D1)
    (else
     (let* ((p (cn-p C)) (u1 (car D1)) (v1 (cadr D1)) (u2 (car D2)) (v2 (cadr D2))
            (e1 (cn-egcd p u1 u2))
            (e2 (cn-egcd p (car e1) (cn-add p v1 v2)))
            (d (car e2))
            (s1 (cn-mul p (cadr e2) (cadr e1)))
            (s2 (cn-mul p (cadr e2) (caddr e1)))
            (s3 (caddr e2))
            (u (cn-quot-exact p (cn-mul p u1 u2) (cn-mul p d d)))
            (num (cn-add p (cn-add p (cn-mul p s1 (cn-mul p u1 v2)) (cn-mul p s2 (cn-mul p u2 v1)))
                         (cn-mul p s3 (cn-add p (cn-mul p v1 v2) (cn-co C)))))
            (v (cn-mod p (cn-quot-exact p num d) u)))
       (cn-reduce-raw C u v)))))

(define (cn-mul-raw C n D)
  (let loop ((n (abs n)) (base (if (< n 0) (cn-neg-raw C D) D)) (acc (cn-zero-of (cn-p C))))
    (cond ((= n 0) acc)
          ((= 1 (remainder n 2))
           (loop (quotient n 2) (if (> n 1) (cn-add-raw C base base) base) (cn-add-raw C acc base)))
          (else (loop (quotient n 2) (cn-add-raw C base base) acc)))))

(define (cantor-neg C D)
  (cn-need-curve C "cantor-neg")
  (cn-neg-raw C (cn-need-valid C D "cantor-neg")))

(define (cantor-add C D1 D2)
  (cn-need-curve C "cantor-add")
  (cn-add-raw C (cn-need-valid C D1 "cantor-add") (cn-need-valid C D2 "cantor-add")))

(define (cantor-double C D)
  (cn-need-curve C "cantor-double")
  (let ((D1 (cn-need-valid C D "cantor-double"))) (cn-add-raw C D1 D1)))

; (cantor-mul C n D) — n·D, n целое (отрицательное — через −D), двоичный метод
(define (cantor-mul C n D)
  (cn-need-curve C "cantor-mul")
  (if (not (integer? n)) (error "cantor-mul: n — целое" n))
  (cn-mul-raw C n (cn-need-valid C D "cantor-mul")))

; ---------- дивизор по рациональным точкам ----------

; место (a b), b — число, ram или элемент ℚ(√…) из dv-k->rat → (u v); (inf ram) → нуль; иначе ошибка
; ордината места над K = ℚ(√d): число | ram | элемент dv-k (ключи () и (d)) → пара (a b) или #f
(define (cn-k-pair b d)
  (cond ((equal? b 'ram) ck-zero)
        ((number? b) (list b 0))
        ((and (list? b) (dv-k-in-qd? b d)) (list (ib-k-coeff b '()) (ib-k-coeff b (list d))))
        (else #f)))

(define (cn-place->rep-k C pl)
  (let* ((p (cn-p C)) (d (car p)))
    (cond
      ((not (and (list? pl) (= 2 (length pl)))) (error "cantor-from-points: место — (a b)" pl))
      ((equal? (car pl) 'inf)
       (if (equal? (cadr pl) 'ram) (cn-zero-of p) (error "cantor-from-points: на ∞ только точка ветвления (inf ram)" pl)))
      ((not (cn-coef-ok? 0 (car pl))) (error "cantor-from-points: абсцисса — рациональное число" pl))
      (else
       (let ((b (cn-k-pair (cadr pl) d)))
         (if (not b) (error "cantor-from-points: ордината не лежит в K" pl))
         (let ((pa (cn-eval-k p (cn-co C) (list (car pl) 0))))
           (if (not (equal? (ck* p b b) pa))
               (error "cantor-from-points: точка не лежит на кривой" pl))
           (list (list (list (- (car pl)) 0) ck-one) (if (cn-ez? b) '() (list b)))))))))

; значение многочлена над K в точке x ∈ K
(define (cn-eval-k p a x)
  (let loop ((cs (reverse a)) (acc ck-zero))
    (if (null? cs) acc (loop (cdr cs) (ck+ (ck* p acc x) (car cs))))))

(define (cn-place->rep C pl)
  (let ((p (cn-p C)))
    (cond
      ((pair? p) (cn-place->rep-k C pl))
      ((not (and (list? pl) (= 2 (length pl)))) (error "cantor-from-points: место — (a b)" pl))
      ((equal? (car pl) 'inf)
       (if (equal? (cadr pl) 'ram) cn-zero (error "cantor-from-points: на ∞ только точка ветвления (inf ram)" pl)))
      ((not (cn-coef-ok? 0 (car pl))) (error "cantor-from-points: абсцисса — рациональное число" pl))
      (else
       (let* ((b (cond ((equal? (cadr pl) 'ram) 0)
                       ((number? (cadr pl)) (cadr pl))
                       (else (try (dv-k->rat (cadr pl)) (lambda (e) #f)))))
              (a1 (if (cn-coef-ok? 0 (car pl)) (cn-in p (car pl)) 0)))
         (if (not (and b (cn-coef-ok? 0 b)))
             (error "cantor-from-points: ордината не рациональна" pl))
         (let ((b1 (cn-in p b)))
           (if (not (= (cn-nrm p (* b1 b1)) (cn-eval p (cn-co C) a1)))
               (error "cantor-from-points: точка не лежит на кривой" pl))
           (list (list (cn-nrm p (- a1)) 1) (if (= b1 0) '() (list b1)))))))))

; (cantor-from-points C D) — D = ((место . n) …), место (a b) с b = y-значение (число | ram | элемент dv-k->rat) либо (inf ram):
; класс Σ nᵢ·Pᵢ − (Σ nᵢ)·O.  При deg D = 0 это класс D в J.
(define (cantor-from-points C D)
  (cn-need-curve C "cantor-from-points")
  (if (not (and (list? D) (every? (lambda (pr) (and (pair? pr) (integer? (cdr pr)))) D)))
      (error "cantor-from-points: D = ((место . n) …), n целое" D))
  (foldl (lambda (acc pr) (cn-add-raw C acc (cn-mul-raw C (cdr pr) (cn-place->rep C (car pr)))))
         (cn-zero-of (cn-p C)) D))

; ---------- редукция по модулю p, порядок ----------

; (cantor-mod-p D p) — (u mod p, v mod p) или #f, если знаменатель делится на p
(define (cantor-mod-p D p)
  (if (not (and (list? D) (= 2 (length D)) (list? (car D)) (list? (cadr D))))
      (error "cantor-mod-p: D = (u v)" D))
  (try (list (cn-trim (map (lambda (c) (cn-in p c)) (car D)))
             (cn-trim (map (lambda (c) (cn-in p c)) (cadr D))))
       (lambda (e) #f)))

; наименьшее n ≤ N с n·D = 0 или #f
(define (cantor-order-upto C D N)
  (cn-need-curve C "cantor-order-upto")
  (cn-need-valid C D "cantor-order-upto")
  (let loop ((n 1) (cur D))
    (cond ((cn-zero-raw? cur) n)
          ((>= n N) #f)
          (else (loop (+ n 1) (cn-add-raw C cur D))))))

; (cantor-order-mod-p C D p) — порядок образа D в J(𝔽_p): #J(𝔽_p) (hyp-jacobian-pick) и перебор делителей по простым;
; #f — p плохое (или знаменатель D кратен p); unknown — #J не вычислен; несовместимость n·D ≠ 0 при n = #J — ошибка
(define (cantor-order-mod-p C D p)
  (cn-need-curve C "cantor-order-mod-p")
  (let ((Cp (and (integer? p) (> p 2) (true? (prime? p)) (cantor-curve-mod-p C p)))
        (Dp (cantor-mod-p D p)))
    (if (not (and Cp Dp))
        #f
        (begin
          (cn-need-valid Cp Dp "cantor-order-mod-p")
          (let ((N (hyp-jacobian-pick (nth C 4) (nth C 5) p)))
            (if (not (and (integer? N) (> N 0)))
                'unknown
                (begin
                  (if (not (cn-zero-raw? (cn-mul-raw Cp N Dp)))
                      (error "cantor-order-mod-p: N·D ≠ 0 при N = #J(F_p) — подсчёт точек несовместим" N p))
                  (cn-ord-from-multiple Cp Dp N))))))))

; порядок D в группе, если N·D = 0: спуск по простым множителям N
(define (cn-ord-from-multiple Cp Dp N)
  (foldl (lambda (o pe)
           (let loop ((o o) (k 0))
             (if (and (< k (cdr pe)) (= 0 (remainder o (car pe)))
                      (cn-zero-raw? (cn-mul-raw Cp (quotient o (car pe)) Dp)))
                 (loop (quotient o (car pe)) (+ k 1))
                 o)))
         N (ib-factor-int N)))

; ---------- R5.3b: «кручение / не кручение» для дивизора вычетов δ (кривая y² = P, нечётная степень, род ≥ 2) ----------
;
; Обоснование.  Для нечётного хорошего p (p ∤ lc·disc P, знаменатели координат точек δ не делятся на p) редукция
; J(ℚ) → J(𝔽_p) — гомоморфизм, инъективный на кручении (p > 2, индекс ветвления 1 < p − 1).  Поэтому:
;  1) если δ — кручение порядка n, то n = ord_p(δ) =: m (n·δ = 0 ⇒ ord_p | n; обратное — инъективность);
;  2) тогда m·δ = 0 над ℚ, а значит и m·δ ≡ 0 по модулю любого другого хорошего q.  Если m·D ≠ 0 по модулю
;     какого-то q — δ не кручение (иначе m·δ = 0 над ℚ и по модулю q);
;  3) если везде 0, точная проверка m·D над ℚ (cantor-mul): ≠ 0 ⇒ не кручение (как в п. 2), = 0 ⇒ порядок δ в J(ℚ)
;     делит m, а ord_p = m ⇒ порядок ровно m (меньший k | m с k·δ = 0 дал бы k·D ≡ 0 по модулю p).
; Ответ с функцией u всё равно проходит прежний сертификат (hyp-log-check / int-check) — проверка Кантора его не заменяет.

(define cn-exact-limit 60)     ; точная проверка m·D над ℚ — только при m ≤ 60 и m·g ≤ 150 (высота растёт ∼ m²)
(define cn-exact-work 150)
(define cn-check-primes 3)     ; сколько простых q ≠ p проверяется

(define (cn-genus-odd P x)
  (let ((n (try (degree P x) (lambda (e) 0))))
    (if (and (integer? n) (> n 2) (odd? n)) (quotient (- n 1) 2) 0)))

; (p . m): наименьшее хорошее p ≥ 3 (подсчёт #J(𝔽_p) укладывается в бюджет dv-cap) и m = ord_p(D); #f — такого p нет
(define (cn-first-order P x C D g)
  (let loop ((p 3))
    (cond ((or (> p 50) (> (^ p g) (dv-cap))) #f)
          ((not (equal? (hyp-good-prime? P x p) #t)) (loop (next-prime p)))
          (else
           (let ((m (try (cantor-order-mod-p C D p) (lambda (e) #f))))
             (if (and (integer? m) (> m 0))
                 (cons p m)
                 (loop (next-prime p))))))))

; до cnt хороших q > p0 с определёнными редукциями кривой и D: ((q Cq Dq) …); #J не нужен
(define (cn-reductions P x C D p0 cnt)
  (let loop ((q (next-prime p0)) (acc '()))
    (cond ((or (>= (length acc) cnt) (> q 200)) (reverse acc))
          ((not (equal? (hyp-good-prime? P x q) #t)) (loop (next-prime q) acc))
          (else
           (let ((Cq (cantor-curve-mod-p C q)) (Dq (cantor-mod-p D q)))
             (if (and Cq Dq)
                 (loop (next-prime q) (cons (list q Cq Dq) acc))
                 (loop (next-prime q) acc)))))))

; ---------- R5.3c1: чётная степень 2g + 2 с рациональным корнем a ----------
;
; Замена x = a + 1/z, w = y·z^{g+1}: P(a + 1/z) = Q(z)/z^{2g+2}, Q(z) = z^{2g+2}·P(a + 1/z).  Так как P(a) = 0, свободный член
; P(a + t) равен 0 и deg Q = 2g + 1 (старший коэффициент Q — P′(a) ≠ 0): w² = Q(z) — кривая нечётной степени того же рода,
; бирационально изоморфная y² = P (Q бесквадратен вместе с P).  Бирациональный изоморфизм гладких проективных моделей
; индуцирует изоморфизм якобианов над ℚ, переводящий класс δ в класс образа δ; поэтому главность n·δ и порядок кручения
; δ у обеих кривых одни и те же.  Перенос мест: (x₀, y₀), x₀ ≠ a ↦ (z₀, w₀) = (1/(x₀ − a), y₀·z₀^{g+1});
; (a, 0) ↦ ∞ (точка ветвления новой модели); ∞± (y/x^{g+1} → ±√lc) ↦ (0, ±√lc): при z → 0 имеем x^{g+1}z^{g+1} → 1.
; Места не над ℚ (ордината не рациональна) — #f (старый путь).

; рациональные простые корни P (простые линейные множители): список чисел
(define (cn-rat-roots P x)
  (let ((fs (try (factor-list P) (lambda (e) #f))))
    (if (not (pair? fs))
        '()
        (filter (lambda (a) (not (equal? a #f)))
                (map (lambda (pe)
                       (let ((c (and (list? pe) (= 2 (length pe)) (equal? (cadr pe) 1) (ib-poly-parse (car pe) x))))
                         (if (and (list? c) (= 2 (length c)) (not (= 0 (cadr c)))) (/ (- (car c)) (cadr c)) #f)))
                     (cdr fs))))))

; корень попроще: целый с наименьшим |a|, иначе первый
(define (cn-best-root roots)
  (let ((key (lambda (a) (if (integer? a) (abs a) (+ 1000 (abs a))))))
    (foldl (lambda (best a) (if (< (key a) (key best)) a best)) (car roots) (cdr roots))))

; место (x₀ b) исходной модели → место модели w² = Q(z) или #f; h = g + 1.
; d = #f: ордината рациональна; d — целое: ордината в K = ℚ(√d) (элемент dv-k остаётся элементом, w = b·z^h)
(define (cn-even-place pl a h &rest ds)
  (let* ((d (if (null? ds) #f (car ds))) (x0 (car pl)) (b0 (cadr pl))
         (b (cond ((equal? b0 'ram) 'ram)
                  ((number? b0) b0)
                  (d (if (and (list? b0) (dv-k-in-qd? b0 d)) b0 #f))
                  (else (try (dv-k->rat b0) (lambda (e) #f)))))
         (sc (lambda (b z) (if (number? b) (* b (^ z h)) (ib-k-scale b (^ z h))))))
    (cond ((equal? b #f) #f)
          ((not (or (equal? b 'ram) (number? b) (list? b))) #f)
          ((equal? x0 'inf) (if (equal? b 'ram) #f (list 0 b)))
          ((not (cn-coef-ok? 0 x0)) #f)
          ((= x0 a) (if (equal? b 'ram) (list 'inf 'ram) #f))
          (else (let ((z (/ 1 (- x0 a))))
                  (list z (if (equal? b 'ram) 'ram (sc b z))))))))

; (cn-model P x D) → (P′ x′ D′ info): нечётная степень — как есть (info = #f); чётная ≥ 6 с рациональным корнем —
; (Q 'z D′ (a Q)); #f — не применимо.  (cn-model P x D d) — места над K = ℚ(√d) (R5.3c2)
(define (cn-model P x D &rest ds)
  (let ((n (try (degree P x) (lambda (e) 0))))
    (cond ((not (integer? n)) #f)
          ((odd? n) (list P x D #f))
          ((< n 6) #f)
          (else
           (let* ((pl (ib-poly-parse P x))
                  (roots (if (list? pl) (cn-rat-roots P x) '())))
             (if (null? roots)
                 #f
                 (let* ((a (cn-best-root roots)) (h (quotient n 2))
                        (Q (ib-poly->expr (ib-p-trim (reverse (dv-p-shift pl a))) 'z))
                        (D2 (map (lambda (pr) (let ((q (apply cn-even-place (cons (car pr) (cons a (cons h ds)))))) (and q (cons q (cdr pr))))) D)))
                   (if (every? (lambda (e) (not (equal? e #f))) D2)
                       (list Q 'z D2 (list a Q))
                       #f))))))))

; (cantor-torsion-check P x D) — D = ((место . n) …) степени 0 с местами над ℚ; кривая y² = P, deg P нечётная ≥ 5
; либо чётная ≥ 6 с рациональным корнем (R5.3c1: проверка в модели w² = Q(z), результат дополняется шестым элементом (a Q)).
; Результат: #f — не применимо или не решено (старый путь);
;   (torsion p m qs exact)    — ord_p(δ) = m, m·δ ≡ 0 по всем q ∈ qs; exact = #t: m·δ = 0 над ℚ проверено (порядок δ ровно m),
;                               #f: точная проверка опущена (m велико) — кручение не доказано;
;   (non-torsion p m qs q)    — δ не кручение: q — простое с m·δ ≢ 0 по модулю q, либо q = 0: m·δ ≠ 0 над ℚ.
(define (cantor-torsion-check P x D &rest ds)
  (let ((M (apply cn-model (cons P (cons x (cons D ds))))))
    (if (not M)
        #f
        (if (pair? ds)
            (let ((r (cn-torsion-core-k (nth M 0) (nth M 1) (nth M 2) (car ds)
                                        (and (pair? (cdr ds)) (integer? (cadr ds)) (> (cadr ds) 0) (cadr ds)))))
              (if r (append (take r 5) (list (nth M 3)) (list (nth r 5))) r))
            (let ((r (cn-torsion-core (nth M 0) (nth M 1) (nth M 2))))
              (if (and r (nth M 3)) (append r (list (nth M 3))) r))))))

; ---------- R5.3c2: места над K = ℚ(√d) ----------
;
; Обоснование.  Пусть p — хорошее нечётное простое, p ∤ d, jacobi(d, p) = 1 (p расщепляется в K).  Тогда есть простой 𝔭 | p
; степени 1: 𝔭 = (p, √d − s), s² ≡ d (mod p), поле вычетов 𝔽_p; √d ↦ s (один и тот же корень s для всех точек δ и для
; всего Кантора по этому p — редукция — кольцевой гомоморфизм 𝒪_K,(𝔭) → 𝔽_p).  Кривая и якобиан имеют хорошую редукцию по 𝔭
; (p ∤ lc·disc P, знаменатели координат точек не делятся на p), p неразветвлено (e = 1 < p − 1 при p > 2), поэтому редукция
; J(K) → J(𝔽_p) инъективна на кручении.  Следовательно:
;  1) δ — кручение порядка n ⇒ n = ord_𝔭(δ) =: m (ord_𝔭 делит n, обратное — инъективность);
;  2) m·δ ≢ 0 по модулю какого-либо другого простого 𝔮 (хорошее расщеплённое q со своим корнем s_q) ⇒ δ не кручение (иначе
;     m·δ = 0 над K и по любому 𝔮); то же, если ord_𝔮(δ) > N ≥ m (тогда m·δ ≢ 0 по 𝔮);
;  3) m·δ = 0 над K проверяется точно (Кантор над K, коэффициенты — пары рациональных); ≠ 0 ⇒ не кручение, = 0 ⇒ порядок δ
;     в J(K) делит m, а ord_𝔭 = m ⇒ порядок ровно m.
; Порядок ord_𝔭(δ) ищется перебором кратных k·δ, k ≤ N (#J(𝔽_p) не нужен — для p^g ≫ 10⁶ его подсчёт недоступен); если
; ни у одного из первых cn-k-primes простых порядок не ≤ N — #f (старый путь).  Инертные p (нужно 𝔽_{p²}) пропускаются.
; Ответ с функцией u проходит тот же сертификат (hyp-log-check), проверка Кантора его не заменяет.

(define cn-k-search 60)       ; N: перебор k·δ ≤ N
(define cn-k-primes 5)        ; сколько расщеплённых p просматривается при поиске порядка
(define cn-k-exact-work 60)   ; точная проверка над K: m·g ≤ 60

(define (cn-curve-k P x d)
  (let ((pl (try (ib-poly-parse P x) (lambda (e) #f))))
    (if (not (and (pair? pl) (every? (lambda (c) (cn-coef-ok? 0 c)) pl)
                  (> (cn-deg pl) 2) (odd? (cn-deg pl))))
        #f
        (list 'cantor-curve (map (lambda (c) (list c 0)) pl) (list d) (quotient (- (cn-deg pl) 1) 2) P x))))

; место над K → место с целыми координатами по 𝔭 = (p, √d − s); #f — знаменатель кратен p / ордината вне K
(define (cn-k-red-place pl p s d)
  (if (equal? (car pl) 'inf)
      pl
      (let ((b (try (cn-k-pair (cadr pl) d) (lambda (e) #f))))
        (and b (cn-coef-ok? 0 (car pl))
             (try (list (cn-in p (car pl))
                        (modulo (+ (cn-in p (car b)) (* (cn-in p (cadr b)) s)) p))
                  (lambda (e) #f))))))

; (Cp . Dp) — кривая и дивизор по модулю 𝔭 или #f
(define (cn-k-reduce C D p d s)
  (let ((Cp (cantor-curve-mod-p C p)))
    (and Cp
         (let ((Dr (map (lambda (pr) (let ((q (cn-k-red-place (car pr) p s d))) (and q (cons q (cdr pr))))) D)))
           (and (every? (lambda (e) (not (equal? e #f))) Dr)
                (let ((Dp (try (cantor-from-points Cp Dr) (lambda (e) #f))))
                  (and Dp (cons Cp Dp))))))))

(define (cn-k-split-prime? P x d p)
  (and (not (= 0 (modulo d p))) (= 1 (jacobi d p)) (equal? (hyp-good-prime? P x p) #t)))

; (p m s bads): наименьшее расщеплённое хорошее p с ord_𝔭(δ) = m; bads — ((p′ s′) …) просмотренные раньше с ord > N.
; Если известна граница B (порядок кручения J(K) делит B: НОД чисел #J(𝔽_p) / #J(𝔽_{p²}) по хорошим p, hyp-torsion-bound-ev),
; то ord_𝔭(δ) ищется спуском от B (B·δ ≢ 0 по модулю 𝔭 ⇒ δ не кручение — (bound p s)); иначе перебор k·δ, k ≤ N.
(define (cn-k-first-order P x C D d B)
  (let loop ((p 3) (tried 0) (bads '()))
    (cond ((or (> p 200) (>= tried cn-k-primes)) (if (null? bads) #f (list 'none-small (reverse bads))))
          ((not (cn-k-split-prime? P x d p)) (loop (next-prime p) tried bads))
          (else
           (let* ((s (sqrtmod (modulo d p) p)) (red (cn-k-reduce C D p d s)))
             (cond
               ((not red) (loop (next-prime p) tried bads))
               (B (let ((BD (try (cn-mul-raw (car red) B (cdr red)) (lambda (e) #f))))
                    (cond ((not BD) (loop (next-prime p) tried bads))
                          ((not (cn-zero-raw? BD)) (list 'bound p s))
                          (else (list p (cn-ord-from-multiple (car red) (cdr red) B) s '())))))
               (else
                (let ((m (try (cantor-order-upto (car red) (cdr red) cn-k-search) (lambda (e) #f))))
                  (if m
                      (list p m s (reverse bads))
                      (loop (next-prime p) (+ tried 1) (cons (list p s) bads)))))))))))

; до cnt расщеплённых хороших q > p0: ((q Cq Dq sq) …)
(define (cn-k-reductions P x C D d p0 cnt)
  (let loop ((q (next-prime p0)) (acc '()))
    (cond ((or (>= (length acc) cnt) (> q 300)) (reverse acc))
          ((not (cn-k-split-prime? P x d q)) (loop (next-prime q) acc))
          (else
           (let* ((sq (sqrtmod (modulo d q) q)) (red (cn-k-reduce C D q d sq)))
             (if red
                 (loop (next-prime q) (cons (list q (car red) (cdr red) sq) acc))
                 (loop (next-prime q) acc)))))))

; (kind p m qs q/exact #f/(a Q) (d ((p . s) …))) — как cantor-torsion-check; P нечётной степени ≥ 5 (после cn-model)
(define (cn-torsion-core-k P x D d B)
  (let ((g (cn-genus-odd P x)) (C (try (cantor-curve P x) (lambda (e) #f))))
    (if (or (< g 2) (not C))
        #f
        (let ((po (cn-k-first-order P x C D d B)))
          (if (not po)
              #f
              (if (equal? (car po) 'none-small)
                  ; ни у одного из просмотренных p порядок не ≤ N: кручения порядка ≤ N нет, порядок не определён
                  (list 'order-large (car (car (nth po 1))) cn-k-search (map car (nth po 1)) #f
                        (list d (map (lambda (b) (cons (car b) (cadr b))) (nth po 1)) cn-k-search))
              (if (equal? (car po) 'bound)
                  (list 'non-torsion (nth po 1) B '() 'bound (list d (list (cons (nth po 1) (nth po 2))) cn-k-search))
              (let* ((p (nth po 0)) (m (nth po 1)) (s (nth po 2)) (bads (nth po 3))
                     (rs (cn-k-reductions P x C D d p cn-check-primes))
                     (qs (map car rs))
                     (sqs (append (list (cons p s)) (map (lambda (b) (cons (car b) (cadr b))) bads)
                                  (map (lambda (r) (cons (car r) (nth r 3))) rs)))
                     (bad (let loop ((r rs))
                            (cond ((null? r) #f)
                                  ((cn-zero-raw? (cn-mul-raw (nth (car r) 1) m (nth (car r) 2))) (loop (cdr r)))
                                  (else (car (car r)))))))
                (cond
                  ((pair? bads) (list 'non-torsion p m qs (car (car bads)) (list d sqs cn-k-search)))
                  (bad (list 'non-torsion p m qs bad (list d sqs cn-k-search)))
                  ((<= (* m g) cn-k-exact-work)
                   (let* ((CK (cn-curve-k P x d))
                          (Dc (and CK (try (cantor-from-points CK D) (lambda (e) #f)))))
                     (cond ((not Dc) (list 'torsion p m qs #f (list d sqs cn-k-search)))
                           ((cn-zero-raw? (cn-mul-raw CK m Dc)) (list 'torsion p m qs #t (list d sqs cn-k-search)))
                           (else (list 'non-torsion p m qs 0 (list d sqs cn-k-search))))))
                  (else (list 'torsion p m qs #f (list d sqs cn-k-search))))))))))))

(define (cn-torsion-core P x D)
  (let ((g (cn-genus-odd P x)))
    (if (< g 2)
        #f
        (let* ((C (try (cantor-curve P x) (lambda (e) #f)))
               (Dc (and C (try (cantor-from-points C D) (lambda (e) #f)))))
          (if (not Dc)
              #f
              (let ((po (cn-first-order P x C Dc g)))
                (if (not po)
                    #f
                    (let* ((p (car po)) (m (cdr po))
                           (rs (cn-reductions P x C Dc p cn-check-primes))
                           (bad (let loop ((r rs))
                                  (cond ((null? r) #f)
                                        ((cn-zero-raw? (cn-mul-raw (nth (car r) 1) m (nth (car r) 2))) (loop (cdr r)))
                                        (else (car r)))))
                           (qs (map car rs)))
                      (cond
                        (bad (list 'non-torsion p m qs (car bad)))
                        ((and (<= m cn-exact-limit) (<= (* m g) cn-exact-work))
                         (if (cn-zero-raw? (cn-mul-raw C m Dc))
                             (list 'torsion p m qs #t)
                             (list 'non-torsion p m qs 0)))
                        (else (list 'torsion p m qs #f)))))))))))

; (cantor-multiples P x D k) → ((1 (u v)) … (k (u v))): j·D над ℚ, нуль — ((1) ()); #f при ошибке (только для таблицы шага)
; (cantor-multiples P x D k d) — места над K = ℚ(√d): коэффициенты пар Мамфорда — пары (a b) = a + b√d
(define (cantor-multiples P0 x0 D0 k &rest ds)
  (let* ((M (apply cn-model (cons P0 (cons x0 (cons D0 ds))))) (P (and M (nth M 0))) (x (and M (nth M 1))) (D (and M (nth M 2)))
         (C (and M (if (pair? ds) (cn-curve-k P x (car ds)) (try (cantor-curve P x) (lambda (e) #f)))))
         (Dc (and C (try (cantor-from-points C D) (lambda (e) #f)))))
    (and Dc
         (try (let loop ((j 1) (cur Dc) (acc '()))
                (if (> j k)
                    (reverse acc)
                    (loop (+ j 1) (cn-add-raw C cur Dc) (cons (list j cur) acc))))
              (lambda (e) #f)))))
