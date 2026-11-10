; denest.lisp — денестинг радикалов глубины 2 и нормальная форма ℚ(α) (шаг A1.5).
;
; (sqrt-denest e) — √(a + b√r) по критерию BFHT 1985: c = √(a² − b²r) ∈ ℚ ⇒
;   √(a + b√r) = √((a+c)/2) + sign(b)·√((a−c)/2); рекурсия по подвыражениям.
;   Сертификат: квадрат ответа равен подкоренному (точно, в ℚ(α)) и ответ неотрицателен (численно).
; (alg-simplify e) — выражение с квадратными радикалами → элемент ℚ(α) (поле через alg-primitive)
;   → обратно alg->expr; сокращает (√2+√3)² − 2√6 → 5, 1/(1+√2) → √2−1, √2·√8 → 4.
; (alg-equal? e1 e2) — точное равенство выражений с радикалами (диспетчер: 2 арг — выражения,
;   3 арг — прежняя функция поля alg-equal? из algnum).

(module denest
  (export sqrt-denest denest-check? alg-simplify alg-equal-expr? radical-roots))

; прежняя функция поля (3 аргумента) из algnum — захватываем до подмены глобального имени в prelude
(define dn-field-equal alg-equal?)

; ---------- точные помощники ----------

(define (dn-rat? x) (and (number? x) (or (integer? x) (equal? (type-of x) 'rational))))

; floor(sqrt(n)) для целого n >= 0 (Ньютон)
(define (dn-isqrt-step n x)
  (let ((y (floor (/ (+ x (floor (/ n x))) 2))))
    (if (< y x) (dn-isqrt-step n y) x)))
(define (dn-isqrt n) (if (< n 2) n (dn-isqrt-step n n)))

; (dn-square-split n) → (q . s): n = q²·s, s без квадратных множителей (n > 0 целое)
(define (dn-square-split-loop n q i)
  (if (> (* i i) n)
      (cons q n)
      (if (= (modulo n (* i i)) 0)
          (dn-square-split-loop (quotient n (* i i)) (* q i) i)
          (dn-square-split-loop n q (+ i 1)))))
(define (dn-square-split n) (dn-square-split-loop n 1 2))

; (dn-exact-sqrt q) → точный неотрицательный корень рационального q или #f
(define (dn-exact-sqrt q)
  (if (or (not (dn-rat? q)) (< q 0))
      #f
      (let* ((n (numer q)) (d (denom q))
             (sn (dn-isqrt n)) (sd (dn-isqrt d)))
        (if (and (= (* sn sn) n) (= (* sd sd) d))
            (/ sn sd)
            #f))))

; (dn-radical-expr q) — q >= 0 рациональное → √q с выносом квадратного множителя
; (√(3/2) → (* 1/2 (^ 6 1/2)), √4 → 2)
(define (dn-radical-expr q)
  (let* ((n (numer q)) (d (denom q))
         (m (* n d)))
    (if (or (< q 0) (= q 0))
        (if (= q 0) 0 #f)
        (let* ((sp (dn-square-split m))
               (coef (/ (car sp) d))
               (s (cdr sp)))
          (if (= s 1)
              coef
              (simplify (list '* coef (list '^ s 1/2))))))))

; ---------- разбор a + b√r ----------

; терм → (коэффициент . радиканд) или #f; радиканд 1 — рациональный терм
(define (dn-term-rad t)
  (cond ((dn-rat? t) (cons t 1))
        ((and (list? t) (equal? (car t) '^) (equal? (nth t 2) 1/2) (dn-rat? (nth t 1)))
         (let* ((sp (dn-square-split (* (numer (nth t 1)) (denom (nth t 1)))))
                (coef (/ (car sp) (denom (nth t 1))))
                (s (cdr sp)))
           (cons coef s)))
        ((and (list? t) (equal? (car t) '*))
         (dn-term-product (cdr t) 1 1 #f))
        (else #f)))

; произведение: собираем рациональные множители и ровно один радикал
(define (dn-term-product fs coef rad cand)
  (if (null? fs)
      (if cand (cons coef rad) #f)
      (let ((p (dn-term-rad (car fs))))
        (cond ((not p) #f)
              ((= (cdr p) 1)
               (dn-term-product (cdr fs) (* coef (car p)) rad cand))
              (cand #f)
              (else (dn-term-product (cdr fs) coef (cdr p) #t))))))

; (dn-linear-radical X) → (a b r) для X = a + b·√r (a, b рациональные, r без квадратов) или #f
(define (dn-linear-radical X)
  (let* ((e (expand X))
         (terms (if (and (list? e) (equal? (car e) '+)) (cdr e) (list e))))
    (dn-collect-terms terms 0 0 1 #t)))

(define (dn-collect-terms terms a b r ok)
  (if (or (not ok) (null? terms))
      (if ok (list a b r) #f)
      (let ((p (dn-term-rad (car terms))))
        (cond ((not p) #f)
              ((= (cdr p) 1) (dn-collect-terms (cdr terms) (+ a (car p)) b r #t))
              ((and (> r 1) (not (= r (cdr p)))) #f)   ; два разных радикала — глубина > 2
              (else (dn-collect-terms (cdr terms) a (+ b (car p)) (cdr p) #t))))))

; ---------- денестинг ----------

; (denest-check? X res) — res² = X точно и res >= 0 (знак по численному вложению)
(define (denest-check? X res)
  (and (alg-equal-expr? (expand (list '^ res 2)) X)
       (let ((v (try (eval-num res) (lambda (e) #f))))
         (and (number? v) (>= v 0)))))

; (dn-denest-radicand X) — денестинг √X (X = a + b√r) или #f
(define (dn-note-denest X a b r c u v res)
  (if (step-log-enabled?)
      (record-step 'dn-formula "Денестинг квадратного радикала"
                   (string-append "√(a + b√r): a = " (to-string a) ", b = " (to-string b)
                                  ", r = " (to-string r) "; a² − b²r = c², c = " (to-string c)
                                  "; x = " (to-string u) ", y = " (to-string v)
                                  "; √X = " (to-string res) " — проверено возведением в квадрат")
                   X res 'main))
  #t)

(define (dn-note-refuse X why)
  (if (step-log-enabled?)
      (record-step 'dn-refuse "Денестинг невозможен" why X 'refused 'main))
  #t)

(define (dn-denest-radicand X)
  (let ((lr (dn-linear-radical X)))
    (if (not lr)
        #f
        (let ((a (car lr)) (b (cadr lr)) (r (caddr lr)))
          (if (= r 1)
              #f
              (let* ((c2 (- (* a a) (* b b r)))
                     (c (dn-exact-sqrt c2)))
                (if (not c)
                    (begin (dn-note-refuse X (string-append "a² − b²r = " (to-string c2)
                                                            " — не квадрат ⇒ √x ± √y невозможен"))
                           #f)
                    (let* ((u (dn-radical-expr (/ (+ a c) 2)))
                           (v (dn-radical-expr (/ (- a c) 2))))
                      (if (or (not u) (not v))
                          (begin (dn-note-refuse X "x или y не выражается квадратным радикалом") #f)
                          (let ((res (if (>= b 0)
                                         (simplify (list '+ u v))
                                         (simplify (list '- u v)))))
                            (if (denest-check? X res)
                                (begin (dn-note-denest X a b r c u v res) res)
                                (begin (dn-note-refuse X "проверка возведением в квадрат не прошла") #f))))))))))))

; (sqrt-denest e) — денестинг всех √ глубины 2; не удалось — как было
(define (sqrt-denest e)
  (cond ((not (list? e)) e)
        ((and (equal? (car e) '^) (= (length e) 3) (equal? (nth e 2) 1/2))
         (let ((inner (sqrt-denest (nth e 1))))
           (let ((d (try (dn-denest-radicand inner) (lambda (err) #f))))
             (if d d (list '^ inner 1/2)))))
        ((and (equal? (car e) 'sqrt) (= (length e) 2))
         (let ((inner (sqrt-denest (nth e 1))))
           (let ((d (try (dn-denest-radicand inner) (lambda (err) #f))))
             (if d d (list 'sqrt inner)))))
        (else (cons (car e) (map sqrt-denest (cdr e))))))

; ---------- поле ℚ(α) по квадратным радикалам ----------

; список различных squarefree радикандов > 1 в выражении
(define (dn-add-rad s acc)
  (if (member? s acc) acc (append acc (list s))))

; радиканды точного r (√r): squarefree-часть |r| и, при r < 0, ещё −1 (мнимая единица)
(define (dn-rad-rat r)
  (if (= r 0)
      '()
      (let* ((a (if (< r 0) (- r) r))
             (sp (dn-square-split (* (numer a) (denom a))))
             (s (cdr sp)))
        (cond ((< r 0) (if (= s 1) (list -1) (list s -1)))
              ((= s 1) '())
              (else (list s))))))

(define (dn-radicals e)
  (cond ((not (list? e)) (if (equal? e '%i) (list -1) '()))
        ((equal? e '%i) (list -1))
        ((and (equal? (car e) '^) (= (length e) 3) (equal? (nth e 2) 1/2) (dn-rat? (nth e 1)))
         (dn-rad-rat (nth e 1)))
        ((and (equal? (car e) 'sqrt) (= (length e) 2) (dn-rat? (nth e 1)))
         (dn-rad-rat (nth e 1)))
        (else (foldl (lambda (acc u) (dn-union (dn-radicals u) acc)) '() (cdr e)))))

(define (dn-union a b)
  (foldl (lambda (acc x) (dn-add-rad x acc)) b a))

; ---------- независимые радикалы (WASM.6a Д6) ----------
; radsimp(1 + √2 + √3 + √6) даёт root-of, потому что √6 = √2·√3: радикандов три, а поле — степени 4.
; Зависимые радиканды заменяем выражением через независимые, тогда базис произведений совпадает с полем.

; все произведения подмножеств: список (произведение . подмножество)
(define (dn-subset-products xs)
  (if (null? xs)
      (list (cons 1 '()))
      (let ((rest (dn-subset-products (cdr xs))))
        (append rest (map (lambda (p) (cons (* (car xs) (car p)) (cons (car xs) (cdr p)))) rest)))))

; (dn-dependent? s xs) — s·P полный квадрат для непустого подмножества xs: (P . подмножество) или #f
(define (dn-dependent? s xs)
  (let loop ((ps (dn-subset-products xs)))
    (cond ((null? ps) #f)
          ((and (pair? (cdr (car ps)))
                (= (cdr (dn-square-split (* s (car (car ps))))) 1))
           (cons (car (car ps)) (cdr (car ps))))
          (else (loop (cdr ps))))))

; независимый набор (жадно по возрастанию): радиканд, выразимый через набранные, — зависим
(define (dn-independent rads kept dropped)
  (cond ((null? rads) (list (reverse kept) (reverse dropped)))
        ((dn-dependent? (car rads) kept)
         (dn-independent (cdr rads) kept (cons (car rads) dropped)))
        (else (dn-independent (cdr rads) (cons (car rads) kept) dropped))))

; √s через независимые: s·P = c² ⇒ √s = c·√P/P
(define (dn-rad-rewrite s kept)
  (let ((dep (dn-dependent? s kept)))
    (if (not dep)
        #f
        (let* ((p (car dep)) (ts (cdr dep))
               (c (car (dn-square-split (* s p))))
               (roots (cons '* (map (lambda (t) (list '^ t 1/2)) ts))))
          (simplify (list '* (/ c p) roots))))))

; заменить √s (^ s 1/2) и (sqrt s) на выражение r
(define (dn-rad-subst e s r)
  (cond ((and (list? e) (equal? (car e) '^) (= (length e) 3)
              (equal? (nth e 1) s) (equal? (nth e 2) 1/2)) r)
        ((and (list? e) (equal? (car e) 'sqrt) (= (length e) 2) (equal? (nth e 1) s)) r)
        ((list? e) (cons (car e) (map (lambda (z) (dn-rad-subst z s r)) (cdr e))))
        (else e)))

(define (dn-normalize-rads e)
  (let* ((rads (sort (dn-radicals e) <))
         (ind (dn-independent rads '() '()))
         (kept (car ind)))
    (foldl (lambda (acc s)
             (let ((r (dn-rad-rewrite s kept)))
               (if r (dn-rad-subst acc s r) acc)))
           e (cadr ind))))

; (dn-lift Fg elt alpha) — многочлен elt от старой образующей вычислить в alpha
(define (dn-lift Fg elt alpha)
  (let loop ((cs elt) (p '(1)) (acc '()))
    (if (null? cs)
        acc
        (loop (cdr cs) (alg-mul Fg p alpha)
              (alg-add Fg acc (alg-mul Fg (list (car cs)) p))))))

; minpoly поля привести к переменной t (alg-primitive ждёт t)
(define (dn-minpoly-t F)
  (let ((m (alg-field-minpoly F)))
    (if (contains-sym? m 't) m (subst (list 'x 't) m))))

; (dn-build F pairs rest) → (F pairs): добавить радиканды rest
(define (dn-build F pairs rest)
  (if (null? rest)
      (list F pairs)
      (let* ((s (car rest))
             (m2 (list '- (list '^ 't 2) s))
             (pr (alg-primitive (dn-minpoly-t F) m2))
             (Fg (car pr)) (alpha (cadr pr)) (beta (nth pr 2))
             (pairs1 (map (lambda (pe) (cons (car pe) (dn-lift Fg (cdr pe) alpha))) pairs))
             (pairs2 (cons (cons s beta) pairs1)))
        (dn-build Fg pairs2 (cdr rest)))))

(define (dn-build-field rads)
  (let ((F0 (alg-field (list '- (list '^ 't 2) (car rads)) 't)))
    (dn-build F0 (list (cons (car rads) '(0 1))) (cdr rads))))

; (dn-eval F e pairs) — выражение → элемент ℚ(α)
(define (dn-eval F e pairs)
  (cond ((dn-rat? e) (list e))
        ((and (list? e) (equal? (car e) '+))
         (foldl (lambda (acc u) (alg-add F acc (dn-eval F u pairs))) '() (cdr e)))
        ((and (list? e) (equal? (car e) '*))
         (foldl (lambda (acc u) (alg-mul F acc (dn-eval F u pairs))) '(1) (cdr e)))
        ((and (list? e) (equal? (car e) '-))
         (alg-sub F (dn-eval F (nth e 1) pairs) (dn-eval F (nth e 2) pairs)))
        ((and (list? e) (equal? (car e) '/))
         (alg-div F (dn-eval F (nth e 1) pairs) (dn-eval F (nth e 2) pairs)))
        ((and (list? e) (equal? (car e) '^) (= (length e) 3) (integer? (nth e 2)))
         (alg-pow F (dn-eval F (nth e 1) pairs) (nth e 2)))
        ((and (list? e) (equal? (car e) '^) (= (length e) 3) (equal? (nth e 2) 1/2))
         (dn-eval-rad F (nth e 1) pairs))
        ((and (list? e) (equal? (car e) 'sqrt) (= (length e) 2))
         (dn-eval-rad F (nth e 1) pairs))
        (else (error "dn-eval: не поддерживается" e))))

; элемент √r в поле (r — точное, в т. ч. отрицательное: √r = coef·√s·i)
(define (dn-rad-element F r pairs)
  (let* ((a (if (< r 0) (- r) r))
         (sp (dn-square-split (* (numer a) (denom a))))
         (coef (/ (car sp) (denom a)))
         (s (cdr sp))
         (base (if (= s 1) '(1) (cdr (assoc s pairs))))
         (el (alg-mul F (list coef) base)))
    (if (< r 0)
        (alg-mul F el (cdr (assoc -1 pairs)))
        el)))

(define (dn-eval-rad F r pairs)
  (if (not (dn-rat? r))
      (error "dn-eval: под корнем не точное число" r)
      (dn-rad-element F r pairs)))

; ---------- alg-simplify / alg-equal? ----------

(define (dn-expr-radicals e1 e2)
  (dn-union (dn-radicals e1) (dn-radicals e2)))

; (dn-elt->expr F rads pairs elt) — элемент → выражение. Для одного квадратичного радиканда
; печатаем явно a + b·√s (вложение поля может быть отрицательным корнем — не используем его);
; для константы — просто число; иначе — по базису произведений радикалов (WASM.6a Д6:
; раньше печаталось root-of от разности радикалов), а если базис не сходится — alg->expr (root-of).

; произведения радикалов базиса: список (радиканды . элемент поля)
(define (dn-basis-products F pairs)
  (let loop ((ps pairs) (acc (list (cons '() '(1)))))
    (if (null? ps)
        (reverse acc)
        (let* ((s (car (car ps))) (b (cdr (car ps)))
               (more (map (lambda (p) (cons (append (car p) (list s)) (alg-mul F (cdr p) b))) acc)))
          (loop (cdr ps) (append more acc))))))

(define (dn-coord e j) (if (< j (length e)) (nth e j) 0))

; степень поля = степень его минимального многочлена (переменная — x или t)
(define (dn-minpoly-degree F)
  (let ((mp (alg-field-minpoly F)))
    (cond ((contains-sym? mp 'x) (degree mp 'x))
          ((contains-sym? mp 't) (degree mp 't))
          (else 1))))

; коэффициенты разложения elt по произведениям (список согласован с prods) или #f
(define (dn-basis-coeffs F prods elt)
  (let* ((d (dn-minpoly-degree F))
         (m (length prods)))
    (if (not (= m d))
        #f
        (let* ((rows (map (lambda (j)
                            (append (map (lambda (p) (dn-coord (cdr p) j)) prods)
                                    (list (dn-coord elt j))))
                          (range d)))
               (res (tensor->list (rref rows))))
          (if (and (= (length res) m)
                   (every? (lambda (i)
                             (let ((row (nth res i)))
                               (and (= (nth row i) 1)
                                    (every? (lambda (k) (or (= k i) (= (nth row k) 0))) (range m)))))
                           (range m)))
              (map (lambda (row) (nth row m)) res)
              #f)))))

(define (dn-rad-product-expr rs)
  (cond ((null? rs) 1)
        ((null? (cdr rs)) (list '^ (car rs) 1/2))
        (else (cons '* (map (lambda (s) (list '^ s 1/2)) rs)))))

(define (dn-basis->expr prods cs)
  (simplify (cons '+ (map2 (lambda (p c)
                             (if (= c 1) (dn-rad-product-expr (car p))
                                 (list '* c (dn-rad-product-expr (car p)))))
                           prods cs))))

(define (dn-elt->expr F rads pairs elt)
  (cond ((null? elt) 0)
        ((null? (cdr elt)) (car elt))
        ((and (= (length rads) 1) (= (length (alg-field-minpoly F)) 3))
         (simplify (list '+ (car elt)
                         (list '* (cadr elt) (list '^ (car rads) 1/2)))))
        (else
         (let* ((prods (dn-basis-products F pairs))
                (cs (dn-basis-coeffs F prods elt)))
           (if cs (dn-basis->expr prods cs) (alg->expr F elt))))))

; (alg-simplify e) — нормальная форма в ℚ(α); без радикалов — simplify
(define (alg-simplify e)
  (let* ((e1 (dn-normalize-rads (sqrt-denest e)))
         (rads (dn-radicals e1)))
    (if (null? rads)
        (simplify e1)
        (try
         (let* ((fb (dn-build-field rads))
                (F (car fb)) (pairs (cadr fb)))
           (dn-elt->expr F rads pairs (dn-eval F e1 pairs)))
         (lambda (err) (simplify e1))))))

; (alg-equal-expr? e1 e2) — точное равенство выражений с радикалами.
; Глобальный (alg-equal? e1 e2) — диспетчер в prelude (3 аргумента — прежняя функция поля).
(define (alg-equal-expr? a b)
  (let* ((a1 (sqrt-denest a)) (b1 (sqrt-denest b))
         (rads (dn-expr-radicals a1 b1)))
    (if (null? rads)
        (equal? (simplify a1) (simplify b1))
        (try
         (let* ((fb (dn-build-field rads))
                (F (car fb)) (pairs (cadr fb)))
           (dn-field-equal F (dn-eval F a1 pairs) (dn-eval F b1 pairs)))
         (lambda (err) #f)))))

; ================= A1.6: точные корни в solve =================

; чётный многочлен: коэффициенты при x^3 и x нулевые
(define (dn-even-poly? p x)
  (and (equal? (simplify (coeff p x 3)) 0)
       (equal? (simplify (coeff p x 1)) 0)))

; (radical-roots p x) — точные корни биквадратного над ℚ с денестингом или #f.
; Каждый корень проверяется подстановкой в p (alg-equal?), иначе — ошибка.
; (имя solve-radical занято приватной функцией модуля solve — 5 аргументов)
(define (radical-roots p x)
  (let ((e (expand p)))
    (if (and (= (degree e x) 4) (dn-even-poly? e x))
        (dn-biquadratic e x)
        #f)))

(define (dn-sqrt-root y)
  (let ((v (try (eval-num y) (lambda (err) #f))))
    (cond ((and (number? v) (>= v 0)) (sqrt-denest (list '^ y 1/2)))
          ((and (number? v) (< v 0))
           (simplify (list '* (sqrt-denest (list '^ (- y) 1/2)) '%i)))
          (else #f))))

(define (dn-biquadratic e x)
  (let* ((a (simplify (coeff e x 4)))
         (b (simplify (coeff e x 2)))
         (c (simplify (coeff e x 0))))
    (if (not (and (dn-rat? a) (dn-rat? b) (dn-rat? c) (not (= a 0))))
        #f
        (let* ((P (/ b a)) (Q (/ c a)) (D (- (* P P) (* 4 Q))))
          (cond ((not (dn-rat? D)) #f)
                ((< D 0) (dn-complex-roots e x P Q D))
                (else
                 (let* ((s (sqrt-denest (list '^ D 1/2)))
                        (y1 (simplify (list '/ (list '+ (- P) s) 2)))
                        (y2 (simplify (list '/ (list '- (- P) s) 2)))
                        (r1 (dn-sqrt-root y1))
                        (r2 (dn-sqrt-root y2)))
                   (if (or (not r1) (not r2))
                       #f
                       (dn-cert-roots
                        e x
                        (list r1 (simplify (list '* -1 r1))
                              r2 (simplify (list '* -1 r2))))))))))))

; (dn-csqrt Q a b) — √(a + b·i) при |z| = √Q ∈ ℚ (Q — точный квадрат):
; √(a+bi) = √((|z|+a)/2) + sign(b)·i·√((|z|−a)/2)
(define (dn-csqrt Q a b)
  (let* ((r (dn-exact-sqrt Q))
         (u (and r (dn-radical-expr (/ (+ r a) 2))))
         (v (and r (dn-radical-expr (/ (- r a) 2)))))
    (if (or (not u) (not v))
        #f
        (simplify (list '+ u (list '* (if (< b 0) (- v) v) '%i))))))

; D < 0: y = −P/2 ± i√(−D)/2, |y| = √Q; корни x = ±√y
(define (dn-complex-roots e x P Q D)
  (if (or (<= Q 0) (not (dn-exact-sqrt Q)))
      #f
      (let* ((s (sqrt-denest (list '^ (- D) 1/2)))
             (a (- (/ P 2)))
             (b (/ s 2))
             (r1 (dn-csqrt Q a b))
             (r2 (dn-csqrt Q a (- b))))
        (if (or (not r1) (not r2))
            #f
            (dn-cert-roots
             e x
             (list r1 (simplify (list '* -1 r1))
                   r2 (simplify (list '* -1 r2))))))))

; сертификат: каждый корень даёт 0 в исходном многочлене; возвращаются сами корни
(define (dn-cert-roots e x roots)
  (dn-cert-check e x roots)
  roots)

(define (dn-cert-check e x roots)
  (if (null? roots)
      #t
      (let ((v (expand (subst (list '= x (car roots)) e))))
        (if (alg-equal-expr? v 0)
            (dn-cert-check e x (cdr roots))
            (error "radical-roots: корень не прошёл проверку" (car roots))))))