; elliptic.lisp — приведение интегралов с квадратными корнями к формам Лежандра (шаг A3′.3).
;
; Таблица (канонические формы после simplify):
;   ∫ dx/√(1−x⁴)                    → (1/√2)·F(asin(√2·x/√(1+x²)), 1/√2)   — первый род, nonelementary
;   ∫ dx/√((1−x²)(1−k²x²))          → F(asin x, k)                        — первый род, nonelementary
;   ∫ √(1−k²x²)/√(1−x²) dx          → E(asin x, k)                        — второй род, статус unknown
; Ответ проверяется численной квадратурой (Симпсон) в точках 1/2 и 3/4; не прошло — #f.
; Если формы нет в таблице — прежнее поведение (не выдаём неверный ответ).

(module integrate
  (export int-elliptic))

; ---------- численная проверка (Симпсон, eval-num) ----------

(define (int-ell-fval e x t)
  (let ((v (try (eval-num (subst (list '= x t) e)) (lambda (err) #f))))
    (if (number? v) v 0)))

(define (int-ell-simpson-sum e x a h n i acc)
  (if (> i n)
      acc
      (let* ((t (+ a (* i h)))
             (w (cond ((or (= i 0) (= i n)) 1) ((= (modulo i 2) 1) 4) (else 2))))
        (int-ell-simpson-sum e x a h n (+ i 1) (+ acc (* w (int-ell-fval e x t)))))))

(define (int-ell-simpson e x a b n)
  (let ((h (/ (- b a) n)))
    (* (/ h 3) (int-ell-simpson-sum e x a h n 0 0))))

(define (int-ell-check-at ans e x t)
  (let ((v (try (eval-num (subst (list '= x t) ans)) (lambda (err) #f)))
        (q (int-ell-simpson e x 0 t 200)))
    (and (number? v) (number? q) (< (abs (- v q)) 1/1000000))))

(define (int-ell-check ans e x)
  (and (int-ell-check-at ans e x 1/2)
       (int-ell-check-at ans e x 3/4)))

; вещественная часть численного значения (комплекс печатается как (+ re (* im %i)))
(define (int-ell-re v)
  (cond ((number? v) v)
        ((not (pair? v)) #f)
        ((equal? (car v) '+) (int-ell-re (nth v 1)))
        ((and (equal? (car v) '*) (equal? (nth v 2) '%i)) 0)
        (else #f)))

; кубика: производная ответа (конечные разности) сравнивается с 1/√(x³+1)
(define (int-ell-cubic-check-at ans x t)
  (let* ((h 1/100000)
         (v1 (try (int-ell-re (eval-num (subst (list '= x (+ t h)) ans))) (lambda (e) #f)))
         (v0 (try (int-ell-re (eval-num (subst (list '= x (- t h)) ans))) (lambda (e) #f)))
         (ref (try (eval-num (list '^ (list '+ 1 (list '^ t 3)) -1/2)) (lambda (e) #f))))
    (and (number? v1) (number? v0) (number? ref)
         (< (abs (- (/ (- v1 v0) (* 2 h)) ref)) 1/1000))))

(define (int-ell-cubic-check ans x)
  (and (int-ell-cubic-check-at ans x 1/2)
       (int-ell-cubic-check-at ans x 1)
       (int-ell-cubic-check-at ans x 2)))

; ---------- разбор формы ----------

(define (int-ell-one-minus-x2 u x)
  (equal? (simplify u) (simplify (list '+ 1 (list '* -1 (list '^ x 2))))))

; v = 1 − k²·x² → k² (x-free) или #f
(define (int-ell-k2 v x)
  (let ((w (simplify v)))
    (if (and (pair? w) (equal? (car w) '+) (= (length w) 3) (equal? (nth w 1) 1))
        (let ((t2 (nth w 2)))
          (if (and (pair? t2) (equal? (car t2) '*) (= (length t2) 3))
              (let ((p (nth t2 1)) (q (nth t2 2)))
                (cond ((and (equal? q (list '^ x 2)) (x-free? p x)) (- p))
                      ((and (equal? p (list '^ x 2)) (x-free? q x)) (- q))
                      (else #f)))
              #f))
        #f)))

(define (int-ell-one-minus-x4 u x)
  (equal? (simplify u) (simplify (list '+ 1 (list '* -1 (list '^ x 4))))))

; ---------- A3′.6: новые строки таблицы ----------

; w = (^ u -1/2) → u
(define (int-ell-radicand w)
  (if (and (pair? w) (equal? (car w) '^) (= (length w) 3) (equal? (nth w 2) -1/2))
      (nth w 1) #f))

; v = (^ (1−x⁴) -1/2)
(define (int-ell-rad-f1 v x)
  (and (pair? v) (equal? (car v) '^) (= (length v) 3) (equal? (nth v 2) -1/2)
       (int-ell-one-minus-x4 (nth v 1) x)))

; t = c·x² → c (рациональное) | #f
(define (int-ell-coef-x2 t x)
  (cond ((equal? t (list '^ x 2)) 1)
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3))
         (cond ((and (rational-number? (nth t 1)) (equal? (nth t 2) (list '^ x 2))) (nth t 1))
               ((and (equal? (nth t 1) (list '^ x 2)) (rational-number? (nth t 2))) (nth t 2))
               (else #f)))
        (else #f)))

; v = x² + c → c | #f
(define (int-ell-x2-plus-c v x)
  (let ((w (simplify v)))
    (if (and (pair? w) (equal? (car w) '+) (= (length w) 3))
        (cond ((and (equal? (nth w 2) (list '^ x 2)) (rational-number? (nth w 1))) (nth w 1))
              ((and (equal? (nth w 1) (list '^ x 2)) (rational-number? (nth w 2))) (nth w 2))
              (else #f))
        #f)))

; v = 1 − c·x² (c > 0) → c | #f
(define (int-ell-one-minus-c-x2 v x)
  (let ((w (simplify v)))
    (if (and (pair? w) (equal? (car w) '+) (= (length w) 3) (equal? (nth w 1) 1))
        (let ((c (int-ell-coef-x2 (nth w 2) x)))
          (if (and c (< c 0)) (- c) #f))
        #f)))

; v = c − x² (c > 0) → c | #f
(define (int-ell-c-minus-x2 v x)
  (let ((w (simplify v)))
    (if (and (pair? w) (equal? (car w) '+) (= (length w) 3) (rational-number? (nth w 1)))
        (let ((c (int-ell-coef-x2 (nth w 2) x)))
          (if (and c (= c -1) (> (nth w 1) 0)) (nth w 1) #f))
        #f)))

; u = (x²+p)(x²+q) → (p q)
(define (int-ell-quad-pair u x)
  (let ((w (simplify u)))
    (if (and (pair? w) (equal? (car w) '*) (= (length w) 3))
        (let ((p (int-ell-x2-plus-c (nth w 1) x)) (q (int-ell-x2-plus-c (nth w 2) x)))
          (and p q (list p q)))
        #f)))

; u = (p−x²)(q−x²) → (p q)
(define (int-ell-f3-pair u x)
  (let ((w (simplify u)))
    (if (and (pair? w) (equal? (car w) '*) (= (length w) 3))
        (let ((p (int-ell-c-minus-x2 (nth w 1) x)) (q (int-ell-c-minus-x2 (nth w 2) x)))
          (and p q (list p q)))
        #f)))

; пара (p q) → (p>q>0) или #f
(define (int-ell-two-args pq)
  (and pq
       (let ((p (if (> (car pq) (cadr pq)) (car pq) (cadr pq)))
             (q (if (> (car pq) (cadr pq)) (cadr pq) (car pq))))
         (and (> q 0) (list p q)))))

; сортировка трёх рациональных по возрастанию
(define (int-ell-sort3 a b c)
  (let ((hi (if (> a b) a b)) (lo (if (> a b) b a)))
    (cond ((> c hi) (list lo hi c))
          ((> c lo) (list lo c hi))
          (else (list c lo hi)))))

; линейный множитель a·x+b → корень −b/a | #f
(define (int-ell-linear-root f x)
  (let ((cs (try (coefficients f x) (lambda (err) #f))))
    (if (and cs (= (length cs) 2) (every? rational-number? cs) (not (= (nth cs 1) 0)))
        (/ (- (nth cs 0)) (nth cs 1)) #f)))

; u = A·(x−r1)(x−r2)(x−r3), A > 0, r1 < r2 < r3 рациональные → (A r1 r2 r3) | #f
(define (int-ell-cubic-real u x)
  (let ((fl (try (factor-list u) (lambda (err) #f))))
    (and fl (rational-number? (car fl)) (> (car fl) 0)
         (= (length (cdr fl)) 3)
         (every? (lambda (fk) (= (cadr fk) 1)) (cdr fl))
         (let ((rs (map (lambda (fk) (int-ell-linear-root (car fk) x)) (cdr fl))))
           (and (every? (lambda (r) r) rs)
                (let ((ss (int-ell-sort3 (nth rs 0) (nth rs 1) (nth rs 2))))
                  (and (< (nth ss 0) (nth ss 1)) (< (nth ss 1) (nth ss 2))
                       (list (car fl) (nth ss 0) (nth ss 1) (nth ss 2)))))))))

; u = a + b·x³ (a,b рациональные, b ≠ 0) → (a b) | #f
(define (int-ell-ab-x3 u x)
  (let ((w (simplify u)))
    (if (and (pair? w) (equal? (car w) '+) (= (length w) 3))
        (let* ((t1 (nth w 1)) (t2 (nth w 2))
               (c1 (if (equal? t1 (list '^ x 3)) 1
                       (and (pair? t1) (equal? (car t1) '*) (= (length t1) 3)
                            (rational-number? (nth t1 1))
                            (equal? (nth t1 2) (list '^ x 3)) (nth t1 1))))
               (c2 (if (equal? t2 (list '^ x 3)) 1
                       (and (pair? t2) (equal? (car t2) '*) (= (length t2) 3)
                            (rational-number? (nth t2 1))
                            (equal? (nth t2 2) (list '^ x 3)) (nth t2 1)))))
          (cond ((and c1 (rational-number? t2) (not (= t2 0)) (not (= c1 0))) (list t2 c1))
                ((and c2 (rational-number? t1) (not (= t1 0)) (not (= c2 0))) (list t1 c2))
                (else #f)))
        #f)))

; Π(n;φ,k): e = 1/((1−n·x²)·√((1−x²)(1−k²x²))) → (n k²) | #f
(define (int-ell-one-minus-pair u x)
  (let ((w (simplify u)))
    (if (and (pair? w) (equal? (car w) '*) (= (length w) 3))
        (let ((c1 (int-ell-one-minus-c-x2 (nth w 1) x))
              (c2 (int-ell-one-minus-c-x2 (nth w 2) x)))
          (and c1 c2 (list c1 c2)))
        #f)))

(define (int-ell-k2-pair u x)
  (let ((cs (int-ell-one-minus-pair u x)))
    (cond ((not cs) #f)
          ((= (car cs) 1) (cadr cs))
          ((= (cadr cs) 1) (car cs))
          (else #f))))

(define (int-ell-pi-parts sq pl x)
  (let ((u (int-ell-radicand sq)))
    (and u (pair? pl) (equal? (car pl) '^) (= (length pl) 3) (equal? (nth pl 2) -1)
         (let ((n (int-ell-one-minus-c-x2 (nth pl 1) x))
               (k2 (int-ell-k2-pair u x)))
           (and n k2 (list n k2))))))

(define (int-ell-pi-form e x)
  (if (and (pair? e) (equal? (car e) '*) (= (length e) 3))
      (or (int-ell-pi-parts (nth e 1) (nth e 2) x)
          (int-ell-pi-parts (nth e 2) (nth e 1) x))
      #f))

; (int-ell-form e x) → форма (kind …) или #f
(define (int-ell-form e x)
  (let* ((w (simplify e))
         (u (int-ell-radicand w)))
    (cond
      ; f1: 1/√(1−x⁴)
      ((and u (int-ell-one-minus-x4 u x)) (list 'f1 1))
      ; кубика x³+1: один вещественный корень, модуль Лежандра комплексный (j = 0)
      ((and u (equal? (simplify u) (simplify (list '+ 1 (list '^ x 3))))) (list 'cubic 1))
      ; f: 1/√((1−x²)(1−k²x²))
      ((and u (pair? u) (equal? (car u) '*) (= (length u) 3)
            (int-ell-one-minus-x2 (nth u 1) x) (int-ell-k2 (nth u 2) x))
       (list 'f (int-ell-k2 (nth u 2) x)))
      ; e: √(1−k²x²)/√(1−x²)
      ((and (pair? w) (equal? (car w) '*) (= (length w) 3)
            (pair? (nth w 1)) (equal? (car (nth w 1)) '^) (= (length (nth w 1)) 3)
            (equal? (nth (nth w 1) 2) -1/2)
            (int-ell-one-minus-x2 (nth (nth w 1) 1) x)
            (pair? (nth w 2)) (equal? (car (nth w 2)) '^) (= (length (nth w 2)) 3)
            (equal? (nth (nth w 2) 2) 1/2) (int-ell-k2 (nth (nth w 2) 1) x))
       (list 'e (int-ell-k2 (nth (nth w 2) 1) x)))
      ; A3′.6: Π третьего рода
      ((int-ell-pi-form w x) (cons 'pi3 (int-ell-pi-form w x)))
      ; A3′.6: x²/√(1−x⁴)
      ((and (pair? w) (equal? (car w) '*) (= (length w) 3)
            (or (and (equal? (nth w 1) (list '^ x 2)) (int-ell-rad-f1 (nth w 2) x))
                (and (equal? (nth w 2) (list '^ x 2)) (int-ell-rad-f1 (nth w 1) x))))
       (list 'x2f1 1))
      ; A3′.6: 1/√(a+bx³), три вещественных корня, (x²+a²)(x²+b²), (a²−x²)(b²−x²)
      (u (or (let ((ab (int-ell-ab-x3 u x))) (and ab (cons 'cubab ab)))
             (let ((cr (int-ell-cubic-real u x))) (and cr (cons 'cubreal cr)))
             (let ((f2 (int-ell-two-args (int-ell-quad-pair u x)))) (and f2 (cons 'f2 f2)))
             (let ((f3 (int-ell-two-args (int-ell-f3-pair u x)))) (and f3 (cons 'f3 f3)))
             #f))
      (else #f))))

; ---------- ответ ----------

; ∫dx/√(x³+1) = −2·r̄·F(asin(3^{1/4}·e^{iπ/12}/√(x+1)), λ), r̄ = 3^{−1/4}e^{−iπ/12}, λ = e^{−iπ/6}
(define (int-ell-cubic-answer x)
  (let* ((lam (list '- (list '/ (list 'sqrt 3) 2) (list '* 1/2 '%i)))
         (ei12 (list '+ (list '/ (list '+ (list 'sqrt 6) (list 'sqrt 2)) 4)
                      (list '* (list '/ (list '- (list 'sqrt 6) (list 'sqrt 2)) 4) '%i)))
         (er12 (list '- (list '/ (list '+ (list 'sqrt 6) (list 'sqrt 2)) 4)
                      (list '* (list '/ (list '- (list 'sqrt 6) (list 'sqrt 2)) 4) '%i)))
         (w (list '* (list '^ (list '+ 1 x) -1/2) (list '^ 3 1/4) ei12)))
    (list '* -2 (list '^ 3 -1/4) er12 (list 'elliptic-f (list 'asin w) lam))))

(define (int-ell-x2f1-answer x)
  (let* ((k (list '^ 2 -1/2))
         (phi (list 'asin (list '/ (list '* (list '^ 2 1/2) x)
                                (list '^ (list '+ 1 (list '^ x 2)) 1/2))))
         (s (list '^ (list '+ 1 (list '* -1 (list '^ x 4))) 1/2)))
    (simplify (list '-
                    (list '- (list '* (list '^ 2 1/2) (list 'elliptic-e phi k))
                          (list '* (list '^ 2 -1/2) (list 'elliptic-f phi k)))
                    (list '/ (list '* x s) (list '+ 1 (list '^ x 2)))))))

; ∫dx/√(a+bx³): x = r^{−1/3}·u, r = b/a; знаковый кубический корень, ∫du/√(1+u³) — кубика
(define (int-ell-cubic-ab a b x)
  (let* ((r (/ b a))
         (s (list '^ (abs r) 1/3))
         (u (if (> r 0) (list '* s x) (list '* -1 s x)))
         (fa (if (> a 0) (list '^ a -1/2)
                 (list '* -1 '%i (list '^ (- a) -1/2))))
         (inv (if (> r 0) (list '^ s -1) (list '* -1 (list '^ s -1)))))
    (simplify (list '* fa inv (int-ell-cubic-answer u)))))

; три вещественных корня r1 < r2 < r3: −2/√(A(r3−r1))·F(asin√((r3−r1)/(x−r1)), k), k=√((r3−r2)/(r3−r1))
(define (int-ell-cubreal-answer A r1 r2 r3 x)
  (let* ((d (simplify (list '- r3 r1)))
         (k (list '^ (list '/ (list '- r3 r2) d) 1/2))
         (phi (list 'asin (list '^ (list '/ d (list '- x r1)) 1/2))))
    (simplify (list '* -2 (list '^ (list '* A d) -1/2) (list 'elliptic-f phi k)))))

; ∫dx/√((x²+p)(x²+q)), p>q>0: (1/√p)·(K(k)−F(asin(√p/√(x²+p)),k)), k=√((p−q)/p)
(define (int-ell-f2-answer p q x)
  (let* ((k (list '^ (list '/ (list '- p q) p) 1/2))
         (phi (list 'asin (list '/ (list '^ p 1/2)
                                (list '^ (list '+ (list '^ x 2) p) 1/2)))))
    (simplify (list '* (list '^ p -1/2)
                    (list '- (list 'elliptic-k k)
                          (list 'elliptic-f phi k))))))

; ∫dx/√((p−x²)(q−x²)), p>q>0: (1/√p)·F(asin(x/√q), √(q/p))
(define (int-ell-f3-answer p q x)
  (let* ((k (list '^ (list '/ q p) 1/2))
         (phi (list 'asin (list '/ x (list '^ q 1/2)))))
    (simplify (list '* (list '^ p -1/2) (list 'elliptic-f phi k)))))

(define (int-ell-answer f x)
  (let ((kind (car f)))
    (cond
      ((equal? kind 'cubic) (int-ell-cubic-answer x))
      ((equal? kind 'f1)
       (let ((r (list 'sqrt 2)))
         (list '* (list '/ 1 r)
               (list 'elliptic-f
                     (list 'asin (list '/ (list '* r x)
                                       (list 'sqrt (list '+ 1 (list '^ x 2)))))
                     (list '/ 1 r)))))
      ((equal? kind 'f) (list 'elliptic-f (list 'asin x) (simplify (list 'sqrt (nth f 1)))))
      ((equal? kind 'e) (list 'elliptic-e (list 'asin x) (simplify (list 'sqrt (nth f 1)))))
      ((equal? kind 'x2f1) (int-ell-x2f1-answer x))
      ((equal? kind 'cubab) (int-ell-cubic-ab (nth f 1) (nth f 2) x))
      ((equal? kind 'cubreal)
       (int-ell-cubreal-answer (nth f 1) (nth f 2) (nth f 3) (nth f 4) x))
      ((equal? kind 'f2) (int-ell-f2-answer (nth f 1) (nth f 2) x))
      ((equal? kind 'f3) (int-ell-f3-answer (nth f 1) (nth f 2) x))
      (else (list 'elliptic-pi (nth f 1) (list 'asin x)
                  (simplify (list 'sqrt (nth f 2))))))))

; ---------- стратегия ----------

; производная ответа (конечные разности вещественной части) против подынтегрального
(define (int-ell-deriv-at ans e x t)
  (let* ((h 1/100000)
         (v1 (int-ell-re (try (eval-num (subst (list '= x (+ t h)) ans)) (lambda (er) #f))))
         (v0 (int-ell-re (try (eval-num (subst (list '= x (- t h)) ans)) (lambda (er) #f))))
         (ref (int-ell-re (try (eval-num (subst (list '= x t) e)) (lambda (er) #f)))))
    (and (number? v1) (number? v0) (number? ref)
         (< (abs (- (/ (- v1 v0) (* 2 h)) ref)) 1/1000))))

(define (int-ell-cert-ok? f ans e x)
  (let ((kind (car f)))
    (cond ((equal? kind 'cubic) (int-ell-cubic-check ans x))
          ((equal? kind 'cubreal)
           (let ((r3 (nth f 4)))
             (and (int-ell-deriv-at ans e x (+ r3 1/2))
                  (int-ell-deriv-at ans e x (+ r3 1)))))
          ((equal? kind 'cubab)
           (and (int-ell-deriv-at ans e x 1/2)
                (int-ell-deriv-at ans e x 3/4)))
          (else (int-ell-check ans e x)))))

(define (int-elliptic e x d)
  (let ((f (int-ell-form e x)))
    (if (not f)
        #f
        (let ((ans (simplify (int-ell-answer f x))))
          (if (not (int-ell-cert-ok? f ans e x))
              #f
              (begin
                ; первый род (и кубики): элементарной первообразной нет — ответ через F, отказ доказан
                (if (member? (car f) '(f1 f cubic cubab cubreal f2 f3))
                    (record-condition
                     (list 'risch-nonelementary (int-unevaluated e x '()))
                     "эллиптический интеграл первого рода: элементарной первообразной нет (Лиувилль); ответ — через F"))
                ans))))))

(int-add-strategy int-elliptic)
