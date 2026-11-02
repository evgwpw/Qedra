; chebyshev.lisp — теорема Чебышёва о биномиальном дифференциале (шаг A3′.1).
;
; ∫ x^m (a + b·x^n)^p dx (m, n, p ∈ ℚ) элементарен ⇔ p ∈ ℤ, или (m+1)/n ∈ ℤ,
; или (m+1)/n + p ∈ ℤ (Чебышёв 1853). В этих случаях — подстановка, сведение к
; рациональной функции и обратная замена; иначе — доказанный отказ (nonelementary).
; Сертификат элементарного ответа — дифференцирование (int-check).

(module integrate
  (export int-chebyshev int-cheb-form int-cheb-elementary?))

; ---------- разбор формы ----------

; (int-cheb-pow-x t x) — (^ x r) с рациональным r → r, иначе #f
(define (int-cheb-pow-x t x)
  (if (and (pair? t) (equal? (car t) '^) (= (length t) 3)
           (equal? (nth t 1) x) (rational-number? (nth t 2)))
      (nth t 2)
      #f))

; t = x^n или c·x^n (c x-free) → (n . c) или #f
(define (int-cheb-xn-term t x)
  (cond ((int-cheb-pow-x t x) (cons (int-cheb-pow-x t x) 1))
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3))
         (let* ((u (nth t 1)) (v (nth t 2))
                (pu (int-cheb-pow-x u x)) (pv (int-cheb-pow-x v x)))
           (cond ((and (not pu) (x-free? u x) pv) (cons pv u))
                 ((and (not pv) (x-free? v x) pu) (cons pu v))
                 (else #f))))
        (else #f)))

; (int-cheb-base e x) — a + b·x^n → (a b n) или #f
(define (int-cheb-base e x)
  (if (and (pair? e) (equal? (car e) '+) (= (length e) 3))
      (let* ((t1 (nth e 1)) (t2 (nth e 2))
             (p1 (int-cheb-xn-term t1 x)) (p2 (int-cheb-xn-term t2 x)))
        (cond ((and (not p1) (x-free? t1 x) p2) (list t1 (cdr p2) (car p2)))
              ((and p1 (not p2) (x-free? t2 x)) (list t2 (cdr p1) (car p1)))
              (else #f)))
      #f))

; разбор одного множителя в накопитель (m n p a b coef);
; накопитель — список (m n p a b coef), binomial найден, если p ≠ #f
(define (int-cheb-factor t x acc)
  (let ((m (nth acc 0)) (n (nth acc 1)) (p (nth acc 2))
        (a (nth acc 3)) (b (nth acc 4)) (c (nth acc 5)))
    (cond ((rational-number? t) (list m n p a b (* c t)))
          ((equal? t x) (list (+ m 1) n p a b c))
          ((x-free? t x) (list m n p a b (* c t)))
          ((int-cheb-pow-x t x)
           (list (+ m (int-cheb-pow-x t x)) n p a b c))
          ((and (pair? t) (equal? (car t) '^) (= (length t) 3)
                (rational-number? (nth t 2)))
           (let ((bs (int-cheb-base (nth t 1) x)))
             (if (and bs (equal? p #f))
                 (list m (nth bs 2) (nth t 2) (nth bs 0) (nth bs 1) c)
                 #f)))
          ((and (pair? t) (equal? (car t) '/) (= (length t) 3))
           (let* ((num (int-cheb-factor (nth t 1) x acc)))
             (if num (int-cheb-factor (nth t 2) x (int-cheb-neg-exps num)) #f)))
          ((and (pair? t) (equal? (car t) '*))
           (int-cheb-fold (cdr t) x acc))
          (else #f))))

; деление: степени при x и биномиальный множитель получают минус
(define (int-cheb-neg-exps acc)
  (list (- (nth acc 0)) (nth acc 1) (nth acc 2)
        (nth acc 3) (nth acc 4) (nth acc 5)))

(define (int-cheb-neg-exps2 acc)   ; для (^ base p) в знаменателе: только p меняет знак
  (list (nth acc 0) (nth acc 1)
        (if (equal? (nth acc 2) #f) #f (- (nth acc 2)))
        (nth acc 3) (nth acc 4) (nth acc 5)))

(define (int-cheb-fold fs x acc)
  (if (null? fs)
      acc
      (let ((r (int-cheb-factor (car fs) x acc)))
        (if r (int-cheb-fold (cdr fs) x r) #f))))

; (int-cheb-form e x) → (m n p a b coef) или #f
(define (int-cheb-form e x)
  (let ((r (int-cheb-factor e x (list 0 0 #f #f #f 1))))
    (if (and r (not (equal? (nth r 2) #f)) (not (= (nth r 1) 0)))
        r
        #f)))

; ---------- критерий ----------

(define (int-cheb-elementary? m n p)
  (or (integer? p)
      (integer? (/ (+ m 1) n))
      (integer? (+ (/ (+ m 1) n) p))))

; ---------- подстановки ----------

(define (int-cheb-num q) (nth q 5))

; p ∈ ℤ: x = t^N, N = lcm(знаменателей m и n)
(define (int-cheb-case-a m n p a b c x)
  (let* ((N (lcm (denom m) (denom n)))
         (M (* m N)) (Nn (* n N))
         (t '%ct)
         (expr (simplify (list '* c N
                               (list '^ t (+ M N -1))
                               (list '^ (simplify (list '+ a (list '* b (list '^ t Nn)))) p)))))
    (let ((F (int-guard (lambda () (integrate expr t)))))
      (if F (simplify (subst (list t (list '^ x (/ 1 N))) F)) #f))))

; (m+1)/n = q ∈ ℤ: t^s = a + b·x^n, s = знаменатель p
(define (int-cheb-case-b m n p a b c x)
  (let* ((s (denom p)) (P (* p s)) (q (/ (+ m 1) n)) (t '%ct)
         (expr (simplify (list '* c (/ s (* n b))
                               (list '^ (list '/ (list '- (list '^ t s) a) b) (- q 1))
                               (list '^ t (+ P s -1))))))
    (let ((F (int-guard (lambda () (integrate expr t)))))
      (if F (simplify (subst (list t (list '^ (simplify (list '+ a (list '* b (list '^ x n)))) (/ 1 s))) F)) #f))))

; (m+1)/n + p = q ∈ ℤ: t^s = a·x^{−n} + b
(define (int-cheb-case-c m n p a b c x)
  (let* ((s (denom p)) (P (* p s)) (q (+ (/ (+ m 1) n) p)) (t '%ct)
         (expr (simplify (list '* (- (/ s n)) (list '^ a q)
                               (list '^ (list '- (list '^ t s) b) (- (- q) 1))
                               (list '^ t (+ P s -1))))))
    (let ((F (int-guard (lambda () (integrate expr t)))))
      (if F (simplify (subst (list t (list '^ (simplify (list '+ (* a (list '^ x (- n))) b)) (/ 1 s))) F)) #f))))

; ---------- стратегия ----------

; вещественная часть численного значения (дробные степени дают микроскопическую мнимую часть)
(define (int-cheb-re v)
  (cond ((number? v) v)
        ((not (pair? v)) #f)
        ((equal? (car v) '+) (int-cheb-re (nth v 1)))
        ((and (equal? (car v) '*) (equal? (nth v 2) '%i)) 0)
        (else #f)))

; численная проверка ответа (дробные степени simplify не всегда сводит): конечные разности
(define (int-cheb-num-check-at ans e x t)
  (let* ((h 1/100000)
         (v1 (try (int-cheb-re (eval-num (subst (list '= x (+ t h)) ans))) (lambda (err) #f)))
         (v0 (try (int-cheb-re (eval-num (subst (list '= x (- t h)) ans))) (lambda (err) #f)))
         (ref (try (int-cheb-re (eval-num (subst (list '= x t) e))) (lambda (err) #f))))
    (and (number? v1) (number? v0) (number? ref)
         (< (abs (- (/ (- v1 v0) (* 2 h)) ref)) 1/1000))))

(define (int-cheb-num-check ans e x)
  (and (int-cheb-num-check-at ans e x 1/2)
       (int-cheb-num-check-at ans e x 3/4)
       (int-cheb-num-check-at ans e x 2)))

(define (int-cheb-ok? r e x)
  (and r (or (int-check r e x) (int-cheb-num-check r e x))))

(define (int-chebyshev e x d)
  (let ((f (int-cheb-form e x)))
    (if (not f)
        #f
        (let* ((m (nth f 0)) (n (nth f 1)) (p (nth f 2))
               (a (nth f 3)) (b (nth f 4)) (c (nth f 5)))
          (cond ((not (int-cheb-elementary? m n p))
                 (if (step-log-enabled?)
                     (record-step 'alg-refusal "Неэлементарность доказана"
                                  (string-append "теорема Чебышёва: интеграл ∫ x^m (a + b·x^n)^p dx элементарен только если p, (m+1)/n или (m+1)/n + p целое; здесь p = "
                                                 (to-string p) ", (m+1)/n = " (to-string (/ (+ m 1) n)) ", (m+1)/n + p = "
                                                 (to-string (+ (/ (+ m 1) n) p)))
                                  (int-form e x) 'nonelementary 'main))
                 (record-condition
                  (list 'risch-nonelementary (int-unevaluated e x '()))
                  (string-append "интеграл неэлементарен по теореме Чебышёва: p = " (to-string p)
                                 ", (m+1)/n = " (to-string (/ (+ m 1) n)) " — все три условия не выполнены"
                                 (if (or (not (number? a)) (not (number? b))) "; условие: a ≠ 0, b ≠ 0" "")))
                 #f)
                ((integer? p) (let ((r (int-cheb-case-a m n p a b c x)))
                                (if (int-cheb-ok? r e x) r #f)))
                ((integer? (/ (+ m 1) n)) (let ((r (int-cheb-case-b m n p a b c x)))
                                            (if (int-cheb-ok? r e x) r #f)))
                (else (let ((r (int-cheb-case-c m n p a b c x)))
                        (if (int-cheb-ok? r e x) r #f))))))))

(int-add-strategy int-chebyshev)
