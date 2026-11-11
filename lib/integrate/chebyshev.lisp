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

; ---------- обобщение (шаг INT.CH): x^m·(α+β·x^n)^p·R(x^n) и нераскрытый радикал ----------
;
; Подынтегральное = c · x^m0 · P(x)^p · R, p нецелое рациональное, P = x^k·(α+β·x^n) (k ≥ 0 целое), R — произведение
; остальных множителей, рациональное по w = x^n. Тогда m = m0 + k·p (P^p = x^{kp}·(α+βx^n)^p) и три случая Чебышёва:
; p ∈ ℤ здесь невозможен (p нецелое), остаются (m+1)/n ∈ ℤ (t^s = α+β·w) и (m+1)/n + p ∈ ℤ (t^s = α/w + β), s = denom p;
; R(w) выражается через t рационально. Ответ проверяется ЧИСЛЕННО (параметры — пробные числа) в точках x > 0 и x < 0:
; верно везде — без условий; только при x > 0 — условие (> x 0) (ветви x^{1/s}, расщепление (f·g)^p при f < 0).
; Отказ по теореме (NE) — только если R = 1 и α, β — ненулевые числа; с символьными α, β или с R — «не знаю».

; P = x^k·(α+β·x^n) → (k α β n) или #f
(define (int-cheb-split-base base x)
  (let ((b0 (expand base)))
    (cond ((int-cheb-base b0 x) (let ((r (int-cheb-base b0 x))) (list 0 (nth r 0) (nth r 1) (nth r 2))))
          ((polynomial? b0 x)
           (let* ((dg (degree b0 x))
                  (exps (filter (lambda (i) (not (equal? (coeff b0 x i) 0))) (range (+ dg 1)))))
             (if (= (length exps) 2)
                 (list (car exps) (coeff b0 x (car exps)) (coeff b0 x (cadr exps)) (- (cadr exps) (car exps)))
                 #f)))
          (else #f))))

; разбор множителей → (m0 коэффициенты радикал R-множители) или #f (радикал должен быть ровно один)
(define (int-cheb-gen-parse e x)
  (let loop ((l (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e))) (m 0) (cs '()) (rad '()) (rest '()))
    (if (null? l)
        (if (= (length rad) 1) (list m cs (car rad) rest) #f)
        (let ((f (car l)))
          (cond ((x-free? f x) (loop (cdr l) m (cons f cs) rad rest))
                ((equal? f x) (loop (cdr l) (+ m 1) cs rad rest))
                ((int-cheb-pow-x f x) (loop (cdr l) (+ m (int-cheb-pow-x f x)) cs rad rest))
                ((and (pair? f) (equal? (car f) '^) (= (length f) 3) (rational-number? (nth f 2)) (not (integer? (nth f 2))))
                 (loop (cdr l) m cs (cons f rad) rest))
                (else (loop (cdr l) m cs rad (cons f rest))))))))

(define int-cheb-neg-points '(-3/10 -47/100 -71/100 -137/100 -11/5))

; 'all — верно в точках x > 0 и x < 0; 'pos — только x > 0; #f — неверно
(define (int-cheb-gen-verify ans e x)
  (let* ((dfe (list '- (int-diff x ans) (simplify e)))
         (sp (int-numeric-status-at dfe e x 0.000000001 int-test-points)))
    (cond ((not (equal? sp 'ok)) #f)
          ((equal? (int-numeric-status-at dfe e x 0.000000001 int-cheb-neg-points) 'ok) 'all)
          (else 'pos))))

; R(w) = N/D с параметрами и deg N ≥ deg D: делим с остатком, подынтегральное — сумма (частное + остаток/D), каждое
; слагаемое берёт каскад отдельно (рациональный интеграл с параметрами не разлагается на дроби, пока числитель «длинный»).
; → новое подынтегральное по x или #f
(define (int-cheb-divide e x n rest)
  (let* ((w '%cw)
         (rs (map (lambda (f) (int-xpow-subst f x n w)) rest)))
    (and (every? (lambda (f) f) rs)
         (let* ((tg (together (simplify (cons '* (cons 1 rs)))))
                (nu (numer tg)) (de (denom tg)))
           (and (polynomial? nu w) (polynomial? de w) (>= (degree nu w) (degree de w)) (> (degree de w) 0)
                (let ((qq (poly-quotient nu de w)) (rr (poly-remainder nu de w)))
                  (expand
                   (list '* (simplify (list '* e (list '^ (cons '* rest) -1)))
                         (replace-expr (list '+ qq (list '* rr (list '^ de -1))) w (list '^ x n))))))))))

(define (int-cheb-gen-run kind e x d m n p al be coef rest)
  (let ((e2 (and (pair? rest) (pair? (int-symbols (cons '* rest) x)) (int-cheb-divide e x n rest))))
    (if e2
        (with-step ('int-expand "Деление с остатком в рациональном множителе" (int-form e x)
                    :comment "R(x^n) = частное + остаток/знаменатель; слагаемые интегрируем отдельно" :after int-p)
          (let ((r (int-go e2 x (+ d 1))))
            (if r r (begin (attempt-fail "после деления с остатком не интегрируется") #f))))
        (int-cheb-gen-run1 kind e x d m n p al be coef rest))))

(define (int-cheb-gen-run1 kind e x d m n p al be coef rest)
  (let* ((s (denom p)) (P (* p s)) (q1 (/ (+ m 1) n)) (qq (+ q1 p)) (t (int-uvar d)) (w '%cw)
         (tsa (list '+ (list '^ t s) (list '* -1 (if (equal? kind 'b) al be))))
         (wexpr (if (equal? kind 'b)
                    (list '* tsa (list '^ be -1))
                    (list '* al (list '^ tsa -1))))
         (rs (map (lambda (f) (int-xpow-subst f x n w)) rest)))
    (and (every? (lambda (f) f) rs)
         (let* ((Rt (replace-expr (simplify (cons '* (cons 1 rs))) w wexpr))
                (q (simplify
                    (if (equal? kind 'b)
                        (list '* coef (/ s n) (list '^ be -1) (list '^ wexpr (- q1 1)) (list '^ t (+ P s -1)) Rt)
                        (list '* coef (- (/ s n)) (list '^ al qq) (list '^ tsa (- (- qq) 1)) (list '^ t (+ P s -1)) Rt))))
                (back (if (equal? kind 'b)
                          (list '^ (list '+ al (list '* be (list '^ x n))) (/ 1 s))
                          (list '^ (list '+ (list '* al (list '^ x (- n))) be) (/ 1 s)))))
           (and (x-free? q x)
                (with-step ('int-substitution "Метод подстановки" (int-form e x)
                            :comment (lambda (r) (string-append "биномиальный дифференциал (Чебышёв): t = " (int-mp back)
                                                                (if (equal? kind 'b) ", t^s = α + β·x^n" ", t^s = α·x^(−n) + β")))
                            :after int-p)
                  (let ((r (begin
                             (if (step-log-enabled?)
                                 (record-step 'int-substitution-change "Замена переменной"
                                              (string-append "подынтегральное выражение через t: " (int-mp q) " dt")
                                              (int-form e x) (int-form q t)))
                             (int-go q t (+ d 1)))))
                    (if r
                        (let* ((ans (simplify (replace-expr r t back)))
                               (ok (int-cheb-gen-verify ans e x)))
                          (cond ((equal? ok 'all) ans)
                                ((and (equal? ok 'pos) (int-real-on-neg? e x))
                                 (attempt-fail "ответ подстановки Чебышёва верен лишь при x > 0, а подынтегральное вещественно и при x < 0")
                                 #f)
                                ((equal? ok 'pos)
                                 (record-condition (list '> x 0) "integrate: ответ подстановки Чебышёва верен при x > 0")
                                 ans)
                                (else (attempt-fail "ответ подстановки Чебышёва не прошёл численную проверку") #f)))
                        (begin (attempt-fail "не удалось проинтегрировать выражение через t") #f)))))))))

(define (int-cheb-gen e x d)
  (and (< d int-max-depth) (op-expr? e)
       (let ((pr (int-cheb-gen-parse e x)))
         (and pr
              (let* ((f0 (nth pr 2)) (p (nth f0 2)) (sp (int-cheb-split-base (nth f0 1) x)))
                (and sp
                     (let* ((k (nth sp 0)) (al (nth sp 1)) (be (nth sp 2)) (n (nth sp 3))
                            (m (+ (nth pr 0) (* k p)))
                            (coef (simplify (cons '* (cons 1 (nth pr 1)))))
                            (rest (nth pr 3)))
                       (cond ((or (integer? (/ (+ m 1) n)) (integer? (+ (/ (+ m 1) n) p)))
                              (let ((kind (if (integer? (/ (+ m 1) n)) 'b 'c)))
                                (if (and (null? rest) (equal? (denom p) 2))
                                    ; чистый квадратный радикал P(x)^(±1/2): общий алгебраический путь (Кантор) даёт ответ
                                    ; без условия x > 0 — сначала он, подстановка Чебышёва — запасной путь
                                    (or (int-guard (lambda () (integrate::alg-int-strategy e x d)))
                                        (int-cheb-gen-run kind e x d m n p al be coef rest))
                                    (int-cheb-gen-run kind e x d m n p al be coef rest))))
                             ((and (null? rest) (number? al) (number? be))
                              (int-cheb-refuse e x m n p al be)
                              #f)
                             (else #f)))))))))

; доказанный отказ: условие risch-nonelementary для e (+ шаг)
(define (int-cheb-refuse e x m n p a b)
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
                  (if (or (not (number? a)) (not (number? b))) "; условие: a ≠ 0, b ≠ 0" ""))))

(define (int-chebyshev e x d)
  (let ((f (int-cheb-form e x)))
    (if (not f)
        (int-cheb-gen e x d)
        (let* ((m (nth f 0)) (n (nth f 1)) (p (nth f 2))
               (a (nth f 3)) (b (nth f 4)) (c (nth f 5)))
          (cond ((not (int-cheb-elementary? m n p))
                 (int-cheb-refuse e x m n p a b)
                 #f)
                ((integer? p) (let ((r (int-cheb-case-a m n p a b c x)))
                                (if (int-cheb-ok? r e x) (int-cheb-finish r e x) #f)))
                ((integer? (/ (+ m 1) n)) (let ((r (int-cheb-case-b m n p a b c x)))
                                            (if (int-cheb-ok? r e x) (int-cheb-finish r e x) #f)))
                (else (let ((r (int-cheb-case-c m n p a b c x)))
                        (if (int-cheb-ok? r e x) (int-cheb-finish r e x) #f))))))))

; ответ верен численно только при x > 0 (подстановка t = α·x^(−n) + β и т. п. на x < 0) — честное условие
; Шаг INT.BR: если подынтегральное вещественно и при x < 0, ответ «только при x > 0» — потеря области определения
; (√(1−x²) = |x|·√(x⁻²−1)): отказываемся, ответит другая стратегия (алгебраическая, Rubi)
(define (int-cheb-finish r e x)
  (if (equal? (try (int-cheb-gen-verify r e x) (lambda (err) #f)) 'pos)
      (if (int-real-on-neg? e x)
          (begin (attempt-fail "ответ подстановки Чебышёва верен лишь при x > 0, а подынтегральное вещественно и при x < 0") #f)
          (begin (record-condition (list '> x 0) "integrate: ответ подстановки Чебышёва верен при x > 0") r))
      r))

(int-add-strategy int-chebyshev)
