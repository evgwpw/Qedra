; integrate/trig.lisp — степени sin/cos, корни квадратного трёхчлена, произведения sin/cos (часть бывшего lib\integrate.lisp,
; шаг 21h'). Регистрирует стратегии int-trig, int-sqrt-quad, int-prodsum. Загружается после integrate/rational.lisp.
(module integrate)

; ---------- степени sin и cos ----------
; e = sin(u)^m · cos(u)^n (m, n — целые, u линейно по x, наклон a). Работаем по переменной v (вместо u), в конце v → u, делим на a.
;   m = 0 или n = 0 — рекуррентные формулы понижения (для отрицательных степеней — обратные: sec³, csc⁴...);
;   m нечётное > 0 — подстановка w = cos v:  −∫ (1−w²)^((m−1)/2) wⁿ dw;  n нечётное > 0 — w = sin v;
;   m, n чётные ≥ 2 — понижение степени через двойной угол (sin² = (1−cos 2v)/2, cos² = (1+cos 2v)/2);
;   m + n чётно, одна из степеней отрицательна (tanᵏ, secᵏ·tanʲ) — подстановка w = tan v: wᵐ (1+w²)^(−(m+n)/2−1) dw;
;   m чётное ≥ 2 и n < 0 (и симметрично) — sin² = 1 − cos², сводится к степеням одной функции.
; Упрощатель переводит tan/cot/sec/csc в sin/cos, поэтому разбираем именно эту форму.

(define (int-even? k) (= (mod k 2) 0))
(define (int-odd? k) (not (int-even? k)))

; ∫ cos^n v dv
(define (int-cos-pow n v)
  (cond ((= n 0) v)
        ((= n 1) (list 'sin v))
        ((= n -1) (list 'log (list '* (list '+ 1 (list 'sin v)) (list '^ (list 'cos v) -1))))
        ((> n 1) (list '+ (list '* (/ 1 n) (list 'sin v) (list '^ (list 'cos v) (- n 1)))
                       (list '* (/ (- n 1) n) (int-cos-pow (- n 2) v))))
        (else (list '+ (list '* (/ (+ n 2) (+ n 1)) (int-cos-pow (+ n 2) v))
                    (list '* (/ -1 (+ n 1)) (list 'sin v) (list '^ (list 'cos v) (+ n 1)))))))

; ∫ sin^n v dv
(define (int-sin-pow n v)
  (cond ((= n 0) v)
        ((= n 1) (list '* -1 (list 'cos v)))
        ((= n -1) (list 'log (list '* (list '+ 1 (list '* -1 (list 'cos v))) (list '^ (list 'sin v) -1))))
        ((> n 1) (list '+ (list '* (/ -1 n) (list '^ (list 'sin v) (- n 1)) (list 'cos v))
                       (list '* (/ (- n 1) n) (int-sin-pow (- n 2) v))))
        (else (list '+ (list '* (/ (+ n 2) (+ n 1)) (int-sin-pow (+ n 2) v))
                    (list '* (/ 1 (+ n 1)) (list '^ (list 'sin v) (+ n 1)) (list 'cos v))))))

; многочлен (1 − w²)^j · w^k, раскрытый и с w → f (степени одной функции)
(define (int-pyth-expand j k w f)
  (replace-expr (expand (simplify (list '* (list '^ (list '+ 1 (list '* -1 (list '^ w 2))) j) (list '^ w k)))) w f))

; ∫ sin^m v · cos^n v dv; w — свежая переменная для подстановок
(define (int-trig-core v m n d)
  (let ((w (int-uvar (+ d 1))))
    (cond ((= n 0) (int-sin-pow m v))
          ((= m 0) (int-cos-pow n v))
          ((and (> m 0) (int-odd? m))
           (let ((r (int-go (simplify (list '* -1 (list '^ (list '+ 1 (list '* -1 (list '^ w 2))) (/ (- m 1) 2)) (list '^ w n)))
                            w (+ d 1))))
             (and r (replace-expr r w (list 'cos v)))))
          ((and (> n 0) (int-odd? n))
           (let ((r (int-go (simplify (list '* (list '^ w m) (list '^ (list '+ 1 (list '* -1 (list '^ w 2))) (/ (- n 1) 2))))
                            w (+ d 1))))
             (and r (replace-expr r w (list 'sin v)))))
          ((and (> m 0) (> n 0) (int-even? m) (int-even? n))
           (int-go (expand (simplify (list '* (list '^ (list '* 1/2 (list '+ 1 (list '* -1 (list 'cos (list '* 2 v))))) (/ m 2))
                                           (list '^ (list '* 1/2 (list '+ 1 (list 'cos (list '* 2 v)))) (/ n 2)))))
                   v (+ d 1)))
          ((and (int-even? (+ m n)) (or (< m 0) (< n 0)))
           (let ((r (int-go (simplify (list '* (list '^ w m) (list '^ (list '+ 1 (list '^ w 2)) (- (- 0 (/ (+ m n) 2)) 1)))) w (+ d 1))))
             ; atan(tan v) = v (на главной ветви) — убираем, чтобы ответ не содержал atan(sin/cos)
             (and r (replace-expr (replace-expr r (list 'atan w) v) w (list '* (list 'sin v) (list '^ (list 'cos v) -1))))))
          ((and (> m 0) (int-even? m) (< n 0))
           (int-go (int-pyth-expand (/ m 2) n w (list 'cos v)) v (+ d 1)))
          ((and (> n 0) (int-even? n) (< m 0))
           (int-go (int-pyth-expand (/ n 2) m w (list 'sin v)) v (+ d 1)))
          (else #f))))

(define (int-trig-factor f)
  (cond ((and (op-expr? f) (member? (car f) '(sin cos)) (= (length f) 2)) (list (car f) (cadr f) 1))
        ((and (op-expr? f) (equal? (car f) '^) (integer? (caddr f))
              (op-expr? (cadr f)) (member? (car (cadr f)) '(sin cos)) (= (length (cadr f)) 2))
         (list (car (cadr f)) (cadr (cadr f)) (caddr f)))
        (else #f)))

; e → (u m n) или #f
(define (int-trig-parse e)
  (let* ((fs (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))
         (ps (map int-trig-factor fs)))
    (and (every? (lambda (p) p) ps)
         (let ((u (cadr (car ps))))
           (and (every? (lambda (p) (equal? (cadr p) u)) ps)
                (list u
                      (foldl (lambda (acc p) (if (equal? (car p) 'sin) (+ acc (caddr p)) acc)) 0 ps)
                      (foldl (lambda (acc p) (if (equal? (car p) 'cos) (+ acc (caddr p)) acc)) 0 ps)))))))

; Шаг S.3: приём для степеней (m, n) аргумента u — пояснение шага int-trig-powers (только при включённом журнале)
(define (int-trig-hint p x d)
  (let* ((u (car p)) (m (cadr p)) (n (caddr p)) (us (int-mp u))
         (w (int-mp (int-uvar (+ d 1))))
         (lin (if (equal? u x) "" (string-append "; аргумент линейный: u = " us ", dx = du/a")))
         (how (cond ((= n 0) (string-append "формула понижения степени: ∫ sin^m u du = −sin^(m−1)u·cos u/m + (m−1)/m·∫ sin^(m−2)u du, m = " (to-string m)))
                    ((= m 0) (string-append "формула понижения степени: ∫ cos^n u du = cos^(n−1)u·sin u/n + (n−1)/n·∫ cos^(n−2)u du, n = " (to-string n)))
                    ((and (> m 0) (int-odd? m))
                     (string-append "нечётная степень синуса: sin^m = sin·(1 − cos²)^k, подстановка " w " = cos(" us ")"))
                    ((and (> n 0) (int-odd? n))
                     (string-append "нечётная степень косинуса: cos^n = cos·(1 − sin²)^k, подстановка " w " = sin(" us ")"))
                    ((and (> m 0) (> n 0) (int-even? m) (int-even? n))
                     "обе степени чётные: понижаем степень, sin²u = (1 − cos 2u)/2, cos²u = (1 + cos 2u)/2")
                    ((and (int-even? (+ m n)) (or (< m 0) (< n 0)))
                     (string-append "подстановка " w " = tan(" us "): sin^m·cos^n du = w^m·(1 + w²)^(−(m+n)/2 − 1) dw"))
                    (else "чётная степень при отрицательной другой: sin² = 1 − cos² (или cos² = 1 − sin²) сводит к степеням одной функции"))))
    (string-append how lin)))

(define (int-trig e x d)
  (let ((p (and (< d int-max-depth) (int-trig-parse e))))
    (and p
         (let ((a (int-slope (car p) x)))
           (and a
                (with-step ('int-trig-powers "Степени синуса и косинуса" (int-form e x)
                            :comment (lambda (r) (int-trig-hint p x d)) :after int-p)
                  (let* ((v (if (equal? (car p) x) x (int-uvar d))) (r (int-trig-core v (cadr p) (caddr p) d)))
                    (if r (simplify (list '* (list '^ a -1) (replace-expr r v (car p)))) (begin (attempt-fail "степени sin и cos не сводятся к табличным") #f)))))))))

(int-add-strategy int-trig)

; ---------- корни квадратного трёхчлена ----------
; (B·x + C) / sqrt(Q) и sqrt(Q), Q = a·x² + b·x + c (a — число, b, c — без x). Q = a·U² + r, U = x + b/(2a):
;   ∫ (B·x+C)/√Q = (B/a)·√Q + (C − B·b/(2a))·J,   J = ∫ dx/√Q:
;       a > 0:  J = a^(−1/2) · log(U + √(Q/a));   a < 0 (K = r/(−a) > 0):  J = |a|^(−1/2) · asin(U/√K)
;   ∫ √Q:  a > 0:  ½·(U·√Q + (r/a)·√a·log(U + √(Q/a)));   a < 0:  ½·(U·√Q + K·√|a|·asin(U/√K))
; Нечисловой K считается положительным (параметры положительны). Простые случаи (a=±1, b=0) ловит таблица.

(define (int-quad-form Q x)
  (and (op-expr? Q) (polynomial? Q x) (equal? (degree Q x) 2)
       (let ((a (coeff Q x 2)))
         (and (real-numeric? a) (list a (coeff Q x 1) (coeff Q x 0))))))

; e → (N Q p) (N — многочлен степени ≤ 1 по x, p = ±1/2) или #f
(define (int-sqrt-parse e x)
  (let ((fs (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e))))
    (let ((rs (filter (lambda (f) (and (op-expr? f) (equal? (car f) '^) (member? (caddr f) '(1/2 -1/2))
                                       (int-quad-form (cadr f) x)))
                      fs)))
      (and (= (length rs) 1)
           (let ((N (simplify (cons '* (cons 1 (filter (lambda (f) (not (equal? f (car rs)))) fs))))))
             (and (polynomial? N x) (<= (degree N x) 1)
                  (or (equal? (caddr (car rs)) -1/2) (x-free? N x))
                  (list N (cadr (car rs)) (caddr (car rs)))))))))

; ∫ (B·x + C) / √Q, J = ∫ dx/√Q
(define (int-sqrt-inv N sQ J a b x)
  (let ((B (coeff N x 1)) (C (coeff N x 0)))
    (simplify (list '+ (list '* B (list '^ a -1) sQ)
                    (list '* (list '+ C (list '* -1 B b (list '^ (* 2 a) -1))) J)))))

(define (int-sqrt-quad-solve N Q pw x)
  (let* ((f (int-quad-form Q x)) (a (car f)) (b (cadr f)) (c (caddr f))
         (pos (> a 0))
         (h (simplify (list '* b (list '^ (* 2 a) -1))))
         (r (simplify (list '+ c (list '* -1 (list '^ b 2) (list '^ (* 4 a) -1)))))
         (U (simplify (list '+ x h)))
         (sQ (list '^ Q 1/2))
         (K (simplify (list '* r (list '^ (if pos a (- 0 a)) -1))))
         (logt (list 'log (list '+ U (list '^ (list '* Q (list '^ a -1)) 1/2))))
         (asint (list 'asin (list '* U (int-inv-sqrt K)))))
    (and (not (equal? r 0))
         (or pos (not (real-numeric? K)) (> K 0))
         (let ((J (if pos (list '* (int-inv-sqrt a) logt) (list '* (int-inv-sqrt (- 0 a)) asint))))
           (if (equal? pw -1/2)
               (int-sqrt-inv N sQ J a b x)
               (simplify (list '* N 1/2
                               (list '+ (list '* U sQ)
                                     (list '* K (if pos (list '* (int-sqrt a) logt) (list '* (int-sqrt (- 0 a)) asint)))))))))))

(define (int-sqrt-quad e x d)
  (let ((p (int-sqrt-parse e x)))
    (and p
         (with-step ('int-sqrt-quad "Интеграл с корнем из квадратного трёхчлена" (int-form e x)
                     :comment "выделяем полный квадрат Q = a·U² + r; ∫ dx/√Q = log(U + √(Q/a))/√a при a > 0, asin(U/√K)/√|a| при a < 0 (K = r/|a|); ∫ √Q dx и ∫ (B·x + C)/√Q dx сводятся к ней"
                     :after int-p)
           (let ((r (int-sqrt-quad-solve (car p) (cadr p) (caddr p) x))) (if r r (begin (attempt-fail "корень не приводится к табличному (r = 0 или K < 0)") #f)))))))

(int-add-strategy int-sqrt-quad)

; ---------- произведения sin/cos разных аргументов: преобразование в сумму ----------
; sin A·cos B = ½[sin(A+B) + sin(A−B)], sin A·sin B = ½[cos(A−B) − cos(A+B)], cos A·cos B = ½[cos(A−B) + cos(A+B)]
(define (int-sc-factor f)
  (and (op-expr? f) (member? (car f) '(sin cos)) (= (length f) 2) (list (car f) (cadr f))))

(define (int-prodsum-expr kp kq A B)
  (let ((sum (list '+ A B)) (dif (list '+ A (list '* -1 B))))
    (cond ((and (equal? kp 'sin) (equal? kq 'cos)) (list '* 1/2 (list '+ (list 'sin sum) (list 'sin dif))))
          ((and (equal? kp 'cos) (equal? kq 'sin)) (list '* 1/2 (list '+ (list 'sin sum) (list 'sin (list '* -1 dif)))))
          ((and (equal? kp 'sin) (equal? kq 'sin)) (list '* 1/2 (list '+ (list 'cos dif) (list '* -1 (list 'cos sum)))))
          (else (list '* 1/2 (list '+ (list 'cos dif) (list 'cos sum)))))))

(define (int-prodsum e x d)
  (and (< d int-max-depth) (op-expr? e) (equal? (car e) '*) (= (length e) 3)
       (let ((p (int-sc-factor (cadr e))) (q (int-sc-factor (caddr e))))
         (and p q (not (equal? (cadr p) (cadr q)))
              (with-step ('int-trig-product "Произведение синусов и косинусов" (int-form e x)
                          :comment "sin A·cos B = ½[sin(A+B) + sin(A−B)], sin A·sin B = ½[cos(A−B) − cos(A+B)], cos A·cos B = ½[cos(A−B) + cos(A+B)]"
                          :after int-p)
                (let ((s (simplify (int-prodsum-expr (car p) (car q) (cadr p) (cadr q)))))
                  (if (step-log-enabled?)
                      (record-step 'int-product-to-sum "Преобразование произведения в сумму" "" (int-form e x) (int-form s x)))
                  (let ((r (int-go s x (+ d 1)))) (if r r (begin (attempt-fail "преобразованная сумма не интегрируется") #f)))))))))

(int-add-strategy int-prodsum)

; Произведение с ≥ 2 тригонометрическими множителями (sin/cos линейных аргументов, возможно в квадрате) и прочими
; множителями (exp, многочлен): sin²A = (1 − cos 2A)/2, cos²A = (1 + cos 2A)/2, sin A·cos B → сумма (как int-prodsum),
; затем раскрытие и каскад. Без этого по-частям/Риш на sin²x·cos 3x, eˣ·sin x·cos 2x уходили на 15 с – минуты.
(define (int-sq-factor f)
  (and (op-expr? f) (equal? (car f) '^) (= (length f) 3) (equal? (caddr f) 2)
       (int-sc-factor (cadr f))))

(define (int-trig-factor? f) (or (int-sc-factor f) (int-sq-factor f)))

(define (int-prodsum-sq e x d)
  (and (< d int-max-depth) (op-expr? e) (equal? (car e) '*)
       (let* ((ts (filter int-trig-factor? (cdr e)))
              (sq (filter int-sq-factor ts)))
         (and (or (> (length ts) 1) (pair? sq))
              (let* ((pick
                      (if (pair? sq)
                          (let* ((f (car sq)) (p (int-sq-factor f)) (A (cadr p)) (c2 (list 'cos (list '* 2 A))))
                            (list (list f) (list '* 1/2 (list '+ 1 (if (equal? (car p) 'sin) (list '* -1 c2) c2)))))
                          (let ((a (car ts)))
                            (let ((b (let ((l (filter (lambda (f) (not (equal? (cadr f) (cadr a)))) (cdr ts)))) (and (pair? l) (car l)))))
                              (and b (list (list a b) (int-prodsum-expr (car a) (car b) (cadr a) (cadr b)))))))))
                (and pick
                     (let* ((used (car pick))
                            (rest (foldl (lambda (l u) (int-remove-first u l)) (cdr e) used))
                            (ex (expand (cons '* (cons (cadr pick) rest)))))
                       (and (not (equal? ex e))
                            (with-step ('int-trig-product "Произведение синусов и косинусов" (int-form e x)
                                        :comment "sin²A = (1 − cos 2A)/2, cos²A = (1 + cos 2A)/2, sin A·cos B = ½[sin(A+B) + sin(A−B)] …; раскрываем скобки и интегрируем сумму"
                                        :after int-p)
                              (let ((r (int-go ex x (+ d 1)))) (if r r (begin (attempt-fail "сумма после преобразования произведения не интегрируется") #f))))))))))))

(int-add-strategy int-prodsum-sq)

; ---------- дробные степени tan / cot (шаг INT.TQ) ----------
; e = Q(tan x, tan(x)^(1/q)): sin → t·c, cos → c (c — свежий символ), после упрощения остаются только чётные степени c
; (c² = 1/(1+t²)); dx = dt/(1+t²); t = u^q — рациональная (или иная табличная) задача по u; ответ: u → tan(x)^(1/q).
; Быстрый отказ: нужны дробная степень и тригонометрия от x; любой иной x, нечётный c или радикал не от t — #f.

(define tq-t '%tqt)
(define tq-c '%tqc)

(define (tq-frac? r) (and (number? r) (equal? (type-of r) 'rational)))

(define (tq-scan e x)
  (cond ((not (op-expr? e)) '(#f . #f))
        (else (let* ((rs (map (lambda (a) (tq-scan a x)) (cdr e)))
                     (rad (or (equal? (car e) 'sqrt)
                              (and (equal? (car e) '^) (= (length e) 3) (tq-frac? (caddr e)))
                              (any? car rs)))
                     (trg (or (and (member? (car e) '(sin cos tan cot sec csc)) (= (length e) 2) (equal? (cadr e) x))
                              (any? cdr rs))))
                (cons rad trg)))))

(define (tq-conv e x)
  (cond ((equal? e x) (raise 'tq-no))
        ((not (op-expr? e)) e)
        ((and (member? (car e) '(sin cos tan cot sec csc)) (= (length e) 2) (equal? (cadr e) x))
         (case (car e)
           ((sin) (list '* tq-t tq-c))
           ((cos) tq-c)
           ((tan) tq-t)
           ((cot) (list '^ tq-t -1))
           ((sec) (list '^ tq-c -1))
           (else (list '^ (list '* tq-t tq-c) -1))))
        (else (cons (car e) (map (lambda (a) (tq-conv a x)) (cdr e))))))

; c^(2k) → (1 + t²)^(−k); нечётная степень или голое c — отказ
(define (tq-cpow g)
  (cond ((equal? g tq-c) (raise 'tq-no))
        ((not (op-expr? g)) g)
        ((and (equal? (car g) '^) (= (length g) 3) (equal? (cadr g) tq-c))
         (if (and (integer? (caddr g)) (int-even? (caddr g)))
             (list '^ (list '+ 1 (list '^ tq-t 2)) (/ (caddr g) -2))
             (raise 'tq-no)))
        (else (cons (car g) (map tq-cpow (cdr g))))))

; sqrt A → A^(1/2); (t^k)^r → t^(k·r) (k целое): sqrt(cot x) = sqrt(t^(−1)) = t^(−1/2)
(define (tq-norm h)
  (cond ((not (op-expr? h)) h)
        ((and (equal? (car h) 'sqrt) (= (length h) 2)) (tq-norm (list '^ (cadr h) 1/2)))
        ((and (equal? (car h) '^) (= (length h) 3) (number? (caddr h))
              (op-expr? (cadr h)) (equal? (car (cadr h)) '^) (= (length (cadr h)) 3)
              (equal? (cadr (cadr h)) tq-t) (integer? (caddr (cadr h))))
         (list '^ tq-t (* (caddr (cadr h)) (caddr h))))
        (else (cons (car h) (map tq-norm (cdr h))))))

; q — общий знаменатель показателей степеней t; радикал не от t — отказ
(define (tq-order h)
  (cond ((not (op-expr? h)) 1)
        ((and (equal? (car h) 'sqrt) (equal? (cadr h) tq-t)) 2)
        ((equal? (car h) 'sqrt) (raise 'tq-no))
        ((and (equal? (car h) '^) (= (length h) 3) (tq-frac? (caddr h)))
         (if (equal? (cadr h) tq-t) (denom (caddr h)) (raise 'tq-no)))
        (else (foldl (lambda (a x) (lcm a (tq-order x))) 1 (cdr h)))))

(define (tq-sub h q u)
  (cond ((equal? h tq-t) (list '^ u q))
        ((not (op-expr? h)) h)
        ((and (equal? (car h) 'sqrt) (equal? (cadr h) tq-t)) (list '^ u (/ q 2)))
        ((and (equal? (car h) '^) (= (length h) 3) (equal? (cadr h) tq-t) (number? (caddr h)))
         (list '^ u (* q (caddr h))))
        (else (cons (car h) (map (lambda (a) (tq-sub a q u)) (cdr h))))))

(define (int-tan-pow e x d)
  (and (= d 0) (op-expr? e)
       (let ((s (tq-scan e x)))
         (and (car s) (cdr s)
              (let ((plan (try (let* ((g (tq-cpow (simplify (tq-conv e x))))
                                      (h (tq-norm (simplify (list '* g (list '^ (list '+ 1 (list '^ tq-t 2)) -1)))))
                                      (q (tq-order h)))
                                 (and (> q 1) (not (contains-sym? h x)) (list h q)))
                               (lambda (err) #f))))
                (and plan
                     (let* ((q (cadr plan)) (u (int-uvar (+ d 1)))
                            (h2 (simplify (list '* (tq-sub (car plan) q u) q (list '^ u (- q 1))))))
                       (with-step ('int-tan-pow "Дробная степень tan x" (int-form e x)
                                   :comment (lambda (r) (string-append "подстановка t = tan x, dx = dt/(1 + t²), затем u = t^(1/" (to-string q) ")"))
                                   :after int-p)
                         (let ((r (int-go h2 u (+ d 1))))
                           (if (and r (not (int-has-integrate? r)) (not (contains-sym? r tq-t)))
                               (simplify (replace-expr r u (list '^ (list '* (list 'sin x) (list '^ (list 'cos x) -1)) (/ 1 q))))
                               (begin (attempt-fail "после подстановки tan x = u^q интеграл не берётся") #f)))))))))))

(int-add-strategy int-tan-pow)


; ---------- INT.DEF2: 1/(a·sin u + b·cos u + c), корни знаменателя после t = tan(u/2) иррациональны ----------
; Универсальная подстановка t = tan(u/2): sin u = 2t/(1+t²), cos u = (1−t²)/(1+t²), du = 2dt/(1+t²); знаменатель
; становится (A t² + 2B t + C)/(1+t²) с A = c − b, B = a, C = c + b, D = B² − A·C = a² + b² − c². При D > 0 и иррациональном √D
; (Риш над ℚ(x) здесь не берёт логарифмы с √D): ∫ 2dt/(A t²+2B t+C) = (1/√D)·log|(A t + B − √D)/(A t + B + √D)|, модуль — как
; ½·log(·²), чтобы ответ был вещественным. Только рациональные a, b, c, линейный u; ответ проходит int-check.
(define (int-trl-ratp v) (or (integer? v) (equal? (type-of v) (quote rational))))

; слагаемое знаменателя → (sin|cos|c аргумент коэффициент) или #f
(define (int-trl-term t x)
  (if (x-free? t x)
      (list (quote c) #f t)
      (let* ((fs (if (and (op-expr? t) (equal? (car t) (quote *))) (cdr t) (list t)))
             (tr (filter (lambda (f) (not (x-free? f x))) fs)))
        (and (= (length tr) 1) (op-expr? (car tr)) (member? (car (car tr)) (quote (sin cos))) (= (length (car tr)) 2)
             (list (car (car tr)) (cadr (car tr)) (simplify (cons (quote *) (filter (lambda (f) (x-free? f x)) fs))))))))

(define (int-trl-sum ps kind)
  (simplify (cons (quote +) (map caddr (filter (lambda (p) (equal? (car p) kind)) ps)))))

(define (int-trl-build nu w k a b c x)
  (let* ((D (+ (* a a) (* b b) (* -1 c c))) (A (- c b)) (B a))
    (and (> D 0) (not (= A 0))
         (let ((sq (simplify (list (quote ^) D 1/2))))
           (and (not (int-trl-ratp sq))
                (let* ((t (list (quote tan) (list (quote *) 1/2 w)))
                       (u (list (quote /) (list (quote +) (list (quote *) A t) B (list (quote *) -1 sq))
                                (list (quote +) (list (quote *) A t) B sq))))
                  (simplify (list (quote *) nu (list (quote ^) (list (quote *) 2 k sq) -1) (list (quote log) (list (quote ^) u 2))))))))))

(define (int-trig-lin e x d)
  (and (< d int-max-depth) (op-expr? e)
       (let* ((tg (try (together e) (lambda (er) #f)))
              (nu (and tg (numer tg))) (de (and tg (denom tg))))
         (and nu de (x-free? nu x) (not (x-free? de x))
              (let* ((ts (if (and (op-expr? de) (equal? (car de) (quote +))) (cdr de) (list de)))
                     (ps (map (lambda (t) (int-trl-term t x)) ts)))
                (and (every? (lambda (p) p) ps)
                     (let ((trs (filter (lambda (p) (not (equal? (car p) (quote c)))) ps)))
                       (and (pair? trs)
                            (let* ((w (cadr (car trs))) (k (int-slope w x)))
                              (and k (int-trl-ratp k) (every? (lambda (p) (equal? (cadr p) w)) trs)
                                   (let ((a (int-trl-sum ps (quote sin))) (b (int-trl-sum ps (quote cos))) (c (int-trl-sum ps (quote c))))
                                     (and (int-trl-ratp a) (int-trl-ratp b) (int-trl-ratp c)
                                          (let ((r (int-trl-build nu w k a b c x)))
                                            (and r (int-check r e x)
                                                 (with-step ((quote int-substitution) "Универсальная тригонометрическая подстановка" (int-form e x)
                                                             :comment "t = tan(u/2): sin u = 2t/(1+t²), cos u = (1−t²)/(1+t²), интеграл — рациональный с вещественными иррациональными корнями, логарифм с √D"
                                                             :after int-p)
                                                   r)))))))))))))))

(int-add-strategy int-trig-lin)
