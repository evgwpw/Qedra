; integrate/rational.lisp — интегрирование рациональных функций (часть бывшего lib\integrate.lisp, шаг 21h')
; Простейшие дроби (int-rational) и запасной путь Эрмит + Лазар–Риобу–Трагер (int-rational-lrt); регистрирует
; стратегии int-linear, int-rational, int-rational-lrt, int-usub (порядок регистрации = порядок каскада).
; Загружается после integrate/core.lisp.
(module integrate)

; ---------- рациональные функции (простейшие дроби) ----------
; e = P/Q от x (коэффициенты — рациональные числа и параметры): (apart e x) даёт целую часть и дроби N/D^k,
; D — неприводимый над ℤ линейный или квадратичный множитель (D степени ≥ 3 → #f: Ротштейн–Трагер вне рамок).
;   D линейный:   N/(d1·(…)) · log D  или  N/(d1(1−k)) · D^(1−k)
;   D квадратный: выделение полного квадрата D = p2·(U² + δ), U = x + p1/(2p2), δ = (4p2p0 − p1²)/(4p2²);
;     числитель B·x + C = B·U + C';  ∫ U/Qᵏ — log / степень;  ∫ 1/Qᵏ = Iₖ — рекуррентная формула понижения:
;     I₁ = atan(U/√δ)/√δ (δ > 0; для нечислового δ — тоже) или log((U−s)/(U+s))/(2s), s = √−δ (δ < 0);
;     I_{j+1} = U/(2jδ·Qʲ) + (2j−1)/(2jδ) · I_j.
; Символьные параметры допускаются, если apart их разложил (иначе — один «терм» с несколькими множителями → #f).

(define (int-rational? e x)
  (try (let ((tg (together e)))
         (and (polynomial? (numer tg) x) (polynomial? (denom tg) x)))
       (lambda (err) #f)))

; ∫ многочлена по x (коэффициенты могут содержать параметры)
(define (int-poly-integral p x)
  (let ((cs (coefficients p x)))
    (simplify (cons '+ (map2 (lambda (c k) (list '* c (list '^ (+ k 1) -1) (list '^ x (+ k 1))))
                             cs (range (length cs)))))))

; √r и 1/√r для рационального r > 0 с рационализацией: √(p/q) = √(pq)/q (иначе simplify оставляет (3/4)^(1/2))
(define (int-sqrt r)
  (if (and (real-numeric? r) (rational-number? r))
      (list '* (list '^ (* (numer r) (denom r)) 1/2) (list '^ (denom r) -1))
      (list '^ r 1/2)))
(define (int-inv-sqrt r)
  (if (and (real-numeric? r) (rational-number? r))
      (list '* (list '^ (* (numer r) (denom r)) 1/2) (list '^ (numer r) -1))
      (list '^ r -1/2)))

(define (int-quad-I1 U delta)
  (if (and (real-numeric? delta) (< delta 0))
      (let ((s (int-sqrt (simplify (list '* -1 delta)))))
        (list '* 1/2 (list '^ s -1)
              (list 'log (list '* (list '+ U (list '* -1 s)) (list '^ (list '+ U s) -1)))))
      (list '* (int-inv-sqrt delta) (list 'atan (list '* U (int-inv-sqrt delta))))))

(define (int-quad-I-loop j k acc U delta Q)
  (if (>= j k)
      acc
      (let ((den (list '* 2 j delta)))
        (int-quad-I-loop (+ j 1) k
                         (list '+ (list '* U (list '^ den -1) (list '^ Q (- 0 j)))
                               (list '* (- (* 2 j) 1) (list '^ den -1) acc))
                         U delta Q))))

; ∫ (B·x + C) / (cst · D^k) dx для неприводимого квадратного D = p2 x² + p1 x + p0
(define (int-rat-quad B C D k cst x)
  (let* ((p2 (coeff D x 2)) (p1 (coeff D x 1)) (p0 (coeff D x 0))
         (h (simplify (list '* p1 (list '^ (list '* 2 p2) -1))))
         (delta (simplify (list '* (list '+ (list '* 4 p2 p0) (list '* -1 (list '^ p1 2)))
                                (list '^ (list '* 4 (list '^ p2 2)) -1))))
         (U (simplify (list '+ x h)))
         (Cp (simplify (list '+ C (list '* -1 B h))))
         (Q (list '* D (list '^ p2 -1)))
         (Jk (if (= k 1)
                 (list '* 1/2 (list 'log D))
                 (list '* -1/2 (list '^ (- k 1) -1) (list '^ p2 (- k 1)) (list '^ D (- 1 k)))))
         (Ik (int-quad-I-loop 1 k (int-quad-I1 U delta) U delta Q)))
    (simplify (list '* (list '^ (list '* cst (list '^ p2 k)) -1)
                    (list '+ (list '* B Jk) (list '* Cp Ik))))))

; ∫ n / (cst · D^k) dx
(define (int-rat-power n D k cst x)
  (let ((dd (degree D x)))
    (cond ((and (equal? dd 1) (x-free? n x))
           (let ((d1 (coeff D x 1)))
             (if (= k 1)
                 (simplify (list '* n (list '^ (list '* cst d1) -1) (list 'log D)))
                 (simplify (list '* n (list '^ (list '* cst d1 (- 1 k)) -1) (list '^ D (- 1 k)))))))
          ((and (equal? dd 2) (integer? (degree n x)) (<= (degree n x) 1))
           (int-rat-quad (coeff n x 1) (coeff n x 0) D k cst x))
          ((and (equal? dd 2) (x-free? n x)) (int-rat-quad 0 n D k cst x))
          (else #f))))

; один терм простейшей дроби: многочлен или N/(c·D^k)
(define (int-rat-term t x)
  (let* ((tg (together t)) (n (numer tg)) (dn (denom tg)))
    (if (x-free? dn x)
        (int-poly-integral (simplify (list '* n (list '^ dn -1))) x)
        (let* ((fl (factor-list dn)) (fs (cdr fl))
               (xs (filter (lambda (f) (not (x-free? (car f) x))) fs))
               (cs (filter (lambda (f) (x-free? (car f) x)) fs)))
          (and (= (length xs) 1)
               (int-rat-power n (car (car xs)) (cadr (car xs))
                              (simplify (cons '* (cons (car fl) (map (lambda (f) (list '^ (car f) (cadr f))) cs))))
                              x))))))

; Шаг S.3: пояснение к интегралу слагаемого простейшей дроби (только при включённом журнале)
(define (int-term-hint t x)
  (let* ((tg (together t)) (dn (denom tg)))
    (if (x-free? dn x)
        "многочлен: ∫ xⁿ dx = xⁿ⁺¹/(n+1) почленно"
        (let* ((fs (cdr (factor-list dn))) (xs (filter (lambda (f) (not (x-free? (car f) x))) fs)))
          (if (not (= (length xs) 1))
              ""
              (let ((D (car (car xs))) (k (cadr (car xs))))
                (cond ((equal? (degree D x) 1)
                       (if (= k 1)
                           (string-append "знаменатель линейный: ∫ dx/(a·x + b) = log(a·x + b)/a, здесь a·x + b = " (int-mp D))
                           (string-append "знаменатель — степень линейного: ∫ dx/(a·x + b)^k = (a·x + b)^(1−k)/(a·(1−k)), здесь a·x + b = "
                                          (int-mp D) ", k = " (to-string k))))
                      ((equal? (degree D x) 2)
                       (string-append "знаменатель — неприводимый квадратный трёхчлен " (int-mp D)
                                      ": выделяем полный квадрат, ∫ dx/(U² + δ) = atan(U/√δ)/√δ"
                                      (if (= k 1) "" (string-append "; степень k = " (to-string k) " — рекуррентная формула понижения"))))
                      (else ""))))))))

(define (int-rat-term-step t x)
  (with-step ('int-partial-fraction-term "Интеграл слагаемого" (int-form t x)
              :comment (lambda (r) (int-guard (lambda () (int-term-hint t x)))) :after int-p)
    (let ((r (int-rat-term t x)))
      (if r r (begin (attempt-fail "знаменатель не разложен на линейные и квадратные множители") #f)))))

(define (int-rational e x d)
  (and (int-rational? e x)
       (let* ((a (apart e x))
              (terms (if (and (op-expr? a) (equal? (car a) '+)) (cdr a) (list a))))
         (with-step ('int-partial-fractions "Разложение на простые дроби" (int-form e x)
                     :comment "раскладываем дробь на простейшие и интегрируем каждое слагаемое отдельно" :after int-p)
           (begin
             (if (and (step-log-enabled?) (not (equal? a (simplify e))))
                 (record-step 'apart "Разложение на простейшие дроби" "" (int-p e) (int-p a)))
             (let ((rs (map (lambda (t) (int-rat-term-step t x)) terms)))
               (if (every? (lambda (r) r) rs) (simplify (cons '+ rs)) (begin (attempt-fail "слагаемое простейшей дроби не интегрируется") #f))))))))

; ---------- рациональные функции: Эрмит + Лазар–Риобу–Трагер (Шаг 21h) ----------
; Запасной путь для всего, с чем не справился int-rational: множители знаменателя степени ≥ 3, несколько параметров.
; Любая рациональная функция от x над ℚ(параметры) интегрируется (builtin rat-integrate-log, src\RatIntExpr.fs):
;   деление с остатком → многочлен; редукция Эрмита (Мак) → рациональная часть; ЛРТ → Σ_{Q_i(t)=0} t·log S_i(t, x);
;   Q_i раскладывается над ℚ(параметры): линейные множители — a·log S(a, x); квадратные — вещественная форма (атаны от
;   многочленов, Риобу: без разрывов на ℝ) или корни в радикалах; степень ≥ 3 — (root-sum t Q E) (комплексная форма).
; Вещественная форма — если все параметры объявлены вещественными (domain.lisp; необъявленный символ — элемент ℂ).
; Ответ проверяется дифференцированием (int-check): не прошёл проверку — стратегия возвращает #f (это баг, тест упадёт).

(define (int-all-real? e x)
  (every? (lambda (s) (true? (real? s))) (int-symbols e x)))

; свободный от e символ — связанная переменная сумм по корням
(define (int-fresh-t e x)
  (let ((used (cons x (int-symbols e x))))
    (int-first (lambda (s) (if (member? s used) #f s)) '(t s u v w tt t1 t2 t3 t4))))

; Проверка дифференцированием. Структура ответа (Эрмит + ЛРТ + суммы по корням) уже проверена builtin'ом ТОЧНО (в рациональных
; точках, арифметикой ℚ[t]/(f) — исключение при несовпадении); здесь — численная проверка итогового выражения (производная
; в точках, отличных от точек builtin; суммы по корням в производной eval-num считает точно — рациональной арифметикой по модулю Q);
; точная проверка simplify/together — запасной путь (на больших выражениях она дорога).
(define (int-check-lrt F e x)
  (let* ((se (simplify e)) (dfe (list '- (int-diff x F) se))
         ; сумма по корням: точное вычисление в ℚ[t]/(Q) дорого при большой степени Q — две точки (builtin уже проверил точно)
         (pts (if (null? (int-rootsums F)) int-test-points (take int-test-points 2))))
    (or (int-numeric-zero-at? dfe se x 0.0000001 pts)
        (int-check F e x))))

; Шаг S.3: слагаемое ответа — логарифмическая часть (log, atan, сумма по корням)
(define (int-log-part? t)
  (cond ((not (op-expr? t)) #f)
        ((member? (car t) '(log atan root-sum)) #t)
        (else (any? int-log-part? (cdr t)))))

; шаги «Эрмит» (рациональная часть R) и «ЛРТ» (логарифмическая часть L): ∫ e = R + ∫ rem, rem = e − R', ∫ rem = L.
; Ответ F уже получен и проверен; здесь только описание его частей (при включённом журнале, ошибки не мешают)
(define (int-lrt-notes e x F)
  (int-guard
   (lambda ()
     (let* ((terms (if (and (op-expr? F) (equal? (car F) '+)) (cdr F) (list F)))
            (logs (filter int-log-part? terms))
            (rats (filter (lambda (t) (not (int-log-part? t))) terms))
            (hermite "редукция Эрмита: ∫ P/Q dx = A/B + ∫ C/D dx, у D нет кратных множителей; A/B — рациональная часть ответа")
            (lrt (string-append "метод Лазара–Риобу–Трагера: логарифмическая часть — сумма t·log S(t, x) по корням t резольвенты"
                                (if (any? (lambda (t) (contains-sym? t 'root-sum)) logs)
                                    "; корни не выражаются в радикалах — остаётся сумма по корням rootsum"
                                    ""))))
       (cond ((null? logs)
              (record-step 'int-rational-hermite "Метод Эрмита: рациональная часть" hermite (int-form e x) (int-p F)))
             ((null? rats)
              (record-step 'int-rational-lrt "Метод Лазара–Риобу–Трагера: логарифмическая часть" lrt (int-form e x) (int-p F)))
             (else
              (let* ((R (simplify (cons '+ rats))) (L (simplify (cons '+ logs)))
                     (rm (together (list '+ e (list '* -1 (int-diff x R))))))
                (record-step 'int-rational-hermite "Метод Эрмита: рациональная часть" hermite
                             (int-form e x) (list '+ (int-p R) (int-form rm x)))
                (record-step 'int-rational-lrt "Метод Лазара–Риобу–Трагера: логарифмическая часть" lrt
                             (int-form rm x) (int-p L)))))))))

; ---------- A1.4: вещественная форма root-sum — расширение Q(sqrt d) ----------
; sum_{Q(t)=0} t*log S(t,x): Q раскладывается над Q(sqrt d) (норма Трагера, alg-factor); квадратичные множители
; с kappa = b^2-4ac < 0 и sqrt(-kappa) в Q(sqrt d) — пара корней c = u+v*i, сопряжённых над Q(sqrt d):
;   c*log S(c) + conj(c)*log S(conj(c)) = u*log(A^2+B^2) - 2v*atan(B/A),  S(c,x) = A+iB (A,B — замена %i -> -%i);
; линейные множители и kappa > 0 — вещественные корни, явные log. Ответ проверяется дифференцированием (int-check-lrt).

(define int-rs-ds '(2 3 5 6 7 10 11 13 14 15 17 19 21 22 23 26 29 30 31 33 34))

; рациональный sqrt(v) (v — квадрат рационального) | #f
(define (int-rs-rat-sqrt v)
  (let ((r (simplify (list '^ v 1/2))))
    (if (rational-number? r) r #f)))

; sqrt элемента Q(sqrt d): w = x+y*sqrt d, w^2 = p+q*sqrt d — (x y) | #f (z = x^2 — корень z^2 - pz + d*q^2/4)
(define (int-rs-field-sqrt d p q)
  (cond ((= q 0)
         (or (let ((x (int-rs-rat-sqrt p))) (and x (list x 0)))
             (let ((y (int-rs-rat-sqrt (/ p d)))) (and y (list 0 y)))))
        (else
         (let ((s (int-rs-rat-sqrt (- (* p p) (* d q q)))))
           (and s
                (let try-z ((zs (list (/ (+ p s) 2) (/ (- p s) 2))))
                  (if (null? zs) #f
                      (let* ((z (car zs)) (x (int-rs-rat-sqrt z)))
                        (if (not x) (try-z (cdr zs))
                            (let ((y (/ q (* 2 x))))
                              (if (and (rational-number? y)
                                       (= (+ (* x x) (* d y y)) p) (= (* 2 x y) q))
                                  (list x y)
                                  (try-z (cdr zs)))))))))))))

; элемент Q(sqrt d) — пара (p q): p+q*sqrt d
(define (int-rs-elt2 el)
  (list (if (null? el) 0 (nth el 0))
        (if (and (pair? el) (pair? (cdr el))) (nth el 1) 0)))

; числовое значение элемента при alpha = sqrt d (d > 0 — вещественное вложение);
; sqrt в языке даёт алгебраическое число, поэтому значение берём через eval-num
(define (int-rs-elt-val d el)
  (let ((pq (int-rs-elt2 el)))
    (eval-num (simplify (list '+ (nth pq 0)
                              (list '* (nth pq 1) (list '^ d 1/2)))))))

; элемент Q(sqrt d) — выражение p+q*sqrt d (d > 0 — вещественное вложение)
(define (int-rs-elt->expr d el)
  (let* ((pq (int-rs-elt2 el)) (p (nth pq 0)) (q (nth pq 1)))
    (if (= q 0) p
        (simplify (expand (list '+ p (list '* q (list '^ d 1/2))))))))

; S(c,x) — (A B): S(c) = A+iB; A = (S+conj)/2, B = (S-conj)/(2i), conj — замена %i на -%i; #f — %i не сократился
(define (int-rs-reim Sc)
  (let* ((conj (replace-expr Sc '%i (list '* -1 '%i)))
         (A (simplify (expand (together (list '/ (list '+ Sc conj) 2)))))
         (B (simplify (expand (together (list '/ (list '- Sc conj) (list '* 2 '%i)))))))
    (and (not (contains-sym? A '%i)) (not (contains-sym? B '%i))
         (list A B))))

; корни квадратичного множителя q = a*u^2+b*u+c (коэффициенты — элементы Q(sqrt d)): kappa = b^2-4ac;
; kappa < 0 — (complex u v): корни u+-v*i; kappa > 0 — (real r1 r2); корни — выражения (радикалы).
; sqrt(kappa) не лежит в Q(sqrt d) — башня Q(sqrt d, sqrt e), e = ±kappa (int-rs-quad-roots-nested).
(define (int-rs-quad-roots Fg d q)
  (let* ((a (nth q 2)) (b (nth q 1)) (c0 (nth q 0))
         (two-a (alg-elt Fg '(2)))
         (a2 (alg-mul Fg two-a a))
         (kap (alg-sub Fg (alg-mul Fg b b)
                       (alg-mul Fg (alg-elt Fg '(4)) (alg-mul Fg a c0))))
         (kv (int-rs-elt-val d kap))
         (neg-b (alg-negate Fg b)))
    (cond ((< kv -0.000000001)
           (let ((pq (int-rs-elt2 (alg-negate Fg kap))))
             (let ((w (int-rs-field-sqrt d (nth pq 0) (nth pq 1))))
               (if w
                   (list 'complex
                         (int-rs-elt->expr d (alg-div Fg neg-b a2))
                         (int-rs-elt->expr d (alg-div Fg (alg-elt Fg w) a2))
                         #f)
                   (and (int-rs-small-elt? kap)
                        (int-rs-quad-roots-nested Fg d q a2 neg-b 'complex))))))
          ((> kv 0.000000001)
           (let ((pq (int-rs-elt2 kap)))
             (let ((w (int-rs-field-sqrt d (nth pq 0) (nth pq 1))))
               (if w
                   (list 'real
                         (int-rs-elt->expr d (alg-div Fg (alg-add Fg neg-b (alg-elt Fg w)) a2))
                         (int-rs-elt->expr d (alg-div Fg (alg-sub Fg neg-b (alg-elt Fg w)) a2))
                         #f)
                   (and (int-rs-small-elt? kap)
                        (int-rs-quad-roots-nested Fg d q a2 neg-b 'real))))))
          (else #f))))

; (int-rs-sqrt-elt d e) — выражение sqrt(e) для элемента e > 0 из Q(sqrt d) (башня Q(sqrt d, sqrt e)):
; денестинг (sqrt(2+sqrt 3) = (sqrt 6+sqrt 2)/2), вынос рационального квадрата (sqrt(4*sqrt 2) = 2*2^(1/4))
(define (int-rs-sqrt-elt d e)
  (let* ((ex (int-rs-elt->expr d e))
         (raw (list '^ ex 1/2))
         (dn (try (sqrt-denest raw) (lambda (err) #f))))
    (if (and dn (not (equal? dn raw)))
        dn
        (let* ((pq (int-rs-elt2 e)) (p (nth pq 0)) (q (nth pq 1))
               (s (and (= p 0) (> q 0) (int-rs-rat-sqrt q))))
          (if s (list '* s (list '^ d 1/4)) raw)))))

; запасной путь int-rs-quad-roots: sqrt(|kappa|) = q0*sqrt(e), e = ±kappa (элемент Q(sqrt d));
; корни u±v*i (complex) или u±w (real) — выражения с радикалом второй ступени.
; Отбор: коэффициенты kappa малы (иначе ответ раздувается — дешевле оставить root-sum).
(define (int-rs-small-elt? el)
  (every? (lambda (c) (and (rational-number? c)
                           (< (abs (numer c)) 1000000) (< (denom c) 1000000)))
          (int-rs-elt2 el)))

(define (int-rs-quad-roots-nested Fg d q a2 neg-b kind)
  (let* ((a (nth q 2)) (b (nth q 1)) (c0 (nth q 0))
         (kap (alg-sub Fg (alg-mul Fg b b)
                       (alg-mul Fg (alg-elt Fg '(4)) (alg-mul Fg a c0))))
         (kv (int-rs-elt-val d kap))
         (e (if (< kv 0) (alg-negate Fg kap) kap))
         (we (int-rs-sqrt-elt d e))
         (inv (int-rs-elt->expr d (alg-inv Fg a2)))
         (w (simplify (expand (list '* inv we))))
         (u (int-rs-elt->expr d (alg-div Fg neg-b a2))))
    (if (equal? kind 'complex)
        (list 'complex u w #t)
        (list 'real (simplify (list '+ u w)) (simplify (list '- u w)) #t))))

; квадратичный множитель (r — результат int-rs-quad-roots): complex — u*log(A^2+B^2) - 2v*atan(B/A); real — явные log.
; Ответ башни (4-й элемент r = #t) очищается от радикальных дробей; базовое поле Q(√d) — без очистки (дорого на больших Q).
(define (int-rs-quad-term tv S k r)
  (let* ((nested (and (pair? (cddr r)) (equal? (nth r 3) #t)))
         (cl (lambda (e) (if nested (int-rs-clean e tv) e))))
    (if (equal? (car r) 'complex)
        (let* ((u (cl (nth r 1)))
               (v (cl (nth r 2)))
               (c (list '+ u (list '* v '%i)))
               (Sc (together (subst (list tv c) S)))
               (ab (int-rs-reim Sc)))
          (and ab
               (let ((A (cl (nth ab 0))) (B (cl (nth ab 1))))
                 (list '* k
                       (list '-
                             (list '* u (list 'log (list '+ (list '* A A) (list '* B B))))
                             (list '* -2 v (list 'atan (list '/ A B))))))))
        (let* ((r1 (cl (nth r 1)))
               (r2 (cl (nth r 2))))
          (list '* k (list '+ (list '* r1 (list 'log (together (subst (list tv r1) S))))
                           (list '* r2 (list 'log (together (subst (list tv r2) S))))))))))

; вклад множителя q (степени <= 2, кратность k) в сумму t*log S(t,x); Fg = Q(sqrt d)
(define (int-rs-factor-term Fg d tv S q k)
  (let ((dq (algnum::ap-deg q)))
    (cond ((= dq 1)
           (let* ((c (alg-div Fg (alg-negate Fg (nth q 0)) (nth q 1)))
                  (ce (int-rs-elt->expr d c)))
             (list '* k ce (list 'log (together (subst (list tv ce) S))))))
          ((= dq 2)
           (let ((r (int-rs-quad-roots Fg d q)))
             (and r (int-rs-quad-term tv S k r))))
          (else #f))))

; разложение Q над Q(sqrt d) и сборка вкладов всех множителей; генерирующая поля — свежий символ g (не tv!)
(define (int-rs-try-d Q tv S d)
  (let* ((g (gensym))
         (m (simplify (list '+ (list '^ g 2) (list '* -1 d))))
         (Fg (alg-field m g))
         (fg (algnum::expr->ap Fg (replace-expr Q tv g) g))
         (r (alg-factor Fg fg g))
         (pairs (nth r 1)))
    (and (every? (lambda (pr) (<= (algnum::ap-deg (car pr)) 2)) pairs)
         (let ((terms (map (lambda (pr) (int-rs-factor-term Fg d tv S (car pr) (cadr pr))) pairs)))
           (and (every? (lambda (tm) tm) terms)
                (begin (record-condition (list 'rootsum-real-form (list '^ d 1/2))
                        "вещественная форма root-sum: резольвента разложена над Q(sqrt d)")
                  (simplify (cons '+ terms))))))))

; ---------- A3′.4: очистка радикальных коэффициентов (башня Q(sqrt d, sqrt e)) ----------
; Ответ башни содержит дроби с радикальными знаменателями: 1/(6+4*sqrt3) и т. п. Приводим x-свободные
; выражения к явному виду в мультиквадратичном поле ℚ(√p1,√p2,…) (p — простые, не больше трёх):
; моном = коэффициент·∏√p, обратный элемент — произведение всех нетождественных сопряжений / норму.

; x-свободный моном → (coef . rads); rads — squarefree > 1 (после слияния корней)
(define (int-rs-rad-mono t)
  (cond ((rational-number? t) (cons t '()))
        ((and (op-expr? t) (equal? (car t) '^) (= (length t) 3) (equal? (nth t 2) 1/2)
              (rational-number? (nth t 1)) (> (nth t 1) 0))
         (let* ((sp (denest::dn-square-split (* (numer (nth t 1)) (denom (nth t 1)))))
                (coef (/ (car sp) (denom (nth t 1))))
                (s (cdr sp)))
           (cons coef (if (= s 1) '() (list s)))))
        ((and (op-expr? t) (equal? (car t) '*))
         (int-rs-rad-mono-fold (cdr t) 1 '()))
        (else #f)))

(define (int-rs-rad-mono-fold fs coef rads)
  (if (null? fs)
      (int-rs-rad-merge coef rads)
      (let ((m (int-rs-rad-mono (car fs))))
        (and m (int-rs-rad-mono-fold (cdr fs) (* coef (car m)) (append (cdr m) rads))))))

; произведение корней → один корень: √a·√b = c·√s (s без квадратов)
(define (int-rs-rad-merge coef rads)
  (if (null? rads)
      (cons coef '())
      (let* ((n (foldl (lambda (a s) (* a s)) 1 rads))
             (sp (denest::dn-square-split n)))
        (cons (* coef (car sp)) (if (= (cdr sp) 1) '() (list (cdr sp)))))))

; x-свободное выражение → список мономов (coef . rads) | #f
(define (int-rs-rad-sum X)
  (let ((e (expand X)))
    (if (and (op-expr? e) (equal? (car e) '+))
        (let ((ms (map int-rs-rad-mono (cdr e))))
          (and (every? (lambda (m) m) ms) ms))
        (let ((m (int-rs-rad-mono e))) (and m (list m))))))

; простые делители n (n — небольшое squarefree)
(define (int-rs-prime-factors n)
  (let loop ((n n) (d 2) (acc '()))
    (cond ((= n 1) (reverse acc))
          ((> (* d d) n) (reverse (cons n acc)))
          ((= (mod n d) 0) (loop (quotient n d) d (if (member? d acc) acc (cons d acc))))
          (else (loop n (+ d 1) acc)))))

; все простые, встречающиеся в радикандах
(define (int-rs-rad-primes parts)
  (let loop ((ps parts) (acc '()))
    (if (null? ps)
        acc
        (let ((rs (cdr (car ps))))
          (loop (cdr ps)
                (if (null? rs) acc
                    (foldl (lambda (a p) (if (member? p a) a (append a (list p))))
                           acc (int-rs-prime-factors (car rs)))))))))

(define (int-rs-len-basis ps)
  (if (null? ps) 1 (* 2 (int-rs-len-basis (cdr ps)))))

(define (int-rs-vec-zero n) (map (lambda (i) 0) (range n)))

; единица поля: 1 при индексе 0
(define (int-rs-vec-one n)
  (map (lambda (i) (if (= i 0) 1 0)) (range n)))

; прибавить c к компоненте k
(define (int-rs-vec-add v k c)
  (map2 (lambda (x i) (if (= i k) (+ x c) x)) v (range (length v))))

; маска подмножества простых, произведение которых = s
(define (int-rs-rad-mask ps s)
  (let loop ((ps ps) (k 0) (m 0) (s s))
    (cond ((null? ps) (if (= s 1) m #f))
          ((= (mod s (car ps)) 0)
           (loop (cdr ps) (+ k 1) (+ m (^ 2 k)) (quotient s (car ps))))
          (else (loop (cdr ps) (+ k 1) m s)))))

; произведение простых по битовой маске
(define (int-rs-mask-prod ps m)
  (let loop ((ps ps) (k 0) (r 1))
    (if (null? ps) r
        (loop (cdr ps) (+ k 1)
              (if (= (mod (quotient m (^ 2 k)) 2) 1) (* r (car ps)) r)))))

(define (int-rs-bits-xor a b)
  (let loop ((a a) (b b) (p 1) (r 0))
    (if (and (= a 0) (= b 0)) r
        (loop (quotient a 2) (quotient b 2) (* p 2)
              (if (= (mod a 2) (mod b 2)) r (+ r p))))))

(define (int-rs-bits-and-count a b)
  (let loop ((a a) (b b) (r 0))
    (if (and (= a 0) (= b 0)) r
        (loop (quotient a 2) (quotient b 2)
              (+ r (if (and (= (mod a 2) 1) (= (mod b 2) 1)) 1 0))))))

; пересечение масок (общие простые)
(define (int-rs-bits-and a b)
  (let loop ((a a) (b b) (p 1) (r 0))
    (if (and (= a 0) (= b 0)) r
        (loop (quotient a 2) (quotient b 2) (* p 2)
              (if (and (= (mod a 2) 1) (= (mod b 2) 1)) (+ r p) r)))))

; вектор коэффициентов по базису √(подмножества простых)
(define (int-rs-rad-vec parts ps n)
  (foldl (lambda (v pr)
           (let ((m (int-rs-rad-mask ps (if (null? (cdr pr)) 1 (car (cdr pr))))))
             (if m (int-rs-vec-add v m (car pr)) v)))
         (int-rs-vec-zero n) parts))

; произведение элементов в базисе: √S1·√S2 = ∏(S1∩S2)·√(S1 Δ S2)
(define (int-rs-vec-mul ps a b)
  (let ((n (length a)))
    (let loop-i ((i 0) (res (int-rs-vec-zero n)))
      (if (= i n)
          res
          (loop-i (+ i 1) (int-rs-vec-add-row ps (nth a i) i b res))))))

(define (int-rs-vec-add-row ps ai i b res)
  (let ((n (length b)))
    (let loop-j ((j 0) (r res))
      (if (= j n)
          r
          (loop-j (+ j 1)
                  (if (= (nth b j) 0)
                      r
                      (let* ((k (int-rs-bits-xor i j))
                             (c (* ai (nth b j)
                                   (int-rs-mask-prod ps (int-rs-bits-and i j)))))
                        (int-rs-vec-add r k c))))))))

; сопряжение по простому p (маска m): у компонент с p знак меняется
(define (int-rs-vec-conj v m)
  (let loop ((v v) (k 0) (acc '()))
    (if (null? v) (reverse acc)
        (loop (cdr v) (+ k 1)
              (cons (if (= (mod (int-rs-bits-and-count k m) 2) 1) (- (car v)) (car v)) acc)))))

(define (int-rs-rad-print ps w)
  (let loop ((w w) (k 0) (acc '()))
    (if (null? w)
        (if (null? acc) 0 (simplify (cons '+ (reverse acc))))
        (let ((c (car w)))
          (loop (cdr w) (+ k 1)
                (if (= c 0) acc
                    (cons (if (= k 0) c
                              (let ((rad (list '^ (int-rs-mask-prod ps k) 1/2)))
                                (cond ((= c 1) rad)
                                      ((= c -1) (list '* -1 rad))
                                      (else (list '* c rad)))))
                          acc)))))))

; (int-rs-rad-one? X) — X точно равно 1 как радикальное выражение (дешёвый сертификат: вектор коэффициентов (1 0 … 0))
(define (int-rs-rad-one? X)
  (let ((parts (int-rs-rad-sum X)))
    (and parts
         (let* ((ps (int-rs-rad-primes parts))
                (v (int-rs-rad-vec parts ps (int-rs-len-basis ps))))
           (and (= (nth v 0) 1) (every? (lambda (c) (= c 0)) (cdr v)))))))

; (int-rs-rad-inv D) — x-свободное D → 1/D в явном виде | #f (поле шире трёх простых, D = 0 — #f)
(define (int-rs-rad-inv D)
  (let ((parts (int-rs-rad-sum D)))
    (and parts
         (let* ((ps (int-rs-rad-primes parts))
                (n (int-rs-len-basis ps)))
           (and (<= (length ps) 3)
                (let* ((v (int-rs-rad-vec parts ps n))
                       ; произведение всех нетождественных сопряжений: norm = v·prod (рациональное)
                       (prod (let loop ((m 1) (acc (int-rs-vec-one n)))
                               (if (>= m n) acc
                                   (loop (+ m 1) (int-rs-vec-mul ps acc (int-rs-vec-conj v m))))))
                       (normv (int-rs-vec-mul ps v prod))
                       (norm (nth normv 0)))
                  (and (not (= norm 0))
                       (every? (lambda (c) (= c 0)) (cdr normv))
                       (let ((res (int-rs-rad-print ps (map (lambda (c) (/ c norm)) prod))))
                         (and res (int-rs-rad-one? (list '* D res)) res)))))))))

; (int-rs-expr-size e) — число узлов выражения (дешёвый отбор для очистки)
(define (int-rs-expr-size e)
  (if (list? e) (+ 1 (foldl (lambda (a u) (+ a (int-rs-expr-size u))) 0 e)) 1))

; замена x-свободных обратных радикальных выражений на явные (сертификат — int-rs-rad-inv);
; только небольшие знаменатели — иначе разбор радикалов дороже самого ответа
(define (int-rs-clean e x)
  (if (not (list? e))
      e
      (let ((e1 (map (lambda (u) (int-rs-clean u x)) e)))
        (cond ((and (op-expr? e1) (equal? (car e1) '^) (= (length e1) 3)
                    (equal? (nth e1 2) -1) (x-free? (nth e1 1) x)
                    (<= (int-rs-expr-size (nth e1 1)) 40))
               (or (int-rs-rad-inv (nth e1 1)) e1))
              ((and (op-expr? e1) (equal? (car e1) '/) (= (length e1) 3)
                    (equal? (nth e1 1) 1) (x-free? (nth e1 2) x)
                    (<= (int-rs-expr-size (nth e1 2)) 40))
               (or (int-rs-rad-inv (nth e1 2)) e1))
              (else e1)))))

; дешёвый отбор: коэффициенты резольвенты малы (иначе разложение над башней раздувается, а ответ — нет)
(define (int-rs-small-rat? c)
  (and (rational-number? c) (< (abs (numer c)) 100000000) (< (denom c) 100000000)))

(define (int-rs-small-poly? p tv)
  (every? int-rs-small-rat? (coefficients p tv)))

; каждый неприводимый над Q множитель Q — степени 1, 2 или 4
(define (int-rs-degree-ok? Q tv)
  (let ((fl (try (factor-list Q) (lambda (err) #f))))
    (and fl
         (every? (lambda (fk) (member? (degree (nth fk 0) tv) '(0 1 2 4))) (cdr fl)))))

; ---------- INT.RS: резольвента в радикалах — двучлен t^n = ρ (n = 3…12), кубика (Кардано / casus irreducibilis) ----------
; Корни множителей Q выписываются явно; вещественные корни r дают r·log|S(r)|, пара сопряжённых u±v·i — вещественную форму
; Риобу без скачков: S линейно по x, S(c) = α(x+γ), γ = g1+i·g2, и  c·log S(c) + c̄·log S(c̄) ≡ u·log((x+g1)²+g2²) + 2v·atan((x+g1)/g2)
; (atan от линейной функции непрерывен; корни и S раскрываются в радикалы, g2 ≠ 0). Если корни не выписываются — rootsum остаётся.

; cos и sin угла π·p/q, 0 < p/q < 1/2 (и 1/2) — в радикалах
(define int-rs-trig-table
  '(((2 1) 0 1)
    ((3 1) 1/2 (/ (^ 3 1/2) 2))
    ((4 1) (/ (^ 2 1/2) 2) (/ (^ 2 1/2) 2))
    ((5 1) (/ (+ 1 (^ 5 1/2)) 4) (/ (^ (- 10 (* 2 (^ 5 1/2))) 1/2) 4))
    ((5 2) (/ (- (^ 5 1/2) 1) 4) (/ (^ (+ 10 (* 2 (^ 5 1/2))) 1/2) 4))
    ((6 1) (/ (^ 3 1/2) 2) 1/2)
    ((8 1) (/ (^ (+ 2 (^ 2 1/2)) 1/2) 2) (/ (^ (- 2 (^ 2 1/2)) 1/2) 2))
    ((8 3) (/ (^ (- 2 (^ 2 1/2)) 1/2) 2) (/ (^ (+ 2 (^ 2 1/2)) 1/2) 2))
    ((10 1) (/ (^ (+ 10 (* 2 (^ 5 1/2))) 1/2) 4) (/ (- (^ 5 1/2) 1) 4))
    ((10 3) (/ (^ (- 10 (* 2 (^ 5 1/2))) 1/2) 4) (/ (+ 1 (^ 5 1/2)) 4))
    ((12 1) (/ (+ (^ 6 1/2) (^ 2 1/2)) 4) (/ (- (^ 6 1/2) (^ 2 1/2)) 4))
    ((12 5) (/ (- (^ 6 1/2) (^ 2 1/2)) 4) (/ (+ (^ 6 1/2) (^ 2 1/2)) 4))))

; (cos sin) угла π·m/n, 0 < m < n, или #f (угол не в таблице)
(define (int-rs-trig m n)
  (let* ((g (gcd m n)) (p (quotient m g)) (q (quotient n g))
         (mirror (> (* 2 p) q))
         (p1 (if mirror (- q p) p))
         (row (assoc (list q p1) int-rs-trig-table)))
    (and row
         (let ((c (simplify (nth row 1))) (s (simplify (nth row 2))))
           (list (if mirror (simplify (list '* -1 c)) c) s)))))

; вещественный кубический корень выражения (знак — по численному значению)
(define (int-rs-rcbrt y)
  (if (>= (eval-num (simplify y)) 0)
      (simplify (list '^ y 1/3))
      (simplify (list '* -1 (list '^ (simplify (list '* -1 y)) 1/3)))))

(define (int-rs-real-term tv S r)
  ; log|y| записан как ½·log(y²): так вещественно при любом знаке y, а производная не содержит sign (его не берёт eval-num)
  (list '* 1/2 r (list 'log (list '^ (together (subst (list tv r) S)) 2))))

; пара сопряжённых корней u±v·i; S линейно по x, иначе #f
(define (int-rs-cpair-term tv S x u v)
  (and (<= (degree S x) 1)
       (let* ((c (list '+ u (list '* v '%i)))
              (S0 (together (subst (list tv c) (subst (list x 0) S))))
              (S1 (together (subst (list tv c) (subst (list x 1) S))))
              (a (int-rs-reim (together (list '- S1 S0))))
              (b (int-rs-reim S0)))
         (and a b
              (let* ((a1 (nth a 0)) (a2 (nth a 1)) (b1 (nth b 0)) (b2 (nth b 1))
                     (N (simplify (together (list '+ (list '* a1 a1) (list '* a2 a2)))))
                     (g1 (simplify (together (list '/ (list '+ (list '* b1 a1) (list '* b2 a2)) N))))
                     (g2 (simplify (together (list '/ (list '- (list '* b2 a1) (list '* b1 a2)) N)))))
                (and (> (abs (eval-num g2)) 0.000000001)
                     (list '+ (list '* u (list 'log (list '+ (list '^ (list '+ x g1) 2) (list '^ g2 2))))
                           (list '* 2 v (list 'atan (list '/ (list '+ x g1) g2))))))))))

; двучлен a·t^n+b (co — коэффициенты по возрастанию): корни |ρ|^(1/n)·e^{iπ(2k+δ)/n}, ρ = -b/a
(define (int-rs-binomial-terms tv S x co)
  (let* ((n (- (length co) 1)) (rho (/ (- (nth co 0)) (nth co n)))
         (delta (if (> rho 0) 0 1))
         (r (simplify (list '^ (abs rho) (/ 1 n)))))
    (let loop ((k 0) (acc '()))
      (if (= k n)
          (reverse acc)
          (let* ((m (mod (+ (* 2 k) delta) (* 2 n))))
            (cond ((= m 0) (loop (+ k 1) (cons (int-rs-real-term tv S r) acc)))
                  ((= m n) (loop (+ k 1) (cons (int-rs-real-term tv S (simplify (list '* -1 r))) acc)))
                  ((> m n) (loop (+ k 1) acc))
                  (else
                   (let ((cs (int-rs-trig m n)))
                     (and cs
                          (let ((tm (int-rs-cpair-term tv S x (simplify (list '* r (nth cs 0)))
                                                       (simplify (list '* r (nth cs 1))))))
                            (and tm (loop (+ k 1) (cons tm acc)))))))))))))

; неприводимая кубика (Кардано): D > 0 — один вещественный корень и пара; D < 0 — три вещественных, корни через cos(acos(·)/3)
(define (int-rs-cubic-terms tv S x co)
  (let* ((a (nth co 3)) (b (/ (nth co 2) a)) (c (/ (nth co 1) a)) (d (/ (nth co 0) a))
         (p (- c (/ (* b b) 3)))
         (q (+ (- (/ (* 2 b b b) 27) (/ (* b c) 3)) d))
         (D (+ (/ (* q q) 4) (/ (* p p p) 27)))
         (sh (/ (- b) 3)))
    (cond ((> D 0)
           (let* ((sD (simplify (list '^ D 1/2)))
                  ; A — кубический корень без сокращения (знак √D как у -q), B = -p/(3A): одно основание корня в ответе
                  (A (int-rs-rcbrt (simplify (list (if (<= q 0) '+ '-) (/ (- q) 2) sD))))
                  (B (simplify (list '/ (/ (- p) 3) A)))
                  (r1 (simplify (list '+ A B sh)))
                  (u (simplify (list '+ (list '* -1/2 (list '+ A B)) sh)))
                  (v (simplify (list '* (list '/ (list '^ 3 1/2) 2) (list '- A B))))
                  (pr (int-rs-cpair-term tv S x u v)))
             (and pr (list (int-rs-real-term tv S r1) pr))))
          ((< D 0)
           (let* ((m (simplify (list '* 2 (list '^ (/ (- p) 3) 1/2))))
                  (arg (simplify (list '* (/ (* 3 q) (* 2 p)) (list '^ (/ -3 p) 1/2))))
                  (th (list '/ (list 'acos arg) 3)))
             (map (lambda (k)
                    (int-rs-real-term tv S
                      (simplify (list '+ sh (list '* m (list 'cos (list '- th (list '* (/ (* 2 k) 3) 'pi))))))))
                  '(0 1 2))))
          (else #f))))

; вклад неприводимого множителя f (по возрастанию коэффициентов co) — список слагаемых | #f
(define (int-rs-factor-radical tv S x f)
  (let* ((co (coefficients f tv)) (n (- (length co) 1))
         (binom (every? (lambda (c) (= c 0)) (take (cdr co) (- n 1)))))
    (cond ((= n 1)
           (list (int-rs-real-term tv S (/ (- (nth co 0)) (nth co 1)))))
          ((= n 2)
           (let* ((a (nth co 2)) (kap (- (* (nth co 1) (nth co 1)) (* 4 a (nth co 0))))
                  (m (/ (- (nth co 1)) (* 2 a))))
             (if (> kap 0)
                 (let ((w (simplify (list '/ (list '^ kap 1/2) (* 2 a)))))
                   (list (int-rs-real-term tv S (simplify (list '+ m w)))
                         (int-rs-real-term tv S (simplify (list '- m w)))))
                 (let ((tm (int-rs-cpair-term tv S x m (simplify (list '/ (list '^ (- kap) 1/2) (* 2 a))))))
                   (and tm (list tm))))))
          ((and (>= n 3) (<= n 12) binom) (int-rs-binomial-terms tv S x co))
          ((= n 3) (int-rs-cubic-terms tv S x co))
          (else #f))))

; предел размера раскрытия (число узлов): кубики Кардано с D > 0 дают 750…2000 узлов, checkSteps/expand на них — десятки секунд;
; двучлены (≤ 400 узлов) и casus irreducibilis (≈ 360) проходят, x³+x+1 и ему подобные остаются rootsum
(define int-rs-radical-max 500)

(define (int-rs-expand-radical rs)
  (and (op-expr? rs) (equal? (car rs) 'root-sum) (= (length rs) 4)
       (let ((tv (nth rs 1)) (Q (nth rs 2)) (E (nth rs 3)))
         (and (symbol? tv)
              (every? (lambda (s) (equal? s tv)) (int-symbols Q tv))
              (op-expr? E) (equal? (car E) '*) (= (length E) 3) (equal? (nth E 1) tv)
              (op-expr? (nth E 2)) (equal? (car (nth E 2)) 'log)
              (int-rs-small-poly? Q tv)
              (let* ((S (nth (nth E 2) 1))
                     (x (int-rs-first-or-false (filter (lambda (s) (not (equal? s tv))) (int-symbols S tv))))
                     (fl (factor-list Q)))
                (and x
                     (let loop ((fs (cdr fl)) (acc '()))
                       (cond ((null? fs)
                              (let ((res (simplify (cons '+ (reverse acc)))))
                                ; запись чудовищна (> int-rs-radical-max узлов) — честнее оставить rootsum
                                (and (<= (int-rs-expr-size res) int-rs-radical-max)
                                     (begin (record-condition (list 'rootsum-real-form 'radicals)
                                              "вещественная форма root-sum: корни резольвенты в радикалах")
                                       res))))
                             ((= (degree (nth (car fs) 0) tv) 0) (loop (cdr fs) acc))
                             ((not (= (nth (car fs) 1) 1)) #f)
                             (else
                              (let ((ts (int-rs-factor-radical tv S x (nth (car fs) 0))))
                                (and ts (loop (cdr fs) (append (reverse ts) acc)))))))))))))

(define (int-rs-first-or-false l) (if (null? l) #f (car l)))

(define (int-rs-expand rs)
  (or (int-rs-expand-q2 rs)
      ; раскрытие в радикалах — с бюджетом времени (3 с): при исчерпании rootsum остаётся как был
      (let ((r (call-with-time-limit 3 (lambda () (int-rs-expand-radical rs)))))
        (and (pair? r) (equal? (car r) 'ok) (cadr r)))))

; (root-sum tv Q (* tv (log S))) — вещественное выражение | #f: перебор d, факторизация Q над Q(sqrt d)
(define (int-rs-expand-q2 rs)
  (and (op-expr? rs) (equal? (car rs) 'root-sum) (= (length rs) 4)
       (let ((tv (nth rs 1)) (Q (nth rs 2)) (E (nth rs 3)))
         (and (symbol? tv)
              (every? (lambda (s) (equal? s tv)) (int-symbols Q tv))
              (op-expr? E) (equal? (car E) '*) (= (length E) 3) (equal? (nth E 1) tv)
              (op-expr? (nth E 2)) (equal? (car (nth E 2)) 'log)
              ; неприводимый над Q многочлен над квадратичным полем распадается не более чем на 2 сопряжённых множителя:
              ; множители степени ≤ 2 возможны только при deg Q ∈ {2, 4} — иначе перебор полей не нужен (ревью
              ; ревью: без фильтра ratint-тесты замедлились вдвое)
              (int-rs-degree-ok? Q tv)
              ; коэффициенты резольвенты малы: иначе разложение даёт огромный ответ (дешевле оставить root-sum)
              (int-rs-small-poly? Q tv)
              (let ((S (nth (nth E 2) 1)))
                (let loop ((ds int-rs-ds))
                  (if (null? ds) #f
                      (or (try (int-rs-try-d Q tv S (car ds)) (lambda (err) #f))
                          (loop (cdr ds))))))))))

; замена всех root-sum в выражении (не раскрывшиеся остаются как были)
(define (int-rs-walk e)
  (cond ((and (op-expr? e) (equal? (car e) 'root-sum))
         (or (try (int-rs-expand e) (lambda (err) #f)) e))
        ((list? e) (map int-rs-walk e))
        (else e)))

(define (int-rational-lrt e x d)
  (and (int-rational? e x)
       (with-step ('int-rational-function "Рациональная функция: метод Эрмита и Лазара–Риобу–Трагера" (int-form e x)
                   :comment "рациональная часть выделяется редукцией Эрмита, остаток интегрируется как сумма логарифмов (ЛРТ)"
                   :after int-p)
         (let* ((tv (int-fresh-t e x))
                (F0 (simplify (rat-integrate-log e x tv (int-all-real? e x))))
                ; A1.4: вещественная форма root-sum (все параметры вещественны) — расширение Q(sqrt d)
                (F (if (and (int-all-real? e x) (not (null? (int-rootsums F0))))
                       (int-rs-walk F0)
                       F0)))
           (if (int-check-lrt F e x)
               (begin (if (step-log-enabled?) (int-lrt-notes e x F)) F)
               (begin (attempt-fail "ответ не прошёл проверку дифференцированием") #f))))))

(int-add-strategy int-linear)
(int-add-strategy int-rational)
(int-add-strategy int-rational-lrt)
(int-add-strategy int-usub)
