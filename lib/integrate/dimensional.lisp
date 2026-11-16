; integrate/dimensional.lisp — определённые интегралы с параметрами через размерности + квадратура + PSLQ (эксперимент INT.OWN.B9)
;
; ∫ₐᵇ f(x; p₁…pₖ) dx, пределы — 0, ±inf, числа или выражения от параметров. Веса x и pᵢ — из однородности (Б1: аргументы
; exp/log/sin… безразмерны, слагаемые суммы одного веса). Допустимые масштабирования W — ядро линейной системы; результат
; I(λ^{W_p} p) = λ^{s(W)} I. Если вектор весов результата u (Σ uᵢ·Wᵢ = s) определён однозначно (безразмерных групп нет), то
;   I = C · Π pᵢ^{uᵢ},   C = I при pᵢ = 1.
; C — высокоточная квадратура (tanh-sinh на конечном отрезке, exp-sinh на полуоси, sinh-sinh на прямой; рациональная арифметика
; через интервалы, ≥ 25 знаков), точный вид — PSLQ (одночлены 2ᵃ3ᵇ5ᶜ7ᵈπᵉ по логарифмам; малые линейные базисы с 1, π, √π, π²,
; log 2, √2, √3, e, ζ(3), G, γ). Ответ принимается, только если: (1) PSLQ нашёл короткое соотношение; (2) формула совпала с
; квадратурой при двух других наборах параметров (вес проверяется, а не предполагается).
; Больше одной безразмерной группы, символический показатель, осцилляция до ∞, нет сходимости квадратуры — отказ (#f).
; НЕ доказательство: ответ — численно подтверждённая гипотеза (≥ 25 знаков, 3 набора параметров), см. research/intown/b9.md.
(module integrate
  (export int-dimensional int-dimensional-with int-dimensional-info))

; выключено по умолчанию (замер B9: ответ — численно подтверждённая гипотеза, а не доказательство; 3–40 с на отказ)
; решение пользователя 2026-11-16: включено по умолчанию; бюджет 15 с (медиана взятых ≈ 4 с), ответ помечается
; условием numeric-identification — константа опознана численно (PSLQ) и сверена при трёх наборах параметров, не доказана
(define int-dimensional-enabled #t)
(define int-dimensional-time-limit 15)
; последняя ступень определённого интеграла: r — результат каскада; невычисленный → попытка int-dimensional (только если флаг включён)
(define (int-dimensional-step e x a b r)
  (if (and int-dimensional-enabled (int-unevaluated? r))
      (let ((v (int-guard (lambda ()
                            (let ((c (call-with-time-limit int-dimensional-time-limit (lambda () (int-dimensional e x a b)))))
                              (and (pair? c) (equal? (car c) 'ok) (cadr c)))))))
        (if v
            (begin (record-condition '(numeric-identification)
                                     "размерности + квадратура + PSLQ: константа опознана численно и сверена при трёх наборах параметров (не доказательство)")
                   v)
            r))
      r))
(define dm-info '())            ; (статус деталь…) последнего вызова
(define (int-dimensional-info) dm-info)
(define dm-D 45)                ; рабочие знаки интервальной арифметики
(define dm-target 25)           ; знаков, которые должны совпасть между уровнями квадратуры
(define dm-stats-nodes 0)

; ---------- веса ----------
(define dm-cons '())
(define dm-fail #f)
(define dm-consts '(pi e %e))
(define dm-fns '(exp sin cos tan cot sec csc erf erfc erfi Ei li Si Ci atan sinh cosh tanh asinh atanh lambert_w))
(define (dm-con! f) (if (pair? f) (set! dm-cons (cons f dm-cons))))
(define (dm-qnum? q) (or (integer? q) (equal? (type-of q) 'rational)))

(define (dm-w e)
  (cond ((number? e) '())
        ((member? e dm-consts) '())
        ((symbol? e) (list (cons e 1)))
        ((not (op-expr? e)) (set! dm-fail #t) '())
        (else
         (let ((h (car e)) (args (cdr e)))
           (cond ((equal? h '+)
                  (let ((fs (map dm-w args)))
                    (for-each (lambda (g) (dm-con! (wf-sub g (car fs)))) (cdr fs))
                    (car fs)))
                 ((equal? h '*) (foldl wf-add '() (map dm-w args)))
                 ((and (equal? h '^) (= (length args) 2) (dm-qnum? (nth e 2))) (wf-scale (dm-w (nth e 1)) (nth e 2)))
                 ((and (equal? h 'sqrt) (= (length args) 1)) (wf-scale (dm-w (car args)) 1/2))
                 ((equal? h 'abs) (dm-w (car args)))
                 ((and (equal? h 'log) (= (length args) 1)) (dm-con! (dm-w (car args))) '())
                 ((and (member? h dm-fns) (= (length args) 1)) (dm-con! (dm-w (car args))) '())
                 (else (set! dm-fail #t) '()))))))

; ---------- линейная алгебра над ℚ ----------
(define (dm-find p l) (cond ((null? l) #f) ((p (car l)) (car l)) (else (dm-find p (cdr l)))))
(define (dm-remove1 r l) (cond ((null? l) '()) ((equal? (car l) r) (cdr l)) (else (cons (car l) (dm-remove1 r (cdr l))))))

; (rref rows n) → (pivots . остаток): pivots — ((столбец . строка) …), строки приведены (Гаусс — Жордан)
(define (dm-rref rows n)
  (let loop ((c 0) (rows rows) (piv '()))
    (if (or (>= c n) (null? rows))
        (cons (reverse piv) rows)
        (let ((r (dm-find (lambda (u) (not (= (nth u c) 0))) rows)))
          (if (not r)
              (loop (+ c 1) rows piv)
              (let* ((r1 (map (lambda (q) (/ q (nth r c))) r))
                     (elim (lambda (u) (let ((m (nth u c))) (if (= m 0) u (map2 (lambda (p q) (- p (* m q))) u r1))))))
                (loop (+ c 1)
                      (map elim (dm-remove1 r rows))
                      (append (map (lambda (pv) (cons (car pv) (elim (cdr pv)))) piv) (list (cons c r1))))))))))

; ядро: базисные векторы длины n
(define (dm-nullspace rows n)
  (let* ((rr (dm-rref rows n)) (piv (car rr)) (pcols (map car piv)))
    (map (lambda (f)
           (map (lambda (j)
                  (cond ((= j f) 1)
                        ((member? j pcols) (- 0 (nth (cdr (assoc j piv)) f)))
                        (else 0)))
                (range n)))
         (filter (lambda (j) (not (member? j pcols))) (range n)))))

; решить Σ uᵢ·Wⱼ[i] = sⱼ: (u₁…uₖ) | 'groups (недоопределено) | 'inconsistent
(define (dm-solve-u Ws ss k)
  (let* ((rows (map2 (lambda (w s) (append (cdr w) (list s))) Ws ss))
         (rr (dm-rref rows (+ k 1))) (piv (car rr)))
    (cond ((assoc k piv) 'inconsistent)
          ((< (length piv) k) 'groups)
          (else (map (lambda (i) (nth (cdr (assoc i piv)) k)) (range k))))))

; ---------- квадратура ----------
(define (dm-pow10 n) (/ 1 (^ 10 n)))
; e^q (рациональное приближение, ошибка ≪ 10^−(D+10) относительно): ряд Тейлора + возведения в квадрат, округление на каждом шаге
(define (dm-rnd q g) (/ (floor (+ (* q g) 1/2)) g))
(define (dm-exp-pos u)
  (let* ((g (^ 10 (+ dm-D 25)))
         (m (let loop ((m 0) (v u)) (if (<= v 1/2) m (loop (+ m 1) (/ v 2)))))
         (r (/ u (^ 2 m)))
         (s (let loop ((n 1) (term 1) (acc 1))
              (let ((t2 (dm-rnd (/ (* term r) n) g)))
                (if (= t2 0) acc (loop (+ n 1) t2 (+ acc t2)))))))
    (let sq ((k 0) (v s)) (if (= k m) v (sq (+ k 1) (dm-rnd (* v v) g))))))
(define (dm-ndig n) (string-length (number->string (abs n))))
; округление до dm-D + 15 значащих цифр
(define (dm-relk q n)
  (if (= q 0)
      0
      (let* ((e (- (dm-ndig (numer q)) (dm-ndig (denom q)))) (k (- n e)))
        (if (>= k 0)
            (dm-rnd q (^ 10 k))
            (* (^ 10 (- 0 k)) (dm-rnd (/ q (^ 10 (- 0 k))) 1))))))
(define (dm-rel q) (dm-relk q (+ dm-D 15)))
; |q| < 1e-10: 1 + t без округления суммы (иначе exp(u) − 1 теряет всё при малых u)
(define (dm-exp-small q)
  (let loop ((n 2) (term q) (acc q))
    (let ((t2 (dm-rel (/ (* term q) n))))
      (if (< (abs t2) (* (abs q) (dm-pow10 70)))
          (+ 1 acc)
          (loop (+ n 1) t2 (+ acc t2))))))
(define (dm-exp q)
  (cond ((= q 0) 1)
        ((< (abs q) 1/10000000000) (dm-exp-small q))
        (else (dm-rel (if (< q 0) (/ 1 (dm-exp-pos (- 0 q))) (dm-exp-pos q))))))
(define dm-pi 0)

(define (dm-sub e pairs) (foldl (lambda (acc p) (subst p acc)) e pairs))

; значение f в рациональной точке: рациональное | #f
(define (dm-fn0 h v)    ; h(v) через интервалы (значение — середина, ширина проверяется)
  (let ((X (const-enclosure (list h v) dm-D)))
    (if (and X (< (iv-width X) (* (dm-pow10 (- dm-D 14)) (+ 1 (abs (iv-mid X))))))
        (iv-mid X)
        (error "dm-ev: широкое включение" h))))

; ln q для q > 0 любой величины (интервал для крошечного q округляется до 0): q = m·10^e, m ∈ [0.1, 10]
(define dm-ln10 #f)
; ln(1+t), |t| < 1e-4: ряд t − t²/2 + t³/3 …, относительная точность (иначе log(1+ε) теряет ε < 1e-45 под ширину включения)
(define (dm-log1p t)
  (let loop ((k 2) (p t) (acc t))
    (let ((p2 (dm-rel (* p t))))
      (if (< (abs p2) (* (abs t) (dm-pow10 70)))
          acc
          (loop (+ k 1) p2 (+ acc (/ (if (even? k) (- 0 p2) p2) k)))))))
(define (dm-ln q)
  (cond ((<= q 0) (error "dm-ev: log"))
        ((and (< (abs (- q 1)) 1/10000) (not (= q 1))) (dm-log1p (- q 1)))
        ((= q 1) 0)
        (else
         (let ((e (- (dm-ndig (numer q)) (dm-ndig (denom q)))))
           (if (not dm-ln10) (set! dm-ln10 (dm-fn0 'log 10)))
           (+ (dm-fn0 'log (/ q (^ 10 e))) (* e dm-ln10))))))

(define (dm-fn1 h v) (if (equal? h 'log) (dm-ln v) (dm-fn0 h v)))

; рациональное вычисление выражения без символов; exp — своя (быстрая для больших аргументов), остальное — интервалы
(define (dm-ev e)
  (cond ((number? e) e)
        ((not (op-expr? e)) (error "dm-ev: символ" e))
        (else
         (let ((h (car e)) (as (cdr e)))
           ; промежуточные суммы/произведения — 200 значащих цифр: 1 + ε с ε ~ 1e−150 не должно округляться до 1 (log(1 + a²/x²), eˣ − 1)
           (cond ((equal? h '+) (dm-relk (foldl + 0 (map dm-ev as)) 200))
                 ((equal? h '*) (dm-relk (foldl * 1 (map dm-ev as)) 200))
                 ((equal? h 'exp)
                  (let ((v (dm-ev (car as))))
                    (cond ((> v 3000) (error "dm-ev: exp"))
                          ((< v -3000) 0)
                          (else (dm-exp v)))))
                 ((equal? h '^)
                  (let ((b (dm-ev (car as))) (q (dm-ev (cadr as))))
                    (cond ((integer? q) (dm-rel (^ b q)))
                          (else (if (<= b 0) (error "dm-ev: основание") (dm-fn1-pow b q))))))
                 ((and (equal? h 'sqrt) (= (length as) 1))
                  (let ((b (dm-ev (car as)))) (if (< b 0) (error "dm-ev: sqrt") (dm-sqrt b))))
                 ((and (member? h '(log sin cos tan atan)) (= (length as) 1)) (dm-fn1 h (dm-ev (car as))))
                 (else (error "dm-ev: операция" h)))))))

; √q с относительной точностью ~10^-(D+15): целый корень от q·10^(2k)
(define (dm-sqrt q)
  (if (= q 0)
      0
      (let* ((e (- (dm-ndig (numer q)) (dm-ndig (denom q)))) (k (- (+ dm-D 15) (quotient e 2))) (s (^ 10 (* 2 k))))
        (/ (interval::iv-isqrt (floor (* q s))) (^ 10 k)))))

; b^q, b > 0, q рациональное нецелое: знаменатель 2 — через √, иначе exp(q·ln b)
(define (dm-fn1-pow b q)
  (if (= (denom q) 2)
      (let ((r (dm-sqrt b))) (dm-rel (^ r (numer q))))
      (let ((lb (dm-fn1 'log b)))
        (let ((v (* q lb)))
          (cond ((> v 3000) (error "dm-ev: степень"))
                ((< v -3000) 0)
                (else (dm-exp v)))))))

(define (dm-f f x xv pv)
  (try (dm-ev (dm-sub f (cons (list x xv) pv))) (lambda (e) #f)))

(define (dm-fl q) (try (* 1.0 q) (lambda (e) #f)))
(define (dm-fin? v) (and (number? v) (< (abs v) 1e300)))

; узлы: kind 'fin (lo hi), 'half (L s: x = L + s·y, y∈[0,∞)), 'full (±y)
; i — индекс при шаге 1/32; результат — список (x . вес)
(define (dm-nodes kind a b i)
  (let* ((t (/ (abs i) 64)) (et (dm-exp t)) (sh (/ (- et (/ 1 et)) 2)) (ch (/ (+ et (/ 1 et)) 2))
         (u (* (/ dm-pi 2) sh)))
    (cond ((equal? kind 'fin)
           (let ((r (/ (- b a) 2)))
             (if (= i 0)
                 (list (cons (/ (+ a b) 2) (* r (/ dm-pi 2))))
                 (let* ((E (dm-exp (* 2 u))) (d (dm-rel (/ (* 2 r) (+ E 1)))) (w (dm-rel (/ (* (/ dm-pi 2) ch r 4 E) (* (+ E 1) (+ E 1))))))
                   (list (cons (if (> i 0) (- b d) (+ a d)) w))))))
          (else
           (let* ((uu (if (< i 0) (- 0 u) u)) (y (dm-exp uu)) (w (dm-rel (* y (/ dm-pi 2) ch))))
             (if (equal? kind 'half)
                 (list (cons (+ a (* b y)) (* (abs b) w)))
                 (list (cons (* b y) (* b w)) (cons (- 0 (* b y)) (* b w)))))))))

; сумма w·f по узлу; screen — отсечение по float (только полуось/прямая); #f — ошибка вычисления
(define (dm-term f x pv kind a b i)
  (let ((pts (dm-nodes kind a b i)))
    (let loop ((ps pts) (acc 0))
      (if (null? ps)
          (dm-rel acc)
          ; float-отсечение «член мал» НЕ используется: потеря точности float даёт ложный нуль (log(1+e^−x) при x > 37)
          (let* ((xv (car (car ps))) (w (cdr (car ps)))
                 (v (dm-f f x xv pv)))
            (if (not v)
                #f
                (loop (cdr ps) (+ acc (* w v)))))))))

(define dm-imax 400)

; сумма элементов списка с номерами (1-based) кратными k
(define (dm-sum-every l k)
  (let loop ((l l) (j 1) (acc 0))
    (cond ((null? l) acc)
          ((= (remainder j k) 0) (loop (cdr l) (+ j 1) (+ acc (car l))))
          (else (loop (cdr l) (+ j 1) acc)))))

; (dm-quad f x pv kind a b) → (S S′): S — сумма при h = 1/32 (S′ при 1/16) или, если уровни ещё расходятся, при h = 1/64 (S′ при 1/32)
; узлы — индексы i при шаге 1/64; первый проход — чётные i; хвост считается сошедшимся после трёх мелких членов подряд
(define (dm-quad f x pv kind a b)
  (let* ((eps (dm-pow10 (+ dm-D 5))) (tailtol (dm-pow10 dm-target))
         (side (lambda (sgn)
                 (let loop ((i 2) (small 0) (acc '()) (last 0))
                   (if (> i dm-imax)
                       (cons (reverse acc) last)
                       (let ((tm (dm-term f x pv kind a b (* sgn i))))
                         (set! dm-stats-nodes (+ dm-stats-nodes 1))
                         (cond ((not tm) #f)
                               ((and (< (abs tm) eps) (>= small 2)) (cons (reverse (cons 0 acc)) 0))
                               (else (loop (+ i 2) (if (< (abs tm) eps) (+ small 1) 0) (cons tm acc) tm))))))))
         (odd (lambda (sgn n)
                (let loop ((j 0) (acc 0))
                  (if (>= j n)
                      acc
                      (let ((tm (dm-term f x pv kind a b (* sgn (+ (* 2 j) 1)))))
                        (set! dm-stats-nodes (+ dm-stats-nodes 1))
                        (and tm (loop (+ j 1) (+ acc tm)))))))))
    (let ((t0 (dm-term f x pv kind a b 0)))
      (and t0
           (let ((pos (side 1)) (neg (side -1)))
             (and pos neg
                  (< (abs (cdr pos)) tailtol) (< (abs (cdr neg)) tailtol)
                  (let* ((lp (car pos)) (ln (car neg))
                         (s5 (/ (+ t0 (dm-sum-every lp 1) (dm-sum-every ln 1)) 32))
                         (s4 (/ (+ t0 (dm-sum-every lp 2) (dm-sum-every ln 2)) 16)))
                    (if (< (abs (- s5 s4)) (* (dm-pow10 12) (+ 1 (abs s5))))
                        (list s5 s4)
                        (let ((op (odd 1 (length lp))) (on (odd -1 (length ln))))
                          (and op on
                               (list (/ (+ t0 (dm-sum-every lp 1) (dm-sum-every ln 1) op on) 64) s5)))))))))))

; значение интеграла при числовых параметрах pv: (значение . оценка погрешности) | #f
; scale — масштаб узлов на полуоси/прямой (другой набор узлов, для независимой сверки)
(define (dm-integral1 f x lo hi pv scale)
  (let* ((lo-inf (equal? lo '-inf)) (hi-inf (equal? hi 'inf))
         (kind (cond ((and lo-inf hi-inf) 'full) ((or lo-inf hi-inf) 'half) (else 'fin)))
         (a (cond ((and lo-inf hi-inf) 0) (hi-inf lo) (lo-inf hi) (else lo)))
         (b (cond ((and lo-inf hi-inf) scale) (hi-inf scale) (lo-inf (- 0 scale)) (else hi)))
         (r (dm-quad f x pv kind a b)))
    (and r
         (let ((err (abs (- (car r) (cadr r)))))
           ; удвоение узлов возводит погрешность в квадрат: расхождение уровней 1/16 и 1/32 ≤ 1e-12 ⇒ значение ≈ 1e-24
           (and (< err (* (dm-pow10 12) (+ 1 (abs (car r))))) (cons (car r) err))))))
(define (dm-integral f x lo hi pv) (dm-integral1 f x lo hi pv 1))

; независимая сверка: другой набор узлов (полуось/прямая — масштаб 2; отрезок — разбиение пополам)
(define (dm-integral-alt f x lo hi pv)
  (if (or (int-inf? lo) (int-inf? hi))
      (dm-integral1 f x lo hi pv 2)
      (let* ((m (/ (+ lo hi) 2)) (p (dm-integral1 f x lo m pv 1)) (q (dm-integral1 f x m hi pv 1)))
        (and p q (cons (+ (car p) (car q)) 0)))))

; ---------- константы и PSLQ ----------
(define (dm-enc e) (let ((X (const-enclosure e dm-D))) (and X (iv-mid X))))

(define (dm-zeta3)
  (let loop ((n 1) (acc 0) (cb 2))                    ; cb = C(2n, n)
    (if (> n 120)
        (* 5/2 acc)
        (loop (+ n 1) (+ acc (/ (if (odd? n) 1 -1) (* n n n cb)))
              (/ (* cb (* 2 (+ (* 2 n) 1)) ) (+ n 1) 1)))))

(define (dm-catalan)
  (let loop ((n 0) (acc 0) (cb 1))
    (if (> n 120)
        (+ (* (/ dm-pi 8) (dm-enc '(log (+ 2 (sqrt 3))))) (* 3/8 acc))
        (loop (+ n 1) (+ acc (/ 1 (* (+ (* 2 n) 1) (+ (* 2 n) 1) cb)))
              (/ (* cb 2 (+ (* 2 n) 1)) (+ n 1))))))

; Брент — Макмиллан: γ ≈ A/B − log n, ошибка ~ e^{−4n}
(define (dm-euler)
  (let* ((n 30) (ln (dm-enc (list 'log n))))
    (let loop ((k 0) (a 1) (H 0) (A 0) (B 0))
      (if (> k 140)
          (- (/ A B) ln)
          (let* ((Hk (if (= k 0) 0 (+ H (/ 1 k)))) (ak (if (= k 0) 1 (* a (/ (* n n) (* k k))))))
            (loop (+ k 1) ak Hk (+ A (* ak Hk)) (+ B ak)))))))

; Γ(1/4) = √(2ϖ)·(2π)^{1/4}, ϖ = π/agm(1, √2)
(define (dm-gamma14)
  (let loop ((k 0) (a 1) (b (dm-fn1 'sqrt 2)))
    (if (>= k 9)
        (let ((w (/ dm-pi a))) (* (dm-fn1 'sqrt (* 2 w)) (dm-fn1-pow (* 2 dm-pi) 1/4)))
        (loop (+ k 1) (dm-rel (/ (+ a b) 2)) (dm-fn1 'sqrt (dm-rel (* a b)))))))

(define dm-const-table '())    ; ((имя выражение значение) …)

(define (dm-build-table!)
  (set! dm-const-table
        (list (list 'pi 'pi dm-pi)
              (list 'sqrt-pi '(sqrt pi) (dm-enc '(sqrt pi)))
              (list 'pi2 '(^ pi 2) (dm-enc '(^ pi 2)))
              (list 'log2 '(log 2) (dm-enc '(log 2)))
              (list 'sqrt2 '(sqrt 2) (dm-enc '(sqrt 2)))
              (list 'sqrt3 '(sqrt 3) (dm-enc '(sqrt 3)))
              (list 'e '(exp 1) (dm-enc '(exp 1)))
              (list 'zeta3 '(zeta 3) (dm-zeta3))
              (list 'catalan 'catalan (dm-catalan))
              (list 'euler 'euler-gamma (dm-euler))
              (list 'gamma14 '(gamma 1/4) (dm-gamma14))
              (list 'pilog2 '(* pi (log 2)) (dm-enc '(* pi (log 2))))
              (list 'pisqrt2 '(* pi (sqrt 2)) (dm-enc '(* pi (sqrt 2))))
              (list 'pisqrt3 '(* pi (sqrt 3)) (dm-enc '(* pi (sqrt 3)))))))

(define (dm-tc name) (assoc name dm-const-table))

(define (dm-maxabs v) (foldl (lambda (a q) (max a (abs q))) 0 v))
(define (dm-dot r xs) (foldl + 0 (map2 * r xs)))

; PSLQ: рациональные xs → целый вектор или #f; принимается только короткое соотношение (n·lg(max|rᵢ|) ≤ 0.65·digits), невязка < 10^−(digits−4)
(define (dm-pslq xs digits)
  (let ((r (try (constzero::cz-pslq-run xs (+ digits 12) 600) (lambda (e) #f))))
    (and r (not (every? (lambda (a) (= a 0)) r))
         (< (abs (dm-dot r xs)) (dm-pow10 (- digits 4)))
         (<= (* (length xs) (/ (log (+ 1.0 (dm-maxabs r))) (log 10.0))) (* 0.65 digits))
         r)))

; мультипликативно: C = 2ᵃ3ᵇ5ᶜ7ᵈπᵉ (рациональные показатели, знаменатель ≤ 12); C > 0
(define (dm-recognize-mult C digits)
  (if (<= C 0)
      #f
      (let* ((names '(2 3 5 7 pi (gamma 1/4)))
             (lg (map (lambda (n) (cond ((equal? n 'pi) (dm-enc '(log pi)))
                                        ((pair? n) (dm-enc (list 'log (caddr (dm-tc 'gamma14)))))
                                        (else (dm-enc (list 'log n)))))
                      names))
             (r (dm-pslq (cons (dm-enc (list 'log C)) lg) digits)))
        (and r (not (= (car r) 0)) (<= (abs (car r)) 12)
             (let* ((m (car r))
                    (bases (map (lambda (n) (cond ((equal? n 'pi) dm-pi) ((pair? n) (caddr (dm-tc 'gamma14))) (else n))) names))
                    (parts (map2 (lambda (n c) (list '^ n (/ (- 0 c) m))) names (cdr r)))
                    (val (let loop ((bl bases) (cl (cdr r)) (acc 1))
                           (if (null? bl)
                               acc
                               (let ((e (/ (- 0 (car cl)) m)))
                                 (loop (cdr bl) (cdr cl)
                                       (cond ((= e 0) acc)
                                             ((integer? e) (dm-rel (* acc (^ (car bl) e))))
                                             (else (dm-rel (* acc (dm-fn1-pow (car bl) e)))))))))))
               (cons (simplify (cons '* (filter (lambda (p) (not (= (caddr p) 0))) parts))) val))))))

; рациональное: цепная дробь (знаменатель ≤ 10^6, невязка < 1e-19 — случайно такое не бывает)
(define (dm-recognize-rat C)
  (let loop ((x C) (p0 1) (q0 0) (p1 (floor C)) (q1 1) (k 0))
    (cond ((< (abs (- C (/ p1 q1))) (* (dm-pow10 19) (+ 1 (abs C)))) (cons (/ p1 q1) (/ p1 q1)))
          ((or (> q1 1000000) (> k 60) (= x (floor x))) #f)
          (else
           (let* ((r (/ 1 (- x (floor x)))) (a (floor r)))
             (loop r p1 q1 (+ (* a p1) p0) (+ (* a q1) q0) (+ k 1)))))))

; аддитивно: малые базисы; C·r₀ + Σ rᵢ·bᵢ = 0
(define dm-bases '((one) (pi) (sqrt-pi) (pi2) (log2) (sqrt2) (sqrt3) (e) (zeta3) (catalan) (euler)
                   (one pi) (one sqrt-pi) (one pi2) (one log2) (one sqrt2) (one sqrt3) (pi sqrt3)
                   (one euler) (pi log2) (one zeta3) (pi sqrt2) (one catalan)
                   (one pi log2) (pi pi2) (pi sqrt-pi) (pi euler) (one pi pi2) (pi catalan)
                   (log2 sqrt2) (one log2 sqrt2) (pilog2) (one pilog2) (pisqrt2) (pisqrt3) (one pisqrt3) (one pisqrt2)))
(define (dm-recognize-add C digits)
  (let loop ((bs dm-bases))
    (if (null? bs)
        #f
        (let* ((b (car bs))
               (xs (cons C (map (lambda (n) (if (equal? n 'one) 1 (caddr (dm-tc n)))) b)))
               (r (dm-pslq xs digits)))
          (if (and r (not (= (car r) 0)) (<= (abs (car r)) 60))
              (cons (simplify (cons '+ (map2 (lambda (n c) (list '* (/ (- 0 c) (car r)) (if (equal? n 'one) 1 (cadr (dm-tc n))))) b (cdr r))))
                    (foldl + 0 (map2 (lambda (x c) (* (/ (- 0 c) (car r)) x)) (cdr xs) (cdr r))))
              (loop (cdr bs)))))))

; ---------- вход ----------
(define dm-checks '((3/2 5/3 7/4 9/5) (2 3 1/2 5/2)))

(define (dm-lim-val L pv)   ; число | 'inf | '-inf | #f
  (cond ((or (equal? L 'inf) (equal? L '-inf)) L)
        (else (dm-enc (dm-sub L pv)))))

(define (dm-fail! why &rest detail) (set! dm-info (cons why detail)) #f)

(define (dm-params f a b x)
  (filter (lambda (s) (and (not (equal? s x)) (not (member? s dm-consts))))
          (append (const-free-syms f) (if (int-inf? a) '() (const-free-syms a)) (if (int-inf? b) '() (const-free-syms b)))))
(define (dm-uniq l) (let loop ((l l) (acc '())) (cond ((null? l) (reverse acc)) ((member? (car l) acc) (loop (cdr l) acc)) (else (loop (cdr l) (cons (car l) acc))))))

; (int-dimensional f x a b) → выражение | #f; причины отказа — (int-dimensional-info)
(define (int-dimensional f0 x a b) (dm-run f0 x a b #f))

; (int-dimensional-with f x a b ps u) — то же с НАВЯЗАННЫМИ весами u (показатели параметров ps в C·Πpᵢ^uᵢ): для тестов проверки (2)
(define (int-dimensional-with f0 x a b ps u) (dm-run f0 x a b (cons ps u)))

(define (dm-run f0 x a b forced)
  (set! dm-info '(none))
  (set! dm-stats-nodes 0)
  (let ((old (iv-precision)))
    (iv-set-precision! dm-D)
    (unwind-protect
      (try (dm-main f0 x a b forced) (lambda (err) (dm-fail! 'error (if (string? err) err 'exn))))
      (iv-set-precision! old))))

(define (dm-main f0 x a b forced)
  (set! dm-pi (iv-mid (iv-pi)))
  (if (null? dm-const-table) (dm-build-table!))
  (let* ((f (simplify (int-hyp f0)))
         (ps (dm-uniq (dm-params f a b x))) (k (length ps)) (vars (cons x ps)))
    (set! dm-cons '()) (set! dm-fail #f)
    (if forced
        (dm-with-weights f x a b (car forced) (cdr forced))
    (let* ((Wf (dm-w f))
           (_ (if (not (or (int-inf? a) (equal? a 0)))
                  (dm-con! (wf-sub (dm-w a) (list (cons x 1))))))
           (_ (if (not (or (int-inf? b) (equal? b 0)))
                  (dm-con! (wf-sub (dm-w b) (list (cons x 1))))))
           (cond-rows (map (lambda (c) (an-wvec c vars)) dm-cons)))
      (cond
        (dm-fail (dm-fail! 'weights "нет весовой формы"))
        ((or (> k 4) (not (every? (lambda (s) (symbol? s)) ps))) (dm-fail! 'groups "параметров > 4"))
        (else
         (let* ((WI (an-wvec (wf-add Wf (list (cons x 1))) vars))
                (Ws (if (null? cond-rows) (map (lambda (j) (map (lambda (i) (if (= i j) 1 0)) (range (+ k 1)))) (range (+ k 1)))
                        (dm-nullspace cond-rows (+ k 1))))
                (ss (map (lambda (w) (dm-dot WI w)) Ws))
                (u (dm-solve-u Ws ss k)))
           (cond ((equal? u 'groups) (dm-fail! 'groups (- k (- (length Ws) 0))))
                 ((equal? u 'inconsistent) (dm-fail! 'inconsistent))
                 (else (dm-with-weights f x a b ps u))))))))))

; выражение Π pᵢ^{uᵢ}
(define (dm-pexpr ps u)
  (cons '* (filter (lambda (e) e) (map2 (lambda (p v) (if (= v 0) #f (list '^ p v))) ps u))))

(define (dm-pv ps vals) (map2 list ps vals))

; Π pᵢ^{uᵢ} при числах pᵢ: рациональное приближение (D знаков)
(define (dm-prodval ps u vals)
  (dm-enc (cons '* (cons 1 (map2 (lambda (v e) (list '^ v e)) vals u)))))

(define (dm-with-weights f x a b ps u)
  (let* ((k (length ps)) (ones (map (lambda (p) 1) ps))
         (pv0 (dm-pv ps ones))
         (lo (dm-lim-val a pv0)) (hi (dm-lim-val b pv0)))
    (cond
      ((or (not lo) (not hi)) (dm-fail! 'limits))
      ((and (not (int-inf? a)) (not (int-inf? b)) (>= lo hi)) (dm-fail! 'limits))
      (else
       (let ((q0 (dm-integral f x lo hi pv0)))
         (cond
           ((not q0) (dm-fail! 'quad "нет сходимости (особенность, осцилляция или медленный хвост)"))
           (else
            (let* ((C (car q0)) (q1 (dm-integral-alt f x lo hi pv0)))
              (cond
                ((< (abs C) (dm-pow10 18)) (dm-fail! 'zero "значение ≈ 0 — не доказано"))
                ((not q1) (dm-fail! 'alt-quad))
                ((> (abs (- (car q1) C)) (* (dm-pow10 16) (+ 1 (abs C)))) (dm-fail! 'alt-mismatch (* 1.0 C) (* 1.0 (car q1))))
                (else
                 (let ((expr (or (dm-recognize-rat C) (dm-recognize-mult C 22) (dm-recognize-add C 22))))
                   (cond
                     ((not expr) (dm-fail! 'pslq (* 1.0 C)))
                     (else (dm-verify f x a b ps u expr C))))))))))))))

(define (dm-verify f x a b ps u rec C)
  (let ((expr (car rec)) (Cv (cdr rec)))
    (if (not (and Cv (< (abs (- Cv C)) (dm-pow10 18))))
        (dm-fail! 'pslq-mismatch)
        (let loop ((sets (if (null? ps) '() dm-checks)))
          (cond
            ((null? sets)
             (for-each (lambda (p) (record-condition (list '> p 0) "параметр положителен (численная проверка при p > 0)")) ps)
             (set! dm-info (list 'ok (* 1.0 C)))
             (simplify (list '* expr (dm-pexpr ps u))))
            (else
             (let* ((vals (dm-take (car sets) (length ps)))
                    (pv (dm-pv ps vals))
                    (lo (dm-lim-val a pv)) (hi (dm-lim-val b pv))
                    (q (and lo hi (dm-integral f x lo hi pv)))
                    (pred (and q (* Cv (dm-prodval ps u vals)))))
               (cond ((not q) (dm-fail! 'verify-quad))
                     ((< (abs (- (car q) pred)) (* (dm-pow10 18) (+ 1 (abs pred)))) (loop (cdr sets)))
                     (else (dm-fail! 'verify-weight (* 1.0 (car q)) (* 1.0 pred)))))))))))

(define (dm-take l n) (if (or (= n 0) (null? l)) '() (cons (car l) (dm-take (cdr l) (- n 1)))))
