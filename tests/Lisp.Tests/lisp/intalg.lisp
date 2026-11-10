; intalg.lisp — тесты шага A4.1a: целый базис и алгебраический Эрмит для y^n = P.

; сравнение по значению (формы / и ^ -1 равносильны)
(define (ia-eq? a b) (equal? (simplify (together (list '- a b))) 0))

; «не врёт»: integrate либо не взял (форма (integrate …)), либо ответ проходит сертификат
(define (ia-honest? e x)
  (let ((ans (integrate e x)))
    (or (and (pair? ans) (equal? (car ans) 'integrate))
        (int-check ans e x))))

(define (ia-basis P n)
  (car (radical-integral-basis P n 'x)))

(deftest "intalg: базис y² = x³"
  (let* ((P '(^ x 3)) (b (ia-basis P 2)))
    (assert-equal 2 (length b))
    (assert-equal 1 (nth b 0))
    (assert-true (ia-eq? (nth b 1) '(/ y x)))
    (assert-true (ia-eq? (cadr (radical-integral-basis P 2 'x)) '(* 4 x)))))

(deftest "intalg: базис y³ = x²(x+1)⁴ — сокращение n-х степеней"
  (let* ((P '(* (^ x 2) (^ (+ x 1) 4))) (b (ia-basis P 3)))
    (assert-true (ia-eq? (nth b 1) '(/ y (+ 1 x))))
    (assert-true (ia-eq? (nth b 2) '(/ (^ y 2) (* x (^ (+ 1 x) 2)))))
    (assert-true (integral-basis-check P 3 'x b))))

(deftest "intalg: базис y² = (x−1)(x+2)²"
  (let* ((P '(* (- x 1) (^ (+ x 2) 2))) (b (ia-basis P 2)))
    (assert-true (ia-eq? (nth b 1) '(/ y (+ 2 x))))
    (assert-true (integral-basis-check P 2 'x b))))

(deftest "intalg: базис y⁴ = x³"
  (let* ((P '(^ x 3)) (b (ia-basis P 4)))
    (assert-equal 4 (length b))
    (assert-true (ia-eq? (nth b 1) 'y))
    (assert-true (ia-eq? (nth b 2) '(/ (^ y 2) x)))
    (assert-true (ia-eq? (nth b 3) '(/ (^ y 3) (^ x 2))))
    (assert-true (integral-basis-check P 4 'x b))))

(deftest "intalg: сертификат всех четырёх базисов"
  (assert-true (integral-basis-check '(^ x 3) 2 'x (ia-basis '(^ x 3) 2)))
  (assert-true (integral-basis-check '(* (^ x 2) (^ (+ x 1) 4)) 3 'x
                                     (ia-basis '(* (^ x 2) (^ (+ x 1) 4)) 3)))
  (assert-true (integral-basis-check '(* (- x 1) (^ (+ x 2) 2)) 2 'x
                                     (ia-basis '(* (- x 1) (^ (+ x 2) 2)) 2)))
  (assert-true (integral-basis-check '(^ x 3) 4 'x (ia-basis '(^ x 3) 4))))

(deftest "intalg: подделка базиса — лишний множитель"
  ; d₁ = x(x+1) вместо x: целость нарушена
  (assert-equal #f (integral-basis-check '(^ x 3) 2 'x (list 1 '(/ y (* x (+ x 1)))))))

(deftest "intalg: подделка базиса — пропущенный множитель"
  ; d₁ = 1 вместо x: дискриминант больше
  (assert-equal #f (integral-basis-check '(^ x 3) 2 'x (list 1 'y))))

(deftest "intalg: Эрмит восстанавливает G, H = 0"
  (let* ((P '(+ (^ x 3) 1))
         (G0 '(/ y (+ (^ x 2) 1)))
         (A (integrate::alg-der-e G0 P 2 'x))
         (R (alg-hermite-reduce A P 2 'x)))
    (assert-true (list? R))
    (assert-equal 0 (simplify (cadr R)))
    (assert-true (ia-eq? (car R) G0))))

(deftest "intalg: Эрмит с H ≠ 0, сертификат G′ + H = A"
  (let* ((P '(+ (^ x 3) 1))
         (A (together '(/ (* x y) (^ (+ (^ x 2) 1) 2))))
         (R (alg-hermite-reduce A P 2 'x)))
    (assert-true (list? R))
    (assert-true (not (equal? (simplify (cadr R)) 0)))
    (assert-equal 0 (simplify (together
                               (list '- (list '+ (integrate::alg-der-e (car R) P 2 'x)
                                              (cadr R))
                                     A))))))

(deftest "intalg: подделка G — смещённый коэффициент отвергается сертификатом"
  (let* ((P '(+ (^ x 3) 1))
         (G0 '(/ y (+ (^ x 2) 1)))
         (A (integrate::alg-der-e G0 P 2 'x))
         (fake '(/ (* 2 y) (+ (^ x 2) 1))))
    ; G′ − A ≠ 0: испорченный ответ не проходит сертификат
    (assert-true (not (equal? (simplify (together (list '- (integrate::alg-der-e fake P 2 'x) A))) 0)))))

(deftest "intalg: integrate берёт алгебраическую производную"
  (let* ((P '(+ (^ x 3) 1))
         (A (integrate::alg-der-e '(/ y (+ (^ x 2) 1)) P 2 'x))
         (e (integrate::alg-rad-back A P 2))
         (ans (integrate e 'x)))
    (assert-true (not (and (pair? ans) (equal? (car ans) 'integrate))))
    (assert-true (int-check ans e 'x))
    (assert-true (ia-eq? ans '(/ (^ (+ (^ x 3) 1) 1/2) (+ (^ x 2) 1))))))

(deftest "intalg: 1/√(x³+x+1) — integrate не даёт неверного ответа"
  (assert-true (ia-honest? '(/ 1 (^ (+ (^ x 3) x 1) 1/2)) 'x)))

(deftest "intalg: (3x²)/(2√(x³+1)) — ответ только с проверкой"
  (assert-true (ia-honest? '(/ (* 3 (^ x 2)) (* 2 (^ (+ (^ x 3) 1) 1/2))) 'x)))

; ---------- A4.1b: точки ветвления (V | P) ----------

; равенство нулю в ℚ(x)(y), y^n = P (нормализация по y^n = P)
(define (ia-field-zero? e P n)
  (equal? (simplify (integrate::alg-normalize (together e) P n 'x)) 0))

(deftest "intalg: Эрмит при V | P — G = √(x³+1)/(x+1), H = 0"
  (let* ((P '(+ (^ x 3) 1))
         (G0 '(/ y (+ x 1)))
         (A (integrate::alg-der-e G0 P 2 'x))
         (R (alg-hermite-reduce A P 2 'x)))
    (assert-true (list? R))
    (assert-equal 0 (simplify (cadr R)))
    (assert-true (ia-eq? (car R) G0))))

(deftest "intalg: Эрмит при V | P — кубический радикал, G = ∛(x²(x−1))/x²"
  (let* ((P '(* (^ x 2) (- x 1)))
         (G0 '(/ y (^ x 2)))
         (A (integrate::alg-der-e G0 P 3 'x))
         (R (alg-hermite-reduce A P 3 'x)))
    (assert-true (list? R))
    (assert-equal 0 (simplify (cadr R)))
    (assert-true (ia-eq? (car R) G0))))

(deftest "intalg: Эрмит при V | P — y² = x(x−1)(x+2), G = y/(x(x−1))"
  (let* ((P '(* x (- x 1) (+ x 2)))
         (G0 '(/ y (* x (- x 1))))
         (A (integrate::alg-der-e G0 P 2 'x))
         (R (alg-hermite-reduce A P 2 'x)))
    (assert-true (list? R))
    (assert-equal 0 (simplify (cadr R)))
    (assert-true (ia-eq? (car R) G0))))

(deftest "intalg: ∫dx/((x+1)²√(x³+1)) — H ≠ 0 и G′ + H = A в поле"
  (let* ((P '(+ (^ x 3) 1))
         (A (together '(/ 1 (* (^ (+ x 1) 2) y))))
         (R (alg-hermite-reduce A P 2 'x)))
    (assert-true (list? R))
    (assert-true (not (equal? (simplify (cadr R)) 0)))
    (assert-true (ia-field-zero?
                  (list '- (list '+ (integrate::alg-der-e (car R) P 2 'x) (cadr R)) A)
                  P 2))))

(deftest "intalg: стратегия отказывается при H ≠ 0 (точка ветвления)"
  (let ((e '(/ 1 (* (^ (+ x 1) 2) (^ (+ 1 (^ x 3)) 1/2)))))
    (assert-equal #f (integrate::alg-int-strategy e 'x 0))))

(deftest "intalg: подделка G при V | P отвергается сертификатом"
  (let* ((P '(+ (^ x 3) 1))
         (G0 '(/ y (+ x 1)))
         (A (integrate::alg-der-e G0 P 2 'x))
         (fake '(/ (* 2 y) (+ x 1))))
    (assert-true (not (ia-field-zero? (list '- (integrate::alg-der-e fake P 2 'x) A) P 2)))))

(deftest "intalg: integrate берёт производную с точкой ветвления"
  (let* ((P '(+ (^ x 3) 1))
         (A (integrate::alg-der-e '(/ y (+ x 1)) P 2 'x))
         (e (integrate::alg-rad-back A P 2))
         (ans (integrate e 'x)))
    (assert-true (not (and (pair? ans) (equal? (car ans) 'integrate))))
    (assert-true (int-check ans e 'x))
    (assert-true (ia-eq? ans '(/ (^ (+ (^ x 3) 1) 1/2) (+ x 1))))))

(deftest "intalg: √(x³+1) и 1/√(x³+x+1) — без неверных ответов"
  (assert-true (ia-honest? '(^ (+ (^ x 3) 1) 1/2) 'x))
  (assert-true (ia-honest? '(/ 1 (^ (+ (^ x 3) x 1) 1/2)) 'x)))

; ---------- A4.3r: полюсы на ∞ и вердикт первого рода ----------

; доказанная неэлементарность, записанная в канал условий: полным integrate и
; прямым вызовом нашей стратегии (у Чебышёва свои отказы — их не смешиваем)
(define (ia-ne? e x whole)
  (conditions-clear)
  (if whole (integrate e x) (integrate::alg-int-strategy e x 0))
  (any? (lambda (c) (equal? (car (car c)) 'risch-nonelementary)) (conditions)))

(deftest "intalg: A4.3r — полюс на ∞ снимается, ответ — производная"
  (assert-true (ia-eq? (integrate '(/ (* 3 (^ x 2)) (* 2 (^ (+ (^ x 3) 1) 1/2))) 'x)
                       '(^ (+ (^ x 3) 1) 1/2)))
  (assert-true (ia-eq? (integrate '(/ (+ (* 5 (^ x 3)) 2) (* 2 (^ (+ (^ x 3) 1) 1/2))) 'x)
                       '(* x (^ (+ (^ x 3) 1) 1/2))))
  (assert-true (ia-eq? (integrate '(/ (* 5 (^ x 4)) (* 2 (^ (+ (^ x 5) 1) 1/2))) 'x)
                       '(^ (+ (^ x 5) 1) 1/2)))
  (assert-true (ia-eq? (integrate '(/ (^ x 2) (^ (+ (^ x 3) 1) 2/3)) 'x)
                       '(^ (+ (^ x 3) 1) 1/3))))

(deftest "intalg: A4.3r — голоморфный остаток H ≠ 0: доказанная неэлементарность"
  (assert-true (ia-ne? '(/ 1 (^ (+ (^ x 3) x 1) 1/2)) 'x #f))
  (assert-true (ia-ne? '(/ 1 (^ (+ (^ x 4) 1) 1/2)) 'x #f))
  (assert-true (ia-ne? '(/ 1 (^ (+ (^ x 5) 1) 1/2)) 'x #f))
  (assert-true (ia-ne? '(/ x (^ (+ (^ x 5) 1) 1/2)) 'x #f))
  (assert-true (ia-ne? '(/ 1 (^ (+ (^ x 3) x 1) 1/2)) 'x #t)))

(deftest "intalg: A5.4c — x²/√(x⁵+1) — 2-й род, доказанная неэлементарность"
  (assert-true (ia-ne? '(/ (^ x 2) (^ (+ (^ x 5) 1) 1/2)) 'x #f))
  ; чистый вердикт 1-го рода (без A5.4c) по-прежнему unknown
  (assert-equal 'unknown (integrate::alg-integrate-verdict (together '(/ (^ x 2) y))
                                                           '(+ (^ x 5) 1) 2 'x)))

(deftest "intalg: A4.3r — alg-integrate-verdict: elementary / nonelementary / unknown"
  (let ((P '(+ (^ x 5) 1))
        (P3 '(+ (^ x 3) 1)))
    (assert-equal 'nonelementary
                  (car (integrate::alg-integrate-verdict (together '(/ 1 y)) P 2 'x)))
    (assert-equal 'unknown
                  (integrate::alg-integrate-verdict (together '(/ (^ x 2) y)) P 2 'x))
    (assert-equal 'elementary
                  (car (integrate::alg-integrate-verdict
                        (integrate::alg-der-e (together '(/ y (+ x 1))) P3 2 'x) P3 2 'x)))))

(deftest "intalg: A4.3r — подделка H с полюсом отвергается проверкой голоморфности"
  (assert-equal #f (integrate::alg-holomorphic? (together '(/ 1 (+ (^ x 3) x 1)))
                                                '(+ (^ x 3) x 1) 2 'x))
  (assert-equal #f (integrate::alg-holomorphic? (together '(/ 1 (+ x 1))) '(+ (^ x 3) 1) 2 'x))
  (assert-equal #t (integrate::alg-holomorphic? (together '(/ y (+ (^ x 3) x 1)))
                                                '(+ (^ x 3) x 1) 2 'x)))

; ---------- A4.3: общий базис A4.2 и полная M ----------

(deftest "intalg: A4.3 — M квартики: E = x+x², w′E = M·w"
  (let* ((F '(+ (^ y 4) (* -4 x (^ y 2)) (* -2 (^ y 2)) 1))
         (b (integral-basis F 'x 'y))
         (ME (alg-basis-M-general b F 4 'x 'y))
         (M (car ME)) (E (cdr ME)))
    (assert-equal 4 (length b))
    (assert-true (ia-eq? E '(+ x (^ x 2))))
    (assert-true
     (every? (lambda (i)
               (equal? 0 (simplify (integrate::alg-g-expr
                                    (integrate::alg-g-nf
                                     (together (list '- (list '* E (integrate::alg-g-expr
                                                                     (integrate::alg-g-der (nth b i) F 4 'x 'y) 'y))
                                                           (cons '+ (map2 (lambda (m w) (list '* m w))
                                                                          (map (lambda (r) (nth r i)) M) b))))
                                     F 4 'x 'y)
                                    'y))))
             (range 4)))))

(deftest "intalg: A4.3 — Эрмит в общем базисе и согласие с A4.1b"
  (let* ((F '(+ (^ y 4) (* -4 x (^ y 2)) (* -2 (^ y 2)) 1))
         (G0 '(/ y (+ x 1)))
         (A (integrate::alg-g-expr (integrate::alg-g-der G0 F 4 'x 'y) 'y))
         (R (alg-hermite-reduce-general A F 'x 'y))
         (P '(+ (^ x 3) 1))
         (F2 '(- (^ y 2) (+ (^ x 3) 1)))
         (A2 (integrate::alg-g-expr (integrate::alg-g-der G0 F2 2 'x 'y) 'y))
         (R2 (alg-hermite-reduce-general A2 F2 'x 'y))
         (R3 (alg-hermite-reduce A2 P 2 'x)))
    (assert-true (list? R))
    (assert-equal 0 (simplify (cadr R)))
    (assert-true (ia-eq? (car R) G0))
    (assert-equal 0 (simplify (cadr R2)))
    (assert-true (ia-eq? (car R2) (car R3)))))

(deftest "intalg: A4.3 — ∞ общего вида: A = d/dx(y/x) → G = y/x, H = 0"
  (let* ((F '(- (^ y 2) (+ (^ x 3) 1)))
         (G0 '(/ y x))
         (A (integrate::alg-g-expr (integrate::alg-g-der G0 F 2 'x 'y) 'y))
         (R (alg-hermite-at-infinity-general A F 'x 'y)))
    (assert-true (list? R))
    (assert-equal 0 (simplify (cadr R)))
    (assert-true (ia-eq? (car R) G0))))

(deftest "intalg: A4.3 — вердикт на общей кривой рода 1"
  (let* ((F '(- (^ (- y x) 2) (* x (- x 1) (- x 2))))
         (v (alg-integrate-verdict-general '(/ 1 (- y x)) F 'x 'y)))
    (assert-true (pair? v))
    (assert-equal 'nonelementary (car v))))

(deftest "intalg: A4.3 — два радикала: ∫d/dx((√x+√(x+1))/x) = (√x+√(x+1))/x"
  (let* ((e (diff 'x '(/ (+ (^ x 1/2) (^ (+ x 1) 1/2)) x)))
         (ans (integrate e 'x)))
    (assert-true (and ans (int-check ans e 'x)))))

(deftest "intalg: A5.7 — два радикала через integrate: логарифмический ответ"
  ; H = d/dx log((y²−2y−1)/(y²+2y−1)), y = √x + √(x+1) — кривая A5.5;
  ; A5.7: быстрый вход в alg-int-two (два различных радикала) + гейт перед
  ; ∞-Эрмитом, когда H·dx на ∞ голоморфен (иначе шаг падал и integrate висел)
  (let* ((F2 (expand '(- (^ (- (^ y 2) (* 2 x) 1) 2) (* 4 x (+ x 1)))))
         (u '(/ (- (^ y 2) (* 2 y) 1) (+ (^ y 2) (* 2 y) -1)))
         (H (simplify (list '/ (integrate::alg-g-expr
                                (integrate::alg-g-der u F2 4 'x 'y) 'y) u)))
         (e (simplify (subst (list (list 'y '(+ (^ x 1/2) (^ (+ x 1) 1/2)))) H)))
         (ans (integrate e 'x)))
    ; ответ — не невычисленная форма, сертификат производной проходит
    (assert-true (not (and (pair? ans) (equal? (car ans) 'integrate))))
    (assert-true (int-check ans e 'x))))

(deftest "intalg: R1.1 — кубика через integrate: nonelementary с причиной"
  ; (y−x)² = x(x−1)(x−2), H = 1/x − 1/(x−1) + 1/(y−x), y−x = √(x(x−1)(x−2)).
  ; Раньше elliptic-f давал частичный ответ; теперь вердикт gv-log-part
  ; (модель y² − P) доходит до верхнего уровня — невычисленная форма + условие.
  (let ((e '(+ (/ 1 x) (/ -1 (- x 1))
               (/ 1 (^ (* x (- x 1) (- x 2)) 1/2)))))
    (conditions-clear)
    (let ((a (integrate e 'x)))
      (assert-true (and (pair? a) (equal? (car a) 'integrate)))
      (assert-true (any? (lambda (c)
                           (and (pair? (car c))
                                (equal? (car (car c)) 'risch-nonelementary)
                                (equal? (cadr (car c)) a)))
                         (conditions))))))

(deftest "intalg: R1.3 — integrate n=3: логарифм ∛(x³+1)−1"
  ; x²/(y²(y−1)), y = ∛(x³+1): ответ log(y−1)
  (let ((e '(/ (^ x 2) (* (^ (+ (^ x 3) 1) 2/3)
                          (- (^ (+ (^ x 3) 1) 1/3) 1)))))
    (assert-equal '(log (+ -1 (^ (+ 1 (^ x 3)) 1/3)))
                  (simplify (integrate e 'x)))))
