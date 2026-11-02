; intdiv.lisp — тесты шага A5.1: места, ряды, вычеты гиперэллиптической кривой y² = P(x).

(define (idv-eq? a b) (equal? (simplify (together (list '- a b))) 0))

(define (idv-k-eq? a b) (dv-k-eq? a b))

(define (idv-place-eq? p q) (dv-place-eq? p q))

(define (idv-res-of pl res)
  (let loop ((rs res))
    (cond ((null? rs) #f)
          ((idv-place-eq? pl (car (car rs))) (cdr (car rs)))
          (else (loop (cdr rs))))))

(define (idv-dav) '(+ (^ x 4) (* 10 (^ x 2)) (* -96 x) -71))

(deftest "intdiv: места над 0 у y² = x³ + 1"
  (let* ((P '(+ (^ x 3) 1))
         (pls (hyp-places P 'x 0))
         (b (integrate::ib-k-sqrt-rat 1)))
    (assert-equal 2 (length pls))
    (assert-equal 0 (car (nth pls 0)))
    (assert-true (idv-k-eq? (cadr (nth pls 0)) b))
    (assert-true (idv-k-eq? (cadr (nth pls 1)) (integrate::ib-k-scale b -1)))))

(deftest "intdiv: место ветвления и точки над ∞"
  (assert-equal '((-1 ram)) (hyp-places '(+ (^ x 3) 1) 'x -1))
  (assert-equal '((inf ram)) (hyp-places '(+ (^ x 3) 1) 'x 'inf))
  (let* ((pls (hyp-places '(+ (^ x 4) 1) 'x 'inf))
         (b (integrate::ib-k-sqrt-rat 1)))
    (assert-equal 2 (length pls))
    (assert-equal 'inf (car (nth pls 0)))
    (assert-true (idv-k-eq? (cadr (nth pls 0)) b))
    (assert-true (idv-k-eq? (cadr (nth pls 1)) (integrate::ib-k-scale b -1)))))

(deftest "intdiv: ряд в гладком месте удовлетворяет y² = P(x)"
  (let* ((P '(+ (^ x 3) 1))
         (sers (hyp-place-series (list 0 (integrate::ib-k-sqrt-rat 1)) P 'x 9))
         (xs (car sers))
         (ys (cdr sers)))
    (assert-equal '((1 (() . 1))) (integrate::dv-ser-clean xs))
    (assert-true (integrate::dv-ser-null?
                  (integrate::dv-ser-sub (integrate::dv-ser-mul ys ys 9)
                                         (integrate::dv-ser-peval
                                          (integrate::ib-poly-parse P 'x) xs 9))))))

(deftest "intdiv: ряд в точке ветвления удовлетворяет y² = P(x)"
  (let* ((P '(+ (^ x 3) 1))
         (sers (hyp-place-series (list -1 'ram) P 'x 8))
         (xs (car sers))
         (ys (cdr sers)))
    (assert-equal '((0 (() . -1)) (2 (() . 1))) (integrate::dv-ser-clean xs))
    (assert-true (integrate::dv-ser-null?
                  (integrate::dv-ser-sub (integrate::dv-ser-mul ys ys 8)
                                         (integrate::dv-ser-peval
                                          (integrate::ib-poly-parse P 'x) xs 8))))))

(deftest "intdiv: ряд на ∞ (нечётная и чётная степень) удовлетворяет y² = P(x)"
  (let* ((P '(+ (^ x 3) 1))
         (sers (hyp-place-series (list 'inf 'ram) P 'x -4))
         (xs (car sers))
         (ys (cdr sers)))
    (assert-true (integrate::dv-ser-null?
                  (integrate::dv-ser-sub (integrate::dv-ser-mul ys ys -4)
                                         (integrate::dv-ser-peval
                                          (integrate::ib-poly-parse P 'x) xs -4)))))
  (let* ((P '(+ (^ x 4) 1))
         (sers (hyp-place-series (list 'inf (integrate::ib-k-sqrt-rat 1)) P 'x -3))
         (xs (car sers))
         (ys (cdr sers)))
    (assert-true (integrate::dv-ser-null?
                  (integrate::dv-ser-sub (integrate::dv-ser-mul ys ys -3)
                                         (integrate::dv-ser-peval
                                          (integrate::ib-poly-parse P 'x) xs -3))))))

(deftest "intdiv: dv-sqrt-series — квадрат ряда равен 1 + u до порядка N"
  (let* ((u '((1 (() . 1)) (3 (() . 1))))
         (s (dv-sqrt-series u 8))
         (s2 (integrate::dv-ser-mul s s 8))
         (rhs (integrate::dv-ser-add '((0 (() . 1))) u)))
    (assert-true (integrate::dv-ser-null? (integrate::dv-ser-sub s2 rhs)))
    (assert-true (dv-k-eq? (integrate::dv-ser-ref s 0) (integrate::dv-k-rat 1)))
    (assert-equal '((() . 1/2)) (integrate::dv-ser-ref s 1))
    (assert-equal '((() . 9/16)) (integrate::dv-ser-ref s 3))))

(deftest "intdiv: вычеты 1/(x·y), y² = x³ + 1 — ±1, сертификат"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ 1 (* x y)))
         (res (hyp-residues H P 'x))
         (b (integrate::ib-k-sqrt-rat 1)))
    (assert-equal 2 (length res))
    (assert-true (idv-k-eq? (idv-res-of (list 0 b) res) (integrate::dv-k-rat 1)))
    (assert-true (idv-k-eq? (idv-res-of (list 0 (integrate::ib-k-scale b -1)) res)
                            (integrate::dv-k-rat -1)))
    (assert-true (hyp-residues-check H P 'x res))
    (assert-true (idv-eq? (hyp-residue-poly H P 'x 't)
                          '(+ (* -729 (^ t 6)) (* 729 (^ t 8)))))))

(deftest "intdiv: вычеты y/(x(x⁸+1)), y² = x⁸ + 1 — ±1 (Бронштейн, пр. 4)"
  (let* ((P '(+ (^ x 8) 1))
         (H '(/ y (* x (+ (^ x 8) 1))))
         (res (hyp-residues H P 'x))
         (b (integrate::ib-k-sqrt-rat 1)))
    (assert-equal 2 (length res))
    (assert-true (idv-k-eq? (idv-res-of (list 0 b) res) (integrate::dv-k-rat 1)))
    (assert-true (idv-k-eq? (idv-res-of (list 0 (integrate::ib-k-scale b -1)) res)
                            (integrate::dv-k-rat -1)))
    (assert-true (hyp-residues-check H P 'x res))
    (assert-true (idv-eq? (hyp-residue-poly H P 'x 't)
                          '(+ (* -281474976710656 (^ t 16))
                              (* 281474976710656 (^ t 18)))))))

(deftest "intdiv: вычетов нет — x·y/(1 − x³), R = 729t⁶ (Бронштейн, пр. 5)"
  (let* ((P '(+ 1 (* -1 (^ x 3))))
         (H '(/ (* x y) (+ 1 (* -1 (^ x 3)))))
         (res (hyp-residues H P 'x)))
    (assert-equal '() res)
    (assert-true (hyp-residues-check H P 'x res))
    (assert-true (idv-eq? (hyp-residue-poly H P 'x 't) '(* 729 (^ t 6))))))

(deftest "intdiv: Давенпорт, x/y — вычеты ±1 на ∞"
  (let* ((P (idv-dav))
         (res (hyp-residues '(/ x y) P 'x))
         (b (integrate::ib-k-sqrt-rat 1)))
    (assert-equal 2 (length res))
    (assert-true (idv-k-eq? (idv-res-of (list 'inf b) res) (integrate::dv-k-rat -1)))
    (assert-true (idv-k-eq? (idv-res-of (list 'inf (integrate::ib-k-scale b -1)) res)
                            (integrate::dv-k-rat 1)))
    (assert-true (hyp-residues-check '(/ x y) P 'x res))))

(deftest "intdiv: вычет в простом полюсе сводится к (c₀(a) ± c₁(a)b)/D′(a)"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ 1 (* (- x 2) y)))
         (r3 (hyp-residue (list 2 (integrate::ib-k-sqrt-rat 9)) H P 'x)))
    (assert-true (idv-k-eq? r3 (integrate::dv-k-rat 1/3)))
    (assert-true (idv-k-eq? (hyp-residue
                             (list 2 (integrate::ib-k-scale (integrate::ib-k-sqrt-rat 9) -1))
                             H P 'x)
                            (integrate::dv-k-rat -1/3)))))

(deftest "intdiv: вычет в точке ветвления — 2·c₀(a)/D′(a)"
  ; dx/(x+1) на y² = x³ + 1: x + 1 = t², ряд = 2 dt/t, вычет 2; и Σ по всем местам = 0
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ 1 (+ x 1)))
         (res (hyp-residues H P 'x)))
    (assert-equal 2 (length res))
    (assert-true (idv-k-eq? (idv-res-of (list -1 'ram) res) (integrate::dv-k-rat 2)))
    (assert-true (idv-k-eq? (idv-res-of (list 'inf 'ram) res) (integrate::dv-k-rat -2)))))

(deftest "intdiv: подделка вычета ловится сертификатом"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ 1 (* x y)))
         (res (hyp-residues H P 'x))
         (bad (cons (cons (car (car res)) (integrate::ib-k-add (cdr (car res))
                                                              (integrate::dv-k-rat 1)))
                    (cdr res))))
    (assert-true (hyp-residues-check H P 'x res))
    (assert-true (not (hyp-residues-check H P 'x bad)))))

(deftest "intdiv: нормирования x, y, x/y"
  (let* ((P '(+ (^ x 3) 1))
         (pl (list 0 (integrate::ib-k-sqrt-rat 1))))
    (assert-equal 1 (hyp-valuation pl 'x P 'x))
    (assert-equal 0 (hyp-valuation pl 'y P 'x))
    (assert-equal 1 (hyp-valuation pl '(/ x y) P 'x))
    (assert-equal -1 (hyp-valuation pl '(/ y x) P 'x))
    (assert-equal 1 (hyp-valuation pl '(/ (* 2 x) (+ 3 x)) P 'x)))
  ; нечётная степень: x = 1/t², y = t^{−3}·(…)
  (let ((P '(+ (^ x 3) 1)))
    (assert-equal -2 (hyp-valuation (list 'inf 'ram) 'x P 'x))
    (assert-equal -3 (hyp-valuation (list 'inf 'ram) 'y P 'x)))
  ; чётная степень: x = 1/t, y = t^{−2}·(…)
  (let ((P '(+ (^ x 4) 1))
        (pl (list 'inf (integrate::ib-k-sqrt-rat 1))))
    (assert-equal -1 (hyp-valuation pl 'x P 'x))
    (assert-equal -2 (hyp-valuation pl 'y P 'x))))

(deftest "intdiv: дивизоры — сложение, кратность, степень, слияние"
  (let* ((b (integrate::ib-k-sqrt-rat 1))
         (p1 (list 0 b))
         (p2 (list 0 (integrate::ib-k-scale b -1)))
         (d (dv-add (list (cons p1 1)) (list (cons p2 -1)))))
    (assert-equal 0 (dv-degree d))
    (assert-equal 2 (length d))
    (assert-equal 0 (dv-degree (dv-scale d 2)))
    (assert-equal 2 (length (dv-normalize (append d d))))
    (assert-equal 2 (cdr (car (dv-normalize (append d d)))))
    (assert-equal 0 (length (dv-add d (dv-scale d -1))))))

(deftest "intdiv: residue-divisors — δ = (0,1) − (0,−1)"
  (let* ((P '(+ (^ x 3) 1))
         (res (hyp-residues '(/ 1 (* x y)) P 'x))
         (rd (residue-divisors res)))
    (assert-equal 1 (car rd))
    (assert-equal 1 (length (cdr rd)))
    (assert-equal 1 (car (car (cdr rd))))
    (let ((d (cadr (car (cdr rd)))))
      (assert-equal 0 (dv-degree d))
      (assert-equal 2 (length d))
      (assert-equal 1 (cdr (car d)))
      (assert-equal -1 (cdr (cadr d))))))

(deftest "intdiv: residue-divisors отвергает дивизор ненулевой степени"
  (let* ((b (integrate::ib-k-sqrt-rat 1))
         (res (list (cons (list 0 b) (integrate::dv-k-rat 1)))))
    (assert-equal 'unknown (residue-divisors res))
    (assert-equal 'unknown (residue-divisors '()))))

; ---------- A5.2: L(D) и главность ----------

(define (idv-sq b) (integrate::ib-k-sqrt-rat b))

(define (idv-place a b) (list a (integrate::ib-k-sqrt-rat b)))

(define (idv-neg b) (integrate::ib-k-scale (integrate::ib-k-sqrt-rat b) -1))

; значение u/v в точке (x0, y0) (y0² = P(x0)) — численно, точно
(define (idv-ratio-at u v x0 y0)
  (eval-num (simplify (subst (list (list 'x x0) (list 'y y0)) (list '/ u v)))))

; u и v задают один дивизор D: оба проходят чекер, и u не константа
(define (idv-same-divisor? D u v P)
  (and (hyp-principal-check D u P 'x)
       (hyp-principal-check D v P 'x)
       (contains-sym? u 'y)))

(deftest "intdiv: D = 3·((0,1) − (0,−1)) главен, u = (y − 1)/(y + 1)"
  (let* ((P '(+ (^ x 3) 1))
         (D (list (cons (idv-place 0 1) 3) (cons (list 0 (idv-neg 1)) -3)))
         (r (hyp-principal D P 'x)))
    (assert-equal 'principal (car r))
    (assert-true (idv-same-divisor? D (cadr r) '(/ (+ -1 y) (+ 1 y)) P))
    (assert-true (hyp-principal-check D '(/ (+ -1 y) (+ 1 y)) P 'x))
    ; в сопряжённых точках (2, ±3) отношение u/v одно и то же
    (let ((c1 (idv-ratio-at (cadr r) '(/ (+ -1 y) (+ 1 y)) 2 3))
          (c2 (idv-ratio-at (cadr r) '(/ (+ -1 y) (+ 1 y)) 2 -3)))
      (assert-true (= c1 c2))
      (assert-true (not (= c1 0))))))

(deftest "intdiv: D и 2D при D = (0,1) − (0,−1) не главны"
  (let* ((P '(+ (^ x 3) 1))
         (D1 (list (cons (idv-place 0 1) 1) (cons (list 0 (idv-neg 1)) -1)))
         (D2 (list (cons (idv-place 0 1) 2) (cons (list 0 (idv-neg 1)) -2))))
    (assert-equal 'not-principal (hyp-principal D1 P 'x))
    (assert-equal 'not-principal (hyp-principal D2 P 'x))))

(deftest "intdiv: x⁸ + 1 — 4·((0,1) − (0,−1)) главен, 1…3 нет"
  (let* ((P '(+ (^ x 8) 1))
         (mk (lambda (k) (list (cons (idv-place 0 1) k) (cons (list 0 (idv-neg 1)) (- k)))))
         (r (hyp-principal (mk 4) P 'x)))
    (assert-equal 'principal (car r))
    (assert-true (idv-same-divisor? (mk 4) (cadr r) '(/ (^ x 4) (+ 1 y)) P))
    (assert-equal 'not-principal (hyp-principal (mk 1) P 'x))
    (assert-equal 'not-principal (hyp-principal (mk 2) P 'x))
    (assert-equal 'not-principal (hyp-principal (mk 3) P 'x))))

(deftest "intdiv: x⁵ + 1 — 5·((0,1) − (0,−1)) главен"
  (let* ((P '(+ (^ x 5) 1))
         (D (list (cons (idv-place 0 1) 5) (cons (list 0 (idv-neg 1)) -5)))
         (r (hyp-principal D P 'x)))
    (assert-equal 'principal (car r))
    (assert-true (idv-same-divisor? D (cadr r) '(/ (+ -1 y) (+ 1 y)) P))))

(deftest "intdiv: чекер главности отвергает подделки"
  (let* ((P '(+ (^ x 3) 1))
         (D (list (cons (idv-place 0 1) 3) (cons (list 0 (idv-neg 1)) -3)))
         (u '(/ (+ -1 y) (+ 1 y)))
         (D2 (list (cons (idv-place 0 1) 6) (cons (list 0 (idv-neg 1)) -6))))
    (assert-true (hyp-principal-check D u P 'x))
    ; лишний множитель — лишние нуль и полюс
    (assert-true (not (hyp-principal-check D (list '* (list '+ 1 'x) u) P 'x)))
    ; обратный элемент: div = −D
    (assert-true (not (hyp-principal-check D (list '^ u -1) P 'x)))
    ; u для 2D вместо D
    (assert-true (not (hyp-principal-check D2 u P 'x)))
    ; u = 1 при D ≠ 0 и u = 0
    (assert-true (not (hyp-principal-check D 1 P 'x)))
    (assert-true (not (hyp-principal-check D 0 P 'x)))
    ; ревью: лишние нули/полюсы вне x-координат supp D (x = −1, x = 5, x = 2) — раньше проходили
    (assert-true (not (hyp-principal-check D (list '* (list '/ (list '+ 'x 1) (list '- 'x 5)) u) P 'x)))
    (assert-true (not (hyp-principal-check D (list '* (list '/ (list '- 'x 2) (list '- 'x 5)) u) P 'x)))
    ; константа — допустима
    (assert-true (hyp-principal-check D (list '* 7 u) P 'x))))

(deftest "intdiv: Риман — Рох, dim L(k·∞) = k + 1 − g"
  ; y² = x³ + 1, g = 1, одно место на ∞
  (let ((P '(+ (^ x 3) 1)))
    (assert-equal '(1 2 3 4 5)
                  (map (lambda (k) (length (hyp-riemann-roch (list (cons (list 'inf 'ram) k)) P 'x)))
                       '(1 2 3 4 5))))
  ; y² = x⁵ + 1, g = 2
  (let ((P '(+ (^ x 5) 1)))
    (assert-equal '(2 3 4 5 6)
                  (map (lambda (k) (length (hyp-riemann-roch (list (cons (list 'inf 'ram) k)) P 'x)))
                       '(3 4 5 6 7))))
  ; Давенпорт, g = 1, два места на ∞: D = k·∞₊ + k·∞₋, deg 2k
  (let* ((P (idv-dav))
         (mk (lambda (k) (list (cons (list 'inf (idv-sq 1)) k)
                               (cons (list 'inf (idv-neg 1)) k)))))
    (assert-equal '(2 4 6)
                  (map (lambda (k) (length (hyp-riemann-roch (mk k) P 'x))) '(1 2 3)))))

(deftest "intdiv: рост границ степеней не меняет dim L(D)"
  (let* ((P '(+ (^ x 3) 1))
         (D (dv-scale (list (cons (list 'inf 'ram) 5)) -1)))
    (assert-equal 5 (length (integrate::dv-l-basis D P 'x 2)))
    (assert-equal 5 (length (integrate::dv-l-basis D P 'x 4)))
    (assert-equal 5 (length (integrate::dv-l-basis D P 'x 6))))
  (let* ((P (idv-dav))
         (D (dv-scale (list (cons (list 'inf (idv-sq 1)) 2)
                            (cons (list 'inf (idv-neg 1)) 2)) -1)))
    (assert-equal 4 (length (integrate::dv-l-basis D P 'x 2)))
    (assert-equal 4 (length (integrate::dv-l-basis D P 'x 5)))))

; ---------- A5.3: хорошие простые, счёт точек, #J(𝔽_p), кручение ----------

(deftest "intdiv: хорошее простое — нечётное, не делит lc и дискриминант"
  ; y² = x³ − 2: disc = −108, хорошие p = 5, 7; плохие 2, 3
  (assert-true (hyp-good-prime? '(+ (^ x 3) -2) 'x 5))
  (assert-true (hyp-good-prime? '(+ (^ x 3) -2) 'x 7))
  (assert-true (not (hyp-good-prime? '(+ (^ x 3) -2) 'x 2)))
  (assert-true (not (hyp-good-prime? '(+ (^ x 3) -2) 'x 3)))
  ; y² = x⁵ + 1: p = 5 делит disc
  (assert-true (hyp-good-prime? '(+ (^ x 5) 1) 'x 3))
  (assert-true (not (hyp-good-prime? '(+ (^ x 5) 1) 'x 5))))

(deftest "intdiv: #C(𝔽_p) — ручные значения и Хассе — Вейль"
  ; y² = x³ − 2: 6 и 7 (проверено вручную)
  (assert-equal 6 (hyp-count-points '(+ (^ x 3) -2) 'x 5 1))
  (assert-equal 7 (hyp-count-points '(+ (^ x 3) -2) 'x 7 1))
  ; y² = x³ + 1: 6 и 12
  (assert-equal 6 (hyp-count-points '(+ (^ x 3) 1) 'x 5 1))
  (assert-equal 12 (hyp-count-points '(+ (^ x 3) 1) 'x 7 1))
  ; Хассе — Вейль: |#C − p − 1| ≤ 2g√p (для рода 1: квадрат ≤ 4p)
  (let ((P '(+ (^ x 3) 1)))
    (for-each
     (lambda (p)
       (let ((N (hyp-count-points P 'x p 1)))
         (assert-true (<= (* (- N (+ p 1)) (- N (+ p 1))) (* 4 p)))))
     '(5 7 11 13))))

(deftest "intdiv: #J(𝔽_p) — род 1 и делимость известным кручением"
  ; y² = x³ + 1: E(ℚ) ≅ ℤ/6, значит 6 | #E(𝔽_p) при хороших p
  (let ((P '(+ (^ x 3) 1)))
    (for-each
     (lambda (p)
       (let ((j (hyp-jacobian-order P 'x p)))
         (assert-true (integer? j))
         (assert-equal 0 (remainder j 6))))
     '(5 7 11)))
  ; Давенпорт: 8 | #E(𝔽_p)
  (let ((P (idv-dav)))
    (for-each
     (lambda (p)
       (if (hyp-good-prime? P 'x p)
           (assert-equal 0 (remainder (hyp-jacobian-order P 'x p) 8))))
     '(3 5 7 11))))

(deftest "intdiv: подделка счёта на ∞ (без χ(lc)) ловится делимостью"
  ; y² = x³ + 1, p = 5: верный счёт 6 (слагаемое на ∞ — 1 + χ(1) = 2),
  ; «забыли χ(lc)» даёт 5, и 6 ∤ 5
  (let* ((P '(+ (^ x 3) 1))
         (N (hyp-count-points P 'x 5 1))
         (forged (+ (- N (+ 1 (jacobi 1 5))) 1)))
    (assert-equal 6 N)
    (assert-equal 5 forged)
    (assert-equal 0 (remainder N 6))
    (assert-true (not (= 0 (remainder forged 6))))))

(deftest "intdiv: #J(𝔽_p) рода 2 — 5 | #J (y² = x⁵ + 1)"
  (let ((P '(+ (^ x 5) 1)))
    (for-each
     (lambda (p)
       (assert-equal 0 (remainder (hyp-jacobian-order P 'x p) 5)))
     '(3 7 11))
    ; R1b.3: род 3 теперь через дзета-функцию (строгая 2g-проверка при p = 3)
    (assert-equal 28 (hyp-jacobian-order '(+ (^ x 7) 1) 'x 3))))

(deftest "intdiv: граница кручения B = gcd(#J(p), #J(q))"
  (assert-equal 1 (hyp-torsion-bound '(+ (^ x 3) -2) 'x))
  (assert-equal 6 (hyp-torsion-bound '(+ (^ x 3) 1) 'x))
  (assert-equal 0 (remainder (hyp-torsion-bound '(+ (^ x 5) 1) 'x) 5)))

(deftest "intdiv: порядок кручения — три эталона"
  ; y² = x³ − 2, D = (3,5) − (3,−5): кривая ранга 1 с тривиальным кручением
  (let ((P '(+ (^ x 3) -2)))
    (assert-equal 'non-torsion
                  (hyp-torsion-order
                   (list (cons (list 3 (integrate::ib-k-sqrt-rat 25)) 1)
                         (cons (list 3 (integrate::ib-k-scale (integrate::ib-k-sqrt-rat 25) -1)) -1))
                   P 'x)))
  ; y² = x³ + 1, D = (2,3) − (2,−3): E(ℚ) ≅ ℤ/6, порядок 3
  (let* ((P '(+ (^ x 3) 1))
         (D (list (cons (list 2 (integrate::ib-k-sqrt-rat 9)) 1)
                  (cons (list 2 (integrate::ib-k-scale (integrate::ib-k-sqrt-rat 9) -1)) -1)))
         (r (hyp-torsion-order D P 'x)))
    (assert-equal 3 (car r))
    (assert-true (hyp-principal-check (dv-scale D 3) (cadr r) P 'x)))
  ; x⁵ + 1, D = (0,1) − ∞: div(y − 1) = 5(0,1) − 5∞, порядок 5
  (let* ((P '(+ (^ x 5) 1))
         (D (list (cons (list 0 (integrate::ib-k-sqrt-rat 1)) 1)
                  (cons (list 'inf 'ram) -1)))
         (r (hyp-torsion-order D P 'x)))
    (assert-equal 5 (car r))
    (assert-true (hyp-principal-check (dv-scale D 5) (cadr r) P 'x))))

(deftest "intdiv: Давенпорт, D = ∞₊ − ∞₋ — порядок 8 (z-модель)"
  (let* ((P (idv-dav))
         (D (list (cons (list 'inf (idv-sq 1)) 1)
                  (cons (list 'inf (idv-neg 1)) -1)))
         (r (hyp-torsion-order D P 'x)))
    (assert-equal 8 (car r))
    (assert-true (hyp-principal-check (dv-scale D 8) (cadr r) P 'x))
    ; сам 8D главен и находится напрямую (нули на ∞ — через z-модель)
    (assert-equal 'principal (car (hyp-principal (dv-scale D 8) P 'x)))
    ; D не галисов (∞₊ − ∞₋ антиинвариантен): пустое ядро не доказательство
    (assert-equal 'unknown (hyp-principal D P 'x))))

; ---------- A5.4: логарифмическая часть Трагера ----------

(deftest "intdiv: ∫dx/(x√(x³+1)) = (1/3)·log u"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ 1 (* x y)))
         (r (hyp-log-part H P 'x)))
    (assert-equal 'logs (car r))
    (assert-equal 1 (cadr r))
    (assert-equal 3 (cadr (car (caddr r))))
    (assert-true (hyp-log-check H P 'x r))))


(deftest "intdiv: ∫√(x⁸+1)/(x(x⁸+1)) dx = (1/4)·log u (Бронштейн, пр. 4)"
  (let* ((P '(+ (^ x 8) 1))
         (H '(/ y (* x (+ (^ x 8) 1))))
         (r (hyp-log-part H P 'x)))
    (assert-equal 'logs (car r))
    (assert-equal 4 (cadr (car (caddr r))))
    (assert-true (hyp-log-check H P 'x r))))

(deftest "intdiv: ∫dx/(x√(x⁵+1)) = (1/5)·log u (род 2, граница по #J)"
  (let* ((P '(+ (^ x 5) 1))
         (H '(/ 1 (* x y)))
         (r (hyp-log-part H P 'x)))
    (assert-equal 'logs (car r))
    (assert-equal 5 (cadr (car (caddr r))))
    (assert-true (hyp-log-check H P 'x r))))

(deftest "intdiv: Давенпорт, ∫x dx/y = −(1/8)·log u"
  (let* ((P (idv-dav))
         (H '(/ x y))
         (r (hyp-log-part H P 'x)))
    (assert-equal 'logs (car r))
    (assert-equal 8 (cadr (car (caddr r))))
    (assert-true (hyp-log-check H P 'x r))))

(deftest "intdiv: ∫dx/((x−3)√(x³−2)) — неэлементарен (δ не кручение, B = 1)"
  (assert-equal 'nonelementary
                (hyp-log-part '(/ y (* (- x 3) (+ (^ x 3) -2))) '(+ (^ x 3) -2) 'x)))

(deftest "intdiv: подделки hyp-log-check отвергаются"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ 1 (* x y)))
         (r (hyp-log-part H P 'x))
         (m (cadr r))
         (n (cadr (car (caddr r))))
         (u (caddr (car (caddr r)))) )
    (assert-true (hyp-log-check H P 'x r))
    ; другой коэффициент
    (assert-true (not (hyp-log-check H P 'x (list 'logs m (list (list 1 (* 2 n) u))))))
    ; лишний множитель у u
    (assert-true (not (hyp-log-check H P 'x
                                     (list 'logs m (list (list 1 n (list '* (list '+ 1 'x) u)))))))
    ; пропущенный член
    (assert-true (not (hyp-log-check H P 'x (list 'logs m '()))))))

(deftest "intdiv: integrate не ломается на третьем роде"
  (let ((e '(/ 1 (* x (^ (+ (^ x 3) 1) 1/2)))))
    (let ((ans (integrate e 'x)))
      (assert-true (or (and (pair? ans) (equal? (car ans) 'integrate))
                       (int-check ans e 'x))))))

; ---------- A5.4b: голоморфный остаток после логарифмической части ----------

(deftest "intdiv: ∫dx/((x−2)√(x³+1)) — лог + 1-й род, неэлементарен"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ y (* (- x 2) (+ (^ x 3) 1)))))
    (assert-equal 'nonelementary (hyp-log-part H P 'x))))

(deftest "intdiv: ∫(1/(x−2)+1)/√(x³+1) — неэлементарен"
  (let* ((P '(+ (^ x 3) 1))
         (H '(/ (+ x -1) (* (- x 2) y))))
    (assert-equal 'nonelementary (hyp-log-part H P 'x))))

(deftest "intdiv: логарифм + производная — элементарен (сертификат int-check)"
  (let ((e '(+ (/ 1 (* x (^ (+ (^ x 3) 1) 1/2)))
               (/ (* -3 (^ x 2)) (* 2 (^ (+ (^ x 3) 1) 3/2))))))
    (let ((ans (integrate e 'x)))
      (assert-true (and (not (equal? (car ans) 'integrate))
                        (int-check ans e 'x))))))

(deftest "intdiv: hyp-holomorphic? — подделка неголоморфного остатка отвергается"
  (let* ((P '(+ (^ x 3) 1)))
    (assert-true (hyp-holomorphic? 0 P 'x))
    (assert-true (hyp-holomorphic? '(/ y (+ (^ x 3) 1)) P 'x))
    ; полюс в (2, ±3)
    (assert-true (not (hyp-holomorphic? '(/ 1 (* (- x 2) y)) P 'x)))
    (assert-true (not (hyp-holomorphic? '(/ 1 x) P 'x)))
    ; полюс в точках ветвления (x³ + 1 = 0)
    (assert-true (not (hyp-holomorphic? '(/ x (+ (^ x 3) 1)) P 'x)))))

; ---------- A5.4c: полюс порядка ≥ 2 на ∞ (2-й род) ----------

(deftest "intdiv: ∫x dx/√(1−x³) — 2-й род на ∞, неэлементарен (Бронштейн, пр. 5)"
  (let* ((P '(+ 1 (* -1 (^ x 3))))
         (H '(/ x y)))
    (assert-equal #f (hyp-second-kind? H P 'x))
    (assert-equal 'nonelementary (hyp-log-part H P 'x))))

(deftest "intdiv: ∫x dx/√(x³+1) и ∫x² dx/√(x⁵+1) — неэлементарны"
  (assert-equal 'nonelementary (hyp-log-part '(/ x y) '(+ (^ x 3) 1) 'x))
  (assert-equal 'nonelementary (hyp-log-part '(/ (^ x 2) y) '(+ (^ x 5) 1) 'x))
  ; первый род (голоморфный дифференциал) — тот же вердикт
  (assert-equal 'nonelementary (hyp-log-part '(/ 1 y) '(+ (^ x 3) 1) 'x)))

(deftest "intdiv: производные (x√(x³+1))′ и (y³)′ — элементарны"
  (let* ((e1 '(+ (^ (+ (^ x 3) 1) 1/2)
                 (/ (* 3 (^ x 3)) (* 2 (^ (+ (^ x 3) 1) 1/2)))))
         (e3 '(/ (* 9 (^ x 2) (+ (^ x 3) 1)) (* 2 (^ (+ (^ x 3) 1) 1/2)))))
    (assert-true (int-check (integrate e1 'x) e1 'x))
    (assert-true (equal? '(^ (+ 1 (^ x 3)) 3/2) (integrate e3 'x)))
    (assert-true (int-check (integrate e3 'x) e3 'x))))

(deftest "intdiv: hyp-second-kind? — сертификат редукции на ∞"
  (let* ((P '(+ (^ x 3) 1))
         ; d(C + S·y): V = M(S) = P·S′ + (P′/2)·S, S = x
         (Dt '(+ y (/ (* 3/2 (^ x 3) y) (+ (^ x 3) 1)))))
    (assert-equal #t (hyp-second-kind? Dt P 'x))
    ; ненулевой класс: x dx/y, dx/y
    (assert-equal #f (hyp-second-kind? '(/ x y) P 'x))
    (assert-equal #f (hyp-second-kind? '(/ 1 y) P 'x))
    ; конечный полюс или чётная степень — вне критерия
    (assert-equal 'unknown (hyp-second-kind? '(/ 1 (* (- x 2) y)) P 'x))
    (assert-equal 'unknown (hyp-second-kind? '(/ x y) '(+ (^ x 4) 1) 'x))))

; ---------- A5.3b: места не на кривой отвергаются ----------

(deftest "intdiv: место с b² ≠ P(a) отвергается всеми входными функциями"
  (let* ((P '(+ (^ x 3) 1))
         (bad (list 2 (integrate::ib-k-sqrt-rat 3)))     ; (2, √3): 3 ≠ P(2) = 9
         (good (list 2 (integrate::ib-k-sqrt-rat 9)))    ; (2, 3)
         (Dbad (list (cons bad 1) (cons (list 2 (integrate::ib-k-sqrt-rat 3)) -1)))
         (Dgood (list (cons good 1)
                      (cons (list 2 (integrate::ib-k-scale (integrate::ib-k-sqrt-rat 9) -1)) -1))))
    (assert-equal 'unknown (hyp-valuation bad 'x P 'x))
    (assert-equal 'unknown (hyp-riemann-roch Dbad P 'x))
    (assert-equal 'unknown (hyp-principal Dbad P 'x))
    (assert-equal #f (hyp-principal-check Dbad 1 P 'x))
    (assert-equal #f (hyp-torsion-order Dbad P 'x))
    ; корректные места того же x работают
    (assert-equal 0 (hyp-valuation good 'x P 'x))
    (assert-equal 3 (car (hyp-torsion-order Dgood P 'x)))
    ; ram там, где P(a) ≠ 0; гладкое там, где ветвление
    (assert-equal 'unknown (hyp-valuation (list 2 'ram) 'x P 'x))
    (assert-equal 'unknown (hyp-valuation (list -1 (integrate::ib-k-sqrt-rat 1)) 'x P 'x))
    ; ∞: нечётная степень — только ram, чётная — только ±√lc
    (assert-equal 'unknown (hyp-valuation (list 'inf (integrate::ib-k-sqrt-rat 1)) 'x P 'x))
    (assert-equal 'unknown (hyp-valuation (list 'inf 'ram) 'x '(+ (^ x 4) 1) 'x))))

; ---------- Шаг A5.5: общая кривая F(x, y) ----------

(deftest "intdiv: A5.5 — места Пюизё: ветви t → −t — одно место"
  (let ((F (expand '(- (^ (- y x) 2) (* x (- x 1) (- x 2))))))
    (assert-equal '((0 0 2)) (gv-places F 'x 'y 0))
    (assert-equal '((1 0 2)) (gv-places F 'x 'y 1))
    (assert-equal '((inf 0 2)) (gv-places F 'x 'y 'inf))))

(deftest "intdiv: A5.5 — (y − x)² = x(x−1)(x−2): логарифм и ответ"
  (let* ((F (expand '(- (^ (- y x) 2) (* x (- x 1) (- x 2)))))
         (H (simplify '(+ (/ 1 x) (/ -1 (- x 1)))))
         (L (gv-log-part H F 'x 'y)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (gv-log-check H F 'x 'y L))
    (assert-true (int-check (gv-logs->expr 0 L) H 'x))))

(deftest "intdiv: A5.5 — остаток 2-го рода на кубике: nonelementary"
  (let* ((F (expand '(- (^ (- y x) 2) (* x (- x 1) (- x 2)))))
         (H (simplify '(+ (/ 1 x) (/ -1 (- x 1)) (/ 1 (- y x)))))
         (res (gv-residues H F 'x 'y)))
    (assert-true (gv-residues-check H F 'x 'y res))
    (assert-equal 'nonelementary (gv-log-part H F 'x 'y))))

(deftest "intdiv: A5.5 — подделки: главность, места, вычеты"
  (let* ((F (expand '(- (^ (- y x) 2) (* x (- x 1) (- x 2)))))
         (D '(((0 0 2) . 2) ((1 0 2) . -2))))
    (assert-true (gv-principal-check D '(/ x (- x 1)) F 'x 'y))
    (assert-true (not (gv-principal-check D '(/ (* x (+ x 2)) (- x 1)) F 'x 'y)))
    (assert-true (not (gv-principal-check D '(/ x (* (- x 1) (+ x 2))) F 'x 'y)))
    (assert-true (not (gv-principal-check '(((0 1 2) . 2)) 'x F 'x 'y)))
    (let* ((H (simplify '(+ (/ 1 x) (/ -1 (- x 1)) (/ 1 (- y x)))))
           (res (gv-residues H F 'x 'y))
           (bad (cons (cons (car (car res)) 7) (cdr res))))
      (assert-true (gv-residues-check H F 'x 'y res))
      (assert-true (not (gv-residues-check H F 'x 'y bad))))))

(deftest "intdiv: A5.5 — граница кручения: гладкая кубика рода 1"
  (let ((F (expand '(- (^ (- y x) 2) (* x (- x 1) (- x 2)))))
        (F2 (expand '(- (^ (- (^ y 2) (* 2 x) 1) 2) (* 4 x (+ x 1))))))
    (assert-true (gv-good-prime? F 'x 'y 5))
    (assert-equal 8 (gv-jacobian-order F 'x 'y 5))
    (assert-equal 8 (gv-count-points F 'x 'y 5))
    (assert-equal 0 (modulo (gv-torsion-bound F 'x 'y) 4))
    (assert-equal 'unknown (gv-jacobian-order F2 'x 'y 5))))

(deftest "intdiv: A5.5 — два радикала: логарифм u = (y²−2y−1)/(y²+2y−1)"
  (let* ((F2 (expand '(- (^ (- (^ y 2) (* 2 x) 1) 2) (* 4 x (+ x 1)))))
         (u '(/ (- (^ y 2) (* 2 y) 1) (+ (^ y 2) (* 2 y) -1)))
         (H (simplify (list '/ (integrate::alg-g-expr (integrate::alg-g-der u F2 4 'x 'y) 'y) u)))
         (L (gv-log-part H F2 'x 'y)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (gv-log-check H F2 'x 'y L))))

; ---------- Шаг A5.5b: чётный случай ℚ(√d) ----------

(deftest "intdiv: A5.5b — вычеты ±√2: ответ (√2/2)·log(u/ū)"
  (let* ((P '(- (^ x 2) 2))
         ; H = d/dx[√2·log((y−√2)/(y+√2))]: вычеты ±√2 в сопряжённых местах (2,±√2), (−2,±√2)
         (H '(/ (* 4 x) (* y (- (^ x 2) 4))))
         (L (hyp-log-part H P 'x)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (hyp-log-check H P 'x L))
    (assert-true (hyp-residues-check H P 'x (hyp-residues H P 'x)))
    (let* ((tr (car (caddr L)))
           (ue (caddr tr)))
      ; коэффициент √d/2 (множитель 1/2 — от u/ū), порядок кручения 1
      (assert-true (equal? '(* 1/2 (^ 2 1/2)) (simplify (car tr))))
      (assert-equal 1 (cadr tr))
      ; аргумент — именно u/ū: ue·conj(ue) = 1
      (assert-true (equal? 0 (simplify (together
                                        (list '- (list '* ue (integrate::dv-conj-expr ue)) 1))))))))

(deftest "intdiv: A5.5b — подделки: знак √2, коэффициент, аргумент"
  (let* ((P '(- (^ x 2) 2))
         (H '(/ (* 4 x) (* y (- (^ x 2) 4))))
         (L (hyp-log-part H P 'x))
         (ue (caddr (car (caddr L))))
         (mk (lambda (q u) (list 'logs 1 (list (list q 1 u))))))
    (assert-true (hyp-log-check H P 'x L))
    ; неверный знак √d
    (assert-equal #f (hyp-log-check H P 'x (mk (list '* -1/2 (^ 2 1/2)) ue)))
    ; неверный коэффициент c (√d вместо √d/2)
    (assert-equal #f (hyp-log-check H P 'x (mk (^ 2 1/2) ue)))
    (assert-equal #f (hyp-log-check H P 'x (mk (list '* 1/3 (^ 2 1/2)) ue)))
    ; не тот аргумент: 1/ū вместо u/ū (знак производной логарифма)
    (assert-equal #f (hyp-log-check H P 'x (mk (list '* 1/2 (^ 2 1/2)) (list '/ 1 ue))))))

; ---------- Шаг A5.6: полюсы над неприводимыми g(x) степени ≥ 2 ----------

(deftest "intdiv: A5.6 — полюсы над x²−2 (y² = x²+2): логарифмический ответ"
  (let* ((P '(+ (^ x 2) 2))
         ; H = 4x/(y(x²−2)) = d/dx log((y−2)/(y+2)); x²−2 неприводим над ℚ,
         ; P ≡ 4 (mod x²−2) ⇒ b = 2, места (α, ±2) при α² = 2
         (H '(/ (* 4 x) (* y (- (^ x 2) 2))))
         (L (hyp-log-part H P 'x)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (hyp-log-check H P 'x L))
    ; вычеты над g найдены и рациональны: данные по x²−2 — b = 2, ±1
    (let ((d (car (integrate::dv-irred-data H P 'x))))
      (assert-equal '(2) (cadr d))
      (assert-equal 1 (nth d 2))
      (assert-equal -1 (nth d 3)))))

(deftest "intdiv: A5.6 — nonelementary: полюсы над x²+1 на кривой рода 1"
  ; y² = x³+x+1 (род 1), H = 2x/(y(x²+1)); P ≡ 1 (mod x²+1) ⇒ места (α, ±1), α²=−1.
  ; Вычеты ±1 рациональны, δ = Σ по сопряжённым местам — дивизор над ℚ; ни одно
  ; k | B (B = gcd #J(𝔽_p) по хорошим p) не делает k·δ главным ⇒ по Трагеру
  ; (§1.6, п. 4: вычеты рациональны, δ не кручение) элементарной первообразной нет.
  (let ((P '(+ (^ x 3) x 1))
        (H '(/ (* 2 x) (* y (+ (^ x 2) 1)))))
    (assert-equal 'nonelementary (hyp-log-part H P 'x))))

(deftest "intdiv: A5.6 — подделки логарифмического ответа над x²−2"
  (let* ((P '(+ (^ x 2) 2))
         (H '(/ (* 4 x) (* y (- (^ x 2) 2))))
         (L (hyp-log-part H P 'x))
         (u (caddr (car (caddr L)))))
    (assert-true (hyp-log-check H P 'x L))
    ; 1/u — знак производной логарифма обратный
    (assert-equal #f (hyp-log-check H P 'x (list 'logs 1 (list (list 1 1 (list '/ 1 u))))))
    ; (y−2) без знаменателя x²−2 — другой дивизор (нет полюса в (α,−2))
    (assert-equal #f (hyp-log-check H P 'x (list 'logs 1 (list (list 1 1 '(- y 2))))))))

(deftest "intdiv: R1.2 — b = α ∈ ℚ(∛2): логарифм через норму"
  ; y² = x³+x²−2, g = x³−2, P ≡ α² (mod g): b = α ∉ ℚ находится factor-over;
  ; u = (y³−2)/(y³+2) = Norm(y−α)/Norm(y+α)
  (let* ((P '(- (+ (^ x 3) (^ x 2)) 2))
         (u '(/ (- (^ y 3) 2) (+ (^ y 3) 2)))
         (H (simplify (/ (integrate::dv-crv-deriv u P 'x) u)))
         (L (hyp-log-part H P 'x)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (hyp-log-check H P 'x L))))

(deftest "intdiv: R1.3 — места y³ = x³+1: три ветви и ветвление"
  (assert-equal '((0 0 1) (0 1 1) (0 2 1))
                (integrate::hypn3-places '(+ (^ x 3) 1) 0 'x))
  ; P(1) = 2 — куб не в Q (нужна башня) — честный unknown
  (assert-equal 'unknown (integrate::hypn3-places '(+ (^ x 3) 1) 1 'x))
  ; P(-1) = 0 — разветвлённое место (индекс 3)
  (assert-equal '((-1 0 3)) (integrate::hypn3-places '(+ (^ x 3) 1) -1 'x)))

(deftest "intdiv: R1.3 — вычет простого полюса в Q(zeta3)"
  ; y³ = x³+x+1, H = P'/(3y²(y−1)) = d/dx log(y−1);
  ; в месте (0,1): res = P'/(D_y·y') = 1; в ветвях ζ, ζ² полюса нет
  (let* ((P '(+ (^ x 3) x 1))
         (H '(/ (+ (* 3 (^ x 2)) 1) (* 3 (^ y 2) (- y 1)))))
    (assert-equal '(1 0) (integrate::hypn3-residue H P 0 0 'x))
    (assert-equal 0 (integrate::hypn3-residue H P 0 1 'x))
    (assert-equal 0 (integrate::hypn3-residue H P 0 2 'x))))

(deftest "intdiv: R1.3 — ряд y(t) в Q(zeta3): y³ = x³+1"
  ; y = (1+t³)^{1/3} = 1 + t³/3 + …, в ветви k=1 — умножение на ζ
  (assert-equal '((1 0) (0 0) (0 0) (1/3 0))
                (integrate::hypn3-y-series '(+ (^ x 3) 1) 0 0 'x 3))
  (assert-equal '((0 1) (0 0) (0 0) (0 1/3))
                (integrate::hypn3-y-series '(+ (^ x 3) 1) 0 1 'x 3)))

(deftest "intdiv: R1.3 — вычет q=3 и сборка logs"
  ; y³ = x+x², a = 0 — разветвлённое место (0,0,3); H = P'/(3y³) = (log y)'
  (let* ((P '(+ x (^ x 2)))
         (H '(/ (+ 1 (* 2 x)) (* 3 (^ y 3)))))
    (assert-equal 1 (integrate::hypn3-residue-ram H P 0 'x))
    (assert-true (integrate::hypn3-log-check H P 'x '(logs 1 ((1 1 y)))))
    (assert-equal '(log y) (integrate::hypn3-logs->expr 0 '(logs 1 ((1 1 y)))))))

(deftest "intdiv: R1.3 — места y³=P на бесконечности"
  ; deg P = 3: Q(0) = 1 — три неразветвлённых места
  (assert-equal '((inf 0 1) (inf 1 1) (inf 2 1))
                (integrate::hypn3-places-inf '(+ (^ x 3) 1) 'x))
  ; deg P = 2 и 4: Q(0) = 0, порядок 1 — одно место с индексом 3
  (assert-equal '((inf 0 3)) (integrate::hypn3-places-inf '(+ x (^ x 2)) 'x))
  (assert-equal '((inf 0 3)) (integrate::hypn3-places-inf '(+ (^ x 4) 1) 'x)))

(deftest "intdiv: R1.3 — нормирование и главность (конечные места)"
  ; y³ = x³+x+1, a = 0: ветви y = 1, ζ, ζ²; y−1 обращается в нуль только в (0,0,1)
  (let ((P '(+ (^ x 3) x 1)))
    (assert-equal 1 (integrate::hypn3-valuation P 0 0 '(- y 1) 'x 6))
    (assert-equal 0 (integrate::hypn3-valuation P 0 1 '(- y 1) 'x 6))
    (assert-true (integrate::hypn3-principal-check '(((0 0 1) . 1)) '(- y 1) P 'x))
    (assert-true (not (integrate::hypn3-principal-check '(((0 0 1) . 1)) 'y P 'x)))))

(deftest "intdiv: R1.3 — ∞-ряд y(t) в Q(zeta3)"
  ; y^3 = x^3+1: z=1/x, M=1, y = z^-1 (1 + z^3/3 + …)
  (let ((s1 (integrate::hypn3-y-series-inf '(+ (^ x 3) 1) 0 'x 3))
        (s2 (integrate::hypn3-y-series-inf '(+ x (^ x 2)) 0 'x 2)))
    (assert-equal '(-1 1 0) (car s1))
    (assert-equal '(2 1/3 0) (nth s1 3))
    ; y^3 = x+x^2: z=t^3, y = t^-2 + t/3 + …
    (assert-equal '(-2 1 0) (car s2))
    (assert-equal '(1 1/3 0) (nth s2 1))))

(deftest "intdiv: R1.3 — строки L(D) для y³=P"
  ; D = -(0,0,1): v(u) >= 1, т.е. u(0, ветвь y=1) = 0; строки по 6 неизвестным
  (let ((P '(+ (^ x 3) x 1)))
    (assert-equal '((1 0 1 0 1 0) (0 1 0 1 0 1))
                  (integrate::hypn3-l-rows '(((0 0 1) . -1)) P 'x 2))
    (assert-true (member? '(-1 0 1 0 0 0)
                          (integrate::hypn3-l-basis '(((0 0 1) . -1)) P 'x 2)))
    (assert-equal '() (integrate::hypn3-l-rows '() P 'x 2))))

(deftest "intdiv: R1.3 — кручение по L(kD) для y³=P"
  ; y³ = x³+x+1, D=(0,0,1): u = y−1 (v=1), порядок 1
  (let ((P '(+ (^ x 3) x 1)))
    (assert-equal '(1 (-1 0 1 0 0 0))
                  (integrate::hypn3-torsion-search '(((0 0 1) . 1)) P 'x))
    ; 2D: u = (y−1)² (v=2)
    (assert-equal '(1 (1 0 -2 0 1 0))
                  (integrate::hypn3-torsion-search '(((0 0 1) . 2)) P 'x))
    ; полюс (n < 0) полиномиальным u не реализуется — честный unknown
    (assert-equal 'unknown
                  (integrate::hypn3-torsion-search '(((0 0 1) . 1) ((0 1 1) . -1)) P 'x))))

(deftest "intdiv: R1.3 — кручение с ∞: u = y−1 на y³=x³+1"
  ; y³=x³+1: y−1 имеет нуль порядка 3 в (0,0,1) и полюсы по −1 в трёх местах ∞
  (let* ((P '(+ (^ x 3) 1))
         (D (append (list (cons (list 0 0 1) 3))
                    (map (lambda (k) (cons (list 'inf k 1) -1)) '(0 1 2))))
         (H '(/ (^ x 2) (* (^ y 2) (- y 1)))))
    (assert-equal '(1 (-1 0 1 0 0 0)) (integrate::hypn3-torsion-search2 D P 'x))
    (assert-true (integrate::hypn3-log-check H P 'x '(logs 1 ((1 1 (- y 1))))))))

(deftest "intdiv: R1.3 — сборка logs из H"
  ; H = u'/u, u из множителей числителя/знаменателя; сертификат — hypn3-log-check
  (let ((P '(+ (^ x 3) 1)))
    (assert-equal '(logs 1 ((1 1 (+ -1 y))))
                  (integrate::hypn3-log-part '(/ (^ x 2) (* (^ y 2) (- y 1))) P 'x))
    (assert-equal '(logs 1 ((1 1 y)))
                  (integrate::hypn3-log-part '(/ (^ x 2) (^ y 3)) P 'x))))

(deftest "intdiv: R5.1 — инертные p в границе кручения над ℚ(√d): #J(F_p²) = L(1)L(−1), B кратна порядку кручения"
  (let ((P3 '(+ (^ x 3) 1)) (P7 '(+ (^ x 7) 1)))
    ; y²=x³+1, p = 5: #E(F_5) = 6, a = 0 ⇒ #E(F_25) = 36
    (assert-equal 36 (integrate::hyp-jacobian-order-sq P3 'x 5))
    (assert-equal '((5 inert 36) (7 split 12)) (integrate::hyp-torsion-data-ev P3 'x 2))
    ; J(ℚ)_tors ⊂ J(K)_tors: порядок 6 (x³+1) и 14 (x⁷+1) делит B
    (assert-equal 0 (modulo (integrate::hyp-torsion-bound-ev P3 'x 2) 6))
    (assert-equal 0 (modulo (integrate::hyp-torsion-bound-ev P3 'x 3) 6))
    (assert-equal 0 (modulo (integrate::hyp-torsion-bound-ev P7 'x 2) 14))
    (assert-equal 0 (modulo (integrate::hyp-torsion-bound-ev P7 'x 5) 14))))

(deftest "intdiv: R5.1 — род 4, d = 5: граница по инертным p = 3, 7 быстро, B = 1"
  (assert-equal 1 (integrate::hyp-torsion-bound-ev '(+ (^ x 10) (* 3 (^ x 7)) (* -2 (^ x 3)) x 5) 'x 5)))

(deftest "intdiv: R5.2 — таблицы Жюши и орбиты Фробениуса: Σ(1+χ(P(a))) = dv-count-generic, x примитивен"
  (for-each
   (lambda (P)
     (for-each
      (lambda (pk)
        (let* ((p (car pk)) (k (cadr pk))
               (pl (integrate::dv-pmod-coeffs P 'x p))
               (m (integrate::dv-prim-poly p k))
               (F (gf-field p m 't)))
          (assert-true (gf-primitive? (gf-elt F '(0 1)) F))
          (assert-equal (integrate::dv-count-generic F pl p (quotient (- (^ p k) 1) 2) k)
                        (integrate::dv-count-tables pl p m k))))
      '((3 2) (3 5) (5 2) (5 3) (7 3) (11 2))))
   (list '(+ (^ x 5) (* 2 x) 3) '(+ (^ x 4) (* 3 (^ x 2)) 1) '(+ (^ x 10) (* 3 (^ x 7)) (* -2 (^ x 3)) x 5))))

(deftest "intdiv: R5.2 — слишком дорогое p^g пропускается: B по одному p (верная граница) или unknown"
  (let ((P '(+ (^ x 7) 1)) (old integrate::dv-count-cap))
    (let ((full (hyp-torsion-bound P 'x)))
      (set! integrate::dv-count-cap 100)   ; 3³ = 27 допустимо, 5³ = 125 нет
      (let ((one (try (hyp-torsion-bound P 'x) (lambda (e) 'err)))
            (data (try (integrate::hyp-torsion-data P 'x) (lambda (e) 'err))))
        (set! integrate::dv-count-cap 10)
        (let ((none (try (hyp-torsion-bound P 'x) (lambda (e) 'err))))
          (set! integrate::dv-count-cap old)
          (assert-equal 14 full)
          (assert-equal 1 (length data))
          (assert-equal 3 (car (car data)))
          (assert-equal 0 (modulo one full))
          (assert-equal 'unknown none))))))

(deftest "intdiv: R1.4 — #J рода 3 и 4 через дзета-функцию"
  ; y²=x⁷+1 (род 3), y²=x⁹−x (род 4), p = 3 (хорошее простое)
  (let ((J7 (integrate::hyp-jacobian-order-general '(+ (^ x 7) 1) 'x 3))
        (J9 (integrate::hyp-jacobian-order-general '(- (^ x 9) x) 'x 3)))
    (assert-equal 28 J7)
    (assert-equal 64 J9)
    ; (0,±1) — точки Вейерштрасса: их разность 2-кручение; у x⁹−x три
    ; рациональные точки Вейерштрасса 0,±1 ⇒ 2-кручение порядка 4
    (assert-equal 0 (modulo J7 2))
    (assert-equal 0 (modulo J9 4))))

(deftest "intdiv: R1.4 — подделка N_k ломает функциональное уравнение"
  ; g = 1, p = 5: строгая проверка по N1, N2
  (let* ((P '(+ (^ x 3) 1))
         (Ns (list (integrate::hyp-count-points-k P 'x 5 1)
                   (integrate::hyp-count-points-k P 'x 5 2)))
         (bad (cons (+ 2 (car Ns)) (cdr Ns))))
    (assert-true (integer? (integrate::hyp-jacobian-from-Ns Ns 5 1)))
    (assert-equal 'unknown (integrate::hyp-jacobian-from-Ns bad 5 1))))

; ---------- Шаг R1b.1: башня ℚ(α)(√b) и ℚ-базис вычетов ----------

(deftest "intdiv: R1b.1 — башня ℚ(i,√7): b ∉ ℚ(α), места и ℚ-базис вычетов"
  ; y² = x⁴+x²+7, g = x²+1: P(i) = 7 — не квадрат в ℚ(i), нужна башня ℚ(i)(√7)
  (assert-equal (list 'tower 7)
                (integrate::dv-g-branch '(+ (^ x 2) 1) '(+ (^ x 4) (^ x 2) 7) 'x))
  ; вычеты H = 1/(x²+1): −i/2 в двух местах над i и +i/2 над −i;
  ; координаты в ℚ-базисе 1, i, √7, i√7 (§1.3)
  (assert-equal '(((0 1) 0 -1/2 0 0) ((0 -1) 0 -1/2 0 0)
                  ((1 1) 0 1/2 0 0) ((1 -1) 0 1/2 0 0))
                (integrate::dv-tower-places '(+ (^ x 2) 1) 7 '(0 -1/2) '() 'x)))

(deftest "intdiv: R1b.1 — лог-ответ над x²+1 через ℚ-базис и подделки"
  (let* ((P '(+ (^ x 4) (^ x 2) 7))
         (H '(/ 1 (+ (^ x 2) 1)))
         (L (hyp-log-part H P 'x)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (hyp-log-check H P 'x L))
    (assert-equal 2 (cadr L))
    (assert-equal '%i (car (car (caddr L))))
    (let ((u (caddr (car (caddr L)))))
      ; неверный коэффициент и обратный логарифм — подделки
      (assert-equal #f (hyp-log-check H P 'x (list 'logs 2 (list (list '(* 2 %i) 1 u)))))
      (assert-equal #f (hyp-log-check H P 'x (list 'logs 2 (list (list '%i 1 (list '/ 1 u))))))))
  ; y/(x²+1): β-компонента вычетов требует u с коэффициентами башни —
  ; сейчас только честный unknown (не ложное nonelementary)
  (assert-equal 'unknown (hyp-log-part '(/ y (+ (^ x 2) 1)) '(+ (^ x 4) (^ x 2) 7) 'x)))

; ---------- Шаг R1b.2: y³ = P ----------

(deftest "intdiv: R1b.2 — y³=x⁴+1: лог-ответ через integrate и подделки"
  ; H = P′/(3y²(y−1)) = d/dx log(y−1), y³ = x⁴+1 (род 3)
  (let* ((P '(+ (^ x 4) 1))
         (H '(/ (* 4 (^ x 3)) (* 3 (^ y 2) (- y 1))))
         (L (integrate::hypn3-log-part H P 'x)))
    (assert-true (and (list? L) (equal? (car L) 'logs)))
    (assert-true (integrate::hypn3-log-check H P 'x L))
    ; подделки: неверный коэффициент и обратный логарифм
    (assert-equal #f (integrate::hypn3-log-check
                      H P 'x (list 'logs 1 (list (list 2 1 (list '- 'y 1))))))
    (assert-equal #f (integrate::hypn3-log-check
                      H P 'x (list 'logs 1 (list (list 1 1 (list '/ 1 (list '- 'y 1))))))))
  ; через integrate: радикальная форма P^{1/3}
  (assert-equal '(log (+ -1 (^ (+ 1 (^ x 4)) 1/3)))
                (integrate '(/ (* 4 (^ x 3))
                               (* 3 (^ (+ (^ x 4) 1) 2/3) (- (^ (+ (^ x 4) 1) 1/3) 1)))
                           'x)))

(deftest "intdiv: R1b.2 — вычеты над неприводимым g=x⁴−7 (пары ℚ(α,ζ₃))"
  ; b = 2 ∈ ℚ(α): 2³ ≡ P (mod x⁴−7)
  (assert-equal '(2) (integrate::hypn3-g-cube-root '(+ -7 (^ x 4)) '(+ (^ x 4) 1) 'x))
  ; H = 1/(y−2): полюс только в ветви k = 0 (y = 2); вычет 1/y′ = 3/α³ = 3α/7
  (assert-equal '(((+ -7 (^ x 4)) (2) ((0 (0 3/7) ()) (1 () ()) (2 () ()))))
                (integrate::hypn3-g-residues '(/ 1 (- y 2)) '(+ (^ x 4) 1) 'x)))

(deftest "intdiv: R1b.2 — ряд y(s) в ℚ(α,ζ₃)"
  ; y³ = x⁴+1, a = 0, b = 1: y = (1+s⁴)^{1/3}
  (assert-equal '(((1) ()) (() ()) (() ()) (() ()) ((1/3) ()))
                (integrate::hypn3-y-series-g '(+ (^ x 4) 1) 'x '(1) 0 'x 4))
  ; ветвь k = 1: y_0 = ζ
  (assert-equal '((() (1)) (() ()) (() ()) (() ()) (() (1/3)))
                (integrate::hypn3-y-series-g '(+ (^ x 4) 1) 'x '(1) 1 'x 4)))

(deftest "intdiv: R1b.2 — ряд в нормальном замыкании ℚ(α,i) при iα"
  ; y³ = x⁴+1, g = x⁴−7, b = 2, точка α_j = iα
  (let ((ys (integrate::hypn3-y-series-K '(+ (^ x 4) 1) '(+ -7 (^ x 4))
                                         (list '() (list 0 1)) 2 4)))
    ; y₁ = P′(iα)/(3·4) = −iα³/3
    (assert-equal '(() (0 0 0 -1/3)) (nth ys 1))
    (assert-equal '((67/972) ()) (nth ys 4))))

(deftest "intdiv: R1b.2 — строки Трагера в K(ζ₃): u=y−2 в ядре"
  ; 16 строк × 4 сопряжённых корня для u = c₀+c₁y+c₂y², c₀ = −2, c₁ = 1
  (let* ((P '(+ (^ x 4) 1))
         (g '(+ -7 (^ x 4)))
         (v (append (integrate::z-coords (integrate::z2-num -2))
                    (integrate::z-coords (integrate::z2-num 1))
                    (integrate::z-coords (integrate::z2-num 0)))))
    (assert-true
     (every? (lambda (a)
               (let ((rows (integrate::hypn3-F-place-rows P g a 0 2 1)))
                 (every? (lambda (row)
                           (= 0 (foldl + 0
                                       (integrate::dv-zip2 (lambda (x y) (* x y)) row v))))
                         rows)))
             (integrate::hypn3-g-roots)))))

; ---------- Шаг R1b.3: граница кручения рода >= 3 ----------

(deftest "intdiv: R1b.3 — строгая проверка 2g значений N_k (род 3)"
  ; y² = x⁷+1, p = 3: 6 значений N_k; #J = 28
  (let* ((P '(+ (^ x 7) 1))
         (ks (map (lambda (i) (+ i 1)) (range 6)))
         (Ns (map (lambda (k) (integrate::hyp-count-points-k P 'x 3 k)) ks)))
    (assert-equal 28 (integrate::hyp-jacobian-from-Ns Ns 3 3))
    ; подделка N_6 ломает симметрию L(T) -> unknown
    (let ((bad (let loop ((i 0) (xs Ns) (acc '()))
                 (if (null? xs)
                     (reverse acc)
                     (loop (+ i 1) (cdr xs)
                           (cons (if (= i 5) (+ 1 (car xs)) (car xs)) acc))))))
      (assert-equal 'unknown (integrate::hyp-jacobian-from-Ns bad 3 3)))))

(deftest "intdiv: R1b.3 — публичная граница кручения рода 3"
  ; y² = x⁷+1: #J(𝔽₃)=28, #J(𝔽₅) делится на 14 -> B = 14
  (assert-equal 14 (hyp-torsion-bound '(+ (^ x 7) 1) 'x)))

(deftest "integrate: кручение порядка 7 — ∫(28 − 5x)/(x√(4x³ − 15x² + 8x + 16)) берётся (точный сертификат при численном сокращении)"
  (conditions-clear)
  (let ((r (integrate '(/ (- 28 (* 5 x)) (* x (^ (+ (* 4 (^ x 3)) (* -15 (^ x 2)) (* 8 x) 16) 1/2))) 'x)))
    (assert-true (and (pair? r) (equal? (car r) 'log)))
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'certificate-exact-log)) (conditions)))))

; ---------- ST.1c: сертификат порядка δ законом сложения (род 1) ----------

(define ecc-P '(+ (* 4 (^ x 3)) (* -15 (^ x 2)) (* 8 x) 16))
(define (ecc-pl a b) (list a (integrate::dv-k-rat b)))
; δ = k₁·(0, 4) + k₂·(0, −4)
(define (ecc-D k1 k2) (list (cons (ecc-pl 0 4) k1) (cons (ecc-pl 0 -4) k2)))

(deftest "ec: таблица kT для y² = 4x³ − 15x² + 8x + 16, δ = (0,4) − (0,−4): T = 2·(0,4), порядок 7"
  (let ((ms (ec-multiples ecc-P 'x (ecc-D 1 -1) 7)))
    (assert-equal '((1 (4 -8)) (2 (2 -2)) (3 (0 -4)) (4 (0 4)) (5 (2 2)) (6 (4 8)) (7 O)) ms)
    (assert-true (ec-point-order-check ecc-P 'x (ecc-D 1 -1) 7))
    ; (0,4) само: 2T = (4,−8), 3T = (2,2), 4T = (2,−2), 5T = (4,8), 6T = (0,−4), 7T = O
    (assert-equal '((1 (0 4)) (2 (4 -8)) (3 (2 2)) (4 (2 -2)) (5 (4 8)) (6 (0 -4)) (7 O))
                  (ec-multiples ecc-P 'x (list (cons (ecc-pl 0 4) 1) (cons '(inf ram) -1)) 7))))

(deftest "ec: δ = 7·(0,4) − 7·(0,−4) — T = O, порядок 1"
  (assert-equal 'O (ec-divisor-sum ecc-P 'x (ecc-D 7 -7)))
  (assert-true (ec-point-order-check ecc-P 'x (ecc-D 7 -7) 1)))

(deftest "ec: подделки — неверный порядок, точка не на кривой, не deg 3, deg D ≠ 0"
  (assert-true (not (ec-point-order-check ecc-P 'x (ecc-D 1 -1) 6)))
  (assert-true (not (ec-point-order-check ecc-P 'x (ecc-D 1 -1) 14)))
  (assert-true (not (ec-point-order-check ecc-P 'x (ecc-D 1 -1) 1)))
  (assert-true (not (ec-point-order-check ecc-P 'x (list (cons (ecc-pl 0 5) 1) (cons (ecc-pl 0 -5) -1)) 7)))
  (assert-true (not (ec-point-order-check '(+ (^ x 4) 1) 'x (list (cons (ecc-pl 0 1) 1) (cons (ecc-pl 0 -1) -1)) 2)))
  (assert-true (not (ec-point-order-check ecc-P 'x (list (cons (ecc-pl 0 4) 1)) 7))))

(deftest "ec: точка 2-кручения (y = 0) и касательная; y² = x³ + x + 1 — δ не кручение"
  (let ((P '(+ (^ x 3) (* -1 x))))   ; y² = x³ − x, точки (0,0), (1,0), (−1,0) порядка 2
    (assert-true (ec-point-order-check P 'x (list (cons (list 0 'ram) 1) (cons '(inf ram) -1)) 2)))
  (let ((ms (ec-multiples '(+ (^ x 3) x 1) 'x (list (cons (ecc-pl 0 1) 1) (cons (ecc-pl 0 -1) -1)) 6)))
    (assert-equal '(1/4 -9/8) (cadr (car ms)))
    (assert-true (not (any? (lambda (km) (equal? (cadr km) 'O)) ms)))))
