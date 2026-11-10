; cfinite.lisp — тесты шага RE.1: C-конечные последовательности (точные сертификаты).

(define cf-fib (cfinite '(1 1) '(0 1)))
(define cf-luc (cfinite '(1 1) '(2 1)))
(define cf-mat '((1 1) (1 0)))

(deftest "re1: F(100) и F(1000) — известные значения"
  (assert-equal (cf-term cf-fib 100) 354224848179261915075)
  (assert-equal (cf-term cf-fib 1000)
                43466557686937456435688527675040625802564660517371780402481729089536555417949051890403879840079255169295922593080322634775209689623239873322471161642996440906533187938298969649928516003704476137795166849228875))

(deftest "re1: F(10^6) mod p совпадает у cf-term и cf-term-mod"
  (let ((p 1000000007))
    (assert-equal (modulo (cf-term cf-fib 1000000) p)
                  (cf-term-mod cf-fib 1000000 p))))

(deftest "re1: сверка с mat-power на n ≤ 200"
  (map (lambda (n)
         (assert-equal (cf-term cf-fib n)
                       (car (cadr (mat-power cf-mat n)))))
       '(1 2 5 20 50 200)))

(deftest "re1: cf-terms, cf-shift вперёд и назад"
  (assert-equal (cf-terms cf-fib 10) '(0 1 1 2 3 5 8 13 21 34))
  (assert-equal (cf-init (cf-shift cf-fib 3)) '(2 3))
  ; F(−1) = 1, F(−2) = −1
  (assert-equal (cf-init (cf-shift cf-fib -1)) '(1 0))
  (assert-equal (cf-init (cf-shift cf-fib -2)) '(-1 1)))

(deftest "re1: cf-from-terms угадывает рекуррентность n^2"
  (let ((g (cf-from-terms (map (lambda (n) (* n n)) (range 10)))))
    (assert-equal (cf-order g) 3)
    (assert-equal (cf-coeffs g) '(3 -3 1))
    (assert-equal (cf-init g) '(0 1 4))
    (assert-equal (cf-term g 20) 400)))

(deftest "re1: cf+, cf*, cf-scale, cf-partial-sum"
  (let ((s (cf+ cf-fib (cf-shift cf-fib 1)))
        (p (cf* cf-fib cf-luc))
        (q (cf-scale cf-fib 3))
        (ps (cf-partial-sum cf-fib)))
    ; F(n)+F(n+1) = F(n+2)
    (assert-true (<= (cf-order s) 4))
    (assert-equal (map (lambda (n) (cf-term s n)) (range 8))
                  (map (lambda (n) (cf-term cf-fib (+ n 2))) (range 8)))
    ; F(n)·L(n) = F(2n)
    (assert-true (<= (cf-order p) 4))
    (assert-equal (map (lambda (n) (cf-term p n)) (range 8))
                  (map (lambda (n) (cf-term cf-fib (* 2 n))) (range 8)))
    (assert-equal (cf-term q 10) (* 3 (cf-term cf-fib 10)))
    ; Σ_{k≤n} F(k) = F(n+2) − 1; порядок ≤ r+1 = 3
    (assert-true (<= (cf-order ps) 3))
    (assert-equal (cf-term ps 12) (- (cf-term cf-fib 14) 1))))

(deftest "re1: cf-check подтверждает рекуррентность; cf-from-terms проверяет данные"
  (let ((g (cf-from-terms (map (lambda (n) (* n n)) (range 10)))))
    (assert-true (cf-check g))
    (assert-equal (cf-term g 20) 400)
    ; другая рекуррентность даёт другие члены — коэффициент важен
    (assert-true (not (equal? (cf-term (cfinite '(4 -3 1) '(0 1 4)) 5)
                              (cf-term g 5))))))

; ---------- RE.2: доказательство тождеств ----------

(deftest "re2: доказанные тождества Фибоначчи"
  (map (lambda (pair)
         (let ((proof (cf-prove (car pair) (cadr pair))))
           (assert-equal (car proof) 'proved)
           (assert-true (cf-check-proof (car pair) (cadr pair) proof))))
       (list (list '(fib (* 2 n)) '(* (fib n) (lucas n)))
             (list '(- (* (fib (+ n 1)) (fib (- n 1))) (^ (fib n) 2)) '(^ -1 n))
             (list '(sum (fib k) k 0 n) '(- (fib (+ n 2)) 1))
             (list '(+ (^ (fib n) 2) (^ (fib (+ n 1)) 2)) '(fib (+ (* 2 n) 1))))))

(deftest "re2: ложное тождество — контрпример"
  (let ((proof (cf-prove '(fib (* 2 n)) '(* 2 (^ (fib n) 2)))))
    (assert-equal (car proof) 'disproved)
    ; F(2·1)=1, 2F(1)^2=2 — контрпример в точке 1
    (assert-equal (cadr proof) 1)
    (assert-equal (nth proof 2) 1)
    (assert-equal (nth proof 3) 2)
    (assert-true (cf-check-proof '(fib (* 2 n)) '(* 2 (^ (fib n) 2)) proof))))

(deftest "re2: cf-check-proof отвергает заниженное R"
  ; n² = n верно при n=0,1, но не при n=2; доказательство (proved 2) поддельное
  (assert-equal (car (cf-prove '(^ n 2) 'n)) 'disproved)
  (assert-equal (cf-check-proof '(^ n 2) 'n '(proved 2)) #f)
  (assert-true (cf-check-proof '(^ n 2) 'n (cf-prove '(^ n 2) 'n))))

(deftest "re2: не C-конечное выражение — ошибка"
  (assert-error (cf-prove '(factorial n) '(fib n))))

; ---------- RE.3: производящие функции и замкнутая форма ----------

(deftest "re3: cf->gf и gf->cf обратимы"
  (let ((pq (cf->gf cf-fib 'x)))
    (assert-equal pq '((0 1) (1 -1 -1)))
    (let ((s (gf->cf (car pq) (cadr pq))))
      (assert-equal (cf-coeffs s) (cf-coeffs cf-fib))
      (assert-equal (cf-init s) (cf-init cf-fib))
      (assert-equal (cf-term s 20) (cf-term cf-fib 20)))))

(deftest "re3: cf-closed-form — Бине, геометрическая, кратный корень"
  (let ((f (cf-closed-form cf-fib 'n)))
    (assert-true (not (equal? f #f)))
    (assert-true (= (eval-num (eval (subst '(n 10) f))) 55)))
  (assert-equal (cf-closed-form (cfinite '(2) '(1)) 'n) '(^ 2 n))
  (let ((g (cf-closed-form (cfinite '(2 -1) '(1 2)) 'n)))
    (assert-true (= (eval-num (eval (subst '(n 5) g))) 6))))
