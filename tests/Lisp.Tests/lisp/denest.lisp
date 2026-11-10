; denest.lisp — тесты шага A1.5: денестинг глубины 2 и нормальная форма ℚ(α).

(deftest "a15: денестинг глубины 2"
  ; √(3+2√2) = 1+√2
  (assert-true (alg-equal? (sqrt-denest '(^ (+ 3 (* 2 (^ 2 1/2))) 1/2))
                           '(+ 1 (^ 2 1/2))))
  ; √(5−2√6) = √3−√2
  (assert-true (alg-equal? (sqrt-denest '(^ (+ 5 (* -2 (^ 6 1/2))) 1/2))
                           '(- (^ 3 1/2) (^ 2 1/2))))
  ; √(2+√3) = (√6+√2)/2
  (assert-true (alg-equal? (sqrt-denest '(^ (+ 2 (^ 3 1/2)) 1/2))
                           '(/ (+ (^ 6 1/2) (^ 2 1/2)) 2)))
  ; √(1+√2) не денестится — остаётся
  (assert-equal (sqrt-denest '(^ (+ 1 (^ 2 1/2)) 1/2))
                '(^ (+ 1 (^ 2 1/2)) 1/2))
  ; форма sqrt(...) тоже обрабатывается
  (assert-true (alg-equal? (sqrt-denest '(sqrt (+ 3 (* 2 (sqrt 2)))))
                           '(+ 1 (^ 2 1/2)))))

(deftest "a15: сертификат денестинга отвергает неверный знак и чужой квадрат"
  ; (1+√2)² = 3+2√2 — верно; (−1−√2)² тоже верно, но значение отрицательно
  (assert-true (denest-check? '(+ 3 (* 2 (^ 2 1/2))) '(+ 1 (^ 2 1/2))))
  (assert-equal (denest-check? '(+ 3 (* 2 (^ 2 1/2))) '(- -1 (^ 2 1/2))) #f)
  ; чужой квадрат
  (assert-equal (denest-check? '(+ 5 (* -2 (^ 6 1/2))) '(+ 1 (^ 2 1/2))) #f))

(deftest "a15: alg-simplify — нормальная форма ℚ(α)"
  ; (√2+√3)² − 2√6 = 5
  (assert-equal (alg-simplify '(- (^ (+ (^ 2 1/2) (^ 3 1/2)) 2) (* 2 (^ 6 1/2)))) 5)
  ; 1/(1+√2) = √2−1
  (assert-true (alg-equal? (alg-simplify '(/ 1 (+ 1 (^ 2 1/2))))
                           '(- (^ 2 1/2) 1)))
  ; √2·√8 = 4
  (assert-equal (alg-simplify '(* (^ 2 1/2) (^ 8 1/2))) 4))

(deftest "a15: alg-equal? — точное равенство выражений с радикалами"
  (assert-true (alg-equal? '(+ (^ 2 1/2) (^ 3 1/2))
                           '(^ (+ 5 (* 2 (^ 6 1/2))) 1/2)))
  (assert-equal (alg-equal? '(+ (^ 2 1/2) (^ 3 1/2))
                            '(^ (+ 5 (* -2 (^ 6 1/2))) 1/2)) #f)
  ; без радикалов — обычное упрощение
  (assert-true (alg-equal? '(+ 1 1) 2))
  ; трёхаргументная форма (функция поля из algnum) продолжает работать
  (assert-true (alg-equal? (alg-field '(+ (^ t 2) -2) 't) '(0 1) '(0 1))))

; ---------- A1.6: точные корни в solve ----------

(deftest "a16: биквадратное x^4−10x^2+1 — четыре точных корня ±√2±√3"
  (let* ((p '(+ (^ x 4) (* -10 (^ x 2)) 1))
         (r (set->list (solve (list '= p 0) 'x))))
    (assert-equal (length r) 4)
    ; каждый корень даёт 0 в исходном многочлене (точная проверка в ℚ(α))
    (map (lambda (s)
           (assert-true (alg-equal? (expand (subst (list '= 'x s) p)) 0)))
         r)
    (assert-true (member? '(+ (^ 2 1/2) (^ 3 1/2)) r))
    (assert-true (member? '(+ (* -1 (^ 2 1/2)) (* -1 (^ 3 1/2))) r))))

(deftest "a16: квадратное над ℚ(√2) — корни √2±1"
  (let ((r (set->list (solve '(= (+ (^ x 2) (* -2 (^ 2 1/2) x) 1) 0) 'x))))
    (assert-true (member? '(+ -1 (^ 2 1/2)) r))
    (assert-true (member? '(+ 1 (^ 2 1/2)) r))
    (map (lambda (s)
           (assert-true (alg-equal? (expand (subst (list '= 'x s)
                                                   '(+ (^ x 2) (* -2 (^ 2 1/2) x) 1)))
                                    0)))
         r)))

(deftest "a16/a17: x^4−2 — четыре корня ±⁴√2, ±i⁴√2 (подстановка)"
  (let* ((p '(- (^ x 4) 2))
         (r (set->list (solve (list '= p 0) 'x))))
    (assert-equal (length r) 4)
    (map (lambda (s)
           (let ((v (num-abs (subst (list '= 'x s) p))))
             (assert-true (and (number? v) (< v 1/1000000000)))))
         r)))

(deftest "a16: сертификат отвергает поддельный корень"
  ; 1 не является корнем x^4−10x^2+1 (−8 ≠ 0) — сертификат обязан упасть
  (assert-error (denest::dn-cert-roots '(+ (^ x 4) (* -10 (^ x 2)) 1) 'x (list 1))))

; ---------- A1.7: комплексный денестинг ----------

(deftest "a17: solve x^4+1 — четыре комплексных корня ±√2/2 ± i√2/2"
  (let* ((p '(+ 1 (^ x 4)))
         (r (set->list (solve (list '= p 0) 'x))))
    (assert-equal (length r) 4)
    (assert-true (every? (lambda (s) (contains-sym? s '%i)) r))
    (map (lambda (s)
           (let ((v (num-abs (subst (list '= 'x s) p))))
             (assert-true (and (number? v) (< v 1/1000000000)))))
         r)
    ; точно в ℚ(i): (√2/2 + i√2/2)^4 + 1 = 0
    (assert-true (alg-equal?
                  (expand (subst (list '= 'x (list '+ (list '/ (list '^ 2 1/2) 2)
                                                       (list '* (list '/ (list '^ 2 1/2) 2) '%i)))
                                 p))
                  0))))

(deftest "a17: x^4+2x^2−1 — два вещественных и два мнимых корня"
  (let* ((p '(+ -1 (* 2 (^ x 2)) (^ x 4)))
         (r (set->list (solve (list '= p 0) 'x))))
    (assert-equal (length r) 4)
    (map (lambda (s)
           (let ((v (num-abs (subst (list '= 'x s) p))))
             (assert-true (and (number? v) (< v 1/1000000000)))))
         r)
    (assert-true (any? (lambda (s) (not (contains-sym? s '%i))) r))
    (assert-true (any? (lambda (s) (contains-sym? s '%i)) r))))

; ---------- WASM.6a Д6: radsimp от суммы/разности радикалов ----------

(deftest "WASM.6a Д6: radsimp суммы радикалов — без root-of"
  (let ((s (alg-simplify '(+ (^ 5 1/2) (^ 3 1/2))))
        (d (alg-simplify '(- (^ 5 1/2) (^ 3 1/2))))
        (i (alg-simplify '(/ 1 (- (^ 5 1/2) (^ 3 1/2))))))
    (assert-equal s '(+ (^ 3 1/2) (^ 5 1/2)))
    (assert-equal d '(+ (* -1 (^ 3 1/2)) (^ 5 1/2)))
    ; 1/(√5 − √3) = (√5 + √3)/2
    (assert-true (equal? i '(+ (* 1/2 (^ 3 1/2)) (* 1/2 (^ 5 1/2)))))
    (assert-true (not (contains-sym? i 'root-of)))
    (assert-true (< (abs (- (eval-num i) 1.9840593925343336)) 0.000000000001))))

(deftest "WASM.6a Д6: зависимые радикалы (√6 = √2·√3) сводятся к независимым"
  (let ((m (alg-simplify '(+ 1 (^ 2 1/2) (^ 3 1/2) (^ 6 1/2)))))
    (assert-true (not (contains-sym? m 'root-of)))
    (assert-true (< (abs (- (eval-num m) 6.59575411272515)) 0.000000000001))))
