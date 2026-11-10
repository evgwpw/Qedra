; Lisp-тесты мелких исправлений Шага 15b: case с несколькими выражениями, степень алгебраического числа,
; скаляр-выражение в тензорных операциях

(deftest "case: несколько выражений в ветке"
  (define x 0)
  (assert-equal (case 2 ((1) 'one) ((2 3) (set! x 10) (set! x (+ x 1)) x) (else 'other)) 11)
  (assert-equal x 11))

(deftest "case: else с несколькими выражениями и ветка по умолчанию"
  (assert-equal (case 9 ((1) 'one) (else 1 2 3)) 3)
  (assert-true (null? (case 9 ((1) 'one)))))

(deftest "case: пустая ветка — ошибка"
  (assert-error (case 1 ((1)))))

(deftest "case: последнее выражение хвостовое"
  (define (loop n) (case n ((0) 'done) (else (+ n 0) (loop (- n 1)))))
  (assert-equal (loop 100000) 'done))

(deftest "степень алгебраического числа: n >= 0"
  (assert-equal (^ (sqrt 2) 2) 2)
  (assert-equal (^ (sqrt 2) 4) 4)
  (assert-equal (^ (sqrt 2) 0) 1)
  (assert-equal (^ (sqrt 2) 1) (sqrt 2))
  (assert-true (= (^ (sqrt 2) 3) (* 2 (sqrt 2)))))

(deftest "степень алгебраического числа: n < 0 — символьная форма"
  (assert-equal (^ (sqrt 2) -1) (list '^ (sqrt 2) -1)))

(deftest "скаляр-выражение (+ a b) на вектор"
  (assert-equal (tensor->list (simplify (* (+ 'a 'b) (tensor '(1 2)))))
                '((+ a b) (* 2 (+ a b))))
  (assert-equal (tensor->list (scale (+ 'a 'b) '(1 2)))
                (tensor->list (simplify (* (+ 'a 'b) (tensor '(1 2)))))))

(deftest "outer: скаляр-выражение — скаляр, а не тензор"
  (assert-equal (tensor->list (outer (+ 'a 'b) (tensor '(1 2))))
                (tensor->list (scale (+ 'a 'b) (tensor '(1 2)))))
  (assert-equal (tensor->list (outer (tensor '(1 2)) (+ 'a 'b)))
                (tensor->list (scale (+ 'a 'b) (tensor '(1 2)))))
  (assert-equal (shape (+ 'a 'b)) '()))

; Шаг 20: производная невычисленного интеграла

(deftest "diff невычисленного неопределённого интеграла = подынтегральное"
  (assert-equal (diff 'x '(integrate (exp (^ x 2)) x)) '(exp (^ x 2)))
  (assert-equal (diff 'x '(integrate (sin (^ t 2)) t)) 0)
  (assert-equal (diff 'x (integrate '(sin x) 'x)) '(sin x)))

(deftest "diff определённого интеграла: правило Лейбница"
  (assert-equal (diff 'x '(integrate (exp (- (^ t 2))) t 0 x)) '(exp (* -1 (^ x 2))))
  (assert-equal (diff 'x '(integrate (exp t) t 0 (^ x 2))) '(* 2 x (exp (^ x 2))))
  (assert-equal (diff 'x '(integrate (exp t) t 1 2)) 0)
  (assert-equal (diff 'x '(integrate (sin t) t x (^ x 2)))
                (simplify '(- (* 2 x (sin (^ x 2))) (sin x)))))

(deftest "diff определённого интеграла: подынтегральное зависит от x"
  (assert-equal (diff 'x '(integrate (* x (exp t)) t 0 x))
                '(+ (* x (exp x)) (integrate (exp t) t 0 x))))

; шаг 21i: произведение/сумма алгебраических чисел — минимальный многочлен (неприводимый множитель результанта),
; а не результант степени deg p · deg q (r³ давал степень 64, подстановка корня в многочлен «зависала»)
(deftest "алгебраические числа: r·r, r³, r + r — минимальный многочлен степени 4"
  (let ((r (car (real-roots '(+ -1 (* -2 y) (^ y 3) (^ y 4)) 'y))))
    ; r² — корень y⁴ − y³ + 2y² − 4y + 1, r³ — корень y⁴ − 5y³ + 9y² − 5y − 1 (точная арифметика алгебраических чисел)
    (assert-equal (let ((s (* r r))) (+ (^ s 4) (- (^ s 3)) (* 2 (^ s 2)) (* -4 s) 1)) 0)
    (assert-equal (let ((s (^ r 3))) (+ (^ s 4) (* -5 (^ s 3)) (* 9 (^ s 2)) (* -5 s) -1)) 0)
    (assert-equal (- (* r r) (^ r 2)) 0)
    (assert-true (< (abs (- (eval-num (^ r 3)) (* (eval-num r) (eval-num r) (eval-num r)))) 0.000000001))
    (assert-true (< (abs (- (eval-num (+ r r)) (* 2 (eval-num r)))) 0.000000001))
    ; подстановка корня в многочлен (раньше — минуты)
    (assert-equal (simplify (subst (list '= 'y r) '(+ -1 x (^ y 3)))) (simplify (list '+ -1 'x (^ r 3))))))

; eval-num: гиперболические функции
(deftest "eval-num: sinh/cosh/tanh и обратные"
  (assert-equal (eval-num '(cosh 0)) 1.0)
  (assert-true (< (abs (- (eval-num '(sinh (log 2))) 0.75)) 0.000000001))
  (assert-true (< (abs (- (eval-num '(tanh (atanh 1/2))) 0.5)) 0.000000001))
  (assert-true (< (abs (- (eval-num '(cosh 1)) 1.5430806348152437)) 0.000000001))
  (assert-true (< (abs (- (eval-num '(coth 1)) 1.3130352854993313)) 0.000000001))
  (assert-true (< (abs (- (eval-num '(asinh -3)) -1.8184464592320668)) 0.000000001))
  (assert-equal (eval-num '(acosh 1)) 0.0)
  (assert-equal (eval-num '(atanh 0)) 0.0)
  (assert-true (< (abs (- (eval-num '(cosh (* %i 1))) (cos 1))) 0.000000001)))

(deftest "eval-num: гиперболические — полюсы не число, сертификаты с cosh"
  (assert-equal (eval-num '(coth 0)) '(coth 0))
  (assert-equal (eval-num '(atanh 1)) '(atanh 1))
  (assert-true (dsolve-check '(= (+ (diff (diff (y x) x) x) (* -1 (y x))) 0) '(cosh x) '(y x)))
  (assert-equal (dsolve-check '(= (+ (diff (diff (y x) x) x) (* -1 (y x))) 0) '(cos x) '(y x)) #f)
  (assert-true (int-check '(sinh x) '(cosh x) 'x)))

; WASM.6a Д3: eval-num знает обратные тригонометрические/гиперболические функции
(deftest "WASM.6a Д3: eval-num — acot, asec, acsc, acoth, asech, acsch"
  (map (lambda (x)
         (assert-true (< (abs (- (eval-num (list 'acot x))
                                 (- (/ (eval-num 'pi) 2) (eval-num (list 'atan x))))) 0.000000001))
         (assert-true (< (abs (- (eval-num (list 'asec x))
                                 (eval-num (list 'acos (/ 1 x))))) 0.000000001))
         (assert-true (< (abs (- (eval-num (list 'acsc x))
                                 (eval-num (list 'asin (/ 1 x))))) 0.000000001))
         (assert-true (< (abs (- (eval-num (list 'acoth x))
                                 (eval-num (list 'atanh (/ 1 x))))) 0.000000001))
         (assert-true (< (abs (- (eval-num (list 'acsch x))
                                 (eval-num (list 'asinh (/ 1 x))))) 0.000000001)))
       '(2 3 7 11/3 5/2))
  ; значения в пяти точках для asech (аргумент из (0, 1])
  (map (lambda (x)
         (assert-true (< (abs (- (eval-num (list 'asech x))
                                 (eval-num (list 'acosh (/ 1 x))))) 0.000000001)))
       '(1/2 1/3 1/4 2/7 9/10))
  ; известные значения
  (assert-true (< (abs (- (eval-num '(acot 1)) (/ (eval-num 'pi) 4))) 0.000000001))
  (assert-true (< (abs (- (eval-num '(asec 2)) (/ (eval-num 'pi) 3))) 0.000000001))
  (assert-true (< (abs (- (eval-num '(acsch 1)) (eval-num '(asinh 1)))) 0.000000001)))
