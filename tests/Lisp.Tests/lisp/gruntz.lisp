; Lisp-тесты алгоритма Грунца (lib\gruntz.lisp), шаг 21j.1.
; Эталоны — таблица 8.1–8.20 диссертации Грунца и классические примеры пределов.
; Где осмысленно, ответ сверяется численно: значение выражения в большой точке x0 (eval-num).

(define (grt-lim e) (gruntz-limitinf e 'x))
(define (grt-set-equal? a b)
  (and a b (= (length a) (length b)) (every? (lambda (u) (member? u b)) a)))
(define (grt-mrv-is e expected)
  (assert-true (grt-set-equal? (gruntz-mrv e 'x) (map simplify expected))))
(define (grt-num e x0) (eval-num (subst (list '= 'x x0) e)))
; ответ Грунца равен ожидаемому, а значение в x0 близко к нему (для ±inf — по модулю больше tol)
(define (grt-check e expected x0 tol)
  (assert-equal (grt-lim e) expected)
  (let ((v (grt-num e x0)))
    (cond ((equal? expected 'inf) (assert-true (> v tol)))
          ((equal? expected '-inf) (assert-true (< v (- 0 tol))))
          (else (assert-true (< (num-abs (- v (eval-num expected))) tol))))))

(deftest "грунц: сравнение классов роста (test_compare1–3)"
  (assert-equal (gruntz-compare 2 'x 'x) '<)
  (assert-equal (gruntz-compare 'x '(exp x) 'x) '<)
  (assert-equal (gruntz-compare '(exp x) '(exp (^ x 2)) 'x) '<)
  (assert-equal (gruntz-compare '(exp (^ x 2)) '(exp (exp x)) 'x) '<)
  (assert-equal (gruntz-compare 1 '(exp (exp x)) 'x) '<)
  (assert-equal (gruntz-compare 'x 2 'x) '>)
  (assert-equal (gruntz-compare '(exp x) 'x 'x) '>)
  (assert-equal (gruntz-compare '(exp (exp x)) '(exp (^ x 2)) 'x) '>)
  (assert-equal (gruntz-compare 2 3 'x) '=)
  (assert-equal (gruntz-compare 3 -5 'x) '=)
  (assert-equal (gruntz-compare 'x '(^ x 2) 'x) '=)
  (assert-equal (gruntz-compare '(^ x 3) '(/ 1 x) 'x) '=)
  (assert-equal (assuming ((m reals)) (gruntz-compare '(/ 1 x) '(^ x m) 'x)) '=)
  (assert-equal (gruntz-compare '(exp x) '(exp (- x)) 'x) '=)
  (assert-equal (gruntz-compare '(exp (- x)) '(exp (* 2 x)) 'x) '=)
  (assert-equal (gruntz-compare '(exp (* 2 x)) '(^ (exp x) 2) 'x) '=)
  (assert-equal (gruntz-compare '(^ (exp x) 2) '(exp (+ x (exp (- x)))) 'x) '=)
  (assert-equal (gruntz-compare '(exp x) '(exp (+ x (exp (- x)))) 'x) '=)
  (assert-equal (gruntz-compare '(exp (^ x 2)) '(/ 1 (exp (^ x 2))) 'x) '=)
  ; test_compare2, test_compare3
  (assert-equal (gruntz-compare '(exp x) '(^ x 5) 'x) '>)
  (assert-equal (gruntz-compare '(exp (^ x 2)) '(^ (exp x) 2) 'x) '>)
  (assert-equal (gruntz-compare '(exp (+ x (exp (- x)))) '(exp (- x)) 'x) '=)
  (assert-equal (gruntz-compare '(exp (- x)) 'x 'x) '>)
  (assert-equal (gruntz-compare 'x '(exp (- x)) 'x) '<)
  (assert-equal (gruntz-compare '(exp (+ x (/ 1 x))) 'x 'x) '>)
  (assert-equal (gruntz-compare '(exp (- (exp x))) '(exp x) 'x) '>)
  (assert-equal (gruntz-compare '(exp (+ (exp (- (exp x))) x)) '(exp (- (exp x))) 'x) '<)
  (assert-equal (gruntz-compare '(exp (exp x)) '(exp (+ x (exp (- (exp x))))) 'x) '>))

(deftest "грунц: знак при x → ∞ (test_sign1–2)"
  (assert-equal (gruntz-sign 0 'x) 0)
  (assert-equal (gruntz-sign 3 'x) 1)
  (assert-equal (gruntz-sign -5 'x) -1)
  (assert-equal (gruntz-sign '(log x) 'x) 1)
  (assert-equal (gruntz-sign '(exp (- x)) 'x) 1)
  (assert-equal (gruntz-sign '(exp x) 'x) 1)
  (assert-equal (gruntz-sign '(- (exp x)) 'x) -1)
  (assert-equal (gruntz-sign '(- 3 (/ 1 x)) 'x) 1)
  (assert-equal (gruntz-sign '(- -3 (/ 1 x)) 'x) -1)
  (assert-equal (gruntz-sign '(sin (/ 1 x)) 'x) 1)
  (assert-equal (gruntz-sign '(^ x 2) 'x) 1)
  (assert-equal (gruntz-sign '(^ x 5) 'x) 1)
  (assert-equal (gruntz-sign 'x 'x) 1)
  (assert-equal (gruntz-sign '(- x) 'x) -1)
  (assuming ((y positive))
    (assert-equal (gruntz-sign 'y 'x) 1)
    (assert-equal (gruntz-sign '(- y) 'x) -1)
    (assert-equal (gruntz-sign '(* y x) 'x) 1)
    (assert-equal (gruntz-sign '(- (* y x)) 'x) -1))
  ; знак константы без деклараций неизвестен — «не знаю», а не угадывание
  (assert-equal (gruntz-sign 'y 'x) #f))

(deftest "грунц: mrv-множества (test_mrv1–4)"
  (grt-mrv-is 'x '(x))
  (grt-mrv-is '(+ x (/ 1 x)) '(x))
  (grt-mrv-is '(^ x 2) '(x))
  (grt-mrv-is '(log x) '(x))
  (grt-mrv-is '(exp x) '((exp x)))
  (grt-mrv-is '(exp (- x)) '((exp (- x))))
  (grt-mrv-is '(exp (^ x 2)) '((exp (^ x 2))))
  (grt-mrv-is '(- (exp (/ 1 x))) '(x))
  (grt-mrv-is '(exp (+ x (/ 1 x))) '((exp (+ x (/ 1 x)))))
  ; test_mrv2a–c
  (grt-mrv-is '(exp (+ x (exp (- (exp x))))) '((exp (- (exp x)))))
  (grt-mrv-is '(exp (+ x (exp (- x)))) '((exp (+ x (exp (- x)))) (exp (- x))))
  (grt-mrv-is '(exp (+ (/ 1 x) (exp (- x)))) '((exp (- x))))
  (grt-mrv-is '(exp (+ x (exp (- (^ x 2))))) '((exp (- (^ x 2)))))
  (grt-mrv-is '(- (exp (+ (- x) (/ 1 (^ x 2)))) (exp (+ x (/ 1 x)))) '((exp (+ x (/ 1 x))) (exp (+ (- x) (/ 1 (^ x 2))))))
  ; test_mrv3, test_mrv4
  (grt-mrv-is '(+ (exp (^ x 2)) (* x (exp x)) (/ (^ (log x) x) x)) '((exp (^ x 2))))
  (grt-mrv-is '(* (exp x) (- (exp (+ (/ 1 x) (exp (- x)))) (exp (/ 1 x)))) '((exp x) (exp (- x))))
  (grt-mrv-is '(log (+ (^ x 2) (* 2 (exp (exp (* 3 (^ x 3) (log x))))))) '((exp (exp (* 3 (^ x 3) (log x))))))
  (grt-mrv-is '(/ (log (- x (log x))) (log x)) '(x))
  (grt-mrv-is '(- (/ 1 (exp (+ (- x) (exp (- x))))) (exp x)) '((exp x) (exp (- x)) (exp (- x (exp (- x))))))
  (grt-mrv-is '(log (log (+ (* x (exp (* x (exp x)))) 1))) '((exp (* x (exp x)))))
  (grt-mrv-is '(/ (* (log x) (- (log (+ (log x) (log (log x)))) (log (log x)))) (log (+ (log x) (log (log (log x)))))) '(x))
  ; exp(exp(log(log x + 1/x))): simplify сворачивает exp(log u) раньше mrv, остаётся exp(log x + 1/x) того же класса,
  ; что x (у эталон — {x}); множество другое, но верное
  (grt-mrv-is '(exp (exp (log (+ (log x) (/ 1 x))))) '((exp (+ (log x) (/ 1 x))) x)))

(deftest "грунц: ведущий член (test_mrv_leadterm1–2)"
  (assert-equal (gruntz-leadterm '(- (exp (/ 1 x))) 'x) '(-1 0))
  (assert-equal (gruntz-leadterm '(- (/ 1 (exp (+ (- x) (exp (- x))))) (exp x)) 'x) '(-1 0))
  (assert-equal (gruntz-leadterm '(* (- (exp (- (/ 1 x) (exp (- x)))) (exp (/ 1 x))) (exp x)) 'x)
                (list (simplify '(- (exp (/ 1 x)))) 0))
  ; пример 3.25 диссертации
  (assert-equal (gruntz-leadterm '(* (/ (- (log (+ (exp x) x)) x) (log (+ (exp x) (log x)))) (exp x)) 'x) '(1 0)))

(deftest "грунц: простые пределы (test_limit1–2)"
  (assert-equal (grt-lim 'x) 'inf)
  (assert-equal (grt-lim '(- x)) '-inf)
  (assert-equal (grt-lim '(- (^ x 2))) '-inf)
  (assert-equal (grt-lim '(/ 1 x)) 0)
  (assert-equal (grt-lim '(exp x)) 'inf)
  (assert-equal (grt-lim '(- (exp x))) '-inf)
  (assert-equal (grt-lim '(/ (exp x) x)) 'inf)
  (assert-equal (grt-lim '(- (/ 1 x) (exp (- x)))) 0)
  (assert-equal (grt-lim '(+ x (/ 1 x))) 'inf)
  (assert-equal (grt-lim '(+ 1 (/ 1 x))) 1)
  (assert-equal (grt-lim '(+ x (exp (- x)))) 'inf)
  (assert-equal (grt-lim '(+ x (exp (- (^ x 2))))) 'inf)
  (assert-equal (grt-lim '(+ x (exp (- (exp x))))) 'inf)
  (grt-check '(- (exp (/ 1 x))) -1 1000.0 0.01)
  (grt-check '(+ 13 (/ 1 x) (- (exp (- x)))) 13 1000.0 0.01)
  ; x → 0+ сводится к x → +∞ заменой x → 1/x: x·log x → 0, x^x → 1
  (grt-check '(* (/ 1 x) (log (/ 1 x))) 0 1000000.0 0.001)
  (grt-check '(^ (/ 1 x) (/ 1 x)) 1 1000000.0 0.001)
  (grt-check '(/ (log x) x) 0 1000000.0 0.001)
  (grt-check '(^ x (/ 1 x)) 1 1000000.0 0.001)
  (grt-check '(^ (+ 1 (/ 1 x)) x) '(exp 1) 1000000.0 0.001)
  (grt-check '(- (sqrt (+ (^ x 2) x)) x) 1/2 1000000.0 0.001)
  (grt-check '(* x (sin (/ 1 x))) 1 1000.0 0.001))

(deftest "грунц: x − log(a + eˣ) и eˣ/(a + eˣ) (test_limit3)"
  (grt-check '(- x (log (+ 1 (exp x)))) 0 30.0 0.000001)
  (grt-check '(/ (exp x) (+ 1 (exp x))) 1 30.0 0.000001)
  ; параметр a без деклараций: знак a не нужен — ответ есть
  (assert-equal (grt-lim '(- x (log (+ a (exp x))))) 0)
  (assert-equal (grt-lim '(/ (exp x) (+ a (exp x)))) 1)
  (assert-true (< (num-abs (grt-num '(- x (log (+ 3 (exp x)))) 30.0)) 0.000001)))

(deftest "грунц: гиперболические функции (x → ±∞ через x → −x)"
  (assert-equal (grt-lim '(cosh x)) 'inf)
  (assert-equal (grt-lim '(cosh (- x))) 'inf)
  (assert-equal (grt-lim '(sinh x)) 'inf)
  (assert-equal (grt-lim '(sinh (- x))) '-inf)
  (assert-equal (grt-lim '(* 2 (cosh x) (exp x))) 'inf)
  (assert-equal (grt-lim '(* 2 (cosh (- x)) (exp (- x)))) 1)
  (assert-equal (grt-lim '(* 2 (sinh x) (exp x))) 'inf)
  (assert-equal (grt-lim '(* 2 (sinh (- x)) (exp (- x)))) -1)
  (assert-equal (grt-lim '(tanh x)) 1)
  (assert-equal (grt-lim '(tanh (- x))) -1)
  (assert-equal (grt-lim '(coth x)) 1)
  (assert-equal (grt-lim '(coth (- x))) -1)
  (grt-check '(* 2 (exp (- x)) (/ (+ (exp x) (exp (- x))) 2)) 1 20.0 0.000001))

(deftest "грунц: трудные пределы диссертации 8.1–8.8"
  (grt-check '(* (exp x) (- (exp (- (/ 1 x) (exp (- x)))) (exp (/ 1 x)))) -1 25.0 0.05)
  (grt-check '(* (exp x) (- (exp (+ (/ 1 x) (exp (- x)) (exp (- (^ x 2))))) (exp (- (/ 1 x) (exp (- (exp x)))))))
             1 25.0 0.05)
  (assert-equal (grt-lim '(- (exp (/ (exp (- x (exp (- x)))) (- 1 (/ 1 x)))) (exp (exp x)))) 'inf)
  (assert-equal (grt-lim '(- (exp (exp (/ (exp x) (- 1 (/ 1 x)))))
                             (exp (exp (/ (exp x) (- 1 (/ 1 x) (^ (log x) (- (log x))))))))) '-inf)
  (assert-equal (grt-lim '(/ (exp (exp (exp (+ x (exp (- x)))))) (exp (exp (exp x))))) 'inf)
  (assert-equal (grt-lim '(/ (exp (exp (exp x))) (exp (exp (exp (- x (exp (- (exp x))))))))) 'inf)
  (assert-equal (grt-lim '(/ (exp (exp (exp x))) (exp (exp (exp (- x (exp (- (exp (exp x)))))))))) 1)
  (assert-equal (grt-lim '(/ (exp (exp x)) (exp (exp (- x (exp (- (exp (exp x))))))))) 1)
  (assert-equal (grt-lim '(/ (exp (exp (exp (+ x (exp (- x)))))) (exp (exp x)))) 'inf))

(deftest "грунц: трудные пределы диссертации 8.10–8.20"
  (assert-equal (grt-lim '(/ (* x (log x) (^ (log (- (* x (exp x)) (^ x 2))) 2))
                             (log (log (+ (^ x 2) (* 2 (exp (exp (* 3 (^ x 3) (log x)))))))))) 1/3)
  (grt-check '(/ (- (exp (/ (* x (exp (- x))) (+ (exp (- x)) (exp (/ (* -2 (^ x 2)) (+ x 1)))))) (exp x)) x)
             '(* -1 (exp 2)) 30.0 0.5)
  (grt-check '(/ x (log (^ x (log (^ x (/ (log 2) (log x))))))) 'inf 1000.0 100)
  (assert-equal (grt-lim '(/ (exp (exp (* 2 (log (+ (^ x 5) x)) (log (log x))))) (exp (exp (* 10 (log x) (log (log x))))))) 'inf)
  (grt-check '(/ (- (exp (/ (* 4 x (exp (- x))) (+ (/ 1 (exp x)) (/ 1 (exp (/ (* 2 (^ x 2)) (+ x 1))))))) (exp x)) (^ (exp x) 4))
             1 30.0 0.000001)
  (grt-check '(/ (exp (/ (* x (exp (- x))) (+ (exp (- x)) (exp (/ (* -2 (^ x 2)) (+ x 1)))))) (exp x)) 1 30.0 0.000001)
  (let* ((a '(/ (- x) (+ 1 (exp (- x)))))
         (e (list '+ (list '/ (list '* (list 'exp (list 'exp a)) (list 'exp (list '/ '(- x) (list '+ 1 (list 'exp a))))
                                     (list 'exp (list 'exp (list '+ '(- x) (list 'exp a)))))
                           (list '^ (list 'exp a) 2))
                  '(- (exp x)) 'x)))
    (assert-equal (grt-lim e) 2))
  (grt-check '(/ (* (log x) (- (log (+ (log x) (log (log x)))) (log (log x)))) (log (+ (log x) (log (log (log x))))))
             1 1e300 0.01)
  (assert-equal (grt-lim '(exp (/ (log (log (+ x (exp (* (log x) (log (log x)))))))
                                  (log (log (log (+ (exp x) x (log x))))))))
                '(exp 1)))

(deftest "грунц: прочие эталоны"
  ; test_gruntz_eval_special, первая строка: sin с аргументом, имеющим конечный предел
  (grt-check '(* (exp x) (- (sin (+ (/ 1 x) (exp (- x)))) (sin (+ (/ 1 x) (exp (- (^ x 2))))))) 1 25.0 0.01)
  ; test_issue_24210_25885, test_exp_log_series, test_issue_4814, test_issue_3644
  (grt-check '(/ (exp x) (^ (+ 1 (/ 1 x)) (^ x 2))) '(exp 1/2) 100.0 0.01)
  (assert-equal (grt-lim '(/ (^ (+ 1 (/ 1 x)) (^ x 2)) (exp x))) '(exp -1/2))
  (grt-check '(/ x (log (log (* x (exp x))))) 'inf 500.0 50)
  (grt-check '(^ (+ x 1) (/ 1 (log (+ x 1)))) '(exp 1) 1000.0 0.000001)
  (grt-check '(^ (/ (+ (^ x 7) x 1) (+ (^ 2 x) (^ x 2))) (/ -1 x)) 2 1000.0 0.2)
  ; вручную: eˣ − e^(x + e^(−x)) → −1
  (grt-check '(- (exp x) (exp (+ x (exp (- x))))) -1 20.0 0.000001))

(deftest "грунц: «не знаю» вместо угадывания"
  ; ограниченная осцилляция, неподдерживаемые функции, отрицательное основание степени с переменным показателем
  (assert-equal (grt-lim '(sin x)) #f)
  (assert-equal (grt-lim '(* x (sin x))) #f)
  (assert-equal (grt-lim '(floor x)) #f)
  (assert-equal (grt-lim '(f x)) #f)
  (assert-equal (grt-lim '(^ (- x) x)) #f)
  ; показатель ω — сравнение констант с параметром не определяется: (a^x + 5^x)^(1/x), c = log 5/log a — «не знаю»
  (assert-equal (grt-lim '(^ (+ (^ a x) (^ 5 x)) (/ 1 x))) #f)
  (assuming ((a positive))
    (assert-equal (grt-lim '(^ (+ (^ a x) (^ 5 x)) (/ 1 x))) #f))
  ; ряд по τ слишком большого порядка не строится — прямой подсчёт; при отказе обоих — «не знаю», а не ошибка
  (assert-equal (grt-lim '(+ (exp x) (sin (exp x)))) #f)
  ; бюджет: при пределе в 2 вызова — «не знаю», а не переполнение стека
  (let ((old gruntz::gr-max-calls))
    (set! gruntz::gr-max-calls 2)
    (unwind-protect
      (assert-equal (grt-lim '(* (exp x) (- (exp (- (/ 1 x) (exp (- x)))) (exp (/ 1 x))))) #f)
      (set! gruntz::gr-max-calls old)))
  (assert-equal (grt-lim '(* (exp x) (- (exp (- (/ 1 x) (exp (- x)))) (exp (/ 1 x))))) -1)
  (assert-error (gruntz-limitinf 'x '(+ x 1))))

(deftest "грунц: параметры — знак только из деклараций"
  ; a^x: нужен знак a − 1; без деклараций — «не знаю» и условие в канале conditions
  (let ((r (capture-conditions (lambda () (grt-lim '(^ a x))))))
    (assert-equal (car r) #f)
    (assert-true (assoc '(gruntz-sign-unknown a) (cadr r))))
  (assuming ((a positive))
    (let ((r (capture-conditions (lambda () (grt-lim '(^ a x))))))
      (assert-equal (car r) #f)
      (assert-true (assoc '(gruntz-sign-unknown (+ -1 a)) (cadr r))))
    (assert-equal (grt-lim '(* a (exp x))) 'inf)
    (assert-equal (grt-lim '(* (- a) (exp x))) '-inf))
  (assert-equal (grt-lim '(^ 2 x)) 'inf)
  (assert-equal (grt-lim '(^ 1/2 x)) 0)
  (assert-equal (grt-lim '(* a (exp x))) #f))

; ---------- подшаг 21j.2: нецелые показатели ω ----------

(deftest "грунц: дробные показатели ω — 8.9 и 8.15 (ω = τ^q)"
  ; 8.9: ω^(−1/2) при подъёме x → eˣ (sqrt log x → sqrt x); ответ 0
  (let ((e '(/ (* (^ (log x) 2) (exp (* (sqrt (log x)) (^ (log (log x)) 2)
                                        (exp (* (sqrt (log (log x))) (^ (log (log (log x))) 3))))))
                (sqrt x))))
    (assert-equal (grt-lim e) 0)
    ; тот же ответ через прямой подсчёт без рядов (gr-max-q = 1 отключает ряд по τ при q > 1)
    (let ((old gruntz::gr-max-q))
      (set! gruntz::gr-max-q 1)
      (unwind-protect (assert-equal (grt-lim e) 0)
        (set! gruntz::gr-max-q old))))
  ; 8.15: показатели 5/7, 6/11, 49/45 — q = 315 > gr-max-q, прямой подсчёт; ответ +∞
  (assert-equal (grt-lim '(/ (^ (exp (exp (+ (* 5/2 (^ x -5/7)) (* 21/8 (^ x 6/11)) (* 2 (^ x -8)) (* 54/17 (^ x 49/45))))) 8)
                             (^ (log (log (- (log (* 4/3 (^ x -5/14)))))) 7/6)))
                'inf)
  ; свои: ряд по τ, q = 2
  (grt-check '(* (sqrt x) (- (exp (/ 1 (sqrt x))) 1)) 1 1000000.0 0.001)
  (grt-check '(/ (exp (sqrt (+ x 1))) (exp (sqrt x))) 1 1000000.0 0.001)
  (assert-equal (grt-lim '(* x (- (exp (/ 1 (sqrt x))) 1))) 'inf)
  (assert-equal (grt-lim '(/ (exp (^ x 1/3)) (exp (sqrt x)))) 0)
  (grt-check '(- (^ (+ (^ x 3) 1) 1/3) x) 0 1000000.0 0.001)
  (grt-check '(- (sqrt (+ (^ x 2) x)) x) 1/2 1000000.0 0.001))

(deftest "грунц: иррациональные показатели ω — 8.12 и родственные (log 5/log 3)"
  (grt-check '(^ (+ (^ 3 x) (^ 5 x)) (/ 1 x)) 5 200.0 0.000001)
  (grt-check '(^ (+ (^ 2 x) (^ 3 x)) (/ 1 x)) 3 200.0 0.000001)
  (grt-check '(^ (+ (^ 2 x) (^ 3 x) (^ 5 x)) (/ 1 x)) 5 200.0 0.000001)
  (grt-check '(^ (- (^ 5 x) (^ 3 x)) (/ 1 x)) 5 200.0 0.000001)
  (grt-check '(^ (+ (^ 2 x) (^ 4 x)) (/ 1 x)) 4 200.0 0.000001)
  (grt-check '(^ (+ (^ 1/2 x) (^ 2 x)) (/ 1 x)) 2 200.0 0.000001)
  (grt-check '(/ (^ (+ (^ 3 x) (^ 5 x)) (/ 1 x)) 5) 1 200.0 0.000001)
  (grt-check '(^ (+ (^ 2 x) (^ 3 x)) (/ -1 x)) 1/3 200.0 0.000001)
  (grt-check '(/ (log (+ (^ 3 x) (^ 5 x))) x) '(log 5) 200.0 0.000001)
  ; ответ — константа с логарифмами: lim ln(3ˣ+5ˣ)/ln(2ˣ+7ˣ) = ln 5/ln 7
  (grt-check '(/ (log (+ (^ 3 x) (^ 5 x))) (log (+ (^ 2 x) (^ 7 x)))) '(* (log 5) (^ (log 7) -1)) 200.0 0.000001)
  ; ответ — рациональная степень без exp(log): 3^(−1) = 1/3
  (assert-equal (grt-lim '(^ (+ (^ 2 x) (^ 3 x)) (/ -1 x))) 1/3))
