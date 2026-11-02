; ode-kovacic.lisp — ODE.8a: алгоритм Ковачича (нормальная форма, условия случаев, случай 1).

(define (okv-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (okv-has? s sub) (string-contains? s sub))
(define (okv-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (okv-cert r) (nth r 14))
(define (okv-sols r) (ode-solutions r))

(deftest "Ковачич: Эйри y″ = x·y — доказанный no-liouvillian и сертификат отсева"
  (let* ((eq '(= (diff (diff (y x) x) x) (* x (y x))))
         (r (dsolve eq '(y x)))
         (s (okv-text (lambda () (dsolve eq '(y x))) 'brief)))
    (assert-equal (ode-status r) 'no-liouvillian)
    (assert-equal (nth r 12) 'kovacic)
    ; ODE.9: к доказанному отказу добавлен ответ через Ai/Bi (решение не лиувиллево)
    (assert-true (pair? (okv-sols r)))
    (assert-true (string-contains? (to-string (okv-sols r)) "airy-ai"))
    ; сертификат независимо перепроверяется
    (assert-true (kovacic-check eq (okv-cert r) '(y x)))
    ; отсев: o(∞) = −1, полюсов нет, все три случая невозможны
    (assert-true (okv-has? s "лиувиллевых решений нет"))
    (assert-true (okv-has? s "o(∞) = -1"))
    (assert-true (okv-has? s "все нарушены"))
    ; подделка: «полюс порядка 2» и ложные условия
    (assert-equal (kovacic-check eq '(kovacic-none ((0 2)) -1 (#f #t #f)) '(y x)) #f)
    ; пустой и вырожденный сертификат
    (assert-equal (kovacic-check eq '() '(y x)) #f)
    (assert-equal (kovacic-check eq '(kovacic-none) '(y x)) #f)
    (assert-true (<= (okv-lines s) 15))))

(deftest "Ковачич: y″ = (x²+1)y — случай 1, y₁ = e^{x²/2}"
  (let* ((eq '(= (diff (diff (y x) x) x) (* (+ (^ x 2) 1) (y x))))
         (r (dsolve eq '(y x)))
         (s (okv-text (lambda () (dsolve eq '(y x))) 'brief))
         (sol (car (okv-sols r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (nth r 12) 'kovacic)
    (assert-true (okv-has? s "случай 1"))
    (assert-true (okv-has? s "ω = x"))
    ; y₁ = e^{x²/2} проверяется подстановкой; y₂ — по формуле понижения порядка
    (assert-equal (dsolve-check eq '(= (y x) (exp (* 1/2 (^ x 2)))) '(y x)) #t)
    (assert-true (kovacic-check eq (okv-cert r) '(y x)))
    (assert-true (okv-has? (to-string (okv-sols r)) "integrate"))
    ; подделка ω (x → x+1) и подделка P
    (let ((c (okv-cert r)))
      (assert-equal (kovacic-check eq (list 'kovacic-case1 (nth c 1) (nth c 2) '(+ x 1) (nth c 4) (nth c 5)) '(y x)) #f)
      (assert-equal (kovacic-check eq (list 'kovacic-case1 (nth c 1) (nth c 2) (nth c 3) '(+ x 1) (nth c 5)) '(y x)) #f))
    (assert-true (<= (okv-lines s) 15))))

(deftest "Ковачич: Бессель ν = 1/2 — cos x/√x и sin x/√x"
  (let* ((eq '(= (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x))
                   (* (- (^ x 2) 1/4) (y x))) 0))
         (r (dsolve eq '(y x)))
         (st (to-string (okv-sols r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (nth r 12) 'kovacic)
    ; вещественная форма, без %i
    (assert-true (not (string-contains? st "%i")))
    (assert-true (okv-has? st "cos x"))
    (assert-true (okv-has? st "sin x"))
    (assert-true (kovacic-check eq (okv-cert r) '(y x)))
    (assert-equal (dsolve-check eq (car (okv-sols r)) '(y x)) #t)))

(deftest "Ковачич: y″ − 2xy′ + 2y = 0 — y₁ = x"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* -2 x (diff (y x) x)) (* 2 (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (nth r 12) 'kovacic)
    (assert-equal (dsolve-check eq '(= (y x) x) '(y x)) #t)
    (assert-true (kovacic-check eq (okv-cert r) '(y x)))
    ; ответ — линейная комбинация x и второго решения
    (assert-true (okv-has? (to-string (okv-sols r)) "C1 x"))))

(deftest "Ковачич: общий шаг проверки не перебивает сертификат (method kovacic вне ode-check)"
  (let* ((eq '(= (diff (diff (y x) x) x) (* (+ (^ x 2) 1) (y x))))
         (s (okv-text (lambda () (dsolve eq '(y x))) 'brief)))
    ; в brief нет общего шага «Проверка решения» с ложным «не даёт 0»
    (assert-true (not (okv-has? s "подстановка не даёт 0")))
    (assert-true (okv-has? s "y₁ проверено подстановкой"))))

(deftest "Ковачич: случай 2 — z″ = (1/x − 3/(16x²))z, ω = 1/(4x) ± 1/√x"
  (let* ((eq '(= (diff (diff (y x) x) x) (* (+ (/ 1 x) (* -3/16 (^ x -2))) (y x))))
         (r (dsolve eq '(y x)))
         (s (okv-text (lambda () (dsolve eq '(y x))) 'brief))
         (st (to-string (okv-sols r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (nth r 12) 'kovacic)
    (assert-true (okv-has? s "случай 2"))
    ; интеграл упрощён: x·(4/x)^{1/2} → 2√x (в показателе exp)
    ; ревью (слияние): форма зависит от упрощателя (2√x или ½·4√x, log x или log √x) — проверяем суть
    (assert-true (okv-has? st "(^ x 1/2)"))
    (assert-true (okv-has? st "log"))
    ; сертификат Риккати (ω′ + ω² + aω + b = 0) проходит
    (assert-true (kovacic-check eq (okv-cert r) '(y x)))
    ; подделка ω отвергается
    (let ((c (okv-cert r)))
      (assert-equal (kovacic-check eq
                                   (list 'kovacic-case2 (nth c 1) (nth c 2)
                                         '(+ (/ 1 (* 4 x)) (^ x -1/2) 1) (nth c 4) (nth c 5))
                                   '(y x))
                    #f))
    (assert-true (<= (okv-lines s) 15))))

(deftest "Ковачич: случай 3 — условия выполнены, honest unknown, не отказ"
  (let* ((eq '(= (diff (diff (y x) x) x)
                 (* (+ (/ 1 (^ (- x 1) 2)) (/ 1 (^ (+ x 2) 2)) (/ 1 (^ x 2))) (y x))))
         (k (kovacic eq '(y x)))
         (d (dsolve eq '(y x)))
         (s (okv-text (lambda () (kovacic eq '(y x))) 'brief)))
    ; три полюса порядка 2, o(∞) = 2: случай 3 возможен, но n = 4/6/12 не реализован
    (assert-equal k #f)
    (assert-true (not (equal? (ode-status d) 'no-liouvillian)))
    (assert-true (okv-has? s "условия случая 3 выполнены"))
    (assert-true (okv-has? s "unknown, не отказ")))
  ; доказанный отказ, когда условия случая 3 нарушены (Эйри: o(∞) = −1)
  (let ((r (dsolve '(= (diff (diff (y x) x) x) (* x (y x))) '(y x))))
    (assert-equal (ode-status r) 'no-liouvillian)))

(deftest "Ковачич: случай 3 (n = 4) — z = x/√(x−1)"
  (let* ((r0 '(/ (- 4 x) (* 4 x (^ (- x 1) 2))))
         (eq (list '= (list 'diff (list 'diff '(y x) 'x) 'x) (list '* r0 '(y x))))
         (q (dsolve eq '(y x)))
         (s (okv-text (lambda () (dsolve eq '(y x))) 'brief)))
    (assert-equal (ode-status q) 'ok)
    (assert-equal (nth q 12) 'kovacic)
    (assert-true (okv-has? s "случай 3"))
    ; y₁ = e^{log x − ½log(x−1)} = x/√(x−1); сертификат Риккати
    (assert-true (kovacic-check eq (okv-cert q) '(y x)))
    (assert-true (okv-has? (to-string (okv-sols q)) "log x"))
    (assert-true (<= (okv-lines s) 15))))

; ---------- ODE.8d: случай 1 при иррегулярной ∞ (o(∞) < 0, чётный) ----------

(deftest "Ковачич 8d: случай 1 при o(∞) < 0 — П1, ω из ℚ[x]"
  ; r = ω′ + ω² для ω ∈ ℚ[x]; o(∞) = −2m < 0 чётно, ответ обязан найтись
  (let ((cases (list (list (list '+ (list '^ 'x 4) (list '* 2 'x)) '(1/3 (^ x 3)))
                     (list (list '+ (list '^ 'x 2) 3) '(exp (* 1/2 (^ x 2))))
                     (list (list '+ (list '^ 'x 6) (list '* 3 (list '^ 'x 2))) '(exp (* 1/4 (^ x 4))))
                     (list (list '+ (list '^ 'x 6) (list '* 2 (list '^ 'x 4))
                                 (list '* 4 (list '^ 'x 2)) 1)
                           '(exp (+ (* 1/2 (^ x 2)) (* 1/4 (^ x 4)))))
                     (list (list '+ (list '* 4 (list '^ 'x 4)) (list '* 4 'x))
                           '(exp (* 2/3 (^ x 3)))))))
    (for-each
     (lambda (c)
       (let* ((eq (list '= (list 'diff (list 'diff '(y x) 'x) 'x) (list '* (car c) '(y x))))
              (r (dsolve eq '(y x))))
         (assert-equal (ode-status r) 'ok)
         (assert-equal (nth r 12) 'kovacic)
         (assert-equal (dsolve-check eq (car (okv-sols r)) '(y x)) #t)
         (assert-true (kovacic-check eq (okv-cert r) '(y x)))))
     cases)))

(deftest "Ковачич 8d: x⁴+2x даёт y₁ = e^{x³/3}, brief без сырых o(-4)"
  (let* ((eq '(= (diff (diff (y x) x) x) (* (+ (^ x 4) (* 2 x)) (y x))))
         (r (dsolve eq '(y x)))
         (s (okv-text (lambda () (dsolve eq '(y x))) 'brief))
         (st (to-string (okv-sols r))))
    (assert-equal (ode-status r) 'ok)
    (assert-true (okv-has? st "exp"))
    (assert-equal (dsolve-check eq '(= (y x) (exp (* 1/3 (^ x 3)))) '(y x)) #t)
    ; П6: в brief нет сырых «o(-4)» и «o ⇒ cases», есть человекочитаемые строки
    (assert-true (not (okv-has? s "o(-4)")))
    (assert-true (not (okv-has? s "o ⇒ cases")))
    (assert-true (okv-has? s "o(∞) = -4"))
    (assert-true (okv-has? s "возможен только случай 1"))
    (assert-true (<= (okv-lines s) 15))))

(deftest "Ковачич 8d: П2 — y″ = −3/(16x²)y, y₂ без невычисленного integrate"
  (let* ((eq '(= (diff (diff (y x) x) x) (* -3/16 (^ x -2) (y x))))
         (r (dsolve eq '(y x)))
         (st (to-string (okv-sols r))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (nth r 12) 'kovacic)
    (assert-true (not (okv-has? st "integrate")))
    (assert-true (okv-has? st "(^ x 3/4)"))
    (assert-true (okv-has? st "(^ x 1/4)"))
    (assert-equal (dsolve-check eq (car (okv-sols r)) '(y x)) #t)
    (assert-true (kovacic-check eq (okv-cert r) '(y x)))))

(deftest "Ковачич 8d: П3 — y″ = x³y, доказанный no-liouvillian"
  (let ((r (dsolve '(= (diff (diff (y x) x) x) (* (^ x 3) (y x))) '(y x))))
    (assert-equal (ode-status r) 'no-liouvillian)
    (assert-true (kovacic-check '(= (diff (diff (y x) x) x) (* (^ x 3) (y x))) (okv-cert r) '(y x)))
    (assert-equal (kovacic '(= (diff (diff (y x) x) x) (* (^ x 3) (y x))) '(y x)) r)))

(deftest "Ковачич 8d: П4 — Бессель ν = 2/3, 1 и I₀: unknown, не отказ"
  (let ((eqs (list '(= (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x))
                           (* (+ (^ x 2) -4/9) (y x))) 0)
                   '(= (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x))
                           (* (+ (^ x 2) -1) (y x))) 0)
                   '(= (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x))
                           (* -1 (^ x 2) (y x))) 0))))
    (for-each
     (lambda (eq)
       (let ((k (kovacic eq '(y x))) (d (dsolve eq '(y x))))
         ; Ковачич не отказывает: условия случаев выполнены, решения не нашлось
         (assert-equal k #f)
         (assert-true (not (equal? (ode-status d) 'no-liouvillian)))))
     eqs)))

(deftest "Ковачич 8d: П5 — подделки сертификата отсева для y″ = (x²+1)y"
  (let ((eq '(= (diff (diff (y x) x) x) (* (+ (^ x 2) 1) (y x)))))
    ; настоящее уравнение имеет решение: любой сертификат отсева — подделка
    (assert-equal (kovacic-check eq '(kovacic-none () -2 (#f #f #f)) '(y x)) #f)
    (assert-equal (kovacic-check eq '(kovacic-none () -2 (#f #t #f)) '(y x)) #f)
    (assert-equal (kovacic-check eq '(kovacic-none () -2 (#t #f #f)) '(y x)) #f)
    (assert-equal (kovacic-check eq '(kovacic-none) '(y x)) #f)
    (assert-equal (kovacic-check eq '() '(y x)) #f)
    ; вырожденный: неверный o(∞)
    (assert-equal (kovacic-check eq '(kovacic-none () -4 (#t #f #f)) '(y x)) #f)))
