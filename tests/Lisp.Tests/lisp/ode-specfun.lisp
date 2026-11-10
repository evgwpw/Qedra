; ode-specfun.lisp — ODE.9: ответы dsolve через головы Бесселя/Эйри/Лежандра/₂F₁.

(define (osf-str r) (to-string (ode-solutions r)))
(define (osf-has? r s) (string-contains? (osf-str r) s))
(define (osf-method r) (ode::ode-field r :method))
(define (osf-check eq y) (dsolve-check eq (list '= '(y x) y) '(y x)))

; x²y″ + xy′ + (α²x^{2m} − ν²)y = 0
(define (osf-bessel-eq nu al m)
  (list '= (list '+
                 (list '* (list '^ 'x 2) (list 'diff (list 'diff '(y x) 'x) 'x))
                 (list '* 'x (list 'diff '(y x) 'x))
                 (list '* (list '- (list '* (list '^ al 2) (list '^ 'x (* 2 m)))
                                 (list '^ nu 2))
                         '(y x)))
        0))

; y″ = (αx + β)y
(define (osf-airy-eq al be)
  (list '= (list 'diff (list 'diff '(y x) 'x) 'x)
        (list '* (list '+ (list '* al 'x) be) '(y x))))

(deftest "ODE.9: Бессель J_{1/3}, Y_{1/3} вместо unknown; проверка подстановкой"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (/ (diff (y x) x) x)
                    (* (- 1 (/ 1 (* 9 (^ x 2)))) (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (osf-method r) 'specfun)
    (assert-true (osf-has? r "(bessel-j 1/3 x)"))
    (assert-true (osf-has? r "(bessel-y 1/3 x)"))
    (assert-true (osf-check eq '(bessel-j 1/3 x)))
    (assert-true (osf-check eq '(bessel-y 1/3 x)))
    (assert-true (not (string-contains? (to-string r) "unknown")))))

(deftest "ODE.9: Бессель x²y″+xy′+(4x²−1)y = 0 → J₁(2x), Y₁(2x)"
  (let* ((eq '(= (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x))
                    (* (- (* 4 (^ x 2)) 1) (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (osf-method r) 'specfun)
    (assert-true (osf-has? r "(bessel-j 1 (* 2 x))"))
    (assert-true (osf-has? r "(bessel-y 1 (* 2 x))"))
    (assert-true (osf-check eq '(bessel-j 1 (* 2 x))))
    ; второе решение больше не ряд с log x (намеренное улучшение ответа)
    (assert-true (not (string-contains? (osf-str r) "(log x)")))))

(deftest "ODE.9: модифицированный Бессель x²y″+xy′−(x²+4)y = 0 → I₂, K₂"
  (let* ((eq '(= (- (+ (* (^ x 2) (diff (diff (y x) x) x)) (* x (diff (y x) x)))
                    (* (+ (^ x 2) 4) (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-true (osf-has? r "(bessel-i 2 x)"))
    (assert-true (osf-has? r "(bessel-k 2 x)"))
    (assert-true (osf-check eq '(bessel-i 2 x)))
    (assert-true (osf-check eq '(bessel-k 2 x)))))

(deftest "ODE.9: Эйри y″ = x·y — no-liouvillian сохраняется, ответ Ai/Bi добавлен"
  (let* ((eq '(= (diff (diff (y x) x) x) (* x (y x))))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'no-liouvillian)
    (assert-equal (osf-method r) 'kovacic)
    (assert-true (osf-has? r "(airy-ai x)"))
    (assert-true (osf-has? r "(airy-bi x)"))
    ; сертификат отказа Ковачича не ослаблен
    (assert-true (kovacic-check eq (nth r 14) '(y x)))
    (assert-true (osf-check eq '(airy-ai x)))
    (assert-true (osf-check eq '(airy-bi x)))))

(deftest "ODE.9: Эйри с линейным аргументом y″ = (2x−3)y"
  (let* ((eq '(= (diff (diff (y x) x) x) (* (- (* 2 x) 3) (y x))))
         (r (dsolve eq '(y x)))
         (t '(+ (* -3/2 (^ 2 1/3)) (* (^ 2 1/3) x))))
    (assert-equal (ode-status r) 'no-liouvillian)
    (assert-true (osf-has? r "(^ 2 1/3)"))
    (assert-true (osf-check eq (list 'airy-ai t)))
    (assert-true (osf-check eq (list 'airy-bi t)))))

(deftest "ODE.9: Лежандр n = 2 — P₂ и Q₂ вместо невычисленного интеграла"
  (let* ((eq '(= (+ (* (- 1 (^ x 2)) (diff (diff (y x) x) x))
                    (* -2 x (diff (y x) x)) (* 6 (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (osf-method r) 'specfun)
    (assert-true (osf-has? r "(legendre-p 2 x)"))
    (assert-true (osf-has? r "(legendre-q 2 x)"))
    (assert-true (osf-check eq '(legendre-p 2 x)))
    (assert-true (osf-check eq '(legendre-q 2 x)))
    (assert-true (not (string-contains? (osf-str r) "integrate")))))

(deftest "ODE.9: Эрмит n = 3 — H₃ = 8x³−12x, второе через интеграл"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* -2 x (diff (y x) x)) (* 6 (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-true (osf-has? r "(* 8 (^ x 3))"))
    (assert-true (osf-check eq '(- (* 8 (^ x 3)) (* 12 x))))
    ; второе решение допустимо через ∫e^{x²}/H₃²
    (assert-true (string-contains? (osf-str r) "integrate"))))

(deftest "ODE.9: ₂F₁ a = b = 1, c = 2 — y₁ = −log(1−x)/x"
  (let* ((eq '(= (+ (* x (- 1 x) (diff (diff (y x) x) x))
                    (* (- 2 (* 3 x)) (diff (y x) x)) (* -1 (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (osf-method r) 'specfun)
    (assert-true (osf-has? r "(log (+ 1 (* -1 x)))"))
    (assert-true (osf-check eq '(* -1 (^ x -1) (log (+ 1 (* -1 x))))))
    ; первая ветвь — именно −log(1−x)/x (а не log(x−1)/x от Ковачича)
    (assert-true (osf-has? r "(* -1 C1 (^ x -1) (log (+ 1 (* -1 x))))"))))

(deftest "ODE.9: обобщённый Бессель y″ + x²·y = 0 → √x·J_{1/4}(x²/2)"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* (^ x 2) (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (osf-method r) 'specfun)
    (assert-true (osf-has? r "(bessel-j 1/4 (* 1/2 (^ x 2)))"))
    (assert-true (osf-has? r "(bessel-y 1/4 (* 1/2 (^ x 2)))"))
    (assert-true (osf-check eq '(* (^ x 1/2) (bessel-j 1/4 (* 1/2 (^ x 2))))))))

(deftest "ODE.9: y″ + x·y = 0 → Ai(−x), Bi(−x)"
  (let* ((eq '(= (+ (diff (diff (y x) x) x) (* x (y x))) 0))
         (r (dsolve eq '(y x))))
    (assert-equal (ode-status r) 'no-liouvillian)
    (assert-true (osf-has? r "(airy-ai (* -1 x))"))
    (assert-true (osf-check eq '(airy-ai (* -1 x))))))

(deftest "ODE.9: запрещено — поддельные ответы не проходят подстановку"
  ; не тот порядок Бесселя
  (assert-equal (dsolve-check '(= (+ (diff (diff (y x) x) x) (y x)) 0)
                              '(= (y x) (bessel-j 1/3 x)) '(y x)) #f)
  ; не тот аргумент Эйри
  (assert-equal (dsolve-check '(= (diff (diff (y x) x) x) (* 2 x (y x)))
                              '(= (y x) (airy-ai x)) '(y x)) #f)
  ; не та степень Лежандра
  (assert-equal (dsolve-check '(= (+ (* (- 1 (^ x 2)) (diff (diff (y x) x) x))
                                    (* -2 x (diff (y x) x)) (* 6 (y x))) 0)
                              '(= (y x) (legendre-q 3 x)) '(y x)) #f)
  ; линейно зависимая пара (y₂ = 2·y₁) отвергается в sfo-augment
  (assert-equal (dsolve-check '(= (- (diff (diff (y x) x) x) (* x (y x))) 0)
                              '(= (y x) (* 2 (airy-ai x))) '(y x)) #t))

(deftest "ODE.9: покрытие — 6 построенных (ν, α, m) класса (Б) и 6 класса (Э)"
  (for-each (lambda (c)
              (let* ((r (dsolve (osf-bessel-eq (car c) (cadr c) (caddr c)) '(y x))))
                (assert-equal (ode-status r) 'ok)
                (assert-true (pair? (ode-solutions r)))))
            '((2/3 3 1) (1 2 2) (5/2 1 1) (7/3 1/2 3) (0 1 1) (3 2 2)))
  (for-each (lambda (c)
              (let* ((r (dsolve (osf-airy-eq (car c) (cadr c)) '(y x))))
                (assert-equal (ode-status r) 'no-liouvillian)
                (assert-true (pair? (ode-solutions r)))))
            '((1 0) (2 -1) (1/2 3) (3 2) (-1 0) (4 1))))
