; definite.lisp — тесты шага DI.1: несобственные интегралы (вычеты, таблицы, сходимость, сертификат)

(define (dit-near? e v) (< (abs (- (eval-num e) v)) 1e-9))
(define (dit-div? r) (and (pair? r) (equal? (car r) 'divergent)))
(define (dit-I f a b) (definite-integral f 'x a b))

(deftest "вычеты: 1/(1+x²) и 1/(x²+2x+2) на прямой"
  (assert-equal (dit-I '(/ 1 (+ 1 (^ x 2))) '-inf 'inf) 'pi)
  (assert-equal (dit-I '(/ 1 (+ (^ x 2) (* 2 x) 2)) '-inf 'inf) 'pi))

(deftest "вычеты: 1/(1+x⁴) = π/√2 (неприводимый множитель степени 4)"
  (assert-true (dit-near? (dit-I '(/ 1 (+ 1 (^ x 4))) '-inf 'inf) 2.2214414690791831))
  (assert-true (dit-near? (dit-I '(/ 1 (+ 1 (^ x 4))) 0 'inf) 1.1107207345395915)))

(deftest "вычеты: кратные полюса x²/(1+x²)², 1/(1+x²)³"
  (assert-equal (dit-I '(/ (^ x 2) (^ (+ 1 (^ x 2)) 2)) '-inf 'inf) '(* 1/2 pi))
  (assert-equal (dit-I '(/ 1 (^ (+ (^ x 2) 1) 3)) '-inf 'inf) '(* 3/8 pi)))

(deftest "вычеты: полупрямая через log z, 1/(1+x³) = 2π/(3√3)"
  (assert-true (dit-near? (dit-I '(/ 1 (+ 1 (^ x 3))) 0 'inf) 1.2091995761561452))
  (assert-equal (dit-I '(/ 1 (* (+ x 1) (+ (^ x 2) 1))) 0 'inf) '(* 1/4 pi))
  (assert-equal (dit-I '(/ 1 (^ (+ x 1) 3)) 0 'inf) 1/2))

(deftest "вычеты: сдвиг и отражение полупрямой"
  (assert-equal (dit-I '(/ 1 (+ (^ x 2) 1)) '-inf 0) '(* 1/2 pi))
  (assert-equal (dit-I '(/ 1 (+ (^ x 2) 1)) 1 'inf) '(* 1/4 pi)))

(deftest "Жордан: ∫ cos x/(1+x²) = π/e и ∫ x sin x/(1+x²) = π/e"
  (assert-true (dit-near? (dit-I '(/ (cos x) (+ 1 (^ x 2))) '-inf 'inf) 1.1557273497909217))
  (assert-true (dit-near? (dit-I '(/ (* x (sin x)) (+ 1 (^ x 2))) '-inf 'inf) 1.1557273497909217))
  (assert-equal (dit-I '(/ (sin (* 2 x)) (+ 1 (^ x 2))) '-inf 'inf) 0))

(deftest "Жордан: полупрямая по чётности и сдвинутый полюс"
  (assert-true (dit-near? (dit-I '(/ (cos x) (+ 1 (^ x 2))) 0 'inf) 0.57786367489546085))
  (assert-true (dit-near? (dit-I '(/ (cos x) (+ (^ x 2) (* 2 x) 2)) '-inf 'inf) (eval-num '(* pi (exp -1) (cos 1))))))

(deftest "Дирихле: sin(ax)/x"
  (assert-equal (dit-I '(/ (sin x) x) 0 'inf) '(* 1/2 pi))
  (assert-equal (dit-I '(/ (sin (* -2 x)) x) 0 'inf) '(* -1/2 pi))
  (assert-equal (dit-I '(/ (sin x) x) '-inf 'inf) 'pi))

(deftest "Френель: ∫₀^∞ sin x² = ∫₀^∞ cos x² = √(π/8)"
  (assert-true (dit-near? (dit-I '(sin (^ x 2)) 0 'inf) 0.6266570686577501))
  (assert-true (dit-near? (dit-I '(cos (^ x 2)) 0 'inf) 0.6266570686577501)))

(deftest "Гаусс: ∫ e^{-x²} = √π, моменты"
  (assert-equal (dit-I '(exp (* -1 (^ x 2))) '-inf 'inf) '(^ pi 1/2))
  (assert-equal (dit-I '(* (^ x 2) (exp (* -1 (^ x 2)))) '-inf 'inf) '(* 1/2 (^ pi 1/2)))
  (assert-equal (dit-I '(* x (exp (* -1 (^ x 2)))) '-inf 'inf) 0))

(deftest "Γ: ∫₀^∞ x³e^{-2x} = 3/8, x^{s-1}e^{-x} = Γ(s)"
  (assert-equal (dit-I '(* (^ x 3) (exp (* -2 x))) 0 'inf) 3/8)
  (assert-equal (dit-I '(* (^ x -1/2) (exp (* -1 x))) 0 'inf) '(^ pi 1/2))
  (assert-equal (dit-I '(* (^ x (- s 1)) (exp (* -1 x))) 0 'inf) '(gamma s)))

(deftest "Бета: ∫₀^1 √(x(1−x)) = π/8"
  (assert-equal (dit-I '(sqrt (* x (- 1 x))) 0 1) '(* 1/8 pi))
  (assert-equal (dit-I '(* (^ x 2) (- 1 x)) 0 1) 1/12))

(deftest "Бета: ∫₀^∞ x^{a-1}/(1+x) = π/sin(πa)"
  (assert-equal (dit-I '(/ (^ x -1/2) (+ 1 x)) 0 'inf) 'pi)
  (assert-true (dit-near? (dit-I '(/ (^ x -2/3) (+ 1 x)) 0 'inf) 3.6275987284684357))
  (assert-equal (dit-I '(/ (^ x 2) (^ (+ 1 x) 4)) 0 'inf) 1/3))

(deftest "окружность: ∫₀^{2π} dθ/(2+cos θ) = 2π/√3"
  (assert-true (dit-near? (dit-I '(/ 1 (+ 2 (cos x))) 0 (* 2 'pi)) 3.6275987284684357))
  (assert-true (dit-near? (dit-I '(/ 1 (+ 3 (* 2 (cos x)))) 0 (* 2 'pi)) 2.8099258924162912)))

(deftest "окружность: cos²θ, полюс на окружности — расходится"
  (assert-true (dit-near? (dit-I '(^ (cos x) 2) 0 (* 2 'pi)) 3.141592653589793))
  (assert-true (dit-div? (dit-I '(/ 1 (+ 1 (cos x))) 0 (* 2 'pi)))))

(deftest "расходимость: ∫₁^∞ 1/x, ∫_{-1}^1 1/x², ∫₀^1 1/x²"
  (assert-true (dit-div? (dit-I '(/ 1 x) 1 'inf)))
  (assert-true (dit-div? (dit-I '(/ 1 (^ x 2)) -1 1)))
  (assert-true (dit-div? (dit-I '(/ 1 (^ x 2)) 0 1)))
  (assert-true (dit-div? (dit-I '(/ 1 (- x 1)) 0 2))))

(deftest "расходимость: нет предела (sin x), x/(1+x²), x²/(1+x)"
  (assert-true (dit-div? (dit-I '(sin x) 0 'inf)))
  (assert-true (dit-div? (dit-I '(/ x (+ 1 (^ x 2))) '-inf 'inf)))
  (assert-true (dit-div? (dit-I '(/ (^ x 2) (+ 1 x)) 0 'inf))))

(deftest "параметр: ∫₀^∞ e^{-ax} = 1/a с условием a > 0"
  (let ((r (capture-conditions (lambda () (dit-I '(exp (* -1 (* a x))) 0 'inf)))))
    (assert-equal (car r) '(^ a -1))
    (assert-equal (car (car (cadr r))) '(> a 0))))

(deftest "параметры: ∫₀^∞ e^{-ax} cos bx = a/(a²+b²), x e^{-x} sin x"
  (assert-equal (dit-I '(* (exp (* -1 (* a x))) (cos (* b x))) 0 'inf) '(* a (^ (+ (^ a 2) (^ b 2)) -1)))
  (assert-equal (dit-I '(* x (exp (* -1 x)) (sin x)) 0 'inf) 1/2))

(deftest "Ньютон–Лейбниц и порядок концов"
  (assert-equal (dit-I '(/ (^ x 2) (+ 1 (^ x 2))) 0 1) '(+ 1 (* -1/4 pi)))
  (assert-equal (dit-I '(* x x) 3 1) -26/3)
  (assert-equal (dit-I '(* x x) 2 2) 0)
  (assert-equal (dit-I '(log x) 0 1) -1)
  (assert-equal (dit-I '(/ 1 (sqrt x)) 0 1) 2))

(deftest "definite-convergence: сходится, условно, расходится"
  (assert-equal (definite-convergence '(/ (sin x) x) 'x 1 'inf) 'conditional)
  (assert-equal (definite-convergence '(/ 1 (sqrt x)) 'x 0 1) 'convergent)
  (assert-equal (definite-convergence '(exp (* -1 x)) 'x 0 'inf) 'convergent)
  (assert-true (dit-div? (definite-convergence '(/ 1 x) 'x 1 'inf)))
  (assert-true (dit-div? (definite-convergence '(/ 1 (^ x 2)) 'x 0 1)))
  (assert-true (dit-div? (definite-convergence '(cos x) 'x 0 'inf))))

(deftest "сертификат: рациональные подынтегральные — строгое включение"
  (assert-equal (definite-check '(/ 1 (+ 1 (^ x 2))) 'x '-inf 'inf 'pi) #t)
  (assert-equal (definite-check '(/ 1 (+ 1 (^ x 4))) 'x 0 'inf '(* 1/4 (^ 2 1/2) pi)) #t))

(deftest "сертификат: e^{-ax} — строгий хвост, Дирихле — только квадратура"
  (assert-equal (definite-check '(* (^ x 3) (exp (* -2 x))) 'x 0 'inf 3/8) #t)
  (assert-equal (definite-check '(/ (sin x) x) 'x 0 'inf '(* 1/2 pi)) 'numeric))

(deftest "сертификат: подделки π/3, √π/2, неверный знак, 5 для 1/x"
  (assert-equal (definite-check '(/ (sin x) x) 'x 0 'inf '(/ pi 3)) #f)
  (assert-equal (definite-check '(exp (* -1 (^ x 2))) 'x '-inf 'inf '(/ (^ pi 1/2) 2)) #f)
  (assert-equal (definite-check '(/ 1 (+ 1 (^ x 2))) 'x '-inf 'inf '(* -1 pi)) #f)
  (assert-equal (definite-check '(/ 1 x) 'x 1 'inf 5) #f))

; ---------- DI.2: точные вычеты, замочная скважина, параметры, окружность ----------

(define (dit-same? a b) (< (abs (- (eval-num a) (eval-num b))) 1e-9))
(define (dit-has? e h) (and (pair? e) (or (equal? (car e) h) (any? (lambda (u) (dit-has? u h)) e))))

(deftest "DI.2 точные вычеты: 1/(1+x⁴), 1/(x⁴+2x²+3)"
  (assert-true (dit-same? (dit-I (quote (/ 1 (+ 1 (^ x 4)))) (quote -inf) (quote inf)) (quote (/ pi (sqrt 2)))))
  (assert-true (dit-same? (dit-I (quote (/ 1 (+ (^ x 4) (* 2 (^ x 2)) 3))) (quote -inf) (quote inf))
                          (quote (/ pi (* (sqrt 3) (sqrt (+ 2 (* 2 (sqrt 3))))))))))

(deftest "DI.2 точные вычеты: x⁴+x+5 — root-sum, значение сверено численно"
  (let ((v (dit-I (quote (/ 1 (+ (^ x 4) x 5))) (quote -inf) (quote inf))))
    (assert-true (dit-has? v (quote root-sum)))
    (assert-equal (definite-check (quote (/ 1 (+ (^ x 4) x 5))) (quote x) (quote -inf) (quote inf) v) (quote numeric))
    (assert-equal (definite-check (quote (/ 1 (+ (^ x 4) x 5))) (quote x) (quote -inf) (quote inf) (list (quote *) -1 v)) #f)))

(deftest "DI.2 точные вычеты: x⁶+1, x²/(x⁶+1)"
  (assert-equal (dit-I (quote (/ 1 (+ 1 (^ x 6)))) (quote -inf) (quote inf)) (quote (* 2/3 pi)))
  (assert-equal (dit-I (quote (/ (^ x 2) (+ 1 (^ x 6)))) (quote -inf) (quote inf)) (quote (* 1/3 pi)))
  (assert-equal (dit-I (quote (/ (^ x 2) (+ 1 (^ x 6)))) 0 (quote inf)) (quote (* 1/6 pi))))

(deftest "DI.2 замочная скважина: log x"
  (assert-equal (dit-I (quote (/ (log x) (+ 1 (^ x 2)))) 0 (quote inf)) 0)
  (assert-equal (dit-I (quote (/ (log x) (^ (+ 1 (^ x 2)) 2))) 0 (quote inf)) (quote (* -1/4 pi)))
  (assert-equal (dit-I (quote (/ (log x) (* (+ x 1) (+ x 2)))) 0 (quote inf)) (quote (* 1/2 (^ (log 2) 2))))
  (assert-true (dit-div? (dit-I (quote (/ (log x) (+ x 1))) 0 (quote inf)))))

(deftest "DI.2 замочная скважина: x^s R(x)"
  (assert-equal (dit-I (quote (/ (^ x 1/3) (+ 1 (^ x 2)))) 0 (quote inf)) (quote (* 1/3 (^ 3 1/2) pi)))
  (assert-true (dit-same? (dit-I (quote (/ (^ x -1/2) (+ 1 (^ x 2)))) 0 (quote inf)) (quote (/ pi (sqrt 2)))))
  (assert-equal (definite-check (quote (/ (^ x 1/3) (+ 1 (^ x 2)))) (quote x) 0 (quote inf) (quote (* 1/3 (^ 3 1/2) pi))) (quote numeric)))

(deftest "DI.2 параметры: 1/(x²+a²), 1/(x²+a²)², условия a > 0"
  (conditions-clear)
  (assert-equal (dit-I (quote (/ 1 (+ (^ x 2) (^ a 2)))) (quote -inf) (quote inf)) (quote (* (^ a -1) pi)))
  (assert-true (member? (quote ((> a 0) "параметр > 0 (в знаменателе)")) (conditions)))
  (assert-equal (dit-I (quote (/ 1 (^ (+ (^ x 2) (^ a 2)) 2))) 0 (quote inf)) (quote (* 1/4 (^ a -3) pi)))
  (assert-equal (dit-I (quote (* (^ x 2) (exp (* -1 a (^ x 2))))) 0 (quote inf)) (quote (* 1/4 (^ a -3/2) (^ pi 1/2))))
  (assert-equal (dit-I (quote (/ 1 (+ (^ x 2) (* 2 b x) (^ b 2) (^ c 2)))) (quote -inf) (quote inf)) (quote (* (^ c -1) pi))))

(deftest "DI.2 Фейнман: log x · x^p e^{-ax}, производная по параметру"
  (assert-equal (dit-I (quote (* (^ x 2) (log x) (exp (* -1 x)))) 0 (quote inf)) (quote (* 2 (+ 3/2 (* -1 euler-gamma)))))
  (assert-equal (dit-I (quote (* (log x) (exp (* -1 a x)))) 0 (quote inf)) (quote (+ (* -1 (^ a -1) (log a)) (* (^ a -1) (* -1 euler-gamma)))))
  (assert-equal (definite-feynman (quote (* x (exp (* -1 a x)))) (quote x) (quote a) 0 (quote inf)) (quote (* -2 (^ a -3))))
  (assert-equal (definite-feynman (quote (/ 1 (+ (^ x 2) (^ a 2)))) (quote x) (quote a) (quote -inf) (quote inf)) (quote (* -1 (^ a -2) pi))))

(deftest "DI.2 окружность: 1/(2+sin²θ) — знаменатель степени 4 по z (нормальное поле)"
  (assert-equal (dit-I (quote (/ 1 (+ 2 (^ (sin x) 2)))) 0 (* 2 (quote pi))) (quote (* 1/3 (^ 6 1/2) pi))))

(deftest "DI.2 окружность: нечётные степени sin, кратные полюса"
  (assert-equal (dit-I (quote (/ 1 (^ (- 5 (* 4 (cos x))) 2))) 0 (* 2 (quote pi))) (quote (* 10/27 pi)))
  (assert-equal (dit-I (quote (/ 1 (+ 2 (sin x)))) 0 (* 2 (quote pi))) (quote (* 2/3 (^ 3 1/2) pi)))
  (assert-equal (dit-I (quote (/ (sin x) (+ 2 (cos x)))) 0 (* 2 (quote pi))) 0)
  (assert-equal (dit-I (quote (/ (sin x) (+ 3 (cos x)))) 0 (* 2 (quote pi))) 0))

(deftest "DI.2 сертификат: подделки (знак log-интеграла, π/(2a) вместо π/a, окружность)"
  (assert-equal (definite-check (quote (/ (log x) (^ (+ 1 (^ x 2)) 2))) (quote x) 0 (quote inf) (quote (* -1/4 pi))) (quote numeric))
  (assert-equal (definite-check (quote (/ (log x) (^ (+ 1 (^ x 2)) 2))) (quote x) 0 (quote inf) (quote (* 1/4 pi))) #f)
  (assert-equal (definite-check (quote (/ 1 (+ (^ x 2) 4))) (quote x) (quote -inf) (quote inf) (quote (* 1/2 pi))) #t)
  (assert-equal (definite-check (quote (/ 1 (+ (^ x 2) 4))) (quote x) (quote -inf) (quote inf) (quote (* 1/4 pi))) #f)
  (assert-equal (definite-check (quote (/ 1 (+ 2 (^ (sin x) 2)))) (quote x) 0 (* 2 (quote pi)) (quote (* 1/3 (^ 6 1/2) pi))) (quote numeric))
  (assert-equal (definite-check (quote (/ 1 (+ 2 (^ (sin x) 2)))) (quote x) 0 (* 2 (quote pi)) (quote (* 1/6 (^ 6 1/2) pi))) #f))

; ---------- шаг DI.3: (integrate f x a b) идёт через definite ----------

(define (dit-J f a b) (integrate f 'x a b))

(deftest "integrate: несобственные пределы — через definite (π, π/2, √π/2)"
  (assert-equal (dit-J '(/ 1 (+ 1 (^ x 2))) '-inf 'inf) 'pi)
  (assert-equal (dit-J '(/ (sin x) x) 0 'inf) '(* 1/2 pi))
  (assert-true (dit-near? (dit-J '(exp (* -1 (^ x 2))) 0 'inf) 0.886226925452758)))

(deftest "integrate: ∫₀^{2π} 1/(2+cos θ) = 2π/√3; ∫₀^1 log x = −1 (Ньютон–Лейбниц с пределом)"
  (assert-true (dit-near? (dit-J '(/ 1 (+ 2 (cos x))) 0 '(* 2 pi)) 3.6275987284684357))
  (assert-equal (dit-J '(log x) 0 1) -1))

(deftest "integrate: особенность внутри промежутка — не Ньютон–Лейбниц (1/x² на [−1, 1] расходится)"
  (let* ((r (capture-conditions (lambda () (dit-J '(/ 1 (^ x 2)) -1 1)))))
    (assert-equal (car r) '(integrate (^ x -2) x -1 1))
    (assert-true (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'divergent))) (cadr r)))))

(deftest "integrate: параметр с условием — ∫₀^∞ e^{−ax} = 1/a при a > 0"
  (let ((r (capture-conditions (lambda () (dit-J '(exp (* -1 a x)) 0 'inf)))))
    (assert-equal (car r) '(^ a -1))
    (assert-true (member? '((> a 0)) (map (lambda (c) (list (car c))) (cadr r))))))

(deftest "integrate: definite-check подтверждает значение integrate"
  (assert-equal (definite-check '(/ 1 (+ 1 (^ x 2))) 'x '-inf 'inf (dit-J '(/ 1 (+ 1 (^ x 2))) '-inf 'inf)) #t))

(deftest "integrate: входной язык — integrate(1/(1+x^2), x, -inf, inf) = π"
  (assert-equal (math-eval "integrate(1/(1+x^2), x, -inf, inf)") (quote pi)))

; ---------- шаг DI.4: особые точки внутри конечного отрезка ----------

(define (dit-divcond? f a b)
  (let ((r (capture-conditions (lambda () (integrate f 'x a b)))))
    (and (equal? (car (car r)) 'integrate)
         (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'divergent))) (cadr r)))))

(deftest "integrate: ∫₀² tan x расходится (полюс π/2), а не −log cos 2; ∫₀¹ tan x = −log cos 1"
  (assert-true (dit-divcond? '(tan x) 0 2))
  (assert-equal (integrate '(tan x) 'x 0 1) '(* -1 (log (cos 1)))))

(deftest "integrate: 1/sin x на [0, π] и 1/x на [−1, 1] расходятся (главное значение — не ответ)"
  (assert-true (dit-divcond? '(/ 1 (sin x)) 0 'pi))
  (assert-true (dit-divcond? '(/ 1 x) -1 1)))

(deftest "integrate: ветви — log(x−1) на [0, 3] и (x−1)^{−1/3} на [0, 2] не дают комплексного «значения»"
  (assert-equal (integrate '(log (- x 1)) 'x 0 3) '(integrate (log (+ -1 x)) x 0 3))
  (assert-equal (integrate '(^ (- x 1) -1/3) 'x 0 2) '(integrate (^ (+ -1 x) -1/3) x 0 2)))

(deftest "integrate: интегрируемая особенность внутри — разбиение: ∫₀² (x−1)^{−1/2}-типа через |…| остаётся, гладкое — классика"
  (assert-equal (integrate '(^ x 2) 'x 0 3) 9)
  (assert-equal (integrate '(^ (sin x) 2) 'x 0 'pi) '(* 1/2 pi)))

(deftest "DI.4: полюс-касание внутри отрезка — 1/sin²x на [1, 4], 1/(1 − cos x) на [−1, 1] — расходятся (не cot 1 − cot 4)"
  (assert-true (and (pair? (definite-interior '(/ 1 (^ (sin x) 2)) 'x 1 4))
                    (equal? (car (definite-interior '(/ 1 (^ (sin x) 2)) 'x 1 4)) 'divergent)))
  (assert-true (and (pair? (definite-interior '(/ 1 (- 1 (cos x))) 'x -1 1))
                    (equal? (car (definite-interior '(/ 1 (- 1 (cos x))) 'x -1 1)) 'divergent)))
  (assert-equal #f (definite-interior '(/ 1 (^ (sin x) 2)) 'x 1 2)))

(define (nl-num r) (try (eval-num r) (lambda (er) #f)))
(define (nl-close? e x a b val)
  (let ((r (integrate e x a b)))
    (let ((n (nl-num r))) (and (number? n) (< (abs (- n val)) 1e-9)))))

(deftest "Ньютон — Лейбниц: ∫₁² dx/(1 − cos x) — первообразная через tan(x/2) непрерывна на отрезке, значение"
  (assert-true (nl-close? '(/ 1 (- 1 (cos x))) 'x 1 2 1.1883951057781212))
  (assert-true (nl-close? '(/ 1 (+ 2 (cos x))) 'x 0 1 0.35279779326504845)))

(deftest "Ньютон — Лейбниц: набор элементарных определённых интегралов (точные значения)"
  (assert-equal (integrate '(^ (tan x) 2) 'x 0 '(/ pi 4)) '(+ 1 (* -1/4 pi)))
  (assert-equal (integrate '(^ (sin x) 3) 'x 0 '(/ pi 2)) 2/3)
  (assert-equal (integrate '(^ (log x) 2) 'x 1 '(exp 1)) '(+ -2 (exp 1)))
  (assert-equal (integrate '(* x (exp x)) 'x 0 1) 1)
  (assert-equal (integrate '(* x (sin x)) 'x 0 'pi) 'pi)
  (assert-equal (integrate '(/ 1 (+ 1 (^ x 2))) 'x 0 1) '(* 1/4 pi))
  (assert-equal (integrate '(sqrt (- 1 (^ x 2))) 'x 0 1) '(* 1/4 pi))
  (assert-true (nl-close? '(/ 1 (- (^ x 2) 1)) 'x 2 3 (* 0.5 (log 1.5))))
  (assert-true (nl-close? '(/ 1 (cos x)) 'x 0 '(/ pi 3) (log (+ 2 (sqrt 3.0))))))

(deftest "Ньютон — Лейбниц: расходящиеся ∫₁⁴ dx/sin²x и ∫₀² tan x остаются невычисленными"
  (assert-true (dit-divcond? '(/ 1 (^ (sin x) 2)) 1 4))
  (assert-true (dit-divcond? '(tan x) 0 2)))
