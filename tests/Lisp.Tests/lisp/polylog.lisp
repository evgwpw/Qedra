; polylog.lisp — тесты шага PL: полилогарифм Li_s, функция Ламберта W₀ (значения, производные, ряды, интегралы, solve)

(define (plt-close? a b tol) (and (number? a) (number? b) (< (abs (- a b)) tol)))
(define (plt-fd f x0) (/ (- (f (+ x0 0.00001)) (f (- x0 0.00001))) 0.00002))
(define (plt-at e x v) (polylog-evalf (subst (list x v) e)))

; ---------- численные значения ----------

(deftest "polylog-num: известные значения Li₂, Li₃"
  (assert-true (plt-close? (polylog-num 2 1/3) 0.3662132299770634 0.000000000001))
  (assert-true (plt-close? (polylog-num 2 -2) -1.4367463668836806 0.000000000001))
  (assert-true (plt-close? (polylog-num 3 1/2) 0.5372131936080403 0.000000000001))
  (assert-true (plt-close? (polylog-num 2 1/2) 0.5822405264650125 0.000000000001))
  (assert-true (plt-close? (polylog-num 2 0.9) 1.2997147230049587 0.000000000001))
  (assert-true (plt-close? (polylog-num 2 -7) -3.400162044428386 0.00000001)))

(deftest "polylog-num: краевые точки и отказы"
  (assert-true (plt-close? (polylog-num 2 1) 1.6449340668482264 0.000000000001))
  (assert-true (plt-close? (polylog-num 2 -1) -0.8224670334241132 0.000000000001))
  (assert-true (plt-close? (polylog-num 4 1) 1.0823232337111381 0.000000000001))
  (assert-equal (polylog-num 2 0) 0.0)
  (assert-equal (polylog-num 2 3/2) #f)       ; x > 1: значение комплексное
  (assert-equal (polylog-num 1/2 0.3) #f)     ; s не целое
  (assert-true (plt-close? (polylog-num 1 0.5) 0.6931471805599453 0.000000000001)))

(deftest "polylog-num: тождества отражения и инверсии"
  ; Li₂(x) + Li₂(1−x) = π²/6 − log x·log(1−x)
  (assert-true (plt-close? (+ (polylog-num 2 0.3) (polylog-num 2 0.7))
                           (- 1.6449340668482264 (* (eval-num '(log 0.3)) (eval-num '(log 0.7)))) 0.0000000001))
  ; Li₂(x) + Li₂(1/x) = −π²/6 − ½ log²(−x), x < 0
  (assert-true (plt-close? (+ (polylog-num 2 -3) (polylog-num 2 -1/3))
                           (- (- 1.6449340668482264) (* 0.5 (^ (eval-num '(log 3)) 2))) 0.0000000001))
  ; Li_s(x) + Li_s(−x) = 2^(1−s) Li_s(x²)
  (assert-true (plt-close? (+ (polylog-num 3 0.8) (polylog-num 3 -0.8)) (* 0.25 (polylog-num 3 0.64)) 0.0000000001)))

(deftest "lambert-w-num: известные значения"
  (assert-true (plt-close? (lambert-w-num 1) 0.5671432904097838 0.000000000000001))
  (assert-true (plt-close? (lambert-w-num 0) 0.0 0.000000000000001))
  (assert-true (plt-close? (lambert-w-num (exp 1.0)) 1.0 0.000000000000001))
  (assert-true (plt-close? (lambert-w-num -0.3) -0.4894022271 0.0000000001))
  (assert-true (plt-close? (lambert-w-num 100) 3.3856301402900502 0.00000000001))
  (assert-equal (lambert-w-num -1) #f))        ; x < −1/e: значение комплексное

(deftest "lambert-w-num: W e^W = x"
  (assert-true (plt-close? (* (lambert-w-num 2.5) (exp (lambert-w-num 2.5))) 2.5 0.00000000001))
  (assert-true (plt-close? (* (lambert-w-num -0.2) (exp (lambert-w-num -0.2))) -0.2 0.00000000001))
  (assert-true (plt-close? (* (lambert-w-num 1000) (exp (lambert-w-num 1000))) 1000 0.0000001)))

(deftest "polylog-evalf: выражения с головами"
  (assert-true (plt-close? (polylog-evalf '(+ 1 (polylog 2 1/2))) 1.5822405264650125 0.000000000001))
  (assert-true (plt-close? (polylog-evalf '(* 2 (lambert_w 1))) 1.1342865808195676 0.000000000001))
  (assert-equal (polylog-evalf '(polylog 2 5)) #f))

; ---------- тождества ----------

(deftest "polylog: значения и свёртки"
  (assert-equal (simplify '(polylog 2 0)) 0)
  (assert-equal (simplify '(polylog 1 x)) '(* -1 (log (+ 1 (* -1 x)))))
  (assert-equal (simplify '(polylog 0 x)) '(* x (^ (+ 1 (* -1 x)) -1)))
  (assert-equal (simplify '(polylog -1 x)) '(* x (^ (+ 1 (* -1 x)) -2)))
  (assert-equal (simplify '(polylog 2 1)) '(* 1/6 (^ pi 2)))
  (assert-equal (simplify '(polylog 4 1)) '(* 1/90 (^ pi 4)))
  (assert-equal (simplify '(polylog 2 -1)) '(* -1/12 (^ pi 2)))
  (assert-equal (simplify '(polylog 2 1/2)) '(+ (* 1/12 (^ pi 2)) (* -1/2 (^ (log 2) 2))))
  (assert-equal (simplify '(polylog 3 x)) '(polylog 3 x))        ; атом
  (assert-equal (simplify '(polylog 3 1)) '(polylog 3 1)))        ; ζ(3) в проекте нет

(deftest "polylog: значения совпадают с численными"
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog 2 1/2))) (polylog-num 2 1/2) 0.000000000001))
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog 2 -1))) (polylog-num 2 -1) 0.000000000001))
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog 4 -1))) (polylog-num 4 -1) 0.000000000001))
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog 6 1))) (polylog-num 6 1) 0.000000000001))
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog 6 -1))) (polylog-num 6 -1) 0.000000000001))
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog 0 1/3))) 0.5 0.000000000001))
  (assert-true (plt-close? (polylog-evalf (simplify '(polylog -2 1/3))) (/ (* (/ 1 3) (/ 4 3)) (^ (/ 2 3) 3)) 0.000000000001)))

(deftest "lambert_w: значения и условия"
  (assert-equal (simplify '(lambert_w 0)) 0)
  (assert-equal (simplify '(lambert_w (exp 1))) 1)
  (assert-equal (simplify '(lambert_w (* -1 (exp -1)))) -1)
  (assert-equal (simplify '(lambert_w (* 2 (exp 2)))) 2)
  ; без допущений W(x·eˣ) не упрощается (при x < −1 это другая ветвь)
  (assert-equal (simplify '(lambert_w (* x (exp x)))) '(lambert_w (* x (exp x))))
  (assert-equal (assuming ((x positive)) (simplify '(lambert_w (* x (exp x))))) 'x)
  (assert-equal (simplify '(lambert_w (* -3 (exp -3)))) '(lambert_w (* -3 (exp -3))))
  (assert-equal (simplify '(* y (lambert_w x) (exp (lambert_w x)))) '(* x y)))

; ---------- производные ----------

(deftest "polylog: производная (проверка конечными разностями и вид)"
  (assert-equal (pl-diff 'x '(polylog 2 x)) '(* -1 (^ x -1) (log (+ 1 (* -1 x)))))
  (assert-equal (pl-diff 'x '(polylog 1 x)) '(^ (+ 1 (* -1 x)) -1))
  (assert-equal (pl-diff 'x '(polylog 2 (* 3 x))) '(* -1 (^ x -1) (log (+ 1 (* -3 x)))))
  (assert-equal (pl-diff 'x '(polylog 3 (^ x 2))) '(* 2 (^ x -1) (polylog 2 (^ x 2))))
  (assert-true (plt-close? (plt-at (pl-diff 'x '(polylog 3 (+ x (^ x 2)))) 'x 0.2)
                           (plt-fd (lambda (t) (polylog-num 3 (+ t (* t t)))) 0.2) 0.0000001))
  (assert-true (plt-close? (plt-at (pl-diff 'x '(polylog 2 (* -2 x))) 'x 0.3)
                           (plt-fd (lambda (t) (polylog-num 2 (* -2 t))) 0.3) 0.0000001)))

(deftest "polylog: m-diff языка вычисляет остатки"
  (assert-equal (math-eval "diff(polylog(2, 3*x), x)") '(* -1 (^ x -1) (log (+ 1 (* -3 x)))))
  (assert-equal (math-eval "diff(polylog(3, x^2), x)") '(* 2 (^ x -1) (polylog 2 (^ x 2)))))

(deftest "lambert_w: производная"
  (assert-equal (diff 'x '(lambert_w x))
                '(* (^ x -1) (^ (+ 1 (lambert_w x)) -1) (lambert_w x)))
  (assert-equal (diff 'x '(lambert_w (* 2 x)))
                '(* (^ x -1) (^ (+ 1 (lambert_w (* 2 x))) -1) (lambert_w (* 2 x))))
  (assert-true (plt-close? (plt-at (diff 'x '(lambert_w x)) 'x 1.5)
                           (plt-fd (lambda (t) (lambert-w-num t)) 1.5) 0.0000001)))

; ---------- ряды ----------

(deftest "series: polylog и lambert_w в нуле"
  (assert-equal (math-eval "series(polylog(2, x), x, 0, 5)") (math-eval "series(x + x^2/4 + x^3/9 + x^4/16, x, 0, 5)"))
  (assert-equal (taylor '(polylog 2 x) 'x 0 4) '(+ x (* 1/4 (^ x 2)) (* 1/9 (^ x 3))))
  (assert-equal (taylor '(lambert_w x) 'x 0 4) '(+ x (* -1 (^ x 2)) (* 3/2 (^ x 3))))
  (assert-equal (taylor '(polylog 3 (+ x (^ x 2))) 'x 0 3) '(+ x (* 9/8 (^ x 2)))))

; ---------- интегралы ----------

(deftest "integrate: log(1 ± a t)/t → −Li₂(∓a t)"
  (assert-equal (integrate '(* (^ x -1) (log (+ 1 x))) 'x) '(* -1 (polylog 2 (* -1 x))))
  (assert-true (int-check (integrate '(* (^ x -1) (log (+ 1 (* -2 x)))) 'x) '(* (^ x -1) (log (+ 1 (* -2 x)))) 'x))
  (assert-equal (integrate '(* (^ x -1) (log (+ 1 (* -2 x)))) 'x) '(* -1 (polylog 2 (* 2 x))))
  (assert-equal (integrate '(* 3 (^ x -1) (log (+ 1 (* -1 x)))) 'x) '(* -3 (polylog 2 x)))
  ; x^n в аргументе: u = x², dx/x = du/(2u)
  (assert-equal (integrate '(* (^ x -1) (log (+ 1 (^ x 2)))) 'x) '(* -1/2 (polylog 2 (* -1 (^ x 2)))))
  (assert-true (int-check (integrate '(* (^ x -1) (log (+ 1 (^ x 2)))) 'x) '(* (^ x -1) (log (+ 1 (^ x 2)))) 'x)))

(deftest "integrate: atanh, Li_s, log(t)/(1−t)"
  (assert-equal (integrate '(* (^ x -1) (atanh x)) 'x)
                '(* 1/2 (+ (polylog 2 x) (* -1 (polylog 2 (* -1 x))))))
  (assert-equal (integrate '(* (^ x -1) (polylog 2 x)) 'x) '(polylog 3 x))
  (assert-equal (integrate '(* (^ x -1) (polylog 3 (* 2 x))) 'x) '(polylog 4 (* 2 x)))
  (assert-equal (integrate '(* (log x) (^ (+ 1 (* -1 x)) -1)) 'x) '(polylog 2 (+ 1 (* -1 x))))
  (assert-true (int-check (integrate '(* (log x) (^ (+ 1 (* -1 x)) -1)) 'x) '(* (log x) (^ (+ 1 (* -1 x)) -1)) 'x)))

(deftest "integrate: пример плана (a + b·atanh(c x²))/x"
  (let ((e '(* (^ x -1) (+ a (* b (atanh (* c (^ x 2))))))))
    (let ((F (integrate e 'x)))
      (assert-true (not (contains-sym? F 'integrate)))
      (assert-true (int-check F e 'x))
      (assert-true (contains-sym? F 'polylog)))))

(deftest "integrate: сумма с элементарным слагаемым"
  (let ((e '(+ (^ x -1) (* (^ x -1) (log (+ 1 x))) (exp x))))
    (let ((F (integrate e 'x)))
      (assert-true (not (contains-sym? F 'integrate)))
      (assert-true (int-check F e 'x)))))

(deftest "integrate: определённые через Li₂"
  (assert-equal (integrate '(* (^ x -1) (log (+ 1 x))) 'x 0 1) '(* 1/12 (^ pi 2)))
  (assert-equal (integrate '(* (^ x -1) (log (+ 1 (* -1 x)))) 'x 0 1) '(* -1/6 (^ pi 2)))
  (assert-equal (integrate '(* (log x) (^ (+ 1 (* -1 x)) -1)) 'x 0 1) '(* -1/6 (^ pi 2)))
  (assert-equal (integrate '(* (^ x -1) (atanh x)) 'x 0 1) '(* 1/8 (^ pi 2)))
  ; численная сверка Симпсоном: ∫₀^1/2 log(1+x)/x = −Li₂(−1/2)
  (let ((v (polylog-evalf (integrate '(* (^ x -1) (log (+ 1 x))) 'x 0 1/2))))
    (assert-true (plt-close? v (- (polylog-num 2 -1/2)) 0.000000000001))))

(deftest "integrate: честные отказы сохранены"
  (assert-true (contains-sym? (integrate '(exp (^ x 2)) 'x) 'integrate))
  (assert-true (contains-sym? (integrate '(* (^ x -1) (log (+ 1 (^ x 2) (sin x)))) 'x) 'integrate))
  ; log(1 + x²)/x при a = x·... не из таблицы: аргумент не k·xⁿ
  (assert-true (contains-sym? (integrate '(* (^ x -1) (log (+ 2 x))) 'x) 'integrate)))

(deftest "int-check: подделка ответа с Li₂ отвергается"
  (let ((e '(* (^ x -1) (log (+ 1 x)))))
    (assert-true (int-check '(* -1 (polylog 2 (* -1 x))) e 'x))
    (assert-true (not (int-check '(polylog 2 (* -1 x)) e 'x)))
    (assert-true (not (int-check '(* -1 (polylog 2 x)) e 'x)))
    (assert-true (not (int-check '(* -1 (polylog 3 (* -1 x))) e 'x)))))

(deftest "integrate: ∫W = u(W − 1) + e^W, ∫W/x = W + W²/2"
  (let ((F (integrate '(lambert_w x) 'x)))
    (assert-true (int-check F '(lambert_w x) 'x))
    ; совпадает с x(W − 1 + 1/W) (W·e^W = x): численно
    (assert-true (plt-close? (plt-at F 'x 2.0) (let ((w (lambert-w-num 2.0))) (* 2.0 (+ w -1.0 (/ 1.0 w)))) 0.0000000001)))
  (let ((F (integrate '(* 3 (lambert_w (+ 1 (* 2 x)))) 'x)))
    (assert-true (int-check F '(* 3 (lambert_w (+ 1 (* 2 x)))) 'x)))
  (assert-true (int-check (integrate '(* (^ x -1) (lambert_w (* 2 x))) 'x) '(* (^ x -1) (lambert_w (* 2 x))) 'x))
  (assert-true (not (int-check '(* x (lambert_w x)) '(lambert_w x) 'x))))

(deftest "integrate: определённый ∫₀¹ W dx не теряет F(0)"
  ; F(x) = x(W−1) + e^W: F(0) = 1; ∫₀¹ W = W(1) − 2 + e^W(1) = 0.3303…
  (let ((v (polylog-evalf (integrate '(lambert_w x) 'x 0 1))))
    (assert-true (plt-close? v 0.33036648 0.000001))))

; ---------- solve ----------

(deftest "solve: уравнения типа Ламберта"
  (assert-equal (solve '(= (* x (exp x)) 2) 'x) (list->set (list '(lambert_w 2))))
  (assert-equal (solve '(= (+ x (exp x)) 3) 'x) (list->set (list '(+ 3 (* -1 (lambert_w (exp 3)))))))
  (assert-equal (solve '(= (* 2 x (exp (* 3 x))) 5) 'x) (list->set (list '(* 1/3 (lambert_w 15/2)))))
  (assert-equal (solve '(= (* a x (exp (* b x))) c) 'x)
                (list->set (list '(* (^ b -1) (lambert_w (* (^ a -1) b c))))))
  ; корень проверяется подстановкой
  (let ((s (car (set->list (solve '(= (* x (exp x)) 2) 'x)))))
    (assert-true (plt-close? (polylog-evalf (subst (list 'x s) '(* x (exp x)))) 2.0 0.0000000001)))
  (let ((s (car (set->list (solve '(= (+ x (* 2 (exp (* 3 x)))) 4) 'x)))))
    (assert-true (plt-close? (polylog-evalf (subst (list 'x s) '(+ x (* 2 (exp (* 3 x)))))) 4.0 0.0000000001))))

(deftest "solve: Ламберт — вещественная область"
  (assert-equal (assuming ((x reals)) (solve '(= (* x (exp x)) 2) 'x)) (list->set (list '(lambert_w 2))))
  ; x e^x = −1: корней нет (−1 < −1/e)
  (assert-equal (assuming ((x reals)) (solve '(= (* x (exp x)) -1) 'x)) (set))
  ; −1/e < a < 0: два вещественных корня, ветви W₋₁ нет — отказ, не неполный ответ
  (assert-error (assuming ((x reals)) (solve '(= (* x (exp x)) -1/5) 'x))))

; ---------- язык ----------

(deftest "mathlang: polylog и lambert_w"
  (assert-equal (math-eval "polylog(2, 1)") '(* 1/6 (^ pi 2)))
  (assert-equal (math-eval "polylog(2, x)") '(polylog 2 x))
  (assert-equal (math-eval "polylog(1, x)") '(* -1 (log (+ 1 (* -1 x)))))
  (assert-true (plt-close? (math-eval "polylog(2, 0.5)") 0.5822405264650125 0.000000000001))
  (assert-equal (math-eval "polylog(2, 3/2)") '(polylog 2 3/2))
  (assert-equal (math-eval "lambert_w(0)") 0)
  (assert-equal (math-eval "lambert_w(x)") '(lambert_w x))
  (assert-true (plt-close? (math-eval "lambert_w(1.0)") 0.5671432904097838 0.000000000001))
  (assert-equal (math-eval "lambert_w(-2.0)") '(lambert_w -2.0))
  (assert-equal (math-eval "integrate(log(1 + x)/x, x)") '(* -1 (polylog 2 (* -1 x))))
  (assert-equal (math-eval "integrate(log(1 + x)/x, x, 0, 1)") '(* 1/12 (^ pi 2)))
  (assert-equal (math-eval "solve(x*exp(x) = 2, x)") (list->set (list '(lambert_w 2)))))
