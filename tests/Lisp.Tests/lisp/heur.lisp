; INT.HEUR: приёмы «как у модели» (lib/integrate/heur.lisp, int-ahyp-full в core.lisp, добавочные кандидаты И4 в subst.lisp).
; Каждый ответ — int-check по исходному f и численная проверка самой F (he-num-ok?: точки по обе стороны нуля).

(define (hv-num e v) (eval-num (subst (list 'u v) e)))
(define (hv-close? a b) (< (abs (- a b)) (* 0.0000001 (+ 1 (abs b)))))
; e^(n·g(u)) = int-ahyp-full в точках u (и при u < 0, и при u > 0, где g определена)
(define (hv-ahyp-ok? head n pts)
  (every? (lambda (v)
            (let ((lhs (hv-num (list 'exp (list '* n (list head 'u))) v))
                  (rhs (hv-num (integrate::int-ahyp-full (list '* n (list head 'u))) v)))
              (hv-close? lhs rhs)))
          pts))

(deftest "heur: e^(n·asinh u) = (u+√(1+u²))^n — все u"
  (assert-true (hv-ahyp-ok? 'asinh 2 '(-3 -0.5 0.5 3)))
  (assert-true (hv-ahyp-ok? 'asinh -1 '(-3 -0.5 0.5 3)))
  (assert-true (hv-ahyp-ok? 'asinh 3 '(-2 2))))

(deftest "heur: e^(n·acosh u) = (u+√(u−1)√(u+1))^n — область u ≥ 1"
  (assert-true (hv-ahyp-ok? 'acosh 1 '(1.5 3 10)))
  (assert-true (hv-ahyp-ok? 'acosh 2 '(1.5 3)))
  (assert-true (hv-ahyp-ok? 'acosh -1 '(1.5 3))))

(deftest "heur: e^(n·acsch u) = (1/u+√(1+1/u²))^n — u < 0 и u > 0 (ловушка √(1+u²)/u не берётся)"
  (assert-true (hv-ahyp-ok? 'acsch 1 '(-3 -0.5 0.5 3)))
  (assert-true (hv-ahyp-ok? 'acsch 2 '(-3 -0.5 0.5 3)))
  (assert-true (hv-ahyp-ok? 'acsch -1 '(-3 -0.5 0.5 3)))
  ; именно эта запись: корень от 1 + u⁻², не √(1+u²)/u
  (assert-true (contains-sym? (integrate::int-ahyp-full '(* 2 (acsch u))) 'u))
  ; контроль ловушки: √(1+u²)/u при u < 0 — отрицательное число, e^(acsch u) > 0 всегда
  (assert-true (< (hv-num '(/ (sqrt (+ 1 (^ u 2))) u) -2) 0)))

(deftest "heur: e^(n·asech u) = ((1+√(1−u²))/u)^n — область 0 < u ≤ 1"
  (assert-true (hv-ahyp-ok? 'asech 1 '(0.2 0.5 0.9)))
  (assert-true (hv-ahyp-ok? 'asech 3 '(0.2 0.5 0.9))))

(deftest "heur: e^(n·atanh u) = ((1+u)/(1−u))^(n/2), e^(n·acoth u) = ((u+1)/(u−1))^(n/2), в том числе нечётные n"
  (assert-true (hv-ahyp-ok? 'atanh 1 '(-0.7 -0.2 0.3 0.8)))
  (assert-true (hv-ahyp-ok? 'atanh 3 '(-0.7 0.3)))
  (assert-true (hv-ahyp-ok? 'atanh -1 '(-0.7 0.3)))
  (assert-true (hv-ahyp-ok? 'acoth 1 '(-3 -1.5 1.5 3)))
  (assert-true (hv-ahyp-ok? 'acoth 3 '(-3 1.5)))
  (assert-true (hv-ahyp-ok? 'acoth 2 '(-3 1.5))))

(deftest "heur: int-exp-ahyp-full обходит дерево; чужие exp не трогает"
  (assert-equal (integrate::int-exp-ahyp-full '(exp (* 2 x))) '(exp (* 2 x)))
  (assert-true (not (contains-sym? (integrate::int-exp-ahyp-full '(* x (exp (asinh x)))) 'asinh))))

(define (hv-solved s)
  (let* ((f (math-eval s)) (F (int-heur f 'x)))
    (assert-true F)
    (assert-true (not (contains-sym? F 'integrate)))
    (assert-true (int-check F f 'x))
    F))

(deftest "heur: ход 3 — x⁴·e^(2·acsch(ax)) (стенд llm-heur-21 № 19), ответ верен и при x < 0"
  (let* ((f (math-eval "x**4*exp(2*acsch(a*x))")) (F (hv-solved "x**4*exp(2*acsch(a*x))")))
    (assert-true (integrate::he-num-ok? F f 'x))))

(deftest "heur: ход 3 — x·e^(acosh(2x)), x·e^(asech x), e^(3·atanh x) (область, нечётное n)"
  (hv-solved "x*exp(acosh(2*x))")
  (hv-solved "x*exp(asech(x))")
  (hv-solved "exp(3*atanh(x))"))

(deftest "heur: ход 2 — e^(acot x)/(ax²+a)³ (№ 17), подстановка x = cot t, ответ в x"
  (let ((F (hv-solved "exp(acot(x))/(a*x**2+a)**3")))
    (assert-true (contains-sym? F 'acot))))

(deftest "heur: ход 2 — аргумент k·x: e^(acot(2x))/(1+4x²)"
  (hv-solved "exp(acot(2*x))/(1+4*x**2)"))

(deftest "heur: ход 2 — asin: √(1−x²)·asin(x)²"
  (hv-solved "sqrt(1-x**2)*asin(x)**2"))

(deftest "heur: ход 4 — stress 92: P·e^(x²+x)/(x⁴+1)^(3/2), ответ e^(x²+x)/√(x⁴+1)"
  (let ((F (hv-solved "(-2*x**3+(2*x+1)*(x**4+1))*exp(x**2+x)/(x**4+1)**(3/2)")))
    (assert-true (contains-sym? F 'exp))))

(deftest "heur: ход 4 — stress 49: D = Q²(1+t²), t = x√P/Q, ответ atan"
  (let ((F (hv-solved "(2*x**2*(-x**2-3)*(x**2+1)+2*x**2*(x**4+6*x**2+1)-(x**2+1)*(x**4+6*x**2+1))/((x**2*(x**4+6*x**2+1)+(x**2+1)**2)*sqrt(x**4+6*x**2+1))")))
    (assert-true (contains-sym? F 'atan))))

(deftest "heur: ход 4 — hebisch 8132: e^x/x + рациональная часть (A·e^u + B)"
  (hv-solved "(((625*x-625)*exp(1/5)**4+(-500*x**2+500*x)*exp(1/5)**3+(150*x**3-150*x**2-50*x+50)*exp(1/5)**2+(-20*x**4+20*x**3+20*x**2-20*x)*exp(1/5)+x**5-x**4-2*x**3+2*x**2+x-1)*exp(x)+100*exp(1/5)**2+(10*x**2-80*x)*exp(1/5)-2*x**3+12*x**2-4)/(625*x**2*exp(1/5)**4-500*x**3*exp(1/5)**3+(150*x**4-50*x**2)*exp(1/5)**2+(-20*x**5+20*x**3)*exp(1/5)+x**6-2*x**4+x**2)"))

(deftest "heur: подстановка e^w для гиперболических — tanh²(c+dx)/(a+b·sech²(c+dx))"
  (hv-solved "tanh(c+d*x)**2/(a+b*sech(c+d*x)**2)"))

(deftest "heur: подстановка N^x — 4^x/√(a+b/2^x)"
  (hv-solved "4**x/sqrt(a+b/2**x)"))

(deftest "heur: подстановка tan w — √(3+4tan x), tan^(3/2)/(1+tan)"
  (hv-solved "sqrt(3+4*tan(x))")
  (hv-solved "tan(x)**(3/2)/(1+tan(x))"))

(deftest "heur: честный отказ #f — нечётная степень cos при tan-подстановке и неберущийся интеграл"
  (assert-equal (int-heur (math-eval "exp(x**2)") 'x) #f)
  (assert-equal (int-heur (math-eval "sqrt(tan(x))*cos(x)") 'x) #f))

(deftest "heur: ступень применима только при форме хода (he-applicable?)"
  (assert-equal (integrate::he-applicable? (math-eval "1/(x**2+1)") 'x) #f)
  (assert-equal (integrate::he-applicable? (math-eval "sqrt(x**4+1)") 'x) #f)
  (assert-true (integrate::he-applicable? (math-eval "x*exp(asinh(x))") 'x))
  (assert-true (integrate::he-applicable? (math-eval "exp(acot(x))/(x**2+1)") 'x)))

(deftest "heur: флаг int-heur-enabled и без-heur"
  (assert-equal (without-heur (lambda () integrate::int-heur-enabled)) #f)
  (assert-equal integrate::int-heur-enabled #t))

(deftest "heur: И4 — добавочные кандидаты: отношение множителей подкоренного (числовой параметр)"
  (let* ((f (math-eval "(4*x**6-x)/(x**5+1)/(2*x**5+2-x)/(x**6+x)**(1/2)")) (F (int-hidden-subst f 'x)))
    (assert-true F)
    (assert-true (int-check F f 'x))))

(deftest "heur: И4 — без добавочных кандидатов (without-subst-extra) ступень видит прежний набор"
  (let ((f (math-eval "(4*x**6-x)/(x**5+1)/(2*x**5+2-x)/(x**6+x)**(1/2)")))
    (assert-true (without-subst-extra (lambda () (int-hidden-subst f 'x))))))

(deftest "heur: через integrate — шаг «Приём по структуре» и ответ верен"
  (let* ((f (math-eval "(-2*x**3+(2*x+1)*(x**4+1))*exp(x**2+x)/(x**4+1)**(3/2)")) (F (integrate f 'x)))
    (assert-true (not (contains-sym? F 'integrate)))
    (assert-true (int-check F f 'x))))

; пилот 6d56943: ветка struct давала e^|x|/sign(x) — производная верна, но скачок 2 в нуле, и ∫₋₁³ e^|x| выходило e³+e
(deftest "heur: кусочная первообразная с sign/abs, которых нет в f, отвергается (e^|x|)"
  (let ((F (integrate '(exp (abs x)) 'x)))
    (assert-true (not (contains-sym? F 'sign))))
  (let ((v (integrate '(exp (abs x)) 'x -1 3)))
    (assert-true (or (contains-sym? v 'integrate)
                     (< (abs (- (eval-num v) (eval-num (math-read "exp(3) + exp(1) - 2")))) 1e-9)))))
