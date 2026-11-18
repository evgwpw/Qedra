; INT.SUBST: скрытая подстановка (lib/integrate/subst.lisp) — u из кирпичиков f, f/u′ = R(u), R рациональна;
; ответ проверен int-check по исходному f; нет подстановки — #f с причиной в (int-subst-stats).

(define (su-solved f)
  (let ((F (int-hidden-subst f 'x)))
    (assert-true F)
    (assert-true (int-check F f 'x))
    F))

(deftest "subst: Чебышёв, стресс 2 — (3x⁴+1)/(√(x⁴+1)(x²(x⁴+1)+1)) = atan(x√(x⁴+1))"
  (assert-equal (int-hidden-subst (math-eval "(3*x**4 + 1)/(sqrt(x**4 + 1)*(x**2*(x**4 + 1) + 1))") 'x)
                '(atan (* x (^ (+ 1 (^ x 4)) 1/2)))))

(deftest "subst: стресс 37 — u = √(x⁴+4x²+4), ответ atan"
  (let ((F (su-solved (math-eval "2*x*(x**4 + 4*x**2 + (-x**2 - 2)*(x**2 - 2) + 4)/(sqrt(x**4 + 4*x**2 + 4)*(x**4 + 4*x**2 + (x**2 - 2)**2 + 4))"))))
    (assert-true (contains-sym? F 'atan))))

(deftest "subst: корень третьей степени — (x²+2x+6)/((1+x)·∛(x²+x+2)·(2x²−x+2))"
  ; бюджет ступени 60 с только здесь: на CI под нагрузкой 3 с не хватало (Qedra ci, 6aefe9b)
  (let ((old integrate::int-subst-time-limit))
    (unwind-protect
      (begin (set! integrate::int-subst-time-limit 60)
             (su-solved (math-eval "(x**2+2*x+6)/(1+x)/(x**2+x+2)**(1/3)/(2*x**2-x+2)")))
      (set! integrate::int-subst-time-limit old))))

(deftest "subst: параметры — R от параметров не зависит, (2ax−... )/(…)·(−ax+x²+b)^(−1/4)"
  (let ((F (su-solved (math-eval "(-a+2*x)/(-a*x+x**2+b-1)/(-a*x+x**2+b)**(1/4)"))))
    (assert-true (contains-sym? F 'atan))))

(deftest "subst: вложенный радикал — (1+√(x²+1))^(1/2)/(x²+1)"
  (su-solved (math-eval "(1+(x**2+1)**(1/2))**(1/2)/(x**2+1)")))

(deftest "subst: R, верная лишь на куске оси (√(x−3) при x < 3 и x > 3), отвергается"
  (assert-equal (int-hidden-subst (math-eval "1/(1+(x**2-6*x+9)**(1/4))") 'x) #f)
  (assert-equal (car (int-subst-stats)) 'no-u))

(deftest "subst: R не рациональна — √(x⁴+1) и log(x)/(x√(log²x+2)√(log²x+3)) — честный отказ #f"
  (for-each (lambda (s) (assert-equal (int-hidden-subst (math-eval s) 'x) #f))
            '("(x**4+1)**(1/2)" "log(x)/(x*sqrt(log(x)**2 + 2)*sqrt(log(x)**2 + 3))")))

(deftest "subst: без радикала ступень не применяется (su-applicable?)"
  (assert-equal (integrate::su-applicable? (math-eval "1/(x**2+1)") 'x) #f)
  (assert-true (integrate::su-applicable? (math-eval "sqrt(x**4+1)") 'x)))

(deftest "subst: флаг int-subst-enabled и without-subst — через integrate ступень выключается"
  (let ((f (math-eval "(3*x**4 + 1)/(sqrt(x**4 + 1)*(x**2*(x**4 + 1) + 1))")))
    (assert-equal (without-subst (lambda () integrate::int-subst-enabled)) #f)
    (assert-equal integrate::int-subst-enabled #t)
    (assert-equal (integrate::int-subst-fallback f 'x) '(atan (* x (^ (+ 1 (^ x 4)) 1/2))))
    (assert-equal (without-subst (lambda () (integrate::int-subst-fallback f 'x))) #f)))

(deftest "subst: через integrate — ответ каскада с шагом «Подстановка»"
  (let* ((f (math-eval "(3*x**4 + 1)/(sqrt(x**4 + 1)*(x**2*(x**4 + 1) + 1))"))
         (F (integrate f 'x)))
    (assert-true (not (contains-sym? F 'integrate)))
    (assert-true (int-check F f 'x))))
