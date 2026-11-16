; INT.ANSATZ.7: метод Блейка (lib/integrate/blake.lisp) — псевдоэллиптические интегралы R(x)·r(x)^(j/m), deg r > 2:
; подстановка Лорана u = s(x)/x^k, рациональная часть по значениям в точках, integrate по u, обратная подстановка;
; каждый ответ проходит int-check по исходному f; нет подстановки — #f с причиной в (int-blake-stats).

(define (bk-solved f)
  (let ((F (int-blake f 'x)))
    (assert-true F)
    (assert-true (int-check F f 'x))
    F))

(deftest "blake: пример статьи (x²−1)/((x²+1)√(x⁴+1)) = −(1/√2)·atan(√2·x/√(x⁴+1))"
  (let ((F (bk-solved (math-eval "(x**2-1)/(x**2+1)/(1+x**4)**(1/2)"))))
    (assert-true (contains-sym? F 'atan))))

(deftest "blake: √(x⁴+1)/x — точная производная, линейное подкоренное u = r/x⁴"
  (bk-solved (math-eval "(x**4-1)/x**2/(x**4+1)**(1/2)")))

(deftest "blake: x²/√(x⁶−1) = ⅓·log(x³+√(x⁶−1)) — корень степени 6"
  (let ((F (bk-solved (math-eval "x**2/(x**6-1)**(1/2)"))))
    (assert-true (contains-sym? F 'log))))

(deftest "blake: (x⁴−1)√(x⁴+1)/(x⁸+1) — логарифмы и арктангенс от √(x⁴+1)/x"
  (bk-solved (math-eval "(x**4-1)*(x**4+1)**(1/2)/(x**8+1)")))

(deftest "blake: (x−1)/((x+1)√(x³+x²+x)) = −2·atan(x/√(x³+x²+x))"
  (assert-equal (int-blake (math-eval "(-1+x)/(1+x)/(x**3+x**2+x)**(1/2)") 'x)
                '(* -2 (atan (* x (^ (+ x (^ x 2) (^ x 3)) -1/2))))))

; знак (пилот c1b8d62): вынос (x+1) из √((x+1)²·…) неверен при x < −1 — метод отказывается (а не даёт ответ, верный на полуоси)
(deftest "blake: кратный множитель нечётной степени не выносится из-под корня — 1/√(x⁴+4x+3), √((5x+3)²)"
  (assert-true (not (int-blake (math-eval "1/(x**4+4*x+3)**(1/2)") 'x)))
  (assert-true (not (int-blake (math-eval "((5*x+3)**2)**(1/2)") 'x))))

(deftest "blake: нечётное E/2 — ответ для x < 0 через |x| (проверка численной производной F)"
  (let* ((f (math-eval "((-1+x**2)*(1+x**2)*(1+3*x**2+x**4)**(1/2))/(x**2*(1+x+x**2)**2)"))
         (F (int-blake f 'x)))
    (assert-true F)
    ; форма может быть и без abs (после исправления знака при выносе из-под корня) — важна проверка по обе стороны нуля
    (assert-true (integrate::bk-numeric-ok? F f 'x))))

(deftest "blake: эллиптические и непсевдоэллиптические — честный отказ #f"
  (for-each (lambda (s) (assert-equal (int-blake (math-eval s) 'x) #f))
            '("1/(x**4+1)**(1/2)" "1/(x**3+x+1)**(1/2)" "x/(x**5+x+1)**(1/2)")))

(deftest "blake: параметры и несколько радикалов — не берётся (причина в статистике)"
  (assert-equal (int-blake (math-eval "1/(x**4+a)**(1/2)") 'x) #f)
  (assert-equal (car (int-blake-stats)) 'parameters)
  (assert-equal (int-blake (math-eval "1/((x**4+1)**(1/2)+(x**4+2)**(1/2))") 'x) #f))

(deftest "blake: integrate с радикалом степени 4 даёт ответ (ступень каскада)"
  (let ((f (math-eval "(x**4-1)/x**2/(x**4+1)**(1/2)")))
    (assert-equal (integrate f 'x) '(* (^ x -1) (^ (+ 1 (^ x 4)) 1/2)))))
