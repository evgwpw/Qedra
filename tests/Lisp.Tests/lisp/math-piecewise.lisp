; math-piecewise.lisp — Q.2: piecewise во входном языке и печати.

(deftest "Q.2: piecewise читается, печатается и читается обратно"
  (let* ((v (math-eval "piecewise((x>0, x), (x<=0, -x))"))
         (s (math-print v)))
    (assert-equal (car v) 'piecewise)
    (assert-equal (length (cadr v)) 2)
    (assert-equal s "piecewise((x > 0, x), (x ≤ 0, -x))")
    ; круговой тест: печать читается в ту же форму
    (assert-equal (math-eval s) v)))

(deftest "Q.2: три ветви, and/or и diff по ветвям"
  (let* ((v (math-eval "piecewise((x>1 and y>0, x*y), (x>1 or y>0, x+y), (x<=1, 0))"))
         (d (diff 'x v)))
    (assert-equal (length (cadr v)) 3)
    (assert-equal (car d) 'piecewise)
    (assert-equal (length (cadr d)) 3)
    (assert-true (string-contains? (math-print d) "piecewise("))
    ; условия сохранены (не потеряны и не изменены)
    (assert-equal (car (car (cadr d))) '(and (> x 1) (> y 0)))
    (assert-equal (car (nth (cadr d) 1)) '(or (> x 1) (> y 0)))
    (assert-equal (car (nth (cadr d) 2)) '(<= x 1))))

(deftest "Q.2: ответ integrate с параметром печатается как piecewise"
  (let ((v (math-eval "integrate(exp(a*x), x)")))
    (assert-equal (car v) 'piecewise)
    (assert-true (string-contains? (math-print v) "piecewise(")))
  (let ((v (math-eval "integrate(x^a, x)")))
    (assert-equal (car v) 'piecewise)
    (assert-true (string-contains? (math-print v) "piecewise(")))
  (let ((v (math-eval "integrate(1/(x^2+a), x)")))
    (assert-equal (car v) 'piecewise)
    (assert-equal (length (cadr v)) 3)
    (assert-true (string-contains? (math-print v) "piecewise("))))

; ---------- WASM.6a Д9: условия piecewise вычисляются ----------

(deftest "WASM.6a Д9: числовые условия выбирают ветвь"
  (assert-equal (math-show (math-eval "piecewise((2 > 0, 7), (2 <= 0, -7))")) "7")
  (assert-equal (math-show (math-eval "piecewise((1 > 2, 7), (2 <= 2, -7))")) "-7")
  ; ни одно условие не верно — undefined
  (assert-equal (math-show (math-eval "piecewise((1 > 2, 7), (2 < 1, -7))")) "undefined")
  ; невыбранная ветвь не вычисляется: 1/0 не возникает
  (assert-equal (math-show (math-eval "piecewise((2 > 0, 7), (2 <= 0, 1/0))")) "7"))

(deftest "WASM.6a Д9: символьное условие сохраняет piecewise, подстановка числа решает"
  (assert-equal (car (math-eval "piecewise((x > 0, x), (x <= 0, -x))")) 'piecewise)
  (assert-equal (math-show (math-eval "subst(piecewise((x > 0, x), (x <= 0, -x)), x, 2)")) "2")
  (assert-equal (math-show (math-eval "subst(piecewise((x > 0, x), (x <= 0, -x)), x, -3)")) "3")
  ; ветвь = 0 при x = 0, деление в другой ветви не выполняется
  (assert-equal (math-show (math-eval "subst(piecewise((x = 0, 0), (x > 0, 1/x)), x, 0)")) "0")
  ; осталось неизвестное y — прежняя форма, но с подставленным x
  (assert-equal (math-show (math-eval "subst(piecewise((x > y, x), (x <= y, y)), x, 5)"))
                "piecewise((5 > y, 5), (5 ≤ y, y))"))
