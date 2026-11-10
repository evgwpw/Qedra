; WASM.5a: комментарии шагов — входным языком, а не Lisp-формой; пустых шагов в brief нет.

; Признак Lisp-формы в тексте: «(оператор » или «(голова » для голов, которые печатались Lisp-формой.
; Замечание ревью WASM.5: прежний критерий «(слово пробел» ловил обычный текст «(u + v)'» — ради него
; из пояснений убирали пробелы; теперь проверяется только настоящая префиксная запись
(define sc-lisp-heads '("(* " "(+ " "(^ " "(- " "(/ " "(erf " "(erfi " "(erfc " "(Ei " "(Si " "(Ci " "(li "
                        "(Shi " "(Chi " "(exp " "(log " "(sin " "(cos " "(sqrt " "(int/dx " "(d/dx "))

(define (sc-lisp-form? s)
  (and (string? s) (any? (lambda (h) (string-contains? s h)) sc-lisp-heads)))

(define (sc-empty-step? st)
  (and (equal? (to-string (step-title st)) "")
       (equal? (to-string (step-comment st)) "")
       (null? (step-before st))
       (null? (step-after st))))

; обход журнала: все комментарии без Lisp-форм, пустых шагов нет
(define (sc-check-steps src level)
  (let ((cap (capture-step-log (lambda () (math-eval src)) level)))
    (let walk ((xs (cadr cap)))
      (if (null? xs) #t
          (begin
            (assert-true (not (sc-lisp-form? (step-comment (car xs)))))
            (assert-true (not (sc-lisp-form? (step-title (car xs)))))
            (assert-true (not (sc-empty-step? (car xs))))
            (walk (step-children (car xs)))
            (walk (cdr xs)))))))

(define sc-corpus
  '("integrate(exp(x^2), x)" "integrate(exp(-x^2), x)" "integrate(sin(x)/x, x)"
    "integrate(cos(x)/x, x)" "integrate(exp(x)/x, x)" "integrate(1/log(x), x)"
    "integrate(log(x), x)" "integrate(x*exp(x), x)" "integrate(x^2*exp(x), x)"
    "integrate(sin(x)^2, x)" "integrate(tan(x), x)" "integrate(1/(x^3+1), x)"
    "integrate(1/(x^2-1), x)" "integrate(1/(x^6+x^3+1), x)" "integrate(sqrt(1+x^2), x)"
    "integrate(exp(-x)*sin(x), x)" "integrate(atan(x), x)" "integrate(sqrt(1+x), x)"
    "dsolve(y' = y, y(x))" "dsolve(y'' + y = 0, y(x))"
    "limit(sin(x)/x, x, 0)" "limit((1+1/x)^x, x, inf)"
    "sum(k^2, k, 1, n)" "sum(1/k^2, k, 1, inf)"
    "solve(x^3 - 1, x)" "factor(x^4 - 5*x^2 + 4)"
    "integrate(exp(-x), x, 0, 1)" "diff(sin(x)^2, x)"))

(deftest "WASM.5a: комментарии шагов — без Lisp-форм, пустых шагов нет (brief и full)"
  (for-each (lambda (src) (sc-check-steps src 'brief)) sc-corpus)
  (for-each (lambda (src) (sc-check-steps src 'full)) sc-corpus))

(deftest "WASM.5a: подсказка о специальной функции печатается входным языком"
  (let* ((cap (capture-step-log (lambda () (math-eval "integrate(exp(x^2), x)")) 'full))
         (text (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-true (string-contains? text "erfi(x)"))
    (assert-true (not (sc-lisp-form? text)))))

(deftest "WASM.5a: ответы и заголовки шагов не изменились"
  (for-each
    (lambda (src)
      (let ((a (math-eval src))
            (cap (capture-step-log (lambda () (math-eval src)) 'brief)))
        (assert-equal (car cap) a)
        (assert-true (string-contains? (steps-text (cadr cap) (caddr cap) 'ru) "Алгоритм Риша"))))
    '("integrate(exp(x^2), x)" "integrate(sin(x)/x, x)" "integrate(exp(-x^2), x)")))
