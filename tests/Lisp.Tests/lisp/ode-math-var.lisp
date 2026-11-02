; ode-math-var.lisp — входной язык: штрихи y′ берутся по переменной из y(t) во втором аргументе dsolve

(define (omv-sol src) (car (ode-solutions (math-eval src))))

(deftest "OMV: y'' + y = 0, y(t), y(0) = 1, y'(0) = 0 → cos t"
  (assert-equal (omv-sol "dsolve(y'' + y = 0, y(t), y(0) = 1, y'(0) = 0)") '(= (y t) (cos t))))

(deftest "OMV: y' = t*y, y(0) = 1 → e^(t²/2)"
  (assert-equal (omv-sol "dsolve(y' = t*y, y(t), y(0) = 1)") '(= (y t) (exp (* 1/2 (^ t 2))))))

(deftest "OMV: y'' + y = heaviside(t − 1), метод Лапласа"
  (let ((r (math-eval "dsolve(y'' + y = heaviside(t - 1), y(t), y(0) = 0, y'(0) = 0)")))
    (assert-equal (ode::ode-field r :method) 'laplace)
    (assert-equal (car (ode-solutions r))
                  '(= (y t) (* (+ 1 (* -1 (cos (+ -1 t)))) (heaviside (+ -1 t)))))))

(deftest "OMV: явное y′(t) и старая форма y(x) без изменений"
  (assert-equal (omv-sol "dsolve(y'(t) = y(t), y(t), y(0) = 1)") '(= (y t) (exp t)))
  (assert-equal (omv-sol "dsolve(y'' + y = 0, y(x), y(0) = 1, y'(0) = 0)") '(= (y x) (cos x))))

(deftest "OMV: смесь y(t) и явной производной по x — не неверный ответ"
  (assert-true (equal? (ode-status (math-eval "dsolve(diff(y(x), x) = y, y(t), y(0) = 1)")) 'unknown)))

; ---------- WASM.6a Д1: печать ответа ОДУ во входном языке ----------

(deftest "WASM.6a Д1: dsolve печатается уравнениями, а не служебной Lisp-формой"
  (let* ((r (math-eval "dsolve(y' = x^4, y(x))"))
         (s (math-show r)))
    (assert-equal s "y(x) = C1 + 1/5*x^5")
    ; печать читается обратно в то же решение (math-read → уравнение)
    (assert-equal (math-eval s) (car (ode-solutions r)))
    ; особые решения — следом, тоже уравнением
    (let ((ss (math-show (math-eval "dsolve(y' = y^(2/3), y(x))"))))
      (assert-true (and (string-contains? ss "y(x) = 0")
                        (not (string-contains? ss "ode-solution")))))
    ; отказ — «unknown», не Lisp-форма
    (assert-equal (math-show (math-eval "dsolve(y' + y^2 = x, y(x))")) "unknown")
    ; нелиувиллево решение (Эйри) всё равно печатается уравнениями, а не «unknown»
    (assert-equal (math-show (math-eval "dsolve(y'' = x*y(x), y(x))"))
                  "y(x) = C1*AiryAi(x) + C2*AiryBi(x)")))

; ---------- WASM.6a Д4: ode_check с голым y ----------

(deftest "WASM.6a Д4: ode_check принимает верное решение, записанное через y"
  ; до правки y′ читался как (diff (y x) x), а y — как символ: проверка всегда #f
  (assert-equal (math-show (math-eval "ode_check(y' = 1 + y^2, y = tan(x), y(x))")) "true")
  (assert-equal (math-show (math-eval "ode_check(y' = 2*y, y = exp(2*x), y(x))")) "true"))

(deftest "WASM.6a Д4: подделка по-прежнему отвергается"
  (assert-equal (math-show (math-eval "ode_check(y' = 1 + y^2, y = x, y(x))")) "false")
  (assert-equal (math-show (math-eval "ode_check(y' = 2*y, y = x^2, y(x))")) "false"))
