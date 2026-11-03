; Lisp-тесты шага 19: символьное интегрирование (lib\integrate.lisp).
; Главный инвариант: КАЖДЫЙ тест интегрирования проверяется дифференцированием (int-check: F' − e = 0
; точно через simplify/together, иначе численно в нескольких точках). Форма ответа проверяется
; только в «витринных» тестах.

(define (itest-unevaluated? r) (and (list? r) (not (null? r)) (equal? (car r) 'integrate)))

; (chk e) — интеграл вычислен (не невычисленная форма) и производная первообразной равна e
(define (chk e)
  (let ((r (integrate e 'x)))
    (if (itest-unevaluated? r)
        (error (string-append "не вычислен интеграл " (math-print e))))
    ; ответ с разбором случаев по параметру — piecewise: проверяется его сертификатом (покрытие + каждая ветвь)
    (if (if (and (list? r) (equal? (car r) 'piecewise)) (equal? (int-piecewise-check r e 'x) 'ok) (int-check r e 'x))
        #t
        (error (string-append "производная первообразной " (math-print r) " не равна " (math-print e))))))

(define (chk-all es) (every? (lambda (e) (chk e)) es))

; ---------- таблица и линейная подстановка ----------

(deftest "таблица: степени"
  (assert-true (chk-all '((^ x 2) (^ x 5) (^ x -2) (^ x 1/2) (^ x a) (^ x -1) x 5 a))))

(deftest "таблица: линейный аргумент u = a·x + b"
  (assert-true (chk-all '((sin (+ (* 2 x) 1)) (cos (+ (* 3 x) b)) (exp (* -1 x)) (exp (* 2 x))
                          (^ (+ (* 2 x) 1) 3) (^ (+ (* 2 x) 1) -2) (/ 1 (+ (* 3 x) 2)) (log (* 2 x))
                          (^ 3 (* 2 x)) (^ 2 x)))))

(deftest "таблица: тригонометрия и гиперболические"
  (assert-true (chk-all '((tan x) (cot x) (sec x) (csc x) (^ (cos x) -2) (^ (sin x) -2)
                          (sinh x) (cosh x) (tanh x) (^ (cosh x) -2)))))

(deftest "таблица: обратные тригонометрические и 1/(c+u²)"
  (assert-true (chk-all '((atan x) (asin x) (acos (* 2 x)) (/ 1 (+ 1 (^ x 2))) (/ 1 (+ 4 (^ x 2)))
                          (/ 1 (+ (^ a 2) (^ x 2))) (/ 1 (sqrt (- 1 (^ x 2)))) (/ 1 (sqrt (- 4 (^ x 2))))
                          (/ 1 (sqrt (- (^ a 2) (^ x 2)))) (/ 1 (sqrt (+ 1 (^ x 2)))) (/ 1 (sqrt (- (^ x 2) 1)))))))

(deftest "линейность: суммы и множители без x"
  (assert-true (chk-all '((+ (^ x 2) (* 3 x) 5) (* 3 (sin x)) (* a x) (+ (* a (^ x 2)) (* b x) c)
                          (- (* 3 x) (/ 2 x)) (+ (log x) (exp x)) (+ (^ x 3) (* 2 (cos x)) 7)
                          (* a b (exp (* 2 x)))))))

; ---------- «производная делит» ----------

(deftest "подстановка: примеры из постановки"
  (assert-true (chk-all '((* x (exp (^ x 2))) (* (sin x) (cos x)) (/ (* 2 x) (+ (^ x 2) 1))
                          (/ (log x) x) (* (cos x) (exp (sin x))) (/ x (sqrt (- 1 (^ x 2))))))))

(deftest "подстановка: прочие"
  (assert-true (chk-all '((* (^ x 2) (exp (^ x 3))) (/ (exp x) (+ 1 (exp x))) (/ 1 (* x (log x)))
                          (* x (sin (^ x 2))) (/ (+ (* 2 x) 3) (+ (^ x 2) (* 3 x) 1))
                          (/ (cos x) (+ 1 (^ (sin x) 2))) (* (exp x) (sin (exp x))) (/ (^ (log x) 2) x)
                          (* x (sqrt (+ (^ x 2) 1))) (* x (^ (+ (^ x 2) 1) 3)) (/ (sin x) (^ (cos x) 2))
                          (/ (+ (* 3 (^ x 2)) 1) (+ (^ x 3) x)) (* (cos x) (sqrt (sin x)))
                          (* (sin x) (sin x) (cos x)) (* 3 x (exp (* x x)))))))

(deftest "приведение входа: exp(2x), exp(x)·exp(2x), (exp x)²"
  (assert-true (chk-all '((exp (* 2 x)) (* (exp x) (exp (* 2 x))) (^ (exp x) 2) (/ (exp (* 2 x)) (+ 1 (exp (* 2 x))))))))

; ---------- рациональные функции ----------

(deftest "рациональные: простые дроби (линейные множители)"
  (assert-true (chk-all '((/ 1 (- (^ x 2) 1)) (/ (+ (^ x 3) 1) (- (^ x 2) 1))
                          (/ 1 (* (^ (- x 1) 2) (+ x 2))) (/ 1 (* x (+ x 1))) (/ 1 (- x a))
                          (/ 1 (- (^ x 4) 1))))))

(deftest "рациональные: неприводимый квадратный множитель, k = 1"
  (assert-true (chk-all '((/ 1 (+ (^ x 2) 1)) (/ 1 (+ (^ x 2) (* 2 x) 5)) (/ x (+ (^ x 2) x 1))
                          (/ 1 (+ (^ x 3) 1)) (/ 1 (+ (* 2 (^ x 2)) (* 3 x) 4))
                          (/ (+ x 1) (+ (* 4 (^ x 2)) 4)) (/ (^ x 5) (+ (^ x 2) 1))))))

(deftest "рациональные: кратные квадратные множители (формула понижения)"
  (assert-true (chk-all '((/ 1 (^ (+ (^ x 2) 1) 2)) (/ 1 (^ (+ (^ x 2) 1) 3))
                          (/ (+ (* 3 x) 1) (^ (+ (^ x 2) (* 2 x) 3) 2))))))

(deftest "рациональные: вещественные иррациональные корни знаменателя"
  (assert-true (chk-all '((/ 1 (- (^ x 2) 2)) (/ 1 (- (^ x 2) 3))))))

(deftest "рациональные: многочлены (произведения раскрываются)"
  (assert-true (chk-all '((* (+ x 1) (+ x 2) (+ x 3)) (^ (+ x 1) 4) (* (^ x 2) (- x 1))))))

; Шаг 21h: раньше здесь ожидалась невычисленная форма («Ротштейн–Трагер вне рамок»); теперь стратегия int-rational-lrt
; (Эрмит + ЛРТ + сумма по корням) вычисляет любую рациональную функцию — ожидания заменены на проверку дифференцированием
(deftest "рациональные: неприводимый множитель степени ≥ 3 — сумма по корням (шаг 21h)"
  (assert-true (chk '(/ 1 (- (^ x 3) 2))))
  (assert-true (chk '(/ (+ (^ x 2) 1) (+ (^ x 4) 1))))
  ; INT.RS: корни x³−2 в радикалах — вещественная форма без root-sum
  (assert-true (not (contains-sym? (integrate '(/ 1 (- (^ x 3) 2)) 'x) 'root-sum)))
  ; если числитель — производная знаменателя, получается логарифм
  (assert-true (chk '(/ (^ x 2) (- (^ x 3) 2)))))

(deftest "рациональные: параметры в разных линейных множителях (шаг 21h)"
  (assert-true (chk '(/ 1 (* (- x a) (- x b)))))
  (assert-equal (integrate '(/ 1 (* (- x a) (- x b))) 'x)
                '(+ (* (^ (+ a (* -1 b)) -1) (log (+ (* -1 a) x))) (* -1 (^ (+ a (* -1 b)) -1) (log (+ (* -1 b) x))))))

(deftest "форма: рациональные"
  (assert-equal (integrate '(/ 1 (- (^ x 2) 1)) 'x) '(+ (* 1/2 (log (+ -1 x))) (* -1/2 (log (+ 1 x)))))
  (assert-equal (integrate '(/ 1 (+ (^ x 2) 1)) 'x) '(atan x))
  (assert-equal (integrate '(/ 1 (+ (^ x 2) (* 2 x) 5)) 'x) '(* 1/2 (atan (* 1/2 (+ 1 x)))))
  (assert-equal (integrate '(/ (+ (^ x 3) 1) (- (^ x 2) 1)) 'x) '(+ (* 1/2 (^ x 2)) (log (+ -1 x)))))

(deftest "определённые: рациональные"
  (assert-equal (integrate '(/ 1 (+ (^ x 2) 1)) 'x -1 1) '(* 1/2 pi))
  ; на [2, 3] знаменатель не обращается в 0: ½·ln(3/2) = 0.2027...
  (let ((r (integrate '(/ 1 (- (^ x 2) 1)) 'x 2 3)))
    (assert-true (< (abs (- (eval-num r) 0.2027325540540822)) 0.000000001)))
  ; корень знаменателя внутри отрезка — невычисленная форма
  (assert-equal (integrate '(/ 1 (- (^ x 2) 1)) 'x 0 2) '(integrate (^ (+ -1 (^ x 2)) -1) x 0 2)))

; ---------- по частям (LIATE) ----------

(deftest "по частям: многочлен × exp/sin/cos/log"
  (assert-true (chk-all '((* x (exp x)) (* (^ x 2) (sin x)) (* x (log x)) (* (^ x 3) (exp (* 2 x)))
                          (* x (cos (* 2 x))) (* (^ x 2) (log x)) (* (+ x 1) (exp x)) (* (^ x 5) (exp x))
                          (* (^ x 7) (sin x))))))

(deftest "по частям: log и обратные тригонометрические"
  (assert-true (chk-all '((log x) (atan x) (^ (log x) 2) (log (+ (^ x 2) 1)) (* x (atan x))
                          (* x (exp x) (sin x))))))

(deftest "по частям: циклический случай (exp·sin, exp·cos)"
  (assert-true (chk-all '((* (exp x) (sin x)) (* (exp x) (cos x)) (* (exp (* 2 x)) (sin (* 3 x)))
                          (* (exp (* -1 x)) (cos (* 2 x)))))))

; ---------- степени тригонометрических функций ----------

(deftest "тригонометрия: степени sin и cos"
  (assert-true (chk-all '((^ (sin x) 2) (^ (cos x) 2) (^ (cos x) 3) (^ (sin x) 4) (^ (sin x) 5)
                          (* (^ (sin x) 2) (^ (cos x) 2)) (* (^ (sin x) 3) (^ (cos x) 2))
                          (* (^ (sin x) 2) (^ (cos x) 4)) (* (sin x) (^ (cos x) 4))))))

(deftest "тригонометрия: tan, sec, csc, cot в степенях"
  (assert-true (chk-all '((^ (tan x) 2) (^ (tan x) 3) (^ (tan x) 4) (^ (sec x) 3) (^ (sec x) 4)
                          (^ (csc x) 2) (^ (csc x) 3) (^ (cot x) 2) (* (^ (tan x) 2) (^ (sec x) 2))
                          (/ (^ (sin x) 2) (cos x))))))

(deftest "тригонометрия: линейные аргументы и произведения разных аргументов"
  (assert-true (chk-all '((^ (sin (* 2 x)) 2) (* (sin (* 2 x)) (cos (* 2 x))) (^ (cos (+ (* 3 x) 1)) 3)
                          (* (sin x) (cos (* 2 x))) (* (sin (* 3 x)) (sin (* 5 x))) (* (cos x) (cos (* 4 x)))))))

; ---------- корни квадратного трёхчлена ----------

(deftest "корни: 1/sqrt(ax²+bx+c)"
  (assert-true (chk-all '((/ 1 (sqrt (+ (^ x 2) (* 2 x) 5))) (/ 1 (sqrt (+ (* 2 (^ x 2)) (* 3 x) 1)))
                          (/ 1 (sqrt (- 3 (* 2 x) (^ x 2)))) (/ 1 (sqrt (- 1 (* 2 (^ x 2)))))))))

(deftest "корни: sqrt(ax²+bx+c) и (Bx+C)/sqrt(...)"
  (assert-true (chk-all '((sqrt (- 1 (^ x 2))) (sqrt (- (^ a 2) (^ x 2))) (sqrt (+ (^ x 2) 1))
                          (sqrt (+ (^ x 2) (* 2 x) 5)) (sqrt (- 3 (* 2 x) (^ x 2)))
                          (/ x (sqrt (+ (^ x 2) (* 2 x) 5))) (/ (+ x 1) (sqrt (- 3 (* 2 x) (^ x 2))))
                          (/ (+ (* 3 x) 2) (sqrt (+ (* 2 (^ x 2)) x 1)))))))

; ---------- раскрытие, смешанные случаи ----------

(deftest "раскрытие скобок и подстановка с exp(n·u)"
  (assert-true (chk-all '((^ (+ (sin x) (cos x)) 2) (* (sin x) (+ 1 (cos x))) (/ (exp x) (+ 1 (exp (* 2 x))))
                          (/ (^ x 3) (+ 1 (^ x 4)))))))

; ---------- витринные: точная форма ----------

(deftest "форма: степени и линейная подстановка"
  (assert-equal (integrate '(^ x 2) 'x) '(* 1/3 (^ x 3)))
  (assert-equal (integrate 'x 'x) '(* 1/2 (^ x 2)))
  (assert-equal (integrate 5 'x) '(* 5 x))
  (assert-equal (integrate '(+ (^ x 2) (* 3 x) 5) 'x) '(+ (* 5 x) (* 3/2 (^ x 2)) (* 1/3 (^ x 3))))
  (assert-equal (integrate '(sin (+ (* 2 x) 1)) 'x) '(* -1/2 (cos (+ 1 (* 2 x)))))
  (assert-equal (integrate '(/ 1 (+ (* 3 x) 2)) 'x) '(* 1/3 (log (+ 2 (* 3 x)))))
  (assert-equal (integrate '(exp (* 3 x)) 'x) '(* 1/3 (exp (* 3 x)))))

(deftest "форма: ∫1/x = log x (без модуля), log, 2^x"
  (assert-equal (integrate '(/ 1 x) 'x) '(log x))
  (assert-equal (integrate '(^ x -1) 'x) '(log x))
  (assert-equal (integrate '(log x) 'x) '(+ (* -1 x) (* x (log x))))
  (assert-equal (integrate '(^ 2 x) 'x) '(* (^ 2 x) (^ (log 2) -1))))

(deftest "форма: подстановка"
  (assert-equal (integrate '(* x (exp (^ x 2))) 'x) '(* 1/2 (exp (^ x 2))))
  (assert-equal (integrate '(/ (* 2 x) (+ (^ x 2) 1)) 'x) '(log (+ 1 (^ x 2))))
  (assert-equal (integrate '(/ (log x) x) 'x) '(* 1/2 (^ (log x) 2)))
  (assert-equal (integrate '(* (cos x) (exp (sin x))) 'x) '(exp (sin x))))

(deftest "форма: atan, asin, 1/(1+x²)"
  (assert-equal (integrate '(/ 1 (+ 1 (^ x 2))) 'x) '(atan x))
  (assert-equal (integrate '(/ 1 (sqrt (- 1 (^ x 2)))) 'x) '(asin x))
  (assert-equal (integrate '(tan x) 'x) '(* -1 (log (cos x)))))

(deftest "форма: по частям"
  (assert-equal (integrate '(* x (exp x)) 'x) '(+ (* x (exp x)) (* -1 (exp x))))
  (assert-equal (integrate '(* x (log x)) 'x) '(+ (* -1/4 (^ x 2)) (* 1/2 (^ x 2) (log x))))
  (assert-equal (integrate '(atan x) 'x) '(+ (* x (atan x)) (* -1/2 (log (+ 1 (^ x 2))))))
  (assert-equal (integrate '(* (exp x) (sin x)) 'x) '(+ (* -1/2 (cos x) (exp x)) (* 1/2 (exp x) (sin x))))
  (assert-equal (integrate '(* (exp x) (cos x)) 'x) '(* 1/2 (+ (* (cos x) (exp x)) (* (exp x) (sin x))))))

(deftest "форма: тригонометрия и корни"
  (assert-equal (integrate '(^ (sin x) 2) 'x) '(+ (* 1/2 x) (* -1/2 (cos x) (sin x))))
  (assert-equal (integrate '(^ (cos x) 3) 'x) '(+ (* 1/3 (^ (cos x) 2) (sin x)) (* 2/3 (sin x))))
  (assert-equal (integrate '(^ (tan x) 2) 'x) '(+ (* -1 x) (* (^ (cos x) -1) (sin x))))
  (assert-equal (integrate '(sqrt (- 1 (^ x 2))) 'x) '(* 1/2 (+ (* x (^ (+ 1 (* -1 (^ x 2))) 1/2)) (asin x))))
  (assert-equal (integrate '(/ 1 (sqrt (+ (^ x 2) (* 2 x) 5))) 'x) '(log (+ 1 x (^ (+ 5 (* 2 x) (^ x 2)) 1/2)))))

(deftest "форма: sqrt(a² − x²) — параметр a считается положительным"
  (assert-equal (integrate '(sqrt (- (^ a 2) (^ x 2))) 'x)
                '(* 1/2 (+ (* (^ a 2) (asin (* (^ a -1) x))) (* x (^ (+ (^ a 2) (* -1 (^ x 2))) 1/2))))))

(deftest "определённые: по частям, тригонометрия, корни"
  (assert-equal (integrate '(* x (exp x)) 'x 0 1) 1)
  (assert-equal (integrate '(* x (sin x)) 'x 0 'pi) 'pi)
  (assert-equal (integrate '(^ (sin x) 2) 'x 0 'pi) '(* 1/2 pi))
  (assert-equal (integrate '(sqrt (- 1 (^ x 2))) 'x 0 1) '(* 1/4 pi))
  (assert-equal (integrate '(/ 1 (sqrt (- 1 (^ x 2)))) 'x -1 1) 'pi)
  (assert-equal (integrate '(log x) 'x 1 '(exp 1)) 1)
  (assert-equal (integrate '(* (exp x) (sin x)) 'x 0 'pi) '(+ 1/2 (* 1/2 (exp pi)))))

(deftest "невычисленные: вне рамок эвристик"
  ; тригонометрическая подстановка, спецфункции, модуль (Вейерштрасс — с 21k″ в Рише: 1/(2 + cos x) берётся)
  (assert-equal (integrate '(* x (asin x)) 'x) '(integrate (* x (asin x)) x))
  (assert-true (not (contains-sym? (integrate '(/ 1 (+ 2 (cos x))) 'x) 'integrate)))
  (assert-equal (integrate '(/ (exp x) x) 'x) '(integrate (* (^ x -1) (exp x)) x))
  (assert-equal (integrate '(abs x) 'x) '(integrate (abs x) x)))

; ---------- невычисленные формы ----------

(deftest "невычисленная форма вместо ошибки"
  (assert-equal (integrate '(exp (^ x 2)) 'x) '(integrate (exp (^ x 2)) x))
  (assert-equal (integrate '(/ (sin x) x) 'x) '(integrate (* (^ x -1) (sin x)) x))
  (assert-equal (integrate '(/ 1 (log x)) 'x) '(integrate (^ (log x) -1) x))
  (assert-equal (integrate '(sin (^ x 2)) 'x) '(integrate (sin (^ x 2)) x))
  (assert-equal (integrate '(^ x x) 'x) '(integrate (^ x x) x)))

; ---------- определённые интегралы ----------

(deftest "определённые: числа и π"
  (assert-equal (integrate '(^ x 2) 'x 0 1) 1/3)
  (assert-equal (integrate '(sin x) 'x 0 'pi) 2)
  (assert-equal (integrate '(/ 1 x) 'x 1 '(exp 1)) 1)
  (assert-equal (integrate '(/ 1 (+ 1 (^ x 2))) 'x 0 1) '(* 1/4 pi))
  (assert-equal (integrate '(exp x) 'x 0 1) '(+ -1 (exp 1)))
  (assert-equal (integrate '(log x) 'x 0 1) -1))

(deftest "определённые: символьные пределы"
  (assert-equal (integrate '(^ x 2) 'x 'a 'b) '(+ (* -1/3 (^ a 3)) (* 1/3 (^ b 3))))
  (assert-equal (integrate 'x 'x 0 'b) '(* 1/2 (^ b 2))))

(deftest "определённые: особенность в [a, b] — невычисленная форма"
  (assert-equal (integrate '(/ 1 x) 'x -1 1) '(integrate (^ x -1) x -1 1))
  (assert-equal (integrate '(/ 1 x) 'x 0 1) '(integrate (^ x -1) x 0 1))
  (assert-equal (integrate '(/ 1 (- (^ x 2) 1)) 'x 0 2) '(integrate (^ (+ -1 (^ x 2)) -1) x 0 2)))

(deftest "определённые: невычислимый интеграл — невычисленная форма"
  (assert-equal (integrate '(exp (^ x 2)) 'x 0 1) '(integrate (exp (^ x 2)) x 0 1)))

; ---------- порядок аргументов, объекты ----------

(deftest "устаревший порядок аргументов (integrate 'x выражение)"
  (assert-equal (integrate 'x '(^ x 2)) '(* 1/3 (^ x 3)))
  (assert-equal (integrate 'a 'x) '(* a x)))

(deftest "тензор: покомпонентно, невычисленные компоненты"
  (assert-equal (tensor->list (integrate (tensor '(x a)) 'x)) '((* 1/2 (^ x 2)) (* a x)))
  (assert-equal (tensor->list (integrate (tensor '((* 2 x) (exp (^ x 2)))) 'x))
                '((^ x 2) (integrate (exp (^ x 2)) x))))

(deftest "своя таблица: (int-rule ...) расширяет таблицу"
  (int-rule '(foo ?u) '(* 3 ?u))
  (assert-equal (integrate '(foo x) 'x) '(* 3 x))
  (assert-equal (integrate '(foo (* 2 x)) 'x) '(* 3 x)))

; ---------- несобственные интегралы (Шаг 20) ----------

(deftest "несобственные: бесконечные пределы"
  (assert-equal (integrate '(exp (* -1 x)) 'x 0 'inf) 1)
  (assert-equal (integrate '(/ 1 (^ x 2)) 'x 1 'inf) 1)
  (assert-equal (integrate '(/ 1 x) 'x 1 'inf) 'inf)
  (assert-equal (integrate '(/ 1 (+ 1 (^ x 2))) 'x '-inf 'inf) 'pi)
  (assert-equal (integrate '(exp x) 'x '-inf 0) 1)
  (assert-equal (integrate '(* (^ x 2) (exp (* -1 x))) 'x 0 'inf) 2)
  (assert-equal (integrate '(/ 1 (^ x 2)) 'x 'inf 1) -1)
  (assert-equal (integrate '(/ x (+ 1 (^ x 2))) 'x 0 'inf) 'inf))

(deftest "несобственные: особенность в конце отрезка — предел первообразной"
  (assert-equal (integrate '(/ 1 (sqrt x)) 'x 0 1) 2)
  (assert-equal (integrate '(log x) 'x 0 1) -1)
  (assert-equal (integrate '(/ 1 (sqrt (- 1 (^ x 2)))) 'x -1 1) 'pi))

(deftest "несобственные: невычисленная форма"
  (assert-equal (integrate '(sin x) 'x 0 'inf) '(integrate (sin x) x 0 inf))
  ; DI.3: гауссов интеграл теперь берёт модуль definite (раньше — невычисленная форма)
  (assert-equal (integrate '(exp (* -1 (^ x 2))) 'x 0 'inf) '(* 1/2 (^ pi 1/2)))
  ; расходящийся на конечном отрезке и особенность внутри — невычисленные
  (assert-equal (integrate '(/ 1 (^ x 2)) 'x 0 1) '(integrate (^ x -2) x 0 1))
  (assert-equal (integrate '(/ 1 (^ x 2)) 'x -1 1) '(integrate (^ x -2) x -1 1)))

; ---------- шаг AC.4: таблица на AC-сопоставлении (вторая попытка после int-table-try) ----------

(deftest "AC.4: (c + k·u²)^(-3/2) — сумма параметров, коэффициент, c − u²"
  (assert-true (chk-all '((^ (+ 1 (^ x 2)) -3/2) (^ (+ a b (^ x 2)) -3/2) (^ (+ 4 (* -1 (^ x 2))) -3/2)
                          (^ (+ a b (* -1 (^ x 2))) -3/2) (^ (+ 1 (* 4 (^ x 2))) -3/2) (^ (+ a b (* 3 (^ x 2))) -3/2)
                          (* 5 (^ (+ 1 (^ x 2)) -3/2)) (^ (+ 1 (^ (+ x 1) 2)) -3/2) (^ (+ (^ x 2) (^ y 2)) -3/2))))
  (assert-equal (integrate '(^ (+ 1 (^ x 2)) -3/2) 'x) '(* x (^ (+ 1 (^ x 2)) -1/2)))
  (assert-equal (integrate '(^ (+ a b (^ x 2)) -3/2) 'x) '(* x (^ (+ a b) -1) (^ (+ a b (^ x 2)) -1/2))))

(deftest "AC.4: (c + u²)^(3/2) и (c − u²)^(3/2)"
  (assert-true (chk-all '((^ (+ 1 (^ x 2)) 3/2) (^ (+ a b (^ x 2)) 3/2) (^ (+ 4 (* -1 (^ x 2))) 3/2)
                          (^ (+ 1 (^ (+ (* 2 x) 1) 2)) 3/2)))))

(deftest "AC.4: новые строки обычной таблицы — sech, csch, csch²"
  (assert-true (chk-all '((^ (cosh x) -1) (^ (sinh x) -1) (^ (sinh x) -2) (^ (sinh (* 2 x)) -1)
                          (* 3 (^ (cosh (+ (* 2 x) 1)) -1)))))
  (assert-equal (integrate '(^ (cosh x) -1) 'x) '(atan (sinh x))))

(deftest "AC.4: условия отсекают зависимые «константы» и нулевые c, k"
  ; c зависит от x — строка не применяется (и кандидат отбрасывается на каждом разборе)
  (assert-true (itest-unevaluated? (integrate '(^ (+ (sin x) (^ x 2)) -3/2) 'x)))
  (assert-true (itest-unevaluated? (integrate '(^ (+ (* x y) (^ x 2) (^ x 3)) -3/2) 'x)))
  ; u нелинеен: (x³ + 1)^(-3/2) — не строка (u² = x³ невозможно)
  (assert-true (itest-unevaluated? (integrate '(^ (+ 1 (^ x 3)) -3/2) 'x)))
  ; параметр в c: ответ записывает условие c > 0 для (c − u²)^(3/2) с нечисловым c
  (let ((r (capture-conditions (lambda () (integrate '(^ (+ a b (* -1 (^ x 2))) 3/2) 'x)))))
    (assert-true (not (itest-unevaluated? (car r))))
    (assert-true (member? '(> (+ a b) 0) (map car (cadr r))))))

(deftest "AC.4: AC-вариант покрывает все перестановки int-variants"
  (assert-true (every? (lambda (row)
                         (every? (lambda (v) (if (ac-match (car row) v) #t #f))
                                 (integrate::int-variants (car row))))
                       integrate::int-base-rows)))

(deftest "AC.4: прежние ответы таблицы не меняются (AC-попытка — только после неудачи)"
  (assert-equal (integrate '(^ (+ x 1) 1) 'x) '(+ x (* 1/2 (^ x 2))))
  (assert-equal (integrate '(/ 1 (+ 4 (^ x 2))) 'x) '(* 1/2 (atan (* 1/2 x))))
  (assert-equal (integrate '(^ (cosh x) -2) 'x) '(tanh x)))

; ---------- A1.4: вещественная форма root-sum (расширение Q(sqrt d)) ----------

(deftest "A1.4: 1/(x^4+1) — вещественная форма (log + atan с sqrt(2))"
  (let ((r (integrate '(/ 1 (+ 1 (^ x 4))) 'x)))
    (assert-true (not (contains-sym? r 'root-sum)))
    (assert-true (not (contains-sym? r '%i)))
    (assert-true (contains-sym? r 'atan))
    (assert-true (chk '(/ 1 (+ 1 (^ x 4)))))))

(deftest "A1.4: 1/(x^6+1) — вещественная форма (sqrt(3))"
  (let ((r (integrate '(/ 1 (+ 1 (^ x 6))) 'x)))
    (assert-true (not (contains-sym? r 'root-sum)))
    (assert-true (not (contains-sym? r '%i)))
    (assert-true (chk '(/ 1 (+ 1 (^ x 6)))))))

(deftest "A1.4: 1/(x^2-2) — линейные множители над Q(sqrt 2), вещественные log"
  (let ((r (integrate '(/ 1 (- (^ x 2) 2)) 'x)))
    (assert-true (not (contains-sym? r 'root-sum)))
    (assert-true (not (contains-sym? r '%i)))))

(deftest "A1.4/INT.RS: кубическая резольвента (x^3-2) — раскрыта в радикалах (вне Q(sqrt d) — отдельный путь INT.RS)"
  (let ((r (integrate '(/ 1 (- (^ x 3) 2)) 'x)))
    (assert-true (not (contains-sym? r 'root-sum)))
    (assert-true (not (contains-sym? r '%i)))))

(deftest "A1.4: параметрический знаменатель (a+x^4) — root-sum остаётся (разложение зависит от знака a)"
  (assert-true (contains-sym? (integrate '(/ 1 (+ a (^ x 4))) 'x) 'root-sum)))

; ---------- INT.TQ: дробные степени tan/cot ----------
; Оракул: |F'(x) − f(x)| < 1e-9 в точках области tan x > 0, F вещественна (eval-num — число).
(define (tq-num e v) (eval-num (subst (list 'x v) e)))
(define (tq-oracle? f F)
  (let ((dF (diff 'x F)))
    (every? (lambda (v)
              (let ((a (tq-num dF v)) (b (tq-num f v)))
                (and (number? a) (number? b) (< (abs (- a b)) 1e-9))))
            '(0.2 0.5 0.8 1.1 1.4))))
(define (tq-check s)
  (let* ((f (math-eval s)) (F (integrate f 'x)))
    (and (not (itest-unevaluated? F))
         (not (contains-sym? F 'integrate))
         (tq-oracle? f F))))

(deftest "INT.TQ: sqrt(tan x), 1/sqrt(tan x), sqrt(cot x), tan(x)^(1/3)"
  (assert-true (tq-check "sqrt(tan(x))"))
  (assert-true (tq-check "1/sqrt(tan(x))"))
  (assert-true (tq-check "sqrt(cot(x))"))
  (assert-true (tq-check "tan(x)^(1/3)")))

(deftest "INT.TQ: sqrt(tan x)/cos^2 x, sqrt(tan x)*tan x, (1+tan x)/sqrt(tan x), tan(x)^(2/3)"
  (assert-true (tq-check "sqrt(tan(x))/cos(x)^2"))
  (assert-true (tq-check "sqrt(tan(x))*tan(x)"))
  (assert-true (tq-check "(1+tan(x))/sqrt(tan(x))"))
  (assert-true (tq-check "tan(x)^(2/3)")))

(deftest "INT.TQ: sqrt(tan x)/cos^2 x = 2/3·tan^(3/2) — без log и atan"
  (let ((r (integrate (math-eval "sqrt(tan(x))/cos(x)^2") 'x)))
    (assert-true (not (contains-sym? r 'log)))
    (assert-true (not (contains-sym? r 'atan)))))

(deftest "INT.TQ: не тот класс — sqrt(sin x), sqrt(tan x)/sin x, sqrt(tan x)*sin x — не ложная формула"
  (assert-true (itest-unevaluated? (integrate '(sqrt (sin x)) 'x)))
  (assert-true (itest-unevaluated? (integrate (math-eval "sqrt(tan(x))/sin(x)") 'x)))
  (assert-true (itest-unevaluated? (integrate (math-eval "sqrt(tan(x))*sin(x)") 'x))))

; ---------- sech, csch, coth: приведение к cosh/sinh на входе интегратора ----------

(deftest "sech/csch/coth: табличные и по частям — ответ проходит проверку производной"
  (assert-true (tq-check "sech(x)^2"))
  (assert-true (tq-check "sech(x)"))
  (assert-true (tq-check "csch(x)"))
  (assert-true (tq-check "coth(x)"))
  (assert-true (tq-check "csch(x)^2"))
  (assert-true (tq-check "x*sech(x)^2"))
  (assert-true (tq-check "x*csch(x)^2"))
  (assert-true (tq-check "cosh(x)*csch(x)^(3/2)"))
  (assert-true (tq-check "sinh(x)*sech(x)^(5/2)")))
