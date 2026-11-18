; RUBI.STUBS: девять утилит, бывших заглушками (lib/rubi/utils-s.lisp), — перенос по IntegrationUtilityFunctions.m.
; Истина/ложь у каждой сверена с текстом исходника (строки — в lib/rubi/utils-s.lisp и ниже).

(load "lib/rubi/fuzz.lisp")

; Ожившие правила: фаззер (lib/rubi/fuzz.lisp) строит пример по условию правила, движок делает шаг.
; До переноса NiceSqrtQ/FractionalPowerFactorQ были заглушками (на самом деле — даже с неверной арностью 2),
; и эти правила получали статус cond-unsat; теперь они срабатывают сами.
(define (rs-fuzz-status id)
  (rubi-integrate 1 'x)
  (let ((r (car (filter (lambda (q) (equal? (nth q 1) id)) rubi::*rubi-rules*))))
    (cadr (rubi::fuzz-rule r))))

(deftest "rubi-stubs/ожили правила с NiceSqrtQ: 1.2.1.2 #7, 1.2.1.4 #6 и #7"
  (assert-equal (rs-fuzz-status "Rubi 1.2.1.2 #7") 'self)
  (assert-equal (rs-fuzz-status "Rubi 1.2.1.4 #6") 'self)
  (assert-equal (rs-fuzz-status "Rubi 1.2.1.4 #7") 'self))

(deftest "rubi-stubs/интеграл через ожившее правило проходит проверку производной"
  ; (x+3)/((x+1)(x+2)): b^2-4ac = 1 — NiceSqrtQ истинно, разложение 1.2.1.2 #7
  (let ((old rubi::rubi-time-limit))
    (unwind-protect
      (begin (set! rubi::rubi-time-limit 60.0)
             (let ((r (rubi-integrate '(/ (+ 3 x) (+ 2 (* 3 x) (^ x 2))) 'x)))
               (assert-true (pair? r))
               (assert-true (int-check r '(/ (+ 3 x) (+ 2 (* 3 x) (^ x 2))) 'x))))
      (set! rubi::rubi-time-limit old))))

; FunctionOfQ[v,u,x] (IUF.m:4443-4483), FunctionOfExpnQ (4486-4516), FunctionOfSinQ/CosQ/TanQ (4572-4653)
(deftest "rubi-stubs/FunctionOfQ: степенная замена"
  (assert-true (rubi::rubi-functionofq '(^ x 2) '(+ 1 (* 3 (^ x 4))) 'x))
  (assert-true (rubi::rubi-functionofq '(^ x 2) '(+ (^ x 2) (^ x -2)) 'x))
  ; x^3 нечётная степень относительно x^2: u[[2]]/v[[2]] = 3/2 не целое — False
  (assert-equal (rubi::rubi-functionofq '(^ x 2) '(+ 1 (* 3 (^ x 3))) 'x) #f))

(deftest "rubi-stubs/FunctionOfQ: атом v и u без x"
  (assert-true (rubi::rubi-functionofq 'x '(sin x) 'x))       ; AtomQ[v] — True
  (assert-equal (rubi::rubi-functionofq '(sin x) 5 'x) #f)    ; FreeQ[u,x] — False
  (assert-equal (rubi::rubi-functionofq '(sin x) '(+ a b) 'x) #f))

(deftest "rubi-stubs/FunctionOfQ: тригонометрия"
  ; sec^2 x — функция от tan x (чётная степень, IUF.m:4644)
  (assert-true (rubi::rubi-functionofq '(tan x) '(^ (sec x) 2) 'x))
  ; cos 2x — функция от sin x (m чётно, Cos[m v] — функция Sin[v], IUF.m:4582)
  (assert-true (rubi::rubi-functionofq '(sin x) '(cos (* 2 x)) 'x))
  ; sin 2x — не функция от sin x, cos x
  (assert-equal (rubi::rubi-functionofq '(sin x) '(sin (* 2 x)) 'x) #f)
  (assert-equal (rubi::rubi-functionofq '(cos x) '(sin (* 2 x)) 'x) #f)
  ; cos^2 x — функция от cos x (чётная степень, IUF.m:4617-4619)
  (assert-true (rubi::rubi-functionofq '(cos x) '(+ 1 (^ (cos x) 2)) 'x))
  ; tan x не функция от cos x
  (assert-equal (rubi::rubi-functionofq '(cos x) '(tan x) 'x) #f))

(deftest "rubi-stubs/FunctionOfQ: гиперболические и PureFlag"
  (assert-true (rubi::rubi-functionofq '(tanh x) '(^ (sech x) 2) 'x))
  (assert-true (rubi::rubi-functionofq '(sinh x) '(+ 1 (^ (sinh x) 2)) 'x))
  ; PureFlag (IUF.m:4453): только Sin/Csc от v
  (assert-true (rubi::rubi-functionofq '(sin x) '(* 3 (sin x)) 'x #t))
  (assert-true (rubi::rubi-functionofq '(sin x) '(+ 1 (csc x)) 'x #t))
  (assert-equal (rubi::rubi-functionofq '(sin x) '(cos x) 'x #t) #f)
  (assert-equal (rubi::rubi-functionofq '(sin x) '(* 3 (sin (* 2 x))) 'x #t) #f))

; FunctionOfExponentialQ/FunctionOfExponential/FunctionOfExponentialFunction (IUF.m:4263-4350)
(deftest "rubi-stubs/FunctionOfExponentialQ: истина"
  (assert-true (rubi::rubi-function-of-exponential-q '(+ 1 (^ E (* 2 x))) 'x))
  ; 2^x + 4^x: основания 2 и 4 соизмеримы (Log[4]/Log[2] = 2)
  (assert-true (rubi::rubi-function-of-exponential-q '(+ (^ 2 x) (^ 4 x)) 'x))
  (assert-true (rubi::rubi-function-of-exponential-q '(* (^ E x) (^ E (* 3 x))) 'x)))

(deftest "rubi-stubs/FunctionOfExponentialQ: ложь"
  (assert-equal (rubi::rubi-function-of-exponential-q '(+ (^ 2 x) (^ 3 x)) 'x) #f)   ; Log[3]/Log[2] иррационально
  (assert-equal (rubi::rubi-function-of-exponential-q '(+ 1 x) 'x) #f)
  ; гиперболический синус — функция от E^x, но явной экспоненты нет ($exponFlag$ = False)
  (assert-equal (rubi::rubi-function-of-exponential-q '(sinh x) 'x) #f))

(deftest "rubi-stubs/FunctionOfExponential и FunctionOfExponentialFunction"
  (assert-equal (rubi::rubi-function-of-exponential '(+ 1 (^ E (* 2 x))) 'x) '(^ E (* 2 x)))
  ; меньшее целое основание берётся за базу
  (assert-equal (rubi::rubi-function-of-exponential '(+ (^ 2 x) (^ 4 x)) 'x) '(^ 2 x))
  (assert-equal (rubi::rubi-function-of-exponential '(* (^ E x) (^ E (* 3 x))) 'x) '(^ E x))
  ; u с заменой F^v на x
  (assert-equal (rubi::rubi-function-of-exponential-function '(+ 1 (^ E (* 2 x))) 'x) '(+ 1 x))
  (assert-equal (rubi::rubi-function-of-exponential-function '(+ (^ 2 x) (^ 4 x)) 'x) '(+ x (^ x 2)))
  ; Sinh[x] = (E^x - E^-x)/2 -> x/2 - 1/(2x)
  (assert-equal (rubi::rubi-function-of-exponential-function '(sinh x) 'x) '(+ (* -1/2 (^ x -1)) (* 1/2 x))))

; FunctionOfLinear (IUF.m:4169-4227)
(deftest "rubi-stubs/FunctionOfLinear: степень и функции линейного"
  (assert-equal (rubi::rubi-function-of-linear '(^ (+ 1 (* 2 x)) 3) 'x) '((^ x 3) 1 2))
  (assert-equal (rubi::rubi-function-of-linear '(sin (+ 1 (* 2 x))) 'x) '((sin x) 1 2))
  (assert-equal (rubi::rubi-function-of-linear '(log (+ a (* b x))) 'x) '((log x) a b)))

(deftest "rubi-stubs/FunctionOfLinear: общий линейный множитель и отказы"
  ; sin 2x + cos 4x = f(2x), f(x) = sin x + cos 2x; a = 0, b = 2
  (let ((r (rubi::rubi-function-of-linear '(+ (sin (* 2 x)) (cos (* 4 x))) 'x)))
    (assert-equal (cdr r) '(0 2))
    (assert-true (equal? (simplify (list '- (car r) '(+ (sin x) (cos (* 2 x))))) 0)))
  ; sin x + cos(x^2): аргумент нелинеен
  (assert-equal (rubi::rubi-function-of-linear '(+ (sin x) (cos (^ x 2))) 'x) #f)
  ; одночлен x^n перед функцией линейного (ветка MonomialFactor, IUF.m:4193): False
  (assert-equal (rubi::rubi-function-of-linear '(* x (sin (+ 1 x))) 'x) #f)
  ; f(x) без замены (a = 0, b = 1) — False (IUF.m:4171)
  (assert-equal (rubi::rubi-function-of-linear '(^ x 3) 'x) #f))

; PowerVariableExpn (IUF.m:4976-5006)
(deftest "rubi-stubs/PowerVariableExpn"
  ; m = 0: степени x^4 и x^6 — общий делитель 2, c = 1: {x^0*(sin x^2 + cos x^3), 2, 1}
  (let ((r (rubi::rubi-power-variable-expn '(+ (sin (^ x 4)) (cos (^ x 6))) 0 'x)))
    (assert-equal (rubi::rubi-part r 2) 2)
    (assert-equal (rubi::rubi-part r 3) 1)
    (assert-equal (rubi::rubi-part r 1) '(+ (cos (^ x 3)) (sin (^ x 2)))))
  ; (2x)^4: c = 2
  (assert-equal (rubi::rubi-power-variable-expn '(sin (^ (* 2 x) 4)) 0 'x) '((sin x) 4 2))
  ; GCD[1,2] = 1 — False; нет степени — False; m не целое — False
  (assert-equal (rubi::rubi-power-variable-expn '(sin (^ x 2)) 1 'x) #f)
  (assert-equal (rubi::rubi-power-variable-expn '(sin x) 0 'x) #f)
  (assert-equal (rubi::rubi-power-variable-expn '(sin (^ x 4)) 1/2 'x) #f))

; NiceSqrtQ, FractionalPowerFactorQ (IUF.m:651-669)
(deftest "rubi-stubs/NiceSqrtQ"
  (assert-true (rubi::rubi-nice-sqrt-q 4))
  (assert-equal (rubi::rubi-nice-sqrt-q -4) #f)       ; RationalQ: u>0
  (assert-equal (rubi::rubi-nice-sqrt-q 0) #f)
  (assert-true (rubi::rubi-nice-sqrt-q '(^ a 2)))     ; Rt[a^2,2] = a — без дробной степени
  (assert-true (rubi::rubi-nice-sqrt-q '(* 4 (^ a 2))))
  (assert-equal (rubi::rubi-nice-sqrt-q '(* -1 a c)) #f)   ; sqrt(-a c) — дробная степень
  (assert-equal (rubi::rubi-nice-sqrt-q '(* -1 (^ a 2))) #f))  ; sqrt(-a^2) = i a — комплексное

(deftest "rubi-stubs/FractionalPowerFactorQ"
  (assert-true (rubi::rubi-fractional-power-factor-q '(^ a 1/2)))
  (assert-true (rubi::rubi-fractional-power-factor-q '(* 3 (^ a 1/2))))
  (assert-true (rubi::rubi-fractional-power-factor-q '%i))            ; Head[u] === Complex
  (assert-true (rubi::rubi-fractional-power-factor-q '(* 2 %i)))
  (assert-equal (rubi::rubi-fractional-power-factor-q 3) #f)
  (assert-equal (rubi::rubi-fractional-power-factor-q '(* 3 a)) #f)
  (assert-equal (rubi::rubi-fractional-power-factor-q '(^ a 2)) #f)
  (assert-equal (rubi::rubi-fractional-power-factor-q '(+ a b)) #f))

; FunctionOfSquareRootOfQuadratic (IUF.m:5071-5128): подстановки Эйлера
(deftest "rubi-stubs/FunctionOfSquareRootOfQuadratic: подстановка Эйлера 2 (c > 0)"
  (let ((r (rubi::rubi-function-of-square-root-of-quadratic '(^ (+ 1 x (^ x 2)) -1/2) 'x)))
    (assert-equal (rubi::rubi-part r 3) 2)
    (assert-equal (rubi::rubi-part r 1) '(^ (+ 1 (* 2 x)) -1))
    (assert-equal (rubi::rubi-part r 2) '(+ x (^ (+ 1 x (^ x 2)) 1/2))))
  (let ((r (rubi::rubi-function-of-square-root-of-quadratic '(* (^ x -1) (^ (+ 1 x (^ x 2)) -1/2)) 'x)))
    (assert-equal (rubi::rubi-part r 3) 2)
    (assert-equal (rubi::rubi-part r 1) '(^ (+ -1 (^ x 2)) -1))))

(deftest "rubi-stubs/FunctionOfSquareRootOfQuadratic: отказы"
  ; линейный корень — не квадратный трёхчлен
  (assert-equal (rubi::rubi-function-of-square-root-of-quadratic '(^ (+ 1 (* 2 x)) 1/2) 'x) #f)
  ; x^m (a+b x^n)^p — форма, которую IUF.m:5072 исключает
  (assert-equal (rubi::rubi-function-of-square-root-of-quadratic '(* x (^ (+ 1 (^ x 2)) 1/2)) 'x) #f)
  ; нет корня из квадратного трёхчлена
  (assert-equal (rubi::rubi-function-of-square-root-of-quadratic '(sin x) 'x) #f)
  ; b^2 - 4ac = 0: полный квадрат
  (assert-equal (rubi::rubi-function-of-square-root-of-quadratic '(^ (+ 1 (* 2 x) (^ x 2)) 1/2) 'x) #f))
