; Шаг 21c: целочисленные примитивы, min/max, значения функций в точке (бывшие обходы), декларации-сессия

(deftest "min, max: числа любой точности"
  (assert-equal (min 3 1 2) 1)
  (assert-equal (max 3 1 2) 3)
  (assert-equal (min 5) 5)
  (assert-equal (max 1/2 1/3) 1/2)
  (assert-equal (min 1/2 1/3 1) 1/3)
  (assert-equal (max 100000000000000000000 1) 100000000000000000000)
  (assert-equal (min -1 -1/2) -1)
  ; float заражает результат, как в Scheme
  (assert-equal (max 1 2.5) 2.5)
  (assert-equal (max 3 2.5) 3.0)
  (assert-equal (min 1/2 0.75) 0.5))

(deftest "min, max: символы и пустой вызов — ошибка"
  (assert-error (min 'x 1))
  (assert-error (max 1 '(+ x 1)))
  (assert-error (min))
  (assert-error (max)))

(deftest "quotient, remainder, modulo"
  (assert-equal (quotient 7 2) 3)
  (assert-equal (quotient -7 2) -3)
  (assert-equal (quotient 7 -2) -3)
  (assert-equal (remainder 7 2) 1)
  (assert-equal (remainder -7 2) -1)
  (assert-equal (remainder 7 -2) 1)
  (assert-equal (modulo 7 2) 1)
  (assert-equal (modulo -7 2) 1)
  (assert-equal (modulo 7 -2) -1)
  (assert-equal (modulo -7 -2) -1)
  (assert-equal (modulo 6 3) 0)
  (assert-equal (modulo -6 3) 0)
  (assert-equal (mod 7 2) 1)
  (assert-error (quotient 1 0))
  (assert-error (remainder 1 0))
  (assert-error (modulo 1 0))
  (assert-error (quotient 1.5 2)))

(deftest "gcd, lcm"
  (assert-equal (gcd 12 18) 6)
  (assert-equal (gcd 12 18 8) 2)
  (assert-equal (gcd -12 18) 6)
  (assert-equal (gcd 0 5) 5)
  (assert-equal (gcd) 0)
  (assert-equal (lcm 4 6) 12)
  (assert-equal (lcm 4 6 10) 60)
  (assert-equal (lcm -4 6) 12)
  (assert-equal (lcm 0 5) 0)
  (assert-equal (lcm) 1)
  (assert-error (gcd 1.5 2))
  (assert-error (lcm 'x 2)))

; --- декларации — состояние сессии ---

(deftest "declarations: список текущих деклараций"
  (math-reset)
  (assert-equal (declarations) '())
  (declare 'pt-x reals)
  (declare 'pt-y integers positive)
  (assert-equal (declarations) (list (list 'pt-x reals) (list 'pt-y integers positive)))
  (assert-equal (declarations 'pt-x) (list reals))
  (undeclare 'pt-x)
  (assert-equal (declarations) (list (list 'pt-y integers positive)))
  (math-reset)
  (assert-equal (declarations) '()))

(deftest "declarations: assuming не оставляет следов в реестре"
  (math-reset)
  (assert-equal (assuming ((pt-a integers)) (declarations)) (list (list 'pt-a integers)))
  (assert-equal (declarations) '())
  (declare 'pt-a reals)
  (assuming ((pt-a positive)) (assert-equal (declarations 'pt-a) (list reals positive)))
  (assert-equal (declarations) (list (list 'pt-a reals)))
  (math-reset))

(deftest "math-reset сбрасывает декларации, но оставляет pi > 0"
  (declare 'pt-z reals)
  (declare 'pi reals)
  (math-reset)
  (assert-equal (declarations 'pt-z) '())
  (assert-equal (declarations) '())
  (assert-equal (declarations 'pi) (list positive))
  (assert-equal (simplify '(abs pi)) 'pi))

(deftest "решение x^2+1=0: с декларацией и после сброса"
  (math-reset)
  (assert-equal (solve '(= (+ (^ x 2) 1) 0) 'x) (set '%i '(* -1 %i)))
  (declare 'x reals)
  (assert-equal (solve '(= (+ (^ x 2) 1) 0) 'x) (set))
  (math-reset)
  (assert-equal (solve '(= (+ (^ x 2) 1) 0) 'x) (set '%i '(* -1 %i))))

(deftest "язык: x :∈ без домена снимает декларацию, clear() — все"
  (math-reset)
  (assert-equal (math-show (math-eval "solve(x^2 + 1 = 0, x)")) "{%i, -%i}")
  (math-eval "x :∈ ℝ")
  (assert-equal (math-show (math-eval "solve(x^2 + 1 = 0, x)")) "{}")
  (assert-equal (math-show (math-eval "x :∈")) "x")
  (assert-equal (declarations 'x) '())
  (assert-equal (math-show (math-eval "solve(x^2 + 1 = 0, x)")) "{%i, -%i}")
  (math-eval "x :∈ ℝ; y :∈ ℕ")
  (assert-equal (length (declarations)) 2)
  (math-eval "clear()")
  (assert-equal (declarations) '())
  (math-eval "x :∈ ℝ")
  (math-eval "undeclare(x)")
  (assert-equal (declarations) '())
  (math-reset))

(deftest "значения функций в точке считает simplify (бывшие int-fold, m-fold)"
  (assert-equal (simplify '(exp 0)) 1)
  (assert-equal (simplify '(+ (sin (* 1/2 pi)) (cos pi))) 0)
  (assert-equal (subst '(= x 0) '(+ (exp x) (cos x))) 2)
  (assert-equal (subst '(= x 1) '(^ (- 1 (^ x 2)) 1/2)) 0)
  (assert-equal (integrate '(cos x) 'x 0 '(* 1/2 pi)) 1)
  (assert-equal (integrate '(^ x 2) 'x 0 1) 1/3)
  (assert-equal (limit '(/ (sin x) x) 'x 0) 1)
  (assert-equal (limit '(* x (exp (* -1 x))) 'x 'inf) 0)
  (assert-equal (limit '(/ (exp x) (^ x 2)) 'x 'inf) 'inf))

; ---------- Шаг 21d: точечные пары ----------

(deftest "пары: cons не со списком, car/cdr, pair?, equal?"
  (let ((p (cons 1 2)))
    (assert-equal (car p) 1)
    (assert-equal (cdr p) 2)
    (assert-true (pair? p))
    (assert-true (not (list? p)))
    (assert-true (not (null? p)))
    (assert-true (equal? p (cons 1 2)))
    (assert-true (not (equal? p (cons 1 3))))
    (assert-equal (to-string p) "(1 . 2)"))
  ; cons со списком и nil — как раньше
  (assert-equal (cons 1 '(2 3)) '(1 2 3))
  (assert-equal (cons 1 '()) '(1))
  (assert-true (pair? '(1)))
  (assert-true (not (pair? '())))
  (assert-true (not (pair? 5))))

(deftest "пары: цепочка (a b . c), ридер и quote"
  (assert-equal (to-string (cons 1 (cons 2 3))) "(1 2 . 3)")
  (assert-equal (cdr (cdr '(1 2 . 3))) 3)
  (assert-equal (car (cdr '(1 2 . 3))) 2)
  (assert-equal '(a . (b c)) '(a b c))
  (assert-equal '(a . ()) '(a))
  (assert-true (equal? '(1 . 2) (cons 1 2)))
  (assert-error (car (cdr (cons 1 2)))))

(deftest "пары: assoc со списком пар и со списками"
  (assert-equal (assoc 'b '((a . 1) (b . 2) (c . 3))) (cons 'b 2))
  (assert-equal (cdr (assoc 'b '((a . 1) (b . 2)))) 2)
  (assert-equal (assoc 'c '((a 1) (b 2) (c 3 4))) '(c 3 4))
  (assert-equal (assoc 'z '((a . 1))) #f)
  (assert-equal (assoc 'a '()) #f)
  ; смесь, ключи — любые значения (equal?)
  (assert-equal (assoc "k" (list (cons 1 'one) (cons "k" 'str))) (cons "k" 'str)))

(deftest "пары: ведут себя как атомы в simplify, порядке и множествах"
  (let ((p (cons 1 2)))
    (assert-equal (simplify (list '+ p p)) (list '* 2 p))
    (assert-equal (simplify (list '* 3 p p)) (list '* 3 (list '^ p 2)))
    (assert-true (orderp (cons 1 2) (cons 1 3)))
    (assert-true (not (orderp (cons 1 3) (cons 1 2))))
    (assert-equal (card (set p (cons 1 2) (cons 3 4))) 2)
    (assert-equal (type-of p) 'pair)))

; Ключевые слова :имя самовычисляются
(deftest "ключевые слова: :foo самовычисляется, equal? с квотированным, печать, quote"
  (assert-equal :foo ':foo)
  (assert-true (equal? :a ':a))
  (assert-true (symbol? :a))
  (assert-equal (to-string :abc) ":abc")
  (assert-equal (quote :k) :k)
  (assert-equal (list :a :b) '(:a :b))
  (assert-true (member? :b '(:a :b)))
  (assert-true (not (equal? :a :b))))

(deftest "ключевые слова: define и set! — ошибка, module::имя работает"
  (assert-error (eval '(define :a 1)))
  (assert-error (eval '(define (:f x) x)))
  (assert-error (eval '(set! :a 1)))
  (assert-equal match::ac-default-limit 10000)
  (assert-equal (ac-match '(+ ?a ?b) '(+ x y)) '((?a x) (?b y))))

(deftest "ключевые слова: опции ac-match без кавычки и с кавычкой, with-step с опциями"
  (assert-equal (ac-match '(+ ?a ?b) '(+ x y) :where '(equal? ?a 'x)) '((?a x) (?b y)))
  (assert-equal (ac-match '(+ ?a ?b) '(+ x y) ':where '(equal? ?a 'y)) '((?a y) (?b x)))
  (assert-equal (ac-match '(* ?x) '(* 2 3) :limit 10 :identities #t) (ac-match '(* ?x) '(* 2 3) ':limit 10 ':identities #t))
  (assert-equal (with-step ('r "Т" 'e :comment "пояснение" :level 'detail :after (lambda (v) (* v 2))) 21) 21))
