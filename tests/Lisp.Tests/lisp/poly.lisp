; Lisp-тесты многочленов и рациональных функций (Шаг 17): together, cancel, numer/denom, apart,
; poly-gcd/lcm, poly-quotient/remainder, coeff/degree/variables, sqfree, factor, ядра.
; Где форма неочевидна — проверяются инварианты (together(apart e) = together e, expand(factor e) = expand e).

; --- together ---

(deftest "together: 1/x + 1/y"
  (assert-equal (together '(+ (/ 1 x) (/ 1 y)))
                '(* (^ x -1) (^ y -1) (+ x y))))

(deftest "together: общий знаменатель — НОК, а не произведение"
  (assert-equal (numer '(+ (/ 1 (- x 1)) (/ 1 (+ x 1)))) '(* 2 x))
  (assert-equal (denom '(+ (/ 1 (- x 1)) (/ 1 (+ x 1)))) '(+ -1 (^ x 2))))

(deftest "together: сокращение на НОД"
  (assert-equal (together '(/ (- (^ x 2) 1) (- x 1))) '(+ 1 x))
  (assert-equal (together '(+ (/ x (+ x 1)) (/ 1 (+ x 1)))) 1))

(deftest "together: рациональные коэффициенты — целые в числителе и знаменателе"
  (assert-equal (together '(+ 1/2 (/ 1 x))) '(* 1/2 (^ x -1) (+ 2 x)))
  (assert-equal (numer '(+ 1/2 (/ 1 x))) '(+ 2 x))
  (assert-equal (denom '(+ 1/2 (/ 1 x))) '(* 2 x)))

(deftest "together: многочлен — раскрытый вид, числа — сами себя"
  (assert-equal (together '(* (+ x 1) (+ x 2))) '(+ 2 (* 3 x) (^ x 2)))
  (assert-equal (together 5) 5)
  (assert-equal (together 1/3) 1/3))

(deftest "together: ядра"
  (assert-equal (together '(+ (/ 1 (sin x)) (/ 1 (cos x))))
                (simplify '(* (+ (sin x) (cos x)) (^ (sin x) -1) (^ (cos x) -1)))))

; --- cancel ---

(deftest "cancel: сокращение дроби"
  (assert-equal (cancel '(/ (- (^ x 2) 1) (+ (^ x 2) (* 2 x) 1))) (together '(/ (- x 1) (+ x 1))))
  (assert-equal (denom (cancel '(/ (- (^ x 2) 1) (+ (^ x 2) (* 2 x) 1)))) '(+ 1 x)))

(deftest "cancel: слагаемые не приводятся к общему знаменателю"
  (assert-equal (cancel '(+ (/ (- (^ x 2) 1) (- x 1)) (/ 1 y))) '(+ 1 x (^ y -1))))

(deftest "simplify не сокращает дробей — только явные команды"
  (assert-true (not (equal? (simplify '(/ (- (^ x 2) 1) (- x 1))) '(+ 1 x))))
  (assert-equal (cancel '(/ (- (^ x 2) 1) (- x 1))) '(+ 1 x)))

; --- apart ---

(deftest "apart: два линейных множителя"
  (assert-equal (apart '(/ 1 (- (^ x 2) 1)) 'x)
                '(+ (* 1/2 (^ (+ -1 x) -1)) (* -1/2 (^ (+ 1 x) -1)))))

(deftest "apart: повторный множитель"
  (assert-equal (apart '(/ 1 (* x (^ (+ x 1) 2))) 'x)
                '(+ (^ x -1) (* -1 (^ (+ 1 x) -2)) (* -1 (^ (+ 1 x) -1)))))

(deftest "apart: целая часть многочленом"
  (assert-equal (apart '(/ (^ x 3) (- (^ x 2) 1)) 'x)
                '(+ x (* 1/2 (^ (+ -1 x) -1)) (* 1/2 (^ (+ 1 x) -1)))))

(deftest "apart: квадратичный множитель — инвариант"
  (define e '(/ (+ (^ x 3) 1) (* (^ (- x 1) 2) (+ (^ x 2) 1))))
  (assert-equal (together (apart e 'x)) (together e)))

(deftest "apart: знаменатель степени 6 — инвариант"
  (define e '(/ (+ (* 3 (^ x 4)) x 7) (- (^ x 6) 1)))
  (assert-equal (together (apart e 'x)) (together e)))

(deftest "apart: кратность 3 и квадратичный множитель в степени 2"
  (define e '(/ (+ (^ x 5) 2) (* (^ (+ x 2) 3) (^ (+ (^ x 2) x 1) 2))))
  (assert-equal (together (apart e 'x)) (together e)))

(deftest "apart: параметр в числителе"
  (define e '(/ y (* x (+ x 1))))
  (assert-equal (together (apart e 'x)) (together e))
  (assert-equal (apart e 'x) '(+ (* (^ x -1) y) (* -1 y (^ (+ 1 x) -1)))))

(deftest "apart: x в знаменателе нет — выражение не меняется"
  (assert-equal (apart '(/ (+ x 1) y) 'x) (simplify '(/ (+ x 1) y))))

(deftest "apart: без знаменателя с x — выражение как есть (simplify, без раскрытия)"
  (assert-equal (apart '(* (+ x 1) (+ x 2)) 'x) '(* (+ 1 x) (+ 2 x))))

; --- gcd / lcm / деление ---

(deftest "poly-gcd: одномерный"
  (assert-equal (poly-gcd '(- (^ x 2) 1) '(+ (^ x 2) (* 2 x) 1)) '(+ 1 x))
  (assert-equal (poly-gcd '(+ x 1) '(+ x 2)) 1))

(deftest "poly-gcd: многомерный"
  (assert-equal (poly-gcd '(- (^ x 2) (^ y 2)) '(+ x y)) '(+ x y))
  (assert-equal (poly-gcd '(* (+ x y) (+ x 1)) '(* (+ x y) (+ y 1))) '(+ x y)))

(deftest "poly-lcm"
  (assert-equal (poly-lcm '(- (^ x 2) 1) '(+ (^ x 2) (* 2 x) 1))
                (expand '(* (- x 1) (^ (+ x 1) 2)))))

(deftest "poly-quotient и poly-remainder"
  (assert-equal (poly-quotient '(+ (^ x 3) 1) '(+ x 1) 'x) '(+ 1 (* -1 x) (^ x 2)))
  (assert-equal (poly-remainder '(+ (^ x 3) 2) '(+ x 1) 'x) 1)
  (assert-true (poly-divides? '(+ x 1) '(+ (^ x 3) 1) 'x)))

(deftest "poly-quotient: параметры — инвариант a = q b + r"
  (define a '(+ (^ x 3) (* y x) 7))
  (define b '(+ (* y x) 1))
  (define q (poly-quotient a b 'x))
  (define r (poly-remainder a b 'x))
  (assert-equal (together (list '+ (list '* q b) r)) (together a)))

; --- coeff / degree / variables ---

(deftest "coeff и degree"
  (assert-equal (coeff '(* (+ x 1) (+ x 2)) 'x 1) 3)
  (assert-equal (coeff '(* (+ x 1) (+ x 2)) 'x 2) 1)
  (assert-equal (coeff '(* (+ x 1) (+ x 2)) 'x 5) 0)
  (assert-equal (degree '(* (+ x 1) (+ x 2)) 'x) 2))

(deftest "coeff и degree: несколько переменных"
  (assert-equal (coeff '(+ (* x x y) (* 3 x) (^ y 3)) 'x 2) 'y)
  (assert-equal (degree '(+ (* x x y) (* 3 x) (^ y 3)) 'y) 3)
  (assert-equal (coeff '(+ (* a x) (* b x) c) 'x 1) '(+ a b)))

(deftest "degree: нуль и рациональная функция"
  (assert-equal (degree 0 'x) '-inf)
  (assert-equal (degree 7 'x) 0)
  (assert-equal (degree '(/ (^ x 3) (+ x 1)) 'x) 2))

(deftest "variables: символы и ядра"
  (assert-equal (variables '(+ x (* y (sin z)) (sqrt 2))) '((^ 2 1/2) x y (sin z)))   ; Шаг 21c: (sqrt 2) → (^ 2 1/2)
  (assert-equal (variables 5) '())
  (assert-equal (variables '(* (sin x) (sin x))) '((sin x))))

(deftest "coefficients, leading-coefficient, coefficients->poly"
  (assert-equal (coefficients '(+ 1 (* 3 x) (^ x 3)) 'x) '(1 3 0 1))
  (assert-equal (leading-coefficient '(+ 1 (* 3 x) (* 5 (^ x 3))) 'x) 5)
  (assert-equal (coefficients->poly '(1 3 0 1) 'x) '(+ 1 (* 3 x) (^ x 3)))
  (assert-equal (coefficients 0 'x) '()))

; --- sqfree, poly?, polynomial? ---

(deftest "sqfree"
  (assert-equal (sqfree (expand '(* (^ (+ x 1) 2) (- x 2)))) '(* (+ -2 x) (^ (+ 1 x) 2))))

(deftest "poly? и polynomial?"
  (assert-true (poly? '(+ (* x x) y)))
  (assert-true (not (poly? '(+ x (/ 1 x)))))
  (assert-true (polynomial? '(+ x (/ 1 y)) 'x))
  (assert-true (not (polynomial? '(+ x (/ 1 x)) 'x)))
  (assert-true (not (polynomial? '(sin x) 'x)))
  (assert-true (polynomial? '(* y (sin z)) 'x)))

; --- factor: рациональные функции, ядра, инвариант ---

(deftest "factor: рациональная функция"
  (assert-equal (factor '(/ (- (^ x 2) 1) (+ (^ x 2) (* 2 x) 1)))
                '(* (+ -1 x) (^ (+ 1 x) -1))))

(deftest "factor: ядра"
  (assert-equal (factor '(- (^ (exp x) 2) 1)) '(* (+ -1 (exp x)) (+ 1 (exp x))))
  (assert-equal (factor '(- (^ (sin x) 2) 4)) '(* (+ -2 (sin x)) (+ 2 (sin x)))))

(deftest "factor: инвариант expand(factor p) = expand p"
  (define ps '((- (^ x 4) 1) (+ (^ x 4) 4) (+ (* 2 (^ x 2)) (* 4 x) 2) (- (^ x 2) (^ y 2))
               (+ (* x x y) (* x y y)) (- (^ x 8) 1)))
  (assert-true (every? (lambda (p) (equal? (expand (factor p)) (expand p))) ps)))

(deftest "factor: x^20 - 1 и многомерный пример"
  (assert-equal (length (cdr (factor '(- (^ x 20) 1)))) 6)
  (assert-equal (factor '(- (^ x 2) (^ y 2))) '(* (+ x y) (+ x (* -1 y)))))
