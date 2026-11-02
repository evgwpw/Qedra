; Lisp-тесты рядов Тейлора/Лорана (lib\series.lisp), Шаг 20

; коэффициенты при (x − a)^k для k от lo до hi-1
(define (sc s lo hi) (map (lambda (k) (series-coeff s k)) (series::ser-range lo hi)))

(deftest "ряды: стандартные функции в нуле"
  (assert-equal (sc (series '(exp x) 'x 0 5) 0 5) '(1 1 1/2 1/6 1/24))
  (assert-equal (sc (series '(sin x) 'x 0 6) 0 6) '(0 1 0 -1/6 0 1/120))
  (assert-equal (sc (series '(cos x) 'x 0 6) 0 6) '(1 0 -1/2 0 1/24 0))
  (assert-equal (sc (series '(log (+ 1 x)) 'x 0 5) 0 5) '(0 1 -1/2 1/3 -1/4))
  (assert-equal (sc (series '(/ 1 (- 1 x)) 'x 0 5) 0 5) '(1 1 1 1 1)))

(deftest "ряды: tan, atan, asin, гиперболические"
  (assert-equal (sc (series '(tan x) 'x 0 8) 0 8) '(0 1 0 1/3 0 2/15 0 17/315))
  (assert-equal (sc (series '(atan x) 'x 0 6) 0 6) '(0 1 0 -1/3 0 1/5))
  (assert-equal (sc (series '(asin x) 'x 0 6) 0 6) '(0 1 0 1/6 0 3/40))
  (assert-equal (sc (series '(sinh x) 'x 0 5) 0 5) '(0 1 0 1/6 0))
  (assert-equal (sc (series '(cosh x) 'x 0 5) 0 5) '(1 0 1/2 0 1/24))
  (assert-equal (sc (series '(tanh x) 'x 0 6) 0 6) '(0 1 0 -1/3 0 2/15)))

(deftest "ряды: (1+x)^r и корень"
  (assert-equal (sc (series '(^ (+ 1 x) 1/2) 'x 0 4) 0 4) '(1 1/2 -1/8 1/16))
  (assert-equal (sc (series '(^ (+ 1 x) -1) 'x 0 4) 0 4) '(1 -1 1 -1))
  (assert-equal (sc (series '(sqrt (+ 1 x)) 'x 0 3) 0 3) '(1 1/2 -1/8))
  (assert-equal (sc (series '(^ (+ 1 x) r) 'x 0 3) 0 3)
                (list 1 'r (simplify '(* 1/2 r (+ r -1))))))

(deftest "ряды: печать"
  (assert-equal (to-string (series '(exp x) 'x 0 3)) "1 + x + 1/2*x^2 + O(x^3)")
  (assert-equal (to-string (series '(sin x) 'x 0 6)) "x - 1/6*x^3 + 1/120*x^5 + O(x^6)")
  (assert-equal (to-string (series '(/ 1 (sin x)) 'x 0 3)) "x^-1 + 1/6*x + O(x^3)")
  (assert-equal (to-string (series '(exp x) 'x 1 2)) "exp(1) + exp(1)*(x - 1) + O((x - 1)^2)")
  (assert-equal (to-string (series 0 'x 0 3)) "O(x^3)"))

(deftest "ряды: композиции"
  (assert-equal (sc (series '(exp (sin x)) 'x 0 6) 0 6) '(1 1 1/2 0 -1/8 -1/15))
  (assert-equal (sc (series '(log (cos x)) 'x 0 7) 0 7) '(0 0 -1/2 0 -1/12 0 -1/45))
  (assert-equal (sc (series '(/ (sin x) x) 'x 0 5) 0 5) '(1 0 -1/6 0 1/120))
  (assert-equal (sc (series '(sin (^ x 2)) 'x 0 7) 0 7) '(0 0 1 0 0 0 -1/6))
  (assert-equal (sc (series '(exp (log (+ 1 x))) 'x 0 4) 0 4) '(1 1 0 0))
  (assert-equal (sc (series '(/ (- (exp x) 1 x) (^ x 2)) 'x 0 3) 0 3) '(1/2 1/6 1/24)))

(deftest "ряды: в точке, отличной от нуля"
  (assert-equal (to-string (series '(exp x) 'x 1 2)) "exp(1) + exp(1)*(x - 1) + O((x - 1)^2)")
  (assert-equal (sc (series '(log x) 'x 1 4) 0 4) '(0 1 -1/2 1/3))
  (assert-equal (sc (series '(sqrt x) 'x 4 3) 0 3) '(2 1/4 -1/64))
  (assert-equal (sc (series '(^ x 2) 'x 3 4) 0 4) '(9 6 1 0))
  (assert-equal (sc (series '(/ 1 x) 'x 2 3) 0 3) '(1/2 -1/4 1/8))
  (assert-equal (sc (series '(cos x) 'x '(/ pi 2) 4) 0 4) '(0 -1 0 1/6))
  (assert-equal (sc (series '(sin x) 'x 'pi 4) 0 4) '(0 -1 0 1/6)))

(deftest "ряды: точка — символ"
  (assert-equal (sc (series '(^ x 2) 'x 'b 3) 0 3) (list (simplify '(^ b 2)) (simplify '(* 2 b)) 1))
  (assert-equal (sc (series '(exp x) 'x 'b 3) 0 3)
                (list (simplify '(exp b)) (simplify '(exp b)) (simplify '(* 1/2 (exp b))))))

(deftest "ряды Лорана: полюсы"
  (assert-equal (sc (series '(/ 1 (sin x)) 'x 0 4) -1 4) '(1 0 1/6 0 7/360))
  (assert-equal (sc (series '(/ 1 (* (^ x 2) (- 1 x))) 'x 0 3) -2 3) '(1 1 1 1 1))
  (assert-equal (sc (series '(cot x) 'x 0 4) -1 4) '(1 0 -1/3 0 -1/45))
  (assert-equal (series-order (series '(/ 1 (sin x)) 'x 0 3)) 3)
  (assert-equal (to-string (series '(tan x) 'x '(/ pi 2) 3))
                "-(x - 1/2*pi)^-1 + 1/3*(x - 1/2*pi) + O((x - 1/2*pi)^3)")
  (assert-equal (sc (series '(/ 1 (^ x 3)) 'x 0 2) -3 2) '(1 0 0 0 0)))

(deftest "ряды: символьные коэффициенты"
  (assert-equal (sc (series '(exp (* a x)) 'x 0 4) 0 4)
                (list 1 'a (simplify '(* 1/2 (^ a 2))) (simplify '(* 1/6 (^ a 3)))))
  (assert-equal (sc (series '(sin (* a x)) 'x 0 4) 0 4)
                (list 0 'a 0 (simplify '(* -1/6 (^ a 3)))))
  (assert-equal (sc (series '(/ 1 (- 1 (* a x))) 'x 0 3) 0 3)
                (list 1 'a (simplify '(^ a 2)))))

(deftest "ряды: log(x) как медленный коэффициент"
  (assert-equal (to-string (series '(* x (log x)) 'x 0 2)) "log(x)*x + O(x^2)")
  (assert-equal (series-coeff (series '(^ x x) 'x 0 3) 1) '(log x))
  (assert-equal (series-coeff (series '(^ x x) 'x 0 3) 0) 1)
  (assert-equal (series-coeff (series '(log (* 2 x)) 'x 0 2) 0) (simplify '(+ (log 2) (log x)))))

(deftest "ряды: арифметика объектов"
  (let ((s (series '(exp x) 'x 0 4)) (c (series '(cos x) 'x 0 4)))
    (assert-equal (sc (+ s c) 0 4) '(2 1 0 1/6))
    (assert-equal (sc (- s c) 0 4) '(0 1 1 1/6))
    (assert-equal (sc (* s c) 0 4) '(1 1 0 -1/3))
    (assert-equal (sc (+ s 1) 0 3) '(2 1 1/2))
    (assert-equal (sc (* 2 s) 0 3) '(2 2 1))
    (assert-equal (sc (/ 1 c) 0 4) '(1 0 1/2 0))
    (assert-equal (sc (^ c 2) 0 3) '(1 0 -1))
    (assert-equal (sc (^ s -1) 0 3) '(1 -1 1/2))
    (assert-equal (sc (* 'x s) 1 4) '(1 1 1/2))))

(deftest "ряды: taylor — многочлен без O"
  (assert-equal (taylor '(exp x) 'x 0 4) (simplify '(+ 1 x (* 1/2 (^ x 2)) (* 1/6 (^ x 3)))))
  (assert-equal (taylor '(sin x) 'x 0 4) (simplify '(+ x (* -1/6 (^ x 3)))))
  (assert-equal (taylor '(+ 1 (* 2 x)) 'x 0 5) (simplify '(+ 1 (* 2 x))))
  (assert-equal (series->expr (series '(/ 1 (sin x)) 'x 0 3)) (simplify '(+ (^ x -1) (* 1/6 x)))))

(define (nth-diff e j) (if (= j 0) e (nth-diff (diff 'x e) (- j 1))))
; k-й коэффициент ряда · k! совпадает (численно) с k-й производной в нуле
(define (taylor-matches? f k)
  (let ((a (eval-num (simplify (list '* (series-coeff (series f 'x 0 5) k) (series::ser-fact k)))))
        (b (eval-num (subst (list '= 'x 0) (nth-diff f k)))))
    (< (num-abs (- a b)) 0.000000001)))

(deftest "ряды: taylor совпадает с определением через производные"
  (assert-true
   (every? (lambda (f) (every? (lambda (k) (taylor-matches? f k)) '(0 1 2 3 4)))
           '((exp x) (sin x) (cos x) (/ 1 (+ 2 x)) (atan x) (log (+ 1 x)) (sqrt (+ 1 x)) (exp (sin x))
             (/ x (+ 1 (exp x))) (* (cos x) (exp (* 2 x)))))))

(define (sq-plus u) (+ (* u u) 1))

(deftest "ряды: запасной путь (производные) и пользовательские функции"
  (assert-equal (sc (series '(acosh (+ 1 x)) 'x 1 2) 0 1) (list (simplify '(acosh 2))))
  (assert-equal (sc (series '(sq-plus x) 'x 0 4) 0 4) '(1 0 1 0))
  (assert-equal (sc (series '(asec x) 'x 2 1) 0 1) (list (simplify '(asec 2)))))

(deftest "ряды: ошибки"
  (assert-error (series '(sin (/ 1 x)) 'x 0 3))
  (assert-error (series '(^ x 1/2) 'x 0 3))
  (assert-error (series '(exp x) 'x 'inf 3))
  (assert-error (series '(exp x) 3 0 3))
  (assert-error (series '(unknown-fn x) 'x 0 3)))
