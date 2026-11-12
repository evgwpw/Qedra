; RUBI.CH-C.2: утилиты главы 4 в lib/rubi/utils-c.lisp (InertTrigFreeQ, FunctionOfTrigOfLinearQ).
; Источник: Rubi 4.17.3.0, commit 61e9c18, IntegrationUtilityFunctions.m (строки указаны в тестах).
; Файл утилит грузится движком перед правилами главы 4; здесь — явно, тест движок не поднимает.
(load "lib/rubi/utils-c.lisp")

(deftest "rubi-c: InertTrigFreeQ — тригонометрия есть"
  (assert-true (not (rubi::rubi-inert-trig-free-q '(sin x))))
  (assert-true (not (rubi::rubi-inert-trig-free-q '(* 2 (cos (+ a (* b x)))))))
  (assert-true (not (rubi::rubi-inert-trig-free-q '(+ 1 (tan x))))))

(deftest "rubi-c: InertTrigFreeQ — тригонометрии нет"
  (assert-true (rubi::rubi-inert-trig-free-q '(+ 1 x)))
  (assert-true (rubi::rubi-inert-trig-free-q '(* a (^ x 2))))
  (assert-true (rubi::rubi-inert-trig-free-q 'y)))

(deftest "rubi-c: FunctionOfTrigOfLinearQ — линейный аргумент"
  ; IUF.m:4358: (c+d*x)^m*(a+b*trig[e+f*x])^n
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(* (^ x 2) (sin (+ a (* b x)))) 'x))
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(+ 1 (^ (cos (* 2 x)) 2)) 'x))
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(/ (sin x) (cos x)) 'x)))

(deftest "rubi-c: FunctionOfTrigOfLinearQ — нелинейный аргумент или не тригонометрия"
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(sin (^ x 2)) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q (list '^ (list 'sin (list '^ 'x 2)) '(/ 1 2)) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(+ 1 x) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(exp x) 'x))))

(deftest "rubi-c: FunctionOfTrigOfLinearQ — параметр в аргументе и смешанные случаи"
  ; e+0*x — тоже линейный аргумент, поэтому sin(a+b) годится
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(sin (+ a b)) 'x))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(* (sin x) (sin (* x x))) 'x))))
