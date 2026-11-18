; tests/Lisp.Tests/lisp/rubi-nf.lisp — RUBI.NF: одна нормальная форма выражения для Rubi.
; Проверяется, что rubi-nf делает ровно автовычисление Mathematica (Flat/Orderless, числа, основания
; степеней, целые степени произведения, Times[-1, …]) и НЕ делает упрощений (tan остаётся tan,
; скобки не раскрываются, подобные с символьными коэффициентами не собираются).
(load "lib/rubi/nf.lisp")

(define (nf-is e want) (assert-equal (rubi-nf e) want))

(deftest "rubi-nf: числа сворачиваются, единицы и нули уходят"
  (nf-is '(* 2 3 x) '(* 6 x))
  (nf-is '(+ 1/2 1/3 x) '(+ 5/6 x))
  (nf-is '(* 1 x) 'x)
  (nf-is '(+ 0 x) 'x)
  (nf-is '(* 0 x) 0)
  (nf-is '(+ 1 2) 3)
  (nf-is '(* -1 (^ 2 3)) -8))

(deftest "rubi-nf: подобные слагаемые и Times[-1, …]"
  (nf-is '(+ x x) '(* 2 x))
  (nf-is '(+ (* 2 x) (* 3 x)) '(* 5 x))
  (nf-is '(+ x (* -1 x)) 0)
  (nf-is '(- (* 2 x) (* 3 x)) '(* -1 x))
  (nf-is '(- x) '(* -1 x))
  ; с символьными коэффициентами Mathematica подобные не собирает — и мы нет
  (nf-is '(+ (* a x) (* b x)) '(+ (* a x) (* b x))))

(deftest "rubi-nf: степени — основания склеиваются, целые степени раскрываются"
  (nf-is '(* x (^ x 2)) '(^ x 3))
  (nf-is '(* (^ x 1/2) (^ x 1/2)) 'x)
  (nf-is '(* (exp x) (exp (* 2 x))) '(^ E (* 3 x)))
  (nf-is '(* (^ x a) (^ x b)) '(^ x (+ a b)))
  (nf-is '(^ (^ x 2) 3) '(^ x 6))
  (nf-is '(^ (* a b) 2) '(* (^ a 2) (^ b 2)))
  ; дробная внешняя степень НЕ сворачивается: (u²)^(1/2) = |u|, а не u
  (nf-is '(^ (^ x 2) 1/2) '(^ (^ x 2) 1/2))
  (nf-is '(^ x 0) 1)
  (nf-is '(^ x 1) 'x))

(deftest "rubi-nf: деление и корни — как автовычисление, без упрощений"
  (nf-is '(/ 1 (* a b)) '(* (^ a -1) (^ b -1)))
  (nf-is '(/ (sin x) (cos x)) '(* (sin x) (^ (cos x) -1)))
  (nf-is '(sqrt 4) 2)
  (nf-is '(sqrt (* 4 x)) '(* 2 (^ x 1/2)))
  (nf-is '(sqrt (* a b)) '(^ (* a b) 1/2)))

(deftest "rubi-nf: тригонометрия и скобки не трогаются (одна форма — головы Rubi)"
  (nf-is '(tan x) '(tan x))
  (nf-is '(sec x) '(sec x))
  (nf-is '(cot x) '(cot x))
  (nf-is '(csc x) '(csc x))
  (nf-is '(* (tan x) (cos x)) '(* (tan x) (cos x)))
  (nf-is '(^ (+ a b) 2) '(^ (+ a b) 2))
  ; ac-norm под единой формой тоже не переписывает sec/cot/csc
  (ac-trig-recip! #f)
  (assert-equal (ac-norm '(sec x)) '(sec x))
  (assert-equal (ac-norm '(^ (cot x) 2)) '(^ (cot x) 2))
  (ac-trig-recip! #t)
  (assert-equal (ac-norm '(sec x)) '(^ (cos x) -1)))

(deftest "rubi-nf: форма идемпотентна (норма дважды = норма один раз)"
  (for-each
   (lambda (e)
     (assert-equal (rubi-nf (rubi-nf e)) (rubi-nf e)))
   (list '(/ 1 (* a b)) '(* (tan x) (^ (cos x) -2)) '(+ (* 2 (^ x 2)) (* -2 (^ x 2)) y)
         '(sqrt (* 4 (^ x 2))) '(* (exp x) (^ (exp x) -1)) '(+ (/ a b) (/ c d)))))

(deftest "rubi-nf: интегралы, где форма решает (Rubi узнаёт правило)"
  ; флаг включается только на время проверки: по умолчанию единая форма выключена (шаги 2–3 карточки)
  (set! *rubi-nf* #t)
  (ac-trig-recip! #f)
  ; tan и sec остаются головами: правила 4.1/4.2 на них есть, на sin·cos^-1 — нет
  (assert-equal (integrate '(tan x) 'x) '(* -1 (log (cos x))))
  (assert-equal (integrate '(/ 1 (cos x)) 'x)
                '(log (* (+ 1 (sin x)) (^ (cos x) -1))))
  (assert-equal (integrate '(* (sin x) (cos x)) 'x) '(* 1/2 (^ (sin x) 2)))
  (assert-equal (integrate '(/ 1 (+ 1 (^ x 2))) 'x) '(atan x))
  (set! *rubi-nf* #f)
  (ac-trig-recip! #t))


(deftest "rubi-nf: упрощения Rubi не меняют тригонометрическую форму (шаг 3)"
  ; Simp/SimplifyIntegrand не переписывают tan/cot/sec/csc в sin/cos даже ценой «меньшего» выражения
  (assert-equal (rubi::rubi-simplify-integrand '(tan x) 'x) '(tan x))
  (assert-equal (rubi::rubi-simplify-integrand '(^ (sec x) 2) 'x) '(^ (sec x) 2))
  (assert-equal (rubi::rubi-simp '(cot x)) '(cot x))
  ; обычное упрощение (не больше исходного, без тригонометрии) проходит как раньше
  (assert-equal (rubi::rubi-simplify-integrand '(+ x x) 'x) '(* 2 x))
  (assert-equal (rubi::rubi-simp '(+ (* 2 x) (* 3 x))) '(* 5 x)))

