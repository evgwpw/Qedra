; RUBI.SYMU: утилиты условий (IntegerQ/EqQ/PolyQ) и Simp/SimplifyIntegrand по IUF.m и symbolica-integrate
; (src/lib.rs, MIT). Утилиты приватны — грузим utils.lisp, как rubi-rule.lisp.
(load (string-append lib-dir "rubi/utils.lisp"))

(deftest "rubi-symu: IntegerQ/RationalQ/IGtQ сворачивают числовое дерево (Sqrt[4])"
  (assert-equal #t (rubi::rubi-integerq '(^ 4 1/2)))
  (assert-equal #t (rubi::rubi-igtq '(^ 4 1/2) 1))
  (assert-equal #t (rubi::rubi-rationalq '(^ 4 1/2)))
  (assert-equal #f (rubi::rubi-integerq '(^ 2 1/2)))
  (assert-equal #f (rubi::rubi-integerq 'a))
  (assert-equal #f (rubi::rubi-integerq 4.0))
  (assert-equal #f (rubi::rubi-igtq 3 'a)))

(deftest "rubi-symu: EqQ — численный нуль константного выражения (PossibleZeroQ)"
  (assert-equal #t (rubi::rubi-eqq '(- (^ (+ 3 (* 2 (^ 2 1/2))) 1/2) (+ 1 (^ 2 1/2))) 0))
  (assert-equal #t (rubi::rubi-eqq '(- (log 8) (* 3 (log 2))) 0))
  (assert-equal #f (rubi::rubi-eqq '(- (^ 3 1/2) (^ 3 1/3)) 0))
  (assert-equal #t (rubi::rubi-neq '(- (^ 3 1/2) (^ 3 1/3)) 0))
  ; символьное: без численной догадки
  (assert-equal #f (rubi::rubi-eqq '(- (sin (* 2 a)) (* 2 (sin a) (cos a))) 0))
  (assert-equal #f (rubi::rubi-eqq '(- (* b c) (* a d)) 0)))

(deftest "rubi-symu: PolyQ — упрощённая дробь с (^ b -1) проходит через Together"
  (assert-equal #t (rubi::rubi-poly-q (/ (+ (^ 'x 3) 'x) 'x) 'x))
  (assert-equal #t (rubi::rubi-poly-q (/ (+ (^ 'x 3) 'x) 'x) 'x 2))
  (assert-equal #t (rubi::rubi-poly-q (/ (- (^ 'x 2) 1) (- 'x 1)) 'x 1))
  (assert-equal #f (rubi::rubi-poly-q (^ 'x -1) 'x))
  (assert-equal #f (rubi::rubi-poly-q (^ (+ 'a (* 'b 'x)) -1) 'x)))

; SYMU.2: NormalizeLeadTermSigns (IUF.m:2060) и схема принятия SimplifyIntegrand/NormalizeIntegrand (IUF.m:2148, 1988)
(deftest "rubi-symu: NormalizeLeadTermSigns — минус уходит из сумм со старшим отрицательным членом"
  (assert-equal '(* (+ 1 (* -1 x)) (+ 2 (* -1 x)))
                (rubi::rubi-normalize-lead-term-signs '(* (+ -1 x) (+ -2 x))))
  (assert-equal '(^ (+ 1 (* -1 x)) 2)
                (rubi::rubi-normalize-lead-term-signs '(^ (+ -1 x) 2)))
  ; нечётная степень: знак остаётся в сумме, как есть (AbsorbMinusSign возвращает минус обратно)
  (assert-equal '(+ -1 x) (rubi::rubi-normalize-lead-term-signs '(+ -1 x)))
  (assert-equal '(+ a (* b x)) (rubi::rubi-normalize-lead-term-signs '(+ a (* b x))))
  (assert-equal -5 (rubi::rubi-normalize-lead-term-signs -5)))

(deftest "rubi-symu: SimplifyIntegrand/NormalizeIntegrand возвращают исходное, если меняются только знаки"
  (assert-equal '(^ (+ -1 x) 2) (rubi::rubi-simplify-integrand '(^ (+ -1 x) 2) 'x))
  (assert-equal '(^ (+ -1 x) 2) (rubi::rubi-normalize-integrand '(^ (+ -1 x) 2) 'x))
  (assert-equal '(+ a (* b x)) (rubi::rubi-simplify-integrand '(+ a (* b x)) 'x)))
