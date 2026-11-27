; zerotest.lisp — тесты шага CHECK.DUAL: общий тест нуля zero-test (lib/zerotest.lisp)

(define zt-c2
  ; c2 из SPDE1 для exp((x + 300)·log(log x + 1)): тождественный нуль, together не сокращает степени суммы
  '(* (^ (+ x (* %t1 x)) -1)
      (+ (* -1 %t1 x (^ (+ 1 %t1) 299)) (* -300 %t1 (^ (+ 1 %t1) 299)) (* -1 x (^ (+ 1 %t1) 299))
         (* x (^ (+ 1 %t1) 300)) (* -300 (^ (+ 1 %t1) 299)) (* 300 (^ (+ 1 %t1) 300)))))
(define zt-log-zero '(+ (log 6) (* -1 (log 2)) (* -1 (log 3))))

(deftest "zerotest: дешёвые признаки — together дал 0, число"
  (assert-equal (zero-test 0 '()) 'zero)
  (assert-equal (zero-test 5 '()) 'nonzero)
  (assert-equal (zero-test '(- (^ (+ x 1) 2) (+ (^ x 2) (* 2 x) 1)) '(x)) 'zero)
  (assert-equal (zero-test '(- (/ (+ (^ x 2) -1) (+ x -1)) (+ x 1)) '(x)) 'zero))

(deftest "zerotest: ненуль — по точкам, подделка не проходит"
  (assert-equal (zero-test '(+ x 1) '(x)) 'nonzero)
  (assert-equal (zero-test '(- (^ (+ x 1) 2) (+ (^ x 2) (* 2 x))) '(x)) 'nonzero)
  ; тождество с возмущением 1e-3
  (assert-equal (zero-test '(+ (* 1/1000 x) (- (^ (+ x 1) 2) (+ (^ x 2) (* 2 x) 1))) '(x)) 'nonzero)
  (assert-equal (zero-test '(- (* a x) (* x b)) #f) 'nonzero))

(deftest "zerotest: степень суммы > 32 — together не канонична, нуль подтверждается подстановкой (INT.FALSENE.1)"
  (assert-equal (zero-test zt-c2 #f 'kernels) 'zero)
  (assert-equal (zero-test (list '+ zt-c2 '(^ (+ 1 %t1) 300)) #f 'kernels) 'nonzero)
  ; разность (1 + θ)^300 − (1 + θ)^299: точки не вычислены (степень 300 числа не раскрывается) — «не знаю», но не «zero»
  (assert-true (not (equal? (zero-test '(- (^ (+ 1 %t1) 300) (^ (+ 1 %t1) 299)) #f 'kernels) 'zero))))

(deftest "zerotest: константы — точный const-zero?, ядра log независимы только по запросу"
  (assert-equal (zero-test (list '* zt-log-zero 'x) '(x)) 'zero)
  (assert-equal (zero-test '(log 2) '()) 'nonzero)
  ; с ядрами log независимы: 'zero по ним верно, 'nonzero лишь «нуль не подтверждён» — тождество log 6 = log 2 + log 3 скрыто
  (assert-equal (zero-test (list '* zt-log-zero 'x) '(x) 'kernels) 'nonzero)
  (assert-equal (zero-test '(+ (^ (+ x (log 2)) 40) (* -1 (^ (+ x (log 2)) 40))) '(x) 'kernels) 'zero))

(deftest "zerotest: unknown — не решено, а не догадка"
  ; неизвестная голова: значение не константа
  (assert-equal (zero-test '(foo x) '(x)) 'unknown)
  ; а sin 7 ≠ 0 const-zero? доказывает
  (assert-equal (zero-test '(sin x) '(x)) 'nonzero)
  ; cos(π/5) − (1 + √5)/4: const-zero? не решает — unknown, никогда не zero без доказательства
  (assert-equal (zero-test '(+ (cos (/ pi 5)) (* -1 (/ (+ 1 (^ 5 1/2)) 4))) '()) 'unknown)
  ; полюс в единственной пробной точке (x = 7) → не число
  (assert-equal (zero-test '(^ (+ x -7) -1) '(x) '(points 1)) 'unknown))

(deftest "zerotest: опция (at правила) — одна заданная точка, решение оракула"
  (assert-equal (zero-test '(- (* a x) (* x a)) '() (list 'at '((x 3/10) (a 17/10)))) 'zero)
  (assert-equal (zero-test '(+ (* a x) 1) '() (list 'at '((x 3/10) (a 17/10)))) 'nonzero)
  (assert-equal (zero-test '(+ (* 1/1000 x) (- (* a x) (* x a))) '() (list 'at '((x 3/10) (a 17/10)))) 'nonzero)
  (assert-equal (zero-test '(- (log 4) (* 2 (log 2))) '() (list 'at '())) 'zero)
  (assert-equal (zero-test '(foo x) '() (list 'at '((x 3/10)))) 'unknown)
  ; полюс в точке — не ноль и не число
  (assert-equal (zero-test '(^ (+ x -3/10) -1) '() (list 'at '((x 3/10)))) 'unknown))
