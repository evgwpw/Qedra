; prob.lisp — тесты шага PROB: вероятность и статистика.
; Оракулы: (1) нормировка pdf/pmf = 1 для каждого распределения на двух наборах чисел (общий движок sum/integrate);
; (2) табличные среднее и дисперсия встроенных распределений = вычисленные ОБЩИМ движком (dist-expectation:
; sum / integrate по плотности), точно; у Пуассона и геометрического (бесконечные суммы) — численно, частичные суммы
; из 200 членов; (3) известные числа; (4) подделки: ненормированная плотность, выборка из одного элемента.

(define (pt-zero? a b) (let ((d (simplify (list '+ a (list '* -1 b))))) (or (equal? d 0) (< (abs (eval-num d)) 1e-12))))
(define (pt-done? v) (not (and (pair? v) (or (contains-sym? v 'integrate) (contains-sym? v 'sum) (contains-sym? v 'expectation)))))

; численная частичная сумма Σ_{k=lo}^{n} g(k)·pmf(k)
(define (pt-psum d g n)
  (let loop ((k (nth (dist-support d) 1)) (acc 0))
    (if (> k n) acc (loop (+ k 1) (+ acc (eval-num (list '* (g k) (dist-pdf d k))))))))

(define pt-finite-and-cont
  (list (bernoulli-dist 1/3) (bernoulli-dist 3/4) (binomial-dist 6 1/3) (binomial-dist 5 3/5)
        (uniform-discrete 2 7) (uniform-discrete -3 4) (hypergeometric-dist 10 4 3) (hypergeometric-dist 12 5 6)
        (uniform-dist 1 4) (uniform-dist -2 3/2) (normal-dist 1 2) (normal-dist 0 1) (exponential-dist 1/2) (exponential-dist 3)
        (gamma-dist 3 2) (gamma-dist 5/2 1) (beta-dist 2 3) (beta-dist 3 2) (chi2-dist 4) (chi2-dist 3)
        (student-dist 3) (student-dist 5)))

(deftest "prob: нормировка — сумма/интеграл плотности = 1 (два набора параметров на распределение)"
  (for-each (lambda (d)
              (let ((m (dist-mass d)))
                (assert-true (pt-done? m))
                (assert-true (pt-zero? m 1))
                (assert-equal (dist-check d) #t)))
            pt-finite-and-cont)
  ; бесконечные дискретные суммы — численно (частичные суммы)
  (assert-true (< (abs (- (pt-psum (poisson-dist 2) (lambda (k) 1) 200) 1)) 1e-12))
  (assert-true (< (abs (- (pt-psum (poisson-dist 7/2) (lambda (k) 1) 200) 1)) 1e-12))
  (assert-true (< (abs (- (pt-psum (geometric-dist 1/3) (lambda (k) 1) 200) 1)) 1e-12))
  (assert-true (< (abs (- (pt-psum (geometric-dist 3/4) (lambda (k) 1) 200) 1)) 1e-12))
  ; честно «не знаю», а не #t
  (assert-equal (dist-check (poisson-dist 2)) 'unknown))

(deftest "prob: среднее и дисперсия — таблица = общий движок (sum/integrate), точно"
  (for-each (lambda (d)
              (let ((m (dist-mean d)) (m1 (dist-expectation 'x 'x d)) (m2 (dist-expectation '(^ x 2) 'x d)))
                (assert-true (pt-done? m1))
                (assert-true (pt-done? m2))
                (assert-true (pt-zero? m m1))
                (assert-true (pt-zero? (dist-variance d) (list '+ m2 (list '* -1 (list '* m1 m1)))))
                (assert-true (pt-zero? (dist-stddev d) (list '^ (dist-variance d) 1/2)))))
            pt-finite-and-cont)
  (for-each (lambda (d)
              (let ((m (dist-mean d)) (v (dist-variance d)))
                (assert-true (< (abs (- m (pt-psum d (lambda (k) k) 200))) 1e-10))
                (assert-true (< (abs (- (+ v (* m m)) (pt-psum d (lambda (k) (* k k)) 200))) 1e-10))))
            (list (poisson-dist 2) (poisson-dist 7/2) (geometric-dist 1/3) (geometric-dist 3/4))))

(deftest "prob: символьные параметры — среднее, дисперсия, mgf, моменты"
  (assert-equal (dist-mean (normal-dist 'm 's)) 'm)
  (assert-true (pt-zero? (dist-variance (binomial-dist 'n 'p)) '(* n p (+ 1 (* -1 p)))))
  (assert-true (pt-zero? (dist-mgf (exponential-dist 'l) 't) '(* l (^ (+ l (* -1 t)) -1))))
  (assert-true (pt-zero? (dist-moment (exponential-dist 'l) 3) '(* 6 (^ l -3))))
  (assert-equal (dist-moment (normal-dist 0 1) 4) 3)
  (assert-equal (dist-moment (normal-dist 0 1) 3) 0)
  (assert-equal (dist-moment (poisson-dist 2) 2) 6)
  (assert-equal (dist-moment (uniform-dist 1 4) 3) 85/4)         ; (4⁴ − 1⁴)/(4·3); mgf в 0 — особенность, общий путь
  ; момент из mgf = момент по определению (общий движок)
  (for-each (lambda (d)
              (assert-true (pt-zero? (dist-moment d 3) (dist-expectation '(^ x 3) 'x d))))
            (list (binomial-dist 5 1/3) (uniform-dist 1 4) (exponential-dist 1/2) (gamma-dist 3 2) (chi2-dist 4)))
  ; mgf в нуле равен 1
  (for-each (lambda (d) (assert-true (pt-zero? (dist-mgf d 0) 1)))
            (list (bernoulli-dist 1/3) (binomial-dist 4 1/2) (poisson-dist 2) (normal-dist 1 2) (gamma-dist 2 3)))
  ; у Стьюдента mgf нет — ошибка, у ν ≤ 1 нет среднего
  (assert-error (dist-mgf (student-dist 3) 't))
  (assert-error (dist-mean (student-dist 1)))
  (assert-error (dist-moment (student-dist 3) 3)))

(deftest "prob: известные числа"
  ; нормальное cdf(1) ≈ 0.841344746068543
  (assert-true (< (abs (- (eval-num (dist-cdf (normal-dist 0 1) 1)) 0.841344746068543)) 1e-12))
  (assert-equal (dist-cdf (normal-dist 0 1) 0) 1/2)
  (assert-equal (dist-cdf (normal-dist 0 1) '-inf) 0)
  ; P(−1 ≤ Z ≤ 1) = erf(1/√2) ≈ 0.6826894921370859
  (assert-true (< (abs (- (eval-num (dist-prob (normal-dist 0 1) -1 1)) 0.6826894921370859)) 1e-12))
  ; биномиальное P(X = 3), n = 10, p = 1/2
  (assert-equal (dist-pdf (binomial-dist 10 1/2) 3) 15/128)
  (assert-equal (dist-cdf (binomial-dist 10 1/2) 10) 1)
  ; Пуассон λ = 2: P(X ≤ 2) = 5e^{−2}
  (assert-true (pt-zero? (dist-cdf (poisson-dist 2) 2) '(* 5 (exp -2))))
  (assert-true (pt-zero? (dist-prob (poisson-dist 2) 3 'inf) '(+ 1 (* -5 (exp -2)))))
  ; показательное λ = 1/2: P(X > 4) = e^{−2}; P(X ≤ 4) дополняет
  (assert-true (pt-zero? (dist-prob (exponential-dist 1/2) 4 'inf) '(exp -2)))
  (assert-true (pt-zero? (dist-cdf (exponential-dist 1/2) 4) '(+ 1 (* -1 (exp -2)))))
  ; равномерное и бета
  (assert-equal (dist-prob (uniform-dist 0 4) 1 3) 1/2)
  (assert-equal (dist-cdf (beta-dist 2 3) 1/2) 11/16)
  (assert-equal (dist-pdf (geometric-dist 1/2) 3) 1/8)
  ; гипергеометрическое: P(X = 1), N = 10, K = 4, n = 3 → C(4,1)C(6,2)/C(10,3) = 1/2
  (assert-equal (dist-pdf (hypergeometric-dist 10 4 3) 1) 1/2)
  ; вне носителя и нецелая точка — 0
  (assert-equal (dist-pdf (binomial-dist 10 1/2) 11) 0)
  (assert-equal (dist-pdf (binomial-dist 10 1/2) 1/2) 0)
  (assert-equal (dist-pdf (exponential-dist 2) -1) 0)
  (assert-equal (dist-cdf (exponential-dist 2) -1) 0)
  ; квантили
  (assert-equal (dist-quantile (uniform-dist 1 5) 1/4) 2)
  (assert-true (pt-zero? (dist-quantile (exponential-dist 2) 1/2) '(* 1/2 (log 2))))
  (assert-equal (dist-quantile (normal-dist 3 2) 1/2) 3)
  (assert-equal (dist-quantile (table-dist '(1 2 3) '(1/2 1/4 1/4)) 3/4) 2)
  (assert-equal (dist-quantile (gamma-dist 2 1) 1/2) '(quantile (gamma_dist 2 1) 1/2)))

(deftest "prob: ожидание функции E[g(X)], вероятность по плотности, свои распределения"
  (assert-equal (dist-expectation '(^ x 2) 'x (uniform-dist 0 1)) 1/3)
  (assert-equal (dist-expectation '(* x (- x 1)) 'x (poisson-dist 2)) 4)
  (assert-equal (dist-expectation '(^ x 2) 'x (normal-dist 0 1)) 1)
  (assert-true (pt-zero? (dist-expectation '(exp (* -1 x)) 'x (exponential-dist 1)) 1/2))
  ; плотность 3x² на [0,1]
  (let ((d (density-dist '(* 3 (^ x 2)) 'x 0 1)))
    (assert-equal (dist-mean d) 3/4)
    (assert-equal (dist-variance d) 3/80)
    (assert-equal (dist-prob d 0 1/2) 1/8)
    (assert-equal (dist-cdf d 1/2) 1/8)
    (assert-equal (dist-pdf d 2) 0)
    (assert-equal (dist-pdf d 1/2) 3/4))
  ; другая переменная в записи
  (assert-equal (dist-mean (density-dist '(* 2 t) 't 0 1)) 2/3)
  ; таблица
  (let ((d (table-dist '(1 2 3) '(1/2 1/4 1/4))))
    (assert-equal (dist-mean d) 7/4)
    (assert-equal (dist-variance d) 11/16)
    (assert-equal (dist-cdf d 2) 3/4)
    (assert-equal (dist-prob d 2 3) 1/2)
    (assert-equal (dist-pdf d 2) 1/4)
    (assert-equal (dist-pdf d 5) 0)
    (assert-equal (dist-expectation '(^ x 2) 'x d) 15/4)
    (assert-equal (dist-moment d 2) 15/4)
    (assert-true (pt-zero? (dist-mgf d 't) '(+ (* 1/2 (exp t)) (* 1/4 (exp (* 2 t))) (* 1/4 (exp (* 3 t))))))))

(deftest "prob: подделки — ненормированная плотность и неверные параметры не молчат"
  (assert-error (density-dist 'x 'x 0 1))                       ; интеграл 1/2
  (assert-error (density-dist '(* 2 x) 'x 0 2))                 ; интеграл 4
  (assert-error (density-dist '(+ 2 (* -4 x)) 'x 0 1))          ; интеграл 0 (и отрицательна)
  (assert-error (density-dist '(+ 3 (* -6 x)) 'x 0 1))          ; интеграл 0
  (assert-error (density-dist '(* 3 (+ 1 (* -2 x))) 'x 0 1))    ; интеграл 0
  (assert-error (density-dist '(* -1 (^ x 2)) 'x -1 1))         ; интеграл отрицателен
  (assert-error (density-dist '(* c x) 'x 0 1))                 ; интеграл c/2 ≠ 1
  (let ((msg (try (density-dist 'x 'x 0 1) (lambda (e) (error-message e)))))
    (assert-true (string-contains? msg "не 1")))
  ; интеграл 1, но плотность отрицательна: нормировка проходит, знак — нет
  (assert-error (density-dist '(* 3/2 (+ -1 (* 4 (^ x 2)))) 'x -1 1))
  (assert-error (table-dist '(1 2) '(1/2 1/3)))
  (assert-error (table-dist '(1 2) '(3/2 -1/2)))
  (assert-error (table-dist '(1 2 3) '(1/2 1/2)))
  (assert-error (binomial-dist 5 3/2))
  (assert-error (normal-dist 0 -1))
  (assert-error (poisson-dist 0))
  (assert-error (hypergeometric-dist 10 12 3))
  (assert-error (dist-pdf 'foo 1))
  (assert-error (dist-moment (normal-dist 0 1) -1))
  (assert-error (dist-quantile (normal-dist 0 1) 2)))

(deftest "prob: выборка — точные значения"
  (let ((xs '(2 4 4 4 5 5 7 9)))
    (assert-equal (sample-mean xs) 5)
    (assert-equal (sample-variance xs) 32/7)
    (assert-true (pt-zero? (sample-stddev xs) '(^ 32/7 1/2)))
    (assert-equal (sample-median xs) 9/2)
    (assert-equal (sample-median '(3 1 2)) 2)
    (assert-equal (sample-median '(5)) 5))
  (assert-equal (sample-mean '(1/2 1/3)) 5/12)
  ; квантиль, метод 7
  (assert-equal (quantile-sample '(1 2 3 4 5) 1/4) 2)
  (assert-equal (quantile-sample '(1 2 3 4) 1/2) 5/2)
  (assert-equal (quantile-sample '(1 2 3 4) 0) 1)
  (assert-equal (quantile-sample '(1 2 3 4) 1) 4)
  (assert-equal (quantile-sample '(7 1 3) 1/3) 7/3)          ; h = 2/3: 1 + 2/3·(3 − 1)
  ; ковариация и корреляция
  (assert-equal (sample-covariance '(1 2 3) '(2 4 7)) 5/2)
  (assert-true (pt-zero? (sample-correlation '(1 2 3) '(2 4 7)) '(* 5/2 (^ 19/3 -1/2))))   ; cov / (σx·σy): σx² = 1, σy² = 19/3
  (assert-equal (sample-correlation '(1 2 3) '(3 2 1)) -1)
  (assert-equal (sample-correlation '(1 2 3 4) '(2 4 6 8)) 1)
  ; МНК: (1,2) (2,3) (3,5) (4,4) → y = 3/2 + 4/5·x (у задания 7/10 — опечатка: Sxy = 4, Sxx = 5)
  (assert-equal (linear-regression '(1 2 3 4) '(2 3 5 4)) '(3/2 4/5))
  (assert-equal (linear-regression '(0 1 2) '(1 3 5)) '(1 2))
  ; частоты
  (assert-equal (frequencies '(3 1 2 2 3 3)) '((1 1) (2 2) (3 3)))
  (assert-equal (frequencies '(5 5)) '((5 2))))

(deftest "prob: выборка — подделки (один элемент, вырожденные данные, разная длина)"
  (assert-error (sample-variance '(5)))
  (assert-error (sample-stddev '(5)))
  (assert-error (sample-variance '()))
  (assert-error (sample-mean '()))
  (assert-error (sample-covariance '(1) '(2)))
  (assert-error (sample-covariance '(1 2) '(1 2 3)))
  (assert-error (sample-correlation '(1 1 1) '(1 2 3)))          ; нулевая дисперсия
  (assert-error (linear-regression '(2 2 2) '(1 2 3)))           ; все x одинаковы
  (assert-error (quantile-sample '(1 2 3) 3/2))
  (assert-error (sample-median '())))

(deftest "prob: полная вероятность и Байес"
  ; тест на редкую болезнь: распространённость 1 %, чувствительность 99 %, ложноположительные 5 %
  (assert-equal (total-probability '(1/100 99/100) '(99/100 5/100)) 297/5000)
  (assert-equal (bayes-posterior '(1/100 99/100) '(99/100 5/100)) '(1/6 5/6))
  ; три фабрики
  (assert-equal (bayes-posterior '(1/2 3/10 1/5) '(1/100 2/100 3/100)) '(5/17 6/17 6/17))
  ; невозможное свидетельство, невероятные априорные
  (assert-error (bayes-posterior '(1/2 1/2) '(0 0)))
  (assert-error (bayes-posterior '(1/2 1/3) '(1/2 1/2)))
  (assert-error (bayes-posterior '(1/2 1/2) '(3/2 1/2)))
  (assert-error (bayes-posterior '(1) '(1/2 1/2)))
  (assert-error (total-probability '(1/2 1/2) '(1/2))))

(deftest "prob: язык — распределения, операции, выборка"
  (assert-true (< (abs (- (eval-num (math-eval "cdf(normal_dist(0, 1), 1)")) 0.841344746068543)) 1e-12))
  (assert-equal (math-eval "pmf(binomial_dist(10, 1/2), 3)") 15/128)
  (assert-equal (math-eval "pdf(binomial_dist(10, 1/2), 3)") 15/128)
  (assert-true (pt-zero? (math-eval "cdf(poisson_dist(2), 2)") '(* 5 (exp -2))))
  (assert-true (pt-zero? (math-eval "prob(exponential_dist(1/2), 4, inf)") '(exp -2)))
  (assert-equal (math-eval "mean(normal_dist(m, s))") 'm)
  (assert-equal (math-eval "variance(uniform_dist(0, 6))") 3)
  (assert-equal (math-eval "moment(normal_dist(0, 1), 4)") 3)
  (assert-equal (math-eval "expectation(x^2, x, uniform_dist(0, 1))") 1/3)
  (assert-equal (math-eval "mean([2, 4, 4, 4, 5, 5, 7, 9])") 5)
  (assert-equal (math-eval "sample_variance([2, 4, 4, 4, 5, 5, 7, 9])") 32/7)
  (assert-equal (math-eval "median([3, 1, 2, 4])") 5/2)
  (assert-equal (tensor->list (math-eval "linear_regression([1, 2, 3, 4], [2, 3, 5, 4])")) '(3/2 4/5))
  (assert-equal (tensor->list (math-eval "bayes([1/100, 99/100], [99/100, 5/100])")) '(1/6 5/6))
  (assert-equal (math-eval "mean(table_dist([1, 2, 3], [1/2, 1/4, 1/4]))") 7/4)
  (assert-equal (math-eval "variance(density_dist(3*x^2, x, 0, 1))") 3/80)
  (assert-equal (math-eval "prob(normal_dist(0, 1), -inf, inf)") 1)
  (assert-error (math-eval "density_dist(x, x, 0, 1)"))
  (assert-error (math-eval "sample_variance([5])"))
  (assert-error (math-eval "variance([1, 2, 3])"))
  ; прежние имена не сломаны
  (assert-equal (math-eval "binomial(10, 3)") 120)
  (assert-equal (math-eval "gamma(5)") 24))
