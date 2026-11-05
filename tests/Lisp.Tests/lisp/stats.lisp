; stats.lisp — тесты шага PROB.b: математическая статистика.
; Оракулы: (1) квантили — общеизвестные табличные значения (допуск 1e-8) и обратная проверка cdf(quantile(p)) = p;
; (2) cdf — замкнутые формулы (χ² с 2 и 4 степенями, Стьюдент с 1 и 2, F(2, 2)) и независимое численное интегрирование
; плотности (Симпсон по dist-pdf); (3) скобка квантиля содержит табличное значение; (4) критерии — независимый расчёт
; p-значения (Симпсон, замкнутая форма через erf); (5) MLE — производная ln L в оценке равна нулю, а в сдвинутой точке нет;
; (6) подделки: p вне (0, 1), выборка из одного элемента, отрицательные частоты, несогласованные суммы.

(define (st-close? a b tol) (< (abs (- a b)) tol))

; Симпсон по плотности распределения: ∫_a^b pdf, n чётное
(define (st-simpson d a b n)
  (let ((h (/ (- (* 1.0 b) a) n)))
    (let loop ((i 0) (acc 0.0))
      (if (> i n)
          (* acc (/ h 3.0))
          (let* ((x (+ a (* i h)))
                 (w (cond ((or (= i 0) (= i n)) 1.0) ((= (mod i 2) 1) 4.0) (else 2.0))))
            (loop (+ i 1) (+ acc (* w (eval-num (dist-pdf d x))))))))))

(define st-xs '(2 4 4 4 5 5 7 9))
(define st-ys '(1 3 3 5 6 6 8 12))

(deftest "stats: квантили — табличные значения (допуск 1e-8)"
  (assert-true (st-close? (dist-quantile-num (normal-dist 0 1) 0.975) 1.959963984540054 1e-8))
  (assert-true (st-close? (dist-quantile-num (student-dist 10) 0.975) 2.228138851986274 1e-8))
  (assert-true (st-close? (dist-quantile-num (chi2-dist 5) 0.95) 11.0704976935164 1e-8))
  (assert-true (st-close? (dist-quantile-num (f-dist 3 10) 0.95) 3.708264819 1e-8))
  (assert-true (st-close? (dist-quantile-num (student-dist 7) 0.975) 2.364624251592785 1e-8))
  (assert-true (st-close? (dist-quantile-num (chi2-dist 7) 0.025) 1.689869180677 1e-8))
  (assert-true (st-close? (dist-quantile-num (chi2-dist 7) 0.975) 16.01276427462 1e-8))
  ; символьный/точный путь через quantile-dist: точные квантили остаются точными, числовые — числами
  (assert-equal (quantile-dist (normal-dist 3 1) 1/2) 3)
  (assert-true (st-close? (quantile-dist (normal-dist 10 2) 0.975) (+ 10 (* 2 1.959963984540054)) 1e-8))
  (assert-true (st-close? (quantile-dist (student-dist 10) 39/40) 2.228138851986274 1e-8))
  (assert-equal (quantile-dist (exponential-dist 2) 1/2) (simplify '(* 1/2 (log 2))))
  (assert-true (pair? (quantile-dist (normal-dist 'm 1) 0.9))))

(deftest "stats: cdf(quantile(p)) = p и монотонность на сетке распределений и p"
  (for-each (lambda (d)
              (let loop ((ps '(0.001 0.01 0.1 0.25 0.5 0.75 0.9 0.99 0.999)) (prev -1e300))
                (if (not (null? ps))
                    (let ((q (dist-quantile-num d (car ps))))
                      (assert-true (st-close? (dist-cdf-num d q) (car ps) 1e-10))
                      (assert-true (> q prev))
                      (loop (cdr ps) q)))))
            (list (normal-dist 0 1) (normal-dist -3 5/2) (student-dist 1) (student-dist 3) (student-dist 30)
                  (chi2-dist 1) (chi2-dist 5) (chi2-dist 40) (f-dist 1 1) (f-dist 3 10) (f-dist 12 4))))

(deftest "stats: скобка квантиля — доказанный отрезок, содержит эталон, ширина ≤ 2e-10"
  (for-each (lambda (c)
              (let* ((b (dist-quantile-bounds (car c) (cadr c))) (lo (car b)) (hi (cadr b)))
                (assert-true (<= lo (caddr c)))
                (assert-true (<= (caddr c) hi))
                (assert-true (< (- hi lo) 2e-10))))
            (list (list (normal-dist 0 1) 0.975 1.959963984540054)
                  (list (student-dist 10) 0.975 2.228138851986274)
                  (list (student-dist 7) 0.975 2.364624251592785)
                  (list (chi2-dist 5) 0.95 11.0704976935164))))

(deftest "stats: cdf — замкнутые формулы"
  ; χ²₂: 1 − e^{−x/2}; χ²₄: 1 − e^{−x/2}(1 + x/2)
  (for-each (lambda (x)
              (assert-true (st-close? (dist-cdf-num (chi2-dist 2) x) (- 1 (exp (* -0.5 x))) 1e-12))
              (assert-true (st-close? (dist-cdf-num (chi2-dist 4) x) (- 1 (* (exp (* -0.5 x)) (+ 1 (* 0.5 x)))) 1e-12))
              ; F(2, 2): x/(1 + x)
              (assert-true (st-close? (dist-cdf-num (f-dist 2 2) x) (/ x (+ 1 x)) 1e-12)))
            '(0.1 0.5 1.0 2.5 7.0 20.0))
  ; Стьюдент ν = 1: ½ + atan(t)/π; ν = 2: ½ + t/(2√(2 + t²))
  (for-each (lambda (t)
              (assert-true (st-close? (dist-cdf-num (student-dist 1) t) (+ 0.5 (/ (atan t) 3.141592653589793)) 1e-12))
              (assert-true (st-close? (dist-cdf-num (student-dist 2) t) (+ 0.5 (/ t (* 2 (sqrt (+ 2 (* t t)))))) 1e-12)))
            '(-5.0 -1.0 -0.2 0.0 0.7 3.0 25.0))
  ; Φ(1)
  (assert-true (st-close? (dist-cdf-num (normal-dist 0 1) 1) 0.8413447460685429 1e-12)))

(deftest "stats: cdf — независимое численное интегрирование плотности (Симпсон)"
  (assert-true (st-close? (dist-cdf-num (student-dist 3) 1.7) (+ 0.5 (st-simpson (student-dist 3) 0 1.7 400)) 1e-9))
  (assert-true (st-close? (dist-cdf-num (student-dist 10) -2.2) (- 0.5 (st-simpson (student-dist 10) 0 2.2 400)) 1e-9))
  (assert-true (st-close? (dist-cdf-num (normal-dist 1 2) 2.5) (+ 0.5 (st-simpson (normal-dist 1 2) 1 2.5 400)) 1e-9))
  (assert-true (st-close? (dist-cdf-num (chi2-dist 6) 4.3) (st-simpson (chi2-dist 6) 0 4.3 400) 1e-8))
  (assert-true (st-close? (dist-cdf-num (f-dist 6 10) 2.1) (st-simpson (f-dist 6 10) 0 2.1 400) 1e-8))
  (assert-true (st-close? (dist-cdf-num (f-dist 6 10) 4.0) (st-simpson (f-dist 6 10) 0 4.0 800) 1e-8))
  ; заявленная граница ошибки — не меньше фактической и мала
  (let ((r (dist-cdf-cert (student-dist 10) 2.228138851986274)))
    (assert-true (< (cadr r) 1e-12))
    (assert-true (<= (abs (- (car r) 0.975)) (+ (cadr r) 1e-15)))))

(deftest "stats: f_dist — среднее, дисперсия, границы существования"
  (assert-equal (dist-mean (f-dist 3 10)) 5/4)
  (assert-equal (dist-variance (f-dist 3 10)) 275/144)
  (assert-error (dist-mean (f-dist 3 2)))
  (assert-equal (dist-variance (f-dist 3 4)) 'inf)
  (assert-error (f-dist 0 3))
  (assert-error (f-dist 3 -1))
  ; F(d1, d2) и 1/F(d2, d1): cdf(x; d1, d2) + cdf(1/x; d2, d1) = 1
  (assert-true (st-close? (+ (dist-cdf-num (f-dist 7 7) 16/41) (dist-cdf-num (f-dist 7 7) 41/16)) 1 1e-12))
  (assert-true (st-close? (+ (dist-cdf-num (f-dist 3 10) 1.7) (dist-cdf-num (f-dist 10 3) (/ 1 1.7))) 1 1e-12)))

(deftest "stats: подделки квантилей и cdf"
  (assert-error (dist-quantile-num (normal-dist 0 1) 0))
  (assert-error (dist-quantile-num (normal-dist 0 1) 1))
  (assert-error (dist-quantile-num (student-dist 5) 1.5))
  (assert-error (dist-quantile-num (chi2-dist 5) -0.1))
  (assert-error (quantile-dist (chi2-dist 5) 2))
  (assert-error (dist-quantile-num (chi2-dist 5) 1e-15))      ; слишком близко к 0: точность не гарантируется
  (assert-error (dist-quantile-num (exponential-dist 2) 0.5)) ; не поддерживается численной частью (есть точный quantile)
  (assert-error (dist-cdf-num (student-dist 5) 'a)))

(deftest "stats: MLE и метод моментов"
  (let ((n (mle 'normal st-xs)))
    (assert-equal (stat-get n 'mu) 5)
    (assert-equal (stat-get n 'sigma2) 4)                      ; смещённая: делитель n
    (assert-equal (stat-get n 'score_check) #t))
  (assert-equal (stat-get (mle 'exponential st-xs) 'lambda) 1/5)
  (assert-equal (stat-get (mle 'poisson st-xs) 'lambda) 5)
  (assert-equal (stat-get (mle 'binomial st-xs 10) 'p) 1/2)
  (assert-equal (stat-get (mle 'uniform st-xs) 'a) 2)
  (assert-equal (stat-get (mle 'uniform st-xs) 'b) 9)
  (for-each (lambda (f) (assert-equal (mle-check f st-xs 10) #t)) '(normal exponential poisson binomial))
  ; производная ln L в оценке = 0, в сдвинутой точке — нет и знак верный (ℓ вогнута: score убывает по параметру)
  (assert-equal (mle-score 'normal st-xs '(5 4)) '(0 0))
  (assert-true (> (car (mle-score 'normal st-xs '(4 4))) 0))
  (assert-true (< (car (mle-score 'normal st-xs '(6 4))) 0))
  (assert-true (> (cadr (mle-score 'normal st-xs '(5 3))) 0))
  (assert-true (< (cadr (mle-score 'normal st-xs '(5 5))) 0))
  (assert-equal (mle-score 'exponential st-xs '(1/5)) '(0))
  (assert-true (> (car (mle-score 'exponential st-xs '(1/6))) 0))
  (assert-true (< (car (mle-score 'poisson st-xs '(6))) 0))
  (assert-true (> (car (mle-score 'binomial st-xs '(2/5) 10)) 0))
  ; дробные данные: производная нулевая до округления
  (assert-equal (mle-check 'normal '(0.5 1.25 2.0 3.75) ) #t)
  ; метод моментов
  (let ((m (moments-estimate 'normal st-xs)))
    (assert-equal (stat-get m 'mu) 5)
    (assert-equal (stat-get m 'sigma2) 4))
  (assert-equal (stat-get (moments-estimate 'exponential st-xs) 'lambda) 1/5)
  (assert-equal (stat-get (moments-estimate 'binomial st-xs 10) 'p) 1/2)
  (let ((u (moments-estimate 'uniform st-xs)))                  ; a, b = 5 ∓ √(3·4)
    (assert-true (st-close? (eval-num (stat-get u 'a)) (- 5 (sqrt 12.0)) 1e-12))
    (assert-true (st-close? (eval-num (stat-get u 'b)) (+ 5 (sqrt 12.0)) 1e-12)))
  (let ((g (moments-estimate 'gamma st-xs)))                    ; k = x̄²/v, θ = v/x̄
    (assert-equal (stat-get g 'k) 25/4)
    (assert-equal (stat-get g 'theta) 4/5)))

(deftest "stats: подделки MLE"
  (assert-error (mle 'normal '(3 3 3)))                         ; вырожденная σ̂² = 0
  (assert-error (mle 'poisson '(1.5 2)))                        ; не целые
  (assert-error (mle 'poisson '(0 0)))                          ; граница
  (assert-error (mle 'binomial st-xs))                          ; n не задано
  (assert-error (mle 'binomial '(3 12) 10))                     ; наблюдение больше n
  (assert-error (mle 'exponential '(1 -2)))
  (assert-error (mle 'weibull st-xs))
  (assert-error (mle 'normal '()))
  (assert-error (mle-score 'normal st-xs 5)))

(deftest "stats: доверительный интервал среднего, σ неизвестна — два независимых пути"
  (let* ((r (confint-mean st-xs)) (iv (stat-get r 'interval))
         ; путь 1: t из табличного значения и s из sample-stddev
         (t7 2.364624251592785) (s (eval-num (sample-stddev st-xs)))
         (h (/ (* t7 s) (sqrt 8.0))))
    (assert-true (st-close? (car iv) (- 5 h) 1e-9))
    (assert-true (st-close? (cadr iv) (+ 5 h) 1e-9))
    ; путь 2: √(32/7)/√8 = √(4/7) — точная алгебра
    (assert-true (st-close? (stat-get r 'std_error) (eval-num '(^ (/ 4 7) 1/2)) 1e-12))
    (assert-true (st-close? (stat-get r 'quantile) t7 1e-9))
    (assert-equal (stat-get r 'df) 7)
    (assert-true (< (stat-get r 'quantile_error) 1e-10))
    ; симметрия вокруг среднего
    (assert-true (st-close? (+ (car iv) (cadr iv)) 10 1e-9)))
  ; уровень 0.99 шире 0.95
  (let ((a (stat-get (confint-mean st-xs 0.95) 'interval)) (b (stat-get (confint-mean st-xs 0.99) 'interval)))
    (assert-true (< (car b) (car a)))
    (assert-true (> (cadr b) (cadr a))))
  (assert-true (st-close? (stat-get (confint-mean st-xs 19/20) 'quantile) 2.364624251592785 1e-9)))

(deftest "stats: интервалы — σ известна, дисперсия, доля"
  (let* ((r (confint-mean-sigma st-xs 2)) (iv (stat-get r 'interval)) (h (* 1.959963984540054 (/ 2 (sqrt 8.0)))))
    (assert-true (st-close? (car iv) (- 5 h) 1e-9))
    (assert-true (st-close? (cadr iv) (+ 5 h) 1e-9)))
  ; (n − 1)s² = 32; χ²_{0.975, 7} = 16.01276427462, χ²_{0.025, 7} = 1.689869180677
  (let ((iv (stat-get (confint-variance st-xs) 'interval)))
    (assert-true (st-close? (car iv) (/ 32 16.01276427462) 1e-8))
    (assert-true (st-close? (cadr iv) (/ 32 1.689869180677) 1e-8)))
  ; доля 40/100: Вальд 0.4 ∓ 1.96·√(0.24/100); Уилсон — известный интервал (0.3094, 0.4980)
  (let ((iv (stat-get (confint-proportion 40 100) 'interval)) (h (* 1.959963984540054 (sqrt 0.0024))))
    (assert-true (st-close? (car iv) (- 0.4 h) 1e-9))
    (assert-true (st-close? (cadr iv) (+ 0.4 h) 1e-9)))
  (let ((iv (stat-get (confint-wilson 40 100) 'interval)))
    (assert-true (st-close? (car iv) 0.30940 1e-4))
    (assert-true (st-close? (cadr iv) 0.49800 1e-4)))
  ; граничная доля: интервал остаётся в [0, 1]
  (let ((iv (stat-get (confint-proportion 0 20) 'interval)))
    (assert-true (and (>= (car iv) 0) (<= (cadr iv) 1)))))

(deftest "stats: подделки интервалов"
  (assert-error (confint-mean '(5)))
  (assert-error (confint-mean st-xs 1.5))
  (assert-error (confint-mean st-xs 0))
  (assert-error (confint-mean '(a b c)))
  (assert-error (confint-mean-sigma st-xs -1))
  (assert-error (confint-variance '(1)))
  (assert-error (confint-proportion 11 10))
  (assert-error (confint-proportion -1 10))
  (assert-error (confint-wilson 3 0)))

(deftest "stats: t-критерий одной выборки — p независимо через Симпсона по плотности"
  (let* ((r (t-test st-xs 3)))
    ; t = (5 − 3)/√(4/7) = √7, df = 7
    (assert-true (st-close? (stat-get r 'statistic) (sqrt 7.0) 1e-12))
    (assert-equal (stat-get r 'df) 7)
    (assert-true (st-close? (stat-get r 'p_value)
                            (- 1 (* 2 (st-simpson (student-dist 7) 0 (sqrt 7.0) 800))) 1e-9))
    (assert-equal (stat-get r 'reject) #t)
    (assert-equal (stat-get r 'decision) "отвергаем H0"))
  ; односторонние p: p_less + p_greater = 1, двусторонний = 2·min
  (let ((l (stat-get (t-test st-xs 3 'less) 'p_value)) (g (stat-get (t-test st-xs 3 'greater) 'p_value))
        (two (stat-get (t-test st-xs 3) 'p_value)))
    (assert-true (st-close? (+ l g) 1 1e-12))
    (assert-true (st-close? two (* 2 (min l g)) 1e-12)))
  ; H0: μ = 5 — статистика 0, p = 1, не отвергаем
  (let ((r (t-test st-xs 5)))
    (assert-true (st-close? (stat-get r 'p_value) 1 1e-12))
    (assert-equal (stat-get r 'reject) #f))
  ; α задаётся: p = 0.0331 отвергается при 0.05 и не отвергается при 0.01
  (assert-equal (stat-get (t-test st-xs 3 0.01) 'reject) #f))

(deftest "stats: двухвыборочные и парный t-критерии"
  (let* ((w (t-test-two st-xs st-ys)) (p (t-test-pooled st-xs st-ys)) (d (t-test-paired st-xs st-ys)))
    ; разность средних −1/2·… : x̄ = 5, ȳ = 5.5; s₁² = 32/7, s₂² = 154/14 − … проверяем по определению
    (let* ((v1 (eval-num (sample-variance st-xs))) (v2 (eval-num (sample-variance st-ys)))
           (tp (/ (- 5 (eval-num (sample-mean st-ys))) (sqrt (* (/ (+ (* 7 v1) (* 7 v2)) 14) (/ 2 8.0)))))
           (tw (/ (- 5 (eval-num (sample-mean st-ys))) (sqrt (+ (/ v1 8) (/ v2 8))))))
      (assert-true (st-close? (stat-get p 'statistic) tp 1e-12))
      (assert-true (st-close? (stat-get w 'statistic) tw 1e-12)))
    (assert-equal (stat-get p 'df) 14)
    (assert-true (<= (stat-get w 'df) 14))
    (assert-true (> (stat-get w 'df) 7))
    ; p pooled — независимый расчёт по плотности Стьюдента
    (assert-true (st-close? (stat-get p 'p_value)
                            (- 1 (* 2 (st-simpson (student-dist 14) 0 (abs (stat-get p 'statistic)) 800))) 1e-9))
    ; парный = одновыборочный на разностях: x − y = (1 1 1 −1 −1 −1 −1 −3), среднее −1/2
    (assert-equal (stat-get d 'mean) -1/2)
    (assert-true (st-close? (stat-get d 'p_value) (stat-get (t-test (map2 - st-xs st-ys) 0) 'p_value) 1e-15))
    (assert-equal (stat-get d 'statistic) -1.0))
  ; разные размеры; выборка против себя же — статистика 0
  (let ((r (t-test-two st-xs '(10 11 12 13 14))))
    (assert-equal (stat-get r 'reject) #t))
  (assert-true (st-close? (stat-get (t-test-two st-xs st-xs) 'p_value) 1 1e-12)))

(deftest "stats: χ²-согласия — честная кость"
  ; частоты 16, 18, 16, 14, 12, 24 (n = 100); E = 50/3: χ² = Σ(O − E)²/E = 128/25 = 5.12, df = 5
  ; (в формулировке задачи ошибочно 5.6; пересчёт: Σ(O − 50/3)² = 768/9, ·3/50 = 128/25)
  (let* ((o '(16 18 16 14 12 24)) (e '(50/3 50/3 50/3 50/3 50/3 50/3)) (r (chi2-gof o e)))
    (assert-equal (stat-get r 'statistic) 128/25)
    (assert-equal (stat-get r 'df) 5)
    ; p для нечётного df = 5: Q = erfc(√(x/2)) + √(2x/π)·e^{−x/2}·(1 + x/3) — независимая замкнутая форма
    (let* ((x 5.12) (erfc (- 1 (eval-num (list 'erf (sqrt (/ x 2))))))
           (q (+ erfc (* (sqrt (/ (* 2 x) 3.141592653589793)) (exp (* -0.5 x)) (+ 1 (/ x 3))))))
      (assert-true (st-close? (stat-get r 'p_value) q 1e-11))
      (assert-true (st-close? (stat-get r 'p_value) 0.4014 1e-4)))
    (assert-equal (stat-get r 'reject) #f))
  ; явно смещённая кость отвергается
  (assert-equal (stat-get (chi2-gof '(40 10 10 10 10 20) '(100/6 100/6 100/6 100/6 100/6 100/6)) 'reject) #t)
  ; ddof: при одном оценённом параметре df на единицу меньше
  (assert-equal (stat-get (chi2-gof '(10 20 30) '(20 20 20) 1) 'df) 1)
  (assert-equal (stat-get (chi2-gof '(10 20 30) '(20 20 20)) 'df) 2)
  ; χ²₂: p = e^{−χ²/2} (замкнутая форма)
  (let ((r (chi2-gof '(10 20 30) '(20 20 20))))
    (assert-equal (stat-get r 'statistic) 10)
    (assert-true (st-close? (stat-get r 'p_value) (exp -5.0) 1e-12))))

(deftest "stats: χ²-независимости, таблица 2×2"
  (let ((r (chi2-independence '((10 20) (30 40)))))
    ; E = ((12 18) (28 42)); χ² = 4/12 + 4/18 + 4/28 + 4/42 = 50/63
    (assert-equal (stat-get r 'statistic) 50/63)
    (assert-equal (stat-get r 'df) 1)
    (assert-equal (stat-get r 'expected) '((12 18) (28 42)))
    ; df = 1: p = erfc(√(x/2))
    (assert-true (st-close? (stat-get r 'p_value) (- 1 (eval-num (list 'erf (sqrt (/ (eval-num 50/63) 2))))) 1e-11)))
  ; Йейтс: Σ(|O − E| − ½)²/E = 25/56
  (let ((r (chi2-independence '((10 20) (30 40)) 'yates)))
    (assert-equal (stat-get r 'statistic) 25/56)
    (assert-equal (stat-get r 'df) 1))
  ; 2×3: df = 2
  (let ((r (chi2-independence '((20 30 50) (30 30 40)))))
    (assert-equal (stat-get r 'df) 2)
    (assert-true (and (>= (stat-get r 'p_value) 0) (<= (stat-get r 'p_value) 1))))
  ; сильная зависимость — отвергаем
  (assert-equal (stat-get (chi2-independence '((90 10) (10 90))) 'reject) #t)
  ; независимая таблица — статистика 0
  (assert-equal (stat-get (chi2-independence '((10 20) (20 40))) 'statistic) 0))

(deftest "stats: F-критерий равенства дисперсий"
  (let ((r (f-test-variances st-xs st-ys)))
    (assert-equal (stat-get r 'statistic) 16/41)
    (assert-equal (stat-get r 'df) '(7 7))
    ; двусторонний p = 2·min(F(f), 1 − F(f)); симметрия F(7,7): F(f) + F(1/f) = 1
    (let ((c (dist-cdf-num (f-dist 7 7) 16/41)))
      (assert-true (st-close? (stat-get r 'p_value) (* 2 (min c (- 1 c))) 1e-12)))
    (assert-equal (stat-get r 'reject) #f))
  ; очень разные дисперсии отвергаются
  (assert-equal (stat-get (f-test-variances '(1 2 3 4 5 6 7 8) '(10 30 50 70 90 110 130 150)) 'reject) #t)
  (assert-true (st-close? (stat-get (f-test-variances st-xs st-xs) 'p_value) 1 1e-12)))

(deftest "stats: подделки критериев"
  (assert-error (t-test '(5) 3))
  (assert-error (t-test '(5 5 5) 3))                            ; нулевая дисперсия
  (assert-error (t-test st-xs 'a))
  (assert-error (t-test st-xs 3 0))                             ; α вне (0, 1)
  (assert-error (t-test-two '(1) '(2 3)))
  (assert-error (t-test-paired '(1 2 3) '(1 2)))
  (assert-error (chi2-independence '((10 -20) (30 40))))
  (assert-error (chi2-independence '((10 20))))
  (assert-error (chi2-independence '((10 20) (0 0))))          ; нулевая строка
  (assert-error (chi2-independence '((10 20 30) (30 40 50)) 'yates))
  (assert-error (chi2-gof '(16 18) '(20 20)))                   ; суммы различаются
  (assert-error (chi2-gof '(16 -18) '(1 -3)))
  (assert-error (chi2-gof '(10 30) '(20 20) 1))                 ; df = 0
  (assert-error (f-test-variances '(1) '(2 3)))
  (assert-error (f-test-variances '(1 1 1) '(2 3 4)))
  (assert-error (stat-get (t-test st-xs 3) 'nosuch)))

(deftest "stats: p-значения всегда в [0, 1], вывод согласован с α"
  (for-each (lambda (r)
              (let ((p (stat-get r 'p_value)))
                (assert-true (and (>= p 0) (<= p 1)))
                (assert-equal (stat-get r 'reject) (< p (stat-get r 'alpha)))))
            (list (t-test st-xs 100) (t-test st-xs 5) (t-test st-xs 4.9 'greater) (t-test st-xs -50 'less)
                  (t-test-two st-xs st-ys) (t-test-pooled st-xs st-ys 0.1)
                  (chi2-gof '(1000 10) '(505 505)) (chi2-independence '((500 1) (1 500)))
                  (f-test-variances st-xs st-ys 0.2) (f-test-variances st-ys st-xs 'greater))))
