; prob.lisp — Шаг PROB: теория вероятностей и математическая статистика (точные символьные ответы).
;
; Распределение — ДАННЫЕ: выражение-голова с параметрами, например (normal_dist 0 1), (binomial_dist 10 1/2).
; Конструкторы проверяют параметры (числовые — строго, символьные принимаются) и не меняют форму.
; Свои распределения: (table_dist (v₁ …) (p₁ …)) — дискретное по таблице; (density_dist f x a b) — непрерывное
; по плотности f(x) на [a, b]. Конструктор своего распределения ПРОВЕРЯЕТ нормировку: интеграл/сумма плотности
; считается через integrate/sum и должен быть равен 1 — иначе ошибка «интеграл = …, не 1» (тихих вероятностей нет;
; не вычислился интеграл — тоже ошибка, а не молчаливое согласие).
;
; Операции (pdf/pmf, cdf, prob, expectation, moment, mgf) считаются ОБЩИМ движком через sum (дискретные,
; конечная числовая граница — прямая сумма) и integrate (непрерывные) по плотности; не вычислилось — невычисленная
; форма (операция d …), не ошибка. Табличные значения среднего, дисперсии и mgf встроенных распределений (dist-mean,
; dist-variance, dist-mgf) сверяются в тестах с общим движком (dist-expectation). Нормальное cdf — через erf.
; Бесконечные дискретные суммы (Пуассон, геометрическое) summation не берёт — общий движок отвечает невычисленной
; формой; табличное среднее/дисперсия тестами сверяются численно (частичные суммы).
;
; Выборка: sample-variance — несмещённая (n − 1), covariance — тоже n − 1; quantile-sample — метод 7 (R, Excel):
; h = (n − 1)·q, линейная интерполяция между порядковыми статистиками h⌊⌋ и ⌊h⌋ + 1. Выборка из одного элемента
; для дисперсии/ковариации — ошибка (а не 0 и не деление на 0).

(module prob
  (export bernoulli-dist binomial-dist poisson-dist geometric-dist uniform-discrete hypergeometric-dist
          uniform-dist normal-dist exponential-dist gamma-dist beta-dist chi2-dist student-dist
          table-dist density-dist dist? dist-support dist-pdf dist-cdf dist-prob dist-mean dist-variance dist-stddev
          dist-moment dist-expectation dist-mgf dist-quantile dist-mass dist-check
          sample-mean sample-variance sample-stddev sample-median quantile-sample sample-covariance sample-correlation
          linear-regression frequencies bayes-posterior total-probability))

; ---------- общее ----------

(define pb-discrete-names '(bernoulli_dist binomial_dist poisson_dist geometric_dist uniform_discrete hypergeometric_dist))
(define pb-continuous-names '(uniform_dist normal_dist exponential_dist gamma_dist beta_dist chi2_dist student_dist))

(define (pb-err name msg) (error (string-append name ": " msg)))
(define (pb-req ok name msg) (if ok #t (pb-err name msg)))

(define (dist? d)
  (and (pair? d)
       (or (member? (car d) pb-discrete-names) (member? (car d) pb-continuous-names)
           (equal? (car d) 'table_dist) (equal? (car d) 'density_dist))
       #t))

(define (pb-need-dist d name) (pb-req (dist? d) name "ожидается распределение (normal_dist(0, 1), binomial_dist(10, 1/2), …)"))

(define (pb-simp e) (simplify e))

; граница диапазона: число, inf, -inf или выражение; (* -1 inf) читается как -inf
(define (pb-bound b)
  (cond ((equal? b '(* -1 inf)) '-inf) (else b)))
(define (pb-inf? b) (or (equal? b 'inf) (equal? b '-inf)))

(define (pb-has? e s) (contains-sym? e s))

; значение выражения при x := v
(define (pb-at f x v) (pb-simp (subst (list x v) f)))

; число ли и не float-мусор: проверки параметров только для чисел
(define (pb-num-ok? p pred) (or (not (number? p)) (pred p)))

; ---------- конструкторы ----------

(define (bernoulli-dist p)
  (pb-req (pb-num-ok? p (lambda (q) (and (>= q 0) (<= q 1)))) "bernoulli_dist" "p должно лежать в [0, 1]")
  (list 'bernoulli_dist p))

(define (binomial-dist n p)
  (pb-req (pb-num-ok? n (lambda (q) (and (integer? q) (>= q 0)))) "binomial_dist" "n — целое ≥ 0")
  (pb-req (pb-num-ok? p (lambda (q) (and (>= q 0) (<= q 1)))) "binomial_dist" "p должно лежать в [0, 1]")
  (list 'binomial_dist n p))

(define (poisson-dist l)
  (pb-req (pb-num-ok? l (lambda (q) (> q 0))) "poisson_dist" "λ > 0")
  (list 'poisson_dist l))

(define (geometric-dist p)
  (pb-req (pb-num-ok? p (lambda (q) (and (> q 0) (<= q 1)))) "geometric_dist" "p должно лежать в (0, 1]")
  (list 'geometric_dist p))

(define (uniform-discrete a b)
  (pb-req (pb-num-ok? a integer?) "uniform_discrete" "a — целое")
  (pb-req (pb-num-ok? b integer?) "uniform_discrete" "b — целое")
  (pb-req (or (not (number? a)) (not (number? b)) (<= a b)) "uniform_discrete" "a ≤ b")
  (list 'uniform_discrete a b))

(define (hypergeometric-dist nn kk n)
  (pb-req (and (integer? nn) (integer? kk) (integer? n)) "hypergeometric_dist" "N, K, n — целые числа")
  (pb-req (and (>= kk 0) (<= kk nn) (>= n 0) (<= n nn)) "hypergeometric_dist" "0 ≤ K ≤ N и 0 ≤ n ≤ N")
  (list 'hypergeometric_dist nn kk n))

(define (uniform-dist a b)
  (pb-req (or (not (number? a)) (not (number? b)) (< a b)) "uniform_dist" "a < b")
  (list 'uniform_dist a b))

(define (normal-dist m s)
  (pb-req (pb-num-ok? s (lambda (q) (> q 0))) "normal_dist" "σ > 0")
  (list 'normal_dist m s))

(define (exponential-dist l)
  (pb-req (pb-num-ok? l (lambda (q) (> q 0))) "exponential_dist" "λ > 0")
  (list 'exponential_dist l))

(define (gamma-dist k th)
  (pb-req (pb-num-ok? k (lambda (q) (> q 0))) "gamma_dist" "k > 0")
  (pb-req (pb-num-ok? th (lambda (q) (> q 0))) "gamma_dist" "θ > 0")
  (list 'gamma_dist k th))

(define (beta-dist a b)
  (pb-req (pb-num-ok? a (lambda (q) (> q 0))) "beta_dist" "a > 0")
  (pb-req (pb-num-ok? b (lambda (q) (> q 0))) "beta_dist" "b > 0")
  (list 'beta_dist a b))

(define (chi2-dist k)
  (pb-req (pb-num-ok? k (lambda (q) (and (integer? q) (>= q 1)))) "chi2_dist" "k — целое ≥ 1")
  (list 'chi2_dist k))

(define (student-dist nu)
  (pb-req (pb-num-ok? nu (lambda (q) (> q 0))) "student_dist" "ν > 0")
  (list 'student_dist nu))

; table_dist(значения, вероятности): вероятности ≥ 0, сумма точно 1
(define (table-dist vs ps)
  (pb-req (and (list? vs) (list? ps) (= (length vs) (length ps)) (not (null? vs)))
          "table_dist" "ожидаются два непустых списка одной длины: значения и вероятности")
  (pb-req (every? number? ps) "table_dist" "вероятности должны быть числами")
  (pb-req (every? (lambda (p) (>= p 0)) ps) "table_dist" "вероятность отрицательна")
  (let ((s (apply + ps)))
    (pb-req (equal? s 1) "table_dist" (string-append "сумма вероятностей = " (to-string s) ", не 1")))
  (list 'table_dist vs ps))

; density_dist(f, x, a, b): плотность f(x) на [a, b]; нормировка и неотрицательность проверяются
(define (density-dist f x a0 b0)
  (let ((a (pb-bound a0)) (b (pb-bound b0)))
    (pb-req (symbol? x) "density_dist" "вторым аргументом ожидается переменная")
    (let ((d (list 'density_dist f x a b)))
      (let ((m (dist-mass d)))
        (cond ((and (number? m) (not (= m 1)))
               (pb-err "density_dist" (string-append "интеграл плотности = " (to-string m) ", не 1")))
              ((and (not (number? m)) (not (pb-one? m)))
               (pb-err "density_dist" (string-append "интеграл плотности = " (to-string m) ", не 1 (или не вычислен)")))
              (else
               (pb-req (pb-nonneg-sampled? f x a b) "density_dist" "плотность принимает отрицательное значение")
               d))))))

; m = 1: точно или (для иррационального вида) численно до 1e-12 — ответ уже не молчаливый, интеграл вычислен
(define (pb-one? m)
  (if (equal? m 1)
      #t
      (let ((v (try (eval-num m) (lambda (e) #f))))
        (and (number? v) (< (abs (- v 1)) 1/1000000000000)))))

; на конечном носителе: 41 точка не даёт отрицательного значения (на бесконечном — не проверяется)
(define (pb-nonneg-sampled? f x a b)
  (if (and (number? a) (number? b))
      (let loop ((i 0))
        (if (> i 40)
            #t
            (let ((v (try (eval-num (pb-at f x (+ a (* (- b a) (/ i 40))))) (lambda (e) 0))))
              (if (and (number? v) (< v -1/1000000000000)) #f (loop (+ i 1))))))
      #t))

; ---------- носитель и плотность ----------

(define (pb-kind d)
  (cond ((member? (car d) pb-discrete-names) 'discrete)
        ((equal? (car d) 'table_dist) 'table)
        (else 'continuous)))

(define (pb-lo d)
  (let ((h (car d)) (a (cdr d)))
    (cond ((equal? h 'bernoulli_dist) 0) ((equal? h 'binomial_dist) 0) ((equal? h 'poisson_dist) 0)
          ((equal? h 'geometric_dist) 1) ((equal? h 'uniform_discrete) (car a))
          ((equal? h 'hypergeometric_dist) (max 0 (- (caddr a) (- (car a) (cadr a)))))
          ((equal? h 'uniform_dist) (car a))
          ((member? h '(normal_dist student_dist)) '-inf)
          ((member? h '(exponential_dist gamma_dist chi2_dist beta_dist)) 0)
          ((equal? h 'density_dist) (nth a 2))
          (else (error "prob: неизвестное распределение" d)))))

(define (pb-hi d)
  (let ((h (car d)) (a (cdr d)))
    (cond ((equal? h 'bernoulli_dist) 1) ((equal? h 'binomial_dist) (car a))
          ((member? h '(poisson_dist geometric_dist)) 'inf)
          ((equal? h 'uniform_discrete) (cadr a))
          ((equal? h 'hypergeometric_dist) (min (caddr a) (cadr a)))
          ((equal? h 'uniform_dist) (cadr a))
          ((member? h '(normal_dist student_dist exponential_dist gamma_dist chi2_dist)) 'inf)
          ((equal? h 'beta_dist) 1)
          ((equal? h 'density_dist) (nth a 3))
          (else (error "prob: неизвестное распределение" d)))))

; Γ(s) в замкнутом виде: целое > 0, полуцелое; иначе (gamma s)
(define (pb-gamma s)
  (cond ((and (integer? s) (> s 0)) (pb-simp (list 'gamma s)))
        ((and (number? s) (= (denom s) 2) (> s 0))
         (let loop ((r 1/2) (acc (list '^ 'pi 1/2)))
           (if (= r s) (pb-simp acc) (loop (+ r 1) (list '* r acc)))))
        (else (list 'gamma s))))

; плотность/функция вероятности как выражение от v (для табличного — не определена)
(define (pb-dens d v)
  (let ((h (car d)) (a (cdr d)))
    (cond
      ((equal? h 'bernoulli_dist)
       (let ((p (car a))) `(* (^ ,p ,v) (^ (+ 1 (* -1 ,p)) (+ 1 (* -1 ,v))))))
      ((equal? h 'binomial_dist)
       (let ((n (car a)) (p (cadr a)))
         `(* (binomial ,n ,v) (^ ,p ,v) (^ (+ 1 (* -1 ,p)) (+ ,n (* -1 ,v))))))
      ((equal? h 'poisson_dist)
       (let ((l (car a))) `(* (exp (* -1 ,l)) (^ ,l ,v) (^ (gamma (+ ,v 1)) -1))))
      ((equal? h 'geometric_dist)
       (let ((p (car a))) `(* ,p (^ (+ 1 (* -1 ,p)) (+ ,v -1)))))
      ((equal? h 'uniform_discrete)
       `(^ (+ ,(cadr a) (* -1 ,(car a)) 1) -1))
      ((equal? h 'hypergeometric_dist)
       (let ((nn (car a)) (kk (cadr a)) (n (caddr a)))
         `(* (binomial ,kk ,v) (binomial ,(- nn kk) (+ ,n (* -1 ,v))) (^ ,(binomial nn n) -1))))
      ((equal? h 'uniform_dist) `(^ (+ ,(cadr a) (* -1 ,(car a))) -1))
      ((equal? h 'normal_dist)
       (let ((m (car a)) (s (cadr a)))
         `(* (^ (* 2 pi) -1/2) (^ ,s -1) (exp (* -1/2 (^ (+ ,v (* -1 ,m)) 2) (^ ,s -2))))))
      ((equal? h 'exponential_dist)
       (let ((l (car a))) `(* ,l (exp (* -1 ,l ,v)))))
      ((equal? h 'gamma_dist)
       (let ((k (car a)) (th (cadr a)))
         `(* (^ ,v (+ ,k -1)) (exp (* -1 ,v (^ ,th -1))) (^ ,(pb-gamma k) -1) (^ ,th (* -1 ,k)))))
      ((equal? h 'beta_dist)
       (let ((p (car a)) (q (cadr a)))
         `(* ,(pb-simp `(* ,(pb-gamma (pb-simp `(+ ,p ,q))) (^ ,(pb-gamma p) -1) (^ ,(pb-gamma q) -1)))
             (^ ,v (+ ,p -1)) (^ (+ 1 (* -1 ,v)) (+ ,q -1)))))
      ((equal? h 'chi2_dist)
       (let ((k (car a)))
         `(* (^ ,v (+ (* 1/2 ,k) -1)) (exp (* -1/2 ,v)) (^ ,(pb-gamma (pb-simp `(* 1/2 ,k))) -1) (^ 2 (* -1/2 ,k)))))
      ((equal? h 'student_dist)
       (let ((nu (car a)))
         `(* ,(pb-simp `(* ,(pb-gamma (pb-simp `(* 1/2 (+ ,nu 1)))) (^ ,(pb-gamma (pb-simp `(* 1/2 ,nu))) -1)
                           (^ (* ,nu pi) -1/2)))
             (^ (+ 1 (* ,v ,v (^ ,nu -1))) (* -1/2 (+ ,nu 1))))))
      ((equal? h 'density_dist)
       (if (equal? (cadr a) v) (car a) (pb-simp (subst (list (cadr a) v) (car a)))))
      (else (error "prob: плотность неизвестного распределения" d)))))

; описание носителя: (вид нижняя верхняя)
(define (dist-support d)
  (pb-need-dist d "dist_support")
  (if (equal? (car d) 'table_dist)
      (let ((s (sort (pb-vals d) <))) (list 'table (car s) (last s)))
      (list (pb-kind d) (pb-lo d) (pb-hi d))))

; ---------- суммы и интегралы ----------

(define (pb-unevaluated? r) (or (equal? r #f) (and (pair? r) (or (pb-has? r 'integrate) (pb-has? r 'sum)))))

; Σ_{k=lo}^{hi} term; #f — не вычислилась
(define (pb-sum term v lo hi)
  (cond ((and (number? lo) (number? hi))
         (cond ((< hi lo) 0)
               ((> (- hi lo) 3000) (pb-sum-symbolic term v lo hi))
               (else (pb-simp (cons '+ (let loop ((k hi) (acc '()))
                                          (if (< k lo) acc (loop (- k 1) (cons (pb-at term v k) acc)))))))))
        (else (pb-sum-symbolic term v lo hi))))

(define (pb-sum-symbolic term v lo hi)
  (let ((r (try (sum-symbolic term v lo hi) (lambda (e) #f))))
    (if (pb-unevaluated? r) #f (pb-simp r))))

(define (pb-int f v lo hi)
  (let ((r (try (integrate f v lo hi) (lambda (e) #f))))
    (if (pb-unevaluated? r) #f (pb-simp r))))

; ---------- общие операции ----------

; E[g(v)]
(define (dist-expectation g v d)
  (pb-need-dist d "expectation")
  (let ((k (pb-kind d)))
    (let ((r (cond ((equal? k 'table)
                    (pb-simp (cons '+ (map2 (lambda (x p) (list '* p (pb-at g v x))) (pb-vals d) (pb-probs d)))))
                   ((equal? k 'discrete)
                    (or (pb-sum (list '* g (pb-dens d v)) v (pb-lo d) (pb-hi d))
                        (pb-poly-expectation g v d)))
                   ((equal? (car d) 'normal_dist)
                    ; стандартизация x = μ + σ·v: интегралы от степеней v·e^{−v²/2} берутся
                    (let ((g2 (pb-at g v (list '+ (cadr d) (list '* (caddr d) v)))))
                      (pb-int (list '* g2 (pb-dens (list 'normal_dist 0 1) v)) v '-inf 'inf)))
                   (else (pb-int (list '* g (pb-dens d v)) v (pb-lo d) (pb-hi d))))))
      (if r r (list 'expectation g v d)))))

; E[g] для многочлена g по v на бесконечном дискретном носителе (суммы бесконечные — summation их не берёт):
; Σ cᵢ·E[Xⁱ], моменты — из mgf (dist-moment); не многочлен — #f
(define (pb-poly-expectation g v d)
  (if (and (pb-mgf-table d 't) (try (polynomial? g v) (lambda (e) #f)))
      (let ((n (degree g v)))
        (pb-simp (cons '+ (let loop ((i 0) (acc '()))
                            (if (> i n) (reverse acc)
                                (loop (+ i 1) (cons (list '* (coeff g v i) (dist-moment d i)) acc)))))))
      #f))

; суммарная масса плотности: 1 для корректного распределения
(define (dist-mass d)
  (pb-need-dist d "dist_mass")
  (let ((k (pb-kind d)))
    (cond ((equal? k 'table) (pb-simp (apply + (pb-probs d))))
          ((equal? k 'discrete) (or (pb-sum (pb-dens d 'x) 'x (pb-lo d) (pb-hi d)) (list 'dist-mass d)))
          (else (or (pb-int (pb-dens d 'x) 'x (pb-lo d) (pb-hi d)) (list 'dist-mass d))))))

; dist_check: #t — нормировка подтверждена (точно или численно 1e-12); unknown — сумма/интеграл не вычислены
; (бесконечные дискретные суммы); (not_normalized m) — масса m ≠ 1
(define (dist-check d)
  (let ((m (dist-mass d)))
    (cond ((pb-unevaluated-form? m) 'unknown)
          ((pb-one? m) #t)
          (else (list 'not_normalized m)))))
(define (pb-unevaluated-form? m) (and (pair? m) (equal? (car m) 'dist-mass)))

(define (pb-in-support-cond x d)
  (let ((lo (pb-lo d)) (hi (pb-hi d)))
    (if (not (pb-inf? lo)) (record-condition (list '>= x lo) "x внутри носителя распределения") #f)
    (if (not (pb-inf? hi)) (record-condition (list '<= x hi) "x внутри носителя распределения") #f)
    #t))

; pdf/pmf в точке; вне носителя 0; символьная точка — формула и условие носителя
(define (dist-pdf d x0)
  (pb-need-dist d "pdf")
  (let ((k (pb-kind d)))
    (cond ((equal? k 'table)
           (let loop ((vs (pb-vals d)) (ps (pb-probs d)) (acc 0))
             (cond ((null? vs) acc)
                   ((equal? (car vs) x0) (loop (cdr vs) (cdr ps) (+ acc (car ps))))
                   (else (loop (cdr vs) (cdr ps) acc)))))
          ((number? x0)
           (let ((lo (pb-lo d)) (hi (pb-hi d)))
             (if (or (and (number? lo) (< x0 lo)) (and (number? hi) (> x0 hi))
                     (and (equal? k 'discrete) (not (integer? x0))))
                 0
                 (pb-at (pb-dens d 'x) 'x x0))))
          (else
           (pb-in-support-cond x0 d)
           (pb-at (pb-dens d 'x) 'x x0)))))

(define (pb-normal-cdf m s x)
  (pb-simp `(* 1/2 (+ 1 (erf (* (+ ,x (* -1 ,m)) (^ ,s -1) (^ 2 -1/2)))))))

; F(x) = P(X ≤ x)
(define (dist-cdf d x0)
  (pb-need-dist d "cdf")
  (let ((k (pb-kind d)) (x (pb-bound x0)))
    (cond ((equal? x 'inf) 1)
          ((equal? x '-inf) 0)
          ((equal? k 'table)
           (if (number? x)
               (let loop ((vs (pb-vals d)) (ps (pb-probs d)) (acc 0))
                 (cond ((null? vs) acc)
                       ((<= (car vs) x) (loop (cdr vs) (cdr ps) (+ acc (car ps))))
                       (else (loop (cdr vs) (cdr ps) acc))))
               (list 'cdf d x)))
          ((equal? (car d) 'normal_dist) (pb-normal-cdf (cadr d) (caddr d) x))
          ((equal? k 'discrete)
           (let ((lo (pb-lo d)) (hi (pb-hi d)))
             (cond ((not (number? x)) (list 'cdf d x))
                   ((< x lo) 0)
                   ((and (number? hi) (>= x hi)) 1)
                   (else (or (pb-sum (pb-dens d 'x) 'x lo (floor x)) (list 'cdf d x))))))
          (else
           (let ((lo (pb-lo d)) (hi (pb-hi d)))
             (cond ((and (number? x) (number? lo) (<= x lo)) 0)
                   ((and (number? x) (number? hi) (>= x hi)) 1)
                   (else
                    (let ((r (pb-int (pb-dens d 't) 't lo x)))
                      (if r
                          (begin (if (not (number? x)) (pb-in-support-cond x d) #f) r)
                          (list 'cdf d x))))))))))

; P(a ≤ X ≤ b)
(define (dist-prob d a0 b0)
  (pb-need-dist d "prob")
  (let ((a (pb-bound a0)) (b (pb-bound b0)) (k (pb-kind d)))
    (cond ((and (number? a) (number? b) (< b a)) 0)
          ((equal? k 'table)
           (if (and (or (number? a) (pb-inf? a)) (or (number? b) (pb-inf? b)))
               (let loop ((vs (pb-vals d)) (ps (pb-probs d)) (acc 0))
                 (cond ((null? vs) acc)
                       ((and (or (equal? a '-inf) (>= (car vs) a)) (or (equal? b 'inf) (<= (car vs) b)))
                        (loop (cdr vs) (cdr ps) (+ acc (car ps))))
                       (else (loop (cdr vs) (cdr ps) acc))))
               (list 'prob d a b)))
          ((not (and (or (number? a) (pb-inf? a)) (or (number? b) (pb-inf? b)))) (list 'prob d a b))
          ((equal? (car d) 'normal_dist)
           (pb-simp (expand (list '+ (dist-cdf d b) (list '* -1 (dist-cdf d a))))))
          ((equal? k 'discrete)
           (let* ((lo (pb-lo d)) (hi (pb-hi d))
                  (lo2 (if (equal? a '-inf) lo (max lo (ceiling a))))
                  (hi2 (cond ((equal? b 'inf) hi) ((equal? hi 'inf) (floor b)) (else (min hi (floor b))))))
             (cond ((and (number? hi2) (< hi2 lo2)) 0)
                   ((equal? hi2 'inf)
                    (if (<= lo2 lo) 1
                        (let ((s (pb-sum (pb-dens d 'x) 'x lo (- lo2 1))))
                          (if s (pb-simp (list '+ 1 (list '* -1 s))) (list 'prob d a b)))))
                   (else (or (pb-sum (pb-dens d 'x) 'x lo2 hi2) (list 'prob d a b))))))
          (else
           (let* ((lo (pb-lo d)) (hi (pb-hi d))
                  (lo2 (cond ((pb-inf? lo) a) ((equal? a '-inf) lo) (else (max lo a))))
                  (hi2 (cond ((pb-inf? hi) b) ((equal? b 'inf) hi) (else (min hi b)))))
             (cond ((and (number? lo2) (number? hi2) (<= hi2 lo2)) 0)
                   (else (or (pb-int (pb-dens d 't) 't lo2 hi2) (list 'prob d a b)))))))))

; ---------- моменты ----------

; M(t) = E[e^{tX}]; #f — нет замкнутой формы в таблице
(define (pb-mgf-table d t)
  (let ((h (car d)) (a (cdr d)))
    (cond
      ((equal? h 'bernoulli_dist) `(+ 1 (* -1 ,(car a)) (* ,(car a) (exp ,t))))
      ((equal? h 'binomial_dist) `(^ (+ 1 (* -1 ,(cadr a)) (* ,(cadr a) (exp ,t))) ,(car a)))
      ((equal? h 'poisson_dist) `(exp (* ,(car a) (+ -1 (exp ,t)))))
      ((equal? h 'geometric_dist)
       (let ((p (car a)))
         `(* ,p (exp ,t) (^ (+ 1 (* -1 (+ 1 (* -1 ,p)) (exp ,t))) -1))))
      ((equal? h 'uniform_discrete)
       (let ((lo (car a)) (hi (cadr a)))
         `(* (+ (exp (* ,lo ,t)) (* -1 (exp (* ,(pb-simp `(+ ,hi 1)) ,t))))
             (^ (* (+ ,hi (* -1 ,lo) 1) (+ 1 (* -1 (exp ,t)))) -1))))
      ((equal? h 'uniform_dist)
       (let ((lo (car a)) (hi (cadr a)))
         `(* (+ (exp (* ,hi ,t)) (* -1 (exp (* ,lo ,t)))) (^ (* ,t (+ ,hi (* -1 ,lo))) -1))))
      ((equal? h 'normal_dist) `(exp (+ (* ,(car a) ,t) (* 1/2 (^ ,(cadr a) 2) (^ ,t 2)))))
      ((equal? h 'exponential_dist) `(* ,(car a) (^ (+ ,(car a) (* -1 ,t)) -1)))
      ((equal? h 'gamma_dist) `(^ (+ 1 (* -1 ,(cadr a) ,t)) (* -1 ,(car a))))
      ((equal? h 'chi2_dist) `(^ (+ 1 (* -2 ,t)) (* -1/2 ,(car a))))
      (else #f))))

(define (pb-mgf-cond d t)
  (if (number? t)
      #t
      (let ((h (car d)) (a (cdr d)))
        (cond ((equal? h 'exponential_dist) (record-condition (list '< t (car a)) "mgf существует при t < λ"))
              ((equal? h 'gamma_dist) (record-condition (list '< (list '* (cadr a) t) 1) "mgf существует при θt < 1"))
              ((equal? h 'chi2_dist) (record-condition (list '< (list '* 2 t) 1) "mgf существует при 2t < 1"))
              ((equal? h 'geometric_dist)
               (record-condition (list '< (list 'exp t) (list '^ (list '+ 1 (list '* -1 (car a))) -1))
                                 "mgf существует при (1 − p)·eᵗ < 1"))
              (else #t)))))

; mgf(d, t) = E[e^{tX}]
(define (dist-mgf d t)
  (pb-need-dist d "mgf")
  (cond ((equal? (car d) 'student_dist) (pb-err "mgf" "у распределения Стьюдента производящей функции моментов нет"))
        ((pb-mgf-table d t) (pb-mgf-cond d t) (pb-simp (pb-mgf-table d t)))
        (else (let ((r (dist-expectation (list 'exp (list '* t 'x)) 'x d)))
                (if (and (pair? r) (equal? (car r) 'expectation)) (list 'mgf d t) r)))))

; значения и вероятности табличного распределения (в языке хранятся векторами — для печати [...])
(define (pb-vals d) (if (tensor? (cadr d)) (tensor->list (cadr d)) (cadr d)))
(define (pb-probs d) (if (tensor? (caddr d)) (tensor->list (caddr d)) (caddr d)))

; E[X]
(define (dist-mean d)
  (pb-need-dist d "mean")
  (let ((h (car d)) (a (cdr d)))
    (cond
      ((equal? h 'bernoulli_dist) (car a))
      ((equal? h 'binomial_dist) (pb-simp (list '* (car a) (cadr a))))
      ((equal? h 'poisson_dist) (car a))
      ((equal? h 'geometric_dist) (pb-simp (list '^ (car a) -1)))
      ((equal? h 'uniform_discrete) (pb-simp (list '* 1/2 (list '+ (car a) (cadr a)))))
      ((equal? h 'hypergeometric_dist) (pb-simp (list '* (caddr a) (cadr a) (list '^ (car a) -1))))
      ((equal? h 'uniform_dist) (pb-simp (list '* 1/2 (list '+ (car a) (cadr a)))))
      ((equal? h 'normal_dist) (car a))
      ((equal? h 'exponential_dist) (pb-simp (list '^ (car a) -1)))
      ((equal? h 'gamma_dist) (pb-simp (list '* (car a) (cadr a))))
      ((equal? h 'beta_dist) (pb-simp (list '* (car a) (list '^ (list '+ (car a) (cadr a)) -1))))
      ((equal? h 'chi2_dist) (car a))
      ((equal? h 'student_dist)
       (let ((nu (car a)))
         (cond ((not (number? nu)) (record-condition (list '> nu 1) "среднее Стьюдента существует при ν > 1") 0)
               ((> nu 1) 0)
               (else (pb-err "mean" "у распределения Стьюдента при ν ≤ 1 среднего нет")))))
      (else (let ((r (dist-expectation 'x 'x d)))
              (if (and (pair? r) (equal? (car r) 'expectation)) (list 'mean d) r))))))

; Var X
(define (dist-variance d)
  (pb-need-dist d "variance")
  (let ((h (car d)) (a (cdr d)))
    (cond
      ((equal? h 'bernoulli_dist) (pb-simp `(* ,(car a) (+ 1 (* -1 ,(car a))))))
      ((equal? h 'binomial_dist) (pb-simp `(* ,(car a) ,(cadr a) (+ 1 (* -1 ,(cadr a))))))
      ((equal? h 'poisson_dist) (car a))
      ((equal? h 'geometric_dist) (pb-simp `(* (+ 1 (* -1 ,(car a))) (^ ,(car a) -2))))
      ((equal? h 'uniform_discrete)
       (pb-simp `(* 1/12 (+ (^ (+ ,(cadr a) (* -1 ,(car a)) 1) 2) -1))))
      ((equal? h 'hypergeometric_dist)
       (let ((nn (car a)) (kk (cadr a)) (n (caddr a)))
         (if (= nn 1) 0
             (pb-simp `(* ,n ,(/ kk nn) ,(- 1 (/ kk nn)) ,(/ (- nn n) (- nn 1)))))))
      ((equal? h 'uniform_dist) (pb-simp `(* 1/12 (^ (+ ,(cadr a) (* -1 ,(car a))) 2))))
      ((equal? h 'normal_dist) (pb-simp `(^ ,(cadr a) 2)))
      ((equal? h 'exponential_dist) (pb-simp `(^ ,(car a) -2)))
      ((equal? h 'gamma_dist) (pb-simp `(* ,(car a) (^ ,(cadr a) 2))))
      ((equal? h 'beta_dist)
       (pb-simp `(* ,(car a) ,(cadr a) (^ (+ ,(car a) ,(cadr a)) -2) (^ (+ ,(car a) ,(cadr a) 1) -1))))
      ((equal? h 'chi2_dist) (pb-simp `(* 2 ,(car a))))
      ((equal? h 'student_dist)
       (let ((nu (car a)))
         (cond ((not (number? nu)) (record-condition (list '> nu 2) "дисперсия Стьюдента существует при ν > 2")
                                   (pb-simp `(* ,nu (^ (+ ,nu -2) -1))))
               ((> nu 2) (pb-simp `(* ,nu (^ (+ ,nu -2) -1))))
               ((> nu 1) 'inf)
               (else (pb-err "variance" "у распределения Стьюдента при ν ≤ 1 дисперсии нет")))))
      (else
       (let ((m (dist-mean d)) (m2 (dist-expectation '(^ x 2) 'x d)))
         (if (or (and (pair? m) (equal? (car m) 'mean)) (and (pair? m2) (equal? (car m2) 'expectation)))
             (list 'variance d)
             (pb-simp (list '+ m2 (list '* -1 (list '* m m))))))))))

(define (dist-stddev d)
  (let ((v (dist-variance d)))
    (if (or (equal? v 'inf) (and (pair? v) (equal? (car v) 'variance))) (list 'stddev d) (pb-simp (list '^ v 1/2)))))

; k-й начальный момент E[X^k]: производная mgf в нуле, иначе общий движок
(define (dist-moment d k)
  (pb-need-dist d "moment")
  (pb-req (and (integer? k) (>= k 0)) "moment" "порядок момента — целое ≥ 0")
  (cond ((equal? k 0) 1)
        ((and (equal? (car d) 'student_dist) (number? (cadr d)) (<= (cadr d) k))
         (pb-err "moment" "момент порядка k у Стьюдента существует только при k < ν"))
        ; у равномерных mgf в t = 0 — устранимая особенность 0/0: производные в нуле подстановкой не берутся
        ((and (pb-mgf-table d 't) (not (member? (car d) '(student_dist uniform_dist uniform_discrete))))
         (let loop ((i 0) (e (pb-simp (pb-mgf-table d 't))))
           (if (= i k)
               (pb-simp (subst '(t 0) e))
               (loop (+ i 1) (pb-simp (diff 't e))))))
        (else
         (let ((r (dist-expectation (list '^ 'x k) 'x d)))
           (if (and (pair? r) (equal? (car r) 'expectation)) (list 'moment d k) r)))))

; квантиль F⁻¹(q): равномерные, показательное, табличное; иначе невычисленная форма
(define (dist-quantile d q)
  (pb-need-dist d "quantile")
  (pb-req (or (not (number? q)) (and (> q 0) (< q 1))) "quantile" "q должно лежать в (0, 1)")
  (let ((h (car d)) (a (cdr d)))
    (cond
      ((equal? h 'uniform_dist) (pb-simp `(+ ,(car a) (* ,q (+ ,(cadr a) (* -1 ,(car a)))))))
      ((equal? h 'exponential_dist) (pb-simp `(* (log (^ (+ 1 (* -1 ,q)) -1)) (^ ,(car a) -1))))
      ((and (equal? h 'normal_dist) (equal? q 1/2)) (car a))
      ((and (equal? h 'table_dist) (number? q))
       (let ((pairs (sort-pairs (map2 cons (pb-vals d) (pb-probs d)))))
         (let loop ((ps pairs) (acc 0))
           (let ((acc2 (+ acc (cdr (car ps)))))
             (if (or (>= acc2 q) (null? (cdr ps))) (car (car ps)) (loop (cdr ps) acc2))))))
      ((and (equal? h 'uniform_discrete) (number? q) (number? (car a)) (number? (cadr a)))
       (let ((n (+ (- (cadr a) (car a)) 1)))
         (+ (car a) (- (ceiling (* q n)) 1))))
      (else (list 'quantile d q)))))

(define (sort-pairs ps) (sort ps (lambda (x y) (< (car x) (car y)))))

; ---------- выборка ----------

(define (pb-data xs name)
  (pb-req (and (list? xs) (not (null? xs))) name "ожидается непустой список (вектор) чисел"))

(define (sample-mean xs)
  (pb-data xs "sample_mean")
  (pb-simp (list '* (apply + xs) (/ 1 (length xs)))))

(define (pb-sq x) (list '* x x))

(define (sample-variance xs)
  (pb-data xs "sample_variance")
  (pb-req (>= (length xs) 2) "sample_variance" "несмещённая дисперсия (n − 1) определена при n ≥ 2, в выборке один элемент")
  (let ((m (sample-mean xs)))
    (pb-simp (list '* (/ 1 (- (length xs) 1))
                   (cons '+ (map (lambda (x) (pb-sq (pb-simp (list '+ x (list '* -1 m))))) xs))))))

(define (sample-stddev xs) (pb-simp (list '^ (sample-variance xs) 1/2)))

(define (sample-median xs)
  (pb-data xs "median")
  (let* ((s (sort xs <)) (n (length s)))
    (if (= (mod n 2) 1)
        (nth s (quotient n 2))
        (pb-simp (list '* 1/2 (list '+ (nth s (- (quotient n 2) 1)) (nth s (quotient n 2))))))))

; квантиль выборки, метод 7: h = (n − 1)q, интерполяция между x₍⌊h⌋₊₁₎ и x₍⌊h⌋₊₂₎ (порядковые статистики с нуля)
(define (quantile-sample xs q)
  (pb-data xs "quantile_sample")
  (pb-req (and (number? q) (>= q 0) (<= q 1)) "quantile_sample" "q — число из [0, 1]")
  (let* ((s (sort xs <)) (n (length s)) (h (* (- n 1) q)) (i (floor h)) (f (- h i)))
    (if (>= i (- n 1))
        (last s)
        (pb-simp (list '+ (nth s i) (list '* f (list '+ (nth s (+ i 1)) (list '* -1 (nth s i)))))))))

(define (pb-pairs xs ys name)
  (pb-req (and (list? xs) (list? ys) (= (length xs) (length ys))) name "ожидаются два списка (вектора) одной длины")
  (pb-req (>= (length xs) 2) name "нужно хотя бы два наблюдения"))

(define (pb-centered xs)
  (let ((m (sample-mean xs))) (map (lambda (x) (pb-simp (list '+ x (list '* -1 m)))) xs)))

(define (pb-dot us vs) (pb-simp (cons '+ (map2 (lambda (u v) (list '* u v)) us vs))))

(define (sample-covariance xs ys)
  (pb-pairs xs ys "covariance")
  (pb-simp (list '* (/ 1 (- (length xs) 1)) (pb-dot (pb-centered xs) (pb-centered ys)))))

(define (sample-correlation xs ys)
  (pb-pairs xs ys "correlation")
  (let* ((cx (pb-centered xs)) (cy (pb-centered ys))
         (sxx (pb-dot cx cx)) (syy (pb-dot cy cy)) (sxy (pb-dot cx cy)))
    (pb-req (and (not (equal? sxx 0)) (not (equal? syy 0))) "correlation" "у одной из выборок нулевая дисперсия — корреляция не определена")
    (pb-simp (list '* sxy (list '^ (pb-simp (list '* sxx syy)) -1/2)))))

; МНК-прямая y = a + b·x: (a b), b = Sxy/Sxx, a = ȳ − b·x̄
(define (linear-regression xs ys)
  (pb-pairs xs ys "linear_regression")
  (let* ((cx (pb-centered xs)) (cy (pb-centered ys)) (sxx (pb-dot cx cx)) (sxy (pb-dot cx cy)))
    (pb-req (not (equal? sxx 0)) "linear_regression" "все x одинаковы — прямая не определена")
    (let ((b (pb-simp (list '* sxy (list '^ sxx -1)))))
      (list (pb-simp (list '+ (sample-mean ys) (list '* -1 b (sample-mean xs)))) b))))

; частоты: ((значение число) …) по возрастанию значения
(define (frequencies xs)
  (pb-data xs "frequencies")
  (let loop ((vs (sort xs <)) (acc '()))
    (cond ((null? vs) (reverse acc))
          ((and (pair? acc) (equal? (car (car acc)) (car vs)))
           (loop (cdr vs) (cons (list (car (car acc)) (+ 1 (cadr (car acc)))) (cdr acc))))
          (else (loop (cdr vs) (cons (list (car vs) 1) acc))))))

; ---------- полная вероятность и Байес ----------

(define (pb-prob? p) (and (number? p) (>= p 0) (<= p 1)))

(define (pb-check-hyp priors liks name)
  (pb-req (and (list? priors) (list? liks) (= (length priors) (length liks)) (not (null? priors)))
          name "ожидаются два списка одной длины: P(Hᵢ) и P(E | Hᵢ)")
  (pb-req (and (every? pb-prob? priors) (every? pb-prob? liks)) name "вероятности — числа из [0, 1]")
  (let ((s (apply + priors)))
    (pb-req (equal? s 1) name (string-append "априорные вероятности дают сумму " (to-string s) ", не 1"))))

; P(E) = Σ P(Hᵢ)·P(E | Hᵢ)
(define (total-probability priors liks)
  (pb-check-hyp priors liks "total_probability")
  (pb-simp (cons '+ (map2 (lambda (p l) (list '* p l)) priors liks))))

; P(Hᵢ | E) = P(Hᵢ)·P(E | Hᵢ) / P(E)
(define (bayes-posterior priors liks)
  (pb-check-hyp priors liks "bayes")
  (let ((pe (total-probability priors liks)))
    (pb-req (not (equal? pe 0)) "bayes" "P(E) = 0: свидетельство невозможно, апостериорные не определены")
    (map2 (lambda (p l) (pb-simp (list '* p l (list '^ pe -1)))) priors liks)))
