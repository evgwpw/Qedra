; stats.lisp — Шаг PROB.b: математическая статистика (поверх prob.lisp).
;
; 1. Численные cdf с ЗАЯВЛЕННОЙ ПОГРЕШНОСТЬЮ для нормального, Стьюдента, χ², Фишера: dist-cdf-cert d x → (значение граница),
;    граница — оценка |ошибки| сверху (обрыв ряда по геометрической оценке хвоста + запас на округление double).
;    Основа — регуляризованная неполная бета I_x(a, b) = xᵃ(1−x)ᵇ/(a·B(a, b)) · Σ uₙxⁿ (uₙ₊₁/uₙ = (a+b+n)/(a+n+1), члены
;    положительные, при x ≤ (a+1)/(a+b+2) отношение соседних членов < 1 и хвост ≤ tₙ·ρ/(1−ρ)) и неполная гамма P(a, z) = zᵃe⁻ᶻ/Γ(a+1) · Σ zⁿ/((a+1)…(a+n)).
; 2. Квантиль: бисекция по монотонной cdf. Скобка [lo, hi] строится так, что истинные F(lo) < p ≤ F(hi) (значение cdf ± граница ошибки
;    не пересекает p). Результат — середина скобки, точность — её полуширина (≤ 1e-10·max(1, |x|), иначе ошибка).
; 3. Оценки (mle, moments-estimate), доверительные интервалы, критерии. Ответ всегда запись — список пар (ключ значение).
;    Данные могут быть точными (рациональными): среднее, дисперсия, χ², F считаются точно, p-значения и квантили — числами.

(module stats
  (export dist-cdf-cert dist-cdf-num dist-sf-num dist-quantile-bounds dist-quantile-num quantile-dist
          mle mle-check mle-score moments-estimate
          confint-mean confint-mean-sigma confint-variance confint-proportion confint-wilson
          t-test t-test-two t-test-pooled t-test-paired chi2-gof chi2-independence f-test-variances
          stat-get))

(define (st-err name msg) (error (string-append name ": " msg)))
(define (st-req ok name msg) (if ok #t (st-err name msg)))
(define (st-fl x) (* 1.0 x))
(define (st-num-list? xs) (and (list? xs) (every? number? xs)))
(define (st-sq x) (* x x))

; ---------- гамма-функция: ln Γ(z), z > 0 (сдвиг до z ≥ 30 и ряд Стирлинга: остаток < 1/(1188·z⁹) ≈ 4e-17) ----------

(define (st-lgamma z0)
  (let loop ((z (st-fl z0)) (prod 1.0))
    (if (< z 12.0)
        (loop (+ z 1.0) (* prod z))
        (let* ((w (/ 1.0 (* z z)))
               ; B₂ₖ/(2k(2k−1)z^{2k−1}), k = 1…8 по схеме Горнера по w = 1/z²; остаток < 2e-18 при z ≥ 12
               (ser (* (/ 1.0 z)
                       (+ 1/12 (* w (+ -1/360 (* w (+ 1/1260 (* w (+ -1/1680 (* w (+ 1/1188 (* w (+ -691/360360
                          (* w (+ 1/156 (* w -3617/122400)))))))))))))))))
          (- (+ (- (* (- z 0.5) (log z)) z) 0.9189385332046727 ser)
             (log prod))))))

(define (st-lbeta a b) (- (+ (st-lgamma a) (st-lgamma b)) (st-lgamma (+ a b))))

; запас на округление: u = 1.1e-16, умножено на число операций; префактор — относительная ошибка ≈ 3e-14 + 4e-16·(масштаб логарифмов)
(define st-u 2.3e-16)
(define st-max-terms 400000)

; ---------- неполная бета ----------

; I_x(a, b), y = 1 − x (задаётся отдельно: без потери точности), a, b > 0, 0 < x < 1; ряд (прямой) → (значение граница)
(define (st-ibeta-series a b x y)
  (let* ((lg (+ (abs (st-lgamma a)) (abs (st-lgamma b)) (abs (st-lgamma (+ a b)))))
         (e1 (* a (log x))) (e2 (* b (log y)))
         (pre (exp (- (+ e1 e2) (+ (log a) (st-lbeta a b)))))
         (scale (+ 1.0 (abs e1) (abs e2) (abs (log a)) lg))
         (pre-rel (+ 3e-14 (* 4e-16 scale))))
    (let loop ((n 0) (term 1.0) (s 1.0))
      (let* ((rho0 (* (/ (+ a b n) (+ a n 1.0)) x))
             (rho (if (>= b 1.0) rho0 x)))
        (cond ((> n st-max-terms) (st-err "cdf" "ряд неполной беты не сошёлся"))
              ((and (< rho 1.0) (< (* pre term (/ rho (- 1.0 rho))) 1e-17))
               (let* ((v (* pre s)) (tail (* pre term (/ rho (- 1.0 rho)))))
                 (list v (+ tail (* v (+ pre-rel (* (+ n 8) st-u))) 1e-17))))
              (else
               (let ((t2 (* term (/ (+ a b n) (+ a n 1.0)) x)))
                 (loop (+ n 1) t2 (+ s t2)))))))))

; I_x(a, b) с переключением на симметрию I_x(a, b) = 1 − I_{1−x}(b, a) → (значение граница)
(define (st-ibeta a b x y)
  (cond ((<= x 0.0) (list 0.0 0.0))
        ((<= y 0.0) (list 1.0 0.0))
        ((<= x (/ (+ a 1.0) (+ a b 2.0))) (st-ibeta-series a b x y))
        (else (let ((r (st-ibeta-series b a y x)))
                (list (- 1.0 (car r)) (+ (cadr r) 1.2e-16))))))

; ---------- неполная гамма ----------

; P(a, z) = γ(a, z)/Γ(a), z ≥ 0 → (значение граница)
(define (st-igamma a z)
  (if (<= z 0.0)
      (list 0.0 0.0)
      (let* ((e (- (* a (log z)) z (st-lgamma (+ a 1.0))))
             (pre (exp e))
             (scale (+ 1.0 (abs (* a (log z))) z (abs (st-lgamma (+ a 1.0)))))
             (pre-rel (+ 3e-14 (* 4e-16 scale))))
        (let loop ((n 0) (term 1.0) (s 1.0))
          (let ((rho (/ z (+ a n 1.0))))
            (cond ((> n st-max-terms) (st-err "cdf" "ряд неполной гаммы не сошёлся"))
                  ((and (< rho 1.0) (< (* pre term (/ rho (- 1.0 rho))) 1e-17))
                   (let* ((v (* pre s)) (tail (* pre term (/ rho (- 1.0 rho)))))
                     (list v (+ tail (* v (+ pre-rel (* (+ n 8) st-u))) 1e-17))))
                  (else (let ((t2 (* term (/ z (+ a n 1.0))))) (loop (+ n 1) t2 (+ s t2))))))))))

; ---------- cdf и хвост по распределению → (значение граница) ----------

(define (st-clamp01 r) (list (max 0.0 (min 1.0 (car r))) (cadr r)))
(define (st-compl r) (list (- 1.0 (car r)) (+ (cadr r) 1.2e-16)))

(define (st-head d) (car d))
(define (st-par d i) (st-fl (nth (cdr d) i)))

; стандартный нормальный: Φ(z) = ½ + ½·sgn(z)·P(½, z²/2); при z²/2 > 750 хвост < e⁻⁷⁵⁰
(define (st-norm-cdf z)
  (let ((z2 (/ (* z z) 2.0)))
    (cond ((> z2 750.0) (if (> z 0.0) (list 1.0 1e-300) (list 0.0 1e-300)))
          (else (let* ((p (st-igamma 0.5 z2)) (v (car p)) (e (cadr p)))
                  (cond ((= z 0.0) (list 0.5 0.0))
                        ((> z 0.0) (st-clamp01 (list (+ 0.5 (* 0.5 v)) (+ (* 0.5 e) 1.2e-16))))
                        (else (st-clamp01 (list (- 0.5 (* 0.5 v)) (+ (* 0.5 e) 1.2e-16))))))))))

; Стьюдент: хвост P(T > |t|) = ½·I_{ν/(ν+t²)}(ν/2, ½)
(define (st-t-half nu t)
  (let* ((a (abs t)) (t2 (* a a))
         (big? (> t2 1e290))
         (x (if big? (/ nu t2) (/ nu (+ nu t2))))
         (y (if big? 1.0 (/ t2 (+ nu t2))))
         (r (st-ibeta (/ nu 2.0) 0.5 x y)))
    (list (* 0.5 (car r)) (* 0.5 (cadr r)))))

(define (st-t-cdf nu t)
  (let ((h (st-t-half nu t)))
    (cond ((= t 0.0) (list 0.5 0.0))
          ((> t 0.0) (st-clamp01 (st-compl h)))
          (else (st-clamp01 h)))))
(define (st-t-sf nu t) (st-t-cdf nu (- t)))

(define (st-chi2-cdf k x) (if (<= x 0.0) (list 0.0 0.0) (st-clamp01 (st-igamma (/ k 2.0) (/ x 2.0)))))

; Фишер: F(x) = I_{d1x/(d1x+d2)}(d1/2, d2/2); хвост — I_{d2/(d1x+d2)}(d2/2, d1/2)
(define (st-f-cdf d1 d2 x)
  (if (<= x 0.0) (list 0.0 0.0)
      (let ((u (* d1 x)))
        (st-clamp01 (st-ibeta (/ d1 2.0) (/ d2 2.0) (/ u (+ u d2)) (/ d2 (+ u d2)))))))
(define (st-f-sf d1 d2 x)
  (if (<= x 0.0) (list 1.0 0.0)
      (let ((u (* d1 x)))
        (st-clamp01 (st-ibeta (/ d2 2.0) (/ d1 2.0) (/ d2 (+ u d2)) (/ u (+ u d2)))))))

(define (st-supported? d) (and (dist? d) (member? (car d) '(normal_dist student_dist chi2_dist f_dist)) #t))
(define (st-need d name)
  (st-req (st-supported? d) name "ожидается normal_dist, student_dist, chi2_dist или f_dist")
  (st-req (every? number? (cdr d)) name "параметры распределения должны быть числами"))

(define (st-dist-cdf d x0)
  (let ((h (st-head d)) (x (st-fl x0)))
    (cond ((equal? h 'normal_dist) (st-norm-cdf (/ (- x (st-par d 0)) (st-par d 1))))
          ((equal? h 'student_dist) (st-t-cdf (st-par d 0) x))
          ((equal? h 'chi2_dist) (st-chi2-cdf (st-par d 0) x))
          (else (st-f-cdf (st-par d 0) (st-par d 1) x)))))

(define (st-dist-sf d x0)
  (let ((h (st-head d)) (x (st-fl x0)))
    (cond ((equal? h 'normal_dist) (st-norm-cdf (/ (- (st-par d 0) x) (st-par d 1))))
          ((equal? h 'student_dist) (st-t-sf (st-par d 0) x))
          ((equal? h 'chi2_dist) (st-clamp01 (st-compl (st-chi2-cdf (st-par d 0) x))))
          (else (st-f-sf (st-par d 0) (st-par d 1) x)))))

; dist_cdf_cert(d, x) → (значение граница_ошибки)
(define (dist-cdf-cert d x)
  (st-need d "cdf_cert")
  (st-req (number? x) "cdf_cert" "x — число")
  (st-dist-cdf d x))
(define (dist-cdf-num d x) (car (dist-cdf-cert d x)))
(define (dist-sf-num d x)
  (st-need d "sf")
  (st-req (number? x) "sf" "x — число")
  (car (st-dist-sf d x)))

; ---------- квантиль: бисекция с сертифицированной скобкой ----------

(define st-q-pmin 1e-12)
(define st-q-tol 1e-13)

; скобка квантиля стандартизованного/исходного распределения: (lo hi), F(lo) < p ≤ F(hi) с запасом на ошибку
; решение «F(x) ≥ p?» с учётом ошибки: 1 — F(x) ≥ p доказано, −1 — F(x) < p доказано, 0 — в пределах ошибки.
; при p > 1/2 сравнивается хвост 1 − F(x) с q = 1 − p (у Стьюдента и Фишера хвост считается напрямую, с малой относительной ошибкой)
(define (st-side d p)
  (if (> p 0.5)
      (let ((q (- 1.0 p)))
        (lambda (x) (let* ((r (st-dist-sf d x)) (v (car r)) (e (cadr r)))
                      (cond ((<= (+ v e) q) 1) ((> (- v e) q) -1) (else 0)))))
      (lambda (x) (let* ((r (st-dist-cdf d x)) (v (car r)) (e (cadr r)))
                    (cond ((>= (- v e) p) 1) ((< (+ v e) p) -1) (else 0))))))

; скобка (lo hi): F(lo) < p ≤ F(hi) доказано (носитель χ², F — с нуля: F(0) = 0)
(define (st-bracket d p)
  (let* ((h (st-head d))
         (side (st-side d p))
         (pos? (member? h '(chi2_dist f_dist)))
         (center (cond ((equal? h 'chi2_dist) (st-par d 0)) ((equal? h 'f_dist) 1.0) (else 0.0)))
         (up (let loop ((s 1.0) (n 0))
               (let ((x (+ center s)))
                 (cond ((= (side x) 1) x)
                       ((> n 1100) (st-err "quantile" "верхняя граница не найдена"))
                       (else (loop (* s 2.0) (+ n 1)))))))
         (lo (if pos?
                 0.0
                 (let loop ((s 1.0) (n 0))
                   (let ((x (- center s)))
                     (cond ((= (side x) -1) x)
                           ((> n 1100) (st-err "quantile" "нижняя граница не найдена"))
                           (else (loop (* s 2.0) (+ n 1)))))))))
    (list lo up)))

(define (st-bisect d p lo0 hi0)
  (let ((side (st-side d p)))
    (let loop ((lo lo0) (hi hi0) (n 0))
      (let ((mid (* 0.5 (+ lo hi))))
        (if (or (> n 400) (<= (- hi lo) (* st-q-tol (max 1.0 (abs mid)))))
            (list lo hi)
            (let ((s (side mid)))
              (cond ((= s 1) (loop lo mid (+ n 1)))
                    ((= s -1) (loop mid hi (+ n 1)))
                    ; mid внутри зоны неопределённости cdf: сжимаем скобку к краям зоны (доказанные −1 слева, 1 справа)
                    (else (list (st-edge side lo mid -1) (st-edge side mid hi 1))))))))))

; край зоны: на [a, b] ровно один из концов доказан (значение want у a при want = −1, у b при want = 1); сужаем до допуска
(define (st-edge side a b want)
  (let loop ((a a) (b b) (n 0))
    (let ((m (* 0.5 (+ a b))))
      (if (or (> n 400) (<= (- b a) (* st-q-tol (max 1.0 (abs m)))))
          (if (= want -1) a b)
          (if (= want -1)
              (if (= (side m) -1) (loop m b (+ n 1)) (loop a m (+ n 1)))
              (if (= (side m) 1) (loop a m (+ n 1)) (loop m b (+ n 1))))))))

(define (st-check-p p name)
  (st-req (number? p) name "p — число")
  (st-req (and (> p 0) (< p 1)) name "p должно лежать в (0, 1)")
  (st-req (and (>= p st-q-pmin) (<= p (- 1.0 st-q-pmin))) name
          "p слишком близко к 0 или 1: ошибка cdf сравнима с p, точность 1e-10 не гарантируется (допустимо 1e-12 ≤ p ≤ 1 − 1e-12)"))

; dist_quantile_bounds(d, p) → (lo hi): истинная F⁻¹(p) лежит в [lo, hi] (F(lo) < p ≤ F(hi) с запасом на ошибку cdf)
(define (dist-quantile-bounds d p0)
  (st-need d "quantile_bounds")
  (st-check-p p0 "quantile")
  (let* ((p (st-fl p0)) (h (st-head d))
         (dd (if (equal? h 'normal_dist) (list 'normal_dist 0 1) d))   ; нормальное — стандартизацией x = μ + σz
         (br (st-bracket dd p)) (b (st-bisect dd p (car br) (cadr br))))
    (if (equal? h 'normal_dist)
        (let ((m (st-par d 0)) (s (st-par d 1)))
          (list (+ m (* s (car b))) (+ m (* s (cadr b)))))
        b)))

; dist_quantile_num(d, p) → число; точность (полуширина скобки) проверяется: ≤ 1e-10·max(1, |x|), иначе ошибка
(define (dist-quantile-num d p)
  (let* ((b (dist-quantile-bounds d p)) (lo (car b)) (hi (cadr b)) (mid (* 0.5 (+ lo hi))))
    (st-req (<= (* 0.5 (- hi lo)) (* 1e-10 (max 1.0 (abs mid)))) "quantile"
            (string-append "точность 1e-10 не достигнута (скобка [" (to-string lo) ", " (to-string hi) "])"))
    mid))

; точный квантиль prob там, где он есть; для normal/student/chi2/F с числовыми параметрами — число (квантиль p = 1/2 нормального — μ)
(define (quantile-dist d q)
  (let ((r (dist-quantile d q)))
    (if (and (pair? r) (equal? (car r) 'quantile) (number? q) (st-supported? d) (every? number? (cdr d)))
        (dist-quantile-num d q)
        r)))

; ---------- записи ----------

(define (stat-get rec key)
  (let ((p (assoc key rec)))
    (if p (cadr p) (st-err "stat_get" (string-append "в записи нет поля " (to-string key))))))

(define (st-mean xs) (/ (apply + xs) (length xs)))
(define (st-ssq xs) (let ((m (st-mean xs))) (apply + (map (lambda (x) (st-sq (- x m))) xs))))   ; Σ(x − x̄)²
(define (st-svar xs) (/ (st-ssq xs) (- (length xs) 1)))                                           ; несмещённая
(define (st-sd-num v) (sqrt (st-fl v)))

(define (st-data xs name min-n)
  (st-req (st-num-list? xs) name "ожидается список (вектор) чисел")
  (st-req (>= (length xs) min-n) name
          (string-append "нужно не менее " (to-string min-n) " наблюдений, получено " (to-string (length xs)))))

(define (st-level lv name)
  (st-req (and (number? lv) (> lv 0) (< lv 1)) name "уровень доверия — число из (0, 1)"))

(define (st-alpha a name)
  (st-req (and (number? a) (> a 0) (< a 1)) name "уровень значимости α — число из (0, 1)"))

; ---------- оценки параметров ----------

(define (st-family f name)
  (cond ((member? f '(normal normal_dist)) 'normal)
        ((member? f '(exponential exponential_dist)) 'exponential)
        ((member? f '(poisson poisson_dist)) 'poisson)
        ((member? f '(binomial binomial_dist)) 'binomial)
        ((member? f '(uniform uniform_dist)) 'uniform)
        ((member? f '(gamma gamma_dist)) 'gamma)
        (else (st-err name "семейство: normal, exponential, poisson, binomial (n известно), uniform, gamma (только moments_estimate)"))))

(define (st-nonneg-ints? xs) (every? (lambda (x) (and (integer? x) (>= x 0))) xs))

; ноль производной логарифма правдоподобия: точный 0 или float ≤ 1e-9
(define (st-zero? v) (or (equal? v 0) (and (number? v) (< (abs v) 1e-9))))

(define (st-sum-expr f xs) (cons '+ (map f xs)))

; (имя значение) для параметров и список оценок производных log L в точке оценки
(define (st-scores fam xs m extra)
  (let ((n (length xs)))
    (cond
      ((equal? fam 'normal)
       ; ℓ(μ, v) = −n/2·ln v − Σ(x − μ)²/(2v); оценки (μ̂, v̂)
       (let* ((ll (simplify `(+ (* ,(/ n -2) (log st_v)) (* -1/2 (^ st_v -1) ,(st-sum-expr (lambda (x) `(^ (+ ,x (* -1 st_mu)) 2)) xs)))))
              (dm (simplify (diff 'st_mu ll))) (dv (simplify (diff 'st_v ll))))
         (list (simplify (subst (list 'st_v (cadr m)) (subst (list 'st_mu (car m)) dm)))
               (simplify (subst (list 'st_v (cadr m)) (subst (list 'st_mu (car m)) dv))))))
      ((equal? fam 'exponential)
       (let* ((ll (simplify `(+ (* ,n (log st_l)) (* -1 st_l ,(apply + xs))))) (dl (simplify (diff 'st_l ll))))
         (list (simplify (subst (list 'st_l (car m)) dl)))))
      ((equal? fam 'poisson)
       (let* ((ll (simplify `(+ (* ,(apply + xs) (log st_l)) (* -1 ,n st_l)))) (dl (simplify (diff 'st_l ll))))
         (list (simplify (subst (list 'st_l (car m)) dl)))))
      ((equal? fam 'binomial)
       (if (or (equal? (car m) 0) (equal? (car m) 1))
           'boundary
           (let* ((sx (apply + xs))
                  (ll (simplify `(+ (* ,sx (log st_p)) (* ,(- (* n extra) sx) (log (+ 1 (* -1 st_p)))))))
                  (dp (simplify (diff 'st_p ll))))
             (list (simplify (subst (list 'st_p (car m)) dp))))))
      (else 'boundary))))

(define (st-score-check fam xs m extra)
  (let ((s (st-scores fam xs m extra)))
    (cond ((equal? s 'boundary) 'boundary)
          (else (every? st-zero? s)))))

; mle(семейство, данные [, n]) → ((семейство f) (параметр значение) … (score_check #t|boundary))
(define (mle fam0 xs &rest rest)
  (let ((fam (st-family fam0 "mle")) (extra (if (null? rest) #f (car rest))))
    (st-data xs "mle" 1)
    (let ((n (length xs)) (m (st-mean xs)))
      (cond
        ((equal? fam 'normal)
         (let ((v (/ (st-ssq xs) n)))
           (st-req (not (equal? v 0)) "mle" "все наблюдения равны: σ̂² = 0 — оценка вырождена (на границе параметров)")
           (list (list 'family 'normal) (list 'mu m) (list 'sigma2 v)
                 (list 'score_check (st-score-check fam xs (list m v) #f)))))
        ((equal? fam 'exponential)
         (st-req (every? (lambda (x) (>= x 0)) xs) "mle" "для показательного нужны x ≥ 0")
         (st-req (> m 0) "mle" "все наблюдения равны 0: λ̂ = ∞")
         (let ((l (/ 1 m)))
           (list (list 'family 'exponential) (list 'lambda l) (list 'score_check (st-score-check fam xs (list l) #f)))))
        ((equal? fam 'poisson)
         (st-req (st-nonneg-ints? xs) "mle" "для Пуассона нужны целые x ≥ 0")
         (st-req (> m 0) "mle" "все наблюдения равны 0: λ̂ = 0 лежит на границе (λ > 0)")
         (list (list 'family 'poisson) (list 'lambda m) (list 'score_check (st-score-check fam xs (list m) #f))))
        ((equal? fam 'binomial)
         (st-req (and (integer? extra) (> extra 0)) "mle" "для биномиального нужно число испытаний n: mle(binomial, данные, n)")
         (st-req (every? (lambda (x) (and (integer? x) (>= x 0) (<= x extra))) xs) "mle" "наблюдения — целые от 0 до n")
         (let ((p (/ m extra)))
           (list (list 'family 'binomial) (list 'n extra) (list 'p p) (list 'score_check (st-score-check fam xs (list p) extra)))))
        ((equal? fam 'uniform)
         (let ((lo (apply min xs)) (hi (apply max xs)))
           (st-req (< lo hi) "mle" "все наблюдения равны: U(a, b) вырождено")
           (list (list 'family 'uniform) (list 'a lo) (list 'b hi) (list 'score_check 'boundary))))
        (else (st-err "mle" "для гамма-семейства оценка максимального правдоподобия не имеет замкнутой формы: используйте moments_estimate"))))))

; mle_score(семейство, данные, оценка [, n]) → список производных ln L по параметрам в заданной точке
; (оценка — список параметров: normal (μ σ²), exponential/poisson (λ), binomial (p), n — число испытаний); 'boundary для uniform
(define (mle-score fam0 xs est &rest rest)
  (let ((fam (st-family fam0 "mle_score")))
    (st-data xs "mle_score" 1)
    (st-req (and (list? est) (every? number? est)) "mle_score" "оценка — список чисел")
    (st-scores fam xs est (if (null? rest) #f (car rest)))))

; mle_check(f, данные, оценка…) → #t: производная ln L в точке оценки равна нулю (или оценка на границе)
(define (mle-check fam0 xs &rest rest)
  (let ((r (apply mle (cons fam0 (cons xs rest)))))
    (stat-get r 'score_check)))

; moments_estimate(семейство, данные [, n]): метод моментов
(define (moments-estimate fam0 xs &rest rest)
  (let ((fam (st-family fam0 "moments_estimate")) (extra (if (null? rest) #f (car rest))))
    (st-data xs "moments_estimate" 1)
    (let* ((n (length xs)) (m (st-mean xs)) (v (/ (st-ssq xs) n)))
      (cond
        ((equal? fam 'normal) (list (list 'family 'normal) (list 'mu m) (list 'sigma2 v)))
        ((equal? fam 'exponential)
         (st-req (> m 0) "moments_estimate" "среднее должно быть положительным")
         (list (list 'family 'exponential) (list 'lambda (/ 1 m))))
        ((equal? fam 'poisson)
         (st-req (> m 0) "moments_estimate" "среднее должно быть положительным")
         (list (list 'family 'poisson) (list 'lambda m)))
        ((equal? fam 'binomial)
         (st-req (and (integer? extra) (> extra 0)) "moments_estimate" "для биномиального нужно число испытаний n")
         (list (list 'family 'binomial) (list 'n extra) (list 'p (/ m extra))))
        ((equal? fam 'uniform)
         (st-req (> v 0) "moments_estimate" "все наблюдения равны: U(a, b) вырождено")
         (let ((h (simplify (list '^ (* 3 v) 1/2))))
           (list (list 'family 'uniform) (list 'a (simplify (list '+ m (list '* -1 h)))) (list 'b (simplify (list '+ m h))))))
        (else
         (st-req (and (> m 0) (> v 0)) "moments_estimate" "среднее и дисперсия должны быть положительными")
         (list (list 'family 'gamma) (list 'k (/ (st-sq m) v)) (list 'theta (/ v m))))))))

; ---------- доверительные интервалы ----------

(define (st-q-record kind q-dist p lo hi level extra)
  ; q — использованный квантиль (число) и точность (полуширина скобки)
  (let* ((b (dist-quantile-bounds q-dist p)) (mid (* 0.5 (+ (car b) (cadr b)))))
    (list mid (* 0.5 (- (cadr b) (car b))))))

(define (st-ci-result kind lo hi level q qerr extra)
  (append (list (list 'kind kind) (list 'interval (list lo hi)) (list 'level level)
                (list 'quantile q) (list 'quantile_error qerr))
          extra))

(define (st-level-p level) (/ (+ 1 level) 2))   ; квантиль уровня 1 − α/2

; среднее при известной σ: x̄ ± z·σ/√n
(define (confint-mean-sigma xs sigma &rest rest)
  (let ((level (if (null? rest) 0.95 (car rest))))
    (st-data xs "confint_mean_sigma" 1)
    (st-level level "confint_mean_sigma")
    (st-req (and (number? sigma) (> sigma 0)) "confint_mean_sigma" "σ — положительное число")
    (let* ((n (length xs)) (m (st-fl (st-mean xs)))
           (qq (st-q-record 'z (normal-dist 0 1) (st-level-p level) 0 0 level 0))
           (h (* (car qq) (/ (st-fl sigma) (sqrt (st-fl n))))))
      (st-ci-result 'z (- m h) (+ m h) level (car qq) (cadr qq) (list (list 'n n) (list 'mean (st-mean xs)))))))

; среднее при неизвестной σ: x̄ ± t_{n−1}·s/√n
(define (confint-mean xs &rest rest)
  (let ((level (if (null? rest) 0.95 (car rest))))
    (st-data xs "confint_mean" 2)
    (st-level level "confint_mean")
    (let* ((n (length xs)) (df (- n 1)) (m (st-fl (st-mean xs)))
           (qq (st-q-record 't (student-dist df) (st-level-p level) 0 0 level 0))
           (se (/ (st-sd-num (st-svar xs)) (sqrt (st-fl n))))
           (h (* (car qq) se)))
      (st-ci-result 't (- m h) (+ m h) level (car qq) (cadr qq)
                    (list (list 'df df) (list 'n n) (list 'mean (st-mean xs)) (list 'std_error se))))))

; дисперсия: [(n−1)s²/χ²_{1−α/2}, (n−1)s²/χ²_{α/2}], χ² с n − 1 степенью свободы
(define (confint-variance xs &rest rest)
  (let ((level (if (null? rest) 0.95 (car rest))))
    (st-data xs "confint_variance" 2)
    (st-level level "confint_variance")
    (let* ((n (length xs)) (df (- n 1)) (ss (st-fl (st-ssq xs)))
           (d (chi2-dist df))
           (qhi (st-q-record 'chi2 d (st-level-p level) 0 0 level 0))
           (qlo (st-q-record 'chi2 d (/ (- 1 level) 2) 0 0 level 0)))
      (st-ci-result 'chi2 (/ ss (car qhi)) (/ ss (car qlo)) level (list (car qlo) (car qhi))
                    (max (cadr qlo) (cadr qhi))
                    (list (list 'df df) (list 'n n) (list 'sample_variance (st-svar xs)))))))

(define (st-prop-check k n name)
  (st-req (and (integer? n) (> n 0)) name "n — целое > 0")
  (st-req (and (integer? k) (>= k 0) (<= k n)) name "число успехов — целое от 0 до n"))

; доля, нормальное приближение (Вальд): p̂ ± z·√(p̂(1−p̂)/n), обрезано до [0, 1]
(define (confint-proportion k n &rest rest)
  (let ((level (if (null? rest) 0.95 (car rest))))
    (st-prop-check k n "confint_proportion")
    (st-level level "confint_proportion")
    (let* ((ph (st-fl (/ k n)))
           (qq (st-q-record 'z (normal-dist 0 1) (st-level-p level) 0 0 level 0))
           (h (* (car qq) (sqrt (/ (* ph (- 1.0 ph)) n)))))
      (st-ci-result 'z (max 0.0 (- ph h)) (min 1.0 (+ ph h)) level (car qq) (cadr qq)
                    (list (list 'method 'wald) (list 'estimate (/ k n)))))))

; доля, интервал Уилсона
(define (confint-wilson k n &rest rest)
  (let ((level (if (null? rest) 0.95 (car rest))))
    (st-prop-check k n "confint_wilson")
    (st-level level "confint_wilson")
    (let* ((ph (st-fl (/ k n)))
           (qq (st-q-record 'z (normal-dist 0 1) (st-level-p level) 0 0 level 0))
           (z (car qq)) (z2 (* z z)) (den (+ 1.0 (/ z2 n)))
           (c (/ (+ ph (/ z2 (* 2.0 n))) den))
           (h (* (/ z den) (sqrt (+ (/ (* ph (- 1.0 ph)) n) (/ z2 (* 4.0 n n)))))))
      (st-ci-result 'z (max 0.0 (- c h)) (min 1.0 (+ c h)) level z (cadr qq)
                    (list (list 'method 'wilson) (list 'estimate (/ k n)))))))

; ---------- проверка гипотез ----------

; хвосты: alt = two_sided | less | greater; sf/cdf — функции (значение граница)
(define (st-alt a name)
  (st-req (member? a '(two_sided less greater)) name "альтернатива: two_sided, less или greater")
  a)

(define (st-p-record test stat extra p alpha alt)
  (let ((pp (max 0.0 (min 1.0 p))))
    (append (list (list 'test test) (list 'statistic stat))
            extra
            (list (list 'p_value pp) (list 'alpha alpha) (list 'alternative alt)
                  (list 'reject (< pp alpha))
                  (list 'decision (if (< pp alpha) "отвергаем H0" "не отвергаем H0"))))))

; p для t-статистики с df степенями свободы
(define (st-t-pvalue t df alt)
  (let* ((d (student-dist df))
         (lo (car (st-dist-cdf d t))) (hi (car (st-dist-sf d t))))
    (cond ((equal? alt 'two_sided) (* 2.0 (min lo hi)))
          ((equal? alt 'less) lo)
          (else hi))))

; разбор необязательных аргументов: число из (0, 1) — α; символ — альтернатива; целое ≥ 1 — ddof; yates — поправка
(define (st-opts rest name)
  (let loop ((r rest) (alpha 0.05) (alt 'two_sided) (ddof 0) (yates #f))
    (cond ((null? r) (list alpha alt ddof yates))
          ((equal? (car r) 'yates) (loop (cdr r) alpha alt ddof #t))
          ((symbol? (car r)) (loop (cdr r) alpha (st-alt (car r) name) ddof yates))
          ((and (number? (car r)) (> (car r) 0) (< (car r) 1)) (loop (cdr r) (car r) alt ddof yates))
          ((and (integer? (car r)) (>= (car r) 1)) (loop (cdr r) alpha alt (car r) yates))
          (else (st-err name "необязательные аргументы: α из (0, 1), two_sided/less/greater, yates, целое ddof")))))

(define (st-nz v name) (st-req (> v 0) name "нулевая дисперсия: статистика не определена"))

; t-критерий одной выборки: H0: μ = μ₀; t = (x̄ − μ₀)/(s/√n), df = n − 1
(define (t-test xs mu0 &rest rest)
  (st-data xs "t_test" 2)
  (st-req (number? mu0) "t_test" "μ₀ — число")
  (let* ((o (st-opts rest "t_test")) (n (length xs)) (v (st-svar xs)))
    (st-nz v "t_test")
    (let* ((t (/ (st-fl (- (st-mean xs) mu0)) (sqrt (/ (st-fl v) n)))) (df (- n 1)))
      (st-p-record 't_one_sample t (list (list 'df df) (list 'mean (st-mean xs)))
                   (st-t-pvalue t df (cadr o)) (car o) (cadr o)))))

; двухвыборочный: Уэлч (по умолчанию) или с равными дисперсиями (pooled?)
(define (st-t-two xs ys pooled? name rest)
  (st-data xs name 2)
  (st-data ys name 2)
  (let* ((o (st-opts rest name)) (n1 (length xs)) (n2 (length ys))
         (v1 (st-svar xs)) (v2 (st-svar ys)) (dm (st-fl (- (st-mean xs) (st-mean ys)))))
    (if pooled?
        (let* ((df (+ n1 n2 -2)) (sp (/ (+ (* (- n1 1) v1) (* (- n2 1) v2)) df)))
          (st-nz sp name)
          (let ((t (/ dm (sqrt (st-fl (* sp (+ (/ 1 n1) (/ 1 n2))))))))
            (st-p-record 't_two_sample_pooled t (list (list 'df df) (list 'pooled_variance sp))
                         (st-t-pvalue t df (cadr o)) (car o) (cadr o))))
        (let* ((a (st-fl (/ v1 n1))) (b (st-fl (/ v2 n2))))
          (st-nz (+ a b) name)
          (let* ((t (/ dm (sqrt (+ a b))))
                 (df (/ (st-sq (+ a b)) (+ (/ (st-sq a) (- n1 1)) (/ (st-sq b) (- n2 1))))))
            (st-p-record 't_two_sample_welch t (list (list 'df df))
                         (st-t-pvalue t df (cadr o)) (car o) (cadr o)))))))

(define (t-test-two xs ys &rest rest) (st-t-two xs ys #f "t_test_two" rest))
(define (t-test-pooled xs ys &rest rest) (st-t-two xs ys #t "t_test_pooled" rest))

(define (t-test-paired xs ys &rest rest)
  (st-data xs "t_test_paired" 2)
  (st-req (and (st-num-list? ys) (= (length xs) (length ys))) "t_test_paired" "две выборки одной длины")
  (let ((r (apply t-test (cons (map2 - xs ys) (cons 0 rest)))))
    (cons (list 'test 't_paired) (cdr r))))

; χ²-согласия: observed, expected (частоты; сумма совпадает), необязательно α и ddof (число оценённых параметров)
(define (chi2-gof obs expd &rest rest)
  (st-req (and (st-num-list? obs) (st-num-list? expd) (= (length obs) (length expd)) (>= (length obs) 2))
          "chi2_gof" "ожидаются два списка чисел одной длины ≥ 2: наблюдаемые и ожидаемые частоты")
  (st-req (every? (lambda (x) (>= x 0)) obs) "chi2_gof" "наблюдаемая частота отрицательна")
  (st-req (every? (lambda (x) (> x 0)) expd) "chi2_gof" "ожидаемые частоты должны быть положительными")
  (let ((so (apply + obs)) (se (apply + expd)))
    (st-req (or (equal? so se) (and (not (equal? so 0)) (< (abs (/ (- so se) so)) 1e-9))) "chi2_gof"
            (string-append "суммы наблюдаемых (" (to-string so) ") и ожидаемых (" (to-string se) ") частот различаются"))
    (let* ((o (st-opts rest "chi2_gof")) (df (- (length obs) 1 (caddr o))))
      (st-req (>= df 1) "chi2_gof" "число степеней свободы k − 1 − ddof должно быть ≥ 1")
      (if (any? (lambda (e) (< e 5)) expd)
          (record-condition '(>= expected 5) "ожидаемые частоты < 5: χ²-приближение ненадёжно")
          #f)
      (let* ((stat (apply + (map2 (lambda (x e) (/ (st-sq (- x e)) e)) obs expd)))
             (p (car (st-dist-sf (chi2-dist df) stat))))
        (st-p-record 'chi2_goodness stat (list (list 'df df)) p (car o) 'greater)))))

; χ²-независимости по таблице сопряжённости (список строк); yates — поправка для 2×2
(define (chi2-independence table &rest rest)
  (st-req (and (list? table) (>= (length table) 2) (every? st-num-list? table)
               (every? (lambda (r) (= (length r) (length (car table)))) table) (>= (length (car table)) 2))
          "chi2_independence" "ожидается таблица (список строк одной длины, не меньше 2×2)")
  (st-req (every? (lambda (r) (every? (lambda (x) (>= x 0)) r)) table) "chi2_independence" "в таблице есть отрицательная частота")
  (let* ((o (st-opts rest "chi2_independence")) (nr (length table)) (nc (length (car table)))
         (rows (map (lambda (r) (apply + r)) table))
         (cols (let loop ((j 0) (acc '()))
                 (if (= j nc) (reverse acc)
                     (loop (+ j 1) (cons (apply + (map (lambda (r) (nth r j)) table)) acc)))))
         (n (apply + rows)))
    (st-req (> n 0) "chi2_independence" "в таблице нет наблюдений")
    (st-req (and (every? (lambda (x) (> x 0)) rows) (every? (lambda (x) (> x 0)) cols)) "chi2_independence"
            "нулевая строка или столбец: ожидаемая частота 0, статистика не определена")
    (st-req (or (not (nth o 3)) (and (= nr 2) (= nc 2))) "chi2_independence" "поправка Йейтса — только для таблицы 2×2")
    (let* ((exps (map (lambda (ri) (map (lambda (cj) (/ (* ri cj) n)) cols)) rows))
           (yates (nth o 3))
           (cell (lambda (x e) (let ((d (if yates (max 0 (- (abs (- x e)) 1/2)) (- x e)))) (/ (st-sq d) e))))
           (stat (apply + (map2 (lambda (rx re) (apply + (map2 cell rx re))) table exps)))
           (df (* (- nr 1) (- nc 1))))
      (if (any? (lambda (r) (any? (lambda (e) (< e 5)) r)) exps)
          (record-condition '(>= expected 5) "ожидаемые частоты < 5: χ²-приближение ненадёжно")
          #f)
      (st-p-record (if yates 'chi2_independence_yates 'chi2_independence) stat
                   (list (list 'df df) (list 'expected exps))
                   (car (st-dist-sf (chi2-dist df) stat)) (car o) 'greater))))

; F-критерий равенства дисперсий: F = s₁²/s₂², df = (n₁ − 1, n₂ − 1)
(define (f-test-variances xs ys &rest rest)
  (st-data xs "f_test" 2)
  (st-data ys "f_test" 2)
  (let* ((o (st-opts rest "f_test")) (v1 (st-svar xs)) (v2 (st-svar ys)))
    (st-req (> v2 0) "f_test" "дисперсия второй выборки равна нулю")
    (st-req (> v1 0) "f_test" "дисперсия первой выборки равна нулю")
    (let* ((d1 (- (length xs) 1)) (d2 (- (length ys) 1)) (f (/ v1 v2)) (d (f-dist d1 d2))
           (lo (car (st-dist-cdf d f))) (hi (car (st-dist-sf d f)))
           (alt (cadr o))
           (p (cond ((equal? alt 'two_sided) (* 2.0 (min lo hi))) ((equal? alt 'less) lo) (else hi))))
      (st-p-record 'f_variances f (list (list 'df (list d1 d2))) p (car o) alt))))
