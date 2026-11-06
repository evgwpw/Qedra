; curvature.lisp — тесты шага TEN: метрика и кривизна (Кристоффель, Риман, Риччи, Эйнштейн, ∇, Бьянки, сертификат).
; Конвенция MTW/Wald: R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + …; у сферы R > 0.

(define ten-pol '((1 0) (0 (^ r 2))))
(define ten-spf '((1 0 0) (0 (^ r 2) 0) (0 0 (* (^ r 2) (^ (sin th) 2)))))
(define ten-sph '(((^ a 2) 0) (0 (* (^ a 2) (^ (sin th) 2)))))
(define ten-s3 '((1 0 0) (0 (^ (sin chi) 2) 0) (0 0 (* (^ (sin chi) 2) (^ (sin th) 2)))))
(define ten-poi '(((^ y -2) 0) (0 (^ y -2))))
(define ten-f '(+ 1 (* -2 (/ m r))))
(define ten-sch (list (list (list '* -1 ten-f) 0 0 0) (list 0 (list '^ ten-f -1) 0 0)
                      (list 0 0 '(^ r 2) 0) (list 0 0 0 '(* (^ r 2) (^ (sin th) 2)))))
(define ten-frw '((-1 0 0 0) (0 (^ (a t) 2) 0 0) (0 0 (^ (a t) 2) 0) (0 0 0 (^ (a t) 2))))
(define ten-sx '(t r th ph))

; все компоненты тензора равны 0
(define (ten-zero? t) (every? (lambda (x) (equal? (curvature-normalize x) 0)) (vector->list (tensor-data t))))

; R_{abcd} сферы: s — знак всех компонент, s2 — знак компоненты (1 0 1 0)
(define (ten-r4 s s2)
  (let ((x '(* (^ a 2) (^ (sin th) 2))))
    (make-tensor '(2 2 2 2)
                 (lambda (i)
                   (cond ((equal? i '(0 1 0 1)) (list '* s x))
                         ((equal? i '(1 0 1 0)) (list '* (* s s2) x))
                         ((member? i '((0 1 1 0) (1 0 0 1))) (list '* (- s) x))
                         (else 0))))))

(deftest "curvature: метрика полярных координат — Γ^r_θθ = −r, Γ^θ_rθ = 1/r, Риман = 0"
  (let ((g (christoffel ten-pol '(r th))))
    (assert-equal (tref g 0 1 1) '(* -1 r))
    (assert-equal (tref g 1 0 1) '(^ r -1))
    (assert-equal (tref g 1 1 0) '(^ r -1))
    (assert-equal (tref g 0 0 0) 0))
  (assert-true (ten-zero? (riemann ten-pol '(r th))))
  (assert-equal (ricci-scalar ten-pol '(r th)) 0))

(deftest "curvature: плоская метрика в сферических координатах — Γ ненулевые, Риман ≡ 0, Эйнштейн = 0"
  (let ((g (christoffel ten-spf '(r th ph))))
    (assert-equal (tref g 0 1 1) '(* -1 r))
    (assert-equal (tref g 0 2 2) '(* -1 r (^ (sin th) 2)))
    (assert-equal (tref g 1 0 1) '(^ r -1))
    (assert-equal (tref g 1 2 2) '(* -1 (cos th) (sin th)))
    (assert-equal (tref g 2 1 2) '(* (cos th) (^ (sin th) -1))))
  (assert-true (ten-zero? (riemann ten-spf '(r th ph))))
  (assert-true (ten-zero? (riemann-lower ten-spf '(r th ph))))
  (assert-true (ten-zero? (einstein ten-spf '(r th ph)))))

(deftest "curvature: обратная метрика"
  (assert-equal (tensor->list (metric-inverse ten-pol '(r th))) '((1 0) (0 (^ r -2))))
  ; недиагональная: g · g⁻¹ = единица
  (let* ((g '((1 x) (x 2))) (gi (metric-inverse g '(x y))) (p (mat-mul g gi)))
    (assert-true (ten-zero? (- p (identity-matrix 2))))))

(deftest "curvature: сфера радиуса a — R_θφθφ = a² sin²θ, Ricci = g/a², R = 2/a², Эйнштейн = 0 (2D)"
  (let ((rl (riemann-lower ten-sph '(th ph))))
    (assert-equal (tref rl 0 1 0 1) '(* (^ a 2) (^ (sin th) 2)))
    (assert-equal (tref rl 1 0 0 1) '(* -1 (^ a 2) (^ (sin th) 2)))
    (assert-equal (tref rl 1 0 1 0) '(* (^ a 2) (^ (sin th) 2)))
    (assert-equal (tref rl 0 1 1 0) '(* -1 (^ a 2) (^ (sin th) 2))))
  (assert-equal (tensor->list (ricci ten-sph '(th ph))) '((1 0) (0 (^ (sin th) 2))))
  (assert-equal (ricci-scalar ten-sph '(th ph)) '(* 2 (^ a -2)))
  (assert-true (ten-zero? (einstein ten-sph '(th ph))))
  (assert-equal (kretschmann ten-sph '(th ph)) '(* 4 (^ a -4))))

(deftest "curvature: сфера — сертификат и подделка"
  (assert-equal (curvature-check ten-sph '(th ph) 'ricci-scalar '(* 2 (^ a -2))) 'verified)
  (assert-equal (curvature-check ten-sph '(th ph) 'ricci-scalar '(^ a -2)) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'ricci-scalar '(* -2 (^ a -2))) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'ricci '((1 0) (0 (^ (sin th) 2)))) 'verified)
  (assert-equal (curvature-check ten-sph '(th ph) 'ricci '((1 0) (0 (* 2 (^ (sin th) 2))))) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'ricci '((1 0) (0 (^ (cos th) 2)))) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'riemann-lower (ten-r4 1 1)) 'verified)
  (assert-equal (curvature-check ten-sph '(th ph) 'riemann-lower (ten-r4 -1 1)) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'riemann-lower (ten-r4 1 -1)) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'kretschmann '(* 4 (^ a -4))) 'verified)
  (assert-equal (curvature-check ten-sph '(th ph) 'kretschmann '(* 2 (^ a -4))) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'einstein '((0 0) (0 0))) 'verified)
  (assert-equal (curvature-check ten-sph '(th ph) 'einstein '((1 0) (0 0))) 'mismatch)
  (assert-equal (curvature-check ten-sph '(th ph) 'christoffel
                                 '(((0 0) (0 (* -1 (cos th) (sin th)))) ((0 (* (cos th) (^ (sin th) -1))) ((* (cos th) (^ (sin th) -1)) 0))))
                'verified)
  (assert-equal (curvature-check ten-sph '(th ph) 'christoffel
                                 '(((0 0) (0 (* (cos th) (sin th)))) ((0 (* (cos th) (^ (sin th) -1))) ((* (cos th) (^ (sin th) -1)) 0))))
                'mismatch)
  (assert-error (curvature-check ten-sph '(th ph) 'nonsense 0)))

(deftest "curvature: 3-сфера R = 6, Ricci = 2g; плоскость Пуанкаре R = −2"
  (assert-equal (ricci-scalar ten-s3 '(chi th ph)) 6)
  (assert-equal (tensor->list (ricci ten-s3 '(chi th ph)))
                '((2 0 0) (0 (* 2 (^ (sin chi) 2)) 0) (0 0 (* 2 (^ (sin chi) 2) (^ (sin th) 2)))))
  (assert-equal (ricci-scalar ten-poi '(x y)) -2)
  (assert-equal (curvature-check ten-poi '(x y) 'ricci-scalar -2) 'verified)
  (assert-equal (curvature-check ten-poi '(x y) 'ricci-scalar 2) 'mismatch))

(deftest "curvature: Шварцшильд — Ricci ≡ 0, R = 0, K = 48 m²/r⁶"
  (assert-true (ten-zero? (ricci ten-sch ten-sx)))
  (assert-equal (ricci-scalar ten-sch ten-sx) 0)
  (assert-equal (kretschmann ten-sch ten-sx) '(* 48 (^ m 2) (^ r -6)))
  (assert-equal (curvature-check ten-sch ten-sx 'ricci-scalar 0) 'verified)
  (assert-equal (curvature-check ten-sch ten-sx 'ricci-scalar 1) 'mismatch)
  (assert-equal (curvature-check ten-sch ten-sx 'kretschmann '(* 48 (^ m 2) (^ r -6))) 'verified)
  (assert-equal (curvature-check ten-sch ten-sx 'kretschmann '(* 12 (^ m 2) (^ r -6))) 'mismatch)
  (assert-equal (curvature-check ten-sch ten-sx 'ricci (make-tensor '(4 4) (lambda (i) 0))) 'verified)
  (assert-equal (curvature-check ten-sch ten-sx 'ricci (make-tensor '(4 4) (lambda (i) (if (equal? i '(0 0)) 1 0)))) 'mismatch))

(deftest "curvature: Шварцшильд — Γ^t_tr = m/(r(r − 2m)), Γ^r_tt = m(r − 2m)/r³"
  (let ((g (christoffel ten-sch ten-sx)))
    (assert-equal (curvature-normalize (list '+ (tref g 0 0 1) (list '* -1 (list '* 'm (list '^ (list '* 'r (list '+ 'r (list '* -2 'm))) -1))))) 0)
    (assert-equal (curvature-normalize (list '+ (tref g 1 0 0) (list '* -1 (list '* 'm (list '+ 'r (list '* -2 'm)) (list '^ 'r -3))))) 0)
    (assert-equal (tref g 3 2 3) '(* (cos th) (^ (sin th) -1)))))

(deftest "curvature: FRW — R = 6 (a'' / a + a'² / a²) с символьной функцией a(t); подделка — mismatch"
  (let ((rs (ricci-scalar ten-frw ten-sx)))
    (assert-equal (curvature-normalize (list '+ rs (list '* -1 '(* 6 (+ (/ (diff (diff (a t) t) t) (a t)) (/ (^ (diff (a t) t) 2) (^ (a t) 2)))))))
                  0))
  (assert-equal (curvature-check ten-frw ten-sx 'ricci-scalar
                                 '(* 6 (+ (/ (diff (diff (a t) t) t) (a t)) (/ (^ (diff (a t) t) 2) (^ (a t) 2)))))
                'verified)
  (assert-equal (curvature-check ten-frw ten-sx 'ricci-scalar
                                 '(* 6 (+ (/ (diff (diff (a t) t) t) (a t)) (* 2 (/ (^ (diff (a t) t) 2) (^ (a t) 2))))))
                'mismatch)
  (assert-equal (curvature-check ten-frw ten-sx 'ricci-scalar 0) 'mismatch))

(deftest "curvature: ∇g = 0 — сфера, Шварцшильд, FRW"
  (assert-true (ten-zero? (covariant-derivative (tensor ten-sph) '(down down) ten-sph '(th ph))))
  (assert-true (ten-zero? (covariant-derivative (tensor ten-sch) '(down down) ten-sch ten-sx)))
  (assert-true (ten-zero? (covariant-derivative (tensor ten-frw) '(down down) ten-frw ten-sx)))
  ; обратная метрика (верхние индексы)
  (assert-true (ten-zero? (covariant-derivative (metric-inverse ten-sch ten-sx) '(up up) ten-sch ten-sx))))

(deftest "curvature: ∇ скаляра и вектора — градиент и дивергенция в полярных координатах"
  ; скаляр f = r² cos θ: (∇f)_e = ∂_e f
  (let ((d (covariant-derivative '(* (^ r 2) (cos th)) '() ten-pol '(r th))))
    (assert-equal (tensor->list d) '((* 2 r (cos th)) (* -1 (^ r 2) (sin th)))))
  ; ∇_a V^a для V = r ∂_r (радиальное поле, плоскость): div = 2
  (let* ((d (covariant-derivative (tensor '(r 0)) '(up) ten-pol '(r th)))
         (div (simplify (list '+ (tref d 0 0) (tref d 1 1)))))
    (assert-equal div 2))
  (assert-error (covariant-derivative (tensor '(r 0)) '(up down) ten-pol '(r th)))
  (assert-error (covariant-derivative (tensor '(r 0)) '(sideways) ten-pol '(r th))))

(define (ten-mixed-einstein g xs)
  ; G^a_b = g^{ac} G_{cb}
  (let ((gi (metric-inverse g xs)) (ge (einstein g xs)))
    (mat-mul gi ge)))

(define (ten-div-einstein g xs)
  ; ∇_a G^a_b — свёртка ∇_e G^a_b по (a, e): тензор (a b e) → индексы 0 и 2
  (let ((d (covariant-derivative (ten-mixed-einstein g xs) '(up down) g xs)))
    (contract d 0 2)))

(deftest "curvature: свёрнутое тождество Бьянки ∇_a G^{ab} = 0 — сфера, Шварцшильд, FRW"
  (assert-true (ten-zero? (ten-div-einstein ten-sph '(th ph))))
  (assert-true (ten-zero? (ten-div-einstein ten-sch ten-sx)))
  (assert-true (ten-zero? (ten-div-einstein ten-frw ten-sx))))

(deftest "curvature: ∇_a G^a_b = 0 для метрики с ненулевым Эйнштейном — 3-сфера не плоская, но Бьянки выполнено"
  (assert-true (not (ten-zero? (einstein ten-s3 '(chi th ph)))))
  (assert-true (ten-zero? (ten-div-einstein ten-s3 '(chi th ph)))))

; R^a_{bcd} + R^a_{cdb} + R^a_{dbc} = 0
(define (ten-first-bianchi g xs)
  (let* ((r (riemann g xs)) (n (length xs)))
    (every? (lambda (idx)
              (let ((a (nth idx 0)) (b (nth idx 1)) (c (nth idx 2)) (d (nth idx 3)))
                (equal? (curvature-normalize (list '+ (tref r a b c d) (tref r a c d b) (tref r a d b c))) 0)))
            (all-quads n))))
(define (all-quads n)
  (append-map (lambda (a) (append-map (lambda (b) (append-map (lambda (c) (map (lambda (d) (list a b c d)) (range n))) (range n))) (range n))) (range n)))

(deftest "curvature: первое тождество Бьянки R^a_[bcd] = 0 — сфера, 3-сфера, Шварцшильд, FRW"
  (assert-true (ten-first-bianchi ten-sph '(th ph)))
  (assert-true (ten-first-bianchi ten-s3 '(chi th ph)))
  (assert-true (ten-first-bianchi ten-sch ten-sx))
  (assert-true (ten-first-bianchi ten-frw ten-sx)))

; ∇_e R_{abcd} + ∇_c R_{abde} + ∇_d R_{abec} = 0 (2D и 3D)
(define (ten-second-bianchi g xs)
  (let* ((n (length xs))
         (d (covariant-derivative (riemann-lower g xs) '(down down down down) g xs)))
    (every? (lambda (idx)
              (let ((a (nth idx 0)) (b (nth idx 1)) (c (nth idx 2)) (dd (nth idx 3)) (e (nth idx 4)))
                (equal? (curvature-normalize (list '+ (tref d a b c dd e) (tref d a b dd e c) (tref d a b e c dd))) 0)))
            (append-map (lambda (q) (map (lambda (e) (append q (list e))) (range n))) (all-quads n)))))

(deftest "curvature: второе тождество Бьянки — сфера и 3-сфера"
  (assert-true (ten-second-bianchi ten-sph '(th ph)))
  (assert-true (ten-second-bianchi ten-s3 '(chi th ph))))

(deftest "curvature: геодезические полярной плоскости: r'' = r θ'², θ'' = −2 r' θ' / r"
  (let ((eqs (geodesic-equations ten-pol '(r th) 's)))
    (assert-equal (length eqs) 2)
    (assert-equal (car eqs) '(= (diff (diff (r s) s) s) (* (^ (diff (th s) s) 2) (r s))))
    (assert-equal (cadr eqs) '(= (diff (diff (th s) s) s) (* -2 (diff (r s) s) (diff (th s) s) (^ (r s) -1))))))

(deftest "curvature: недиагональная плоская метрика (x = u + v², y = v) — Γ ненулевые, Риман ≡ 0; общий путь обращения"
  (let ((g '((1 (* 2 v)) ((* 2 v) (+ 1 (* 4 (^ v 2)))))))
    (assert-true (not (ten-zero? (christoffel g '(u v)))))
    (assert-true (ten-zero? (riemann g '(u v))))
    (assert-equal (ricci-scalar g '(u v)) 0)
    (assert-true (ten-zero? (covariant-derivative (tensor g) '(down down) g '(u v))))))

(deftest "curvature: ошибки входа — несимметричная метрика, размеры, координаты"
  (assert-error (christoffel '((1 1) (0 1)) '(x y)))
  (assert-error (christoffel '((1 0) (0 1)) '(x)))
  (assert-error (christoffel '((1 0) (0 1)) '(x 1)))
  (assert-error (ricci '((1 0 0) (0 1)) '(x y))))

(deftest "curvature: входной язык — christoffel, riemann, ricci, ricci_scalar, einstein, kretschmann, curvature_check"
  (assert-equal (math-eval "ricci_scalar([[a^2, 0], [0, a^2*sin(th)^2]], [th, ph])") '(* 2 (^ a -2)))
  (assert-equal (math-eval "kretschmann([[1, 0, 0], [0, r^2, 0], [0, 0, r^2*sin(th)^2]], [r, th, ph])") 0)
  (assert-equal (math-eval "curvature_check([[a^2, 0], [0, a^2*sin(th)^2]], [th, ph], ricci_scalar, 2/a^2)") 'verified)
  (assert-equal (math-eval "curvature_check([[a^2, 0], [0, a^2*sin(th)^2]], [th, ph], ricci_scalar, 1/a^2)") 'mismatch)
  (assert-equal (math-eval "christoffel([[1, 0], [0, r^2]], [r, th])[1, 2, 2]") '(* -1 r))
  (assert-equal (math-eval "ricci([[a^2, 0], [0, a^2*sin(th)^2]], [th, ph])[2, 2]") '(^ (sin th) 2))
  (assert-equal (math-eval "einstein([[a^2, 0], [0, a^2*sin(th)^2]], [th, ph])[1, 1]") 0))
