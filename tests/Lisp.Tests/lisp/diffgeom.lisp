; diffgeom.lisp — тесты шага DG: дифференциальная геометрия кривых и поверхностей.
; Оракулы: (1) общеизвестные значения — окружность (κ = 1/R, τ = 0), винтовая линия (κ = a/(a²+b²), τ = b/(a²+b²)),
; парабола (κ(0) = 2), сфера (K = 1/R²), цилиндр, плоскость, тор, седло z = xy (K = −1 в нуле);
; (2) независимая численная проверка конечными разностями по исходной параметризации (формулы пятиточечные, шаг 0.01),
; не использующая символьный путь: кривизна кривых и K, H, главные кривизны поверхностей в трёх точках;
; (3) Гаусс–Бонне: сфера (χ = 2) и тор (χ = 0); (4) подделки: прямая, вырожденные точки и параметризации, неверный χ.

(define (dg-t-close? a b tol) (< (abs (- a b)) tol))

; ---- численные векторные вычисления без символьного пути ----
(define (dg-t-vpt r bindings) (map (lambda (c) (eval-num (subst bindings c))) r))
(define (dg-t-vlin cs vs)
  (map (lambda (i) (foldl (lambda (acc p) (+ acc (* (car p) (nth (cdr p) i)))) 0 (map2 cons cs vs)))
       (range (length (car vs)))))
(define (dg-t-vscale k v) (map (lambda (x) (* k x)) v))
(define (dg-t-vdot a b) (foldl (lambda (acc p) (+ acc (* (car p) (cdr p)))) 0 (map2 cons a b)))
(define (dg-t-vnorm a) (eval-num (list 'sqrt (dg-t-vdot a a))))
(define (dg-t-vcross a b)
  (list (- (* (nth a 1) (nth b 2)) (* (nth a 2) (nth b 1)))
        (- (* (nth a 2) (nth b 0)) (* (nth a 0) (nth b 2)))
        (- (* (nth a 0) (nth b 1)) (* (nth a 1) (nth b 0)))))

; f: число → вектор; производные по x пятиточечными формулами
(define (dg-t-d1 f x h)
  (dg-t-vscale (/ 1 (* 12 h)) (dg-t-vlin '(-1 8 -8 1) (list (f (+ x (* 2 h))) (f (+ x h)) (f (- x h)) (f (- x (* 2 h)))))))
(define (dg-t-d2 f x h)
  (dg-t-vscale (/ 1 (* 12 h h))
               (dg-t-vlin '(-1 16 -30 16 -1) (list (f (+ x (* 2 h))) (f (+ x h)) (f x) (f (- x h)) (f (- x (* 2 h)))))))
; третья производная (шеститочечная формула)
(define (dg-t-d3 f x h)
  (dg-t-vscale (/ 1 (* 8 h h h))
               (dg-t-vlin '(-1 8 -13 13 -8 1)
                          (list (f (+ x (* 3 h))) (f (+ x (* 2 h))) (f (+ x h)) (f (- x h)) (f (- x (* 2 h))) (f (- x (* 3 h)))))))

(define dg-t-h 0.01)

; кривизна ℝ³ и ℝ² (со знаком) по численным производным
(define (dg-t-curv-num r t0)
  (let* ((f (lambda (x) (dg-t-vpt r (list (list 't x)))))
         (d1 (dg-t-d1 f t0 dg-t-h)) (d2 (dg-t-d2 f t0 dg-t-h)))
    (if (= (length d1) 3)
        (/ (dg-t-vnorm (dg-t-vcross d1 d2)) (^ (dg-t-vnorm d1) 3))
        (/ (- (* (nth d1 0) (nth d2 1)) (* (nth d1 1) (nth d2 0))) (^ (dg-t-vnorm d1) 3)))))

(define (dg-t-tors-num r t0)
  (let* ((f (lambda (x) (dg-t-vpt r (list (list 't x)))))
         (d1 (dg-t-d1 f t0 0.02)) (d2 (dg-t-d2 f t0 0.02)) (d3 (dg-t-d3 f t0 0.02))
         (w (dg-t-vcross d1 d2)))
    (/ (dg-t-vdot w d3) (dg-t-vdot w w))))

; поверхность: K, H по конечным разностям r(u, v)
(define (dg-t-surf-num r u0 v0)
  (let* ((f (lambda (x y) (dg-t-vpt r (list (list 'u x) (list 'v y)))))
         (h dg-t-h)
         (ru (lambda (y) (dg-t-d1 (lambda (x) (f x y)) u0 h)))
         (ru0 (dg-t-d1 (lambda (x) (f x v0)) u0 h))
         (rv0 (dg-t-d1 (lambda (y) (f u0 y)) v0 h))
         (ruu (dg-t-d2 (lambda (x) (f x v0)) u0 h))
         (rvv (dg-t-d2 (lambda (y) (f u0 y)) v0 h))
         (ruv (dg-t-d1 (lambda (y) (ru y)) v0 h))
         (e (dg-t-vdot ru0 ru0)) (ff (dg-t-vdot ru0 rv0)) (g (dg-t-vdot rv0 rv0))
         (w (dg-t-vcross ru0 rv0)) (wn (dg-t-vnorm w))
         (l (/ (dg-t-vdot ruu w) wn)) (m (/ (dg-t-vdot ruv w) wn)) (n (/ (dg-t-vdot rvv w) wn))
         (d (- (* e g) (* ff ff))))
    (list (/ (- (* l n) (* m m)) d)
          (/ (+ (- (* e n) (* 2 ff m)) (* g l)) (* 2 d)))))

(define (dg-t-num e) (eval-num e))

; ---- кривые: общеизвестные значения ----
(define dg-circle '((* R (cos t)) (* R (sin t))))
(define dg-helix '((* a (cos t)) (* a (sin t)) (* b t)))

(deftest "diffgeom: окружность — κ = 1/R, радиус R, скорость R (при R > 0)"
  (assuming ((R positive))
    (assert-equal (curvature dg-circle 't) (simplify '(^ R -1)))
    (assert-equal (curvature-radius dg-circle 't) 'R)
    (assert-equal (curve-speed dg-circle 't) 'R)
    (assert-equal (curvature '((* R (cos t)) (* R (sin t)) 0) 't) (simplify '(^ R -1)))
    (assert-equal (torsion '((* R (cos t)) (* R (sin t)) 0) 't) 0)))

(deftest "diffgeom: окружность без знака R — корень честно остаётся с abs, не R"
  (let ((sp (curve-speed dg-circle 't)))
    (assert-true (contains-sym? sp 'abs))
    (assert-true (not (equal? sp 'R)))))

(deftest "diffgeom: винтовая линия — κ = a/(a²+b²), τ = b/(a²+b²)"
  (assuming ((a positive) (b positive))
    (assert-equal (curvature dg-helix 't) (simplify '(* a (^ (+ (^ a 2) (^ b 2)) -1))))
    (assert-equal (torsion dg-helix 't) (simplify '(* b (^ (+ (^ a 2) (^ b 2)) -1)))))
  (assert-equal (curvature '((cos t) (sin t) t) 't) 1/2)
  (assert-equal (torsion '((cos t) (sin t) t) 't) 1/2)
  (assert-equal (curvature '((cos t) (sin t) t) '(t 5)) 1/2))

(deftest "diffgeom: парабола y = x² — κ(0) = 2; в ℝ² кривизна со знаком"
  (assert-equal (curvature '(t (^ t 2)) '(t 0)) 2)
  (assert-true (dg-t-close? (dg-t-num (curvature '(t (^ t 2)) '(t 1))) (/ 2 (^ 5.0 1.5)) 1e-12))
  ; против часовой стрелки +, по часовой −
  (assert-equal (curvature '((cos t) (sin t)) 't) 1)
  (assert-equal (curvature '((cos t) (* -1 (sin t))) 't) -1)
  (assert-equal (curvature-radius '((cos t) (* -1 (sin t))) 't) 1))

(deftest "diffgeom: репер Френе — ортонормирован, B = T × N, нормаль ℝ² — левая"
  (let* ((fr (frenet-frame '((cos t) (sin t) t) '(t 1)))
         (tg (dg-t-vpt (nth fr 0) '()))
         (nn (dg-t-vpt (nth fr 1) '()))
         (bb (dg-t-vpt (nth fr 2) '())))
    (assert-true (dg-t-close? (dg-t-vnorm tg) 1 1e-12))
    (assert-true (dg-t-close? (dg-t-vnorm nn) 1 1e-12))
    (assert-true (dg-t-close? (dg-t-vdot tg nn) 0 1e-12))
    (assert-true (dg-t-close? (dg-t-vdot tg bb) 0 1e-12))
    (assert-true (dg-t-close? (dg-t-vnorm (map2 - (dg-t-vcross tg nn) bb)) 0 1e-12)))
  (assert-equal (curve-tangent '((cos t) (sin t) t) '(t 0)) (list 0 (simplify '(* 1/2 (^ 2 1/2))) (simplify '(* 1/2 (^ 2 1/2)))))
  (assert-equal (curve-normal '((cos t) (sin t)) 't) '((* -1 (cos t)) (* -1 (sin t))))
  (assert-equal (curve-normal '((cos t) (sin t)) '(t 0)) '(-1 0))
  (assert-equal (curve-binormal '((cos t) (sin t) 0) 't) '(0 0 1)))

(deftest "diffgeom: кривизна и кручение — конечные разности в трёх точках (допуск 1e-8; кручение 1e-6)"
  (let ((curves (list (list '((* 2 (cos t)) (sin t)) '(0.3 1.1 2.5))
                      (list '(t (^ t 2) (^ t 3)) '(0.2 0.7 -0.5))
                      (list '((* 3 (cos t)) (* 3 (sin t)) (* 2 t)) '(0.4 1.7 3.0))
                      (list '((exp t) (cos t) (sin t)) '(0.1 0.6 -0.4)))))
    (for-each
     (lambda (c)
       (for-each (lambda (t0)
                   (assert-true (dg-t-close? (dg-t-num (curvature (car c) (list 't t0))) (dg-t-curv-num (car c) t0) 1e-8)))
                 (cadr c)))
     curves)
    (for-each
     (lambda (c)
       (for-each (lambda (t0)
                   (assert-true (dg-t-close? (dg-t-num (torsion (car c) (list 't t0))) (dg-t-tors-num (car c) t0) 1e-6)))
                 (cadr c)))
     (cdr curves))))

(deftest "diffgeom: прямая и вырожденные точки — κ = 0, кручение и радиус — честные ошибки"
  (assert-equal (curvature '(t (* 2 t) (+ t 1)) 't) 0)
  (assert-equal (curvature '(t (* 2 t)) 't) 0)
  (assert-error (torsion '(t (* 2 t) (+ t 1)) 't))
  (assert-error (curve-binormal '(t (* 2 t) (+ t 1)) 't))
  (assert-error (curvature-radius '(t (* 2 t) (+ t 1)) 't))
  ; r′ = 0 при t = 0: полукубическая парабола (t², t³)
  (assert-error (curvature '((^ t 2) (^ t 3)) '(t 0)))
  (assert-error (curve-tangent '((^ t 2) (^ t 3)) '(t 0)))
  ; кручение не определено в точке спрямления
  (assert-error (torsion '(t (^ t 3) 0) '(t 0)))
  (assert-error (torsion '(t (^ t 2)) 't))
  (assert-error (curvature '(t) 't))
  (assert-error (curve-binormal '((cos t) (sin t)) 't)))

; ---- поверхности ----
; сфера: r(u, v) = (R sin u cos v, R sin u sin v, R cos u), u ∈ (0, π) — полярный угол, v — азимут:
; E = R², F = 0, G = R² sin²u; нормаль r_u × r_v направлена наружу
(define dg-sphere '((* R (sin u) (cos v)) (* R (sin u) (sin v)) (* R (cos u))))
(define dg-torus '((* (+ 3 (cos v)) (cos u)) (* (+ 3 (cos v)) (sin u)) (sin v)))

(deftest "diffgeom: сфера — E = R², F = 0, G = R² sin²u, K = 1/R², H = −1/R (нормаль наружу), главные кривизны равны"
  (assuming ((R positive))
    (assert-equal (first-form dg-sphere 'u 'v) (list (simplify '(^ R 2)) 0 (simplify '(* (^ R 2) (^ (sin u) 2)))))
    (assert-equal (gauss-curvature dg-sphere 'u 'v) (simplify '(^ R -2)))
    (assert-equal (mean-curvature dg-sphere '(u 0 pi) 'v) (simplify '(* -1 (^ R -1))))
    (assert-equal (principal-curvatures dg-sphere '(u 0 pi) 'v)
                  (list (simplify '(* -1 (^ R -1))) (simplify '(* -1 (^ R -1)))))
    (assert-equal (second-form dg-sphere '(u 0 pi) 'v) (list (simplify '(* -1 R)) 0 (simplify '(* -1 R (^ (sin u) 2)))))
    (assert-equal (surface-normal dg-sphere '(u 0 pi) 'v) '((* (cos v) (sin u)) (* (sin u) (sin v)) (cos u)))))

(deftest "diffgeom: сфера без отрезка для u — знак sin u неизвестен, abs остаётся; K от знака не зависит"
  (assuming ((R positive))
    (assert-equal (gauss-curvature dg-sphere 'u 'v) (simplify '(^ R -2)))
    (assert-true (contains-sym? (mean-curvature dg-sphere 'u 'v) 'abs))
    ; в точке u = 1 sin 1 > 0 — знак определён
    (assert-equal (mean-curvature dg-sphere '(u 1) '(v 2)) (simplify '(* -1 (^ R -1))))))

(deftest "diffgeom: цилиндр K = 0, |H| = 1/(2R), главные кривизны {0, −1/R}; плоскость K = H = 0; седло K(0,0) = −1"
  (assuming ((R positive))
    (let ((cyl '((* R (cos u)) (* R (sin u)) v)))
      (assert-equal (gauss-curvature cyl 'u 'v) 0)
      (assert-equal (mean-curvature cyl 'u 'v) (simplify '(* -1/2 (^ R -1))))
      (assert-equal (principal-curvatures cyl 'u 'v) (list (simplify '(* -1 (^ R -1))) 0))))
  (assert-equal (gauss-curvature '(u v (+ (* 2 u) (* 3 v))) 'u 'v) 0)
  (assert-equal (mean-curvature '(u v (+ (* 2 u) (* 3 v))) 'u 'v) 0)
  (assert-equal (gauss-curvature (graph-surface '(* x y) 'x 'y) '(x 0) '(y 0)) -1)
  (assert-equal (gauss-curvature (graph-surface '(* x y) 'x 'y) 'x 'y) (simplify '(* -1 (^ (+ 1 (^ x 2) (^ y 2)) -2))))
  (assert-equal (mean-curvature (graph-surface '(* x y) 'x 'y) '(x 0) '(y 0)) 0)
  ; параболоид z = x² + y² в нуле: K = 4, H = 2 (нормаль r_x × r_y смотрит вверх)
  (assert-equal (gauss-curvature (graph-surface '(+ (^ x 2) (^ y 2)) 'x 'y) '(x 0) '(y 0)) 4)
  (assert-equal (mean-curvature (graph-surface '(+ (^ x 2) (^ y 2)) 'x 'y) '(x 0) '(y 0)) 2))

(deftest "diffgeom: тор (R = 3, r = 1) — K = cos v/(r(R + r cos v))"
  (assert-equal (gauss-curvature dg-torus 'u 'v) (simplify '(* (cos v) (^ (+ 3 (cos v)) -1))))
  (for-each (lambda (v0)
              (assert-true (dg-t-close? (dg-t-num (gauss-curvature dg-torus '(u 0.3) (list 'v v0)))
                                        (/ (cos v0) (+ 3 (cos v0))) 1e-12)))
            '(0.4 1.9 4.0))
  (assert-equal (gauss-curvature '((* (+ R (* r (cos v))) (cos u)) (* (+ R (* r (cos v))) (sin u)) (* r (sin v))) 'u 'v)
                (simplify '(* (cos v) (^ r -1) (^ (+ R (* r (cos v))) -1)))))

(deftest "diffgeom: K, H и главные кривизны — конечные разности в трёх точках (допуск 1e-8)"
  (let ((surfs (list (list '((* 2 (sin u) (cos v)) (* 2 (sin u) (sin v)) (* 2 (cos u))) '((0.7 0.3) (1.4 2.2) (2.2 5.0)))
                     (list dg-torus '((0.3 0.4) (1.1 1.9) (2.0 4.0)))
                     (list '(u v (* u v)) '((0.0 0.0) (0.5 -0.7) (1.2 0.9)))
                     (list '((* u (cos v)) (* u (sin v)) (^ v 2)) '((1.0 0.5) (2.0 1.3) (0.6 -0.8))))))
    (for-each
     (lambda (sf)
       (for-each
        (lambda (p)
          (let* ((r (car sf)) (u0 (car p)) (v0 (cadr p))
                 (num (dg-t-surf-num r u0 v0))
                 (k (dg-t-num (gauss-curvature r (list 'u u0) (list 'v v0))))
                 (hh (dg-t-num (mean-curvature r (list 'u u0) (list 'v v0))))
                 (pc (map dg-t-num (principal-curvatures r (list 'u u0) (list 'v v0)))))
            (assert-true (dg-t-close? k (car num) 1e-8))
            (assert-true (dg-t-close? hh (cadr num) 1e-8))
            ; корни κ² − 2Hκ + K = 0
            (assert-true (dg-t-close? (+ (car pc) (cadr pc)) (* 2 (cadr num)) 1e-8))
            (assert-true (dg-t-close? (* (car pc) (cadr pc)) (car num) 1e-8))
            (assert-true (<= (car pc) (+ (cadr pc) 1e-12)))))
        (cadr sf)))
     surfs)))

(deftest "diffgeom: подделки — вырожденная параметризация и вырожденная точка дают ошибку, не деление на 0"
  (assert-error (gauss-curvature '((* u v) (* u v) (* u v)) 'u 'v))
  (assert-error (mean-curvature '((* u v) (* u v) (* u v)) 'u 'v))
  ; r_u × r_v = 0 в точке u = 0: (u v, u², u³)
  (assert-error (gauss-curvature '((* u v) (^ u 2) (^ u 3)) '(u 0) '(v 1)))
  (assert-error (second-form '((* u v) (^ u 2) (^ u 3)) '(u 0) '(v 1)))
  (assert-error (surface-normal '((* u v) (^ u 2) (^ u 3)) '(u 0) '(v 1)))
  ; полюс сферы: r_u × r_v = 0
  (assert-error (gauss-curvature dg-sphere '(u 0) '(v 1)))
  (assert-error (gauss-curvature '(u v) 'u 'v))
  (assert-error (gauss-curvature dg-sphere 3 'v)))

; ---- Гаусс–Бонне ----
(deftest "diffgeom: Гаусс–Бонне — сфера (χ = 2) и тор (χ = 0) точно"
  (assuming ((R positive))
    (assert-equal (car (gauss-bonnet-check dg-sphere '(u 0 pi) '(v 0 (* 2 pi)) 2)) 'exact)
    (assert-equal (cadr (gauss-bonnet-check dg-sphere '(u 0 pi) '(v 0 (* 2 pi)) 2)) (simplify '(* 4 pi))))
  (assert-equal (gauss-bonnet-check '((* 2 (sin u) (cos v)) (* 2 (sin u) (sin v)) (* 2 (cos u))) '(u 0 pi) '(v 0 (* 2 pi)) 2)
                (list 'exact (simplify '(* 4 pi)) (simplify '(* 4 pi))))
  (assert-equal (gauss-bonnet-check dg-torus '(u 0 (* 2 pi)) '(v 0 (* 2 pi)) 0) '(exact 0 0)))

(deftest "diffgeom: Гаусс–Бонне для тора с символьными R, r — при утверждении R + r cos v > 0"
  (assuming ((R positive) (r positive))
    (let ((tor '((* (+ R (* r (cos v))) (cos u)) (* (+ R (* r (cos v))) (sin u)) (* r (sin v)))))
      (assert-equal (car (gauss-bonnet-check tor '(u 0 (* 2 pi)) '(v 0 (* 2 pi)) 0 '(+ R (* r (cos v))))) 'exact)
      ; без утверждения знак R + r cos v неизвестен — abs остаётся, вердикт честный unknown
      (assert-equal (car (gauss-bonnet-check tor '(u 0 (* 2 pi)) '(v 0 (* 2 pi)) 0)) 'unknown))))

(deftest "diffgeom: Гаусс–Бонне с неверным χ — mismatch; не целое χ и вырожденная параметризация — ошибка"
  (assuming ((R positive))
    (assert-equal (car (gauss-bonnet-check dg-sphere '(u 0 pi) '(v 0 (* 2 pi)) 1)) 'mismatch)
    (assert-equal (car (gauss-bonnet-check dg-sphere '(u 0 pi) '(v 0 (* 2 pi)) 0)) 'mismatch))
  (assert-equal (car (gauss-bonnet-check dg-torus '(u 0 (* 2 pi)) '(v 0 (* 2 pi)) 2)) 'mismatch)
  (assert-error (gauss-bonnet-check dg-sphere '(u 0 pi) '(v 0 (* 2 pi)) 1/2))
  (assert-error (gauss-bonnet-check '((* u v) (* u v) (* u v)) '(u 0 1) '(v 0 1) 2))
  (assert-error (gauss-bonnet-check dg-sphere 'u '(v 0 1) 2)))
