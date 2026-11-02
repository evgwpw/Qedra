; forms.lisp — тесты шага DF.1: дифференциальные формы, d² = 0, прообраз, потенциалы, векторный анализ.
; Подделки: form-potential-check / vf-potential-check / vf-vector-potential-check отвергают неверный потенциал;
; незамкнутая форма → #f; dθ на ℝ²∖{0} — отказ с условием (глобального потенциала нет).

(define fv2 '(x y))
(define fv3 '(x y z))
(define (f3 e) (form e fv3))
(define (f2 e) (form e fv2))
(define (same? a b) (equal? (simplify (expand (list '+ a (list '* -1 b)))) 0))
(define (same-list? a b) (every? (lambda (p) (same? (car p) (cadr p))) (map2 list a b)))

(deftest "forms: конструкторы и печать"
  (let ((w (f2 '(+ (* P dx) (* Q dy)))))
    (assert-equal (form->expr w) '(+ (* P dx) (* Q dy)))
    (assert-equal (form-degree w) 1)
    (assert-true (form-equal? (form (form->expr w) fv2) w)))
  ; make-form: порядок индексов даёт знак, повторы — ноль, нули отбрасываются
  (assert-equal (form-terms (make-form fv3 2 '((5 (2 0)) (0 (0 1)) (7 (1 1)))))
                '((-5 (0 2))))
  (assert-equal (form-terms (make-form fv3 2 '((1 (z x))))) '((-1 (0 2))))
  (assert-equal (form->expr (f3 '(wedge dy dx))) '(* -1 (wedge dx dy)))
  (assert-equal (form->expr (f3 '(+ (* x dx) (* -1 x dx)))) 0)
  (assert-equal (form->expr (f3 '(/ (* 2 dx) 4))) '(* 1/2 dx)))

(deftest "forms: wedge — антисимметрия, dx∧dx = 0, знак перестановки"
  (let ((dx (f3 'dx)) (dy (f3 'dy)) (dz (f3 'dz)))
    (assert-true (form-zero? (wedge dx dx)))
    (assert-true (form-equal? (wedge dx dy) (form-neg (wedge dy dx))))
    (assert-true (form-equal? (wedge dz dx dy) (wedge dx dy dz)))
    (assert-true (form-equal? (wedge dz dy dx) (form-neg (wedge dx dy dz))))
    (assert-true (form-zero? (wedge dx dy dz dx)))
    (assert-equal (form->expr (wedge 'x dx)) '(* x dx))))

(deftest "forms: wedge — ассоциативность и градуированная коммутативность"
  (let ((a (f3 '(+ (* x dx) (* (^ y 2) dz))))
        (b (f3 '(+ (* z dy) (* x y dx))))
        (c (f3 '(+ (* y dz) (* 2 dx))))
        (p (f3 '(+ (* x (wedge dx dy)) (* z (wedge dy dz)))))
        (q (f3 '(+ (* y (wedge dx dz)) (wedge dy dz)))))
    (assert-true (form-equal? (wedge (wedge a b) c) (wedge a (wedge b c))))
    (assert-true (form-equal? (wedge a b) (form-neg (wedge b a))))
    (assert-true (form-equal? (wedge a p) (wedge p a)))
    (assert-true (form-equal? (wedge p q) (wedge q p)))
    (assert-true (form-zero? (wedge p q)))))

(deftest "forms: d² = 0 и правило Лейбница"
  (let ((f (f3 '(+ (* (^ x 2) y (exp z)) (* (sin x) (cos y) z))))
        (a (f3 '(+ (* x y dx) (* (sin z) dy) (* (^ y 2) z dz))))
        (b (f3 '(+ (* z (wedge dx dy)) (* (^ x 2) (wedge dy dz)) (* y (wedge dx dz)))))
        (c (f3 '(+ (* z dx) (* x dy)))))
    (assert-true (form-zero? (form-d (form-d f))))
    (assert-true (form-zero? (form-d (form-d a))))
    (assert-true (form-zero? (form-d (form-d b))))
    ; d(α∧β) = dα∧β − α∧dβ (α — 1-форма)
    (assert-true (form-equal? (form-d (wedge a c))
                              (form-sub (wedge (form-d a) c) (wedge a (form-d c)))))
    (let ((g (form '(+ (* (^ x 2) w dx) (* (sin y) z dw) (* x y dz)) '(x y z w))))
      (assert-true (form-zero? (form-d (form-d g)))))))

(deftest "forms: d — пример (ℝ²)"
  (assert-equal (form->expr (form-d (f2 '(+ (* (^ x 2) y dx) (* (sin x) dy)))))
                '(* (+ (* -1 (^ x 2)) (cos x)) (wedge dx dy))))

(deftest "forms: прообраз — полярные координаты"
  (let ((polar '((* r (cos th)) (* r (sin th)))))
    (assert-equal (form->expr (form-pullback (f2 '(wedge dx dy)) polar '(r th)))
                  '(* r (wedge dr dth)))
    (assert-equal (form->expr (form-pullback (f2 'dx) polar '(r th)))
                  '(+ (* (cos th) dr) (* -1 r (sin th) dth)))
    ; d(φ*ω) = φ*(dω)
    (let ((w (f2 '(+ (* (^ x 2) y dx) (* (sin x) (cos y) dy)))))
      (assert-true (form-equal? (form-d (form-pullback w polar '(r th)))
                                (form-pullback (form-d w) polar '(r th)))))
    (assert-equal (form->expr (form-pullback (f2 '(+ (^ x 2) (^ y 2))) polar '(r th))) '(^ r 2))))

(deftest "forms: прообраз — сферические координаты, ℝ³"
  (let* ((sph '((* rho (sin ph) (cos th)) (* rho (sin ph) (sin th)) (* rho (cos ph))))
         (r (form-pullback (f3 '(wedge dx dy dz)) sph '(rho ph th))))
    (assert-equal (form-terms r)
                  (form-terms (form '(* (^ rho 2) (sin ph) (wedge drho dph dth)) '(rho ph th))))))

(deftest "forms: прообраз — композиция (φ∘ψ)* = ψ*φ*"
  (let* ((w (f2 '(+ (* y dx) (* (^ x 2) dy))))
         (phi '((* u v) (+ u v)))
         (psi '((+ s t) (* s t)))
         (comp '((* (+ s t) s t) (+ s t (* s t)))))
    (assert-true (form-equal? (form-pullback (form-pullback w phi '(u v)) psi '(s t))
                              (form-pullback w (map simplify comp) '(s t))))))

(deftest "forms: внутреннее произведение и Ходж"
  (assert-equal (form->expr (form-interior '(a b c) (f3 '(wedge dx dy))))
                '(+ (* -1 b dx) (* a dy)))
  (assert-equal (form->expr (form-interior '(1 0 0) (f3 '(wedge dx dy)))) 'dy)
  (assert-true (form-zero? (form-interior '(a b c) (form-interior '(a b c) (f3 '(wedge dx dy dz))))))
  (assert-equal (form->expr (form-hodge (f3 'dx))) '(wedge dy dz))
  (assert-equal (form->expr (form-hodge (f3 'dy))) '(* -1 (wedge dx dz)))
  (assert-equal (form->expr (form-hodge (f3 '(wedge dx dy)))) 'dz)
  (assert-equal (form->expr (form-hodge (f3 1))) '(wedge dx dy dz))
  (assert-equal (form->expr (form-hodge (f2 'dx))) 'dy)
  (assert-equal (form->expr (form-hodge (f2 'dy))) '(* -1 dx))
  ; ∗∗ = 1 в ℝ³, на 1-формах ℝ² ∗∗ = −1
  (let ((a (f3 '(+ (* x dx) (* y dz)))) (b (f3 '(* z (wedge dx dz)))))
    (assert-true (form-equal? (form-hodge (form-hodge a)) a))
    (assert-true (form-equal? (form-hodge (form-hodge b)) b)))
  (let ((a (f2 '(+ (* x dx) (* y dy)))))
    (assert-true (form-equal? (form-hodge (form-hodge a)) (form-neg a)))))

(deftest "forms: замкнутость и потенциал — учебные 1-формы"
  (let ((w (f2 '(+ (* 2 x y dx) (* (+ (^ x 2) (* 3 (^ y 2))) dy)))))
    (assert-true (form-closed? w))
    (assert-true (form-exact? w))
    (let ((F (form-potential w)))
      (assert-equal (form->expr F) '(+ (^ y 3) (* (^ x 2) y)))
      (assert-true (form-potential-check w F))))
  (let ((w (f2 '(+ (* (+ (* (exp x) (sin y)) (* 2 x)) dx) (* (* (exp x) (cos y)) dy)))))
    (assert-equal (form->expr (form-potential w)) '(+ (^ x 2) (* (exp x) (sin y)))))
  ; замкнутая 2-форма в ℝ³ имеет потенциал-1-форму
  (let* ((w (f3 '(+ (* z (wedge dx dy)) (* x (wedge dy dz)) (* -2 y (wedge dz dx)))))
         (A (form-potential w)))
    (assert-true (form-closed? w))
    (assert-true (form-potential-check w A))
    (assert-equal (form-degree A) 1)))

(deftest "forms: фейки — подделка потенциала и незамкнутая форма"
  (let ((w (f2 '(+ (* 2 x y dx) (* (+ (^ x 2) (* 3 (^ y 2))) dy)))))
    (assert-true (not (form-potential-check w (f2 '(+ (^ y 3) (* (^ x 2) y) x)))))
    (assert-true (not (form-potential-check w (f2 '(+ (^ y 2) (* (^ x 2) y))))))
    (assert-true (not (form-potential-check w (f2 '(* x dx)))))
    (assert-true (form-potential-check w (f2 '(+ 7 (^ y 3) (* (^ x 2) y))))))
  (let ((w (f2 '(+ (* y dx) (* (* -1 y) dy)))))
    (assert-true (not (form-closed? w)))
    (assert-true (not (form-exact? w)))
    (assert-equal (form-potential w) #f))
  (assert-equal (form-potential (f2 '(+ (* (* -1 y) dx) (* x dy)))) #f))

(deftest "forms: dθ на ℝ²∖{0} — замкнута, но глобального потенциала нет"
  (let* ((dth (f2 '(/ (+ (* -1 y dx) (* x dy)) (+ (^ x 2) (^ y 2)))))
         (r (capture-conditions (lambda () (form-potential dth)))))
    (assert-true (form-closed? dth))
    (assert-equal (car r) #f)
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'form-singular-at-base)) (cadr r)))
    (assert-true (not (form-exact? dth)))
    ; atan(y/x) — только локальный потенциал (x > 0): проверка принимает, atan(x/y) — нет
    (assert-true (form-potential-check dth (f2 '(atan (/ y x)))))
    (assert-true (not (form-potential-check dth (f2 '(atan (/ x y))))))))

(deftest "forms: потенциал от явной базовой точки — условие области"
  (let* ((w (f2 '(+ (* 2 x y dx) (* (+ (^ x 2) 1) dy))))
         (r (capture-conditions (lambda () (form-potential w '(1 1))))))
    (assert-true (form-potential-check w (car r)))
    (assert-true (any? (lambda (c) (equal? (car (car c)) 'star-shaped-domain)) (cadr r)))))

(deftest "forms: векторный анализ — через формы и прямые формулы"
  (let ((f '(+ (^ x 2) (* x y z) (sin z)))
        (F '((* y z) (^ x 2) (* x y z)))
        (G '((* x y) (* y z) (^ z 2))))
    (assert-true (same-list? (vf-grad f fv3) (map (lambda (v) (simplify (diff v f))) fv3)))
    (assert-true (same? (vf-div F fv3) (simplify (+ (diff 'x '(* y z)) (diff 'y '(^ x 2)) (diff 'z '(* x y z))))))
    (assert-true (same-list? (vf-curl F fv3)
                  (list (simplify (- (diff 'y '(* x y z)) (diff 'z '(^ x 2))))
                        (simplify (- (diff 'z '(* y z)) (diff 'x '(* x y z))))
                        (simplify (- (diff 'x '(^ x 2)) (diff 'y '(* y z)))))))
    (assert-true (same? (vf-laplacian f fv3)
                  (simplify (+ (diff 'x (diff 'x f)) (diff 'y (diff 'y f)) (diff 'z (diff 'z f))))))
    (assert-true (same? (vf-laplacian f fv3) (vf-div (vf-grad f fv3) fv3)))
    (assert-equal (vf-curl (vf-grad f fv3) fv3) '(0 0 0))
    (assert-equal (vf-div (vf-curl F fv3) fv3) 0)
    (assert-equal (vf-div (vf-curl G fv3) fv3) 0)
    (assert-equal (vf-curl '((* -1 y) x) fv2) 2)
    (assert-equal (vf-div '((* -1 y) x) fv2) 0)
    (assert-equal (vf-laplacian '(+ (^ x 2) (^ y 2)) fv2) 4)))

(deftest "forms: потенциал консервативного поля и векторный потенциал"
  (let ((F '((* 2 x y) (+ (^ x 2) (* 3 (^ y 2))) 1)))
    (let ((p (vf-potential F fv3)))
      (assert-equal (simplify (- p '(+ z (^ y 3) (* (^ x 2) y)))) 0)
      (assert-true (vf-potential-check F fv3 p))
      (assert-true (not (vf-potential-check F fv3 '(+ z (^ y 2) (* (^ x 2) y))))))
    (assert-equal (vf-potential '((* -1 y) x 0) fv3) #f))
  (let* ((F '((* y z) (* -1 x z) (^ x 2)))
         (A (vf-vector-potential F fv3)))
    (assert-equal (vf-div F fv3) 0)
    (assert-true (vf-vector-potential-check F fv3 A))
    (assert-equal (vf-curl A fv3) (map simplify F))
    (assert-true (not (vf-vector-potential-check F fv3 (list 0 0 '(* x y))))))
  (assert-equal (vf-vector-potential '(x y z) fv3) #f))

; ---------- DF.2: интегрирование форм, Стокс/Грин ----------

(define circ (make-chain '((cos t) (sin t)) '((t 0 (* 2 pi)))))

(deftest "forms: ∫ по кривой — работа по окружности и винтовой линии"
  (assert-equal (integrate-form (f2 '(+ (* -1 y dx) (* x dy))) circ) '(* 2 pi))
  (assert-equal (integrate-form (vf-form1 '((* -1 y) x) fv2) circ) '(* 2 pi))
  ; потенциальное поле по замкнутому контуру — 0
  (assert-equal (integrate-form (vf-form1 '((* 2 x y) (^ x 2)) fv2) circ) 0)
  (let ((helix (make-chain '((cos t) (sin t) t) '((t 0 (* 2 pi))))))
    (assert-true (same? (integrate-form (f3 '(+ (* y dx) (* -1 x dy) (* z dz))) helix)
                        '(+ (* -2 pi) (* 2 (^ pi 2)))))))

(deftest "forms: ∫ по кривой — ∫ dF = F(конец) − F(начало); смена ориентации — знак"
  (let* ((c (make-chain '((cos t) (sin t) t) '((t 0 1))))
         (F '(+ (* x y) (* z z)))
         (w (form-d (form F fv3))))
    (assert-true (same? (integrate-form w c)
                        (- (subst '((x (cos 1)) (y (sin 1)) (z 1)) F) (subst '((x 1) (y 0) (z 0)) F)))))
  (let ((back (make-chain '((cos t) (sin t)) '((t (* 2 pi) 0)))))
    (assert-equal (integrate-form (f2 '(+ (* -1 y dx) (* x dy))) back) '(* -2 pi))))

(deftest "forms: поток r/|r|³ через сферу = 4π; ∫ по поверхности"
  (let* ((r3 '(^ (+ (^ x 2) (^ y 2) (^ z 2)) 3/2))
         (flux (vf-form2 (list (list '/ 'x r3) (list '/ 'y r3) (list '/ 'z r3)) fv3))
         (sph '((* (sin ph) (cos th)) (* (sin ph) (sin th)) (cos ph))))
    (assert-equal (integrate-form flux (make-chain sph '((ph 0 pi) (th 0 (* 2 pi))))) '(* 4 pi)))
  ; площадь единичного диска: ∫∫ dx∧dy в полярных координатах
  (assert-equal (integrate-form (f2 '(wedge dx dy))
                                (make-chain '((* r (cos th)) (* r (sin th))) '((r 0 1) (th 0 (* 2 pi)))))
                'pi))

(deftest "forms: Грин и Стокс — обе части равны (символьно)"
  (let ((polar '((* r (cos th)) (* r (sin th)))))
    ; диск
    (assert-equal (caddr (stokes-check (f2 '(+ (* -1 y dx) (* x dy))) polar '(r 0 1) '(th 0 (* 2 pi)))) 'exact)
    (assert-equal (caddr (stokes-check (f2 '(+ (* (^ y 2) dx) (* (^ x 3) dy))) polar '(r 0 1) '(th 0 (* 2 pi)))) 'exact))
  ; прямоугольник
  (let ((r (stokes-check (f2 '(+ (* (^ x 2) y dx) (* x dy))) '(u v) '(u 0 1) '(v 0 2))))
    (assert-equal (caddr r) 'exact)
    (assert-equal (car r) (cadr r)))
  ; полусфера: граница — экватор
  (let ((hem '((* (sin ph) (cos th)) (* (sin ph) (sin th)) (cos ph))))
    (assert-equal (caddr (stokes-check (f3 '(+ (* z dx) (* x dy) (* y dz))) hem '(ph 0 (/ pi 2)) '(th 0 (* 2 pi)))) 'exact)))

(deftest "forms: численный запасной путь — условие и float"
  (let* ((w (form '(* (exp (* -1 (^ x 2))) dx) '(x)))
         (r (capture-conditions (lambda () (integrate-form w (make-chain '(x) '((x 0 1))))))))
    (assert-equal (type-of (car r)) 'float)
    (assert-true (< (abs (- (car r) 0.7468241328124271)) 1e-8))
    (assert-true (any? (lambda (c) (equal? (car c) '(integrate-form-numeric))) (cadr r)))))

(deftest "forms: интегрирование — ошибки"
  (assert-error (integrate-form (f2 '(wedge dx dy)) circ))
  (assert-error (integrate-form (f2 'dx) (make-chain '((cos t) (sin t) t) '((t 0 1))))))

(deftest "forms: язык — extd, pullback, potential, integrate_form"
  (assert-equal (math-eval "wedge(dz, dx)") '(wedge dz dx))
  (assert-equal (math-eval "pullback(wedge(dx, dy), [x, y], [r*cos(th), r*sin(th)], [r, th])")
                '(* r (wedge dr dth)))
  (assert-true (same? (math-eval "form_potential(2*x*y*dx + (x^2 + 3*y^2)*dy, [x, y])") '(+ (^ y 3) (* (^ x 2) y))))
  (assert-equal (math-eval "form_potential((-y*dx + x*dy)/(x^2 + y^2), [x, y])") #f)
  (assert-equal (math-eval "integrate_form(-y*dx + x*dy, [x, y], [cos(t), sin(t)], [t, 0, 2*pi])") '(* 2 pi))
  (assert-equal (math-eval "wedge(wedge(dx, dy), dz, [x, y, z])") '(wedge dx dy dz))
  (assert-equal (math-eval "extd(x*dy, [x, y])") '(wedge dx dy)))
