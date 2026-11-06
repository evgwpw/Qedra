; conics.lisp — тесты шага AG: кривые и поверхности второго порядка.
; Оракулы: (1) общеизвестные типы и параметры (эллипс x²/4 + y²/9 = 1, гипербола x² − y² = 1, парабола y = x², конусы,
; параболоиды, гиперболоиды, цилиндры); (2) независимая геометрия по числам: точка кривой, построенная по полуосям и
; перенесённая формулами преобразования в исходные координаты, обращает исходное уравнение в нуль; сумма расстояний до
; фокусов эллипса равна 2a, разность для гиперболы — 2a, фокус и директриса параболы равноудалены; (3) подделки сертификата:
; неверная полуось, неверный угол, растяжение вместо поворота — mismatch; (4) честность: параметры — unknown, не многочлен — ошибка.

(define ag-t-v2 '(x y))
(define ag-t-v3 '(x y z))
(define (ag-t-eq s) (math-eval s))
(define (ag-t-get r k) (cadr (assoc k r)))
(define (ag-t-put r k v) (map (lambda (kv) (if (equal? (car kv) k) (list k v) kv)) r))
(define (ag-t-n e) (eval-num e))
(define (ag-t-close? a b) (< (abs (- a b)) 1e-9))

; формулы преобразования в числах: (xp yp) → (x y)
(define (ag-t-map rec nv pt)
  (map (lambda (r) (ag-t-n (subst (map2 list nv pt) (cadr r)))) (ag-t-get rec 'substitution)))
(define (ag-t-f eq vars pt) (ag-t-n (subst (map2 list vars pt) (list '+ (cadr eq) (list '* -1 (caddr eq))))))
(define (ag-t-dist p q) (ag-t-n (list 'sqrt (apply + (map2 (lambda (a b) (* (- a b) (- a b))) p q)))))
(define (ag-t-pt p) (map ag-t-n p))

; ---- типы кривых ----
(deftest "conics: классификация кривых — оракул задания"
  (assert-equal (classify-conic (ag-t-eq "x^2/4 + y^2/9 = 1") ag-t-v2) 'ellipse)
  (assert-equal (classify-conic (ag-t-eq "x^2 - y^2 = 1") ag-t-v2) 'hyperbola)
  (assert-equal (classify-conic (ag-t-eq "y = x^2") ag-t-v2) 'parabola)
  (assert-equal (classify-conic (ag-t-eq "5*x^2 + 4*x*y + 2*y^2 = 1") ag-t-v2) 'ellipse)
  (assert-equal (classify-conic (ag-t-eq "x^2 - y^2 = 0") ag-t-v2) 'intersecting_lines)
  (assert-equal (classify-conic (ag-t-eq "x^2 + y^2 + 1 = 0") ag-t-v2) 'imaginary_ellipse)
  (assert-equal (classify-conic (ag-t-eq "x^2 + 2*x*y + y^2 - 1 = 0") ag-t-v2) 'parallel_lines)
  (assert-equal (classify-conic (ag-t-eq "3*x^2 + 2*x*y + 3*y^2 - 8 = 0") ag-t-v2) 'ellipse))

(deftest "conics: вырожденные кривые и окружность"
  (assert-equal (classify-conic (ag-t-eq "x^2 + y^2 = 4") ag-t-v2) 'circle)
  (assert-equal (classify-conic (ag-t-eq "x^2 + y^2 = 0") ag-t-v2) 'point)
  (assert-equal (classify-conic (ag-t-eq "x^2 + 2*x*y + y^2 + 1 = 0") ag-t-v2) 'imaginary_parallel_lines)
  (assert-equal (classify-conic (ag-t-eq "x^2 + 2*x*y + y^2 = 0") ag-t-v2) 'coincident_lines)
  (assert-equal (classify-conic (ag-t-eq "x*y = 1") ag-t-v2) 'hyperbola)
  (assert-equal (classify-conic (ag-t-eq "x*y = 0") ag-t-v2) 'intersecting_lines)
  (assert-equal (classify-conic (ag-t-eq "x^2 - 4*x + y^2 + 6*y + 13 = 0") ag-t-v2) 'point)
  (assert-equal (classify-conic (ag-t-eq "x^2 = 4") ag-t-v2) 'parallel_lines)
  (assert-equal (classify-conic (ag-t-eq "x^2 = -4") ag-t-v2) 'imaginary_parallel_lines)
  (assert-equal (classify-conic (ag-t-eq "x^2 = 0") ag-t-v2) 'coincident_lines)
  (assert-equal (classify-conic '(+ (* x x) (* -1 y)) ag-t-v2) 'parabola))

(deftest "conics: инварианты эллипса x²/4 + y²/9 = 1"
  (let ((inv (conic-invariants (ag-t-eq "x^2/4 + y^2/9 = 1") ag-t-v2)))
    (assert-equal (ag-t-get inv 'I1) 13/36)
    (assert-equal (ag-t-get inv 'I2) 1/36)
    (assert-equal (ag-t-get inv 'I3) -1/36)))

; ---- элементы ----
(deftest "conics: эллипс x²/4 + y²/9 = 1 — a = 3 по y, e = √5/3, фокусы и директрисы"
  (let ((el (conic-elements (ag-t-eq "x^2/4 + y^2/9 = 1") ag-t-v2)))
    (assert-equal (ag-t-get el 'type) 'ellipse)
    (assert-equal (ag-t-get el 'a) 3)
    (assert-equal (ag-t-get el 'b) 2)
    (assert-equal (ag-t-get el 'major_axis) '(0 1))
    (assert-equal (ag-t-get el 'eccentricity) (simplify '(* 1/3 (^ 5 1/2))))
    (assert-equal (ag-t-get el 'foci) (list (list 0 (simplify '(^ 5 1/2))) (list 0 (simplify '(* -1 (^ 5 1/2))))))
    (assert-equal (ag-t-get el 'center) '(0 0))
    (assert-equal (length (ag-t-get el 'directrices)) 2)))

(deftest "conics: гипербола x² − y² = 1 — асимптоты y = ±x, e = √2"
  (let ((el (conic-elements (ag-t-eq "x^2 - y^2 = 1") ag-t-v2)))
    (assert-equal (ag-t-get el 'type) 'hyperbola)
    (assert-equal (ag-t-get el 'a) 1)
    (assert-equal (ag-t-get el 'b) 1)
    (assert-equal (ag-t-get el 'eccentricity) (simplify '(^ 2 1/2)))
    (assert-equal (ag-t-get el 'asymptotes) (list '(= y x) (list '= 'y (simplify '(* -1 x)))))))

(deftest "conics: парабола y = x² — p = 1/2, фокус (0, 1/4), директриса y = −1/4"
  (let ((el (conic-elements (ag-t-eq "y = x^2") ag-t-v2)))
    (assert-equal (ag-t-get el 'type) 'parabola)
    (assert-equal (ag-t-get el 'p) 1/2)
    (assert-equal (ag-t-get el 'vertex) '(0 0))
    (assert-equal (ag-t-get el 'focus) '(0 1/4))
    (assert-equal (ag-t-get el 'directrix) '(= y -1/4))
    (assert-equal (ag-t-get el 'axis) '(= x 0))
    (assert-equal (ag-t-get el 'eccentricity) 1)))

(deftest "conics: парабола со сдвигом и поворотом — фокус и директриса равноудалены (число)"
  (let* ((eq (ag-t-eq "x^2 + 4*x*y + 4*y^2 + 2*x + y = 0"))
         (el (conic-elements eq ag-t-v2))
         (rec (canonical-conic eq ag-t-v2))
         (F (ag-t-pt (ag-t-get el 'focus)))
         (dir (ag-t-get el 'directrix))
         ; точка параболы: yp = 2·t, xp = yp²/(2p)
         (p (ag-t-n (ag-t-get el 'p))))
    (for-each
     (lambda (t)
       (let* ((P (ag-t-map rec '(xp yp) (list (/ (* t t) (* 2 p)) t)))
              ; директриса y = k + m x
              (rhs (caddr dir))
              (k (ag-t-n (subst '((x 0)) rhs)))
              (m (- (ag-t-n (subst '((x 1)) rhs)) k))
              (d-line (/ (abs (- (nth P 1) (+ k (* m (nth P 0))))) (ag-t-n (list 'sqrt (+ 1 (* m m)))))))
         ; исходное уравнение на построенной точке равно нулю
         (assert-true (ag-t-close? (ag-t-f eq ag-t-v2 P) 0))
         ; расстояние до фокуса равно расстоянию до директрисы
         (assert-true (ag-t-close? (ag-t-dist P F) d-line))))
     '(-3 -1 0 1 2 5))))

(deftest "conics: повёрнутый эллипс 3x² + 2xy + 3y² = 8 — полуоси 2 и √2, угол −π/4, фокусы по сумме расстояний"
  (let* ((eq (ag-t-eq "3*x^2 + 2*x*y + 3*y^2 - 8 = 0"))
         (el (conic-elements eq ag-t-v2))
         (rec (canonical-conic eq ag-t-v2)))
    (assert-equal (ag-t-get el 'a) 2)
    (assert-equal (ag-t-get el 'b) (simplify '(^ 2 1/2)))
    (assert-equal (ag-t-get rec 'angle) (simplify '(* -1/4 pi)))
    (assert-equal (ag-t-get rec 'equation) (simplify '(= (+ (* 1/4 (^ xp 2)) (* 1/2 (^ yp 2))) 1)))
    (assert-equal (ag-t-get rec 'eigenvalues) '(2 4))
    (assert-equal (ag-t-get el 'foci) '((1 -1) (-1 1)))
    (let ((F1 (ag-t-pt (car (ag-t-get el 'foci)))) (F2 (ag-t-pt (cadr (ag-t-get el 'foci)))))
      (for-each
       (lambda (th)
         (let ((P (ag-t-map rec '(xp yp) (list (* 2 (cos th)) (* (ag-t-n (list 'sqrt 2)) (sin th))))))
           (assert-true (ag-t-close? (ag-t-f eq ag-t-v2 P) 0))
           (assert-true (ag-t-close? (+ (ag-t-dist P F1) (ag-t-dist P F2)) 4))))
       '(0.3 1.1 2.5 4.0)))))

(deftest "conics: 5x² + 4xy + 2y² = 1 — собственные значения 1 и 6, канонический вид x′² + 6y′² = 1"
  (let* ((eq (ag-t-eq "5*x^2 + 4*x*y + 2*y^2 = 1"))
         (rec (canonical-conic eq ag-t-v2)))
    (assert-equal (ag-t-get rec 'eigenvalues) '(1 6))
    (assert-equal (ag-t-get rec 'equation) (simplify '(= (+ (^ xp 2) (* 6 (^ yp 2))) 1)))
    (assert-equal (ag-t-get rec 'center) '(0 0))
    (assert-equal (conic-check eq ag-t-v2 rec) 'exact)))

(deftest "conics: гипербола xy = 1 — повёрнута на π/4, асимптоты — оси координат, фокусы по разности расстояний"
  (let* ((eq (ag-t-eq "x*y = 1"))
         (el (conic-elements eq ag-t-v2))
         (rec (canonical-conic eq ag-t-v2)))
    (assert-equal (ag-t-get rec 'angle) (simplify '(* 1/4 pi)))
    (assert-equal (ag-t-get el 'asymptotes) '((= x 0) (= y 0)))
    (assert-equal (ag-t-get el 'a) (simplify '(^ 2 1/2)))
    (let ((F1 (ag-t-pt (car (ag-t-get el 'foci)))) (F2 (ag-t-pt (cadr (ag-t-get el 'foci)))))
      (for-each
       (lambda (s)
         (let ((P (ag-t-map rec '(xp yp) (list (ag-t-n (list '* (list 'sqrt 2) (list 'cosh s))) (ag-t-n (list '* (list 'sqrt 2) (list 'sinh s)))))))
           (assert-true (ag-t-close? (ag-t-f eq ag-t-v2 P) 0))
           (assert-true (ag-t-close? (abs (- (ag-t-dist P F1) (ag-t-dist P F2))) (* 2 (ag-t-n (list 'sqrt 2)))))))
       '(0.2 0.9 1.5)))))

(deftest "conics: вырожденные — прямые, точка, пустое множество: элементы"
  (let ((l (conic-elements (ag-t-eq "x^2 - y^2 = 0") ag-t-v2)))
    (assert-equal (ag-t-get l 'lines) (list '(= y x) (list '= 'y (simplify '(* -1 x))))))
  (let ((l (conic-elements (ag-t-eq "x^2 + 2*x*y + y^2 - 1 = 0") ag-t-v2)))
    (assert-equal (ag-t-get l 'type) 'parallel_lines)
    (assert-equal (length (ag-t-get l 'lines)) 2)
    (assert-equal (ag-t-get l 'distance) (simplify '(^ 2 1/2))))
  (assert-equal (ag-t-get (conic-elements (ag-t-eq "x^2 - 4*x + y^2 + 6*y + 13 = 0") ag-t-v2) 'point) '(2 -3))
  (assert-equal (ag-t-get (conic-elements (ag-t-eq "x^2 + y^2 + 1 = 0") ag-t-v2) 'real_points) 'none))

; ---- сертификат кривых ----
(define ag-t-conics
  '("x^2/4 + y^2/9 = 1" "x^2 - y^2 = 1" "y = x^2" "5*x^2 + 4*x*y + 2*y^2 = 1" "x^2 - y^2 = 0" "x^2 + y^2 + 1 = 0"
    "x^2 + 2*x*y + y^2 - 1 = 0" "3*x^2 + 2*x*y + 3*y^2 - 8 = 0" "x^2 + y^2 = 0" "x^2 + 2*x*y + y^2 + 1 = 0"
    "x^2 + 2*x*y + y^2 = 0" "x*y = 1" "x^2 + y^2 - 2*x + 4*y = 4" "4*x^2 + 4*x*y + y^2 - 6*x + 2*y = 0"
    "x^2 - 6*x*y + y^2 = 8" "-x^2 - y^2 + 2*x = 0" "y^2 = 4*x" "x^2 = 4" "x^2 + 3*y^2 - 6*y + 3 = 0"))

(deftest "conics: сертификат принимает канонический вид всех тестовых кривых"
  (for-each
   (lambda (s)
     (let* ((eq (ag-t-eq s)) (rec (canonical-conic eq ag-t-v2)))
       (assert-equal (ag-t-get rec 'status) 'ok)
       (assert-equal (conic-check eq ag-t-v2 rec) 'exact)))
   ag-t-conics))

(deftest "conics: подделки — неверная полуось, угол, растяжение, чужое уравнение дают mismatch"
  (let* ((eq (ag-t-eq "3*x^2 + 2*x*y + 3*y^2 - 8 = 0"))
         (rec (canonical-conic eq ag-t-v2)))
    (assert-equal (conic-check eq ag-t-v2 rec) 'exact)
    ; неверная полуось: x′²/4 + y′²/3 = 1
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'equation (simplify '(= (+ (* 1/4 (^ xp 2)) (* 1/3 (^ yp 2))) 1))))
                  'mismatch)
    ; неверный угол: π/4 вместо −π/4
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'angle (simplify '(* 1/4 pi)))) 'mismatch)
    ; растяжение вместо поворота
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'substitution '((x (* 2 xp)) (y yp)))) 'mismatch)
    ; поворот на другой угол (формулы согласованы с углом, но канонический вид — не тот)
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put (ag-t-put rec 'angle 0) 'substitution '((x xp) (y yp)))) 'mismatch)
    ; уравнение 0 = 0
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'equation '(= 0 0))) 'mismatch)
    ; чужая кривая
    (assert-equal (conic-check (ag-t-eq "x^2 + y^2 = 1") ag-t-v2 rec) 'mismatch)
    ; нет полей
    (assert-equal (conic-check eq ag-t-v2 '((type ellipse))) 'unknown)))

(deftest "conics: подделка эллипса x²/4 + y²/9 = 1 — неверная полуось"
  (let* ((eq (ag-t-eq "x^2/4 + y^2/9 = 1")) (rec (canonical-conic eq ag-t-v2)))
    (assert-equal (conic-check eq ag-t-v2 rec) 'exact)
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'equation (simplify '(= (+ (* 1/4 (^ xp 2)) (* 1/10 (^ yp 2))) 1)))) 'mismatch)
    ; кратное того же уравнения — тот же эллипс, принимается
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'equation (simplify '(= (+ (* 1/2 (^ xp 2)) (* 2/9 (^ yp 2))) 2)))) 'exact)))

(deftest "conics: вложенные радикалы — численный вердикт numeric (точно не доказывается), подделка всё равно mismatch"
  (let* ((eq (ag-t-eq "2*x^2 + 3*x*y - y^2 + x - y = 5")) (rec (canonical-conic eq ag-t-v2)))
    (assert-equal (ag-t-get rec 'type) 'hyperbola)
    (assert-true (member? (conic-check eq ag-t-v2 rec) '(exact numeric)))
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'center '(0 0))) (conic-check eq ag-t-v2 rec))
    (assert-equal (conic-check eq ag-t-v2 (ag-t-put rec 'equation (simplify (list '= (cadr (ag-t-get rec 'equation)) 2)))) 'mismatch)))

; ---- честность ----
(deftest "conics: параметры в коэффициентах — unknown, либо знак по объявлению"
  (assert-equal (classify-conic (ag-t-eq "a*x^2 + y^2 = 1") ag-t-v2) 'unknown)
  (assert-equal (ag-t-get (canonical-conic (ag-t-eq "a*x^2 + y^2 = 1") ag-t-v2) 'type) 'unknown)
  (assert-equal (ag-t-get (conic-elements (ag-t-eq "a*x^2 + y^2 = 1") ag-t-v2) 'status) 'unknown)
  (assuming ((a positive))
    (assert-equal (classify-conic (ag-t-eq "a*x^2 + y^2 = 1") ag-t-v2) 'ellipse)
    ; тип известен, а числового канонического вида нет
    (let ((rec (canonical-conic (ag-t-eq "a*x^2 + y^2 = 1") ag-t-v2)))
      (assert-equal (ag-t-get rec 'type) 'ellipse)
      (assert-equal (ag-t-get rec 'status) 'unknown))))

(deftest "conics: не многочлен второй степени — ошибка"
  (assert-error (classify-conic '(= (sin x) y) ag-t-v2))
  (assert-error (classify-conic (ag-t-eq "x^3 + y = 0") ag-t-v2))
  (assert-error (classify-conic (ag-t-eq "x + y = 1") ag-t-v2))
  (assert-error (classify-conic (ag-t-eq "x^2 + y^2 = 1") '(x)))
  (assert-error (classify-quadric (ag-t-eq "x^2 + y^2 = 1") ag-t-v2)))

; ---- поверхности ----
(deftest "conics: классификация поверхностей — оракул задания"
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 - z^2 = 0") ag-t-v3) 'cone)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 - z = 0") ag-t-v3) 'elliptic_paraboloid)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 - z^2 = 1") ag-t-v3) 'hyperboloid_one_sheet)
  (assert-equal (classify-quadric (ag-t-eq "x^2 - y^2 - z^2 = 1") ag-t-v3) 'hyperboloid_two_sheets)
  (assert-equal (classify-quadric (ag-t-eq "x*y = z") ag-t-v3) 'hyperbolic_paraboloid)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 = 1") ag-t-v3) 'elliptic_cylinder))

(deftest "conics: классификация поверхностей — остальные типы и вырождения"
  (assert-equal (classify-quadric (ag-t-eq "x^2/4 + y^2/9 + z^2 = 1") ag-t-v3) 'ellipsoid)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 + z^2 + 1 = 0") ag-t-v3) 'imaginary_ellipsoid)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 + z^2 = 0") ag-t-v3) 'point)
  (assert-equal (classify-quadric (ag-t-eq "x^2 - y^2 = 1") ag-t-v3) 'hyperbolic_cylinder)
  (assert-equal (classify-quadric (ag-t-eq "x^2 - y^2 = 0") ag-t-v3) 'intersecting_planes)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 = 0") ag-t-v3) 'line)
  (assert-equal (classify-quadric (ag-t-eq "x^2 = 2*y") ag-t-v3) 'parabolic_cylinder)
  (assert-equal (classify-quadric (ag-t-eq "x^2 = 1") ag-t-v3) 'parallel_planes)
  (assert-equal (classify-quadric (ag-t-eq "x^2 = -1") ag-t-v3) 'imaginary_parallel_planes)
  (assert-equal (classify-quadric (ag-t-eq "x^2 = 0") ag-t-v3) 'coincident_planes)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 + 1 = 0") ag-t-v3) 'imaginary_elliptic_cylinder)
  (assert-equal (classify-quadric (ag-t-eq "x^2 - y^2 = z") ag-t-v3) 'hyperbolic_paraboloid)
  (assert-equal (classify-quadric (ag-t-eq "x*y + y*z + x*z = 1") ag-t-v3) 'hyperboloid_two_sheets)
  (assert-equal (classify-quadric (ag-t-eq "(x + y)^2 = z + 1") ag-t-v3) 'parabolic_cylinder)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 + z^2 - 2*x*y - 2*y*z - 2*x*z + x = 0") ag-t-v3) 'cone)
  (assert-equal (classify-quadric (ag-t-eq "x^2 + y^2 + z^2 - 2*x - 4*y - 6*z + 14 = 0") ag-t-v3) 'point))

(deftest "conics: тип поверхности — по инвариантам, даже если собственные значения не в радикалах"
  ; x² + 2y² + 3z² + 2xy + 4yz = 6: характеристический многочлен не раскладывается — тип есть, канонический вид unknown
  (let* ((eq (ag-t-eq "x^2 + 2*y^2 + 3*z^2 + 2*x*y + 4*y*z - 6 = 0"))
         (rec (canonical-quadric eq ag-t-v3)))
    (assert-equal (classify-quadric eq ag-t-v3) 'hyperboloid_one_sheet)
    (assert-equal (ag-t-get rec 'type) 'hyperboloid_one_sheet)
    (assert-equal (ag-t-get rec 'status) 'unknown)
    (assert-equal (quadric-check eq ag-t-v3 rec) 'unknown)))

(deftest "conics: инварианты поверхности x² + y² − z² = 1"
  (let ((inv (quadric-invariants (ag-t-eq "x^2 + y^2 - z^2 = 1") ag-t-v3)))
    (assert-equal (ag-t-get inv 'I1) 1)
    (assert-equal (ag-t-get inv 'I2) -1)
    (assert-equal (ag-t-get inv 'I3) -1)
    (assert-equal (ag-t-get inv 'I4) 1)))

(define ag-t-quadrics
  '("x^2 + y^2 - z^2 = 0" "x^2 + y^2 - z = 0" "x^2 + y^2 - z^2 = 1" "x^2 - y^2 - z^2 = 1" "x*y = z" "x^2 + y^2 = 1"
    "x^2/4 + y^2/9 + z^2 = 1" "x^2 + y^2 + z^2 + 1 = 0" "x^2 + y^2 + z^2 = 0" "x^2 - y^2 = 1" "x^2 - y^2 = 0" "x^2 + y^2 = 0"
    "x^2 = 2*y" "x^2 = 1" "x^2 = -1" "x^2 = 0" "x^2 + y^2 + 1 = 0" "x^2 - y^2 = z"
    "2*x^2 + 2*y^2 + 2*z^2 + 2*x*y + 2*y*z + 2*x*z = 3" "x*y + y*z + x*z = 1"
    "x^2 + y^2 + z^2 - 2*x*y - 2*y*z - 2*x*z + x = 0" "(x + y)^2 = z + 1"
    "x^2 + y^2 + z^2 - 2*x - 4*y - 6*z + 14 = 0" "x*y = 1" "x*y + z^2 = 0" "2*x^2 + y^2 - 4*x + 2*y + 3*z = 1"))

(deftest "conics: сертификат принимает канонический вид всех тестовых поверхностей"
  (for-each
   (lambda (s)
     (let* ((eq (ag-t-eq s)) (rec (canonical-quadric eq ag-t-v3)))
       (assert-equal (ag-t-get rec 'status) 'ok)
       (assert-equal (ag-t-get rec 'type) (classify-quadric eq ag-t-v3))
       (assert-equal (quadric-check eq ag-t-v3 rec) 'exact)))
   ag-t-quadrics))

(deftest "conics: ху = z — гиперболический параболоид с поворотом на 45°, канонический вид x′² − y′² = 2z′"
  (let* ((eq (ag-t-eq "x*y = z")) (rec (canonical-quadric eq ag-t-v3)))
    (assert-equal (ag-t-get rec 'type) 'hyperbolic_paraboloid)
    (assert-equal (ag-t-get rec 'equation) (simplify '(= (+ (^ xp 2) (* -1 (^ yp 2))) (* 2 zp))))
    (assert-equal (ag-t-get rec 'eigenvalues) '(0 1/2 -1/2))
    ; вращение ортогонально, определитель +1
    (let ((R (map (lambda (row) (map ag-t-n row)) (ag-t-get rec 'rotation))))
      (assert-true (ag-t-close? (ag-t-n (apply + (map2 * (car R) (car R)))) 1))
      (assert-true (ag-t-close? (ag-t-n (apply + (map2 * (car R) (cadr R)))) 0)))
    ; точка поверхности по формулам преобразования
    (let ((P (ag-t-map rec '(xp yp zp) '(3 1 4))))
      (assert-true (ag-t-close? (- (* (car P) (cadr P)) (caddr P)) 0)))))

(deftest "conics: подделки поверхности — неверная ось, растяжение, неверный тип"
  (let* ((eq (ag-t-eq "x^2/4 + y^2/9 + z^2 = 1")) (rec (canonical-quadric eq ag-t-v3)))
    (assert-equal (quadric-check eq ag-t-v3 rec) 'exact)
    (assert-equal (quadric-check eq ag-t-v3 (ag-t-put rec 'equation (simplify '(= (+ (* 1/4 (^ xp 2)) (* 1/10 (^ yp 2)) (^ zp 2)) 1)))) 'mismatch)
    (assert-equal (quadric-check eq ag-t-v3 (ag-t-put rec 'equation (simplify '(= (+ (* 1/4 (^ xp 2)) (* 1/9 (^ yp 2)) (^ zp 2)) 1)))) 'mismatch)
    (assert-equal (quadric-check eq ag-t-v3 (ag-t-put rec 'substitution '((x (* 2 xp)) (y yp) (z zp)))) 'mismatch)
    (assert-equal (quadric-check (ag-t-eq "x^2 + y^2 + z^2 = 1") ag-t-v3 rec) 'mismatch))
  (let* ((eq (ag-t-eq "x*y = z")) (rec (canonical-quadric eq ag-t-v3)))
    (assert-equal (quadric-check eq ag-t-v3 (ag-t-put rec 'equation (simplify '(= (+ (^ xp 2) (^ yp 2)) (* 2 zp))))) 'mismatch)
    (assert-equal (quadric-check eq ag-t-v3 (ag-t-put rec 'substitution '((x xp) (y yp) (z zp)))) 'mismatch)))

(deftest "conics: параметры в коэффициентах поверхности — unknown; не многочлен — ошибка"
  (assert-equal (classify-quadric (ag-t-eq "a*x^2 + y^2 + z^2 = 1") ag-t-v3) 'unknown)
  (assert-equal (ag-t-get (canonical-quadric (ag-t-eq "a*x^2 + y^2 + z^2 = 1") ag-t-v3) 'status) 'unknown)
  (assert-error (classify-quadric (ag-t-eq "x^2 + y^2 + z^3 = 1") ag-t-v3))
  (assert-error (classify-quadric (ag-t-eq "x + y + z = 1") ag-t-v3)))

; ---- язык ----
(deftest "conics: входной язык — classify_conic, canonical_conic, conic_elements, conic_check"
  (assert-equal (math-eval "classify_conic(x^2/4 + y^2/9 = 1, [x, y])") 'ellipse)
  (assert-equal (math-eval "stat_get(conic_elements(x^2 - y^2 = 1, [x, y]), type)") 'hyperbola)
  (assert-equal (math-eval "stat_get(conic_elements(y = x^2, [x, y]), p)") 1/2)
  (assert-equal (math-eval "conic_check(5*x^2 + 4*x*y + 2*y^2 = 1, [x, y], canonical_conic(5*x^2 + 4*x*y + 2*y^2 = 1, [x, y]))") 'exact)
  (assert-equal (math-eval "classify_quadric(x^2 + y^2 - z^2 = 1, [x, y, z])") 'hyperboloid_one_sheet)
  (assert-equal (math-eval "quadric_check(x*y = z, [x, y, z], canonical_quadric(x*y = z, [x, y, z]))") 'exact))
