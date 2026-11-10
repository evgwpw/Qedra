; optimize.lisp — тесты шага OPT.1: критические точки, гессиан, классификация, множители Лагранжа.
; Проверяем только локальную классификацию; ложных min/max быть не должно (сомнение → unknown).

; ---------- критические точки: теорема Ферма ----------

(deftest "opt/OPT.1: x^2+y^2 — единственная критическая точка (0,0)"
  (let ((r (critical-points '(+ (^ x 2) (^ y 2)) '(x y))))
    (assert-equal r '(((= x 0) (= y 0))))))

(deftest "opt/OPT.1: extrema x^2+y^2 — (0,0) min"
  (let ((r (extrema '(+ (^ x 2) (^ y 2)) '(x y))))
    (assert-equal r '((((= x 0) (= y 0)) 0 min)))))

(deftest "opt/OPT.1: extrema x^2-y^2 — (0,0) saddle"
  (let ((r (extrema '(- (^ x 2) (^ y 2)) '(x y))))
    (assert-equal r '((((= x 0) (= y 0)) 0 saddle)))))

(deftest "opt/OPT.1: extrema -x^2-2y^2+4y — (0,1) max, значение 2"
  (let ((r (extrema '(+ (* -1 (^ x 2)) (* -2 (^ y 2)) (* 4 y)) '(x y))))
    (assert-equal r '((((= x 0) (= y 1)) 2 max)))))

; ---------- одномерные ----------

(deftest "opt/OPT.1: extrema x^3-3x — min в 1, max в -1"
  (let ((r (extrema '(- (^ x 3) (* 3 x)) '(x))))
    (assert-equal r '((((= x -1)) 2 max) (((= x 1)) -2 min)))))

(deftest "opt/OPT.1: x^4 — вырожденный гессиан → unknown, НЕ min"
  (let ((r (extrema '(^ x 4) '(x))))
    (assert-equal r '((((= x 0)) 0 unknown)))))

; ---------- двумерные с несколькими точками ----------

(deftest "opt/OPT.1: x^4+y^4-4xy — три точки: (0,0) saddle, (±1,±1) min"
  (let ((r (extrema '(+ (^ x 4) (^ y 4) (* -4 x y)) '(x y))))
    (assert-true (member? (quote (((= x 0) (= y 0)) 0 saddle)) r))
    (assert-true (member? (quote (((= x 1) (= y 1)) -2 min)) r))
    (assert-true (member? (quote (((= x -1) (= y -1)) -2 min)) r))))

(deftest "opt/OPT.1: x^2*y в (0,0) — unknown (седло, замаскированное вырожденностью)"
  (assert-equal (classify-critical '(* (^ x 2) y) '(x y) '((= x 0) (= y 0))) 'unknown))

; ---------- гессиан ----------

(deftest "opt/OPT.1: hessian x^2+y^2 — ((2 0) (0 2))"
  (assert-equal (hessian '(+ (^ x 2) (^ y 2)) '(x y)) '((2 0) (0 2))))

(deftest "opt/OPT.1: hessian x*y — ((0 1) (1 0))"
  (assert-equal (hessian '(* x y) '(x y)) '((0 1) (1 0))))

; ---------- сертификат: подстановка ----------

(deftest "opt/OPT.1: сертификат отвергает ложную точку (x^2+y^2 в (1,0))"
  (assert-true (not (check-critical (quote (+ (^ x 2) (^ y 2))) (quote (x y)) (quote ((= x 1) (= y 0)))))))

(deftest "opt/OPT.1: сертификат принимает истинную точку (x^2+y^2 в (0,0))"
  (assert-true (check-critical '(+ (^ x 2) (^ y 2)) '(x y) '((= x 0) (= y 0)))))

; ---------- множители Лагранжа ----------

(deftest "opt/OPT.1: lagrange x+y при x^2+y^2=1 — (±1/√2, ±1/√2), значения ±√2"
  (let ((r (lagrange '(+ x y) (list '(- (+ (^ x 2) (^ y 2)) 1)) '(x y))))
    (assert-equal (length r) 2)
    (let ((vs (map cadr r))
          (ps (map car r))
          (ts (map (lambda (row) (nth row 3)) r)))
      ; значения ±√2
      (assert-true (member? '(^ 2 1/2) vs))
      (assert-true (member? '(* -1 (^ 2 1/2)) vs))
      ; точки (±1/√2, ±1/√2)
      (assert-true (member? '((= x (* 1/2 (^ 2 1/2))) (= y (* 1/2 (^ 2 1/2)))) ps))
      (assert-true (member? '((= x (* -1/2 (^ 2 1/2))) (= y (* -1/2 (^ 2 1/2)))) ps))
      ; (1/√2,1/√2) — max; (−1/√2,−1/√2) — min
      (assert-true (member? 'max ts))
      (assert-true (member? 'min ts)))))

(deftest "opt/OPT.1: lagrange x*y при x+y=10 — (5,5), max 25"
  (let ((r (lagrange '(* x y) (list '(- (+ x y) 10)) '(x y))))
    (assert-equal (length r) 1)
    (assert-equal (car (car r)) '((= x 5) (= y 5)))
    (assert-equal (cadr (car r)) 25)
    (assert-equal (nth (car r) 3) 'max)))

; lagrange: точка, значение и λ выдаются даже когда классификация unknown (другой размер)
(deftest "opt/OPT.1: lagrange трёх переменных — тип unknown, точка и значение есть"
  (let ((r (lagrange (quote (+ (* x y) z)) (list (quote (- (+ (^ x 2) (^ y 2) (^ z 2)) 3))) (quote (x y z)))))
    (assert-true (> (length r) 0))
    (map (lambda (row) (assert-equal (nth row 3) (quote unknown))) r)
    (map (lambda (row) (assert-true (list? (car row)))) r)))

; линия критических точек (решение-семейство) не теряется молча; классификация — unknown
(deftest "opt/OPT.1: семейство критических точек (x-y)^2 — не пустой ответ, unknown"
  (let ((r (extrema '(^ (- x y) 2) '(x y))))
    (assert-equal (length r) 1)
    (assert-equal (nth (car r) 2) 'unknown)))
