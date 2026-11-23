; INT.FLOOR: floor/ceiling во входном языке и в определённых интегралах — lib/integrate/floor.lisp.
; Определённый интеграл: отрезок разбивается по точкам скачков, на кускам floor — целое; ответ — точное значение
; (эталоны — арифметика по кускам или корпус mit_bee_official). Что не берётся (бесконечно много кусков, немонотонное u)
; остаётся невычисленной формой, а не числом.

(define (fli-int s) (math-eval s))
(define (fli-open? r) (contains-sym? r 'integrate))
(define (fli-near? a b) (< (abs (- a b)) 1e-9))
(define (fli-sqrt n) (eval-num (list 'sqrt n)))
; Σ_{k=k0}^{299} (1 − k·log(1 + 1/k)) в double
(define (fli-sum k acc)
  (if (> k 299)
      acc
      (fli-sum (+ k 1) (+ acc (- 1.0 (* k (log (+ 1.0 (/ 1.0 k)))))))))

(deftest "floor-int/1: floor и ceiling во входном языке — числа, постоянные, форма"
  (assert-equal (fli-int "floor(7/2)") 3)
  (assert-equal (fli-int "ceiling(7/2)") 4)
  (assert-equal (fli-int "floor(-7/2)") -4)
  (assert-equal (fli-int "floor(sqrt(2))") 1)
  (assert-equal (fli-int "ceiling(pi)") 4)
  (assert-equal (fli-int "floor(2.5)") 2)
  (assert-equal (fli-int "floor(x)") '(floor x))
  (assert-equal (fli-int "floor(floor(x))") '(floor x))
  (assert-equal (fli-int "floor(ceiling(x))") '(ceiling x))
  (assert-equal (fli-int "floor(x + 3)") (simplify '(+ 3 (floor x)))))

(deftest "floor-int/2: eval-num считает floor/ceiling"
  (assert-equal (eval-num (subst '(x 2.5) '(+ (floor x) (* 10 (ceiling x))))) 32.0)
  (assert-equal (eval-num '(floor -0.5)) -1.0)
  (assert-equal (eval-num (subst '(x 3) '(ceiling (^ x 1/2)))) 2.0))

(deftest "floor-int/3: простые случаи — целые границы"
  (assert-equal (fli-int "integrate(floor(x), x, 0, 5)") 10)
  (assert-equal (fli-int "integrate(ceiling(x), x, 0, 5)") 15)
  (assert-equal (fli-int "integrate((x - floor(x))^2, x, 0, 256)") 256/3)
  (assert-equal (fli-int "integrate(x - floor(x), x, 0, 1)") 1/2)
  (assert-equal (fli-int "integrate(floor(x)*x*ceiling(x), x, 0, 100)") 24997500)
  (assert-equal (fli-int "integrate(x^2 - floor(x)*ceiling(x), x, 0, 2022)") 674))

(deftest "floor-int/4: нецелые границы и обратный порядок"
  (assert-equal (fli-int "integrate(floor(x), x, 1/2, 7/2)") 9/2)
  (assert-equal (fli-int "integrate(floor(2*x), x, 5, 0)") -45/2)
  (assert-equal (fli-int "integrate(floor(x), x, 3, 3)") 0)
  (assert-equal (fli-int "integrate(floor(x), x, 1/4, 3/4)") 0))

(deftest "floor-int/5: floor(√x), ceiling(√x), √x − floor(√x), floor(log₂ x), floor(log₄₃ x)"
  (assert-equal (fli-int "integrate(floor(sqrt(x)), x, 0, 16)") 34)
  (assert-equal (fli-int "integrate(ceiling(sqrt(x)), x, 0, 100)") 715)
  (assert-equal (fli-int "integrate(sqrt(x) - floor(sqrt(x)), x, 0, 2025)") 1020)
  (assert-equal (fli-int "integrate(floor(log(x)/log(2)), x, 50, 100)") 286)
  (assert-equal (fli-int "integrate(floor(log(x)/log(43)), x, 1, 2024)") 2156))

(deftest "floor-int/6: вложенные floor/ceiling (олимпиадные)"
  (assert-equal (fli-int "integrate(floor(x)/3 - floor(floor(x)/3), x, 0, 2026)") 675)
  (assert-equal (fli-int "integrate(ceiling(floor(x)/2), x, 0, 20)") 100)
  (assert-equal (fli-int "integrate(floor(x*floor(x)), x, 0, 10)") 303)
  (assert-equal (fli-int "integrate(floor(x/2)/floor(x) + ceiling(x/2)/ceiling(x), x, 1, 100)") 197/2)
  (assert-equal (fli-int "integrate(ceiling(2025/floor(x)) - floor(2025/ceiling(x)), x, 1, 2025)") 4034)
  (assert-equal (fli-int "integrate(floor(x)/ceiling(sqrt(x)), x, 0, 2025)") 59730)
  (assert-equal (fli-int "integrate(floor(log(floor(1/x))), x, 1/4, 1/2)") 1/12))

(deftest "floor-int/7: floor от иррациональной постоянной на куске, (−1)^floor"
  (assert-equal (fli-int "integrate(floor(((1 + sqrt(5))/2)^floor(x)), x, 0, 10)") 193)
  (let ((r (fli-int "integrate((-1)^(floor(x) + floor(x/sqrt(2)) + floor(x/sqrt(3))), x, 0, 5)")))
    (assert-true (not (fli-open? r)))
    (assert-true (fli-near? (eval-num r) (- (+ (* 8 (fli-sqrt 2)) (* 6 (fli-sqrt 3))) 21)))))


(deftest "floor-int/8: точки скачков — иррациональные: floor(eˣ), ответ через логарифмы простых"
  (let ((r (fli-int "integrate(floor(exp(x)), x, 0, 2)")))
    (assert-true (not (fli-open? r)))
    ; 14 − log 5040 = 14 − 4·log 2 − 2·log 3 − log 5 − log 7
    (assert-true (fli-near? (eval-num r) (- 14.0 (eval-num '(log 5040)))))))

(deftest "floor-int/9: тысячи кусков с логарифмами — параметрическая первообразная (∫(x − floor x)/x)"
  ; Σ_{k=1}^{n} (1 − k·log((k+1)/k)) — сверка с прямой суммой в double
  (let* ((r (fli-int "integrate((x - floor(x))/x, x, 1, 300)"))
         (s (fli-sum 1 0.0)))
    (assert-true (not (fli-open? r)))
    (assert-true (< (abs (- (eval-num r) s)) 1e-9))))

(deftest "floor-int/10: что не берётся — невычисленная форма, не число"
  ; floor(sin x): u немонотонна на [0, 2π]
  (assert-true (fli-open? (fli-int "integrate(floor(2023*sin(x)), x, 0, 2*pi)")))
  ; бесконечно много кусков у нуля: floor(√(1 + 1/x))
  (assert-true (fli-open? (fli-int "integrate(floor(sqrt(1 + 1/x)), x, 0, 1)")))
  ; бесконечный промежуток, u неограничена
  (assert-true (fli-open? (fli-int "integrate(1/(x + 1 + floor(2*sqrt(x)))^2, x, 0, oo)")))
  ; параметр: значение куска — не число
  (assert-true (fli-open? (fli-int "integrate(a*floor(x), x, 0, 3)"))))

(deftest "floor-int/11: числа-пределы без floor не затронуты"
  (assert-equal (fli-int "integrate(x^2, x, 0, 3)") 9)
  (assert-equal (fli-int "integrate(floor(5/2)*x, x, 0, 2)") 4))
