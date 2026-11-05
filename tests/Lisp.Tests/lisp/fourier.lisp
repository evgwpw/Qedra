; fourier.lisp — тесты шага FS: ряды Фурье на отрезке (lib/fourier.lisp).
; Оракулы (общеизвестные): f = x на [−π, π]: a0 = an = 0, bn = 2(−1)^(n+1)/n; f = x²: a0 = 2π²/3, an = 4(−1)^n/n², bn = 0
; (Парсеваль даёт Σ1/n⁴ = π⁴/90); меандр: bn = 2(1 − (−1)^n)/(nπ), Парсеваль даёт Σ1/(2k+1)² = π²/8;
; |x|: a0 = π, an = 2((−1)^n − 1)/(πn²); синус-ряд 1 на [0, π]: bn = 2(1 − (−1)^n)/(nπ).
; Независимо: численная квадратура (fourier-coefficients-check), частичные суммы N = 200 в точках непрерывности,
; значение в разрыве — полусумма; подделки — чужие коэффициенты, неинтегрируемая f.
; Имя функции Фурье-преобразования `fourier` (transforms.lisp) не затронуто.

(define fst-lo '(* -1 pi))
(define fst-meander '(piecewise (((< x 0) -1) ((> x 0) 1))))

(define (fst-sgn k) (if (= (modulo k 2) 0) 1 -1))
(define (fst-near? a b tol) (< (abs (- a b)) tol))
(define (fst-at c k) (eval-num (subst (list 'n k) c)))
(define (fst-pi) (eval-num 'pi))

; коэффициенты an, bn совпадают с ожидаемыми формулами при n = 1…8 (числами)
(define (fst-match? c fa fb)
  (every? (lambda (k) (and (fst-near? (fst-at (cadr c) k) (fa k) 1e-12)
                           (fst-near? (fst-at (caddr c) k) (fb k) 1e-12)))
          '(1 2 3 4 5 6 7 8)))

(define (fst-ps f a b N x0) (eval-num (subst (list 'x x0) (fourier-series f 'x a b N))))

; ---------- коэффициенты ----------

(deftest "f = x на [−π, π]: a0 = an = 0, bn = 2(−1)^(n+1)/n"
  (let ((c (fourier-coefficients 'x 'x fst-lo 'pi)))
    (assert-equal (car c) 0)
    (assert-equal (cadr c) 0)
    (assert-true (fst-match? c (lambda (k) 0) (lambda (k) (/ (* 2 (- 0 (fst-sgn k))) k))))
    (assert-equal (fourier-coefficients-check 'x 'x fst-lo 'pi c) 'numeric)))

(deftest "f = x²: a0 = 2π²/3, an = 4(−1)^n/n², bn = 0"
  (let ((c (fourier-coefficients '(^ x 2) 'x fst-lo 'pi)))
    (assert-equal (car c) '(* 2/3 (^ pi 2)))
    (assert-true (fst-match? c (lambda (k) (/ (* 4 (fst-sgn k)) (* k k))) (lambda (k) 0)))
    (assert-equal (fourier-coefficients-check '(^ x 2) 'x fst-lo 'pi c) 'numeric)))

(deftest "меандр: a = 0, bn = 2(1 − (−1)^n)/(nπ)"
  (let ((c (fourier-coefficients fst-meander 'x fst-lo 'pi)))
    (assert-equal (car c) 0)
    (assert-equal (cadr c) 0)
    (assert-true (fst-match? c (lambda (k) 0) (lambda (k) (/ (* 2 (- 1 (fst-sgn k))) (* k (fst-pi))))))
    (assert-equal (fourier-coefficients-check fst-meander 'x fst-lo 'pi c) 'numeric)))

(deftest "|x|: a0 = π, an = 2((−1)^n − 1)/(πn²), bn = 0"
  (let ((c (fourier-coefficients '(abs x) 'x fst-lo 'pi)))
    (assert-equal (car c) 'pi)
    (assert-true (fst-match? c (lambda (k) (/ (* 2 (- (fst-sgn k) 1)) (* (fst-pi) k k))) (lambda (k) 0)))
    (assert-equal (fourier-coefficients-check '(abs x) 'x fst-lo 'pi c) 'numeric)))

(deftest "синус-ряд f = 1 на [0, π]: bn = 2(1 − (−1)^n)/(nπ)"
  (let ((s (fourier-sine-series 1 'x 'pi)))
    (assert-equal (car s) 'sum)
    (assert-true (fst-near? (eval-num (subst '((x 1) (n 1)) (cadr s))) (/ (* 4 (eval-num '(sin 1))) (fst-pi)) 1e-12))
    (assert-true (fst-near? (eval-num (subst '((x 1) (n 2)) (cadr s))) 0 1e-12))
    (assert-true (fst-near? (eval-num (subst '((x 1) (n 3)) (cadr s)))
                            (/ (* 4 (eval-num '(sin 3))) (* 3 (fst-pi))) 1e-12))))

(deftest "синус- и косинус-ряд x на [0, π]"
  (assert-true (fst-near? (fst-ps 'x 0 'pi 1 0.5) 0.0 2.0))  ; частичная сумма с одним членом — не расходится
  (let ((s (fourier-sine-series 'x 'x 'pi 200)) (c (fourier-cosine-series 'x 'x 'pi 200)))
    (assert-true (fst-near? (eval-num (subst '(x 1.0) s)) 1.0 0.02))
    (assert-true (fst-near? (eval-num (subst '(x 2.0) s)) 2.0 0.02))
    (assert-true (fst-near? (eval-num (subst '(x 1.0) c)) 1.0 1e-3))
    (assert-true (fst-near? (eval-num (subst '(x 2.0) c)) 2.0 1e-3))))

(deftest "другие отрезки: x² на [0, 2], x на [1, 3], |x − 1| на [0, 3]"
  (for-each (lambda (case)
              (let ((c (fourier-coefficients (car case) 'x (cadr case) (caddr case))))
                (assert-true (list? c))
                (assert-equal (fourier-coefficients-check (car case) 'x (cadr case) (caddr case) c) 'numeric)))
            (list (list '(^ x 2) 0 2) (list 'x 1 3) (list '(abs (- x 1)) 0 3) (list '(exp x) -1 1) (list '(cos (* 3 x)) 0 2))))

(deftest "резонансный номер: sin x и x sin x (формула общего n неверна при n = 1)"
  (let ((c (fourier-coefficients '(sin x) 'x fst-lo 'pi)))
    (assert-equal (cadr c) 0)
    (assert-equal (fourier-coefficients-check '(sin x) 'x fst-lo 'pi c) 'numeric)
    (assert-true (fst-near? (fst-ps '(sin x) fst-lo 'pi 5 0.7) (eval-num '(sin 0.7)) 1e-12)))
  (let ((c (fourier-coefficients '(* x (sin x)) 'x fst-lo 'pi)))
    (assert-equal (fourier-coefficients-check '(* x (sin x)) 'x fst-lo 'pi c) 'numeric)
    ; a0 = 2, a1 = −1/2 (не из общей формулы): сумма с одним членом в x = 0 равна 1 − 1/2
    (assert-true (fst-near? (fst-ps '(* x (sin x)) fst-lo 'pi 1 0.0) 0.5 1e-12))))

(deftest "кусочная f с else и несколькими кусками"
  (let ((f '(piecewise (((< x 1) x) (else 1)))))
    (assert-equal (fourier-coefficients-check f 'x 0 2 (fourier-coefficients f 'x 0 2)) 'numeric)
    (assert-equal (fourier-value-at f 'x 0 2 1) 1)))

; ---------- целые n: sin(nπ) = 0 только для целого ----------

(deftest "n объявляется только на время вычисления"
  (fourier-coefficients '(^ x 2) 'x fst-lo 'pi)
  (assert-equal (declarations 'n) '())
  (assert-equal (simplify '(sin (* n pi))) '(sin (* n pi)))
  (assert-equal (simplify '(cos (* n pi))) '(cos (* n pi))))

(deftest "параметр n в f — ошибка, не молчаливый неверный ответ"
  (assert-error (fourier-coefficients '(* n x) 'x fst-lo 'pi)))

; ---------- частичные суммы и значения ----------

(deftest "частичная сумма N = 200 в трёх точках непрерывности"
  (for-each (lambda (x0) (assert-true (fst-near? (fst-ps '(^ x 2) fst-lo 'pi 200 x0) (* x0 x0) 1e-3)))
            '(0.3 1.0 -2.0))
  (for-each (lambda (x0) (assert-true (fst-near? (fst-ps '(abs x) fst-lo 'pi 200 x0) (abs x0) 1e-3)))
            '(0.3 1.5 -2.5))
  (for-each (lambda (x0) (assert-true (fst-near? (fst-ps 'x fst-lo 'pi 200 x0) x0 0.03)))
            '(0.3 1.0 -1.0))
  (assert-true (fst-near? (fst-ps fst-meander fst-lo 'pi 200 1.0) 1.0 0.02))
  (assert-true (fst-near? (fst-ps fst-meander fst-lo 'pi 200 2.0) 1.0 0.02))
  (assert-true (fst-near? (fst-ps fst-meander fst-lo 'pi 200 -1.5) -1.0 0.02)))

(deftest "частичная сумма в разрыве — 0 (полусумма), общий вид ряда"
  (assert-true (fst-near? (fst-ps fst-meander fst-lo 'pi 200 0.0) 0.0 1e-12))
  (let ((s (fourier-series '(^ x 2) 'x fst-lo 'pi)))
    (assert-equal (car s) '+)
    (assert-equal (car (caddr s)) 'sum)
    (assert-equal (cdr (cdr (cdr (caddr s)))) '(1 inf))))

(deftest "значение в точке разрыва — полусумма (Дирихле), с периодическим продолжением"
  (assert-equal (fourier-value-at fst-meander 'x fst-lo 'pi 0) 0)
  (assert-equal (fourier-value-at fst-meander 'x fst-lo 'pi 'pi) 0)
  (assert-equal (fourier-value-at fst-meander 'x fst-lo 'pi fst-lo) 0)
  (assert-equal (fourier-value-at fst-meander 'x fst-lo 'pi '(* 3 pi)) 0)
  (assert-equal (fourier-value-at fst-meander 'x fst-lo 'pi 1) 1)
  (assert-equal (fourier-value-at fst-meander 'x fst-lo 'pi -1) -1)
  (assert-equal (fourier-value-at 'x 'x fst-lo 'pi 'pi) 0)
  (assert-equal (fourier-value-at '(^ x 2) 'x fst-lo 'pi 'pi) '(^ pi 2))
  (assert-equal (fourier-value-at '(abs x) 'x fst-lo 'pi 0) 0)
  (assert-true (fst-near? (eval-num (fourier-value-at 'x 'x fst-lo 'pi 4)) (- 4 (* 2 (fst-pi))) 1e-12)))

; ---------- комплексная форма ----------

(deftest "комплексные коэффициенты: cn = (an − i bn)/2"
  (let ((c (fourier-complex-coefficients 'x 'x fst-lo 'pi)))
    (assert-equal (car c) 0)
    ; c1 = −i·2·(+1)/2·… : b1 = 2, c1 = −i; c_{−1} = i
    (assert-equal (simplify (subst '(n 1) (cadr c))) (simplify '(* -1 %i)))
    (assert-equal (simplify (subst '(n 1) (caddr c))) '%i)
    (assert-equal (simplify (subst '(n 2) (cadr c))) (simplify '(* 1/2 %i)))))

; ---------- Парсеваль ----------

(deftest "Парсеваль: x² — точно (даёт Σ1/n⁴ = π⁴/90)"
  (let ((r (parseval-check '(^ x 2) 'x fst-lo 'pi)))
    (assert-equal (car r) 'exact)
    (assert-equal (cadr r) '(* 1/5 (^ pi 4)))
    (assert-equal (caddr r) (cadr r))))

(deftest "Парсеваль: меандр — точно (Σ1/(2k+1)² = π²/8), x и |x|"
  (assert-equal (parseval-check fst-meander 'x fst-lo 'pi) '(exact 1 1))
  (assert-equal (car (parseval-check 'x 'x fst-lo 'pi)) 'exact)
  (assert-equal (car (parseval-check '(abs x) 'x fst-lo 'pi)) 'exact)
  (assert-equal (car (parseval-check '(^ x 3) 'x fst-lo 'pi)) 'exact))

(deftest "Парсеваль: e^x — численно, резонансный sin x — численно"
  (assert-equal (car (parseval-check '(exp x) 'x fst-lo 'pi)) 'numeric)
  (assert-equal (car (parseval-check '(sin x) 'x fst-lo 'pi)) 'numeric))

(deftest "подделки: подставные коэффициенты — mismatch, неинтегрируемая f — unknown/отказ"
  ; неверные an (знак без (−1)^n), неверный a0
  (assert-equal (car (parseval-check '(^ x 2) 'x fst-lo 'pi (list 0 '(/ (^ -1 n) (^ n 2)) 0))) 'mismatch)
  (assert-equal (car (parseval-check '(^ x 2) 'x fst-lo 'pi (list '(* 2/3 (^ pi 2)) '(/ 3 (^ n 2)) 0))) 'mismatch)
  ; Парсеваль не видит знаков: 4/n² вместо 4(−1)^n/n² даёт то же самое — это ловит fourier-coefficients-check
  (assert-equal (car (parseval-check '(^ x 2) 'x fst-lo 'pi (list '(* 2/3 (^ pi 2)) '(/ 4 (^ n 2)) 0))) 'exact)
  (assert-equal (car (parseval-check fst-meander 'x fst-lo 'pi (list 0 0 '(/ 4 n)))) 'mismatch)
  (assert-equal (car (parseval-check '(exp x) 'x fst-lo 'pi (list 1 '(/ (^ -1 n) (+ 1 (^ n 2))) 0))) 'mismatch)
  ; 1/x на [−1, 1] не интегрируема: ни чисел, ни ряда
  (assert-equal (fourier-coefficients '(/ 1 x) 'x -1 1) 'unknown)
  (assert-equal (fourier-series '(/ 1 x) 'x -1 1) 'unknown)
  (assert-equal (fourier-series '(/ 1 x) 'x -1 1 5) 'unknown)
  (assert-equal (fourier-sine-series '(/ 1 x) 'x 1) 'unknown)
  (assert-equal (fourier-value-at '(/ 1 x) 'x -1 1 0) 'unknown)
  (assert-equal (car (parseval-check '(/ 1 x) 'x -1 1)) 'unknown)
  (assert-equal (fourier-coefficients '(/ 1 (^ x 2)) 'x -1 1) 'unknown))

(deftest "проверка коэффициентов отвергает чужие"
  (assert-equal (fourier-coefficients-check '(^ x 2) 'x fst-lo 'pi (list '(* 2/3 (^ pi 2)) '(/ (^ -1 n) (^ n 2)) 0)) #f)
  (assert-equal (fourier-coefficients-check 'x 'x fst-lo 'pi (list 0 0 '(/ (* 2 (^ -1 n)) n))) #f)
  (assert-equal (fourier-coefficients-check '(/ 1 x) 'x -1 1 (list 0 0 0)) 'unknown))

; ---------- существующее преобразование Фурье не затронуто ----------

(deftest "fourier (преобразование) работает как раньше"
  (assert-equal (fourier '(exp (* -1 (abs t))) 't 'w) '(* 2 (^ (+ 1 (^ w 2)) -1)))
  (assert-equal (fourier '(exp (* -1 (^ t 2))) 't 'w) '(* (^ pi 1/2) (exp (* -1/4 (^ w 2))))))
