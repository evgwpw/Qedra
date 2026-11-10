; Lisp-тесты шага 21h: интегрирование рациональных функций (Эрмит + Лазар–Риобу–Трагер, вещественная форма, root-sum).
; Источники: эталонные тесты (test_rationaltools.py), набор Rubi (1.3.1 Rational functions), Bronstein ISSAC'98 §1.1–1.3,
; Главный инвариант: ответ проверяется ДИФФЕРЕНЦИРОВАНИЕМ в точках, отличных от
; точек самого интегратора (int-check), с собственными значениями параметров. Невычисленная форма — провал теста.

; точки и значения параметров — рациональные (суммы по корням eval-num считает точно); параметры не совпадают с точками
; (полюсы вида x = a)
(define ri-points '(123/1000 -11/20 91/100 17/10 -23/10 41/10))
(define ri-param-values '(137/100 261/100 193/100 317/100 129/100 289/100 113/100 271/100))

(define (ri-subst-all e x p vals)
  (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr))) (replace-expr e x p) vals))

; F' − e ≈ 0 численно в нескольких точках (параметры — числа), допуск 1e-9. Суммы по корням в производной вычисляются
; eval-num ТОЧНО (рациональная арифметика в ℚ[t]/(Q), одно округление), поэтому шума от больших вычетов нет
(define (ri-deriv-ok? F e x)
  (let* ((syms (integrate::int-symbols (list '+ F e) x))
         (vals (map2 list syms ri-param-values))
         (d (list '- (diff x F) e))
         (tol 0.000000001))
    (every? (lambda (p)
              (let ((a (num-abs (integrate::int-hyp (ri-subst-all d x p vals))))
                    (b (num-abs (integrate::int-hyp (ri-subst-all e x p vals)))))
                (and a b (< a (* tol (+ 1 b))))))
            ri-points)))

(define (ri-unevaluated? r) (and (list? r) (not (null? r)) (equal? (car r) 'integrate)))

; интеграл вычислен и верен
(define (ri-chk e)
  (let ((F (integrate e 'x)))
    (if (ri-unevaluated? F)
        (error (string-append "не вычислен интеграл " (math-print e)))
        ; piecewise (разбор случаев по параметру, integrate/param.lisp) — сертификат int-piecewise-check
        (if (if (and (list? F) (equal? (car F) 'piecewise)) (equal? (int-piecewise-check F e 'x) 'ok) (ri-deriv-ok? F e 'x))
            F
            (error (string-append "производная " (math-print F) " не равна " (math-print e)))))))

(define (ri-str s) (ri-chk (math-read s)))
(define (ri-strs l) (every? (lambda (s) (if (ri-str s) #t #f)) l))

; ---------- численное интегрирование (составная формула Гаусса–Лежандра, 5 узлов): для проверки определённых интегралов ----------
(define ri-gl-nodes '(0.0 0.5384693101056831 -0.5384693101056831 0.906179845938664 -0.906179845938664))
(define ri-gl-weights '(0.5688888888888889 0.47862867049936647 0.47862867049936647 0.23692688505618908 0.23692688505618908))

(define (ri-fval e x p) (num-abs-real (replace-expr e x p)))
(define (num-abs-real v) (eval-num v))

(define (ri-gl-panel e x lo hi)
  (let ((c (/ (+ lo hi) 2)) (h (/ (- hi lo) 2)))
    (* h (foldl (lambda (acc pr) (+ acc (* (cadr pr) (ri-fval e x (+ c (* h (car pr)))))))
                0.0 (map2 list ri-gl-nodes ri-gl-weights)))))

(define (ri-quad e x lo hi n)
  (let ((step (/ (- hi lo) n)))
    (foldl (lambda (acc k) (+ acc (ri-gl-panel e x (+ lo (* k step)) (+ lo (* (+ k 1) step)))))
           0.0 (range n))))

(define (ri-close? a b tol) (< (abs (- a b)) (* tol (+ 1 (abs b)))))

; ---------- эталон: базовые случаи ----------

(deftest "эталон: многочлены, константа, нуль"
  (assert-equal (integrate 0 'x) 0)
  (assert-equal (integrate 7 'x) '(* 7 x))
  (assert-true (ri-strs '("x" "2*x" "-2*x" "8*x^7 + 2*x + 1" "1/(x+1)" "(x^3 - x)/(x - 1)" "x^2/x" "x^3/x^2"))))

; ---------- эталон: чистая логарифмическая часть, Эрмит ----------

(deftest "эталон: x/((x-a)(x+a)) и x/(1-x^2)"
  (assert-true (ri-strs '("x/((x-a)*(x+a))" "x/(1 - x^2)" "-x/(1 - x^2)")))
  (assert-equal (integrate (math-read "x/((x-a)*(x+a))") 'x) (simplify (math-read "log(x^2 - a^2)/2"))))

(deftest "эталон: Эрмит 36/(x^5 - 2x^4 - 2x^3 + 4x^2 + x - 2)"
  (let ((F (ri-str "36/(x^5 - 2*x^4 - 2*x^3 + 4*x^2 + x - 2)")))
    ; рациональная часть (12x + 6)/(x² − 1): производная ответа без логарифмов равна рациональной части
    (assert-true (contains-sym? F 'log))))

(deftest "эталон: 25896 — (4x+7)/(x²+4x+6) + 2/x, (2x+1)/(x²+x+1) + 1/x"
  (assert-true (ri-strs '("(4*x + 7)/(x^2 + 4*x + 6) + 2/x" "(2*x + 1)/(x^2 + x + 1) + 1/x"))))

(deftest "эталон: 4991 — 1/(x(a+bx)^3) (два параметра, кратность 3)"
  (assert-true (ri-strs '("1/(x*(a + b*x)^3)"))))

(deftest "эталон: нулевая логарифмическая часть (x/4 − 4/(1−x))'"
  (assert-true (ri-strs '("1/4 - 4/(1 - x)^2"))))

; ---------- эталон: комплексные корни, вещественная форма ----------

(deftest "эталон: 1/(x^2+1), 1/(x^2+x+1), 1/(x^3+1), 1/(x^2+16)"
  (assert-equal (integrate (math-read "1/(x^2+1)") 'x) '(atan x))
  (assert-true (ri-strs '("1/(x^2 + 1)" "1/(x^2 + x + 1)" "1/(x^3 + 1)" "1/(x^2 + 16)")))
  ; форма 1/(x²+x+1): 2√3/3·atan(√3/3 + 2√3x/3) (после раскрытия скобок совпадает с эталонным)
  (assert-equal (expand (integrate (math-read "1/(x^2+x+1)") 'x))
                (expand (simplify (math-read "2*sqrt(3)*atan(sqrt(3)/3 + 2*x*sqrt(3)/3)/3")))))

(deftest "эталон: параметры a ≠ 0 — 1/(x²+a²), a/(x²+a²), 1/(1+a²x²)"
  (assert-true (ri-strs '("1/(x^2 + a^2)" "a/(x^2 + a^2)" "1/(1 + a^2*x^2)"))))

(deftest "эталон: 5817 — a/(bcx² + a² + ba), a, b, c > 0"
  (assuming ((a positive) (b positive) (c positive))
    (assert-true (ri-strs '("a/(b*c*x^2 + a^2 + b*a)")))))

(deftest "эталон: 5907 — 1/(x²+1)², 1/(x²+a²)²"
  (assert-true (ri-strs '("1/(x^2 + 1)^2" "1/(x^2 + a^2)^2"))))

(deftest "эталон: 6308 — (x² + 1 − k²)/(x² + 1 + a0²), k, a0 вещественные"
  (assuming ((k reals) (a0 reals))
    (assert-true (ri-strs '("(x^2 + 1 - k^2)/(x^2 + 1 + a0^2)")))))

(deftest "эталон: 28186 — 1/(ax²+bx+c), a, b, c вещественные"
  (assuming ((a reals) (b reals) (c reals))
    (assert-true (ri-strs '("1/(a*x^2 + b*x + c)")))))

(deftest "эталон: w²(x−w)³/((x−w)²+1)² по w (x — параметр)"
  (let* ((e (math-read "w^2*(x - w)^3/((x - w)^2 + 1)^2"))
         (F (integrate e 'w)))
    (assert-true (not (ri-unevaluated? F)))
    (assert-true (ri-deriv-ok? F e 'w))))

; ---------- эталон: трудные случаи (непрерывность атанов — Риобу) ----------

(deftest "эталон: (x^4 - 3x^2 + 6)/(x^6 - 5x^4 + 5x^2 + 4) = atan(x) + atan(x^3) + atan(x/2 - 3x^3/2 + x^5/2)"
  (let ((F (integrate (math-read "(x^4 - 3*x^2 + 6)/(x^6 - 5*x^4 + 5*x^2 + 4)") 'x)))
    (assert-equal F (simplify (math-read "atan(x) + atan(x^3) + atan(x/2 - 3*x^3/2 + x^5/2)")))))

(deftest "Непрерывность: ∫_{-5}^{5} (x^4 − 3x^2 + 6)/(x^6 − 5x^4 + 5x^2 + 4) совпадает с квадратурой (атаны без разрывов)"
  (let* ((e (math-read "(x^4 - 3*x^2 + 6)/(x^6 - 5*x^4 + 5*x^2 + 4)"))
         (v (integrate e 'x -5 5))
         (q (ri-quad e 'x -5 5 300)))
    (assert-true (not (ri-unevaluated? v)))
    (assert-true (ri-close? (eval-num v) q 0.000000001))
    ; и на других отрезках
    (assert-true (ri-close? (eval-num (integrate e 'x -2 3)) (ri-quad e 'x -2 3 150) 0.000000001))
    (assert-true (ri-close? (eval-num (integrate e 'x 0.5 7)) (ri-quad e 'x 0.5 7 150) 0.000000001))))

(deftest "эталон: Эрмит с кратностями 2 и 3 — (x^7 − 24x^4 − 4x^2 + 8x − 8)/(x^8 + 6x^6 + 12x^4 + 8x^2)"
  (assert-true (ri-strs '("(x^7 - 24*x^4 - 4*x^2 + 8*x - 8)/(x^8 + 6*x^6 + 12*x^4 + 8*x^2)"
                          "x^3*(x^7 - 24*x^4 - 4*x^2 + 8*x - 8)/(x*(x^8 + 6*x^6 + 12*x^4 + 8*x^2))"
                          "(x^5 - x^4 + 4*x^3 + x^2 - x + 5)/(x^4 - 2*x^3 + 5*x^2 - 4*x + 4)"))))

(deftest "эталон: 28657 — 400π²x²/(1600π⁴x⁴ − 796π²x² + 100): нечисловая константа π, нет скачков"
  (let* ((e (math-read "400*pi^2*x^2/(1600*pi^4*x^4 - 796*pi^2*x^2 + 100)"))
         (F (integrate e 'x)))
    (assert-true (not (ri-unevaluated? F)))
    (assert-true (ri-deriv-ok? F e 'x))
    ; F(1e100) − F(0) ≈ 2.5 (скачков атана нет)
    (assert-true (< (num-abs (list '- (list '- (replace-expr F 'x 1.0e100) (replace-expr F 'x 0)) 2.5)) 0.0000001))))

; ---------- дефектные субрезультанты, корни без радикалов (сумма по корням) ----------

(deftest "1/(x^5+1), 1/(x^4+1), 1/(x^3+2): сумма по корням либо радикалы — производная верна"
  (assert-true (ri-strs '("1/(x^5 + 1)" "1/(x^4 + 1)" "1/(x^3 + 2)" "x/(x^5 + 1)" "x^2/(x^3 - 5)")))
  ; A3′.4: 1/(x^5+1) теперь раскладывается над Q(√5) (квадратичные множители резольвенты) — без root-sum
  (let ((F (integrate (math-read "1/(x^5+1)") 'x)))
    (assert-true (not (contains-sym? F 'root-sum)))
    (assert-true (not (contains-sym? F '%i))))
  (assert-equal (integrate (math-read "x^2/(x^3 - 5)") 'x) (simplify (math-read "log(x^3 - 5)/3"))))

(deftest "x^n + c с числителями 1 и x^k (дефектные PRS), x^n + x + 1"
  (assert-true (ri-strs '("1/(x^7 + 3)" "x^3/(x^7 + 3)" "1/(x^8 + 1)" "x^2/(x^9 + 2)" "1/(x^5 + x + 1)"
                          "1/(x^3 + x + 1)" "1/(x^3 - 2)" "1/(x^5 - x - 1)" "x^4/(x^6 + x + 1)"))))

(deftest "ЛРТ: параметр корневой суммы нормирован — 1/(x^6+x^3+1) без 243 = 3^5 и 19683 = 3^9"
  (let* ((e (math-read "1/(x^6 + x^3 + 1)"))
         (F (integrate e 'x))
         (s (to-string F)))
    (assert-true (ri-deriv-ok? F e 'x))
    (assert-true (not (string-contains? s "243")))
    (assert-true (not (string-contains? s "19683")))
    (assert-true (string-contains? s "(^ t 6)"))))

(deftest "x/(x² − 9), x/(x² + 9) — случай i = deg D"
  (assert-equal (integrate (math-read "x/(x^2 - 9)") 'x) (simplify (math-read "log(x - 3)/2 + log(x + 3)/2")))
  (assert-true (ri-strs '("x/(x^2 - 9)" "x/(x^2 + 9)" "x^3/(x^4 - 16)"))))

; ---------- Bronstein, Tutorial ISSAC'98, §1.1–1.3: утверждения о рациональных функциях ----------

(define (ri-has-sub? e s)
  (or (equal? e s) (and (op-expr? e) (any? (lambda (a) (ri-has-sub? a s)) (cdr e)))))

(deftest "Tutorial §1.2: любое поле, содержащее интеграл 1/(x²+2), содержит √2"
  (let* ((e (math-read "1/(x^2 + 2)")) (F (integrate e 'x)))
    (assert-true (ri-deriv-ok? F e 'x))
    (assert-true (ri-has-sub? F '(^ 2 1/2)))))

(deftest "Tutorial §2.3: ∫ dx/(1+x²) = atan(x) = (√−1/2)·log((√−1+x)/(√−1−x))"
  (assert-equal (integrate (math-read "1/(1 + x^2)") 'x) '(atan x))
  (let ((c (math-read "(%i/2)*log((%i + x)/(%i - x))")))
    (assert-true (every? (lambda (p) (< (num-abs (list '- (list 'atan p) (replace-expr c 'x p))) 0.000000001))
                         '(0.3 1.7 -2.0)))))

(deftest "Tutorial §1.2–1.3: Эрмит — кратные множители, A/(UV^m)"
  (assert-true (ri-strs '("1/(x^2*(x+1)^3)" "(3*x + 1)/((x - 1)^2*(x^2 + 1)^2)" "x^4/((x^2 + 1)^3*(x - 2)^2)"
                          "1/((x^3 + x + 1)^2)" "(x^2 + 3)/((x^3 - 2)^2)"))))

; ---------- Rubi: 1.3.1 Rational functions (Ayres, Edwards–Penney, Grossman, Spivak, Stewart, Thomas, North Texas) ----------

(deftest "Rubi: Ayres"
  (assert-true (ri-strs '("(3*x - 4*x^2 + 3*x^3)/(1 + x^2)"
                          "(5 + 3*x)/(1 - x - x^2 + x^3)"
                          "(-1 - x - x^3 + x^4)/(-x^2 + x^3)"
                          "(2 + x + x^2 + x^3)/(2 + 3*x^2 + x^4)"
                          "(-4 + 8*x - 4*x^2 + 4*x^3 - x^4 + x^5)/(2 + x^2)^3"
                          "(-1 - 3*x + x^2)/(-2*x + x^2 + x^3)"
                          "(3 - x + 3*x^2 - 2*x^3 + x^4)/(3*x - 2*x^2 + x^3)"
                          "(-1 + x + x^3)/(1 + x^2)^2"
                          "(1 + 2*x - x^2 + 8*x^3 + x^4)/((x + x^2)*(1 + x^3))"
                          "(15 - 5*x + x^2 + x^3)/((5 + x^2)*(3 + 2*x + x^2))"
                          "(-3 + 25*x + 23*x^2 + 32*x^3 + 15*x^4 + 7*x^5 + x^6)/((1 + x^2)^2*(2 + x + x^2)^2)"))))

(deftest "Rubi: Edwards and Penney"
  (assert-true (ri-strs '("1/((1 + x^2)*(4 + x^2))"
                          "(x + x^2)/((4 + x)*(-4 + x^2))"
                          "(4 + x^2)/((1 + x^2)*(2 + x^2))"
                          "(5 - 4*x + 3*x^2 + x^4)/((-1 + x)^2*(1 + x^2))"
                          "(1 + x^4)/(2 + x^2)"
                          "(2 + 2*x + x^4)/(x^4 + x^5)"
                          "(2 + x + x^3)/(1 + 2*x^2 + x^4)"
                          "(1 + 2*x + x^2 + x^3)/(1 + 2*x^2 + x^4)"
                          "(3 + 4*x)/((1 + x^2)*(2 + x^2))"
                          "(2 + x)/((1 + x^2)*(4 + x^2))"))))

(deftest "Rubi: Grossman"
  (assert-true (ri-strs '("(2 - x + x^3)/(-7 - 6*x + x^2)"
                          "(-1 + x^5)/(-1 + x^2)"
                          "(5 + 2*x - x^2 + x^3)/(1 + x + x^2)"
                          "(-3 + x - 2*x^3 + x^4)/(10 - 8*x + 2*x^2)"
                          "(1 + 2*x + 3*x^2 + x^3)/((-3 + x)*(-2 + x)*(-1 + x))"
                          "(2 - 7*x + x^2 - x^3 + x^4)/(-24 - 14*x + x^2 + x^3)"
                          "(2 + x^2)/((-1 + x)^2*x*(1 + x))"
                          "(3 + x^2 + x^3)/(2 + x^2)^2"
                          "(-35 + 70*x - 4*x^2 + 2*x^3)/((26 - 10*x + x^2)*(17 - 2*x + x^2))"
                          "(2 + x^2)/((-5 + x)*(-3 + x)*(4 + x))"
                          "x^4/((-1 + x)*(2 + x^2))"))))

(deftest "Rubi: Spivak, Stewart"
  (assert-true (ri-strs '("(-1 + 7*x + 2*x^2)/(-1 - x + x^2 + x^3)"
                          "(1 + 2*x)/(-1 + 3*x - 3*x^2 + x^3)"
                          "(5 - 5*x + 7*x^2 + x^3)/((-1 + x)^2*(1 + x)^3)"
                          "(1 + 3*x + 3*x^2)/(1 + 2*x + 2*x^2 + x^3)"
                          "(-1 + 2*x + x^2)/(-2*x + 3*x^2 + 2*x^3)"
                          "(1 + 4*x - 2*x^2 + x^4)/(1 - x - x^2 + x^3)"
                          "(4 - x + 2*x^2)/(4*x + x^3)"
                          "(1 + x^2 + x^3)/((-1 + x)*x*(1 + x^2)^3*(1 + x + x^2))"
                          "(1 - 3*x + 2*x^2 - x^3)/(1 + x^2)^2"
                          "(1 - 3*x + 2*x^2 - x^3)/(x*(1 + x^2)^2)"
                          "(1 - x - x^2 + x^3 + x^4)/(-x + x^3)"
                          "(2 - 4*x^2 + x^3)/((1 + x^2)*(2 + x^2))"
                          "(1 + x^2 + x^4)/((1 + x^2)*(4 + x^2)^2)"
                          "(1 + x^2 + x^3)/(2*x^2 + x^3 + x^4)"
                          "(1 - 12*x + x^2 + x^3)/(-12 + x + x^2)"
                          "(-3 + 5*x + 6*x^2)/(-3*x + 2*x^2 + x^3)"
                          "(-2 + 3*x + 5*x^2)/(2*x^2 + x^3)"
                          "(18 - 2*x - 4*x^2)/(-6 + x + 4*x^2 + x^3)"
                          "(1 + x - 2*x^2 + x^3)/(4 + 5*x^2 + x^4)"
                          "(8 - 13*x^2 - 7*x^3 + 12*x^5)/(4 - 20*x + 41*x^2 - 80*x^3 + 116*x^4 - 80*x^5 + 100*x^6)"))))

(deftest "Rubi: Thomas, North Texas, большие рациональные коэффициенты, вычеты в ℚ(√5)"
  (assert-true (ri-strs '("(9 + x^4)/(x^2*(9 + x^2))"
                          "(2*x + x^4)/(1 + x^2)"
                          "(-x + x^3)/((-1 + x)^2*(1 + x^2))"
                          "(2 + 5*x + 3*x^2 + 2*x^3)/(1 + x + x^2)"
                          "(4 + 8*x + 5*x^2 + 2*x^3)/(2 + 2*x + x^2)^2"
                          "(x - 1)^4*x^4/(1 + x^2)"
                          "(-20*x + 4*x^2)/(9 - 10*x^2 + x^4)"
                          "(-1 + x + 4*x^3)/((-1 + x)*x^2*(1 + x^2))"
                          "(1 - 3*x + 2*x^2 - 4*x^3 + x^4)/(1 + x^2)^3"
                          "(1 - 3*x + 2*x^2 - 4*x^3 + x^4)/(1 + 3*x^2 + 3*x^4 + x^6)"
                          "(1 + x + 2*x^2 + 2*x^3)/(x^2 + x^3 + x^4)"
                          "(-1 - 5*x + 2*x^2)/(2 - x - 2*x^2 + x^3)"
                          "(-32 + 5*x - 27*x^2 + 4*x^3)/(-70 - 299*x - 286*x^2 + 50*x^3 - 13*x^4 + 30*x^5)"
                          "(3 - 4*x - 5*x^2 + 3*x^3)/(x^3*(-1 + x + x^2))"))))

; ---------- параметры ----------

(deftest "параметры: 1/(x²+a²) — без декларации и при a > 0"
  (assert-true (ri-strs '("1/(x^2 + a^2)")))
  (assuming ((a positive))
    (assert-equal (integrate (math-read "1/(x^2 + a^2)") 'x) (simplify (math-read "atan(x/a)/a")))))

(deftest "параметры: несколько параметров в разных множителях"
  (assert-true (ri-strs '("1/((x - a)*(x - b))" "1/((x - a)*(x - b)*(x - c))" "x/((x + a)*(x^2 + b^2))"
                          "1/((x^2 + a)*(x^2 + b))" "(a*x + b)/(x^2 + c)^2" "1/(x^3 + a)" "1/(x^2 + a*x + b)"))))

(deftest "параметры: корни знаменателя не выражаются — сумма по корням с параметрами"
  (assert-true (ri-strs '("1/(x^4 + a)" "1/(x^5 + a*x + 1)" "x/(x^3 + a*x + b)" "1/(x^3 + sin(a))")))
  (assert-true (contains-sym? (integrate (math-read "1/(x^4 + a)") 'x) 'root-sum)))

; ---------- комплексная форма (невещественные параметры) ----------

(deftest "комплексная форма: real = #f даёт корни в радикалах с %i вместо атанов"
  (let* ((e (math-read "1/(x^2 + x + 1)"))
         (F (simplify (rat-integrate-log e 'x 't #f))))
    (assert-true (contains-sym? F '%i))
    (assert-true (not (contains-sym? F 'atan)))
    (assert-true (ri-deriv-ok? F e 'x)))
  (let* ((e (math-read "(x^3 + 2)/((x^2 + 1)*(x^2 + 2*x + 5))"))
         (F (simplify (rat-integrate-log e 'x 't #f))))
    (assert-true (ri-deriv-ok? F e 'x))
    (assert-true (not (contains-sym? F 'atan)))))

(deftest "вещественная форма: пары сопряжённых корней — атаны и логарифмы квадратичных, без %i"
  (let* ((e (math-read "(x^3 + 2)/((x^2 + 1)*(x^2 + 2*x + 5))"))
         (F (simplify (rat-integrate-log e 'x 't #t))))
    (assert-true (ri-deriv-ok? F e 'x))
    (assert-true (contains-sym? F 'atan))
    (assert-true (not (contains-sym? F '%i))))
  ; один и тот же интеграл в двух формах отличается на константу
  (let* ((e (math-read "1/(x^4 + 5*x^2 + 4)"))
         (Fr (simplify (rat-integrate-log e 'x 't #t)))
         (Fc (simplify (rat-integrate-log e 'x 't #f))))
    (assert-true (< (num-abs (list '- (list '- (replace-expr Fr 'x 0.7) (replace-expr Fc 'x 0.7))
                                   (list '- (replace-expr Fr 'x 2.9) (replace-expr Fc 'x 2.9))))
                    0.000000001))))

; кратность вычета 2: у пары сопряжённых корней Q_2 (квадратичный) S имеет степень 2 по x — цепочка LogToAtan с делением
(deftest "вещественная форма: Q_i квадратичный с i = 2 (S степени 2 по x) — атаны многочленов"
  (assert-equal (simplify (rat-integrate-log (math-read "x/(x^4 + 1)") 'x 't #t)) (simplify '(* 1/2 (atan (^ x 2)))))
  (assert-equal (simplify (rat-integrate-log (math-read "x^2/(x^6 + 1)") 'x 't #t)) (simplify '(* 1/3 (atan (^ x 3)))))
  (assert-true
   (every? (lambda (s)
             (let* ((e (math-read s)) (F (simplify (rat-integrate-log e 'x 't #t))))
               (and (ri-deriv-ok? F e 'x) (contains-sym? F 'atan) (not (contains-sym? F '%i)))))
           '("x/(x^8 + x^4 + 1)" "x^3/(x^8 + 3*x^4 + 5)" "x/(x^4 + x^2 + 1)" "x^5/(x^12 + 3*x^6 + 7)"))))

; ---------- A3′.4: башни Q(√d, √e) ----------

(deftest "A3′.4: 1/(x^4+4x^2+1) и 1/(x^4−2) — башни Q(√2,√3) и Q(⁴√2), без root-sum"
  ; 1/(x⁴+4x²+1): резольвента раскладывается над Q(√3), коэффициенты требуют √(2∓√3) — поле Q(√2,√3)
  (let ((F (ri-str "1/(x^4 + 4*x^2 + 1)")))
    (assert-true (not (contains-sym? F 'root-sum)))
    (assert-true (not (contains-sym? F '%i))))
  ; 1/(x⁴−2): Q(⁴√2) = Q(√2, √(√2)) — радикал четвёртой степени
  (let ((F (ri-str "1/(x^4 - 2)")))
    (assert-true (not (contains-sym? F 'root-sum)))
    (assert-true (contains-sym? F '^)))
  ; прежние случаи не изменились: ответ прежний и проверяется дифференцированием
  (assert-equal (integrate (math-read "1/(x^4 + 1)") 'x)
                (simplify '(+ (* 1/4 (^ 2 1/2) (atan (+ -1 (* (^ 2 1/2) x))))
                              (* 1/4 (^ 2 1/2) (atan (+ 1 (* (^ 2 1/2) x))))
                              (* -1/8 (^ 2 1/2) (log (+ 1 (^ x 2) (* -1 (^ 2 1/2) x))))
                              (* 1/8 (^ 2 1/2) (log (+ 1 (^ x 2) (* (^ 2 1/2) x)))))))
  (assert-true (ri-strs '("1/(x^6 + 1)" "1/(x^4 + 1)"))))

(deftest "A3′.4: обратный радикальный коэффициент — денестинг и сертификат"
  ; 1/(6+4√3) = −1/2 + √3/3
  (assert-equal (simplify (integrate::int-rs-rad-inv '(+ 6 (* 4 (^ 3 1/2)))))
                (simplify '(+ -1/2 (* 1/3 (^ 3 1/2)))))
  ; башня Q(√2,√3): произведение на обратное точно 1
  (let* ((D '(+ 1 (^ 2 1/2) (* 2 (^ 3 1/2)) (* 3 (^ 6 1/2))))
         (inv (integrate::int-rs-rad-inv D)))
    (assert-true inv)
    (assert-true (alg-equal? (expand (list '* D inv)) 1)))
  ; ноль и радикал четвёртой степени — отказ, а не подделка
  (assert-equal (integrate::int-rs-rad-inv 0) #f)
  (assert-equal (integrate::int-rs-rad-inv '(^ 2 1/4)) #f))

; ---------- определённые интегралы ----------

; определённый интеграл (строка, границы, число панелей квадратуры): вычислен и совпадает с квадратурой (значение может быть
; суммой по корням — комплексное число с нулевой мнимой частью, поэтому сравнение через num-abs)
(define (ri-def-ok? s lo hi n)
  (let* ((e (math-read s)) (v (integrate e 'x lo hi)) (q (ri-quad e 'x lo hi n)))
    (and (not (ri-unevaluated? v))
         (< (num-abs (list '- v q)) (* 0.000000001 (+ 1 (abs q)))))))

(deftest "определённые: корни не явны (сумма по корням) — значение совпадает с квадратурой"
  (assert-true (ri-def-ok? "1/(x^4 + 1)" 0 3 40))
  (assert-true (ri-def-ok? "1/(x^5 + 1)" 0 1 20))
  (assert-true (ri-def-ok? "1/(x^3 + 2)" -1 4 40))
  ; S квадратичен по x (кратность вычета 2): x/(x^6 − 2) на отрезке без особенностей
  (assert-equal (integrate (math-read "x/(x^6 - 2)") 'x -1 1) 0)
  (assert-true (ri-def-ok? "x/(x^6 - 2)" 0 1 20))
  (assert-true (ri-def-ok? "1/(x^6 + x^3 + 1)" -2 3 100))
  ; сертификат по значению с суммой по корням без heaviside — численно/unknown, но не падение
  ; (прежде di-rs-value брал (car hv) у пустого списка)
  (let ((e (math-read "1/(x^6 + x^3 + 1)")))
    (assert-true (member? (definite-check e 'x -2 3 (integrate e 'x -2 3)) '(numeric #t unknown)))))

(deftest "определённые: атаны (вещественная форма) и бесконечные пределы"
  (assert-equal (integrate (math-read "(x^4 - 3*x^2 + 6)/(x^6 - 5*x^4 + 5*x^2 + 4)") 'x '-inf 'inf) '(* 3 pi))
  (assert-true (ri-def-ok? "1/(x^6 + x^3 + 1)" 0 1 20))
  (assert-true (ri-def-ok? "(x^3 + 2)/((x^2 + 1)*(x^2 + 2*x + 5))" -3 6 100)))

(deftest "определённые: особенность внутри отрезка — невычисленная форма, снаружи — число"
  (assert-true (ri-unevaluated? (integrate (math-read "1/(x^3 - 2)") 'x 0 2)))
  (assert-true (ri-def-ok? "1/(x^3 - 2)" 2 5 40)))

(deftest "определённые: защита от разреза — аргумент log пересекает отрицательную полуось"
  ; u(x) = −x + t·(x − 1/2), корни Q = t² + 1: Im u = ±(x − 1/2) меняет знак при Re u < 0 на [0, 1] — разрыв
  (assert-true (not (integrate::int-rs-arg-ok? '(+ (* -1 x) (* t (+ x -1/2))) 't '(+ 1 (^ t 2)) 'x 0 1)))
  ; на [2, 3] Im u не обращается в 0
  (assert-true (integrate::int-rs-arg-ok? '(+ (* -1 x) (* t (+ x -1/2))) 't '(+ 1 (^ t 2)) 'x 2 3))
  ; коэффициент при x не зависит от t — безопасно всегда
  (assert-true (integrate::int-rs-arg-ok? '(+ x (* 3 t)) 't '(+ 1 (^ t 2)) 'x 0 5)))

; ---------- случайные знаменатели: Π f_i^k_i, случайные числители ----------

(define ri-seed 12345)
(define (ri-rand n)
  (begin (set! ri-seed (mod (+ (* ri-seed 1103515245) 12345) 2147483648))
         (mod (quotient ri-seed 65536) n)))

(define ri-factors '((+ x 1) (+ (^ x 2) x 1) (+ (^ x 2) -2) (+ x -3) (+ (^ x 3) (* -1 x) -1)
                     (+ (^ x 2) 1) (+ (^ x 4) 1) (+ (^ x 3) 2) (+ x -1/2) (+ (^ x 2) 4)))

(define (ri-random-denominator)
  (let ((picks (filter (lambda (f) (= (ri-rand 3) 0)) ri-factors)))
    (cons '* (map (lambda (f) (list '^ f (+ 1 (ri-rand 2)))) (if (null? picks) (list (car ri-factors)) picks)))))

(define (ri-random-numerator deg)
  (cons '+ (map (lambda (k) (list '* (- (ri-rand 11) 5) (list '^ 'x k))) (range (+ deg 1)))))

(deftest "случайные: Π f^k и случайные числители — производная первообразной"
  (assert-true
   (every? (lambda (k)
             (let ((e (list '/ (ri-random-numerator (ri-rand 9)) (ri-random-denominator))))
               (if (equal? (simplify (list '* e 1)) 0) #t (if (ri-chk e) #t #f))))
           (range 14))))

; ---------- INT.RS: rootsum в радикалах — двучлены t^n = ρ, кубики (Кардано, casus irreducibilis) ----------
; Оракул: |F′ − f| < 1e-9 в пяти точках; вещественность F; на сетке [−5, 5] нет скачков > 0.5 вне ±0.05 от вещественных полюсов.

(define (rsr-fv F v) (eval-num (subst (list 'x v) F)))
(define (rsr-near? v poles) (any? (lambda (p) (< (abs (- v p)) 0.05)) poles))

(define (rsr-deriv-ok? F f poles)
  (let ((dF (diff 'x F)))
    (every? (lambda (v) (or (rsr-near? v poles)
                            (< (abs (- (rsr-fv dF v) (rsr-fv f v))) 0.000000001)))
            '(-2.5 -0.7 0.3 1.1 3.7))))

(define (rsr-real? F) (every? (lambda (v) (number? (rsr-fv F v))) '(-2.5 -0.7 0.3 1.1 3.7)))

(define (rsr-max-step F poles)
  (let loop ((i 0) (prev #f) (m 0))
    (if (> i 100) m
        (let ((v (- (* i 0.1) 5)))
          (if (rsr-near? v poles) (loop (+ i 1) #f m)
              (let ((c (rsr-fv F v)))
                (loop (+ i 1) c (if (and prev (number? c) (number? prev)) (max m (abs (- c prev))) m))))))))

(define rsr-cases
  ; (подынтегральная  вещественные полюса  вещественность проверять?)
  (list (list '(/ 1 (+ (^ x 3) 2)) '(-1.2599210498948732) #t)
        (list '(/ x (- (^ x 3) 3)) '(1.4422495703074083) #t)
        (list '(/ 1 (- (^ x 5) 2)) '(1.148698354997035) #t)
        (list '(/ 1 (+ (^ x 6) 2)) '() #t)
        (list '(/ 1 (+ (^ x 3) (* -3 x) 1)) '(-1.8793852415718169 0.3472963553338607 1.532088886237956) #t)
        (list '(/ (+ x 1) (+ (^ x 3) 2)) '(-1.2599210498948732) #t)
        (list '(/ 1 (+ (* 2 (^ x 3)) 3)) '(-1.1447142425533878) #t)
        (list '(/ x (- (^ x 3) 2)) '(1.2599210498948732) #t)
        (list '(/ 1 (* (+ (^ x 3) 2) (+ (^ x 2) 1))) '(-1.2599210498948732) #t)
        ; линейный множитель резольвенты даёт log без модуля (прежнее соглашение) — вещественность не требуем
        (list '(/ 1 (+ (^ x 5) 1)) '(-1) #f)
        (list '(/ 1 (- (^ x 3) 1)) '(1) #f)
        (list '(/ 1 (- (^ x 6) 1)) '(-1 1) #f)
        (list '(/ (^ x 2) (+ (^ x 3) 1)) '(-1) #f)))

(deftest "INT.RS: rootsum раскрыт в радикалах — без root-sum и %i, производная = подынтегральная, ответ вещественный"
  (assert-true
   (every? (lambda (c)
             (let ((F (integrate (car c) 'x)))
               (and (not (contains-sym? F 'root-sum))
                    (not (contains-sym? F '%i))
                    (rsr-deriv-ok? F (car c) (nth c 1))
                    (or (not (nth c 2)) (rsr-real? F)))))
           rsr-cases)))

(deftest "INT.RS: неизвестные углы (n = 7, 9) и прежние ответы — rootsum остаётся / ответ не меняется"
  (assert-true (contains-sym? (integrate '(/ 1 (+ (^ x 7) 2)) 'x) 'root-sum))
  (assert-true (contains-sym? (integrate '(/ 1 (+ (^ x 9) 2)) 'x) 'root-sum))
  ; кубика с одним вещественным корнем: запись Кардано > int-rs-radical-max узлов (750…2000) — rootsum остаётся
  (assert-true (contains-sym? (integrate '(/ 1 (+ (^ x 3) x 1)) 'x) 'root-sum))
  ; и сама функция раскрытия честно возвращает #f (а не огромное выражение) для x/(x³+x+1)
  (assert-true (let ((r (integrate::int-rs-expand-radical '(root-sum t (+ 1 t (* 31 (^ t 3)))
                                                           (* t (log (+ x (* (+ (* -1 t) (* 9 (^ t 2))) (^ (+ 1 (* 6 (^ t 2))) -1)))))))))
                 (not r)))
  (assert-true (not (contains-sym? (integrate '(/ 1 (+ (^ x 4) 1)) 'x) 'root-sum)))
  (assert-true (contains-sym? (integrate '(/ 1 (+ (^ x 4) 1)) 'x) 'atan))
  (assert-true (rsr-real? (integrate '(/ 1 (+ (^ x 4) 1)) 'x)))
  (assert-true (rsr-real? (integrate '(/ 1 (+ (^ x 2) 1)) 'x))))

; (в тесте шаг сетки 0.1 ради времени; на шаге 0.01 по всем примерам скачков > 0.5 тоже нет — замер при разработке)
(deftest "INT.RS: непрерывность на сетке [−5, 5] — нет скачков atan вне полюсов"
  (assert-true
   (every? (lambda (c)
             (< (rsr-max-step (integrate (car c) 'x) (nth c 1)) 0.5))
           (list (car rsr-cases) (nth rsr-cases 1) (nth rsr-cases 3) (nth rsr-cases 4) (nth rsr-cases 5)))))
