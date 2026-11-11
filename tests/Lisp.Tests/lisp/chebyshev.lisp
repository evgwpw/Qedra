; chebyshev.lisp — тесты шага A3′.1: теорема Чебышёва о биномиальном дифференциале.

(define (a3p1-free? F)
  (not (and (pair? F) (equal? (car F) 'integrate))))

(deftest "a3p1: элементарные случаи — ответ есть и проверяется дифференцированием"
  ; p ∈ ℤ: ∫ x³√(1+x²) (степень p = 1/2 — на самом деле случай (m+1)/n)
  (map (lambda (e)
         (let ((F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (int-check F e 'x))))
       (list '(* (^ x 3) (^ (+ 1 (^ x 2)) 1/2))
             '(* x (^ (+ 1 (^ x 4)) -1/2))
             '(* (^ x -2) (^ (+ 1 (^ x 2)) -1/2))))
  ; p ∈ ℤ: ∫ x²(1+x²) dx
  (let ((F (integrate '(* (^ x 2) (+ 1 (^ x 2))) 'x)))
    (assert-true (a3p1-free? F))
    (assert-true (int-check F '(* (^ x 2) (+ 1 (^ x 2))) 'x))))

(deftest "a3p1: критерий Чебышёва считается точно"
  ; √(1+x³): p=1/2, (m+1)/n=1/3, +p=5/6 — все три не целые
  (assert-equal (int-cheb-form '(^ (+ 1 (^ x 3)) 1/2) 'x) '(0 3 1/2 1 1 1))
  (assert-equal (int-cheb-elementary? 0 3 1/2) #f)
  ; 1/√(1+x⁴): то же
  (assert-equal (int-cheb-elementary? 0 4 -1/2) #f)
  ; x/√(1+x⁴): (m+1)/n + p = 1/2 − 1/2 = 0 — целое
  (assert-true (int-cheb-elementary? 1 4 -1/2))
  ; x³√(1+x²): (m+1)/n = 2 — целое
  (assert-true (int-cheb-elementary? 3 2 1/2)))

; RUBI.6.5: после доказанной неэлементарности integrate зовёт Rubi (ответ через спецфункции); здесь проверяется само
; доказательство — Rubi после него отключён
(define (ch-no-rubi thunk)
  (let ((old integrate::int-rubi-on-nonelementary))
    (set! integrate::int-rubi-on-nonelementary #f)
    (unwind-protect (thunk) (set! integrate::int-rubi-on-nonelementary old))))

(deftest "a3p1: неэлементарные — доказанный отказ, не выдуманный ответ"
  (let ((F (ch-no-rubi (lambda () (integrate '(^ (+ 1 (^ x 3)) 1/2) 'x)))))
    (assert-true (equal? (car F) 'integrate)))
  (let ((F (ch-no-rubi (lambda () (integrate '(^ (+ 1 (^ x 4)) -1/2) 'x)))))
    (assert-true (equal? (car F) 'integrate))))

(deftest "a3p1: ложного отказа нет — случаи «да» дают проверенный ответ"
  ; перебор нескольких форм, где критерий «да»
  (map (lambda (e)
         (let ((F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (int-check F e 'x))))
       (list '(* (^ x 3) (^ (+ 1 (^ x 2)) 1/2))
             '(* x (^ (+ 1 (^ x 4)) -1/2))
             '(* (^ x -2) (^ (+ 1 (^ x 2)) -1/2))
             '(* (^ x 2) (+ 1 (^ x 2))))))

; ---------- шаг INT.CH: R(x^n), нераскрытый радикал, оракул F' = f ----------

(define ch2-pts-all '(-17/10 -3/5 2/5 9/10 23/10))
(define ch2-pts-pos '(2/5 9/10 8/5 23/10))

; невязка |F' - f| / (1 + |f|) < 1e-8 в точках (комплексные значения главной ветви — через модуль)
(define (ch2-oracle? F e pts)
  (equal? (integrate::int-numeric-status-at (list '- (diff 'x F) e) e 'x 0.00000001 pts) 'ok))

(define (ch2-ne? f)
  (conditions-clear)
  (let ((r (ch-no-rubi (lambda () (integrate f 'x)))))
    (and (pair? r) (equal? (car r) 'integrate)
         (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary))) (conditions)))))

(deftest "int.ch: целевой пример — три случая Чебышёва с радикалом (x^3+x)^(1/3) и R(x^2), два набора параметров"
  (map (lambda (s)
         (let* ((e (math-eval s)) (F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (ch2-oracle? F e ch2-pts-pos))))
       (list "(2*x^6+3)/(x^3+x)^(1/3)/(5*x^6+7)"
             "(x^6-2)/(x^3+x)^(1/3)/(3*x^6+1)")))

(deftest "int.ch: символьные параметры a, b, c, d — ответ с rootsum, оракул при пробных значениях"
  (let* ((e (math-eval "(a*x^6+b)/(x^3+x)^(1/3)/(c*x^6+d)")) (F (integrate e 'x)))
    (assert-true (a3p1-free? F))
    (assert-true (ch2-oracle? F e ch2-pts-pos))))

(deftest "int.ch: классика по случаям (оракул на x < 0 и x > 0, где ответ верен на всей оси)"
  (map (lambda (s)
         (let* ((e (math-eval s)) (F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (ch2-oracle? F e ch2-pts-all))))
       (list "x^(1/2)*(1+x^(1/3))^2" "x^(-2/3)/(1+x^(1/3))"
             "x^3*(1+x^2)^(1/2)" "x^5*(1-x^3)^(1/3)" "x*(2+x^2)^(-1/3)"
             "x^(-3)*(1+x^4)^(-1/2)" "(x^4+x)^(1/2)")))

(deftest "int.ch: третий случай x^(-4)(1+x^2)^(-1/2), dx/(x^2(1+x^2)^(3/2)), (x^3+x)^(-1/3) — верны при x > 0"
  (map (lambda (s)
         (let* ((e (math-eval s)) (F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (ch2-oracle? F e ch2-pts-pos))))
       (list "x^(-4)*(1+x^2)^(-1/2)" "1/(x^2*(1+x^2)^(3/2))" "(x^3+x)^(-1/3)" "(x^2+3)/(x^3+x)^(1/3)")))

(deftest "int.ch: условие x > 0 записывается, когда ответ верен только при x > 0"
  (conditions-clear)
  (integrate (math-eval "(x^3+x)^(-1/3)") 'x)
  (assert-true (any? (lambda (c) (equal? (car c) '(> x 0))) (conditions))))

(deftest "int.ch: подделки — доказанная неэлементарность по Чебышёву (только R = 1 и числа α, β)"
  (map (lambda (s) (assert-true (ch2-ne? (math-eval s))))
       (list "(1+x^3)^(1/2)" "x^(1/2)*(1+x)^(1/3)" "(1+x^4)^(1/2)" "(x^3+x)^(1/2)" "(x^5+x^3)^(1/2)"
             "x^(-2)*(1+x^4)^(-1/4)")))

(deftest "int.ch: с множителем R(x^n) без случая Чебышёва — не NE и не ложная формула"
  (conditions-clear)
  (let ((r (integrate (math-eval "x/(x^2+1)/(x^3+x)^(1/3)") 'x)))
    (assert-true (or (not (a3p1-free? r)) (ch2-oracle? r (math-eval "x/(x^2+1)/(x^3+x)^(1/3)") ch2-pts-pos)))
    ; доказательств NE для вложенных форм (побочные подзадачи каскада) не касаемся — только для верхней формы
    (assert-true (not (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary)
                                             (equal? (cadr (car c)) r)))
                            (conditions))))))

(deftest "a3p5: пропуски Чебышёва — отрицательные m, дробные n"
  ; 1/(x√(1+x³)), √x(1+√x)^{1/3}, x^{−1/2}(1+x^{1/4})^{1/3} — элементарны
  (map (lambda (e)
         (let ((F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (integrate::int-cheb-num-check F e 'x))))
       (list '(/ 1 (* x (^ (+ 1 (^ x 3)) 1/2)))
             '(* (^ x 1/2) (^ (+ 1 (^ x 1/2)) 1/3))
             '(* (^ x -1/2) (^ (+ 1 (^ x 1/4)) 1/3)))))
