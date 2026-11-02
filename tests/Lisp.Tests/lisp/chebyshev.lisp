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

(deftest "a3p1: неэлементарные — доказанный отказ, не выдуманный ответ"
  (let ((F (integrate '(^ (+ 1 (^ x 3)) 1/2) 'x)))
    (assert-true (equal? (car F) 'integrate)))
  (let ((F (integrate '(^ (+ 1 (^ x 4)) -1/2) 'x)))
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

(deftest "a3p5: пропуски Чебышёва — отрицательные m, дробные n"
  ; 1/(x√(1+x³)), √x(1+√x)^{1/3}, x^{−1/2}(1+x^{1/4})^{1/3} — элементарны
  (map (lambda (e)
         (let ((F (integrate e 'x)))
           (assert-true (a3p1-free? F))
           (assert-true (integrate::int-cheb-num-check F e 'x))))
       (list '(/ 1 (* x (^ (+ 1 (^ x 3)) 1/2)))
             '(* (^ x 1/2) (^ (+ 1 (^ x 1/2)) 1/3))
             '(* (^ x -1/2) (^ (+ 1 (^ x 1/4)) 1/3)))))
