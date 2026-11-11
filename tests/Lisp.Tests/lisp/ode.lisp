; ode.lisp — тесты шага ODE.0: каркас, квадратуры, сертификат, подделки.

; уравнение решено и сертификат точный
(define (ode-t-ok? eq)
  (let ((r (dsolve eq '(y x))))
    (and (equal? (ode-status r) 'ok)
         (pair? (ode-solutions r))
         (equal? (dsolve-check eq (car (ode-solutions r)) '(y x)) #t))))

(deftest "ODE.0: двадцать квадратур — решение проходит dsolve-check"
  (map (lambda (eq) (assert-true (ode-t-ok? eq)))
       (list '(= (diff (y x) x) (^ x 2))
             '(= (diff (y x) x) (cos x))
             '(= (diff (y x) x) (sin x))
             '(= (diff (y x) x) (exp x))
             '(= (diff (y x) x) (/ 1 x))
             '(= (diff (y x) x) (/ 1 (+ 1 (^ x 2))))
             '(= (diff (y x) x) (/ x (+ 1 (^ x 2))))
             '(= (diff (y x) x) (/ 1 (sqrt (- 1 (^ x 2)))))
             '(= (diff (y x) x) (sinh x))
             '(= (diff (y x) x) (cosh x))
             '(= (diff (y x) x) (^ x 3))
             '(= (diff (y x) x) (+ (* 2 x) 3))
             '(= (diff (diff (y x) x) x) (* 6 x))
             '(= (diff (diff (y x) x) x) (exp x))
             '(= (diff (diff (y x) x) x) (sin x))
             '(= (diff (diff (y x) x) x) 2)
             '(= (diff (diff (y x) x) x) 0)
             '(= (diff (diff (diff (y x) x) x) x) 6)
             '(= (diff (y x) x) 0)
             '(= (diff (diff (y x) x) x) (/ 1 (^ x 2))))))

(deftest "ODE.0: объект решения и константы"
  (let ((r (dsolve '(= (diff (diff (y x) x) x) (exp x)) '(y x))))
    (assert-equal (ode-status r) 'ok)
    (assert-equal (length (ode-solutions r)) 1)
    (assert-equal (cadr r) :type)
    (assert-equal (any? (lambda (m) (equal? m (ode::ode-field r :method)))
                        '(variation quadrature undetermined)) #t)
    (assert-equal (ode::ode-field r :check) #t)
    (assert-equal (length (ode::ode-field r :constants)) 2))
  ; без производных — не ОДУ
  (assert-equal (ode-status (dsolve '(= y 1) '(y x))) 'unknown))

(deftest "ODE.0: десять подделок отвергаются"
  (let ((bad (list
              (list '(= (diff (y x) x) (^ x 2)) '(= (y x) (+ C1 (/ (^ x 3) 2))))
              (list '(= (diff (y x) x) (cos x)) '(= (y x) (+ C1 (cos x))))
              (list '(= (diff (y x) x) (cos x)) '(= (y x) (+ C1 (* -1 (sin x)))))
              (list '(= (diff (y x) x) (exp x)) '(= (y x) (+ C1 (exp x) x)))
              (list '(= (diff (y x) x) (/ 1 x)) '(= (y x) (+ C1 (log (+ x 1)))))
              (list '(= (diff (y x) x) (/ 1 (+ 1 (^ x 2)))) '(= (y x) (+ C1 (atan (^ x 2)))))
              (list '(= (diff (y x) x) (sin x)) '(= (y x) (+ C1 (cos x))))
              (list '(= (diff (y x) x) (/ 1 (sqrt (- 1 (^ x 2))))) '(= (y x) (+ C1 (asin (^ x 2)))))
              (list '(= (diff (diff (y x) x) x) (* 6 x)) '(= (y x) (+ C1 (^ x 2))))
              (list '(= (diff (diff (y x) x) x) (exp x)) '(= (y x) (+ C1 (exp x) (^ x 2)))))))
    (map (lambda (p) (assert-equal (dsolve-check (car p) (cadr p) '(y x)) #f)) bad))
  ; y = erf(x) не решает y′ = 0 (численная проверка возвращает #f)
  (assert-equal (dsolve-check '(= (diff (y x) x) 0) '(= (y x) (erf x)) '(y x)) #f))

(deftest "ODE.0: ode-subst вычисляет производные после подстановки"
  (assert-equal (ode-subst '(diff (diff (y x) x) x) '(y x) '(^ x 3)) '(* 6 x))
  (assert-equal (ode-subst '(diff (y x) x) '(y x) '(sin x)) '(cos x))
  (assert-equal (ode-subst '(diff (y x) x) '(y x) '(+ (^ x 3) C1)) '(* 3 (^ x 2))))

(deftest "ODE.0: классификатор — порядок, линейность, коэффициенты, автономность"
  (assert-equal (ode-order '(= (diff (y x) x) x) 'y 'x) 1)
  (assert-equal (ode-order '(= (diff (diff (y x) x) x) x) 'y 'x) 2)
  (assert-equal (ode-order '(= (diff (diff (diff (y x) x) x) x) 6) 'y 'x) 3)
  (assert-true (ode-linear? '(= (diff (diff (y x) x) x) (+ (* -1 (y x)) x)) '(y x)))
  (assert-equal (ode-linear? '(= (^ (diff (y x) x) 2) 1) '(y x)) #f)
  (assert-true (ode-const-coeff? '(= (+ (diff (diff (y x) x) x) (* 3 (diff (y x) x)) (* 2 (y x))) 0) '(y x)))
  (assert-equal (ode-const-coeff? '(= (+ (diff (y x) x) (* x (y x))) 0) '(y x)) #f)
  (assert-true (ode-autonomous? '(= (+ (diff (diff (y x) x) x) (y x)) 0) '(y x)))
  (assert-equal (ode-autonomous? '(= (diff (y x) x) x) '(y x)) #f))

(deftest "ODE.0: вне квадратур — честный unknown, не ложное решение"
  (let ((r (dsolve '(= (diff (y x) x) (+ (^ x 2) (^ (y x) 2))) '(y x))))
    (assert-equal (ode-status r) 'unknown)
    (assert-equal (ode-solutions r) '())))

; замечание ревью: крошечная точная ошибка решения не проходит ни как «точно», ни как «численно»
(deftest "ode/ODE.0: dsolve-check отвергает решение с ошибкой 1e-12 (точный ненулевой остаток)"
  (assert-equal #f (dsolve-check '(= (diff (y x) x) (* 2 x)) '(= (y x) (+ (^ x 2) (* 1/1000000000000 (sin x)))) '(y x)))
  (assert-equal #f (dsolve-check '(= (diff (y x) x) (* 2 x)) '(= (y x) (+ (^ x 2) (* 1/10000000000000 x))) '(y x))))

; DIFF.BR2: √(1−x)√(1+x)=√(1−x²) (сумма — константа 2) даёт точный сертификат; для (x−1),(x+1) (оба <0 при x<−1) — нет
(deftest "ode/DIFF.BR2: свёртка произведения корней только при положительной сумме подкоренных"
  (assert-equal #t (dsolve-check (quote (= (diff (y x) x) (/ 1 (sqrt (- 1 (^ x 2)))))) (quote (= (y x) (+ C1 (asin x)))) (quote (y x))))
  (assert-equal #t (dsolve-check (quote (= (diff (y x) x) (/ -1 (sqrt (- 1 (^ x 2)))))) (quote (= (y x) (+ C1 (acos x)))) (quote (y x))))
  (assert-equal (quote numeric) (dsolve-check (quote (= (diff (y x) x) (/ 1 (sqrt (- (^ x 2) 1))))) (quote (= (y x) (+ C1 (acosh x)))) (quote (y x))))
  (assert-equal #f (dsolve-check (quote (= (diff (y x) x) (/ -1 (sqrt (- 1 (^ x 2)))))) (quote (= (y x) (+ C1 (asin x)))) (quote (y x)))))
