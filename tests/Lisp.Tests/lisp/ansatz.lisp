; INT.ANSATZ.1: интегрирование анзацем (lib/integrate/ansatz.lisp) — ответ ищется как многочлен от кирпичиков
; подынтегрального с неизвестными коэффициентами; каждый ответ проходит int-check; нет решения — #f.

(define (az-solved f)
  (let ((F (int-ansatz f 'x)))
    (assert-true F)
    (assert-true (int-check F f 'x))
    F))

(deftest "ansatz: x·eˣ, x²·log x, x·e^(x²) — многочлен от кирпичиков"
  (az-solved '(* x (exp x)))
  (az-solved '(* (^ x 2) (log x)))
  (assert-equal (az-solved '(* x (exp (^ x 2)))) '(* 1/2 (exp (^ x 2)))))

(deftest "ansatz: (1+2x²)·e^(x²) = x·e^(x²)"
  (assert-equal (az-solved '(* (+ 1 (* 2 (^ x 2))) (exp (^ x 2)))) '(* x (exp (^ x 2)))))

(deftest "ansatz: eˣ·sin x и e^(2x)·cos x — синус и косинус как кирпичики на окружности"
  (az-solved '(* (exp x) (sin x)))
  (az-solved '(* (exp (* 2 x)) (cos x))))

(deftest "ansatz: логарифмическая часть — 1/(x log x) = log log x, e^x/(e^(2x)-1)"
  (assert-equal (az-solved '(/ 1 (* x (log x)))) '(log (log x)))
  (az-solved '(/ (exp x) (+ (exp (* 2 x)) -1))))

(deftest "ansatz: спецфункции — erf x и atan x"
  (let ((F (az-solved '(erf x))))
    (assert-true (contains-sym? F 'erf)))
  (az-solved '(atan x))
  (az-solved '(* x (atan x))))

(deftest "ansatz: корень √(x+1)·x"
  (az-solved '(* x (^ (+ x 1) 1/2))))

(deftest "ansatz: параметр — x·e^(ax) = (x/a − 1/a²)·e^(ax)"
  (az-solved '(* x (exp (* a x)))))

(deftest "ansatz: неэлементарные интегралы — честный отказ #f"
  (for-each (lambda (f) (assert-equal (int-ansatz f 'x 2) #f))
            '((/ (exp x) x) (exp (^ x 2)) (/ (sin x) x) (/ 1 (log x)) (/ (log x) (+ 1 x)))))

(deftest "ansatz: весовой фильтр сокращает число неизвестных (параметры — вес из однородности f)"
  (az-solved '(* x (exp (* a x))))
  (let ((st (car (int-ansatz-stats))))
    ; (d без-фильтра с-фильтром фильтр-включён?)
    (assert-true (nth st 3))
    (assert-true (< (* 3 (nth st 2)) (nth st 1)))))

(deftest "ansatz: подделка отвергается int-check (ответ с неверной производной не возвращается)"
  (int-ansatz '(* x (exp x)) 'x)
  ; одно неизвестное x·eˣ с коэффициентом 1: F′ = (x+1)·eˣ ≠ x·eˣ
  (assert-equal (integrate::an-assemble '(* x (exp x)) '(* x (exp x)) '((mono 1 (1) () 0)) '(1) '() '()) #f)
  (assert-equal (int-check '(* x (exp x)) '(* x (exp x)) 'x) #f))

(deftest "ansatz: без бюджета на большие системы и без поддержки — #f, не ошибка"
  ; показатель с x, функция от параметров, комплексная единица
  (assert-equal (int-ansatz '(^ 2 x) 'x) #f)
  (assert-equal (int-ansatz '(^ x (* n x)) 'x) #f)
  (assert-equal (int-ansatz '(exp a) 'x) #f)
  (assert-equal (int-ansatz '(* %i x) 'x) #f))

(deftest "ansatz: without-ansatz отключает ступень и восстанавливает флаг"
  (without-ansatz (lambda () (assert-true (list? (integrate '(* x (exp x)) 'x)))))
  (assert-true (int-ansatz '(* x (exp x)) 'x)))

; INT.ANSATZ.2: символьный показатель (кирпичик θ = u^(q·n), θ′ = q·n·u′·θ/u; в коэффициентах знаменатели (q·n+k+j))
(deftest "ansatz: xⁿ, (a+bx)ⁿ, x^(2n+1) — первообразная с множителем 1/(n+1)"
  (assert-equal (az-solved '(^ x n)) '(* (^ x (+ 1 n)) (^ (+ 1 n) -1)))
  (az-solved '(^ (+ a (* b x)) n))
  (az-solved '(* x (^ (+ a (* b x)) n)))
  (az-solved '(^ x (+ 1 (* 2 n))))
  (az-solved '(^ (+ a (* b x)) (+ n -3))))

(deftest "ansatz: x^(n-1)·(1+xⁿ)² = (1+xⁿ)³/(3n); xⁿ·log x — знаменатель (n+1)²"
  (az-solved '(* (^ x (+ n -1)) (^ (+ 1 (^ x n)) 2)))
  (az-solved '(* (^ x n) (log x))))

(deftest "ansatz: условие n ≠ -1 записывается в канал условий"
  (let ((r (capture-conditions (lambda () (int-ansatz '(^ x n) 'x)))))
    (assert-true (car r))
    (assert-true (assoc '(/= (+ 1 n) 0) (cadr r)))))

(deftest "ansatz: неэлементарное с символьным показателем — #f (xⁿ·eˣ — неполная гамма)"
  (assert-equal (int-ansatz '(* (^ x n) (exp x)) 'x 2) #f)
  (assert-equal (int-ansatz '(/ (^ x n) (+ 1 x)) 'x 2) #f))

(deftest "ansatz: подъём констант — (lift …) в статистике, ответ проверен; по умолчанию выключен"
  (assert-equal (int-ansatz '(/ 1 (+ (^ x 4) 1)) 'x 2 3) #f)
  (assert-true (not (any? (lambda (s) (and (pair? s) (equal? (car s) 'lift))) (int-ansatz-stats))))
  (int-ansatz '(/ 1 (+ (^ x 4) 1)) 'x 2 3 #t)
  (assert-true (any? (lambda (s) (and (pair? s) (equal? (car s) 'lift))) (int-ansatz-stats)))
  (let ((F (int-ansatz '(* (exp x) (sin x)) 'x 3 3 #t)))
    (assert-true (int-check F '(* (exp x) (sin x)) 'x))))
