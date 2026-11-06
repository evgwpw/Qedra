; genus0.lisp — тесты шага A3′.2: интегралы на кривых рода 0.

(define (g0-ok? e)
  (let ((ans (integrate e 'x)))
    (and (not (and (pair? ans) (equal? (car ans) 'integrate)))
         (integrate::gn-ok? ans e 'x))))

(deftest "genus0: шесть примеров задания"
  (assert-true (g0-ok? '(/ 1 (* x (^ (* (^ x 2) (+ x 1)) 1/3)))))
  (assert-true (g0-ok? '(^ (* (^ x 2) (+ x 1)) 1/2)))
  (assert-true (g0-ok? '(/ 1 (^ (+ (^ x 3) (^ x 2)) 1/3))))
  (assert-true (g0-ok? '(* x (^ (* (^ x 2) (+ x 1)) 1/2))))
  (assert-true (g0-ok? '(/ 1 (* (- x 1) (^ (* (^ x 2) (+ x 1)) 1/2)))))
  (assert-true (g0-ok? '(/ 1 (^ (* (^ (- x 1) 2) (+ x 1)) 1/3)))))

(deftest "genus0: узловая и касповая кубики"
  (assert-true (g0-ok? '(/ 1 (^ (- (^ x 3) (^ x 2)) 1/2))))
  (assert-true (g0-ok? '(/ 1 (^ (^ x 3) 1/2)))))

(deftest "genus0: род 1 и 2 — стратегия отказывается, без ложного ответа"
  (assert-equal #f (integrate::int-genus0 '(/ 1 (^ (+ (^ x 6) 1) 1/2)) 'x 0))
  (assert-equal #f (integrate::int-genus0 '(/ 1 (^ (+ (^ x 3) x 1) 1/2)) 'x 0)))

(deftest "genus0: обратное отображение и подделка"
  (let* ((F '(- (^ y 3) (* (^ x 2) (+ x 1))))
         (par (parametrize-curve F 'x 'y 't))
         (inv (parametrize-curve-inverse F 'x 'y 't par)))
    (assert-true (parametrization-inverse-check F 'x 'y par inv 't))
    ; неверная база пучка — сертификат отвергает
    (assert-equal #f (parametrization-inverse-check F 'x 'y par '(/ y (- x 1)) 't))))

(deftest "genus0: подделка ветви радикала отвергается"
  (let* ((e '(/ 1 (* x (^ (* (^ x 2) (+ x 1)) 1/3))))
         (ans (integrate e 'x)))
    (assert-true (integrate::gn-ok? ans e 'x))
    ; ответ с противоположным знаком радикала — не производная подынтегрального
    (assert-equal #f (integrate::gn-ok? (list '- ans) e 'x))))

(deftest "genus0: обратное отображение гладкой коники"
  (let* ((F '(- (+ (^ x 2) (^ y 2)) 1))
         (p (parametrize-curve F 'x 'y 't))
         (i (parametrize-curve-inverse F 'x 'y 't p)))
    (assert-true (parametrization-inverse-check F 'x 'y p i 't))))

(deftest "genus0: общий inverse адъюнктной кривой (лемниската)"
  (let* ((F '(- (^ (+ (^ x 2) (^ y 2)) 2) (+ (^ x 2) (* -1 (^ y 2)))))
         (p (parametrize-curve F 'x 'y 't))
         (i (parametrize-curve-inverse F 'x 'y 't p)))
    (assert-true (not (equal? i 'unknown)))
    (assert-true (parametrization-inverse-check F 'x 'y p i 't))))

(deftest "genus0: переключение ветви −y(t) для чётного q"
  (assert-equal 'principal (integrate::gn-branch-mode 'x 2 '(^ t 2) 't 'y 'x))
  (assert-equal 'flip (integrate::gn-branch-mode 'x 2 '(^ t 2) '(- t) 'y 'x)))

(deftest "genus0: корень из единицы для нечётного q"
  (let ((w '(exp (/ (* 2 %i pi) 3))))
    (assert-equal '(root 2)
                  (integrate::gn-branch-mode 'x 3 '(^ t 3) (list '* 't w) 'y 'x))))

; G0.FAST: log/exp/trig от x — не алгебраика, genus0 и алгебраическая стратегия отказывают сразу (раньше 6 с бюджета)
(deftest "genus0: неалгебраическое подынтегральное — быстрый отказ"
  (let ((e '(/ (^ (+ a (* b (log (* c (^ (+ d (* e1 (^ x 1/2))) n))))) 2) (^ x 3))))
    (assert-true (not (integrate::int-algebraic-in? e 'x)))
    (assert-true (integrate::int-algebraic-in? '(/ 1 (* x (^ (* (^ x 2) (+ x 1)) 1/3))) 'x))
    (assert-true (not (integrate::int-algebraic-in? '(^ (+ x 1) n) 'x)))
    (let ((r (call-with-time-limit 1 (lambda () (integrate::int-genus0 e 'x 0)))))
      (assert-equal '(ok #f) r))
    (let ((r (call-with-time-limit 1 (lambda () (integrate::alg-int-strategy e 'x 0)))))
      (assert-equal '(ok #f) r))))
