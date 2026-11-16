; Шаг INT.GAPS.4: интегралы с двумя разными квадратными радикалами √(a+bx²), √(c+dx²).
; Нечётное x·R(x²,√P₁,√P₂): t = x², u = √P₁ — один квадратный радикал по u (int-two-rad-odd, parts.lisp).
; Остаток «по частям» ∫ log(x+√(x²+c))/(x²+d)^(3/2): du = 1/√(x²+c) (int-rad-normalize), v·du — два радикала.

(define (tr-d e x0) (eval-num (replace-expr e 'x x0)))

(define (tr-ok-at? F e x0)
  (let ((a (tr-d (integrate::int-diff 'x F) x0)) (b (tr-d e x0)))
    (if (and (real-numeric? a) (real-numeric? b))
        (< (abs (- a b)) 0.000001)
        #f)))

(define (tr-taken? e) (let ((F (integrate e 'x))) (not (and (pair? F) (equal? (car F) 'integrate)))))

; ответ взят и верен в точках по обе стороны нуля
(define (tr-good? e)
  (let ((F (integrate e 'x)))
    (and (not (and (pair? F) (equal? (car F) 'integrate)))
         (every? (lambda (p) (tr-ok-at? F e p)) '(-7/5 -3/10 3/10 7/10 3)))))

(deftest "two-rad: x/(sqrt(x^2+1)*sqrt(x^2+2)), x/(sqrt(x^2+1)*sqrt(x^2+4)) - один радикал после подстановки"
  (assert-true (tr-good? '(/ x (* (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 2))))))
  (assert-true (tr-good? '(/ x (* (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 4)))))))

(deftest "two-rad: 1/(x*sqrt(x^2+1)*sqrt(x^2+4)), x^3/(sqrt*sqrt), x*sqrt(x^2+1)/sqrt(x^2+3)"
  (for-each (lambda (e) (assert-true (tr-good? e)))
            '((/ 1 (* x (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 4))))
              (/ (^ x 3) (* (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 2))))
              (/ (* x (sqrt (+ (^ x 2) 1))) (sqrt (+ (^ x 2) 3))))))

(deftest "two-rad: log(x+sqrt(x^2+c))/(x^2+d)^(3/2) при c != d - по частям, du = 1/sqrt(x^2+c)"
  (for-each (lambda (e) (assert-true (tr-good? e)))
            '((/ (log (+ x (sqrt (+ (^ x 2) 2)))) (^ (+ (^ x 2) 1) 3/2))
              (/ (log (+ x (sqrt (+ (^ x 2) 5)))) (^ (+ (^ x 2) 1) 3/2))
              (/ (log (+ x (sqrt (+ (^ x 2) 1)))) (^ (+ (^ x 2) 3) 3/2))
              (/ (log (+ x (sqrt (+ (^ x 2) 1)))) (^ (+ (^ x 2) 6) 3/2)))))

(deftest "two-rad: x*log(x+sqrt(x^2+c))/(x^2+d)^(3/2) - остаток эллиптический, ответ берётся"
  (assert-true (tr-taken? '(/ (* x (log (+ x (sqrt (+ (^ x 2) 3))))) (^ (+ (^ x 2) 1) 3/2))))
  (assert-true (tr-taken? '(/ (* x (log (+ x (sqrt (+ (^ x 2) 5))))) (^ (+ (^ x 2) 1) 3/2)))))

(deftest "two-rad: du = d/dx log(x+sqrt(x^2+c)) приводится к 1/sqrt(x^2+c)"
  (assert-equal (integrate::int-rad-normalize (integrate::int-diff 'x '(log (+ x (sqrt (+ 2 (^ x 2)))))) 'x)
                '(^ (+ 2 (^ x 2)) -1/2))
  ; два радикала не трогаются
  (let ((e '(* x (^ (+ 1 (^ x 2)) -1/2) (^ (+ 2 (^ x 2)) -1/2))))
    (assert-equal (integrate::int-rad-normalize e 'x) e)))

(deftest "two-rad: чётное 1/(sqrt*sqrt) (эллиптика) не берётся подстановкой: ответ без ложной элементарной формы"
  (let ((F (integrate '(/ 1 (* (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 2)))) 'x)))
    (assert-true (or (and (pair? F) (equal? (car F) 'integrate))
                     (tr-ok-at? F '(/ 1 (* (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 2)))) 3/10)))))

(deftest "two-rad: подделка - неверный F отвергается int-check и численной проверкой"
  (let ((e '(/ x (* (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 2)))))
        (bad '(log (+ (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 3))))))
    (assert-true (not (int-check bad e 'x)))
    (assert-true (not (integrate::int-F-numeric-ok? bad e 'x)))
    (assert-true (integrate::int-F-numeric-ok? '(log (+ (sqrt (+ (^ x 2) 1)) (sqrt (+ (^ x 2) 2)))) e 'x))))
