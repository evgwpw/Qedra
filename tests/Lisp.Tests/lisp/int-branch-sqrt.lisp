; Шаг INT.BR: ответы integrate для x^n·√(a−b·x²) и родственных верны по обе стороны нуля (раньше подстановка
; t = √(x⁻²−1) давала ответ лишь при x > 0, хотя √(1−x²) определён на (−1, 0)); int-check проверяет и при x < 0.

(define (ib-d e x0) (eval-num (replace-expr e 'x x0)))

; производная ответа совпадает с подынтегральным в точке x0 (числа или вещественно-мнимый шум)
(define (ib-ok-at? F e x0)
  (let ((a (ib-d (integrate::int-diff 'x F) x0)) (b (ib-d e x0)))
    (if (and (real-numeric? a) (real-numeric? b))
        (< (abs (- a b)) 0.000001)
        #f)))

(define ib-points '(-4/5 -3/10 3/10 7/10))

(define (ib-both-sides? e)
  (let ((F (integrate e 'x)))
    (and (not (and (pair? F) (equal? (car F) 'integrate)))
         (every? (lambda (p) (ib-ok-at? F e p)) ib-points))))

(deftest "int-branch: x^2*sqrt(1-x^2) - ответ верен при x < 0 и x > 0"
  (assert-true (ib-both-sides? '(* (^ x 2) (sqrt (- 1 (^ x 2)))))))

(deftest "int-branch: x^n*sqrt(a-b*x^2) и sqrt(a-b*x^2)/x^n, x^n/sqrt(a-b*x^2) - обе стороны нуля"
  (for-each (lambda (e) (assert-true (ib-both-sides? e)))
            '((* (^ x 4) (sqrt (- 1 (^ x 2))))
              (* (^ x 2) (sqrt (- 4 (* 3 (^ x 2)))))
              (* (^ x 4) (sqrt (- 2 (^ x 2))))
              (/ (sqrt (- 1 (^ x 2))) (^ x 2))
              (/ (sqrt (- 1 (^ x 2))) (^ x 4))
              (/ (sqrt (- 4 (* 3 (^ x 2)))) (^ x 2))
              (/ (^ x 2) (sqrt (- 1 (^ x 2))))
              (/ (^ x 4) (sqrt (- 1 (^ x 2))))
              (/ (^ x 2) (sqrt (- 4 (* 3 (^ x 2)))))
              (/ (^ x 2) (sqrt (- 9 (^ x 2))))
              (/ 1 (* (^ x 2) (sqrt (- 1 (^ x 2)))))
              (* (^ x 2) (^ (- 1 (^ x 2)) 3/2))
              (* x (sqrt (- 1 (^ x 2))))
              (/ (sqrt (- 1 (^ x 2))) x))))

(deftest "int-branch: ложный ответ (верный только при x > 0) отвергается int-check"
  (let ((e '(* (^ x 2) (sqrt (- 1 (^ x 2)))))
        (fake '(+ (* -1/8 (^ x 2) (^ (+ -1 (^ x -2)) 1/2))
                  (* 1/4 (^ x 4) (^ (+ -1 (^ x -2)) 1/2))
                  (* -1/8 (atan (^ (+ -1 (^ x -2)) 1/2)))))
        (good '(+ (* 1/4 (^ x 3) (^ (- 1 (^ x 2)) 1/2))
                  (* -1/8 x (^ (- 1 (^ x 2)) 1/2))
                  (* 1/8 (asin x)))))
    (assert-true (not (int-check fake e 'x)))
    (assert-true (int-check good e 'x))))
