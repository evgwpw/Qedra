; BR.ASIN: значение (eval-num) и символьная производная asin/acos/acosh на разрезах согласованы.
; Значение — по Кахану: asin z = −i·log(i·z + √(1−z)·√(1+z)), acos z = π/2 − asin z, acosh z = log(z + √(z−1)·√(z+1));
; их производные — ровно формулы Differentiate.fs (1/(√(1−u)·√(1+u)), −того же, 1/(√(u−1)·√(u+1))).
; Оракул: 5-точечная конечная разность eval-num (h = 1e-5) против подстановки точки в (diff x f).
(load (string-append lib-dir "rubi/utils.lisp"))

(define (dba-pt re im) (if (= im 0) re (list '+ re (list '* im '%i))))
(define (dba-fd head re im)
  (let* ((h 0.00001)
         (f (lambda (k) (eval-num (list head (dba-pt (+ re (* k h)) im))))))
    (/ (+ (- (f -2) (* 8 (f -1))) (- (* 8 (f 1)) (f 2))) (* 12 h))))
(define (dba-sym head re im)
  (eval-num (subst (list 'x (dba-pt re im)) (diff 'x (list head 'x)))))
(define (dba-agree? head re im)
  (< (num-abs (- (dba-fd head re im) (dba-sym head re im))) 0.000001))

(deftest "diff-branch-asin: asin — производная = конечная разность на разрезах и вне"
  (for-each (lambda (p) (assert-true (dba-agree? 'asin (car p) (cadr p))))
            '((1.5 0) (3 0) (-1.5 0) (-3 0) (0.3 0) (-0.7 0) (2 0.5) (-2 0.5) (0.4 -0.8))))

(deftest "diff-branch-asin: acos — производная = конечная разность на разрезах и вне"
  (for-each (lambda (p) (assert-true (dba-agree? 'acos (car p) (cadr p))))
            '((1.5 0) (3 0) (-1.5 0) (-3 0) (0.3 0) (-0.7 0) (2 0.5) (-2 0.5) (0.4 -0.8))))

(deftest "diff-branch-asin: acosh — производная = конечная разность на разрезах и вне"
  (for-each (lambda (p) (assert-true (dba-agree? 'acosh (car p) (cadr p))))
            '((1.5 0) (3 0) (-1.5 0) (-3 0) (0.3 0) (-0.7 0) (2 0.5) (-2 0.5) (0.4 -0.8))))

(deftest "diff-branch-asin: asinh/atanh/atan — уже согласованы (производная от ветви не зависит)"
  (for-each (lambda (h)
    (for-each (lambda (p) (assert-true (dba-agree? h (car p) (cadr p))))
              '((0.3 0) (2 0.5) (-2 0.5) (0.4 -0.8))))
    '(asinh atanh atan)))

(deftest "diff-branch-asin: значения по Кахану на разрезе и неизменны вне разрезов"
  ; на верхнем берегу было π/2 + 0.9624i, теперь нижний: π/2 − 0.9624i
  (let ((a (eval-num '(asin 1.5))) (c (eval-num '(acos 1.5))))
    (assert-true (< (num-abs (- a (dba-pt 1.5707963267948966 -0.9624236501192069))) 1e-12))
    (assert-true (< (num-abs (- c (dba-pt 0 0.9624236501192069))) 1e-12)))
  (assert-true (< (num-abs (- (eval-num '(asin -1.5)) (- (eval-num '(asin 1.5))))) 1e-12))
  ; вне разрезов — прежние главные значения
  (assert-true (< (abs (- (eval-num '(asin 0.3)) 0.3046926540153975)) 1e-14))
  (assert-true (< (abs (- (eval-num '(acos 0.3)) 1.2661036727794992)) 1e-14))
  (assert-true (< (num-abs (- (eval-num '(sin (asin (+ 2 (* 0.5 %i))))) (dba-pt 2 0.5))) 1e-12))
  (assert-true (> (num-abs (eval-num '(asin (+ 2 (* 0.5 %i))))) 1)))

(deftest "diff-branch-asin: композиция asin(c·sqrt(1-2x)) при x < -2/3 (аргумент > 1)"
  (let ((f '(asin (* (^ 21 1/2) 1/7 (^ (- 1 (* 2 x)) 1/2)))))
    (for-each
      (lambda (x)
        (let* ((h 0.00001)
               (g (lambda (k) (eval-num (subst (list 'x (+ x (* k h))) f))))
               (fd (/ (+ (- (g -2) (* 8 (g -1))) (- (* 8 (g 1)) (g 2))) (* 12 h)))
               (sy (eval-num (subst (list 'x x) (diff 'x f)))))
          (assert-true (< (num-abs (- fd sy)) 0.000001))))
      '(-1.0 -2.5 -4.0))))

; --- ответы Rubi (EllipticE/EllipticF + asin) проходят проверку дифференцированием при x < -2/3 ---

(define (dba-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (dba-rel-ok? a b) (< (num-abs (- a b)) (* 1e-8 (+ 1 (num-abs b)))))

(define (dba-corpus input)
  (dba-fresh)
  (set! rubi::rubi-time-limit 30.0)
  (let* ((e (math-read input))
         (r (rubi-integrate e 'x)))
    (set! rubi::rubi-time-limit 4.0)
    (assert-true (not (equal? r 'unknown)))
    (let ((d (diff 'x r)))
      (for-each
        (lambda (x)
          (assert-true (dba-rel-ok? (eval-num (subst (list 'x x) d)) (eval-num (subst (list 'x x) e)))))
        '(-3.7 -2.3 -0.3 0.2)))
    (assert-true (rubi::rubi-int-check r e 'x))
    ; подделка: удвоенный ответ и ответ + x не проходят
    (assert-true (not (rubi::rubi-int-check (list '* 2 r) e 'x)))
    (assert-true (not (rubi::rubi-int-check (list '+ r 'x) e 'x)))))

(deftest "diff-branch-asin: t_1_1_1_3/2808 — ответ Rubi подтверждается"
  (dba-corpus "(3*x + 2)^(7/2)*(5*x + 3)^(5/2)/sqrt(1 - 2*x)"))

(deftest "diff-branch-asin: t_1_1_1_3/2884 — ответ Rubi подтверждается"
  (dba-corpus "(3*x + 2)^(7/2)*(5*x + 3)^(5/2)/(1 - 2*x)^(3/2)"))

(deftest "diff-branch-asin: t_1_1_1_3/2938 — ответ Rubi подтверждается"
  (dba-corpus "(3*x + 2)^(7/2)*(5*x + 3)^(5/2)/(1 - 2*x)^(5/2)"))
