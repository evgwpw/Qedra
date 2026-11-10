; Шаг INT.SQ: подстановки u = xⁿ (x^(kn−1)·F(xⁿ), символьное n) и v = √(c+dx) (P(x)·G(√(c+dx))).
; Оракул: |F′ − f| / (1 + |f|) < 1e-8 в точках x ∈ {0.3, 0.7, 1.3, 2.1} при двух наборах параметров (a b c d w p n).

(define isq-params
  (list '((a 2) (b 3) (c 1) (d 5) (w 2) (p 7/3) (n 3/2))
        '((a 1) (b 1/2) (c 3) (d 2) (w 3) (p -5/2) (n 2))))

(define isq-points '(0.3 0.7 1.3 2.1))

; F′ = f численно для всех наборов параметров и точек
(define (isq-oracle? F f)
  (every? (lambda (ps)
            (let ((Fp (diff 'x (subst ps F))) (fs (subst ps f)))
              (every? (lambda (pt)
                        (let ((dv (eval-num (subst (list 'x pt) Fp))) (fv (eval-num (subst (list 'x pt) fs))))
                          (and (number? dv) (number? fv) (< (/ (abs (- dv fv)) (+ 1 (abs fv))) 1e-8))))
                      isq-points)))
          isq-params))

(define (isq-solved? f)
  (let ((r (integrate f 'x)))
    (and (not (contains-sym? r 'integrate)) (isq-oracle? r f))))

(define (isq-unknown? f)
  (contains-sym? (integrate f 'x) 'integrate))

(deftest "INT.SQ: u = xⁿ, x^(kn−1)·F(xⁿ), символьное n"
  (assert-true (isq-solved? '(* (^ (* w x) (+ -1 (* 3 n))) (^ (+ a (* b (^ (+ c (* d (^ x n))) 1/2))) p))))
  (assert-true (isq-solved? '(* (^ x (+ -1 (* 3 n))) (^ (+ a (* b (^ (+ c (* d (^ x n))) 1/2))) p))))
  (assert-true (isq-solved? '(* (^ x (+ -1 (* 2 n))) (^ (+ a (* b (^ x n))) p))))
  (assert-true (isq-solved? '(* (^ x (+ -1 (* 5 n))) (^ (+ a (* b (^ x n))) -1/2)))))

(deftest "INT.SQ: v = √(c+dx), P(x)·G(√(c+dx))"
  (assert-true (isq-solved? '(* (^ x 2) (^ (+ a (* b (^ (+ c (* d x)) 1/2))) p))))
  (assert-true (isq-solved? '(* x (^ (+ a (* b (^ (+ c (* d x)) 1/2))) p))))
  (assert-true (isq-solved? '(* (^ x 3) (^ (+ a (* b (^ (+ c (* d x)) 1/2))) p))))
  (assert-true (isq-solved? '(* (^ (+ c (* d x)) 1/2) (^ x 2))))
  (assert-true (isq-solved? '(^ (+ a (* b (^ x 1/2))) p)))
  (assert-true (isq-solved? '(* (^ x 2) (^ (+ a (* b x)) p)))))

(deftest "INT.SQ: не этот класс — ложной элементарной формулы нет"
  (assert-true (isq-unknown? '(* x (^ (+ a (* b (^ (+ c (* d x)) 3/2))) p)))))
