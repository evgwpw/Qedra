; INT.GAPS.3: ответы через Li₂/Li₃/Li₄ для logⁿ(p)/q, atanh(p)/q, atanh(√p)/q (p, q линейны) — lib/integrate/polylog.lisp.
; Каждый ответ принят проверкой int-check и численной проверкой самого F (ipl-F-ok?: значения Li_s, не формальная производная);
; подделка (знак, лишний множитель) отвергается.

(define (plp-open? r) (contains-sym? r 'integrate))

; значение F на отрезке — по Li_s вещественной части (ipl-val-at), сверка с квадратурой Симпсона
(define (plp-simpson e a b n)
  (let ((h (/ (- b a) n)))
    (* h 1/3
       (foldl (lambda (acc i)
                (+ acc (* (cond ((or (= i 0) (= i n)) 1) ((= (remainder i 2) 1) 4) (else 2))
                          (eval-num (integrate::int-hyp (subst (list '= 'x (+ a (* i h))) e))))))
              0 (range (+ n 1))))))

(define (plp-def F a b)
  (- (car (integrate::ipl-val-at F 'x b '())) (car (integrate::ipl-val-at F 'x a '()))))

(deftest "polylog-parts/1: ∫log(a+bx)³/(c+dx) — Li₂, Li₃, Li₄ (Google №36)"
  (let* ((f '(* (^ (log (+ a (* b x))) 3) (^ (+ c (* d x)) -1)))
         (F (integrate f 'x)))
    (assert-true (not (plp-open? F)))
    (assert-true (contains-sym? F 'polylog))
    (assert-true (int-check F f 'x))
    (assert-true (integrate::ipl-F-ok? F f 'x))))

(deftest "polylog-parts/2: ∫log(2+3x)³/(5−x), ∫log(x)²/(1+x) — сверка с квадратурой"
  (let* ((f1 '(* (^ (log (+ 2 (* 3 x))) 3) (^ (+ 5 (* -1 x)) -1)))
         (f2 '(* (^ (log x) 2) (^ (+ 1 x) -1)))
         (F1 (integrate f1 'x))
         (F2 (integrate f2 'x)))
    (assert-true (not (plp-open? F1)))
    (assert-true (not (plp-open? F2)))
    (assert-true (< (abs (- (plp-def F1 1.0 2.0) (plp-simpson f1 1.0 2.0 200))) 1e-7))
    (assert-true (< (abs (- (plp-def F2 1.0 3.0) (plp-simpson f2 1.0 3.0 200))) 1e-7))))

(deftest "polylog-parts/3: ∫atanh(√(a+bx))/x (Google №8) — разность дилогарифмов, условие s² > 0"
  (let* ((f '(* (atanh (sqrt (+ a (* b x)))) (^ x -1)))
         (F (integrate f 'x)))
    (assert-true (not (plp-open? F)))
    (assert-true (contains-sym? F 'polylog))
    (assert-true (integrate::ipl-F-ok? F f 'x))))

(deftest "polylog-parts/4: ∫atanh(√(1/2+x/3))/x — численный отрезок [0.2, 1]"
  (let* ((f '(* (atanh (sqrt (+ 1/2 (* 1/3 x)))) (^ x -1)))
         (F (integrate f 'x)))
    (assert-true (not (plp-open? F)))
    (assert-true (< (abs (- (plp-def F 0.2 1.0) (plp-simpson f 0.2 1.0 200))) 1e-7))))

(deftest "polylog-parts/5: ∫atanh(x)/(1+x) и ∫log(a+bx)/(c+dx) — линейные p, q"
  (let* ((f1 '(* (atanh (+ 1/2 (* 1/4 x))) (^ (+ 2 x) -1)))
         (f2 '(* (log (+ a (* b x))) (^ (+ c (* d x)) -1)))
         (F1 (integrate f1 'x))
         (F2 (integrate f2 'x)))
    (assert-true (not (plp-open? F1)))
    (assert-true (not (plp-open? F2)))
    (assert-true (integrate::ipl-F-ok? F2 f2 'x))))

(deftest "polylog-parts/6: подделка ответа отвергается (знак, множитель, не тот подынтегральный)"
  (let* ((f '(* (^ (log (+ 2 (* 3 x))) 3) (^ (+ 5 (* -1 x)) -1)))
         (F (integrate f 'x)))
    (assert-true (integrate::ipl-F-ok? F f 'x))
    (assert-true (not (integrate::ipl-F-ok? (list '* -1 F) f 'x)))
    (assert-true (not (integrate::ipl-F-ok? (list '* 2 F) f 'x)))
    (assert-true (not (integrate::ipl-F-ok? F '(* (^ (log (+ 2 (* 3 x))) 2) (^ (+ 5 (* -1 x)) -1)) 'x)))))

(deftest "polylog-parts/7: прежние формы PL не изменились (log(1+x)/x = −Li₂(−x))"
  (assert-equal (integrate '(* (log (+ 1 x)) (^ x -1)) 'x) '(* -1 (polylog 2 (* -1 x)))))

; ---------- INT.GAPS.3b: комплексный Li₂ и ответы через него ----------

(define (plp-close? a b) (< (abs (- a b)) 1e-13))
(define plp-pi (eval-num 'pi))
(define plp-catalan 0.915965594177219015)

(deftest "polylog-parts/8: Li₂ от комплексного аргумента — эталонные значения"
  (let ((li-i (polylog2-cx 0 1)) (li-m1 (polylog2-cx -1 0)) (li-2 (polylog2-cx 2 0))
        (li-h (polylog2-cx 1/2 0)) (li-hh (polylog2-cx 0.5 0.5)) (ln2 (eval-num '(log 2))))
    ; Li₂(i) = −π²/48 + i·G
    (assert-true (plp-close? (car li-i) (/ (* plp-pi plp-pi) -48)))
    (assert-true (plp-close? (cdr li-i) plp-catalan))
    ; Li₂(−1) = −π²/12
    (assert-true (plp-close? (car li-m1) (/ (* plp-pi plp-pi) -12)))
    (assert-true (plp-close? (cdr li-m1) 0))
    ; Li₂(2) = π²/4 − i·π·ln 2 (разрез сверху вниз: значение «снизу», как в исходнике Rubi)
    (assert-true (plp-close? (car li-2) (/ (* plp-pi plp-pi) 4)))
    (assert-true (plp-close? (cdr li-2) (- (* plp-pi ln2))))
    ; Li₂(1/2) = π²/12 − ln²2/2
    (assert-true (plp-close? (car li-h) (- (/ (* plp-pi plp-pi) 12) (/ (* ln2 ln2) 2))))
    ; Li₂((1+i)/2) = 5π²/96 − ln²2/8 + i(G − π·ln 2/8)
    (assert-true (plp-close? (car li-hh) (- (/ (* 5 plp-pi plp-pi) 96) (/ (* ln2 ln2) 8))))
    (assert-true (plp-close? (cdr li-hh) (- plp-catalan (/ (* plp-pi ln2) 8))))))

(deftest "polylog-parts/9: Li₂(e^{iπ/3}) = π²/6 − θ(2π−θ)/4 + i·Cl₂(θ); d/dz Li₂ = −log(1−z)/z по всей плоскости"
  (let* ((th (/ plp-pi 3)) (v (polylog2-cx (eval-num (list 'cos th)) (eval-num (list 'sin th)))))
    (assert-true (plp-close? (car v) (- (/ (* plp-pi plp-pi) 6) (/ (* th (- (* 2 plp-pi) th)) 4))))
    (assert-true (plp-close? (cdr v) 1.0149416064096536)))
  ; центральная разность вдоль вещественной оси против −log(1−z)/z; точки в каждой области схемы (ряд, отражение, инверсия)
  (let ((h 1e-6))
    (for-each
     (lambda (pt)
       (let* ((x (car pt)) (y (cadr pt))
              (a (polylog2-cx (+ x h) y)) (b (polylog2-cx (- x h) y))
              (d (integrate::int-cx-parts
                  (eval-num (list '* -1 (list 'log (list '+ 1 (list '* -1 (list '+ x (list '* y '%i)))))
                                  (list '^ (list '+ x (list '* y '%i)) -1))))))
         (assert-true (< (abs (- (/ (- (car a) (car b)) (* 2 h)) (car d))) 1e-7))
         (assert-true (< (abs (- (/ (- (cdr a) (cdr b)) (* 2 h)) (cdr d))) 1e-7))))
     '((0.2 0.3) (0.9 0.4) (0.3 1.5) (-3.0 2.0) (-0.7 -0.6) (2.5 1.0) (0.4 -2.0) (0.1 -0.95) (-5.0 0.5)))))

(deftest "polylog-parts/10: ∫atan(x)/x = (i/2)(Li₂(−ix) − Li₂(ix)); atan(x)/(1+x); atan(a+bx)/(c+dx)"
  (let* ((f0 '(* (atan x) (^ x -1))) (F0 (integrate f0 'x))
         (f1 '(* (atan x) (^ (+ 1 x) -1))) (F1 (integrate f1 'x))
         (f2 '(* (atan (+ 1 (* 2 x))) (^ (+ 3 (* -1 x)) -1))) (F2 (integrate f2 'x))
         (f3 '(* (atan (+ a (* b x))) (^ (+ c (* d x)) -1))) (F3 (integrate f3 'x)))
    (assert-equal F0 '(* 1/2 %i (+ (polylog 2 (* -1 %i x)) (* -1 (polylog 2 (* %i x))))))
    (for-each (lambda (r) (assert-true (not (plp-open? r)))) (list F1 F2 F3))
    (assert-true (< (abs (- (plp-def F0 0.3 3.0) (plp-simpson f0 0.3 3.0 400))) 1e-7))
    (assert-true (< (abs (- (plp-def F1 -0.5 2.0) (plp-simpson f1 -0.5 2.0 400))) 1e-7))
    (assert-true (< (abs (- (plp-def F2 3.5 7.0) (plp-simpson f2 3.5 7.0 400))) 1e-7))
    (assert-true (< (abs (- (plp-def F2 -4.0 2.0) (plp-simpson f2 -4.0 2.0 400))) 1e-7))
    (assert-true (integrate::ipl-F-ok? F3 f3 'x))
    (assert-true (not (integrate::ipl-F-ok? (list '* 2 F0) f0 'x)))))

(deftest "polylog-parts/11: ∫atan(a+bx)²/(c+dx)² (Google №5) — по частям и разложение на простые дроби"
  (let* ((f1 '(* (^ (atan x) 2) (^ x -2))) (F1 (integrate f1 'x))
         (f2 '(* (^ (atan (+ 1 (* 2 x))) 2) (^ (+ 3 (* -1 x)) -2))) (F2 (integrate f2 'x))
         (f3 '(* (^ (atan (+ a (* b x))) 2) (^ (+ c (* d x)) -2))) (F3 (integrate f3 'x)))
    (for-each (lambda (r) (assert-true (not (plp-open? r)))) (list F1 F2 F3))
    (assert-true (contains-sym? F3 'polylog))
    (assert-true (< (abs (- (plp-def F1 0.3 3.0) (plp-simpson f1 0.3 3.0 400))) 1e-7))
    (assert-true (< (abs (- (plp-def F2 0.0 2.5) (plp-simpson f2 0.0 2.5 400))) 1e-6))
    (assert-true (< (abs (- (plp-def F2 3.5 7.0) (plp-simpson f2 3.5 7.0 400))) 1e-6))
    (assert-true (integrate::ipl-F-ok? F3 f3 'x))
    (assert-true (not (integrate::ipl-F-ok? (list '* -1 F2) f2 'x)))))

(deftest "polylog-parts/12: ∫(a + b·atanh(c/x²))² (Google №1) — Li₂ от комплексных аргументов, x² > c"
  (let* ((f1 '(^ (atanh (* 1/3 (^ x -2))) 2)) (F1 (integrate f1 'x))
         (f2 '(^ (+ 3 (* 5 (atanh (* 1/4 (^ x -2))))) 2)) (F2 (integrate f2 'x))
         (f3 '(^ (+ a (* b (atanh (* c (^ x -2))))) 2)) (F3 (integrate f3 'x)))
    (for-each (lambda (r) (assert-true (not (plp-open? r)))) (list F1 F2 F3))
    (assert-true (contains-sym? F3 'polylog))
    (assert-true (< (abs (- (plp-def F1 0.7 3.0) (plp-simpson f1 0.7 3.0 400))) 1e-6))
    (assert-true (< (abs (- (plp-def F2 0.6 4.0) (plp-simpson f2 0.6 4.0 400))) 1e-5))
    (assert-true (integrate::ipl-F-ok? F3 f3 'x))
    (assert-true (not (integrate::ipl-F-ok? (list '* 2 F1) f1 'x)))
    (assert-true (not (integrate::ipl-F-ok? F1 '(^ (atanh (* 1/3 (^ x -2))) 3) 'x)))))
