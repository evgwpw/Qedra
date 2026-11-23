; invli.lisp — тесты шага PL.3: ∫x·csc x и ∫x·sec x собственными правилами (Li₂ от tan(x/2)).

(define (ivl-val e v) (eval-num (subst (list 'x v) e)))          ; значение выражения при x = v
(define (ivl-deriv e) (/ (- (ivl-val e 1.00001) (ivl-val e 0.99999)) 0.00002)) ; численная производная
(define (ivl-close? a b) (and (number? a) (number? b) (< (abs (- a b)) 0.00001))) ; совпадение
(define (ivl-free? e) (not (contains-sym? e 'integrate)))          ; в ответе нет невычисленного интеграла

(deftest "invli: ∫x·csc x = i[Li₂(−it) − Li₂(it)]"
  (let ((ans (integrate '(/ x (sin x)) 'x)))                       ; x·csc x
    (assert-true (ivl-free? ans))                                  ; интеграл вычислен
    (assert-true (ivl-close? (ivl-deriv ans) (ivl-val '(/ x (sin x)) 1.0))))) ; производная = подынтегральное

(deftest "invli: ∫x·sec x через сдвиг v = x + π/2"
  (let ((ans (integrate '(/ x (cos x)) 'x)))                       ; x·sec x
    (assert-true (ivl-free? ans))
    (assert-true (ivl-close? (ivl-deriv ans) (ivl-val '(/ x (cos x)) 1.0)))))

(deftest "invli: csc с линейным аргументом"
  (let ((ans (integrate '(* x (csc (* 2 x))) 'x)))                 ; ∫x·csc(2x)
    (assert-true (ivl-free? ans))
    (assert-true (ivl-close? (ivl-deriv ans) (ivl-val '(* x (csc (* 2 x))) 1.0)))))

(deftest "invli: старые формы не сломаны"
  (assert-equal (integrate '(/ 1 (sin x)) 'x) '(log (tan (* 1/2 x)))) ; ∫csc x
  (assert-true (ivl-free? (integrate '(/ (* x (cos x)) (^ (sin x) 2)) 'x)))) ; x·csc x·cot x
