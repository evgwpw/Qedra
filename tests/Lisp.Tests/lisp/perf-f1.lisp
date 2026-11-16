; PERF.F1: треугольный базис по модулю простого на F# (modbasis-*) против Lisp-эталона (an-inc-add! / an-inc-solve в ansatz.lisp)
; и комплексный Li₂ (SolveNum.fs) против эталонных значений.

; случайные разреженные системы: те же результаты строк ('indep / 'dep / 'bad) и то же решение
(define (pf-rand-sys seed nu nrows P)
  (let ((s seed) (piv (make-vector nu #f)) (b (modbasis-new nu P)))
    (let ((rnd (lambda () (set! s (modulo (+ (* s 1103515245) 12345) 2147483648)) (modulo (quotient s 16) 50))))
      (let loop ((i 0) (res '()))
        (if (= i nrows)
            (list (reverse res) (modbasis-solve b) (integrate::an-inc-solve piv nu P) (modbasis-rank b))
            (let* ((row (map (lambda (j) (if (< (rnd) 20) 0 (rnd))) (range (+ nu 1))))
                   (r1 (integrate::an-inc-add! piv (list->vector row) nu P))
                   (r2 (modbasis-add! b row)))
              (loop (+ i 1) (cons (equal? r1 r2) res))))))))

(deftest "perf-f1: modbasis совпадает с an-inc-add!/an-inc-solve на случайных системах"
  (for-each
   (lambda (seed)
     (let ((r (pf-rand-sys seed 7 12 2147483579)))
       (assert-true (every? (lambda (x) x) (car r)))
       (assert-equal (cadr r) (caddr r))))
   '(1 2 3 4 5 6 7 8))
  (let ((r (pf-rand-sys 99 5 9 2147483647)))
    (assert-true (every? (lambda (x) x) (car r)))
    (assert-equal (cadr r) (caddr r))))

(deftest "perf-f1: modbasis — зависимые и несовместные строки"
  (let ((b (modbasis-new 2 2147483579)))
    (assert-equal (modbasis-add! b '(1 1 3)) 'indep)
    (assert-equal (modbasis-add! b '(1 -1 1)) 'indep)
    (assert-equal (modbasis-add! b '(2 0 4)) 'dep)
    (assert-equal (modbasis-add! b '(1 0 5)) 'bad)
    (assert-equal (modbasis-solve b) '(2 1))))

(define (pf-near? c re im) (and (< (abs (- (car c) re)) 1e-13) (< (abs (- (cdr c) im)) 1e-13)))

(deftest "perf-f1: Li₂ комплексный — эталоны"
  (let ((pi2 (* (eval-num 'pi) (eval-num 'pi))) (g 0.915965594177219) (l2 (eval-num '(log 2))))
    (assert-true (pf-near? (polylog2-cx 0 1) (/ pi2 -48.0) g))
    (assert-true (pf-near? (polylog2-cx -1 0) (/ pi2 -12.0) 0.0))
    (assert-true (pf-near? (polylog2-cx 2 0) (/ pi2 4.0) (- (* (eval-num 'pi) l2))))
    (assert-true (pf-near? (polylog2-cx 1/2 0) (- (/ pi2 12.0) (/ (* l2 l2) 2.0)) 0.0))
    (assert-true (pf-near? (polylog2-cx 1/2 1/2) (- (/ (* 5.0 pi2) 96.0) (/ (* l2 l2) 8.0)) (- g (/ (* (eval-num 'pi) l2) 8.0))))
    (assert-true (pf-near? (polylog2-cx 1/2 (/ (eval-num '(sqrt 3)) 2.0)) (/ pi2 36.0) 1.0149416064096536))))

(deftest "perf-f1: eval-num (polylog 2 z) для комплексного z и z > 1"
  (assert-true (< (abs (- (eval-num '(polylog 2 -1)) -0.8224670334241132)) 1e-13))
  (let ((v (eval-num '(polylog 2 (* 2 %i)))) (w (eval-num '(polylog 2 2))))
    (assert-true (contains-sym? v '%i))
    (assert-true (contains-sym? w '%i))
    (assert-true (< (abs (- (cadr w) 2.4674011002723395)) 1e-13))))
