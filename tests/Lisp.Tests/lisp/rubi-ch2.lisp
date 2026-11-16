; RUBI.CH2: глава 2 (экспоненты) — 213/963 в пилоте master 4288a14. Классификация 614 из 750 неудач по журналу
; (run-режим): 356 — правило совпало, но ответ отвергнут проверкой (int-check), 140 — правая часть не дала ответа,
; 92 — условие, 26 — подзадача. Причина главного класса: ответы правил 2.1/2.2 идут через Γ(m+1, z) и
; ExpIntegralEi («2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m», правило 4: Gamma[m+1, -f*g*Log[F]/d*(c+d*x)]),
; а eval-num этих голов не знал — проверка возвращала 'skip и ответ отклонялся. Тест охраняет:
; (1) численные Γ(a,z) (обе ветви: ряд и непрерывная дробь) и Ei, (2) производные этих голов (нужны int-diff),
; (3) значение E (ответы содержат Log[F] с F = E), (4) задачи 2.1/8 и 2.3/305, которые до правки были unknown.

(load (string-append lib-dir "rubi/utils.lisp"))

; другие файлы тестов подменяют правила Rubi игрушечными наборами — возвращаем настоящие
(define (rch-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (rch-near? a b tol) (and (number? a) (number? b) (< (abs (- a b)) tol)))

(deftest "rubi-ch2/1: Γ(a,z) численно — Γ(1,z) = e^(−z) и рекуррентность Γ(a+1,z) = aΓ(a,z) + z^a e^(−z)"
  ; a = 1 — ряд (|z| < |a+1|): Γ(1, 0.6) = e^(−0.6)
  (assert-true (rch-near? (eval-num '(gamma 1 0.6)) (eval-num '(exp -0.6)) 1e-14))
  ; a = −1.7, z = 0.6 — ветвь ряда (отражение Γ(a) для нецелого a)
  (let ((lhs (eval-num '(gamma (+ -0.7 1) 0.6)))
        (rhs (+ (* -0.7 (eval-num '(gamma -0.7 0.6))) (* (^ 0.6 -0.7) (exp -0.6)))))
    (assert-true (rch-near? lhs rhs 1e-12)))
  ; a = 2.4, z = 4.5 — ветвь непрерывной дроби (|z| > |a+1|)
  (let ((lhs (eval-num '(gamma (+ 2.4 1) 4.5)))
        (rhs (+ (* 2.4 (eval-num '(gamma 2.4 4.5))) (* (^ 4.5 2.4) (exp -4.5)))))
    (assert-true (rch-near? lhs rhs 1e-12)))
  ; целое a ≤ 0 (ответ правила 2.1 #4 несёт gamma -2 z): Γ(−2, z) = E₃(z)/z² > 0 при z > 0
  (assert-true (> (eval-num '(gamma -2 1.5)) 0)))

(deftest "rubi-ch2/2: Ei правил Rubi (exp_integral_ei) — то же число, что Ei; производные через int-check"
  (assert-true (rch-near? (eval-num '(exp_integral_ei 1.5)) (eval-num '(Ei 1.5)) 1e-15))
  (assert-true (rch-near? (eval-num '(exp_integral_ei 1.5)) 3.301285449129798 1e-12))
  ; d/du Ei(u) = e^u/u — проверка формы не зависит от вида упрощённого ответа
  (assert-true (int-check '(exp_integral_ei x) '(/ (exp x) x) 'x))
  ; d/dz Γ(a, z) = −z^(a−1)·e^(−z), a = −2 (ответ правила 2.1 #4)
  (assert-true (int-check '(gamma -2 x) '(/ -1 (* (^ x 3) (exp x))) 'x))
  ; a = 5/2 — нецелый порядок, ветвь непрерывной дроби
  (assert-true (int-check '(gamma 5/2 x) '(/ -1 (* (^ x -3/2) (exp x))) 'x)))

(deftest "rubi-ch2/3: основание экспоненты E имеет численное значение (log E = 1)"
  (assert-true (rch-near? (eval-num '(log E)) 1.0 1e-15))
  (assert-true (rch-near? (eval-num '(^ E 2)) (exp 2) 1e-15)))

(deftest "rubi-ch2/4: 2.1/8 F^(c(a+b x))/(d+e x)^3 — ответ через Γ(−2, z) есть и верен численно"
  (rch-fresh)
  (let* ((e (math-read "F**(c*(a + b*x))/(d + e1*x)**3"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r 'integrate)))
    (assert-equal 'ok (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x r) e) r 'x 0.000001 '(0.6 1.3)))))

(deftest "rubi-ch2/5: 2.3/305 F^(a + b/(c+d x)) — ответ есть и верен численно"
  (rch-fresh)
  (let* ((e (math-read "F**(a + b/(c + d*x))"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r 'integrate)))
    (assert-equal 'ok (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x r) e) r 'x 0.000001 '(0.6 1.3)))))
