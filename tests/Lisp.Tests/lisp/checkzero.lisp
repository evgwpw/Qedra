; checkzero.lisp — тесты шага CHECK.ZERO: проверка первообразной не принимает F = 0 для малой f (допуск был абсолютным),
; запасная подстановка не подбирает R = 0 (lib/integrate/check.lisp, subst.lisp; цепочка на hebisch/4586 — tools/rubi/cases/check-zero.lisp)

; f ~ 1e-12 во всех пробных точках: численная сверка с допуском 1e-7·(1 + |f|) принимала любой F с F′ ≈ 0
(define cz-f '(* (^ 10 -12) x (^ (+ 1 (^ x 2)) 1/2)))
(define cz-F '(* 1/3 (^ 10 -12) (^ (+ 1 (^ x 2)) 3/2)))

(deftest "checkzero: F = 0 не первообразная малой f"
  (assert-true (not (equal? (int-check 0 cz-f 'x) #t)))
  (assert-true (not (member? (int-check-how 0 cz-f 'x) '(simplify together numeric))))
  (assert-true (not (member? (int-check-rubi-how 0 cz-f 'x) '(simplify together numeric)))))

(deftest "checkzero: верная первообразная малой f принимается"
  (assert-true (int-check cz-F cz-f 'x))
  (assert-true (not (equal? (int-check-how cz-F cz-f 'x) 'bad))))

(deftest "checkzero: ошибочная первообразная малой f (множитель 1,001) не принимается"
  (assert-true (not (equal? (int-check (list '* 1001/1000 cz-F) cz-f 'x) #t))))

(deftest "checkzero: численная проверка самого ответа — F = 0 не 'ok для малой f"
  (assert-true (not (equal? (integrate::int-check-F-status-try 0 cz-f 'x integrate::int-numchk-params) 'ok))))

(deftest "checkzero: запасная подстановка не отвечает 0 на малую f"
  (assert-true (not (equal? (int-hidden-subst cz-f 'x) 0))))

(deftest "checkzero: нулевая f — F = 0 по-прежнему верна (zero-test доказывает f ≡ 0)"
  (assert-true (int-check 0 '(+ (* x (^ 10 -12)) (* -1 x (^ 10 -12))) 'x)))
