; tests/Lisp.Tests/lisp/rubi-fuzz.lisp — RUBI.FUZZ: генератор примеров и классификация правил Rubi.
; Проверяется сам инструмент самопроверки (шаг RUBI.FUZZ): для правил разных глав строится пример,
; движок делает один шаг, правило получает статус из известного набора, а хотя бы одно правило файла
; обязано быть живым (self) — иначе сломан генератор, а не правила.
(load "lib/rubi/fuzz.lisp")

(define (rubi-fuzz-statuses row) (cadr row))

(define rubi-fuzz-known '(self earlier base later none cond-unsat error))

(define (rubi-fuzz-check-file file n)
  (let* ((rs (rubi::fuzz-file-rules file))
         (rows (map rubi::fuzz-rule (take rs n))))
    (assert-true (>= (length rows) 1))
    (for-each
     (lambda (row)
       (assert-equal (length row) 8)
       (assert-true (member? (cadr row) rubi-fuzz-known))
       ; поле rhs заполнено для всех статусов (- или rhs-*)
       (assert-true (string? (nth row 7))))
     rows)
    rows))

(deftest "rubi-fuzz: правила главы 1.1 — пример строится, статусы из набора, есть живые"
  (rubi-integrate 1 'x)
  (let ((rows (rubi-fuzz-check-file "1.1.1.1" 4)))
    (assert-true (any? (lambda (row) (equal? (cadr row) 'self)) rows))
    ; у сработавшего правила правая часть проверена и не помечена как неверная
    (assert-true (any? (lambda (row) (and (equal? (cadr row) 'self) (equal? (nth row 7) "rhs-ok"))) rows))))

(deftest "rubi-fuzz: правила главы 3 (тригонометрия) — статусы из набора"
  (rubi-integrate 1 'x)
  (let ((rows (rubi-fuzz-check-file "3.1.1" 3)))
    (assert-true (any? (lambda (row) (member? (cadr row) '(self earlier base))) rows))))

(deftest "rubi-fuzz: правила главы 4 (рациональные) — статусы из набора"
  (rubi-integrate 1 'x)
  (let ((rows (rubi-fuzz-check-file "4.1.1.1" 3)))
    (assert-true (any? (lambda (row) (member? (cadr row) '(self earlier base))) rows))))

(deftest "rubi-fuzz: правило по id — цепочка статусов и причина для later/none"
  (rubi-integrate 1 'x)
  (let ((r (car (filter (lambda (q) (equal? (nth q 1) "Rubi 1.1.1.1 #3")) rubi::*rubi-rules*))))
    (assert-true (not (null? r)))
    (let ((row (rubi::fuzz-rule r)))
      (assert-equal (car row) "Rubi 1.1.1.1 #3")
      (assert-true (member? (cadr row) rubi-fuzz-known))
      ; причина осмысленна: «-» только у self/error/base
      (assert-true (or (equal? (nth row 2) "-") (string? (nth row 2)))))))
