; RUBI.BACKTRACK: ограничение перебора главы 9 после отказа правила (lib/rubi/engine.lisp,
; *rubi-bt-9x-tries*). Тест охраняет границы: (1) задачи, которым откат в главу 9 НУЖЕН, решаются
; (предел не режет нужное); (2) откат в главу 9 действительно происходит (механизм не выключен молча).
(load (string-append lib-dir "rubi/utils.lisp"))

; другие файлы тестов подменяют правила Rubi игрушечными наборами — возвращаем настоящие
(define (rbt-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (rbt-deriv-ok? f e pts)
  (equal? 'ok (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x f) e) f 'x 0.000001 pts)))

; 1.1.4.2/408: ответ даёт подстановка главы 9 после отказа правил главы 1 — 11 откатов на подвыражении.
(deftest "rubi-backtrack/1: замена x^(2-n) (1.1.4.2/408) — откат в главу 9 нужен и не срезан пределом"
  (rbt-fresh)
  (let* ((e (math-read "1/sqrt(x^(2 - n)*(a + b*x^n))"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (rbt-deriv-ok? r e '(0.7 1.9)))
    (assert-true (> rubi::*rubi-bt-9x-n* 0))))

; 4.5: секанс — правило главы 1 подходит и отказывает, ответ даёт правило главы 4 через отказ в 9.x;
; численную сверку не делаем: ответ с sec переписан через cos(e1 + pi/2 + f x), eval-num даёт skip.
(deftest "rubi-backtrack/2: (a + b sec^2) sec — перебор 9.x на подвыражении не срезает ответ"
  (rbt-fresh)
  (let* ((e (math-read "(a + b*sec(e1 + f*x)^2)*sec(e1 + f*x)"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r 'integrate)))
    (assert-true (> rubi::*rubi-bt-9x-n* 0))))
