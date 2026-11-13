; RUBI.DET: результат Rubi не зависит от истории процесса — правила всех глав грузятся целиком перед первым
; применением (раньше алгебраический вход видел только главы 1.*, и ответ зависел от прогрева неалгебраическим входом).
(load (string-append lib-dir "rubi/utils.lisp"))
(load (string-append lib-dir "rubi/engine.lisp"))

(define (rdet-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (rdet-solve src)
  (let* ((e (math-read src)) (r (rubi-integrate-within e 'x 20)))
    (assert-true (not (equal? r #f)))
    ; int-check: производная ответа совпадает с подынтегральным в контрольных точках
    (assert-true (rubi::rubi-int-check r e 'x))
    r))

(define rdet-big "(1+x^2)*sqrt(x^2+sqrt(1+x^4))/((x^2-1)*sqrt(1+x^4))")

(deftest "rubi-det: после сброса загружены все главы (stage 2), а не только 1.*"
  (rdet-fresh)
  (rubi::rubi-ensure)
  (assert-equal 2 rubi::*rubi-stage*)
  (assert-true (> (length rubi::*rubi-rules*) 5000)))

(deftest "rubi-det: Rubi 9.3 #24 берётся в свежем состоянии, ответ равен ответу после прогрева"
  (rdet-fresh)
  (let ((r1 (rdet-solve rdet-big)))
    (rdet-fresh)
    (rubi-integrate-within (math-read "sin(x)*exp(x)") 'x 20)
    (assert-equal r1 (rdet-solve rdet-big))))

(deftest "rubi-det: алгебраические входы, которые брались только после полной загрузки"
  (rdet-fresh)
  (for-each rdet-solve
            '("1/sqrt(x^(2 - n)*(a + b*x^n))"
              "1/sqrt(x^n*(a + b*x^(2 - n)))"
              "(x^((n - 1)/p)*(a + b*x^n))^p")))

; RUBI.ORDER: порядок применения — глобальный порядок Rubi.m (файл за файлом, внутри файла по номеру правила);
; индексы (головы, корень образца, форма) только отбирают кандидатов и порядка не меняют.
(define (rord-ascending? l)
  (let loop ((l l) (p -1))
    (or (null? l) (and (> (car (car l)) p) (loop (cdr l) (car (car l)))))))

(deftest "rubi-order: кандидаты и список правил идут по возрастанию глобального номера; 9.3 после 1.x"
  (rdet-fresh)
  (rubi::rubi-ensure)
  (assert-true (rord-ascending? rubi::*rubi-rules*))
  (let* ((e (math-read "(A + B*x^2)/(b*x^2 + c*x^4)^(3/2)"))
         (c (rubi::rubi-candidates e (rubi::rubi-expr-heads e '())))
         (ids (map (lambda (r) (nth r 1)) c))
         (pos (lambda (p) (let loop ((l ids) (i 0)) (cond ((null? l) #f) ((string-contains? (car l) p) i) (else (loop (cdr l) (+ i 1))))))))
    (assert-true (rord-ascending? c))
    (assert-true (< (pos "Rubi 1.1.1.1 #1") (pos "Rubi 1.1.2.5 #11")))
    (assert-true (< (pos "Rubi 1.1.2.5 #11") (pos "Rubi 9.3 #17")))))
