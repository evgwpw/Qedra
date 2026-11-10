; test.lisp — мини-фреймворк Lisp-тестов (Шаг 15b); грузится из prelude.lisp.
;
; (deftest "имя" тело...) — РЕГИСТРИРУЕТ тест в *tests*, не выполняя тела;
; запуск — (run-test "имя") или (run-tests). Файлы tests\lisp\*.lisp выполняются xUnit (LispFileTests.fs).

; Шаг 21h': register-test и assert-error-fn экспортируются, потому что на них раскрываются макросы deftest / assert-error
; (раскрытие компилируется в области имён вызывающего кода)
(module test
  (export deftest register-test run-test run-tests assert-equal assert-true assert-error assert-error-fn))

; список тестов: ((имя функция) ...), новые — в начале
(define *tests* '())

(define (register-test name f)
  (set! *tests* (cons (list name f) *tests*))
  name)

(defmacro (deftest name &rest body)
  `(register-test ,name (lambda () ,@body)))

; (run-test "имя") — выполнить тело теста; ошибка (assert-*) пробрасывается
(define (run-test-in name tests)
  (cond ((null? tests) (error "run-test: тест не найден:" name))
        ((equal? (car (car tests)) name) ((cadr (car tests))))
        (else (run-test-in name (cdr tests)))))
(define (run-test name) (run-test-in name *tests*))

; (run-tests) — выполнить все; печатает «ok/FAIL имя», возвращает число провалов
(define (run-tests-in tests failed)
  (if (null? tests)
      failed
      (let ((r (try (begin ((cadr (car tests))) #t)
                    (lambda (e) (error-message e)))))
        (if (equal? r #t)
            (begin (display "ok   ") (display (car (car tests))) (newline)
                   (run-tests-in (cdr tests) failed))
            (begin (display "FAIL ") (display (car (car tests))) (display ": ") (display r) (newline)
                   (run-tests-in (cdr tests) (+ failed 1)))))))
(define (run-tests) (run-tests-in (reverse *tests*) 0))

; (assert-equal факт ожидание) — structEqual; при неудаче — error с обоими значениями
; в s-записи и в инфиксной записи.
; Шаг D3b: для списочных значений — путь к первому различающемуся подвыражению
; ((2 1) — 2-й аргумент, его 1-й подаргумент) и печать обоих подвыражений там; если
; simplify разности = 0 — подсказка «равны по значению, другая форма»
(define (assert-first-diff a b path)
  (cond ((equal? a b) #f)
        ((and (pair? a) (pair? b) (= (length a) (length b)) (equal? (car a) (car b)))
         ; списки одной длины с одинаковой головой: спускаемся по аргументам
         (assert-first-diff-args (cdr a) (cdr b) 1 path))
        (#t (cons path (list a b)))))
(define (assert-first-diff-args as bs i path)
  (cond ((null? as) (cons path (list as bs)))
        (#t (let ((r (assert-first-diff (car as) (car bs) (append path (list i)))))
              (if r
                  r
                  (assert-first-diff-args (cdr as) (cdr bs) (+ i 1) path))))))
(define (assert-equal actual expected)
  (if (equal? actual expected)
      #t
      (let ((diff (if (and (pair? actual) (pair? expected))
                      (assert-first-diff actual expected '())
                      #f)))
        (error
         (string-append
          "assert-equal: получено " (to-string actual) " [" (math-print actual)
          "], ожидалось " (to-string expected) " [" (math-print expected) "]"
          (if diff
              (string-append "; первое различие в " (to-string (car diff))
                             ": получено " (to-string (cadr diff))
                             ", ожидалось " (to-string (caddr diff)))
              "")
          (let ((d (try (simplify (list '- actual expected)) (lambda (e) 'diff-err))))
            (cond ((equal? d 'diff-err) "")
                  ((and (number? d) (= d 0)) "; разность simplify = 0 — равны по значению, другая форма")
                  (#t ""))))))))

(define (assert-true x)
  (if x #t (error (string-append "assert-true: получено " (to-string x)))))

; (assert-error выражение) — выражение (НЕ вычисляется заранее) должно завершиться ошибкой
(define (assert-error-fn thunk)
  (if (try (begin (thunk) #f) (lambda (e) #t))
      #t
      (error "assert-error: ожидалась ошибка, но её не было")))
(defmacro (assert-error e)
  `(assert-error-fn (lambda () ,e)))
