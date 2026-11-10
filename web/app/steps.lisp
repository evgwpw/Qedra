; WASM.3c: шаги решения в JSON для интерфейса — заголовок, правило, комментарий,
; формула «до ⇒ после» (LaTeX) и текстовые формы на случай служебных шагов без формул.
; Вызывается из web/app/app.js: (app-steps-json "integrate(x*exp(x), x)" 'brief)
; Запись шага (lib/steps.lisp): (rule title comment before after level children omitted).

(define (app-json-esc s)
  (let loop ((i 0) (out ""))
    (if (>= i (string-length s)) out
        (let ((c (substring s i (+ i 1))))
          (loop (+ i 1)
                (string-append out
                  (cond ((equal? c "\"") "\\\"")
                        ((equal? c "\\") "\\\\")
                        (else c))))))))

; пустой служебный шаг: ни заголовка, ни комментария, ни «до», ни «после» (в brief такие были видны точкой)
(define (app-step-empty? st)
  (and (equal? (to-string (step-title st)) "")
       (equal? (to-string (step-comment st)) "")
       (null? (step-before st))
       (null? (step-after st))))

; фильтр дерева: пустой узел заменяется своими детьми
(define (app-steps-nonempty ss)
  (cond ((null? ss) '())
        ((app-step-empty? (car ss))
         (append (app-steps-nonempty (step-children (car ss))) (app-steps-nonempty (cdr ss))))
        (else (cons (car ss) (app-steps-nonempty (cdr ss))))))

(define (app-step-json st)
  (let* ((rule (to-string (step-rule st)))
         (title (to-string (step-title st)))
         (comment (let ((c (step-comment st))) (if (null? c) "" (to-string c))))
         (ks (app-steps-nonempty (step-children st)))
         (sub (if (null? ks) ""
                  (string-append ",\"children\":["
                                 (let loop ((xs ks) (acc "") (first #t))
                                   (if (null? xs) acc
                                       (loop (cdr xs)
                                             (string-append acc (if first "" ",") (app-step-json (car xs)))
                                             #f)))
                                 "]"))))
    (string-append
     "{\"rule\":\"" (app-json-esc rule) "\",\"title\":\"" (app-json-esc title) "\","
     "\"comment\":\"" (app-json-esc comment) "\","
     "\"before_latex\":\"" (app-json-esc (math-latex (step-before st))) "\","
     "\"before_text\":\"" (app-json-esc (math-print (step-before st))) "\","
     "\"after_latex\":\"" (app-json-esc (math-latex (step-after st))) "\","
     "\"after_text\":\"" (app-json-esc (math-print (step-after st))) "\""
     sub "}")))

(define (app-steps-json src level)
  (let* ((cap (capture-step-log (lambda () (math-eval src)) level))
         (ss (app-steps-nonempty (cadr cap))))
    (string-append "{\"steps\":["
                   (let loop ((xs ss) (acc "") (first #t))
                     (if (null? xs) acc
                         (loop (cdr xs)
                               (string-append acc (if first "" ",") (app-step-json (car xs)))
                               #f)))
                   "]}")))
