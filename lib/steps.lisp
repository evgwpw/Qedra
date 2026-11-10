; steps.lisp — пошаговые решения (шаг S.1): рамки with-step, печать steps, доступ к полям шага.
; Механизм — F# (StepLog.fs в Cas.Algebra; builtins record-step, call-with-step, capture-step-log, steps-text в
; AlgoBuiltins.fs). Правила для авторов шагов — docs\lisp-library-guide.md §4 «Журнал шагов».
;
; Шаг — список (rule title comment before after level children omitted):
;   rule     — символ, стабильный английский идентификатор приёма (kebab-case: integration-by-parts)
;   title    — заголовок по-русски («Интегрирование по частям»), comment — пояснение по-русски (может быть "");
;              английский — (steps-translate 'en шаги), словарь src\Cas.Algebra\StepDict.fs (шаг S.5)
;   before/after — выражения до и после, level — main | detail, children — вложенные шаги,
;   omitted  — сколько вложенных шагов скрыто обрезкой при выдаче (0 — ничего)

; with-step и steps — макросы: раскрываются в области вызывающего, поэтому steps-call экспортирован
(module steps
  (export with-step steps steps-call explain explain-call step-rule step-title step-comment step-before
          step-after step-level step-children step-omitted step-rules step-find))

; значение ключа :ключ в списке опций (:comment c :level l :after f) или #f
(define (steps-opt key opts)
  (cond ((or (null? opts) (null? (cdr opts))) #f)
        ((equal? (car opts) key) (cadr opts))
        (else (steps-opt key (cddr opts)))))

(define (steps-check-opts opts)
  (cond ((null? opts) #t)
        ((or (null? (cdr opts)) (not (member? (car opts) '(:comment :level :after))))
         (error "with-step: опции — :comment пояснение, :level 'main|'detail, :after функция; получено" opts))
        (else (steps-check-opts (cddr opts)))))

; (with-step (rule заголовок до [:comment пояснение] [:level 'detail] [:after f]) тело...) — рамка шага.
; Шаги, записанные в теле, становятся вложенными; «после» — значение тела (или (f значение)); пояснение — строка
; или функция значения → строка. Тело вернуло #f (неудача в каскаде) или ошибку — рамка отбрасывается вместе с
; вложенными шагами (неудачные попытки в журнал не попадают). При выключенном журнале rule, заголовок, «до» и
; опции НЕ вычисляются: тело просто выполняется.
(defmacro (with-step header &rest body)
  (if (or (not (list? header)) (< (length header) 3))
      (error "with-step: (with-step (rule заголовок до [:comment ...] [:level ...] [:after ...]) тело...)")
      (let ((opts (cdr (cddr header))))
        (steps-check-opts opts)
        `(let ((step%thunk (lambda () ,@body)))
           (if (step-log-enabled?)
               (call-with-step ,(car header) ,(cadr header) ,(caddr header) step%thunk
                               ,(steps-opt ':comment opts) ,(steps-opt ':level opts) ,(steps-opt ':after opts))
               (step%thunk))))))

; (steps выражение ['brief|'full|'trace ['ru|'en]]) — вычислить выражение с журналом, напечатать дерево шагов, вернуть
; значение. По умолчанию brief (главные шаги верхнего уровня), язык ru; 'en — заголовки и пояснения на английском
; (словарь StepDict, шаг S.5)
(define (steps-call thunk level lang)
  (let ((r (capture-step-log thunk level lang)))
    (display (steps-text (cadr r) (caddr r) lang))
    (newline)
    (car r)))

(defmacro (steps e &rest opts)
  `(steps-call (lambda () ,e) ,(if (null? opts) ''brief (car opts))
               ,(if (or (null? opts) (null? (cdr opts))) ''ru (cadr opts))))

; Шаг D2a: (explain выражение ['ru|'en]) — вычислить выражение с журналом и напечатать дерево ПОПЫТОК
; («стратегия — успех/отказ: причина — мс», повторы схлопываются «×N»), вернуть значение.
; В отличие от steps: показываются и неудачные рамки with-step (в steps они отбрасываются)
(define (explain-call thunk lang)
  (let ((r (capture-attempts thunk lang)))
    (display (attempts-text (cadr r) (caddr r) lang)) (newline)
    (car r)))

(defmacro (explain e &rest opts)
  `(explain-call (lambda () ,e) ,(if (null? opts) ''ru (car opts))))

; поля шага
(define (step-rule s) (car s))
(define (step-title s) (cadr s))
(define (step-comment s) (caddr s))
(define (step-before s) (nth s 3))
(define (step-after s) (nth s 4))
(define (step-level s) (nth s 5))
(define (step-children s) (nth s 6))
(define (step-omitted s) (if (> (length s) 7) (nth s 7) 0))

; (step-rules шаги) — rule всех шагов в порядке обхода (родитель, затем дети): эталон для тестов
(define (step-rules ss)
  (append-map (lambda (s) (cons (step-rule s) (step-rules (step-children s)))) ss))

; (step-find rule шаги) — первый шаг с данным rule (обход в глубину) или #f
(define (step-find rule ss)
  (if (null? ss)
      #f
      (let ((s (car ss)))
        (if (equal? (step-rule s) rule)
            s
            (let ((inner (step-find rule (step-children s))))
              (if inner inner (step-find rule (cdr ss))))))))
