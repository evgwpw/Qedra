; logic.lisp — трёхзначная логика (Шаг 16)
;
; Значения: #t, #f и символ unknown (переменная unknown связана с этим символом).
; ВАЖНО: в обычном (if ...) / (cond ...) / (and ...) / (or ...) / (not ...) символ unknown ИСТИНЕН
; (истинно всё, кроме #f). Для трёхзначных предикатов (in?, subset?, real?, positive? ...)
; нужно писать (if (true? p) ...) — или пользоваться and3 / or3 / not3.
; Условные правила (defrule) срабатывают только при условии, равном ровно #t.

(module logic
  (export unknown true? false? known? not3 and3 or3 and3-all or3-all))

(define unknown 'unknown)

; (true? x) — #t только для #t; (false? x) — #t только для #f; (known? x) — значение определено
(define (true? x) (equal? x #t))
(define (false? x) (equal? x #f))
(define (known? x) (or (equal? x #t) (equal? x #f)))

; Клини (сильная трёхзначная логика). Всё, что не #t и не #f, считается неопределённым.
; (not3 x): #t ↔ #f, unknown остаётся unknown
(define (not3 x)
  (cond ((true? x) #f)
        ((false? x) #t)
        (else unknown)))

; (and3 a b ...): #f, если есть #f; иначе #t, если все #t; иначе unknown. (and3) = #t
(define (and3-from xs acc)
  (cond ((null? xs) acc)
        ((false? (car xs)) #f)
        ((true? (car xs)) (and3-from (cdr xs) acc))
        (else (and3-from (cdr xs) unknown))))
(define (and3 &rest xs) (and3-from xs #t))

; (or3 a b ...): #t, если есть #t; иначе #f, если все #f; иначе unknown. (or3) = #f
(define (or3-from xs acc)
  (cond ((null? xs) acc)
        ((true? (car xs)) #t)
        ((false? (car xs)) (or3-from (cdr xs) acc))
        (else (or3-from (cdr xs) unknown))))
(define (or3 &rest xs) (or3-from xs #f))

; (and3-all список), (or3-all список) — то же над списком значений
(define (and3-all xs) (and3-from xs #t))
(define (or3-all xs) (or3-from xs #f))
