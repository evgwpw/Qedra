; elliptic.lisp — головы эллиптических интегралов Лежандра (шаг A3′.3).
; Численные значения (Карлсон RF/RD, Π — квадратура) и производные по φ — в F#
; (SolveNum.numEval, Differentiate); здесь — конструкторы выражений, чтобы имена были
; доступны в Lisp и выражения оставались данными (simplify их не вычисляет).

(module elliptic
  (export elliptic-f elliptic-e elliptic-pi elliptic-k elliptic-ec))

(define (elliptic-f phi k) (list 'elliptic-f phi k))
; A3′.7: EllipticE(k) (полный интеграл, один аргумент) и EllipticE(φ,k)
(define (elliptic-e phi &rest k)
  (if (null? k) (list 'elliptic-e phi) (list 'elliptic-e phi (car k))))
(define (elliptic-pi n phi k) (list 'elliptic-pi n phi k))
(define (elliptic-k k) (list 'elliptic-k k))
(define (elliptic-ec k) (list 'elliptic-ec k))
