; a1: упрощение с доменами и правилами — assuming с несколькими декларациями,
; simplify крупного выражения с abs / sqrt / степенями / log-exp
(define (a-term i)
  (list '+
        (list '* i (list 'abs (list '+ 'x (list '* i 'y))))
        (list 'sqrt (list '^ (list '+ 'z i) 2))
        (list '^ (list '^ 'w 2) 1/2)
        (list 'log (list 'exp (list '* i 'x)))))
(define a-expr (cons '+ (map a-term (range 25))))
(assuming ((x positive) (y reals positive) (z reals) (w nonnegative))
  (simplify a-expr))
