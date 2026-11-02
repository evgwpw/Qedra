; d1: чистый Lisp — fib 25
(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(fib 25)
