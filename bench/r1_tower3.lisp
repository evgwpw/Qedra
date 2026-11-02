; r1: Риш, башни высоты 3
(risch-integrate '(* (exp x) (exp (exp x)) (exp (exp (exp x)))) 'x)
(risch-integrate '(/ 1 (* x (log x) (log (log x)))) 'x)
(risch-integrate '(/ -1 (* x (log x) (^ (log (log x)) 2))) 'x)
(risch-integrate '(* (exp x) (exp (exp x)) (exp (* 2 (exp (exp x))))) 'x)
(risch-integrate '(exp (+ x (exp x) (exp (exp x)))) 'x)
(risch-integrate '(/ (log (log (log x))) (* x (log x) (log (log x)))) 'x)
(risch-integrate '(* (exp x) (exp (exp x)) (log x)) 'x)
