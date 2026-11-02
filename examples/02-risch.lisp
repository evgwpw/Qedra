; Алгоритм Риша: найденная первообразная и ДОКАЗАННАЯ неэлементарность.
; (risch-nonelementary? f x): #t — доказано, что элементарной первообразной нет;
; #f — первообразная найдена; unknown — алгоритм не решил (не «нет», а «не знаю»).
(define (show-case f)
  (display f)
  (display "  ->  ")
  (display (risch-nonelementary? f 'x))
  (newline))

(show-case '(exp (^ x 2)))          ; интеграл ошибок — неэлементарен
(show-case '(/ (exp x) x))          ; интегральная показательная функция Ei
(show-case '(/ 1 (log x)))          ; логарифмический интеграл li
(show-case '(^ x x))
(show-case '(/ (sin x) x))          ; интегральный синус Si
(show-case '(* x (exp (^ x 2))))    ; есть первообразная exp(x²)/2

; Первообразная, найденная Ришем, и проверка дифференцированием
(define f '(+ (exp x) (* x (exp x))))
(define F (risch-integrate f 'x))
(display F) (newline)
(display (simplify (- (diff 'x F) f))) (newline)
