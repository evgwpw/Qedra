; Пример 13: динамическое программирование с сертификатами (шаг DP.1).
; Каждая задача возвращает (значение решение таблица) и проверяет себя своим …-check;
; здесь печатаем только значение/ответ, чтобы пример был коротким.

(display "рюкзак: ")
(display (car (knapsack '(2 3 4 5 9 7) '(3 4 5 8 10 7) 15)))
(newline)

(display "LCS: ")
(display (car (lcs '(A B C B D A B) '(B D C A B A))))
(newline)

(display "Левенштейн: ")
(display (car (edit-distance '(K I T T E N) '(S I T T I N G))))
(newline)

(display "размен: ")
(display (car (coin-change '(1 5 10 25) 63)))
(newline)

(display "способы: ")
(display (car (coin-ways '(1 2 5) 5)))
(newline)

(display "потенциалы: ")
(display (shortest-paths '(a b c d) '((a b 4) (a c 5) (b c -3) (c d 2)) 'a))
(newline)

(display "Фибоначчи(60): ")
(defmemo (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(display (fib 60))
(newline)
