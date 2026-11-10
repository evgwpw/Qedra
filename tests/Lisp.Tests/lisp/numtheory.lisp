; numtheory.lisp — тесты шага NT.1: модулярная арифметика, КТО, простые числа, факторизация.
; Каждый сертификат проверяется ещё и «на подделку»: приватные предикаты numtheory::nt-…-ok?
; должны отвергать испорченное значение (ложный корень, неверный множитель, не минимальный порядок).
; Контрольные значения посчитаны независимой проверкой.

; ---------- помощники ----------

; произведение p1^k1 · … по разложению (для ручной проверки сертификата факторизации)
(define (ntt-prod fac)
  (foldl (lambda (acc pk) (* acc (^ (car pk) (cadr pk)))) 1 fac))

; ---------- powmod ----------

(deftest "numtheory: powmod — степени по модулю"
  (assert-equal (powmod 3 12345 1000000007) 964676307)
  (assert-equal (powmod 2 10 1000) 24)
  (assert-equal (powmod 7 0 13) 1)
  (assert-equal (powmod 5 3 1) 0)
  (assert-equal (powmod -2 3 5) 2)                       ; (−2)³ = −8 ≡ 2 (mod 5)
  (assert-equal (powmod 2 100 1000000007) (powmod 4 50 1000000007))
  (assert-equal (powmod 2 1000000000000000009 1000000007) 371842544)   ; показатель 10¹⁸+9
  (assert-error (powmod 2 -1 7))
  (assert-error (powmod 2 3 0))
  (assert-error (powmod 2 1/2 7)))

; ---------- invmod, egcd ----------

(deftest "numtheory: invmod — обратный по модулю"
  (assert-equal (invmod 3 11) 4)
  (assert-equal (invmod 2 1000000007) 500000004)
  (assert-equal (modulo (* 3 (invmod 3 1000000007)) 1000000007) 1)
  (assert-equal (invmod 1000000006 1000000007) 1000000006)   ; (−1)⁻¹ = −1
  (assert-equal (invmod -3 11) 7)                            ; (−3)⁻¹ ≡ 8⁻¹ = 7
  (assert-equal (invmod 5 1) 0)
  (assert-equal (invmod 6 9) #f)                             ; не взаимно просты
  (assert-equal (invmod 0 5) #f)
  (assert-error (invmod 3 0)))

(deftest "numtheory: egcd — s·a + t·b = g"
  (assert-equal (egcd 240 46) '(2 -9 47))
  (assert-equal (egcd 46 240) '(2 47 -9))
  (assert-equal (egcd 0 0) '(0 1 0))
  (assert-equal (egcd 0 5) '(5 0 1))
  (let ((e (egcd -240 46)))
    (assert-equal (car e) 2)
    (assert-true (numtheory::nt-egcd-ok? -240 46 (car e) (cadr e) (caddr e))))
  (let ((e (egcd -240 -46)))
    (assert-equal (car e) 2)
    (assert-true (numtheory::nt-egcd-ok? -240 -46 (car e) (cadr e) (caddr e))))
  (assert-equal (egcd 17 5) '(1 -2 7))        ; −2·17 + 7·5 = 1
  (assert-error (egcd 1/2 3)))

(deftest "numtheory: сертификат egcd отвергает подделку"
  (assert-true (numtheory::nt-egcd-ok? 240 46 2 -9 47))
  (assert-equal (numtheory::nt-egcd-ok? 240 46 2 -9 46) #f)     ; неверный t: тождество не выполнено
  (assert-equal (numtheory::nt-egcd-ok? 240 46 2 47 -9) #f)     ; коэффициенты перепутаны
  (assert-equal (numtheory::nt-egcd-ok? 240 46 4 -9 47) #f)     ; g не равно 2
  (assert-equal (numtheory::nt-egcd-ok? 4 6 1 1 0) #f))         ; g = 1 не делит ни 4, ни 6

; ---------- символ Якоби ----------

(deftest "numtheory: jacobi — символ Якоби"
  (assert-equal (jacobi 2 7) 1)
  (assert-equal (jacobi 3 7) -1)
  (assert-equal (jacobi 1001 9907) -1)
  (assert-equal (jacobi 2 15) 1)
  (assert-equal (jacobi 5 21) 1)
  (assert-equal (jacobi 7 7) 0)
  (assert-equal (jacobi 5 1) 1)
  (assert-equal (jacobi -1 3) -1)
  (assert-equal (jacobi 1000000006 1000000007) -1)          ; p ≡ 3 (mod 4): (p−1/p) = −1
  (assert-error (jacobi 3 4))
  (assert-error (jacobi 3 -5)))

(deftest "numtheory: сертификат Якоби (критерий Эйлера) отвергает подделку"
  (assert-true (numtheory::nt-jacobi-euler-ok? 3 7 -1))
  (assert-true (numtheory::nt-jacobi-euler-ok? 2 7 1))
  (assert-true (numtheory::nt-jacobi-euler-ok? 2 1000000007 1))
  (assert-equal (numtheory::nt-jacobi-euler-ok? 3 7 1) #f)          ; знак подменён
  (assert-equal (numtheory::nt-jacobi-euler-ok? 2 7 -1) #f)
  (assert-equal (numtheory::nt-jacobi-euler-ok? 7 7 0) #t))

; ---------- sqrtmod ----------

(deftest "numtheory: sqrtmod — Тонелли–Шенкс"
  (assert-equal (sqrtmod 2 1000000007) 59713600)             ; p ≡ 3 (mod 4)
  (assert-equal (sqrtmod 3 1000000009) 257526493)            ; p ≡ 1 (mod 4) — Тонелли–Шенкс
  (assert-equal (sqrtmod 4 1000000009) 2)
  (assert-equal (sqrtmod 2 7) 3)
  (assert-equal (sqrtmod 0 7) 0)
  (assert-equal (sqrtmod 3 7) #f)                            ; невычет — корня нет
  (assert-equal (sqrtmod 0 2) 0)                             ; p = 2
  (assert-equal (sqrtmod 1 2) 1)
  (assert-equal (sqrtmod 1000000009 1000000009) 0)
  (assert-equal (sqrtmod (+ 2 1000000007) 1000000007) 59713600)  ; a приводится по модулю p
  (assert-equal (modulo (* 59713600 59713600) 1000000007) 2)     ; проверка квадратом
  (assert-equal (modulo (* 257526493 257526493) 1000000009) 3)
  (assert-error (sqrtmod 3 15))                              ; составной модуль
  (assert-error (sqrtmod 3 1)))

(deftest "numtheory: сертификат sqrtmod отвергает ложный корень"
  (assert-true (numtheory::nt-sqrt-root? 2 1000000007 59713600))
  (assert-true (numtheory::nt-sqrt-root? 2 1000000007 940286407))   ; второй корень тоже годится
  (assert-equal (numtheory::nt-sqrt-root? 2 1000000007 59713601) #f)     ; не корень
  (assert-equal (numtheory::nt-sqrt-root? 2 1000000007 100059713600) #f) ; корень, увеличенный на p
  (assert-equal (numtheory::nt-sqrt-root? 2 1000000007 -59713600) #f)    ; отрицательный
  (assert-equal (numtheory::nt-sqrt-root? 3 7 3) #f))                    ; 3² = 2 ≠ 3 (mod 7)

; ---------- китайская теорема об остатках ----------

(deftest "numtheory: crt — решение проверяется подстановкой"
  (assert-equal (crt '(1 3) '(4 6)) '(9 12))                 ; модули не взаимно просты
  (assert-equal (crt '(2 3 2) '(3 5 7)) '(23 105))
  (assert-equal (crt '(0 4) '(4 8)) '(4 8))
  (assert-equal (crt '(3) '(5)) '(3 5))
  (assert-equal (crt '(1 1) '(1 1)) '(0 1))
  (assert-equal (crt '() '()) '(0 1))
  (assert-true (numtheory::nt-crt-ok? '(1 3) '(4 6) 9 12))
  (assert-true (numtheory::nt-crt-ok? '(2 3 2) '(3 5 7) 23 105))
  ; подстановка вручную: 23 ≡ 2 (mod 3), ≡ 3 (mod 5), ≡ 2 (mod 7)
  (assert-equal (modulo (- 23 2) 3) 0)
  (assert-equal (modulo (- 23 3) 5) 0)
  (assert-equal (modulo (- 23 2) 7) 0)
  (assert-error (crt '(1 2) '(3))))

(deftest "numtheory: crt — несовместная система отвергается"
  (assert-equal (crt '(0 1) '(4 6)) #f)
  (assert-equal (crt '(1 2) '(2 4)) #f)
  (assert-equal (crt '(0 0 1) '(2 3 6)) #f)
  (assert-equal (crt '(5 0) '(6 4)) #f)
  ; подделка решения: x вне [0, M) и неверный M
  (assert-equal (numtheory::nt-crt-ok? '(1 3) '(4 6) 21 12) #f)
  (assert-equal (numtheory::nt-crt-ok? '(1 3) '(4 6) 9 24) #f)
  (assert-equal (numtheory::nt-crt-ok? '(1 3) '(4 6) 10 12) #f))

; ---------- функция Эйлера, делители ----------

(deftest "numtheory: totient"
  (assert-equal (totient 1) 1)
  (assert-equal (totient 2) 1)
  (assert-equal (totient 9) 6)
  (assert-equal (totient 97) 96)
  (assert-equal (totient 1000000) 400000)
  (assert-equal (totient (- (^ 2 67) 1)) 147573951827644447920)
  (assert-error (totient 0))
  (assert-error (totient -5)))

(deftest "numtheory: divisors — делители по возрастанию"
  (assert-equal (divisors 1) '(1))
  (assert-equal (divisors 2) '(1 2))
  (assert-equal (divisors 97) '(1 97))
  (assert-equal (divisors 360)
                '(1 2 3 4 5 6 8 9 10 12 15 18 20 24 30 36 40 45 60 72 90 120 180 360))
  (assert-equal (divisors -360) (divisors 360))
  (assert-equal (length (divisors (^ 2 10))) 11)
  (assert-equal (last (divisors 1000000)) 1000000)
  (assert-error (divisors 0))
  (assert-error (divisors 1/2)))

; ---------- порядок и первообразный корень ----------

(deftest "numtheory: order — мультипликативный порядок"
  (assert-equal (order 1 5) 1)
  (assert-equal (order 2 7) 3)
  (assert-equal (order 3 7) 6)
  (assert-equal (order 2 15) 4)
  (assert-equal (order 10 21) 6)
  (assert-equal (order -1 7) 2)
  (assert-equal (order 2 1000000007) 500000003)
  (assert-equal (order 5 1000000007) 1000000006)     ; 5 — первообразный корень
  (assert-equal (order 2 4) #f)                      ; не взаимно просты
  (assert-equal (order 0 5) #f)
  (assert-equal (order 3 1) #f))

(deftest "numtheory: сертификат порядка отвергает не минимальный порядок"
  (assert-true (numtheory::nt-order-ok? 2 7 3))
  (assert-equal (numtheory::nt-order-ok? 2 7 6) #f)   ; 2⁶ ≡ 1, но 2³ ≡ 1 — порядок не минимален
  (assert-equal (numtheory::nt-order-ok? 2 7 2) #f)   ; 2² ≢ 1
  (assert-equal (numtheory::nt-order-ok? 2 7 0) #f))

(deftest "numtheory: primitive-root"
  (assert-equal (primitive-root 2) 1)
  (assert-equal (primitive-root 3) 2)
  (assert-equal (primitive-root 7) 3)
  (assert-equal (primitive-root 1000000007) 5)
  (assert-equal (primitive-root 2147483647) 7)       ; 2³¹ − 1
  (assert-equal (primitive-root 15) #f)              ; не простое
  (assert-equal (primitive-root 561) #f)             ; кармайклово число
  (assert-true (numtheory::nt-primitive-ok? 3 7))
  (assert-true (numtheory::nt-primitive-ok? 5 1000000007)))

(deftest "numtheory: сертификат первообразного корня отвергает подделку"
  (assert-true (numtheory::nt-primitive-ok? 3 7))
  (assert-equal (numtheory::nt-primitive-ok? 2 7) #f)        ; 2³ ≡ 1 — порядок меньше p−1
  (assert-equal (numtheory::nt-primitive-ok? 1 7) #f)
  (assert-equal (numtheory::nt-primitive-ok? 4 7) #f))

; ---------- простота ----------

(deftest "numtheory: prime? — простые, составные и кармайкловы числа"
  (assert-equal (prime? 2) #t)
  (assert-equal (prime? 3) #t)
  (assert-equal (prime? 97) #t)
  (assert-equal (prime? 997) #t)
  (assert-equal (prime? 1000000007) #t)
  (assert-equal (prime? 1000000009) #t)
  (assert-equal (prime? 2147483647) #t)                 ; 2³¹ − 1
  (assert-equal (prime? 1000000000000000009) #t)        ; 10¹⁸ + 9
  (assert-equal (prime? 151) #t)
  (assert-equal (prime? 751) #t)
  (assert-equal (prime? 0) #f)
  (assert-equal (prime? 1) #f)
  (assert-equal (prime? -7) #f)
  (assert-equal (prime? 4) #f)
  (assert-equal (prime? 561) #f)                        ; кармайклово
  (assert-equal (prime? 1105) #f)                       ; кармайклово
  (assert-equal (prime? 41041) #f)                      ; кармайклово
  (assert-equal (prime? 3215031751) #f)                 ; сильно псевдопростое по базам 2,3,5,7
  (assert-equal (prime? 25326001) #f)                   ; псевдопростое по базам 2,3,5
  (assert-equal (prime? (- (^ 2 67) 1)) #f)
  (assert-equal (prime? (* 100000000000000000039 1000000000000000009)) #f)
  (assert-error (prime? 1/2)))

(deftest "numtheory: prime? выше 3.3·10^24 — вероятностный ответ с пометкой"
  ; 2⁸⁹ − 1 — простое Мерсенна; ответ выше границы детерминированности баз, поэтому пишется условие
  (let ((r (capture-conditions (lambda () (prime? (- (^ 2 89) 1))))))
    (assert-equal (car r) #t)
    (assert-true (assoc (list 'probable-prime (- (^ 2 89) 1)) (cadr r))))
  ; ниже границы пометки нет
  (let ((r (capture-conditions (lambda () (prime? 1000000000000000009)))))
    (assert-equal (car r) #t)
    (assert-equal (cadr r) '()))
  (assert-equal (prime? 10000000000000000000000013) #t)  ; 10²⁵ + 13 — простое, выше границы
  (assert-equal (prime? 10000000000000000000000007) #f)) ; 10²⁵ + 7 = 544667 · 18359841885041686021

(deftest "numtheory: next-prime"
  (assert-equal (next-prime -5) 2)
  (assert-equal (next-prime 0) 2)
  (assert-equal (next-prime 1) 2)
  (assert-equal (next-prime 2) 3)
  (assert-equal (next-prime 100) 101)
  (assert-equal (next-prime 1000) 1009)
  (assert-equal (next-prime 1000000000) 1000000007)
  (assert-true (prime? (next-prime 1000000000000000009)))
  (assert-error (next-prime 1/2)))

(deftest "numtheory: primes-up-to — решето"
  (assert-equal (primes-up-to -3) '())
  (assert-equal (primes-up-to 0) '())
  (assert-equal (primes-up-to 1) '())
  (assert-equal (primes-up-to 2) '(2))
  (assert-equal (primes-up-to 30) '(2 3 5 7 11 13 17 19 23 29))
  (assert-equal (length (primes-up-to 1000)) 168)
  (assert-equal (length (primes-up-to 10000)) 1229)
  (assert-equal (length (primes-up-to 100000)) 9592)
  (assert-true (every? (lambda (p) (prime? p)) (primes-up-to 1000)))
  (assert-equal (last (primes-up-to 30)) 29))

; ---------- факторизация ----------

(deftest "numtheory: factor-integer — 2^67−1 = 193707721·761838257287"
  (let ((n (- (^ 2 67) 1)))
    (assert-equal n 147573952589676412927)
    (assert-equal (factor-integer n) '((193707721 1) (761838257287 1)))
    (assert-equal (* 193707721 761838257287) n)
    (assert-true (prime? 193707721))
    (assert-true (prime? 761838257287))
    (assert-equal (prime? n) #f)
    (assert-true (numtheory::nt-factor-ok? (factor-integer n) n))
    (assert-equal (ntt-prod (factor-integer n)) n)))

(deftest "numtheory: factor-integer — большие числа (≥ 10^20)"
  (assert-equal (factor-integer 1000000000000000009) '((1000000000000000009 1)))
  (assert-equal (factor-integer 100000000000000000039) '((100000000000000000039 1)))
  (assert-equal (factor-integer (^ 10 20)) '((2 20) (5 20)))
  ; ρ Полларда находит множитель 544667 у 10²⁵ + 7 (пробное деление до 1000 его не видит)
  (assert-equal (factor-integer 10000000000000000000000007)
                '((544667 1) (18359841885041686021 1)))
  (assert-true (numtheory::nt-factor-ok? (factor-integer 10000000000000000000000007)
                                         10000000000000000000000007)))

(deftest "numtheory: factor-integer — вырожденные случаи"
  (assert-equal (factor-integer 1) '())
  (assert-equal (factor-integer 2) '((2 1)))
  (assert-equal (factor-integer -1) '((-1 1)))
  (assert-equal (factor-integer -2) '((-1 1) (2 1)))
  (assert-equal (factor-integer -360) '((-1 1) (2 3) (3 2) (5 1)))
  (assert-equal (factor-integer (- (- (^ 2 67) 1)))
                '((-1 1) (193707721 1) (761838257287 1)))
  (assert-error (factor-integer 0))
  (assert-error (factor-integer 1/2)))

(deftest "numtheory: сертификат факторизации отвергает подделку"
  (assert-true (numtheory::nt-factor-ok? '((2 3) (3 2) (5 1)) 360))
  (assert-true (numtheory::nt-factor-ok? '() 1))
  (assert-equal (numtheory::nt-factor-ok? '((2 2) (3 2) (5 1)) 360) #f)   ; произведение 180 ≠ 360
  (assert-equal (numtheory::nt-factor-ok? '((2 3) (3 2) (5 2)) 360) #f)   ; лишний множитель
  (assert-equal (numtheory::nt-factor-ok? '((4 1) (5 1)) 20) #f)          ; 4 — не простое
  (assert-equal (numtheory::nt-factor-ok? '((360 1)) 360) #f)             ; 360 — не простое
  (assert-equal (numtheory::nt-factor-ok? '((2 3) (3 2)) 360) #f)         ; множитель 5 потерян
  (assert-equal (numtheory::nt-factor-ok? '((2 3) (3 2) (5 1)) 361) #f))

; ---------- NT.2: сертификаты простоты Пратта ----------

(deftest "NT.2: сертификаты Пратта — проверка, флаг и подделки"
  (map (lambda (n)
         (let ((c (pratt-certificate n)))
           (assert-equal (car c) n)
           (assert-true (pratt-check c))))
       '(2147483647 1000000007 2305843009213693951))
  (assert-true (pratt-check (prime? 2147483647 :certificate)))
  (assert-equal (prime? 561 :certificate) #f)
  (assert-equal (prime? 2 :certificate) '(2 1 ()))
  ; подделки: неверный свидетель, пропущенный q, составное q внутри, сертификат для 561
  (let* ((c (pratt-certificate 2147483647))
         (subs (nth c 2)))
    (assert-equal (pratt-check (list (nth c 0) 1 subs)) #f)
    (assert-equal (pratt-check (list (nth c 0) (nth c 1) (cdr subs))) #f)
    (assert-equal (pratt-check
                   (list (nth c 0) (nth c 1)
                         (cons (list (car (car subs)) '(561 2 ())) (cdr subs))))
                  #f))
  (assert-equal (pratt-check '(561 2 ())) #f)
  (assert-equal (pratt-check '(2 1 ())) #t))

; ---------- NT.4: линейное диофантово уравнение ----------

(deftest "NT.4: solve-linear-diophantine — общее решение"
  (assert-equal (solve-linear-diophantine 3 5 7) '((4 -1) (5 -3)))
  (assert-equal (solve-linear-diophantine 6 9 15) '((1 1) (3 -2)))
  (assert-equal (solve-linear-diophantine 0 5 15) '((0 3) (1 0)))
  (assert-equal (solve-linear-diophantine 5 0 15) '((3 0) (0 -1)))
  (assert-equal (solve-linear-diophantine -3 5 7) '((1 2) (5 3)))
  (assert-equal (solve-linear-diophantine 6 9 4) #f)
  (assert-equal (solve-linear-diophantine 0 0 5) #f)
  (assert-error (solve-linear-diophantine 0 0 0))
  (assert-error (solve-linear-diophantine 1/2 3 4))
  ; подстановка k = 0, 1, −2, 100 в общее решение
  (let ((s (solve-linear-diophantine 3 5 7)))
    (map (lambda (k)
           (assert-equal (+ (* 3 (+ (car (car s)) (* (car (cadr s)) k)))
                            (* 5 (+ (cadr (car s)) (* (cadr (cadr s)) k))))
                         7))
         '(0 1 -2 100)))
  ; сертификат и подделки
  (assert-true (numtheory::nt-dio-ok? 3 5 7 4 -1 5 -3))
  (assert-equal (numtheory::nt-dio-ok? 3 5 7 4 -2 5 -3) #f)
  (assert-equal (numtheory::nt-dio-ok? 3 5 7 4 -1 5 -2) #f)
  (assert-equal (numtheory::nt-dio-ok? 3 5 7 1 2 10 -6) #f))

; ---------- NT.4: уравнение Пелля ----------

(deftest "NT.4: pell — фундаментальное решение x² − D·y² = 1"
  (assert-equal (pell 2) '(3 2))
  (assert-equal (pell 3) '(2 1))
  (assert-equal (pell 5) '(9 4))
  (assert-equal (pell 13) '(649 180))
  (assert-equal (pell 61) '(1766319049 226153980))
  (assert-equal (pell 109) '(158070671986249 15140424455100))
  (assert-equal (- (* 1766319049 1766319049) (* 61 226153980 226153980)) 1)
  (assert-equal (- (* 158070671986249 158070671986249)
                   (* 109 15140424455100 15140424455100))
                1)
  (assert-equal (pell 4) #f)
  (assert-equal (pell 1) #f)
  (assert-equal (pell 0) #f)
  (assert-error (pell 1/2))
  ; подделки: неверный x, решение отрицательного уравнения, нулевой y
  (assert-true (numtheory::nt-pell-ok? 61 1766319049 226153980))
  (assert-equal (numtheory::nt-pell-ok? 61 1766319048 226153980) #f)
  (assert-equal (numtheory::nt-pell-ok? 2 1 1) #f)
  (assert-equal (numtheory::nt-pell-ok? 61 1766319049 0) #f))

(deftest "NT.4: pell-negative — есть ли x² − D·y² = −1"
  (assert-equal (pell-negative 2) '(1 1))
  (assert-equal (pell-negative 5) '(2 1))
  (assert-equal (pell-negative 10) '(3 1))
  (assert-equal (pell-negative 13) '(18 5))
  (assert-equal (pell-negative 3) #f)
  (assert-equal (pell-negative 6) #f)
  (assert-equal (pell-negative 4) #f)
  (assert-equal (pell-negative 0) #f)
  (assert-true (numtheory::nt-pell-neg-ok? 2 1 1))
  (assert-equal (numtheory::nt-pell-neg-ok? 2 3 2) #f)
  (assert-equal (numtheory::nt-pell-neg-ok? 13 18 4) #f))

(deftest "NT.4: pell-solutions — степени фундаментальной единицы"
  (assert-equal (pell-solutions 2 5) '((3 2) (17 12) (99 70) (577 408) (3363 2378)))
  (assert-equal (pell-solutions 2 0) '())
  (assert-equal (pell-solutions 4 3) #f)
  (assert-true (every? (lambda (p) (= (- (* (car p) (car p)) (* 61 (cadr p) (cadr p))) 1))
                       (pell-solutions 61 4)))
  (assert-equal (car (pell-solutions 61 2)) '(1766319049 226153980))
  (assert-error (pell-solutions 2 1/2)))

; ---------- NT.4: сумма двух квадратов ----------

(deftest "NT.4: sum-of-two-squares — по разложению и Корнаккии"
  (assert-equal (sum-of-two-squares 2210) '(41 23))          ; 2·5·13·17
  (assert-equal (+ (* 41 41) (* 23 23)) 2210)
  (assert-equal (sum-of-two-squares 5) '(2 1))
  (assert-equal (sum-of-two-squares 25) '(4 3))
  (assert-equal (sum-of-two-squares 9) '(3 0))
  (assert-equal (sum-of-two-squares 2205) '(42 21))          ; 3²·7²·5
  (assert-equal (sum-of-two-squares 1) '(1 0))
  (assert-equal (sum-of-two-squares 0) '(0 0))
  (assert-equal (sum-of-two-squares 3) #f)
  (assert-equal (sum-of-two-squares 21) #f)                  ; 3·7 — нечётные кратности
  (assert-equal (sum-of-two-squares -5) #f)
  (let ((r (sum-of-two-squares (^ 10 6))))                    ; 10⁶ = 936² + 352²
    (assert-equal (+ (* (car r) (car r)) (* (cadr r) (cadr r))) (^ 10 6)))
  (assert-true (numtheory::nt-two-sq-ok? 2210 41 23))
  (assert-true (numtheory::nt-two-sq-ok? 2210 47 1))
  (assert-equal (numtheory::nt-two-sq-ok? 2210 41 22) #f)
  (assert-equal (numtheory::nt-two-sq-ok? 2210 -41 23) #f)
  (assert-error (sum-of-two-squares 1/2)))

; ---------- NT.4: пифагоровы тройки ----------

(deftest "NT.4: pythagorean-triples — примитивные тройки по формуле Евклида"
  (assert-equal (pythagorean-triples 30)
                '((3 4 5) (5 12 13) (8 15 17) (7 24 25) (20 21 29)))
  (assert-equal (pythagorean-triples 4) '())
  (assert-equal (length (pythagorean-triples 100)) 16)
  (let ((ts (pythagorean-triples 1000)))
    (assert-true (every? (lambda (t) (<= (caddr t) 1000)) ts))
    (assert-true (every? (lambda (t) (numtheory::nt-pyth-ok? (car t) (cadr t) (caddr t))) ts))
    (assert-true (every? (lambda (t) (< (car t) (cadr t))) ts)))
  (assert-true (numtheory::nt-pyth-ok? 3 4 5))
  (assert-equal (numtheory::nt-pyth-ok? 3 4 6) #f)
  (assert-equal (numtheory::nt-pyth-ok? 6 8 10) #f)          ; не примитивная тройка
  (assert-error (pythagorean-triples 1/2)))
