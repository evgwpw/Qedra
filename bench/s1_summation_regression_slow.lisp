; s1: регрессия символьного суммирования (шаг 21l) по эталонным задачам
; (§2 Госпер, §3/§5 «A = B», §6 многочлены/геометрические, §8 Цайльбергер, product — §6).
; Запуск: src/Lisp.Host/bin/Debug/net10.0/Lisp.exe bench/s1_summation_regression_slow.lisp
; Классы: S — замкнутая форма, проверена оракулом (прямой счёт в целых точках, sum-check-how/product-check-how = numeric);
; N — рекуррентность (Цайльбергер без гипергеометрических решений; ответ — рекуррентность);
; U — не вычислено (невычисленная форма sum/product без претензии на ответ);
; W — ответ не проходит проверку оракулом (WRONG; должно быть 0).
; Ожидание — строка допустимых классов; несоответствие и любой W печатаются с ***.

; (метка тело k lo hi ожидание вид) — вид: sum | product
(define s1-cases
  '(
    ; --- §2: Госпер, gosper_sum [эталон] ---
    ("Σ1" 1 k 0 n "S" sum)
    ("Σk" k k 0 n "S" sum)
    ("Σk^2" (^ k 2) k 0 n "S" sum)
    ("Σk^3" (^ k 3) k 0 n "S" sum)
    ("Σ2^k" (^ 2 k) k 0 n "S" sum)
    ("Σk!" (factorial k) k 0 n "U" sum)                       ; None
    ("ΣC(n,k) по k (Госпер)" (C n k) k 0 n "S" sum)           ; Цайльбергер: 2^n
    ("Σk!/k^2" (/ (factorial k) (^ k 2)) k 0 n "U" sum)       ; None
    ("Σ(k-3)k!" (* (- k 3) (factorial k)) k 0 n "U" sum)      ; None
    ("Σk·k!" (* k (factorial k)) k 0 n "S" sum)               ; (n+1)! − 1
    ("Σ(-1)^k C(n,k)" (* (^ -1 k) (C n k)) k 0 n "SN" sum)    ; 0; rsolve не решает нулевое — честная рекуррентность (21l.8)
    ; --- §3: «A = B» часть 1 [эталон] ---
    ("1a n^4" (^ n 4) n 0 m "S" sum)
    ("1b n^3 2^n" (* (^ n 3) (^ 2 n)) n 0 m "S" sum)
    ("1d n^4 4^n/C(2n,n)" (/ (* (^ n 4) (^ 4 n)) (C (* 2 n) n)) n 0 m "SU" sum)
    ("1e (3n)!/(n!(n+1)!(n+2)!27^n)" (/ (factorial (* 3 n)) (* (factorial n) (factorial (+ n 1)) (factorial (+ n 2)) (^ 27 n))) n 0 m "S" sum)
    ("1f C(2n,n)^2/((n+1)4^{2n})" (/ (^ (C (* 2 n) n) 2) (* (+ n 1) (^ 4 (* 2 n)))) n 0 m "SU" sum)
    ("1g (4n-1)C(2n,n)^2/((2n-1)^2 4^{2n})" (/ (* (- (* 4 n) 1) (^ (C (* 2 n) n) 2)) (* (^ (- (* 2 n) 1) 2) (^ 4 (* 2 n)))) n 0 m "SU" sum)
    ; --- §5: «A = B» часть 3 (рациональные) ---
    ("3a 1/n^4" (^ n -4) n 1 m "SU" sum)                      ; None по Госперу; harmonic — тоже верно
    ("3b (6n+3)/(4n^4+8n^3+8n^2+4n+3)" (/ (+ (* 6 n) 3) (+ (* 4 (^ n 4)) (* 8 (^ n 3)) (* 8 (^ n 2)) (* 4 n) 3)) n 1 m "S" sum)
    ("3c 2^n(n^2-2n-1)/(n^2(n+1)^2)" (/ (* (^ 2 n) (- (^ n 2) (* 2 n) 1)) (* (^ n 2) (^ (+ n 1) 2))) n 1 (- m 1) "S" sum)
    ("3d n^2 4^n/((n+1)(n+2))" (/ (* (^ n 2) (^ 4 n)) (* (+ n 1) (+ n 2))) n 1 m "S" sum)
    ("3e 2^n/(n+1)" (/ (^ 2 n) (+ n 1)) n 0 (- m 1) "SU" sum) ; None по Госперу; ψ-форма верна
    ("3g (n^4-14n^2-24n-9)2^n/(n^2(n+1)^2(n+2)^2(n+3)^2)" (/ (* (- (^ n 4) (* 14 (^ n 2)) (* 24 n) 9) (^ 2 n)) (* (^ n 2) (^ (+ n 1) 2) (^ (+ n 2) 2) (^ (+ n 3) 2))) n 1 m "S" sum)
    ; --- §6: многочлены, геометрические, гармоники ---
    ("Σ1 (n,a,b)" 1 n a b "S" sum)
    ("Σn (n,1,b)" n n 1 b "S" sum)
    ("Σn^2 (n,1,b)" (^ n 2) n 1 b "S" sum)
    ("Σpi^n (0,b)" (^ pi n) n 0 b "S" sum)
    ("Σ2·3^n" (* 2 (^ 3 n)) n 0 b "S" sum)
    ("Σ1/k (k,1,n)" (/ 1 k) k 1 n "S" sum)                    ; harmonic(n)
    ("ΣC(2k,k)/4^k" (/ (C (* 2 k) k) (^ 4 k)) k 0 n "SU" sum)
    ("Σ1/k-1/(k+1)" (- (/ 1 k) (/ 1 (+ k 1))) k 1 n "S" sum)  ; n/(n+1)
    ("Σ1/x(x-1) (x,a,b)" (/ 1 (* x (- x 1))) x a b "S" sum)
    ("пустая Σ(x,1,0)" x x 1 0 "S" sum)
    ("Σ2^k(k=1,n)" (^ 2 k) k 1 n "S" sum)
    ; --- §7: Абрамов ---
    ("Σ1/k(k+1) (1,n)" (/ 1 (* k (+ k 1))) k 1 n "S" sum)     ; n/(n+1)
    ("Σ1/k(k+2) (1,n)" (/ 1 (* k (+ k 2))) k 1 n "S" sum)
    ("Σ1/k^2+1" (/ 1 (+ (^ k 2) 1)) k 1 n "U" sum)            ; NOT summable
    ("Σ1/k(2k+1)" (/ 1 (* k (+ (* 2 k) 1))) k 1 n "SU" sum)  ; psi-форма верна (наш ответ сильнее эталонного)
    ; --- §8: Цайльбергер / замкнутые формы ---
    ("ΣC(n,k)^2" (^ (C n k) 2) k 0 n "S" sum)                 ; C(2n,n)
    ("Дикон (-1)^k C(2n,k)^3" (* (^ -1 k) (^ (C (* 2 n) k) 3)) k 0 (* 2 n) "SU" sum)
    ("Апери C(n,k)^2 C(n+k,k)^2" (* (^ (C n k) 2) (^ (C (+ n k) k) 2)) k 0 n "N" sum) ; рекуррентность
    ("ΣC(n,k)x^k" (* (C n k) (^ x k)) k 0 n "SU" sum)         ; (x+1)^n; параметр x — rsolve не решает
    ("Σk C(n,k)" (* k (C n k)) k 0 n "S" sum)                 ; n 2^{n-1}
    ("Σ(-1)^k C(n,k)/(k+1)" (/ (* (^ -1 k) (C n k)) (+ k 1)) k 0 n "SU" sum) ; 1/(n+1)
    ("ΣC(n+k,k)/2^k" (/ (C (+ n k) k) (^ 2 k)) k 0 n "SU" sum) ; 2^n
    ("Σk C(n,k)^2" (* k (^ (C n k) 2)) k 0 n "S" sum)         ; n C(2n-1,n-1)
    ; --- §6: product ---
    ("∏2 (n,a,b)" 2 n a b "S" product)                        ; 2^{b-a+1}
    ("∏n (n,1,b)" n n 1 b "S" product)                        ; b!
    ("∏n^3 (n,1,b)" (^ n 3) n 1 b "S" product)                ; (b!)^3
    ("∏1+1/k (k,1,n)" (+ 1 (/ 1 k)) k 1 n "S" product)        ; n+1
    ("∏1+1/k (k,a,b)" (+ 1 (/ 1 k)) k a b "S" product)        ; (b+1)/a
    ("∏k (k,1,n)" k k 1 n "S" product)                        ; n!
    ("∏2^k" (^ 2 k) k 1 n "S" product)
    ("∏k^3" (^ k 3) k 1 n "S" product)
    ("∏1/(k(k+1))" (/ 1 (* k (+ k 1))) k 1 n "S" product)
    ))

; ---------- классификация результата ----------

; содержит ли выражение невычисленную sum/product-часть (частичный ответ)
(define (s1-has-uneval? e)
  (and (pair? e)
       (or (equal? (car e) 'sum) (equal? (car e) 'product)
           (any? s1-has-uneval? (cdr e)))))

; рекуррентность (ответ Цайльбергера без гипергеометрических решений)
(define (s1-is-recurrence? r) (and (pair? r) (equal? (car r) 'recurrence)))

; запуск одного случая: (класс результат мс)
(define (s1-run c)
  (let* ((body (nth c 1)) (k (nth c 2)) (lo (nth c 3)) (hi (nth c 4)) (kind (nth c 6))
         (t0 (clock-us)))
    (let* ((r (try (cond ((equal? kind 'sum) (sum-symbolic body k lo hi))
                         (else (product-symbolic body k lo hi)))
                   (lambda (err) 'error)))
           (ms (/ (- (clock-us) t0) 1000.0)))
      (list (cond ((equal? r 'error) 'W)
                  ((s1-is-recurrence? r) 'N)
                  ((s1-has-uneval? r) 'U)
                  (else
                   ; ответ: проверяем оракулом (прямой счёт в целых точках)
                   (let ((how (try (cond ((equal? kind 'sum)
                                          (sum-check-how r body k lo hi))
                                         (else (product-check-how r body k lo hi)))
                                   (lambda (err) 'skip))))
                     (if (equal? how 'numeric) 'S 'W))))
            r ms))))

(define (s1-main)
  (let ((counts '()) (bad '()) (total-ms 0))
    (map (lambda (c)
           (let* ((res (s1-run c)) (cls (car res)) (exp (nth c 5)) (kind (nth c 6))
                  (ok (and (not (equal? cls 'W)) (string-contains? exp (to-string cls))))
                  (flag (if ok "" " *** НЕ СОВПАЛО")))
             (set! total-ms (+ total-ms (nth res 2)))
             (set! counts (cons cls counts))
             (if (not ok) (set! bad (cons (car c) bad)))
             (display (car c)) (display " | ") (display kind) (display " | ")
             (display cls) (display " (ожид. ") (display exp) (display ") | ")
             (display (floor (nth res 2))) (display " мс | ")
             (display (nth res 1)) (display flag) (newline)))
         s1-cases)
    (newline)
    (display "ИТОГО: ") (display (length s1-cases)) (display " примеров")
    (map (lambda (kk) (display ", ") (display kk) (display "=")
           (display (length (filter (lambda (cc) (equal? cc kk)) counts))))
         '(S N U W))
    (display ", время ") (display (floor (/ total-ms 1000))) (display " с") (newline)
    (display "расхождения: ") (display bad) (newline)))

(s1-main)

