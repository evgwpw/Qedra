; Lisp-тесты символьного суммирования, подшаг 21l.1: каскад L0–L2 (sum-symbolic), границы
; (числовые/символьные/пустые/отрицательные), шаг, проверка sum-check, невычисленная форма.

; --- Фаульхабер и линейность ---
(deftest "сумма/фаульхабер: Σ k^m, символьная граница"
  (assert-equal (sum-symbolic 'k 'k 1 'n) '(* 1/2 (+ -1 (* -1 n) (^ (+ 1 n) 2))))
  (assert-equal (sum-symbolic '(* 2 k) 'k 1 'n) '(+ -1 (* -1 n) (^ (+ 1 n) 2)))
  (assert-equal (eval-num (subst (list '= 'n 10) (sum-symbolic '(^ k 2) 'k 1 'n))) (eval-num 385))
  (assert-equal (eval-num (subst (list '= 'n 10) (sum-symbolic '(^ k 3) 'k 1 'n))) (eval-num 3025))
  (assert-equal (eval-num (subst (list '= 'm 7) (sum-symbolic '(+ (* 3 (^ k 2)) (* 2 k)) 'k 1 'm)))
                (eval-num 476)))

; --- граничные случаи: числовые, пустые, отрицательные диапазоны ---
(deftest "сумма/границы: числовые диапазоны"
  ; lo > hi — пустой диапазон, 0 (конвенция числового итератора)
  (assert-equal (sum-symbolic '(^ k 2) 'k 5 3) 0)
  ; синглтон
  (assert-equal (sum-symbolic '(^ k 2) 'k 4 4) 16)
  ; отрицательные границы
  (assert-equal (eval-num (sum-symbolic '(^ k 2) 'k -3 3)) (eval-num 28))
  (assert-equal (sum-symbolic 'k 'k -5 -3) -12)
  ; границы 0
  (assert-equal (sum-symbolic 'k 'k 0 0) 0)
  (assert-equal (sum-symbolic 'k 'k 0 4) 10))

(deftest "сумма/границы: символьные границы"
  ; константа: Σ c = c·(b − a + 1)
  (assert-equal (sum-symbolic '5 'k 'a 'b) '(* 5 (+ 1 (* -1 a) b)))
  (assert-true (equal? (simplify (sum-symbolic 'x 'k 1 'n)) (simplify '(* x n)))))

; --- геометрическая ---
(deftest "сумма/геометрическая: Σ q^k"
  (assert-true (< (abs (- (eval-num (sum-symbolic '(^ 2 k) 'k 0 5)) 63)) 1e-9))
  (assert-true (< (abs (- (eval-num (sum-symbolic '(^ 2 k) 'k 3 3)) 8)) 1e-9))
  ; q = 1 числово — не геометрическая ветка, а константа
  (assert-true (< (abs (- (eval-num (sum-symbolic '(^ 1 k) 'k 1 5)) 5)) 1e-9))
  ; символьное q — условие q ≠ 1 (записано в канал условий)
  (conditions-clear)
  (sum-symbolic '(^ q k) 'k 'm 'n)
  (assert-true (equal? (car (car (conditions))) '(/= (- q 1) 0))))

; --- Σ k^-m → harmonic ---
(deftest "сумма/harmonic: Σ 1/k^m"
  (assert-equal (sum-symbolic '(^ k -1) 'k 1 'n) '(harmonic n 1))
  (assert-equal (sum-symbolic '(/ 1 k) 'k 1 'n) '(harmonic n 1))
  (assert-equal (sum-symbolic '(/ 1 (^ k 2)) 'k 1 'n) '(harmonic n 2))
  (assert-true (< (abs (- (eval-num (subst (list '= 'n 5) (sum-symbolic '(^ k -1) 'k 1 'n)))
                          (eval-num '(harmonic 5 1)))) 1e-9)))

; --- шаг ≠ 1 ---
(deftest "сумма/шаг: k = a + s·j"
  ; 1 + 4 + 7 + 10 = 22
  (assert-equal (sum-symbolic 'k 'k 1 10 3) 22)
  ; тот же диапазон вниз: 10 + 7 + 4 + 1 = 22
  (assert-equal (sum-symbolic 'k 'k 10 1 -3) 22)
  ; шаг не помещается ни разу после первого члена: 1 ≤ 2 — первый член включён (как у числового итератора)
  (assert-equal (sum-symbolic 'k 'k 1 2 5) 1)
  ; 2 + 4 + ... + 10 = 30
  (assert-equal (sum-symbolic 'k 'k 2 10 2) 30)
  ; символьный шаг — невычисленная форма
  (assert-equal (sum-symbolic 'k 'k 1 'n 's) '(sum k k 1 n s)))

; --- отказ: невычисленная форма ---
(deftest "сумма/отказ: неизвестное тело"
  (assert-equal (sum-symbolic '(sin k) 'k 1 'n) '(sum (sin k) k 1 n))
  (assert-equal (sum-symbolic '(^ k k) 'k 1 'n) '(sum (^ k k) k 1 n))
  ; полюс в диапазоне: 1/(k(k+1)) закрывается Госпером; 1/(k−3) от 1 — Абрамов даёт ψ-форму
  ; с полюсным аргументом ψ(−2) (k=3 в диапазоне — сумма расходится; ψ(−2) не числится — не ложный ответ)
  (assert-true (and (op-expr? (sum-symbolic '(/ 1 (- k 3)) 'k 1 'n))
                    (equal? (car (sum-symbolic '(/ 1 (- k 3)) 'k 1 'n)) '+))))

; --- sum-check: оракул ---
(deftest "сумма/проверка: sum-check"
  (assert-equal (sum-check (sum-symbolic '(^ k 2) 'k 1 'n) '(^ k 2) 'k 1 'n) 'numeric)
  (assert-equal (sum-check (sum-symbolic '(^ 2 k) 'k 0 'n) '(^ 2 k) 'k 0 'n) 'numeric)
  (assert-equal (sum-check (sum-symbolic '(^ k -1) 'k 1 'n) '(^ k -1) 'k 1 'n) 'numeric)
  (assert-equal (sum-check (sum-symbolic '(+ (* 3 (^ k 2)) (* 2 k)) 'k 1 'm)
                           '(+ (* 3 (^ k 2)) (* 2 k)) 'k 1 'm) 'numeric))

; --- шаги журнала ---
(deftest "сумма/шаги: rule id"
  (let ((r (capture-step-log (lambda () (sum-symbolic '(^ k 2) 'k 1 'n)) 'full 'ru)))
    (assert-true (member? 'sum-symbolic (step-rules (cadr r))))
    (assert-true (member? 'sum-check (step-rules (cadr r)))))
  (let ((r (capture-step-log (lambda () (sum-symbolic '(^ k 2) 'k 5 3)) 'full 'ru)))
    (assert-true (member? 'sum-empty (step-rules (cadr r))))))

; --- 21l.2: классификатор гипергеометрических термов (hyper-ratio) ---
; сравнение отношения (p . q) с ожидаемым p0/q0 подстановкой чисел: p/p0 = q/q0 = 1
(define (hyper-sub e sub)
  (if (null? sub) e
      (hyper-sub (subst (list '= (car (car sub)) (cdr (car sub))) e) (cdr sub))))
(define (hyper-check-ratio r p0 q0)
  (let ((sub (list (cons 'k 3) (cons 'm 5) (cons 'j 2) (cons 'n 7))))
    (and (= (eval-num (hyper-sub (simplify (list '/ (car r) p0)) sub)) 1)
         (= (eval-num (hyper-sub (simplify (list '/ (cdr r) q0)) sub)) 1))))
(deftest "сумма/hyper-ratio: Γ-нормальная форма"
  ; Γ(2k+4)/Γ(3k+6): p=(2k+4)(2k+5), q=(3k+6)(3k+7)(3k+8)
  (assert-true (hyper-check-ratio (hyper-ratio '(/ (gamma (+ (* 2 k) 4)) (gamma (+ (* 3 k) 6))) 'k)
                                  '(* (+ (* 2 k) 4) (+ (* 2 k) 5))
                                  '(* (+ (* 3 k) 6) (+ (* 3 k) 7) (+ (* 3 k) 8)))))
(deftest "сумма/hyper-ratio: C(1/2, m+j) и C(m+j, j)"
  ; C(1/2, m+j): p = (1/2−m−j), q = (1+j+m)
  (assert-true (hyper-check-ratio (hyper-ratio '(binomial (/ 1 2) (+ m j)) 'j)
                                  '(+ 1/2 (* -1 m) (* -1 j)) '(+ 1 j m)))
  ; C(m+j, j): отношение (m+j+1)/(j+1)
  (assert-true (hyper-check-ratio (hyper-ratio '(binomial (+ m j) j) 'j) '(+ 1 j m) '(+ 1 j))))
(deftest "сумма/hyper-ratio: факториалы, (−1)^k, числовая дробная степень"
  ; k!/(2k+1)!: p=(k+1), q=(2k+2)(2k+3)
  (assert-true (hyper-check-ratio (hyper-ratio '(/ (factorial k) (factorial (+ (* 2 k) 1))) 'k)
                                  '(+ 1 k) '(* (+ 2 (* 2 k)) (+ 3 (* 2 k)))))
  (assert-equal (hyper-ratio '(^ -1 k) 'k) '(-1 . 1))
  (assert-equal (hyper-ratio '(^ 4 (/ k 2)) 'k) '(2 . 1))
  ; 1/Γ(k+1/2): p=1, q=k+1/2
  (assert-true (hyper-check-ratio (hyper-ratio '(/ 1 (gamma (+ k (/ 1 2)))) 'k) 1 '(+ k 1/2))))
(deftest "сумма/hyper-ratio: отказы — не гипергеометрические термы"
  (assert-equal (hyper-ratio '(^ k k) 'k) #f)             ; kᵏ
  (assert-equal (hyper-ratio '(harmonic k) 'k) #f)        ; H_k
  (assert-equal (hyper-ratio '(sin k) 'k) #f)             ; sin k
  (assert-equal (hyper-ratio '(gamma (/ k 2)) 'k) #f)     ; Γ(k/2)
  (assert-equal (hyper-ratio '(^ x (/ k 2)) 'k) #f)       ; x^(k/2), x символьный
  (assert-equal (hyper-ratio '(+ (factorial k) (^ 2 k)) 'k) #f)  ; сумма слагаемых
  (assert-equal (hyper-ratio '(cos k) 'k) #f)
  (assert-equal (hyper-termp '(* (^ x k) (rf a k)) 'k) #t)
  (assert-equal (hyper-termp '(^ k k) 'k) #f))
(deftest "сумма/poly-shift: сдвиг многочлена"
  (assert-equal (poly-shift '(+ (* 2 (^ k 2)) k) 'k 3) '(+ 21 (* 13 k) (* 2 (^ k 2))))
  (assert-equal (poly-shift '(+ k 5) 'k 0) '(+ 5 k)))
(deftest "сумма/poly-dispersion: дисперсия знаменателя"
  ; q=(k−1)(k+3): (k+3) = (k−1)+4 → дисперсия 4
  (assert-equal (poly-dispersion '(* (- k 1) (+ k 3)) 'k) 4)
  ; q=k+1: сдвигов нет
  (assert-equal (poly-dispersion '(+ k 1) 'k) #f))

; ---------- подшаг 21l.3: алгоритм Госпера ----------

; оракул: прямая сумма t(j), j = lo..n, числовая (целые); eval — точная (рациональная) оценка
(define (gosper-oracle t k lo n)
  (if (< n lo)
      0
      (+ (eval (subst (list '= k n) t)) (gosper-oracle t k lo (- n 1)))))
; числовая проверка ответа sum-symbolic в точках n0..n0+3; var — символьное имя верхней границы
(define (gosper-check-num r t k lo n0)
  (gosper-check-num-v 'n r t k lo n0))
(define (gosper-check-num-v var r t k lo n0)
  (and (equal? (eval (subst (list '= var n0) r)) (gosper-oracle t k lo n0))
       (equal? (eval (subst (list '= var (+ n0 1)) r)) (gosper-oracle t k lo (+ n0 1)))
       (equal? (eval (subst (list '= var (+ n0 2)) r)) (gosper-oracle t k lo (+ n0 2)))
       (equal? (eval (subst (list '= var (+ n0 3)) r)) (gosper-oracle t k lo (+ n0 3)))))
; ответ — невычисленная форма (sum ...)?
(define (gosper-unev? r) (and (op-expr? r) (equal? (car r) 'sum)))

(deftest "сумма/Госпер: gosper-normal (эталонный тест)"
  ; (4n+5)/(2(4n+1)(2n+3)) → (A, B, C) = (1/4, n+3/2, n+1/4) — точно как эталон
  (let ((nb (gosper-normal '(+ (* 4 k) 5) '(* 2 (+ (* 4 k) 1) (+ (* 2 k) 3)) 'k)))
    (assert-equal (car (car nb)) 1/4)
    (assert-equal (cdr (car nb)) '(+ 3/2 k))
    (assert-equal (cdr nb) '(+ 1/4 k))))

(deftest "сумма/Госпер: gosper-term множители"
  ; k·k! → g = 1/k (z_k = k!)
  (assert-equal (gosper-term '(* k (factorial k)) 'k) '(^ k -1))
  ; k! → доказано: нет гипергеометрической первообразной
  (assert-equal (gosper-term '(factorial k) 'k) 'unsolvable)
  ; k^k → не гипергеометрический
  (assert-equal (gosper-term '(^ k k) 'k) 'no-hyper))

(deftest "сумма/Госпер: Σ k·k! = (n+1)! − 1"
  ; от 0: t(0)=0 — проверка с n0=1 (в точке n=0 z-формула не определена, там сумма=t(0)=0);
  ; от 1: проверка с n0=1
  (assert-true (gosper-check-num-v 'n (sum-symbolic '(* k (factorial k)) 'k 0 'n)
                                   '(* k (factorial k)) 'k 0 1))
  (assert-true (gosper-check-num-v 'n (sum-symbolic '(* k (factorial k)) 'k 1 'n)
                                   '(* k (factorial k)) 'k 1 1)))

(deftest "сумма/Госпер: Σ 1/(k(k+1)) = 1 − 1/(n+1)"
  (assert-true (gosper-check-num-v 'n (sum-symbolic '(/ 1 (* k (+ k 1))) 'k 1 'n)
                                   '(/ 1 (* k (+ k 1))) 'k 1 1)))

(deftest "сумма/Госпер: «A = B» 1b, 1d, 1f, 1g, 3b (числовой оракул)"
  (assert-true (gosper-check-num-v 'm (sum-symbolic '(* (^ n 3) (^ 2 n)) 'n 0 'm)
                                 '(* (^ n 3) (^ 2 n)) 'n 0 0))
  (assert-true (gosper-check-num-v 'm (sum-symbolic '(/ (* (^ n 4) (^ 4 n)) (binomial (* 2 n) n)) 'n 0 'm)
                                 '(/ (* (^ n 4) (^ 4 n)) (binomial (* 2 n) n)) 'n 0 0))
  (assert-true (gosper-check-num-v 'm (sum-symbolic '(/ (^ (binomial (* 2 n) n) 2) (* (+ n 1) (^ 4 (* 2 n)))) 'n 0 'm)
                                 '(/ (^ (binomial (* 2 n) n) 2) (* (+ n 1) (^ 4 (* 2 n)))) 'n 0 0))
  (assert-true (gosper-check-num-v 'm (sum-symbolic '(/ (* (- (* 4 n) 1) (^ (binomial (* 2 n) n) 2)) (* (^ (- (* 2 n) 1) 2) (^ 4 (* 2 n)))) 'n 0 'm)
                                 '(/ (* (- (* 4 n) 1) (^ (binomial (* 2 n) n) 2)) (* (^ (- (* 2 n) 1) 2) (^ 4 (* 2 n)))) 'n 0 0))
  (assert-true (gosper-check-num-v 'm (sum-symbolic '(/ (+ (* 6 n) 3) (+ (* 4 (^ n 4)) (* 8 (^ n 3)) (* 8 (^ n 2)) (* 4 n) 3)) 'n 1 'm)
                                 '(/ (+ (* 6 n) 3) (+ (* 4 (^ n 4)) (* 8 (^ n 3)) (* 8 (^ n 2)) (* 4 n) 3)) 'n 1 1)))

(deftest "сумма/Госпер: (−1)^k C(n,k) и параметрический 2b (числовой оракул)"
  ; Σ (−1)^k C(n,k) при n=5, m=0..3: (−1)^m C(4,m)
  (assert-true (gosper-check-num-v 'm (subst (list '= 'n 5) (sum-symbolic '(* (^ -1 k) (binomial n k)) 'k 0 'm))
                                 '(* (^ -1 k) (binomial 5 k)) 'k 0 0))
  ; 2b: (n − r/2)C(r,n) при r=7, m=0..3: (m−r)C(r,m)/2
  (assert-true (gosper-check-num-v 'm (subst (list '= 'r 7) (sum-symbolic '(* (- n (/ r 2)) (binomial r n)) 'n 0 'm))
                                 '(* (- n (/ 7 2)) (binomial 7 n)) 'n 0 0)))

(deftest "сумма/Госпер: отказы — не суммируемые гипергеометрические термы"
  ; k! не имеет гипергеометрической первообразной (нет решения)
  (assert-equal (gosper-term '(factorial k) 'k) 'unsolvable)
  (assert-true (gosper-unev? (sum-symbolic '(factorial k) 'k 0 'n)))
  ; 1/(k−3) от 5 до m — рациональный терм без первообразной: с 21l.4 Абрамов даёт ψ-разность
  ; (Σ_{k=5}^{7} = ψ(m−2) − ψ(2) = 1/2+1/3+1/4; раньше — невычисленная форма)
  (assert-true (equal? (simplify (sum-symbolic '(/ 1 (- k 3)) 'k 5 'm))
                       (simplify '(+ (* -1 (psi 2 0)) (psi (+ -2 m) 0))))))

(deftest "сумма/Госпер: нули терма на нижней границе (сдвиг + хвост)"
  ; Σ n⁴4ⁿ/C(2n,n) от 0: t(0)=0, формула обязана давать t(0)=0 при m=0 (ошибка z-формы без сдвига)
  (assert-equal (eval-num (subst (list '= 'm 0) (sum-symbolic '(/ (* (^ n 4) (^ 4 n)) (binomial (* 2 n) n)) 'n 0 'm))) (eval-num 0)))

; --- 21l.4: Абрамов — рациональные функции ---

; декомпозиция f = Δg + h (эталонная схема разложения на Δg + h)
(deftest "сумма/Абрамов: декомпозиция 1/(k(k+1)) → g = −1/k, h = 0"
  (let ((d (abramov-decompose '(/ 1 (* k (+ k 1))) 'k)))
    (assert-true (and d (equal? (simplify (cdr d)) 0)))
    (assert-equal (simplify (car d)) '(* -1 (^ k -1)))))

(deftest "сумма/Абрамов: декомпозиция 1/k → g = 0, h ≠ 0 (не суммируется рационально)"
  (let ((d (abramov-decompose '(/ 1 k) 'k)))
    (assert-true (and d (equal? (simplify (car d)) 0)))
    (assert-true (not (equal? (simplify (cdr d)) 0)))))

(deftest "сумма/Абрамов: декомпозиция 1/(k(k+2)) — перенос полюса на 2"
  ; g = −(2k+1)/(2k(k+1)) (сдвиг k+2 → k, offset 2); проверяем тождество Δg + h = f
  (let ((d (abramov-decompose '(/ 1 (* k (+ k 2))) 'k)))
    (assert-true (and d (equal? (simplify (cdr d)) 0)))
    ; Σ_{k=1}^{n} = n(3n+5)/(4(n+1)(n+2)) [проверено вручную, n=1 → 1/3] (float — с допуском)
    (assert-true (let ((v (eval-num (subst (list '= 'n 1) (abramov-sum '(/ 1 (* k (+ k 2))) 'k 1 'n)))))
                   (and (number? v) (< (abs (- v 1/3)) 1e-9))))))

(deftest "сумма/Абрамов: 1/(k(2k+1)) — нецелый сдвиг, замкнутая форма через psi"
  ; k и k+1/2 не переводятся целым сдвигом — рационального g нет, ответ через ψ-разности
  (let ((d (abramov-decompose '(/ 1 (* k (+ (* 2 k) 1))) 'k)))
    (assert-true (not (equal? (simplify (cdr d)) 0)))
    ; численная сверка: Σ_{k=1}^{5} 1/(k(2k+1)) = 1/3+1/10+1/21+1/36+1/55 (float — с допуском)
    (assert-true (let ((v (eval-num (subst (list '= 'n 5) (abramov-sum '(/ 1 (* k (+ (* 2 k) 1))) 'k 1 'n)))))
                   (and (number? v) (< (abs (- v (+ 1/3 1/10 1/21 1/36 1/55))) 1e-9))))))

(deftest "сумма/Абрамов: 1/(k²+1) — неприводимая степень 2, честный отказ"
  (assert-true (not (abramov-sum '(/ 1 (+ (^ k 2) 1)) 'k 1 'n)))
  (assert-true (gosper-unev? (sum-symbolic '(/ 1 (+ (^ k 2) 1)) 'k 1 'n))))

(deftest "сумма/Абрамов: тройное телескопирование 1/(k(k+1)(k+2))"
  ; Σ_{k=1}^{n} = 1/4 − 1/(2(n+1)) + 1/(2(n+2)); проверка тождеством и численно
  (let ((r (abramov-sum '(/ 1 (* k (+ k 1) (+ k 2))) 'k 1 'n)))
    (assert-true r)
    (assert-equal (eval-num (subst (list '= 'n 1) r)) (eval-num 1/6))
    (assert-true (let ((v (eval-num (subst (list '= 'n 10) r))))
                   (and (number? v)
                        (< (abs (- v (+ 1/6 1/24 1/60 1/120 1/210 1/336 1/504 1/720 1/990 1/1320))) 1e-9))))))

(deftest "сумма/Абрамов: Σ 1/k = ψ-разность (прямая декомпозиция; каскад даёт harmonic)"
  (let ((r (abramov-sum '(/ 1 k) 'k 1 'n)))
    ; численная сверка ψ-формы: Σ_{k=1}^{4} 1/k = 25/12 (float — с допуском)
    (assert-true (let ((v (eval-num (subst (list '= 'n 4) r))))
                   (and (number? v) (< (abs (- v (+ 1 1/2 1/3 1/4))) 1e-9))))))

(deftest "сумма/Абрамов: многочленная часть + рациональный хвост (k³/(k+1))"
  ; k³/(k+1) = k² − k + 1 − 1/(k+1): полиномиальная часть по Фаульхаберу, хвост ψ
  (let ((d (abramov-decompose '(/ (^ k 3) (+ k 1)) 'k)))
    (assert-true d)
    ; численная сверка суммы: Σ_{k=1}^{3} k³/(k+1) = 1/2 + 8/3 + 27/4 (float — с допуском)
    (assert-true (let ((v (eval-num (subst (list '= 'n 3) (abramov-sum '(/ (^ k 3) (+ k 1)) 'k 1 'n)))))
                   (and (number? v) (< (abs (- v (+ 1/2 8/3 27/4))) 1e-9))))))

; ---------- 21l.5a: Цайльбергер — форма рекуррентности и проверки ----------

; прямая сумма биномов: S(n) = Σ_{k=0}^{n} C(n,k) = 2^n
(define (zb-bin-sum m)
  (zb-bin-sum-loop m 0 0))
(define (zb-bin-sum-loop m j acc)
  (if (> j m)
      acc
      (zb-bin-sum-loop m (+ j 1) (+ acc (eval (list 'binomial m j))))))

(deftest "сумма/Цайльбергер: проверка рекуррентности ΣC(n,k) (порядок 1)"
  ; Σ C(n,k) = 2^n удовлетворяет S(n+1) − 2·S(n) = 0 (сертификат [−2, 1])
  (assert-true (recurrence-check (list 'recurrence 'S 'n (list -2 1) 0 '()) zb-bin-sum))
  ; ложные коэффициенты отклоняются (не ложное «доказано»)
  (assert-true (not (recurrence-check (list 'recurrence 'S 'n (list -3 1) 0 '()) zb-bin-sum)))
  (assert-true (not (recurrence-check (list 'recurrence 'S 'n (list -2 1) 0 '((0 2))) zb-bin-sum)))
  ; согласованное начальное значение принимается
  (assert-true (recurrence-check (list 'recurrence 'S 'n (list -2 1) 0 '((0 1) (1 2))) zb-bin-sum)))

(deftest "сумма/Цайльбергер: рекуррентность Апери (порядок 2)"
  ; S(n) = Σ_k C(n,k)²·C(n+k,k)²: (n+1)³·S(n+2) − (2n+3)(17n²+51n+39)·S(n+1) + (n+2)³·S(n) = 0
  (define (zb-apery m)
    (zb-apery-loop m 0 0))
  (define (zb-apery-loop m j acc)
    (if (> j m)
        acc
        (zb-apery-loop m (+ j 1)
                       (+ acc (eval (list '* (list 'binomial m j) (list 'binomial m j)
                                       (list 'binomial (+ m j) j) (list 'binomial (+ m j) j)))))))
  (assert-true (recurrence-check
                (list 'recurrence 'S 'n
                      (list (list '^ (list '+ 'n 1) 3)
                            (list '* -1 (list '+ (list '* 2 'n) 3)
                                  (list '+ (list '* 17 'n 'n) (list '* 51 'n) 39))
                            (list '^ (list '+ 'n 2) 3))
                      0 '((0 1) (1 5)))
                zb-apery))
  ; испорченный коэффициент (18n² вместо 17n²) отклоняется
  (assert-true (not (recurrence-check
                 (list 'recurrence 'S 'n
                       (list (list '^ (list '+ 'n 1) 3)
                             (list '* -1 (list '+ (list '* 2 'n) 3)
                                   (list '+ (list '* 18 'n 'n) (list '* 51 'n) 39))
                             (list '^ (list '+ 'n 2) 3))
                       0 '((0 1) (1 5)))
                 zb-apery))))

(deftest "сумма/Цайльбергер: WZ-доказательство ΣC(n,k) = 2^n (ручной сертификат)"
  ; сертификат R(n,k) = k/(2(k−n−1)) (эталонная схема test_wz): тождество + база n=0
  (assert-true (wz-prove-identity '(binomial n k) '(^ 2 n) 'n 'k
                                  '(/ k (* 2 (- k n 1))) 0))
  ; ложная замкнутая форма сертификатом не доказывается
  (assert-true (not (wz-prove-identity '(binomial n k) '(* 3 (^ 2 n)) 'n 'k
                                   '(/ k (* 2 (- k n 1))) 0)))


)

(deftest "сумма/Цайльбергер: ядро zb-par-gosper ΣC(n,k) (порядок 1)"
  (assert-equal (car (zb-par-gosper '(binomial n k) 'n 'k 1)) (list -2 1))
  (assert-true (recurrence-check
              (list 'recurrence 'S 'n (car (zb-par-gosper '(binomial n k) 'n 'k 1)) 0 '())
              zb-bin-sum)))

(deftest "сумма/Цайльбергер: zb-par-gosper J=2 для ΣC(n,k)^2 = C(2n,n)"
  ; ядро параметрического Госпера при J=2 находит рекуррентность порядка 2
  ; (вырожденную: последний коэффициент 0, фактический порядок 1 — минимальный)
  (define (zb-sq-sum m) (eval (list 'binomial (list '* 2 m) m)))
  (define zb-sq-a (car (zb-par-gosper '(^ (binomial n k) 2) 'n 'k 2)))
  (assert-true (list? zb-sq-a))
  ; рекуррентность проверяется численно на C(2m,m)
  (assert-true (recurrence-check (list 'recurrence 'S 'n zb-sq-a 0 '()) zb-sq-sum))
  ; ложная рекуррентность (порядок 1 с неверным коэффициентом) отклоняется
  (assert-true (not (recurrence-check (list 'recurrence 'S 'n (list -3 1 0) 0 '()) zb-sq-sum)))
)

(deftest "сумма/WZ: автоматический сертификат wz-certificate ΣC(n,k) = 2^n"
  ; сертификат строится ядром (Цайльбергер J=1 на F/f) и проверяется:
  ; рациональное тождество + база прямой суммой; #f — пара не доказана
  (assert-true (pair? (wz-certificate '(binomial n k) '(^ 2 n) 'n 'k)))
  ; найденный сертификат проходит wz-prove-identity (проверка сертификата)
  (define zb-wz-r (wz-certificate '(binomial n k) '(^ 2 n) 'n 'k))
  (assert-true (wz-prove-identity '(binomial n k) '(^ 2 n) 'n 'k zb-wz-r 0))
  ; ложная замкнутая форма — сертификата нет
  (assert-true (not (wz-certificate '(binomial n k) '(* 3 (^ 2 n)) 'n 'k)))
  ; Σk·C(n,k) = n·2^(n-1) — ещё одна классическая WZ-пара
  (assert-true (pair? (wz-certificate '(* k (binomial n k)) '(* n (^ 2 (- n 1))) 'n 'k)))
)

(deftest "сумма/Цайльбергер: zb-par-gosper J=2 для Апери (ΣC(n,k)^2C(n+k,k)^2)"
  ; рекуррентность порядка 2 Апери из ядра (без ручных коэффициентов):
  ; S(n) = Σ_k C(n,k)²·C(n+k,k)² — та же, что в тесте «рекуррентность Апери»
  (define (zb-apery2 m)
    (zb-apery2-loop m 0 0))
  (define (zb-apery2-loop m j acc)
    (if (> j m)
        acc
        (zb-apery2-loop m (+ j 1)
                       (+ acc (eval (list '* (list 'binomial m j) (list 'binomial m j)
                                       (list 'binomial (+ m j) j) (list 'binomial (+ m j) j)))))))
  (define zb-ap2 (car (zb-par-gosper
                       (list '* (list 'binomial 'n 'k) (list 'binomial 'n 'k)
                             (list 'binomial (list '+ 'n 'k) 'k)
                             (list 'binomial (list '+ 'n 'k) 'k))
                       'n 'k 2)))
  (assert-true (list? zb-ap2))
  ; проверка численным оракулом на прямых суммах
  (assert-true (recurrence-check (list 'recurrence 'S 'n zb-ap2 0 '()) zb-apery2))
  ; порядок 2 (три коэффициента, ни один не нулевой — полный порядок, не вырожденный)
  (assert-true (= (length zb-ap2) 3))
  (assert-true (not (equal? (simplify (car (cdr (cdr zb-ap2)))) 0)))
)

(deftest "сумма/Цайльбергер: драйвер zeilberger — рекуррентность с начальными значениями"
  ; ΣC(n,k): готовый ответ (recurrence S n (-2 1) 0 ((0 1))) — S(n+1) = 2S(n), S(0)=1
  (assert-equal (zeilberger '(binomial n k) 'n 'k)
                (list 'recurrence 'S 'n (list -2 1) 0 (list (list 0 1))))
  ; C(n,k)^2: минимальная рекуррентность порядка 1, init S(0)=1
  (define zb-drv2 (zeilberger '(^ (binomial n k) 2) 'n 'k))
  (assert-true (list? zb-drv2))
  (assert-true (equal? (car (cdr (cdr (cdr (cdr zb-drv2))))) 0))
  (assert-true (equal? (car (cdr (cdr (cdr (cdr (cdr zb-drv2)))))) (list (list 0 1))))
  ; форма проверена численным оракулом на C(2m,m)
  (define (zb-sq-sum2 m) (eval (list 'binomial (list '* 2 m) m)))
  (assert-true (recurrence-check zb-drv2 zb-sq-sum2))
  ; Апери: порядок 2, init ((0 1) (1 5)) — S(0)=1, S(1)=5
  (define zb-drv3 (zeilberger (list '* (list 'binomial 'n 'k) (list 'binomial 'n 'k)
                                   (list 'binomial (list '+ 'n 'k) 'k)
                                   (list 'binomial (list '+ 'n 'k) 'k)) 'n 'k))
  (assert-true (list? zb-drv3))
  (assert-equal (car (cdr (cdr (cdr (cdr (cdr zb-drv3)))))) (list (list 0 1) (list 1 5)))
  ; отрицательный контроль: не гипергеометрический терм — #f
  (assert-true (not (zeilberger '(* k (sin k)) 'n 'k)))
)

(deftest "сумма/Цайльбергер: zeilberger для Σk·C(n,k) — полюс коэффициента, старт init с n=1"
  ; a0 = −2−2/n (полюс n=0): n0 = 1 после полюса; S(1) = 1 — верно (Σk·C(1,k) = 1)
  (assert-equal (zeilberger '(* k (binomial n k)) 'n 'k)
                (list 'recurrence 'S 'n
                      (list (list '+ -2 (list '* -2 (list '^ 'n -1))) 1)
                      0 (list (list 1 1))))
  ; численный оракул: S(m) = m·2^(m−1)
  (define (zb-ksum m)
    (let ((lo (summation::wz-nat-bound '(* k (binomial n k)) 'n 'k m -1))
          (hi (summation::wz-nat-bound '(* k (binomial n k)) 'n 'k m 1)))
      (summation::wz-direct-sum '(* k (binomial n k)) 'n 'k m lo hi)))
  (assert-true (recurrence-check (zeilberger '(* k (binomial n k)) 'n 'k) zb-ksum))
)

(deftest "сумма/rsolve (21l.6): замкнутые формы из рекуррентностей Цайльбергера"
  ; ΣC(n,k) = 2^n — прямой счёт n=0..5
  (define (rs-bin m) (summation::wz-direct-sum '(binomial n k) 'n 'k m 0 m))
  (define rs-a1 (rsolve (zeilberger '(binomial n k) 'n 'k)))
  (assert-true (equal? rs-a1 '(^ 2 n)))
  (assert-true (rs-check-points rs-a1 'n rs-bin 0 5))
  ; ΣC(n,k)^2 = C(2n,n) — полировка свернула Γ-форму в бином
  (define (rs-sq m) (eval (list 'binomial (list '* 2 m) m)))
  (define rs-a2 (rsolve (zeilberger '(^ (binomial n k) 2) 'n 'k)))
  (assert-true (equal? rs-a2 (list 'binomial (list '* 2 'n) 'n)))
  (assert-true (rs-check-points rs-a2 'n rs-sq 1 5))
  ; каскад sum: те же ответы через sum-symbolic
  (assert-true (equal? (sum-symbolic '(binomial n k) 'k 0 'n) '(^ 2 n)))
  (assert-true (equal? (sum-symbolic '(^ (binomial n k) 2) 'k 0 'n)
                        (list 'binomial (list '* 2 'n) 'n)))
  ; Апери: гипергеометрической замкнутой формы нет — рекуррентность (не «не знаю»)
  (define rs-ap (sum-symbolic
                  (list '* (list 'binomial 'n 'k) (list 'binomial 'n 'k)
                        (list 'binomial (list '+ 'n 'k) 'k)
                        (list 'binomial (list '+ 'n 'k) 'k))
                  'k 0 'n))
  (assert-true (and (pair? rs-ap) (equal? (car rs-ap) 'recurrence)))
  (assert-true (equal? (car (cdr (cdr (cdr (cdr (cdr rs-ap)))))) (list (list 0 1) (list 1 5))))
)

; --- 21l.8: product с символьной границей, combsimp, product-check ---
(deftest "произведение/product: Γ-форма и q^k"
  ; ∏ k = n!
  (assert-equal (product-symbolic 'k 'k 1 'n) '(factorial n))
  ; ∏ (1 + 1/k) = n + 1 (k = 1..n)
  (assert-equal (product-symbolic '(+ 1 (/ 1 k)) 'k 1 'n) '(+ 1 n))
  ; ∏ (1 + 1/k) = (b+1)/a (k = a..b)
  (assert-equal (product-symbolic '(+ 1 (/ 1 k)) 'k 'a 'b) '(* (^ a -1) (+ 1 b)))
  ; ∏ k^3 = (n!)^3
  (assert-equal (product-symbolic '(^ k 3) 'k 1 'n) '(^ (factorial n) 3))
  ; ∏ 2^k = 2^(n(n+1)/2)
  (assert-equal (product-symbolic '(^ 2 k) 'k 1 'n) '(^ 2 (* 1/2 n (+ 1 n))))
  ; ∏ 2 = 2^(b-a+1)
  (assert-equal (product-symbolic '2 'k 'a 'b) '(^ 2 (+ 1 (* -1 a) b)))
  ; ∏ 1/(k(k+1)) = 1/(n!·Γ(n+2)) — верная Γ-форма
  (assert-equal (product-symbolic '(/ 1 (* k (+ k 1))) 'k 1 'n)
                '(* (^ (factorial n) -1) (^ (gamma (+ 2 n)) -1))))

(deftest "произведение/product: прямой счёт n = 1..6"
  (assert-true (let ((ans (product-symbolic 'k 'k 1 'n)))
                 (prod-close-loop ans 'k 'k 1 6)))
  (assert-true (let ((ans (product-symbolic '(+ 1 (/ 1 k)) 'k 1 'n)))
                 (prod-close-loop ans '(+ 1 (/ 1 k)) 'k 1 6)))
  (assert-true (let ((ans (product-symbolic '(* k k k) 'k 1 'n)))
                 (prod-close-loop ans '(^ k 3) 'k 1 6)))
  (assert-true (let ((ans (product-symbolic '(^ 2 k) 'k 1 'n)))
                 (prod-close-loop ans '(^ 2 k) 'k 1 6))))

; сравнение Γ-формы ответа (граница 'n) с прямым произведением тела по k = j..j
; (factorial/C → gamma: eval-num не считает factorial/C, но gamma/binomial — да)
(define (prod-close-loop ans body k j n)
  (if (> j n)
      #t
      (and (prod-close? (eval-num (subst (list '= 'n j) (product-fact-to-gamma ans)))
                        (prod-direct-num body k 1 j))
           (prod-close-loop ans body k (+ j 1) n))))

(define (prod-direct-num body k a n)
  (eval-num (product-direct body k a n)))

(define (prod-close? a b)
  (if (= b 0)
      (< (abs a) 1e-9)
      (< (abs (/ (- a b) b)) 1e-9)))

; --- 21l.8: combsimp ---
(deftest "произведение/combsimp: Γ ↔ factorial и отношения"
  ; x·Γ(x) → x!
  (assert-equal (combsimp '(* x (gamma x))) '(factorial x))
  ; Γ(n+1)/Γ(n) → n
  (assert-equal (combsimp '(/ (gamma (+ n 1)) (gamma n))) 'n)
  ; k·Γ(k+2): combsimp не меняет семантику — прямым счётом
  (assert-true (< (abs (- (eval-num (combsimp '(* k (gamma (+ k 2)))))
                          (eval-num '(* k (gamma (+ k 2)))))) 1e-9)))

; --- 21l.8: product-check-how ---
(deftest "произведение/product-check-how: оракул"
  (assert-equal (product-check-how '(factorial n) 'k 'k 1 'n) 'numeric)
  (assert-equal (product-check-how '(+ 1 n) '(+ 1 (/ 1 k)) 'k 1 'n) 'numeric)
  ; пустой диапазон: ∏ = 1, oracle проверяет
  (assert-equal (product-check-how 1 'k 'k 1 0) 'numeric))


(deftest "сумма/rsolve (21l.6): постоянные коэффициенты (Фибоначчи)"
  ; S(n+2) = S(n+1) + S(n), S(0)=0, S(1)=1 → формула Бине
  (define rs-fib (rsolve (list 'recurrence 'S 'n (list -1 -1 1) 0 '((0 0) (1 1)))))
  (assert-true (pair? rs-fib))
  ; численно: F(10) = 55, F(15) = 610 (eval-num даёт float — близость)
  (assert-true (rs-close? (eval-num (eval (subst (list '= 'n 10) rs-fib))) 55))
  (assert-true (rs-close? (eval-num (eval (subst (list '= 'n 15) rs-fib))) 610))
  ; порядок 1 с знакопеременой: S(n+1) = −S(n), S(0)=1 → (−1)^n
  (define rs-alt (rsolve (list 'recurrence 'S 'n (list 1 1) 0 '((0 1)))))
  (assert-true (rs-close? (eval-num (eval (subst (list '= 'n 7) rs-alt))) -1))
)

; численная проверка замкнутой формы против прямого счёта в точках m0..m1
(define (rs-check-points ans n direct m0 m1)
  (if (> m0 m1)
      #t
      (let* ((v (eval-num (eval (subst (list '= n m0) ans))))
             (d (direct m0)))
        (and (number? v) (number? d)
             (rs-close? v d)
             (rs-check-points ans n direct (+ m0 1) m1)))))

(define (rs-close? a b)
  (if (= b 0)
      (< (abs a) 1e-9)
      (< (abs (/ (- a b) b)) 1e-9)))

; --- 21l.7: точная полировка Γ → C(2n,n) (отношения + одна точка) и проверка рекуррентности прямыми суммами ---
(deftest "сумма/полировка rs-try-central (21l.7): точная, отношения + одна точка"
  ; Γ-форма суммы C(n,k)^2 сворачивается в C(2n,n) ТОЧНО: hyper-ratio совпадает + значения равны
  (assert-equal (rs-try-central
    '(* (^ 4 n) (^ n -1) (^ (gamma 1/2) -1) (^ (gamma n) -1) (gamma (+ 1/2 n))) 'n)
    '(binomial (* 2 n) n))
  ; 2·C(2n,n) — другое отношение соседних членов → НЕ сворачивается
  (assert-equal (rs-try-central '(* 2 (binomial (* 2 n) n)) 'n)
                '(* 2 (binomial (* 2 n) n)))
  ; C(2n+1,n) — отношение отличается → НЕ сворачивается
  (assert-equal (rs-try-central '(binomial (+ (* 2 n) 1) n) 'n)
                '(binomial (+ (* 2 n) 1) n))
)

(deftest "сумма/recurrence-check-sum (21l.7): рекуррентность Апери прямыми суммами"
  ; рекуррентность Апери (порядок 2) проверяется прямыми суммами
  (define ap-rec (zeilberger '(* (^ (binomial n k) 2) (binomial (+ n k) k)) 'n 'k))
  (assert-true (recurrence-check-sum ap-rec
    '(* (^ (binomial n k) 2) (binomial (+ n k) k)) 'k 'n))
)

