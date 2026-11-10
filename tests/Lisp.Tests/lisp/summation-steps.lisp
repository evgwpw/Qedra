; ST.3б-1: шаги диспетчера сумм и алгоритма Госпера — данные для независимой проверки,
; brief ≤ 15 строк, ответ не меняется от включения журнала.

(define (sst-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (sst-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (sst-has? s sub) (string-contains? s sub))
(define (sst-rules thunk) (step-rules (cadr (capture-step-log thunk))))

(deftest "суммы/шаги: Σ k·k! — Госпер: отношение, разложение, граница, анзац, сертификат, телескопирование"
  (let* ((off (sum-symbolic '(* k (factorial k)) 'k 1 'n))
         (s (sst-text (lambda () (sum-symbolic '(* k (factorial k)) 'k 1 'n)) 'brief))
         (rs (sst-rules (lambda () (sum-symbolic '(* k (factorial k)) 'k 1 'n)))))
    (assert-equal (eval (subst (list '= 'n 5) off)) 719)
    ; полное дерево: все шаги Госпера на месте
    (assert-true (member? 'gosper-ratio rs))
    (assert-true (member? 'gosper-normal rs))
    (assert-true (member? 'gosper-degree rs))
    (assert-true (member? 'gosper-ansatz rs))
    (assert-true (member? 'gosper-cert rs))
    (assert-true (member? 'gosper-check rs))
    ; brief: ключевые шаги с проверяемыми данными, без служебного шума
    (assert-true (sst-has? s "Граница степени x(k)"))
    (assert-true (sst-has? s "⇒ d ="))
    (assert-true (sst-has? s "Уравнение a·x(k+1)"))
    (assert-true (sst-has? s "Проверка телескопирования"))
    (assert-true (sst-has? s "g(k+1)·r(k) − g(k) − 1 = 0"))
    ; ST.3б-3: в brief видны a(k), b(k), c(k) и g(k), T(k) = g(k)·t(k)
    (assert-true (sst-has? s "a(k) = "))
    (assert-true (sst-has? s "b(k) = "))
    (assert-true (sst-has? s "c(k) = "))
    (assert-true (sst-has? s "g(k) = "))
    (assert-true (sst-has? s "[1/k, k!]"))
    ; ST.3б-3: ответ — выражение, 1! вычислен
    (assert-true (sst-has? s "⇒ -1 + n*n!"))
    (assert-true (not (sst-has? s "1!")))
    (assert-true (<= (sst-lines s) 15))
    (assert-true (not (sst-has? s "Упрощение")))
    (assert-true (not (sst-has? s "Дифференцирование")))))

(deftest "суммы/шаги: Σ 1/(k(k+1)) — Госпер, ответ n/(n+1)"
  (let ((off (sum-symbolic '(/ 1 (* k (+ k 1))) 'k 1 'n)))
    (assert-equal (eval (subst (list '= 'n 4) off)) 4/5)
    (assert-true (member? 'gosper-check
                          (sst-rules (lambda () (sum-symbolic '(/ 1 (* k (+ k 1))) 'k 1 'n)))))))

(deftest "суммы/шаги: Σ C(n,k) неопределённая — отказ Госпера с причиной"
  (let* ((off (sum-symbolic '(binomial n k) 'k 1 'm))
         (s (sst-text (lambda () (sum-symbolic '(binomial n k) 'k 1 'm)) 'brief))
         (rs (sst-rules (lambda () (sum-symbolic '(binomial n k) 'k 1 'm)))))
    (assert-equal off '(sum (binomial n k) k 1 m))
    (assert-true (member? 'gosper-refuse rs))
    (assert-true (sst-has? s "Неопределённая сумма не гипергеометрическая"))
    (assert-true (or (sst-has? s "доказано") (sst-has? s "не гипергеометрическ")))))

(deftest "суммы/шаги: Σ k² — путь Фаульхабера, ответ не зависит от журнала"
  (let* ((off (sum-symbolic '(^ k 2) 'k 1 'n))
         (s (sst-text (lambda () (sum-symbolic '(^ k 2) 'k 1 'n)) 'brief))
         (rs (sst-rules (lambda () (sum-symbolic '(^ k 2) 'k 1 'n)))))
    (assert-true (member? 'sum-path rs))
    (assert-true (sst-has? s "Фаульхабера"))
    (assert-equal off (sum-symbolic '(^ k 2) 'k 1 'n))
    (assert-true (<= (sst-lines s) 15))))

(deftest "суммы/шаги: геометрическая — выбранный путь и формула"
  (let* ((off (sum-symbolic '(^ 2 k) 'k 0 'n))
         (s (sst-text (lambda () (sum-symbolic '(^ 2 k) 'k 0 'n)) 'brief)))
    (assert-equal (eval-num (subst (list '= 'n 5) off)) (eval-num 63))
    (assert-true (sst-has? s "геометрическая"))))

; ---------- ST.3б-2: Цайльбергер, rsolve, Абрамов ----------

(deftest "суммы/шаги: Σ C(n,k)² = C(2n,n) — Цайльбергер: порядок 1, рекуррентность, rsolve"
  (let* ((cc (capture-step-log (lambda () (sum-symbolic '(^ (binomial n k) 2) 'k 0 'n)) 'full 'ru))
         (off (car cc)) (rs (step-rules (cadr cc)))
         (cb (capture-step-log (lambda () (sum-symbolic '(^ (binomial n k) 2) 'k 0 'n)) 'brief 'ru))
         (s (steps-text (cadr cb) 'brief 'ru)))
    (assert-equal off '(binomial (* 2 n) n))
    (assert-true (member? 'zeilb-order rs))
    (assert-true (member? 'zeilb-recurrence rs))
    (assert-true (member? 'zeilb-cert rs))
    (assert-true (member? 'zeilb-check rs))
    (assert-true (member? 'rsolve-solution rs))
    (assert-true (member? 'sum-zeilberger rs))
    (assert-true (sst-has? s "J = 1"))
    (assert-true (sst-has? s "Сертификат R(n,k)"))
    (assert-true (sst-has? s "тождество проверено"))
    (assert-true (sst-has? s "тип: порядок 1"))
    (assert-true (<= (sst-lines s) 15))))

(deftest "суммы/шаги: Цайльбергер — сертификат R(n,k) проверяется, подделка отвергается"
  (let* ((F '(^ (binomial n k) 2))
         (full (zeilberger-full F 'n 'k))
         (rec (car full)) (R (cdr full)) (a (nth rec 3)))
    (assert-true (not (equal? full #f)))
    ; тождество Σ a_j·t(n+j,k) = R(k+1)·t(k+1) − R(k)·t(k) — рациональная проверка
    (assert-true (zeilberger-cert-check F 'n 'k a R))
    (assert-true (not (zeilberger-cert-check F 'n 'k a (list '+ R 1))))
    (assert-true (not (zeilberger-cert-check F 'n 'k (list 0 1) R)))
    (assert-true (not (zeilberger-cert-check F 'n 'k (list 0 0) 0)))))

(deftest "суммы/шаги: Σ C(n,k) = 2ⁿ — Цайльбергер и rsolve"
  (let* ((cc (capture-step-log (lambda () (sum-symbolic '(binomial n k) 'k 0 'n)) 'full 'ru))
         (off (car cc)) (rs (step-rules (cadr cc))))
    (assert-true (equal? (simplify off) '(^ 2 n)))
    (assert-true (member? 'rsolve-solution rs))
    (assert-true (member? 'zeilb-order rs))))

(deftest "суммы/шаги: rsolve Фибоначчи — C-конечная: χ, корни, общий вид, константы, проверка"
  ; S(n+2) = S(n+1) + S(n), S(0)=0, S(1)=1: S(5) = 5
  (let* ((rec (list 'recurrence 'S 'n (list -1 -1 1) 0 '((0 0) (1 1))))
         (cc (capture-step-log (lambda () (rsolve rec)) 'full 'ru))
         (ans (car cc)) (rs (step-rules (cadr cc)))
         (cb (capture-step-log (lambda () (rsolve rec)) 'brief 'ru))
         (s (steps-text (cadr cb) 'brief 'ru)))
    (assert-true (not (equal? ans #f)))
    (assert-true (< (abs (- (eval-num (eval (subst (list '= 'n 5) ans))) 5)) 1e-9))
    (assert-true (member? 'cf-charpoly rs))
    (assert-true (member? 'cf-roots rs))
    (assert-true (member? 'cf-general rs))
    (assert-true (member? 'cf-constants rs))
    (assert-true (member? 'cf-check rs))
    ; ST.3б-3: служебные шаги solve («относительно z», Гаусс–Жордан) в brief не попадают
    (assert-true (not (sst-has? s "относительно z")))
    (assert-true (not (sst-has? s "Гаусса")))
    (assert-true (<= (sst-lines s) 15))))

(deftest "суммы/шаги: Абрамов — f = Δg + h, проверка тождества и psi-остаток"
  (let* ((cc (capture-step-log (lambda () (sum-symbolic '(/ k (- (* k k) 1)) 'k 1 'n)) 'full 'ru))
         (ans (car cc)) (rs (step-rules (cadr cc))))
    (assert-true (not (equal? ans #f)))
    (assert-true (member? 'abramov-type rs))
    (assert-true (member? 'abramov-decompose rs))
    (assert-true (member? 'abramov-check rs))))
