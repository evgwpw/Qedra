; ST.3г-1: шаги Галуа и денестинга — данные для проверки, сертификат и подделки;
; ответы не меняются от журнала, brief ≤ 15 строк.

(define (ast-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (ast-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (ast-has? s sub) (string-contains? s sub))
(define (ast-rules thunk) (step-rules (cadr (capture-step-log thunk))))

(define ast-s5 '(+ (^ x 5) (* -1 x) -1))
(define ast-f5 '(+ (^ x 5) -2))

(deftest "Галуа: x⁵ − x − 1 — S₅, дискриминант не квадрат, сертификат и подделка"
  (let* ((off (galois-group ast-s5 'x))
         (s (ast-text (lambda () (galois-group ast-s5 'x)) 'brief))
         (rs (ast-rules (lambda () (galois-group ast-s5 'x)))))
    (assert-equal (nth off 1) 'S5)
    (assert-equal (nth off 2) 120)
    (assert-true (galois-group-check ast-s5 'x off))
    ; подделка имени группы отвергается независимой проверкой
    (assert-true (not (galois-group-check ast-s5 'x (cons (car off) (cons 'A5 (cddr off))))))
    (assert-true (member? 'gal-irreducible rs))
    (assert-true (member? 'gal-discriminant rs))
    (assert-true (member? 'gal-cycles rs))
    (assert-true (member? 'gal-conclusion rs))
    (assert-true (ast-has? s "Неприводимость над Q"))
    (assert-true (ast-has? s "не квадрат"))
    (assert-true (ast-has? s "Типы циклов"))
    (assert-true (ast-has? s "Группа Галуа"))
    (assert-true (ast-has? s "S5"))
    (assert-true (<= (ast-lines s) 15))))

(deftest "Галуа: x⁴ + 1 — V₄, дискриминант квадрат"
  (let* ((off (galois-group '(+ (^ x 4) 1) 'x))
         (s (ast-text (lambda () (galois-group '(+ (^ x 4) 1) 'x)) 'brief)))
    (assert-equal (nth off 1) 'V4)
    (assert-equal (nth off 2) 4)
    (assert-true (galois-group-check '(+ (^ x 4) 1) 'x off))
    (assert-true (ast-has? s "точный квадрат"))
    (assert-true (ast-has? s "V4"))))

(deftest "Галуа: x³ − 3x + 1 — A₃ (C₃), дискриминант 81"
  (let* ((off (galois-group '(+ (^ x 3) (* -3 x) 1) 'x))
         (sol (galois-solvability '(+ (^ x 3) (* -3 x) 1) 'x)))
    (assert-equal (nth off 1) 'C3)
    (assert-equal (nth off 2) 3)
    (assert-true (galois-group-check '(+ (^ x 3) (* -3 x) 1) 'x off))
    ; степень ≤ 4 — разрешимость по формулам, без вычисления группы
    (assert-equal (car sol) #t)
    (assert-equal (nth sol 1) :degree)))

(deftest "Галуа: x⁵ − 2 — F₂₀, разрешима; у S₅ — нет"
  (let* ((off (galois-group ast-f5 'x))
         (sol (galois-solvability ast-f5 'x))
         (s (ast-text (lambda () (solvable-by-radicals? ast-s5 'x)) 'brief)))
    (assert-equal (nth off 1) 'F20)
    (assert-equal (nth off 2) 20)
    (assert-true (galois-group-check ast-f5 'x off))
    (assert-equal (car sol) #t)
    (assert-equal (galois-solvability ast-s5 'x) (list #f :group 'S5))
    (assert-equal (solvable-by-radicals? ast-s5 'x) #f)
    (assert-true (ast-has? s "не разрешима"))
    (assert-true (ast-has? s "A₅"))))

(deftest "Денестинг: √(3 + 2√2) = 1 + √2, √(5 + 2√6) = √2 + √3"
  (let* ((off (sqrt-denest '(^ (+ 3 (* 2 (^ 2 1/2))) 1/2)))
         (s (ast-text (lambda () (sqrt-denest '(^ (+ 3 (* 2 (^ 2 1/2))) 1/2))) 'brief))
         (rs (ast-rules (lambda () (sqrt-denest '(^ (+ 3 (* 2 (^ 2 1/2))) 1/2))))))
    (assert-equal off (simplify '(+ 1 (^ 2 1/2))))
    (assert-equal (sqrt-denest '(^ (+ 5 (* 2 (^ 6 1/2))) 1/2))
                  (simplify '(+ (^ 2 1/2) (^ 3 1/2))))
    (assert-true (member? 'dn-formula rs))
    (assert-true (ast-has? s "a² − b²r = c²"))
    (assert-true (ast-has? s "проверено возведением в квадрат"))
    (assert-true (<= (ast-lines s) 15))
    (assert-true (not (denest-check? '(+ 3 (* 2 (^ 2 1/2))) '(- -1 (^ 2 1/2)))))))

(deftest "Денестинг: √(1 + √2) неденестируем — причина в шаге"
  (let* ((off (sqrt-denest '(^ (+ 1 (^ 2 1/2)) 1/2)))
         (s (ast-text (lambda () (sqrt-denest '(^ (+ 1 (^ 2 1/2)) 1/2))) 'brief))
         (rs (ast-rules (lambda () (sqrt-denest '(^ (+ 1 (^ 2 1/2)) 1/2))))))
    (assert-equal off '(^ (+ 1 (^ 2 1/2)) 1/2))
    (assert-true (member? 'dn-refuse rs))
    (assert-true (ast-has? s "не квадрат"))
    (assert-true (<= (ast-lines s) 15))))

; ---------- ST.3г-2: диофантовы уравнения, суммы квадратов и SOS ----------

(deftest "Диофант: 3x + 5y = 7 — Безу, частное и общее решение"
  (let* ((r (solve-linear-diophantine 3 5 7))
         (s (ast-text (lambda () (solve-linear-diophantine 3 5 7)) 'brief))
         (rs (ast-rules (lambda () (solve-linear-diophantine 3 5 7)))))
    (assert-equal (+ (* 3 (car (car r))) (* 5 (cadr (car r)))) 7)
    (assert-equal (+ (* 3 (car (cadr r))) (* 5 (cadr (cadr r)))) 0)
    (assert-true (member? 'dio-bezout rs))
    (assert-true (member? 'dio-particular rs))
    (assert-true (member? 'dio-general rs))
    (assert-true (ast-has? s "Расширенный Евклид"))
    (assert-true (ast-has? s "Частное решение"))
    (assert-true (ast-has? s "Общее решение"))
    (assert-true (ast-has? s "проверено"))
    (assert-true (<= (ast-lines s) 15))))

(deftest "Диофант: 6x + 4y = 3 — НОД 2 не делит 3, решений нет"
  (let* ((r (solve-linear-diophantine 6 4 3))
         (s (ast-text (lambda () (solve-linear-diophantine 6 4 3)) 'brief)))
    (assert-equal r #f)
    (assert-true (ast-has? s "НОД 2 не делит 3"))))

(deftest "Пелль: x² − 61y² = 1 — период и фундаментальное решение"
  (let* ((r (pell 61))
         (s (ast-text (lambda () (pell 61)) 'brief))
         (rs (ast-rules (lambda () (pell 61)))))
    (assert-equal r (list 1766319049 226153980))
    (assert-true (member? 'pell-cf rs))
    (assert-true (member? 'pell-check rs))
    (assert-true (ast-has? s "период цепной дроби"))
    (assert-true (ast-has? s "проверено"))
    (assert-true (<= (ast-lines s) 15))
    (assert-true (not (= (- (* 1766319049 1766319049) (* 61 226153980 226153980)) 2)))))

(deftest "Пелль: x² − 3y² = −1 — период чётен, решения нет"
  (let* ((s (ast-text (lambda () (pell-negative 3)) 'brief)))
    (assert-equal (pell-negative 3) #f)
    (assert-true (ast-has? s "чётен"))
    (assert-true (ast-has? s "решений не имеет"))))

(deftest "Суммы квадратов: 2025 = a² + b², 7 — не сумма трёх квадратов"
  (let* ((r (two-squares 2025))
         (s (ast-text (lambda () (two-squares 2025)) 'brief))
         (s3 (ast-text (lambda () (three-squares 7)) 'brief)))
    (assert-true (member? (list 45 0) r))
    (assert-equal (+ (* 36 36) (* 27 27)) 2025)
    (assert-true (ast-has? s "Проверка суммы квадратов"))
    (assert-equal (three-squares 7) (list 'none 'legendre 0 7))
    (assert-true (ast-has? s3 "8b + 7"))
    (assert-equal (four-squares 7) (list 2 1 1 1))))

(deftest "SOS: x⁴ + y⁴ − 2x²y² и x² − x + 1 — разложение, проверка и подделка"
  (let* ((p '(- (+ (^ x 4) (^ y 4)) (* 2 (^ x 2) (^ y 2))))
         (r (prove-nonneg p '(x y)))
         (s (ast-text (lambda () (prove-nonneg p '(x y))) 'brief))
         (rs (ast-rules (lambda () (prove-nonneg p '(x y))))))
    (assert-equal (car r) 'proved)
    (assert-true (sos-check p '(x y) (cadr r)))
    (assert-true (not (sos-check p '(x y) '())))
    (assert-true (member? 'sos-method rs))
    (assert-true (member? 'sos-decomposition rs))
    (assert-true (member? 'sos-check rs))
    (assert-true (ast-has? s "Метод доказательства"))
    (assert-true (ast-has? s "Разложение в сумму квадратов"))
    (assert-true (ast-has? s "тождество"))
    (assert-true (<= (ast-lines s) 15))
    (assert-equal (car (prove-nonneg '(+ (^ x 2) (* -1 x) 1) 'x)) 'proved)))
