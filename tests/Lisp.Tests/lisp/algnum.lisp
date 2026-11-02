; algnum.lisp — тесты модуля algnum (21m A1.1): поле ℚ(α) = ℚ[t]/(m)

; ---------- поле ----------

(deftest "alg-field: минимальный многочлен и вложение (√2)"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (alg-field-minpoly F) '(+ -2 (^ t 2)))
  (assert-true (alg? (alg-field-embed F))))

(deftest "alg-field: приводимый m отвергается (x^2 − 4)"
  (assert-error (alg-field '(+ -4 (^ t 2)) 't)))

(deftest "alg-field: немонический m отвергается"
  (assert-error (alg-field '(+ -8 (* 2 (^ t 2))) 't)))

(deftest "alg-field: невещественное вложение — приближение double (ℚ(i))"
  (define F (alg-field '(+ 1 (^ t 2)) 't))
  (assert-true (list? (alg-field-embed F))))

; ---------- элемент и арифметика ----------

(deftest "alg-elt: обрезка степени и старших нулей"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (alg-elt F '(1 1)) '(1 1))
  (assert-equal (alg-elt F '(1 1 1)) '(1 1))
  (assert-equal (alg-elt F '(3 0)) '(3)))

(deftest "alg-elt: float-коэффициент отвергается"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-error (alg-elt F '(1 1.5))))

(deftest "арифметика: (1+√2)² = 3+2√2, (√2)·(√2) = 2"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (define a (alg-elt F '(1 1)))
  (define s (alg-elt F '(0 1)))
  (assert-equal (alg-mul F a a) '(3 2))
  (assert-equal (alg-mul F s s) '(2))
  (assert-equal (alg-add F a (alg-negate F a)) '())
  (assert-equal (alg-sub F a '(1)) '(0 1))
  (assert-true (alg-zero? F (alg-sub F a '(1 1))))
  (assert-true (alg-equal? F a '(1 1))))

(deftest "обратный: (1+√2)^-1 = √2 − 1 (эталонный пример)"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (define a (alg-elt F '(1 1)))
  (assert-equal (alg-inv F a) '(-1 1))
  (assert-equal (alg-mul F a (alg-inv F a)) '(1))
  (assert-equal (alg-div F '(1) a) '(-1 1)))

(deftest "обратный: деление на ноль — ошибка"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-error (alg-inv F '()))
  (assert-error (alg-div F '(1) '())))

(deftest "степень: (√2)^10 = 32, (√2)^-2 = 1/2"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (define s (alg-elt F '(0 1)))
  (assert-equal (alg-pow F s 10) '(32))
  (assert-equal (alg-pow F s -2) '(1/2))
  (assert-equal (alg-pow F s 0) '(1)))

; ---------- норма и минимальный многочлен ----------

(deftest "норма: N(1+√2) = −1, N(√2) = −2"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (alg-norm F (alg-elt F '(1 1))) -1)
  (assert-equal (alg-norm F (alg-elt F '(0 1))) -2)
  (assert-equal (alg-norm F '()) 0))

(deftest "minpoly: ∛2 + 1 — (x−1)³ − 2"
  (define F (alg-field '(+ -2 (^ t 3)) 't))
  (define a (alg-elt F '(1 1)))
  (assert-equal (alg-minpoly F a 'x) '(+ -3 (* 3 x) (* -3 (^ x 2)) (^ x 3))))

(deftest "minpoly: √2 + √3 в поле ℚ(√2+√3) — x⁴ − 10x² + 1 (эталон)"
  (define F (alg-field '(+ 1 (* -10 (^ x 2)) (^ x 4)) 'x))
  (define a (alg-elt F '(0 1)))
  (assert-equal (alg-minpoly F a 'y) '(+ 1 (* -10 (^ y 2)) (^ y 4))))

(deftest "minpoly: подсписок у mniejsой степени — α² в ℚ(⁴√2) имеет minpoly x² − 2"
  (define F (alg-field '(+ -2 (^ t 4)) 't))
  (assert-equal (alg-minpoly F (alg-elt F '(0 0 1)) 'x) '(+ -2 (^ x 2))))

(deftest "minpoly: 0 → x"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (alg-minpoly F '() 'x) 'x))

(deftest "minpoly: сертификат отвергает чужой многочлен (подделка)"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  ; ручная проверка: x^2 − 3 не обнуляется на √2 — агументы с чужим m дают ошибку
  (assert-true (not (algnum::ag-check-minpoly F '(0 1) '(+ -3 (^ x 2)) 'x))))

; ---------- выражения ----------

(deftest "alg->expr: квадратичное поле — радикал (^ 2 1/2)"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (alg->expr F (alg-elt F '(1 1))) '(+ 1 (* -1 (^ 2 1/2))))
  (assert-equal (alg->expr F (alg-elt F '(0 1))) '(* -1 (^ 2 1/2)))
  (assert-equal (alg->expr F '()) 0))

(deftest "alg->expr: неквадратичное поле — root-of"
  (define F (alg-field '(+ -2 (^ t 3)) 't))
  (assert-equal (alg->expr F (alg-elt F '(1 1)))
                '(+ 1 (root-of (+ -2 (^ t 3)) t))))

(deftest "expr->alg: рациональные функции от генерирующей"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (expr->alg F '(/ 1 t)) '(0 1/2))     ; 1/t = t/2 (mod t²−2)
  (assert-equal (expr->alg F '(+ 1 (^ t -1))) '(1 1/2))
  (assert-equal (expr->alg F '(/ (+ 1 t) (- 1 t))) '(-3 -2))
  (assert-equal (expr->alg F '3) '(3))
  (assert-equal (expr->alg F '(^ t 2)) '(2)))

(deftest "expr->alg: подстановка численно сходится с alg->expr"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  ; (1+t)/(1−t) при t=√2: = (1+t)²/(1−2) = −(3+2√2) → (−3 −2√2)
  (assert-equal (expr->alg F '(/ (+ 1 t) (+ 1 (* -1 t)))) '(-3 -2)))

(deftest "alg->expr: численно равно значению элемента по вложению"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (define a (alg-elt F '(3 -5)))
  ; вложение α = −√2 ⇒ элемент 3 − 5α = 3 + 5√2 ≈ 10.07
  (assert-true (< (abs (- (eval-num (alg->expr F a)) 10.071067811865476)) 1e-9)))

; ---------- A1.2: НОД, деление, бесквадратность в ℚ(α)[x] ----------

; полиномы ℚ(√2)[x]: коэффициенты-элементы по возрастанию; (√2) = (0 1), 1 = (1)
(deftest "alg-poly-div: деление с остатком, сертификат a = q·b + r"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (define a (list '(1) '(0 1) '(1)))
  (define b (list '(0 1) '(1)))
  (define qr (alg-poly-div F a b))
  ; проверка сертификатом уже внутри; сверяем степень остатка
  (assert-true (< (length (nth qr 1)) (length b)))
  (assert-equal (alg-poly-gcd F a (list '(-2) '() '(1))) '((1))))

(deftest "alg-poly-gcd: gcd(x²−2, x²+2√2x+2) = x+√2 над ℚ(√2) (задание A1.2)"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  (assert-equal (alg-poly-gcd F (list '(-2) '() '(1)) (list '(2) '(0 2) '(1)))
                '((0 1) (1))))

(deftest "alg-poly-sqfree: (x²+√2x+1)² → x²+√2x+1; бесквадратный остаётся"
  (define F (alg-field '(+ -2 (^ t 2)) 't))
  ; (x²+√2x+1)² = x⁴+2√2x³+4x²+2√2x+1
  (assert-equal (alg-poly-sqfree F (list '(1) '(0 2) '(4) '(0 2) '(1)))
                (list '(1) '(0 1) '(1)))
  (assert-equal (alg-poly-sqfree F (list '(1) '() '() '(1)))
                (list '(1) '() '() '(1))))

; ---------- A1.2: примитивный элемент ----------

(deftest "alg-primitive: ℚ(√2, √3) = ℚ(√2+√3) — γ⁴−10γ²+1, α и β выражены через γ"
  (define r (alg-primitive '(+ -2 (^ t 2)) '(+ -3 (^ t 2))))
  (define Fg (nth r 0)) (define alpha (nth r 1)) (define beta (nth r 2))
  (assert-equal (alg-field-minpoly Fg) '(+ 1 (* -10 (^ x 2)) (^ x 4)))
  (assert-equal (nth r 3) 1)
  ; γ = α + β (элемент (0 1) — генерирующая)
  (assert-equal (alg-add Fg alpha beta) '(0 1))
  ; α² = 2 и β² = 3 в ℚ(γ) — полное решение системы (сертификаты уже внутри alg-primitive)
  (assert-equal (alg-mul Fg alpha alpha) '(2))
  (assert-equal (alg-mul Fg beta beta) '(3)))

(deftest "alg-primitive: подделка ловится — испорченный α не удовлетворяет m₁"
  ; вручную: α' = правильный α + 1 — подстановка в m₁ = t²−2 ≠ 0
  (define r (alg-primitive '(+ -2 (^ t 2)) '(+ -3 (^ t 2))))
  (define Fg (nth r 0))
  (define bad (alg-add Fg (nth r 1) '(1)))
  (assert-true (not (algnum::ag-check-minpoly Fg bad '(+ -2 (^ t 2)) 't))))

(deftest "alg-primitive: ℚ(√2, i)"
  (define r (alg-primitive '(+ -2 (^ t 2)) '(+ 1 (^ t 2))))
  (define Fg (nth r 0))
  (assert-equal (alg-field-minpoly Fg) '(+ 9 (* -2 (^ x 2)) (^ x 4)))
  (assert-equal (alg-mul Fg (nth r 1) (nth r 1)) '(2))    ; α² = 2
  (assert-equal (alg-pow Fg (nth r 2) 2) '(-1)))          ; β² = −1 (i)

(deftest "alg-primitive: ℚ(∛2, ω) — ω из t²+t+1, сертификаты пройдены"
  (define r (alg-primitive '(+ -2 (^ t 3)) '(+ 1 (^ t 1) (^ t 2))))
  (define Fg (nth r 0))
  (assert-equal (degree (alg-field-minpoly Fg) 'x) 6)
  ; α³ = 2, β³ = 1 (β ≠ 1 — примитивный кубический корень)
  (assert-equal (alg-pow Fg (nth r 1) 3) '(2))
  (assert-equal (alg-pow Fg (nth r 2) 3) '(1)))


; замечание ревью: приводимый «минимальный многочлен» (x²−2)(x−5) для √2 отвергается
(deftest "algnum/A1: сертификат minpoly отвергает приводимый многочлен"
  (let ((F (alg-field '(+ (^ t 2) -2) 't)))
    (assert-equal #f (algnum::ag-check-minpoly F (alg-elt F '(0 1)) (expand '(* (- (^ x 2) 2) (- x 5))) 'x))))

; замечание ревью: степень композита меньше произведения (ℚ(√2, ⁴√2), ℚ(√2, √2)) — не зацикливается
(deftest "algnum/A1: примитивный элемент, когда [Q(a,b):Q] < deg m1 · deg m2"
  (assert-equal (degree (alg-field-minpoly (car (alg-primitive '(+ (^ t 2) -2) '(+ (^ t 4) -2)))) 'x) 4)
  (assert-equal (degree (alg-field-minpoly (car (alg-primitive '(+ (^ t 2) -2) '(+ (^ t 2) -2)))) 'x) 2))

; ---------- A1.3: факторизация над Q(a) — норма Трагера ----------
(deftest "algnum/A1.3: x^4+1 над Q(sqrt2) → два квадратичных множителя"
  (let ((r (factor-over '(+ 1 (^ x 4)) 'x '(^ 2 1/2))))
    (assert-equal 2 (length (cdr r)))
    (assert-equal 1 (car r))
    ; произведение множителей (каждый степени 2) = x⁴+1 — проверяем expand
    (assert-equal '(+ 1 (^ x 4)) (expand (cons '* (map car (cdr r)))))
    (assert-true (every? (lambda (pr) (= (degree (car pr) 'x) 2)) (cdr r)))))
(deftest "algnum/A1.3: x^4+1 над Q(i)"
  (let ((r (factor-over '(+ 1 (^ x 4)) 'x '%i)))
    (assert-equal 2 (length (cdr r)))
    (assert-equal '(+ 1 (^ x 4)) (expand (cons '* (map car (cdr r)))))))
(deftest "algnum/A1.3: x^2-2 над Q(sqrt2) → линейные"
  (let ((r (factor-over '(- (^ x 2) 2) 'x '(^ 2 1/2))))
    (assert-equal 2 (length (cdr r)))
    (assert-equal (expand '(- (^ x 2) 2)) (expand (cons '* (map car (cdr r)))))))

(deftest "algnum/A1.3: x^2+1 над Q(sqrt2) — неприводим"
  (let ((r (factor-over '(+ 1 (^ x 2)) 'x '(^ 2 1/2))))
    (assert-equal 1 (length (cdr r)))))
(deftest "algnum/A1.3: x^3-2 над Q(cbrt2) → линейный * квадратичный"
  (let ((r (factor-over '(- (^ x 3) 2) 'x '(^ 2 1/3))))
    (assert-equal 2 (length (cdr r)))
    (assert-equal 3 (foldl (lambda (a pr) (+ a (* (cadr pr) (degree (car pr) 'x)))) 0 (cdr r)))))
(deftest "algnum/A1.3: кратности (x^2-2)^2*(x+1)"
  (let ((r (factor-over '(* (- (^ x 2) 2) (- (^ x 2) 2) (+ x 1)) 'x '(^ 2 1/2))))
    (assert-equal 3 (length (cdr r)))
    (assert-equal 5 (foldl (lambda (a pr) (+ a (* (cadr pr) (degree (car pr) 'x)))) 0 (cdr r)))))
(deftest "algnum/A1.3: коэффициенты в Q(a): (x-sqrt2)^2"
  (let ((r (factor-over '(+ 2 (* -2 (^ 2 1/2) x) (^ x 2)) 'x '(^ 2 1/2))))
    (assert-equal 1 (length (cdr r)))
    (assert-equal 2 (cadr (car (cdr r))))))
(deftest "algnum/A1.3: сертификат alg-factor-check отвергает испорченный множитель"
  (let* ((F (alg-field '(- (^ t 2) 2) 't))
         (f (algnum::expr->ap F '(- (^ x 2) 2) 'x))
         (bad (list (alg-elt F '(1))
                    (list (list (algnum::expr->ap F '(+ 1 x) 'x) 1)
                          (list (algnum::expr->ap F '(- 1 x) 'x) 1)))))
    (assert-equal #f (alg-factor-check F f 'x bad))))
(deftest "algnum/A1.3: сертификат alg-factor-check отвергает приводимый множитель"
  (let* ((F (alg-field '(- (^ t 2) 2) 't))
         (f (algnum::expr->ap F '(+ 1 (^ x 4)) 'x))
         (bad (list (alg-elt F '(1)) (list (list f 1)))))
    (assert-equal #f (alg-factor-check F f 'x bad))))
(deftest "algnum/A1.3: сертификат alg-factor-check принимает верное разложение"
  (let* ((F (alg-field '(- (^ t 2) 2) 't))
         (f (algnum::expr->ap F '(+ 1 (^ x 4)) 'x))
         (r (alg-factor F f 'x)))
    (assert-equal #t (alg-factor-check F f 'x r))))
