; risch-steps.lisp — ST.3д-1: шаги башни exp-log, редукции Эрмита, логарифмической части
; (резольвента R(z) = res_θ(d, a − z·Dd), корни и их постоянство) и проверки первообразной.

(define (rst-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (rst-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (rst-has? s sub) (string-contains? s sub))
(define (rst-rules thunk) (step-rules (cadr (capture-step-log thunk))))

(deftest "Риш: ∫ log x dx — башня, многочленная часть и проверка"
  (let* ((s (rst-text (lambda () (risch-integrate '(log x) 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate '(log x) 'x)))))
    (assert-equal (risch-integrate '(log x) 'x) (integrate '(log x) 'x))
    (assert-true (member? 'risch rs))
    (assert-true (member? 'risch-tower rs))
    (assert-true (member? 'risch-check rs))
    (assert-true (rst-has? s "башня: ℚ(x)(θ1 = log(x))"))
    (assert-true (rst-has? s "θ1 — логарифмическое"))
    (assert-true (rst-has? s "система структурной теоремы Риша без решения"))
    (assert-true (rst-has? s "D(F) = f — проверено"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ 1/(x log x) dx — Эрмит, резольвента z − 1, log log x"
  (let* ((s (rst-text (lambda () (risch-integrate '(/ 1 (* x (log x))) 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate '(/ 1 (* x (log x))) 'x)))))
    (assert-equal (risch-integrate '(/ 1 (* x (log x))) 'x) '(log (log x)))
    (assert-true (member? 'risch-hermite rs))
    (assert-true (member? 'risch-lrt rs))
    (assert-true (member? 'risch-check rs))
    (assert-true (rst-has? s "знаменатель d = x*θ1"))
    (assert-true (rst-has? s "разложение Сквайра: (θ1)^1"))
    (assert-true (rst-has? s "резольвента R(z) = res_θ(d, a − z·Dd) = -1 + z"))
    (assert-true (rst-has? s "корни: z = 1 — корни постоянны"))
    (assert-true (rst-has? s "вычеты постоянны"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ eˣ/(eˣ+1) dx — экспоненциальный уровень и постоянный вычет"
  (let* ((s (rst-text (lambda () (risch-integrate '(/ (exp x) (+ (exp x) 1)) 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate '(/ (exp x) (+ (exp x) 1)) 'x)))))
    (assert-equal (risch-integrate '(/ (exp x) (+ (exp x) 1)) 'x) '(log (+ 1 (exp x))))
    (assert-true (member? 'risch-hermite rs))
    (assert-true (member? 'risch-lrt rs))
    (assert-true (rst-has? s "башня: ℚ(x)(θ1 = exp(x))"))
    (assert-true (rst-has? s "θ1 — экспоненциальное"))
    (assert-true (rst-has? s "корни постоянны"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ e^{x²} dx — доказанный отказ с причиной (теорема Лиувилля)"
  (let* ((s (rst-text (lambda () (risch-integrate '(exp (^ x 2)) 'x)) 'brief)))
    (assert-equal (risch-integrate '(exp (^ x 2)) 'x) #f)
    ; отказ — не «не знаю»: доказано, что первообразной нет
    (assert-equal (risch-nonelementary? '(exp (^ x 2)) 'x) #t)
    (assert-equal (risch-nonelementary? '(log x) 'x) #f)
    (assert-true (rst-has? s "интеграл неэлементарен"))
    (assert-true (rst-has? s "теорема Лиувилля"))
    (assert-true (rst-has? s "неэлементарно"))))

(deftest "Риш: ∫ log(log x)/x dx — два логарифмических уровня"
  (let* ((s (rst-text (lambda () (risch-integrate '(/ (log (log x)) x) 'x)) 'brief)))
    (assert-equal (risch-integrate '(/ (log (log x)) x) 'x)
                  '(+ (* (log x) (log (log x))) (* -1 (log x))))
    (assert-true (rst-has? s "ℚ(x)(θ1 = log(x))(θ2 = log(θ1))"))
    (assert-true (rst-has? s "замены: θ1 → log(x), θ2 → log(log(x))"))
    (assert-true (rst-has? s "Dθ2 = 1/(x*θ1)"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ x·eˣ·log x dx — частичный ответ и доказанный остаток"
  (let* ((r (risch-integrate '(* x (exp x) (log x)) 'x))
         (s (rst-text (lambda () (risch-integrate '(* x (exp x) (log x)) 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate '(* x (exp x) (log x)) 'x)))))
    (assert-true (contains-sym? r 'integrate))
    (assert-true (member? 'risch-check rs))
    (assert-true (member? 'risch-nonelementary rs))
    (assert-true (rst-has? s "D(F) = f − R — проверено"))
    (assert-true (rst-has? s "остаток неэлементарен"))
    (assert-true (rst-has? s "∫ exp(x)/x dx"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: шаг проверки отвергает подделку (D(F) ≠ f)"
  ; настоящие первообразные проходят
  (assert-true (int-check '(+ (* -1 x) (* x (log x))) '(log x) 'x))
  (assert-true (int-check '(log (log x)) '(/ 1 (* x (log x))) 'x))
  (assert-true (int-check '(log (+ 1 (exp x))) '(/ (exp x) (+ (exp x) 1)) 'x))
  ; подделки — нет
  (assert-equal (int-check '(* x (log x)) '(log x) 'x) #f)
  (assert-equal (int-check '(log x) '(/ 1 (* x (log x))) 'x) #f)
  (assert-equal (int-check '(log (+ 2 (exp x))) '(/ (exp x) (+ (exp x) 1)) 'x) #f)
  ; журнал не меняет ответа Риша
  (assert-equal (risch-integrate '(log x) 'x)
                (car (capture-step-log (lambda () (risch-integrate '(log x) 'x)) 'brief 'ru))))

; ---------- ST.3д-2: многочленная часть, уравнение Риша, тангенс-уровень ----------

(deftest "Риш: ∫ 2x·e^{x²} dx — уравнение Риша с решением"
  (let* ((e '(* 2 x (exp (^ x 2))))
         (s (rst-text (lambda () (risch-integrate e 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate e 'x)))))
    (assert-equal (risch-integrate e 'x) '(exp (^ x 2)))
    (assert-true (member? 'risch-rde rs))
    (assert-true (rst-has? s "уравнение Риша"))
    (assert-true (rst-has? s "f = 2x, g = 2x"))
    (assert-true (rst-has? s "поле ниже — база ℚ(x)"))
    (assert-true (rst-has? s "найдено решение y в поле ниже"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ e^{x²} dx — уравнение Риша без решения ⇒ отказ с причиной"
  (let* ((e '(exp (^ x 2)))
         (s (rst-text (lambda () (risch-integrate e 'x)) 'brief)))
    (assert-equal (risch-integrate e 'x) #f)
    (assert-true (rst-has? s "интеграл неэлементарен"))
    (assert-true (rst-has? s "старшие члены: deg c < deg b — многочлена-решения нет"))
    (assert-true (rst-has? s "неэлементарно"))))

(deftest "Риш: ∫ x·eˣ dx — уравнение Риша Dy + y = x"
  (let* ((e '(* x (exp x)))
         (s (rst-text (lambda () (risch-integrate e 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate e 'x)))))
    (assert-equal (risch-integrate e 'x) '(* (+ -1 x) (exp x)))
    (assert-true (member? 'risch-rde rs))
    (assert-true (rst-has? s "f = 1, g = x"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ log²x dx — многочленная часть, deg P = 2"
  (let* ((e '(^ (log x) 2))
         (s (rst-text (lambda () (risch-integrate e 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate e 'x)))))
    (assert-equal (risch-integrate e 'x) '(+ (* 2 x) (* -2 x (log x)) (* x (^ (log x) 2))))
    (assert-true (member? 'risch-poly rs))
    (assert-true (rst-has? s "многочленная часть"))
    (assert-true (rst-has? s "P = θ1^2"))
    (assert-true (rst-has? s "deg P = 2"))
    (assert-true (rst-has? s "a2 = 1"))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ tan x dx — тангенс-уровень, ответ проходит проверку"
  (let* ((e '(tan x))
         (s (rst-text (lambda () (risch-integrate e 'x)) 'brief))
         (rs (rst-rules (lambda () (risch-integrate e 'x))))
         (F (risch-integrate e 'x)))
    (assert-true (member? 'risch-tan rs))
    (assert-true (rst-has? s "тангенс-уровень"))
    (assert-true (rst-has? s "Dθ = Du·(1 + θ²)"))
    (assert-true (rst-has? s "специальная часть"))
    ; ответ в полуугловой форме — проверяется подстановкой, а не формой
    (assert-true (int-check F e 'x))
    (assert-true (<= (rst-lines s) 15))))

(deftest "Риш: ∫ (1 + tan²x)·eˣ dx — доказанный отказ"
  (let* ((e '(* (+ 1 (^ (tan x) 2)) (exp x)))
         (s (rst-text (lambda () (risch-integrate e 'x)) 'brief)))
    (assert-equal (risch-integrate e 'x) #f)
    (assert-true (rst-has? s "интеграл неэлементарен"))
    (assert-true (rst-has? s "теорема Лиувилля"))))
