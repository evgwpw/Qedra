; constzero.lisp — тесты шага R4: нуль констант (интервалы, тождества, unknown).

(define cz-denest '(+ (^ (+ 3 (* 2 (^ 2 1/2))) 1/2) -1 (* -1 (^ 2 1/2))))

(deftest "r4: скрытый нуль — вложенный радикал (денестинг)"
  (assert-equal (const-zero? cz-denest) #t))

(deftest "r4: скрытый нуль — log 6 = log 2 + log 3"
  (assert-equal (const-zero? '(+ (log 6) (* -1 (log 2)) (* -1 (log 3)))) #t))

(deftest "r4: скрытый нуль — exp(2 log 3) = 9"
  (assert-equal (const-zero? '(+ (exp (* 2 (log 3))) -9)) #t))

(deftest "r4: скрытый нуль — sin(pi/6) = 1/2"
  (assert-equal (const-zero? '(+ (sin (/ pi 6)) -1/2)) #t))

(deftest "r4: log 12 = 2 log 2 + log 3 и log(1/6)"
  (assert-equal (const-zero? '(+ (log 12) (* -2 (log 2)) (* -1 (log 3)))) #t)
  (assert-equal (const-zero? '(+ (log 1/6) (log 2) (log 3))) #t))

(deftest "r4: не нуль — pi и 355/113 (интервал)"
  (assert-equal (const-zero? '(+ pi -355/113)) #f))

(deftest "r4: не нуль — exp(pi) и pi^e (интервал)"
  (assert-equal (const-zero? '(+ (exp pi) (* -1 (^ pi (exp 1))))) #f))

(deftest "r4: не нуль — log 2 и √2 − 1 (точное число и интервал)"
  (assert-equal (const-zero? '(log 2)) #f)
  (assert-equal (const-zero? '(+ (^ 2 1/2) -1)) #f)
  (assert-equal (const-zero? 5) #f)
  (assert-equal (const-zero? 0) #t))

(deftest "r4: рациональное приближение e − π не равно нулю (интервал различает)"
  (assert-equal (const-zero? '(+ e (* -1 pi) 4233108251307480/10000000000000000)) #f))

(deftest "r4: настоящий нуль, которого нет в упрощателе, — unknown, не #f"
  ; cos(pi/5) = (1 + √5)/4 — верное тождество; включение содержит 0, а числа нуля не доказывают
  (assert-equal (const-zero? '(+ (cos (/ pi 5)) (* -1 (/ (+ 1 (^ 5 1/2)) 4)))) 'unknown))

(deftest "r4: параметр и float — unknown (константой не считаются)"
  (assert-equal (const-zero? 'a) 'unknown)
  (assert-equal (const-zero? '(+ a (log 2))) 'unknown)
  (assert-equal (const-zero? 0.5) 'unknown))

(deftest "r4: const-enclosure — строгое включение и точность"
  (let ((X (const-enclosure '(+ (^ 2 1/2) (log 3)) 30)))
    (assert-true (iv-subset? X (iv 2512825851/1000000000 2512825852/1000000000)))
    (assert-true (< (iv-width X) 1/10000000000000000000000000))
    (assert-equal (const-enclosure '(log 0) 30) #f)
    (assert-equal (iv-precision) 30)))

(deftest "r4: const-clean убирает скрытые нули и оставляет остальное"
  (let ((r (const-clean (list '+ (list '* cz-denest '(exp (^ x 2))) 'x) 'x)))
    (assert-equal (car r) 'x)
    (assert-equal (cadr r) #f))
  (let ((r (const-clean '(* (+ (log 6) (* -1 (log 2)) (* -1 (log 3))) (exp (^ x 2))) 'x)))
    (assert-equal (car r) 0))
  (let ((r (const-clean '(+ (* (+ (log 6) 1) (exp (^ x 2))) x) 'x)))
    (assert-equal (cadr r) #f)
    (assert-true (contains-sym? (car r) 'exp)))
  (let ((r (const-clean '(* (+ (cos (/ pi 5)) (* -1 (/ (+ 1 (^ 5 1/2)) 4))) (exp x)) 'x)))
    (assert-equal (cadr r) #t)))

(deftest "r4: iv-set-precision! — меняет ширину, строгость сохраняется"
  (let ((w30 (iv-width (begin (iv-set-precision! 30) (iv-pi))))
        (w50 (iv-width (begin (iv-set-precision! 50) (iv-pi)))))
    (iv-set-precision! 30)
    (assert-true (< w50 w30))
    (assert-true (iv-contains? (iv-pi) 3141592653589793238462643383279/1000000000000000000000000000000))))

(deftest "r4: комплексные константы — Re и Im по отдельности (log −1 = iπ)"
  (assert-equal (const-zero? '(log -1)) #f)
  (assert-equal (const-zero? '(+ (log -1) (* -1 %i pi))) #t)
  (assert-equal (const-zero? '(+ (^ (+ 1 %i) 2) (* -2 %i))) #t)
  (assert-equal (const-zero? '(+ (exp (* %i pi)) 1)) #t)
  (assert-equal (const-zero? '(+ (log -2) (* -1 (log 2)))) #f))

; ---------- R4.2: соотношения, независимость, классификация ----------
(deftest "r4.2: log 12 = 2 log 2 + log 3 найдено точно"
  (let ((rs (const-relations '((log 12) (log 2) (log 3)))))
    (assert-equal (length rs) 1)
    (assert-equal (const-relation-holds? '((log 12) (log 2) (log 3)) (car rs)) #t)
    (assert-equal (const-relation-holds? '((log 12) (log 2) (log 3)) '(1 -2 -1)) #t)))

(deftest "r4.2: log 2, log 3, log 5 независимы (Бейкер: и над алгебраическими)"
  (assert-equal (log-independent? '((log 2) (log 3) (log 5))) #t)
  (assert-equal (const-relations '((log 2) (log 3) (log 5))) '())
  (assert-equal (log-independent? '((log 6) (log 2) (log 3))) #f)
  (assert-equal (length (const-relations '((log 6) (log 2) (log 3) (log 12)))) 2))

(deftest "r4.2: log 2 и log 4 зависимы (одно соотношение), 2 log 3 = log 9"
  (let ((rs (const-relations '((log 2) (log 4)))))
    (assert-equal (length rs) 1)
    (assert-equal (const-relation-holds? '((log 2) (log 4)) (car rs)) #t))
  (assert-equal (log-independent? '((log 3) (log 9))) #f)
  (assert-equal (log-independent? '(pi)) 'unknown))

(deftest "r4.2: ложное соотношение log 6 = log 2 + 2 log 3 отвергнуто"
  (assert-equal (const-relation-holds? '((log 6) (log 2) (log 3)) '(1 -1 -2)) #f)
  (assert-equal (const-relation-holds? '((log 6) (log 2) (log 3)) '(1 -1 -1)) #t)
  (assert-equal (const-zero? '(+ (log 6) (* -1 (log 2)) (* -2 (log 3)))) #f)
  (assert-equal (const-zero? '(+ 1 (* -1 (log 2)))) #f))

(deftest "r4.2: арктангенсы рациональных — точный нуль и точный не-нуль (гауссовы числа)"
  (assert-equal (const-zero? '(+ (atan 1/2) (atan 1/3) (* -1/4 pi))) #t)
  (assert-equal (const-zero? '(+ (atan 1/2) (atan 1/3) (* -1/3 pi))) #f)
  (assert-equal (const-zero? '(+ (atan 5/11) (atan 11/5) (* -1/2 pi))) #t)
  (assert-equal (const-zero? '(+ (* 4 (atan 1/5)) (* -1 (atan 1/239)) (* -1/4 pi))) #t)
  (assert-equal (const-zero? '(+ (atan 2) (atan 3) (* -3/4 pi))) #t)
  (assert-equal (const-zero? '(+ (atan 2) (atan 3) (* -1/4 pi))) #f))

(deftest "r4.2: PSLQ — кандидат, проходит только после доказательства"
  (assert-equal (const-pslq '((atan 1/2) (atan 1/3) pi) 45) '(-4 -4 1))
  (assert-equal (const-relations '((atan 1/2) (atan 1/3) pi)) '((-4 -4 1)))
  ; π и e: численный кандидат (π + e − (π + e)) есть, но это тривиальное соотношение; между π и e соотношений не найдено
  (assert-equal (const-relations '(pi e)) '())
  (assert-equal (const-pslq '(1 2 3) 30) '(1 1 -1)))

(deftest "r4.2: классификация — только доказанные теоремы"
  (assert-equal (const-class '(^ 2 1/2)) 'algebraic)
  (assert-equal (const-class 'pi) 'transcendental)
  (assert-equal (const-class '(exp pi)) 'transcendental)            ; Гельфонд
  (assert-equal (const-class '(+ 1 (exp 1))) 'transcendental)
  (assert-equal (const-class '(log 3)) 'transcendental)
  (assert-equal (const-class '(sin 1)) 'transcendental)
  (assert-equal (const-class '(^ 2 (^ 2 1/2))) 'transcendental)     ; Гельфонд — Шнайдер
  (assert-equal (const-class '(exp (* %i pi))) 'algebraic)
  (assert-equal (const-class '(+ e pi)) 'unknown)                   ; открытая проблема
  (assert-equal (const-class '(^ pi e)) 'unknown)
  (assert-equal (const-class 'a) 'unknown))

(deftest "r4.2: независимость экспонент (Линдеман — Вейерштрасс)"
  (assert-equal (exp-independent? '(1 (^ 2 1/2))) #t)
  (assert-equal (exp-independent? '((^ 2 1/2) (^ 3 1/2) (^ 6 1/2))) #t)
  (assert-equal (exp-independent? '(1 (^ 2 1/2) (+ 1 (* 2 (^ 2 1/2))))) #f)
  (assert-equal (exp-independent? '(1 pi)) 'unknown))

(deftest "r4.2: const-rational-value — скрытое рациональное доказано, иррациональное — no"
  (assert-equal (const-rational-value '(/ (log 6) (+ (log 2) (log 3)))) 1)
  (assert-equal (const-rational-value '(* 3 (/ (log 4) (log 2)))) 6)
  (assert-equal (const-rational-value '(/ (log 3) (log 2))) 'no)
  (assert-equal (const-rational-value '(^ 2 1/2)) 'no)
  (assert-equal (const-rational-value 'a) 'unknown)
  (assert-equal (const-exp-simplify '(+ (log 2) (* 2 (log 3)))) 18))
