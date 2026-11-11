; RUBI.1: движок правил на игрушечном наборе (без загрузки 8.5 тыс. правил).
; RUBI.2b: параметр x не сливается с переменной, финальная проверка по исходным e и x,
; базовые sin/cos при линейном аргументе; проверка на настоящих правилах главы 1.1.1.
(define (rubi-test-setup rules)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #t)
  (for-each (lambda (r) (rubi::rubi-add-rule (car r) (cadr r) (nth r 2) (nth r 3)))
            (reverse rules))
  (rubi::rubi-build-index))

; Настоящие правила главы 1.1.1 (7 файлов, 208 правил): в тестовом хосте грузятся за десятки мс,
; stack overflow был от загрузки всех 8.5 тыс. правил сразу.
(define rubi-real-files
  '("1.1.1.1" "1.1.1.2" "1.1.1.3" "1.1.1.4" "1.1.1.5" "1.1.1.6" "1.1.1.7"))

(define (rubi-real-setup)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (for-each (lambda (f) (load (string-append lib-dir "rubi/rules/" f ".lisp"))) rubi-real-files)
  (set! rubi::*rubi-rules* (reverse rubi::*rubi-rules*))
  (rubi::rubi-build-index)
  (set! rubi::*rubi-loaded* #t))

(deftest "rubi: правило применяется и ответ проверяется"
  (rubi-test-setup (list (list "первое" '(/ 1 x) '() '(log (quote x)))))
  (assert-equal (rubi-integrate '(/ 1 x) 'x) '(log x)))

(deftest "rubi: непроверенная правая часть отвергается"
  (rubi-test-setup (list (list "подделка" '(/ 1 x) '() '(^ (quote x) 2))))
  (assert-equal (rubi-integrate '(/ 1 x) 'x) 'unknown))

(deftest "rubi: рекурсия правила останавливается стеком"
  ; аргумент вложенного Int — данные: без quote движок получил бы ошибку вычисления, а не цикл
  (rubi-test-setup
   (list (list "цикл" '(foo x) '()
               '(rubi::rubi-int (quote (foo x)) (quote (foo x)) (quote x)))))
  (assert-equal (rubi-integrate '(foo x) 'x) 'unknown))

; --- RUBI.2b: ложные ответы на параметрах (найдено при проверке RUBI.1) ---

(deftest "rubi/2b: параметр x не сливается с переменной — ∫x·y dy = x·y²/2"
  (rubi-real-setup)
  (let ((r (rubi-integrate '(* x y) 'y)))
    (assert-equal (simplify r) (simplify '(* 1/2 x (^ y 2))))
    ; прежний ложный ответ y³/3 не возвращается
    (assert-true (not (equal? (simplify r) (simplify '(* 1/3 (^ y 3))))))))

(deftest "rubi/2b: ∫1/(x+y) dy = log(x+y), а не log(y)/2"
  (rubi-real-setup)
  (let ((r (rubi-integrate '(/ 1 (+ x y)) 'y)))
    (assert-equal (simplify r) (simplify '(log (+ x y))))
    (assert-true (not (equal? (simplify r) (simplify '(* 1/2 (log y))))))))

(deftest "rubi/2b: (1+2x)^3 берётся правилом бинома, шаг Rubi 1.1.1 в журнале"
  (rubi-real-setup)
  (let* ((cap (capture-step-log (lambda () (rubi-integrate '(^ (+ 1 (* 2 x)) 3) 'x)) 'full 'ru))
         (txt (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-equal (simplify (car cap)) (simplify '(* 1/8 (^ (+ 1 (* 2 x)) 4))))
    (assert-true (string-contains? txt "Rubi 1.1.1.1 #4"))))

(deftest "rubi/2b: sin и cos линейного аргумента"
  (rubi-real-setup)
  (assert-equal (simplify (rubi-integrate '(sin x) 'x)) (simplify '(* -1 (cos x))))
  (assert-equal (simplify (rubi-integrate '(cos x) 'x)) (simplify '(sin x)))
  ; аргумент не линейный — честный отказ, а не ложный ответ
  (assert-equal (rubi-integrate '(sin (^ x 2)) 'x) 'unknown))

; --- RUBI.3: утилиты (семантика по IntegrationUtilityFunctions.m) ---

(deftest "rubi/3: предикаты FreeQ/EqQ/NeQ, числа, сравнения, структура"
  (assert-equal (rubi::rubi-freeq (list (quote a) (quote b)) (quote x)) #t)
  (assert-equal (rubi::rubi-freeq (quote x) (quote (^ x 2))) #f)
  (assert-equal (rubi::rubi-eqq (quote (+ 1 1)) 2) #t)
  (assert-equal (rubi::rubi-neq 1 2) #t)
  (assert-equal (rubi::rubi-integerq 3) #t)
  (assert-equal (rubi::rubi-integerq (quote x)) #f)
  (assert-equal (rubi::rubi-igtq 2 1) #t)
  (assert-equal (rubi::rubi-ltq 1 2 3) #t)
  (assert-equal (rubi::rubi-leq 1 1) #t)
  (assert-equal (rubi::rubi-posq 1/2) #t)
  (assert-equal (rubi::rubi-negq -1/2) #t)
  (assert-equal (rubi::rubi-rationalq 1/2) #t)
  (assert-equal (rubi::rubi-fractionq 1/2) #t)
  (assert-equal (rubi::rubi-sumq (quote (+ x 1))) #t)
  (assert-equal (rubi::rubi-productq (quote (* x 1))) #t)
  (assert-equal (rubi::rubi-powerq (quote (^ x 2))) #t))

(deftest "rubi/3: бином/квадрат/трином, степень, SimplerQ, LeafCount"
  (assert-true (rubi::rubi-binomial-q (quote (+ 1 (* 2 x))) (quote x)))
  (assert-true (rubi::rubi-quadratic-q (quote (+ 1 (* 2 (^ x 2)))) (quote x)))
  (assert-equal #f (rubi::rubi-trinomial-q (quote (+ 1 (* 2 x))) (quote x)))
  (assert-equal (rubi::rubi-safe-degree (quote (+ 1 (* 2 (^ x 2)))) (quote x)) 2)
  (assert-true (rubi::rubi-linear-match-q (quote (+ 3 (* 4 x))) (quote x)))
  (assert-true (rubi::rubi-simpler-q (quote x) (quote (* 2 x))))
  (assert-equal (rubi::rubi-leaf-count (quote (+ a b))) 3)
  (assert-equal (simplify (rubi::rubi-discriminant 1 2 3)) (simplify (quote (- (^ 2 2) (* 4 1 3))))))

(deftest "rubi/3: RemoveContent, Coefficient с нецелым показателем, MemberQ"
  (assert-equal (simplify (rubi::rubi-remove-content (quote (+ 4 (* 6 x))) (quote x)))
                (simplify (quote (+ 2 (* 3 x)))))
  (assert-equal (rubi::rubi-coefficient (quote (^ x 1/2)) (quote x) 1/2) 1)
  (assert-equal (rubi::rubi-coefficient (quote (^ x 1/2)) (quote x) 1) 0)
  (assert-equal (rubi::rubi-member-q (quote (a b)) (quote b)) #t)
  (assert-equal (rubi::rubi-independent-q (quote a) (quote x)) #t)
  (assert-equal (rubi::rubi-half-integer-q 3/2 1) #t))

; П3 карточки 3: три задачи корпуса дают ответ и журнал шагов с правилом Rubi
(deftest "rubi/3: три задачи t_1_1_1 с журналом шагов"
  (rubi-real-setup)
  (let* ((cap (capture-step-log (lambda () (rubi-integrate '(^ x -5/2) 'x)) 'full 'ru))
         (txt (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-equal (simplify (car cap)) (simplify '(* -2/3 (^ x -3/2))))
    (assert-true (string-contains? txt "Rubi 1.1.1")))
  (let* ((cap (capture-step-log (lambda () (rubi-integrate '(/ 1 (+ a (* b x))) 'x)) 'full 'ru))
         (txt (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-equal (simplify (car cap)) (simplify '(* (^ b -1) (log (+ a (* b x))))))
    (assert-true (string-contains? txt "Rubi 1.1.1")))
  (let* ((cap (capture-step-log (lambda () (rubi-integrate '(* (^ x 3) (^ (+ a (* b x)) 3)) 'x)) 'full 'ru))
         (rules (step-rules (cadr cap))))
    (assert-true (pair? (car cap)))
    (assert-true (>= (length rules) 3))))

; --- RUBI.4: ExpandIntegrand по первоисточнику ---

(deftest "rubi/4: ExpandLinearProduct раскладывает x² по (a+b*x)"
  (let ((s (rubi::rubi-expand-linear-product '(^ (+ a (* b x)) 2) '(^ x 2) 'a 'b 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (length (cdr s)) 3)))

(deftest "rubi/4: ExpandIntegrand x^4*(a+bx)^(-3/2) — сумма пяти степеней бинома"
  (let ((s (rubi::rubi-expand-integrand '(* (^ x 4) (^ (+ a (* b x)) -3/2)) 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (length (cdr s)) 5)))

(deftest "rubi/4: ∫x^4/(a+bx)^(3/2) берётся и проходит int-check"
  (rubi-real-setup)
  (let* ((e '(/ (^ x 4) (^ (+ a (* b x)) 3/2)))
         (r (rubi-integrate e 'x)))
    (assert-equal (not (equal? r 'unknown)) #t)
    (assert-true (int-check r e 'x))))

(deftest "rubi/4: ветвь 3584 — u*v^n при нецелом m делится на v^(-n)"
  ; x^3 * x^(-2) * (a+bx)^(-1/2) = x*(a+bx)^(-1/2): два слагаемых, x^(-2) не остаётся
  (let* ((e '(* (^ x 3) (^ x -2) (^ (+ a (* b x)) -1/2)))
         (s (rubi::rubi-expand-integrand e 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (length (cdr s)) 2)
    (assert-equal (length (filter (lambda (t) (and (pair? t) (equal? (car t) '^)
                                                   (equal? (cadr t) 'x) (equal? (caddr t) -2)))
                                  (cdr s)))
                  0)))

(deftest "rubi/4: ветвь 3553 — второй бином не теряется"
  (let* ((e '(* (^ (+ a (* b x)) -3/2) (^ (+ c (* d x)) 1/2)))
         (s (rubi::rubi-expand-integrand e 'x)))
    (assert-equal (rubi::rubi-leaf-count s) (rubi::rubi-leaf-count e))))

; --- RUBI.5: Apart/SmartApart (встроенный apart не раскладывает с символьными коэффициентами) ---

(deftest "rubi/5: Apart раскладывает 1/(x(a+bx)) с символьными коэффициентами"
  (let* ((u '(/ 1 (* x (+ a (* b x)))))
         (s (rubi::rubi-apart u 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (simplify (together (- s u))) 0)))

(deftest "rubi/5: SmartApart раскладывает 1/(x^4(a+bx)^3)"
  (let* ((u '(/ 1 (* (^ x 4) (^ (+ a (* b x)) 3))))
         (s (rubi::rubi-smart-apart u 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (length (cdr s)) 7)
    (assert-equal (simplify (together (- s u))) 0)))

(deftest "rubi/5: SmartApart на числовых коэффициентах совпадает с apart"
  (let* ((u '(/ (+ 5 x) (* (^ (- 1 (* 2 x)) 3) (^ (+ (* 3 x) 2) 4))))
         (s (rubi::rubi-smart-apart u 'x)))
    (assert-equal (simplify (together (- s u))) 0)))

; --- RUBI.6: отрицательные целые m — 1/(x^m(a+bx)^n) через ExpandIntegrand+Apar, ветви 3423/3428 ---

(deftest "rubi/6: ветвь 3423 раскрывает (a + b*x^(-2))^3"
  (let* ((e '(^ (+ a (* b (^ x -2))) 3))
         (s (rubi::rubi-expand-integrand e 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (simplify (expand (- s e))) 0)))

(deftest "rubi/6: ветвь 3428 раскрывает x^2*(a + b*x^(-2))^2"
  (let* ((e '(* (^ x 2) (^ (+ a (* b (^ x -2))) 2)))
         (s (rubi::rubi-expand-integrand e 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (simplify (expand (- s e))) 0)))

(deftest "rubi/6: ExpandIntegrand раскладывает 1/(x^4(a+bx)^3) в простейшие"
  (let* ((e '(/ 1 (* (^ x 4) (^ (+ a (* b x)) 3))))
         (s (rubi::rubi-expand-integrand e 'x)))
    (assert-equal (rubi::rubi-sumq s) #t)
    (assert-equal (length (cdr s)) 7)
    (assert-equal (simplify (together (- s e))) 0)))

(deftest "rubi/6: ∫1/(x^4(a+bx)^3) и ∫1/(x^2(a+bx)^2) берутся и проходят int-check"
  (rubi-real-setup)
  (for-each
   (lambda (e)
     (let ((r (rubi-integrate e 'x)))
       (assert-equal (not (equal? r 'unknown)) #t)
       (assert-true (int-check r e 'x))))
   (list '(/ 1 (* (^ x 4) (^ (+ a (* b x)) 3)))
         '(/ 1 (* (^ x 2) (^ (+ a (* b x)) 2))))))

(deftest "rubi/9: профиль фаз не меняет ответ и считает попытки"
  (rubi-real-setup)
  (let* ((e '(^ (+ (* b x) a) 2))
         (plain (rubi-integrate e 'x))
         (_ (rubi::rubi-prof-reset))
         (_on (set! rubi::*rubi-prof* #t))
         (profiled (rubi-integrate e 'x))
         (_off (set! rubi::*rubi-prof* #f)))
    (assert-equal profiled plain)
    (assert-true (> (cdr (assoc 'calls (rubi::rubi-prof-data))) 0))
    (assert-true (> (cdr (assoc 'matches (rubi::rubi-prof-data))) 0))
    (assert-true (> (cdr (assoc 'check-us (rubi::rubi-prof-data))) 0))))

(deftest "rubi/11: профиль матчера не меняет ответ и считает попытки"
  (rubi-real-setup)
  (let* ((e '(^ (+ (* b x) a) 2))
         (plain (rubi-integrate e 'x))
         (_ (match::ac-prof-reset))
         (_on (set! match::ac-prof #t))
         (profiled (rubi-integrate e 'x))
         (_off (set! match::ac-prof #f))
         (data (match::ac-prof-data)))
    (assert-equal profiled plain)
    (assert-true (> (cdr (assoc 'attempts data)) 0))
    (assert-true (> (cdr (assoc 'ticks data)) 0))))

(deftest "rubi/13: условие разбирается на конъюнкты, дешёвые отсеиваются"
  (assert-equal 3 (length (rubi::rubi-conjuncts '(and (and ?a ?b) ?c))))
  (assert-equal 1 (length (rubi::rubi-conjuncts '?a)))
  (assert-true (rubi::rubi-cheap-conjunct? '?a))
  ; размер больше 10 — не дешёвый
  (assert-equal #f (rubi::rubi-cheap-conjunct? '(f a b c d e f g h i j))))

(deftest "rubi/14: утилиты IntLinearQ/IntBinomialQ/IntQuadraticQ и спецфункции"
  ; IntLinearQ: целая положительная степень m даёт применимость
  (assert-equal #t (rubi::rubi-int-linear-q 'a 'b 'c 'd 2 1/2 'x))
  ; m+n = -1 и m рациональное — тоже применимо
  (assert-equal #t (rubi::rubi-int-linear-q 'a 'b 'c 'd -1/2 -1/2 'x))
  ; IntBinomialQ: n = 2, p и q полуцелые
  (assert-equal #t (rubi::rubi-int-binomial-q 'a 'b 'c 'd 2 1/2 -1/2 'x))
  ; n = 5 при тех же показателях — нет
  (assert-equal #f (rubi::rubi-int-binomial-q 'a 'b 'c 'd 5 1/2 -1/2 'x))
  ; IntQuadraticQ: целое p
  (assert-equal #t (rubi::rubi-int-quadratic-q 'a 'b 'c 'd 'e 1/2 3 'x))
  ; неподдержанная спецфункция — метка rubi-no-rule (RUBI.S8: без исключения; правая часть с меткой отвергается)
  (assert-equal '(hypergeometric-2f1 1 2 3 4) (rubi::rubi-hypergeometric2-f1 1 2 3 4))   ; RUBI.H1: функция CAS
  (assert-equal 'rubi-no-rule (rubi::rubi-appell-f1 1 2 3 4 5)))

(deftest "rubi/15: индекс по форме — счётчики и неизменность ответа"
  (rubi-real-setup)
  ; число x-зависимых множителей верхнего уровня
  (assert-equal 1 (rubi::rubi-expr-xfactors 'x 'x))
  (assert-equal 2 (rubi::rubi-expr-xfactors '(* x (^ (+ 1 x) 1/2)) 'x))
  (assert-equal 1 (rubi::rubi-expr-xfactors '(+ a (* b x)) 'x))
  ; сколько конкретных (не голых `?u`) множителей требует образец
  (assert-equal 1 (rubi::rubi-pat-min-factors '(* ?u (^ ?v ?m))))
  (assert-equal 1 (rubi::rubi-pat-min-factors '(* ?u (+ a (* b x)))))
  (assert-equal 2 (rubi::rubi-pat-min-factors '(* (+ a (* b x)) (^ (+ c (* d x)) ?m))))
  ; литеральный показатель образца, которого нет в выражении
  (assert-equal #f (rubi::rubi-exps-subset? '(1/3) '(2 3)))
  (assert-equal #t (rubi::rubi-exps-subset? '(2) '(2 3)))
  ; ответ с отсевом и без него совпадает
  (let* ((e '(/ 1 (* (^ x 2) (^ (+ (* b x) a) 2))))
         (on (begin (set! rubi::*rubi-shape-index* #t) (rubi-integrate e 'x)))
         (off (begin (set! rubi::*rubi-shape-index* #f) (rubi-integrate e 'x))))
    (set! rubi::*rubi-shape-index* #t)
    (assert-equal on off)))

(deftest "rubi/16: журнал причин отказа и мемоизация"
  (rubi-real-setup)
  ; отказ записывает причину
  (let ((r (rubi-integrate '(* x (exp x)) 'x)))
    (assert-equal 'unknown r)
    (assert-true (pair? (cdr (assoc 'fail-reasons (rubi::rubi-prof-data))))))
  ; мемоизация не меняет ответ на повторном вызове
  (let ((a (rubi-integrate '(^ x 3) 'x))
        (b (rubi-integrate '(^ x 3) 'x)))
    (assert-equal a b)))

(deftest "rubi/17: семантика первого правила — unknown вложенного Int окончателен"
  ; два правила на один образец: первое уходит в неподдержанную подзадачу (unknown),
  ; второе даёт верный ответ. По семантике Rubi первое правило окончательное.
  (let ((rules (list (list "первое" '(/ 1 x) '()
                           '(rubi::rubi-int (quote (foo x)) (quote (foo x)) (quote x)))
                     (list "второе" '(/ 1 x) '() '(log (quote x))))))
    (unwind-protect
     (begin
       (set! rubi::*rubi-first-rule-final* #t)
       (rubi-test-setup rules)
       (assert-equal (rubi-integrate '(/ 1 x) 'x) 'unknown)
       ; прежнее поведение — перебор следующего кандидата после unknown
       (set! rubi::*rubi-first-rule-final* #f)
       (rubi-test-setup rules)
       (assert-equal (rubi-integrate '(/ 1 x) 'x) '(log x)))
     (set! rubi::*rubi-first-rule-final* #t))))

(deftest "rubi/18: LinearPairQ, гистограмма заглушек и двухаргументный Simp"
  ; u/v постоянно: (2+4x)/(1+2x) = 2 — пара годна; (1+x)/(1+x^2) — нет
  (assert-equal (rubi::rubi-linear-pair-q '(+ 2 (* 4 x)) '(+ 1 (* 2 x)) 'x) #t)
  (assert-equal (rubi::rubi-linear-pair-q '(+ 1 x) '(+ 1 (^ x 2)) 'x) #f)
  ; u = x — не пара (по исходнику NeQ[u,x])
  (assert-equal (rubi::rubi-linear-pair-q 'x '(+ 1 (* 2 x)) 'x) #f)
  ; Simp: одно- и двухаргументная формы упрощают (RUBI.S7: с переменной — тоже simplify)
  (assert-equal (rubi::rubi-simp '(+ 1 2)) 3)
  (assert-equal (rubi::rubi-simp '(+ 1 2) 'x) 3)
  ; вызванная заглушка попадает в счётчик, а профиль её отдаёт
  (rubi-real-setup)
  (rubi-integrate '(/ 1 x) 'x)
  (let ((before (hash-ref rubi::*rubi-stub-calls* 'rubi-function-of-exponential-q 0)))
    (rubi::rubi-function-of-exponential-q 'x 'x)
    (assert-equal (hash-ref rubi::*rubi-stub-calls* 'rubi-function-of-exponential-q 0)
                  (+ before 1)))
  (let ((d (begin (rubi-integrate '(/ 1 x) 'x) (rubi::rubi-prof-data))))
    (assert-true (pair? (assoc 'tries d)))
    (assert-true (pair? (assoc 'stubs d)))
    (assert-true (pair? (assoc 'errors d)))))

(deftest "rubi/19: GeneralizedBinomialQ и GeneralizedTrinomialQ"
  ; a*x^q + b*x^n при n > q; коэффициенты — в том числе символьные
  (assert-equal (rubi::rubi-generalized-binomial-q '(+ (^ x 2) (^ x 5)) 'x) #t)
  (assert-equal (rubi::rubi-generalized-binomial-q '(+ 2 (* 3 (^ x 2))) 'x) #t)
  (assert-equal (rubi::rubi-generalized-binomial-q '(+ a (* b (^ x 3))) 'x) #t)
  (assert-equal (rubi::rubi-generalized-binomial-q '(+ 1 x (^ x 2)) 'x) #f)
  ; три члена с r = 2n - q (1 + x + x^2 и x^-1 + x + x^3), иначе нет
  (assert-equal (rubi::rubi-generalized-trinomial-q '(+ 1 x (^ x 2)) 'x) #t)
  (assert-equal (rubi::rubi-generalized-trinomial-q '(+ (^ x -1) x (^ x 3)) 'x) #t)
  (assert-equal (rubi::rubi-generalized-trinomial-q '(+ 1 x (^ x 3)) 'x) #f)
  ; член, зависящий от x не как моном, отсекает предикат
  (assert-equal (rubi::rubi-generalized-binomial-q '(+ 1 (* x (sin x))) 'x) #f))

(deftest "rubi/20: Rt, PseudoBinomialParts/PairQ, PiecewiseLinearQ"
  (rubi-real-setup)
  ; Rt извлекает точный корень, иначе оставляет простой вид (2*sqrt(3))
  (assert-equal (rubi::rubi-rt 8 3) 2)
  (assert-equal (rubi::rubi-rt 1/4 2) 1/2)
  (assert-equal (simplify (rubi::rubi-rt '(* 8 (^ x 6)) 3)) (simplify '(* 2 (^ x 2))))
  ; псевдобином a + (c+d*x)^n; чистая степень (a = 0) — не псевдобином
  (assert-equal (rubi::rubi-pseudo-binomial-parts '(+ 1 (^ (+ 1 x) 3)) 'x) '(1 1 1 1 3))
  (assert-equal (rubi::rubi-pseudo-binomial-parts '(^ (+ 1 x) 3) 'x) #f)
  (assert-equal (rubi::rubi-pseudo-binomial-pair-q '(+ 1 (^ (+ 1 x) 3)) '(+ 5 (^ (+ 1 x) 3)) 'x) #t)
  (assert-equal (rubi::rubi-pseudo-binomial-pair-q '(+ 1 (^ (+ 1 x) 3)) '(+ 5 (^ (+ 2 x) 3)) 'x) #f)
  ; PiecewiseLinearQ: линейность, Log[c*F^(линейное)], пара F[G[линейное]] из таблицы
  (assert-equal (rubi::rubi-piecewise-linear-q '(+ a (* b x)) 'x) #t)
  (assert-equal (rubi::rubi-piecewise-linear-q '(log (^ 2 x)) 'x) #t)
  (assert-equal (rubi::rubi-piecewise-linear-q '(atan (tan x)) 'x) #t)
  (assert-equal (rubi::rubi-piecewise-linear-q '(^ x 2) 'x) #f)
  (assert-equal (rubi::rubi-piecewise-linear-q 'x '(+ 1 x) 'x) #t))

; --- RUBI.S1: unknown внутри ответа, индекс по форме, лимит времени условия ---

(deftest "rubi/S1: unknown вложенного Int внутри суммы — отказ, а не ответ"
  ; d/dx (log x + unknown) = 1/x: int-check считал метку константой и пропускал такой «ответ»
  (let ((forged (list (list "подделка" '(/ 1 x) '()
                            '(+ (log (quote x))
                                (rubi::rubi-int (quote (foo x)) (quote (foo x)) (quote x)))))))
    (rubi-test-setup forged)
    (assert-true (rubi::rubi-tainted? '(+ (log x) unknown)))
    (assert-true (rubi::rubi-tainted? '(* 2 (+ 1 (unintegrable))))) 
    (assert-equal #f (rubi::rubi-tainted? '(+ (log x) (* 2 x))))
    (assert-equal (rubi-integrate '(/ 1 x) 'x) 'unknown)
    ; метка в произведении (2·unknown) — тоже отказ
    (rubi-test-setup (list (list "произведение" (quote (/ 1 x)) (quote ())
                                 (quote (+ (log (quote x)) (* 2 (rubi::rubi-int (quote (foo x)) (quote (foo x)) (quote x))))))))
    (assert-equal (rubi-integrate (quote (/ 1 x)) (quote x)) (quote unknown))))

(deftest "rubi/S1: integrate_rubi при отказе возвращает невычисленный integrate (status unknown)"
  (rubi-test-setup (list (list "первое" '(/ 1 x) '() '(log (quote x)))))
  (assert-equal (rubi-integrate-form '(/ 1 x) 'x) '(log x))
  (assert-equal (rubi-integrate-form '(foo x) 'x) '(integrate (foo x) x))
  (assert-equal (math-eval "integrate_rubi(foo(x), x)") '(integrate (foo x) x)))

(define rubi-shape-probes
  '((* (^ (+ 1 x) 1/2) (^ (+ 2 x) -2))
    (* x (^ (+ 1 x) 1/3) (^ (+ 2 x) 3/2))
    (^ (+ 1 (* 2 x)) 3)
    (* x (^ (+ a (* b x)) 9/4))
    (/ 1 (* (^ x 2) (^ (+ a (* b x)) 2)))
    (* (^ (+ a (* b x)) 7/6) (^ (+ c (* d x)) 1/6))
    (^ x -5/2)
    (* (^ x 3) (^ (+ a (* b x)) -3/2))
    (* (+ 1 x) (^ (+ 3 (* 5 x)) -1) (^ (+ 2 (* 3 x)) -4))
    (* (^ (+ 1 (* -2 x)) 1/2) (^ (+ 3 (* 5 x)) -3/2) (^ (+ 2 (* 3 x)) -7/2))
    (^ (+ 1 x (^ x 2)) 3/2)
    (* (^ (+ c (* d x)) 1/2) (+ e (* f x)) (^ x -1))
    (^ (+ 1 (^ x 3)) 1/3)))

(deftest "rubi/S1: индекс по форме не теряет подошедших правил (13 проб)"
  ; правила, отсечённые индексом, хотя прошли отбор по головам, не должны структурно подходить к выражению
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (for-each (lambda (f) (load (string-append lib-dir "rubi/rules/" f ".lisp")))
            (append rubi-real-files '("1.4.1" "1.4.2" "1.1.3.1")))
  (set! rubi::*rubi-rules* (reverse rubi::*rubi-rules*))
  (rubi::rubi-build-index)
  (set! rubi::*rubi-loaded* #t)
  (let ((rejected 0))
    (for-each
     (lambda (e)
       (assert-equal '() (map (lambda (r) (nth r 1)) (rubi::rubi-shape-lost e 'x)))
       (let* ((ne (ac-strip-units (ac-norm (if (rubi::rubi-sqrt-head? e) (rubi::rubi-normalize-heads e) e))))
              (xc (rubi::rubi-expr-xfactors ne 'x))
              (exps (rubi::rubi-expr-exponents ne '())))
         (set! rejected
               (+ rejected
                  (length (filter (lambda (r) (not (rubi::rubi-shape-ok? r xc exps)))
                                  rubi::*rubi-rules*))))))
     rubi-shape-probes)
    ; индекс действительно что-то отсекает (проба не пустая)
    (assert-true (> rejected 0))))

(deftest "rubi/S1: условие правила, превысившее лимит времени, считается ложью"
  (let ((old rubi::*rubi-cond-limit*))
    (unwind-protect
     (begin
       (set! rubi::*rubi-cond-limit* 0.02)
       (assert-equal #t (rubi::rubi-cond-check "r" (lambda (b) #t) '()))
       (assert-equal #f (rubi::rubi-cond-check "r" (lambda (b) #f) '()))
       (let ((n rubi::*rubi-cond-timeouts*))
         (assert-equal #f (rubi::rubi-cond-check "r" (lambda (b) (let l () (l))) '()))
         (assert-equal (+ n 1) rubi::*rubi-cond-timeouts*))
       ; ошибка условия = условие ложно (RUBI.S6), счётчик ошибок растёт
       (let ((n rubi::*rubi-cond-errors*))
         (assert-equal #f (rubi::rubi-cond-check "r" (lambda (b) (error "boom")) '()))
         (assert-equal (+ n 1) rubi::*rubi-cond-errors*)))
     (set! rubi::*rubi-cond-limit* old))))

(deftest "rubi/S3: двухступенчатая загрузка — глава 1 и признак алгебраического входа"
  (assert-equal #t (rubi::rubi-stage1-file? "1.1.1.1"))
  (assert-equal #f (rubi::rubi-stage1-file? "4.1.0.1"))
  (assert-equal #f (rubi::rubi-stage1-file? "9.2-2"))
  (assert-equal #t (rubi::rubi-algebraic? (quote (* x (^ (+ a (* b x)) 1/2)))))
  (assert-equal #t (rubi::rubi-algebraic? (quote (/ 1 (sqrt (+ 1 x))))))
  (assert-equal #f (rubi::rubi-algebraic? (quote (* x (exp x)))))
  (assert-equal #f (rubi::rubi-algebraic? (quote (sin (^ x 2)))))
  ; правила заданы вручную (stage 0): ensure-full ничего не грузит
  (rubi-test-setup (list (list "первое" (quote (/ 1 x)) (quote ()) (quote (log (quote x))))))
  (assert-equal #t (rubi::rubi-ensure-full))
  (assert-equal (rubi-integrate (quote (/ 1 x)) (quote x)) (quote (log x))))

(deftest "rubi/S4: FreeQ видит x внутри составных элементов; ∫x/(d+e1*x)^21 верно"
  (assert-equal #f (rubi::rubi-freeq (list 0 (quote (^ (+ d (* e1 x)) -21)) 1) (quote x)))
  (assert-equal #t (rubi::rubi-freeq (list (quote a) (quote (+ b c)) 1) (quote x)))
  (assert-equal #f (rubi::rubi-freeq (quote (+ 1 (* 2 x))) (quote x)))
  (assert-equal #t (rubi::rubi-freeq (quote (+ 1 (* 2 y))) (quote x)))
  (assert-equal #f (rubi::rubi-freeq (quote (* y z)) (list (quote x) (quote y))))
  (rubi-real-setup)
  (let ((r (rubi-integrate (quote (* x (^ (+ d (* e1 x)) -21))) (quote x))))
    (assert-true (not (equal? r (quote unknown))))
    ; прежний ложный ответ x^2/(2(d+e1*x)^21) не возвращается
    (assert-true (not (equal? (simplify r) (simplify (quote (* 1/2 (^ x 2) (^ (+ d (* e1 x)) -21)))))))
    (assert-true (int-check r (quote (* x (^ (+ d (* e1 x)) -21))) (quote x)))))

(deftest "rubi/S5: ветвь If[...] правой части без результата — правило не сработало, перебор идёт дальше"
  (rubi-test-setup (list (list "условное" (quote (/ 1 x)) (quote ())
                               (quote (if (rubi::rubi-eqq 1 2) (log (quote x)) (quote unknown))))
                         (list "второе" (quote (/ 1 x)) (quote ()) (quote (log (quote x))))))
  ; RUBI.S8: файлы правил уже содержат rubi-no-rule, переписывание — rubi-fix-names, для ручных правил
  (assert-equal (rubi::rubi-fix-names (quote (if c (quote unknown)))) (quote (if c (quote rubi-no-rule))))
  (rubi-test-setup (list (list "условное" (quote (/ 1 x)) (quote ())
                               (quote (if (rubi::rubi-eqq 1 2) (log (quote x)) (quote rubi-no-rule))))
                         (list "второе" (quote (/ 1 x)) (quote ()) (quote (log (quote x))))))
  (assert-equal (rubi-integrate (quote (/ 1 x)) (quote x)) (quote (log x)))
  (assert-true (rubi::rubi-tainted? (quote (* 2 rubi-no-rule)))))

(deftest "rubi/S6: PolyQ с степенью, IntegersQ с несколькими аргументами, LinearQ с символьными коэффициентами без ошибок"
  (assert-equal #t (rubi::rubi-poly-q (quote (+ 1 (* 2 x) (^ x 2))) (quote x) 2))
  (assert-equal #f (rubi::rubi-poly-q (quote (+ 1 (* 2 x) (^ x 2))) (quote x) 3))
  (assert-equal #t (rubi::rubi-poly-q (quote (+ 1 x)) (quote x)))
  (assert-equal #t (rubi::rubi-integers-q 1 2 3))
  (assert-equal #f (rubi::rubi-integers-q 1 1/2))
  (assert-equal #t (rubi::rubi-integers-q (list 2 4)))
  (assert-equal #t (rubi::rubi-linearq (quote (+ 1 (* (^ a -1) b x))) (quote x)))
  (assert-equal #f (rubi::rubi-linearq (quote (+ 1 (* (^ a -1) b (^ x 2)))) (quote x))))

(deftest "rubi/S7: (u^p)^q, пары u/-u, (b*x^n)^p, пропуск переменной при :identities"
  (assert-equal (rubi::rubi-collapse-pow (quote (^ (^ (+ a x) 1/2) -1))) (quote (^ (+ a x) -1/2)))
  ; нецелое q: (u^2)^(1/2) не сворачивается
  (assert-equal (rubi::rubi-collapse-pow (quote (^ (^ u 2) 1/2))) (quote (^ (^ u 2) 1/2)))
  (assert-equal (rubi::rubi-pair-neg-bases (quote (* x (^ (+ a (* b x)) 1/2) (^ (+ (* -1 a) (* -1 b x)) -1/2))) (quote x))
                (quote (* x (^ (+ a (* b x)) 1/2) (^ (* -1 (+ a (* b x))) -1/2))))
  ; без пары — выражение не меняется
  (assert-equal (rubi::rubi-pair-neg-bases (quote (* x (^ (+ a (* b x)) 1/2) (^ (+ c (* d x)) -1/2))) (quote x))
                (quote (* x (^ (+ a (* b x)) 1/2) (^ (+ c (* d x)) -1/2))))
  ; по умолчанию ac-match не находит (a=1, v=u); с флагом — находит; результаты по умолчанию не менялись
  (let ((pat (quote (* (^ (* ?a ?v) ?m) (^ (* ?b ?v) ?n))))
        (e (quote (* (^ (+ a x) 1/2) (^ (* -1 (+ a x)) -1/2)))))
    (assert-equal 0 (length (ac-match-all pat e 100000 :identities #t)))
    (set! match::ac-id-skip #t)
    (assert-true (> (length (ac-match-all pat e 100000 :identities #t)) 0))
    (set! match::ac-id-skip #f)
    (assert-equal 0 (length (ac-match-all pat e 100000 :identities #t)))
    ; без :identities флаг ничего не меняет
    (set! match::ac-id-skip #t)
    (assert-equal (ac-match-all (quote (+ ?a ?b)) (quote (+ x y)))  (begin (set! match::ac-id-skip #f) (ac-match-all (quote (+ ?a ?b)) (quote (+ x y))))))
  (assert-equal #f match::ac-id-skip)
  (set! rubi::*rubi-rules* (quote ()))
  (set! rubi::*rubi-ord* 0)
  (for-each (lambda (f) (load (string-append lib-dir "rubi/rules/" f ".lisp")))
            (append rubi-real-files (quote ("1.4.1" "1.4.2"))))
  (set! rubi::*rubi-rules* (reverse rubi::*rubi-rules*))
  (rubi::rubi-build-index)
  (set! rubi::*rubi-loaded* #t)
  ; sqrt(a+bx)/sqrt(-a-bx) и sqrt(c*x^2)
  (let ((r (rubi-integrate (quote (* x (sqrt (+ a (* b x))) (^ (sqrt (+ (* -1 a) (* -1 b x))) -1))) (quote x))))
    (assert-true (not (equal? r (quote unknown)))))
  (let* ((f (quote (* x (sqrt (* c (^ x 2))) (^ (+ a (* b x)) -1))))
         (r (rubi-integrate f (quote x))))
    (assert-true (not (equal? r (quote unknown))))
    (assert-true (int-check r f (quote x)))))

(deftest "rubi/S8: деление многочленов без броска, множество голов, файлы правил с готовыми именами"
  ; коэффициент c^-1 — для poly-* не многочлен; RUBI.C1: деление своим длинным делением (раньше запасное значение
  ; quotient = 1, remainder = 0 - «делится»: 1.1.1.5 #3 зацикливалось), без исключения
  (assert-equal 0 (rubi::rubi-polynomial-quotient 1 (quote (+ 1 (* (^ c -1) d x))) (quote x)))
  (assert-equal 1 (rubi::rubi-polynomial-remainder 1 (quote (+ 1 (* (^ c -1) d x))) (quote x)))
  (assert-equal 1 (rubi::rubi-poly-gcd 1 (quote (+ 1 (* (^ c -1) d x))) (quote x)))
  (assert-equal #f (rubi::rubi-poly-qr 1 (quote (+ 1 (* (^ c -1) d x))) (quote x)))
  ; обычные многочлены считаются как раньше
  (assert-equal (quote (+ -1 x)) (rubi::rubi-polynomial-quotient (quote (+ (* x x) -1)) (quote (+ x 1)) (quote x)))
  (assert-equal (quote (+ 1 x)) (rubi::rubi-poly-gcd (quote (+ (* x x) -1)) (quote (+ x 1)) (quote x)))
  (let ((hs (rubi::rubi-head-set (quote (+ ^ log)))))
    (assert-equal #t (rubi::rubi-prefilter-set? (quote (log ^)) hs))
    (assert-equal #f (rubi::rubi-prefilter-set? (quote (log sin)) hs))
    (assert-equal #t (rubi::rubi-prefilter-set? (quote ()) hs)))
  ; IntBinomialQ: 7 аргументов (1.1.3.2) — IGtQ[p,0]; 10 аргументов (1.1.3.4) — IntegersQ[p,q]; прочая арность — #f
  (assert-equal #t (rubi::rubi-int-binomial-q 'a 'b 'c 2 1/2 3 'x))
  (assert-equal #f (rubi::rubi-int-binomial-q 'a 'b 'c 3 1/2 1/3 'x))
  (assert-equal #t (rubi::rubi-int-binomial-q 'a 'b 'c 'd 'e 'm 2 1 3 'x))
  (assert-equal #f (rubi::rubi-int-binomial-q 'a 'b 'c 'd 'e 'm 2 1/3 1/3 'x))
  (assert-equal #f (rubi::rubi-int-binomial-q 1 2 3 4 5 6 7 8 9))
  (assert-equal (quote (appell-f1 1 2 3 4 5 6)) (rubi::rubi-appell-f1 1 2 3 4 5 6))   ; RUBI.H1
  (assert-equal (quote rubi-no-rule) (rubi::rubi-hypergeometric2-f1 1 2 3))   ; иная арность — отказ
  ; локальная переменная With/Module в условии If правой части — значение (правило 1.1.3.7 #40: q = Expon[Pq,x])
  (let ((has-form? (lambda (f e)
                     (let walk ((e e))
                       (cond ((equal? e f) #t)
                             ((pair? e) (or (walk (car e)) (walk (cdr e))))
                             (else #f))))))
    (set! rubi::*rubi-rules* (quote ()))
    (set! rubi::*rubi-ord* 0)
    (load (string-append lib-dir "rubi/rules/1.1.3.7.lisp"))
    (let ((r (car (filter (lambda (r) (equal? (nth r 1) "Rubi 1.1.3.7 #40")) rubi::*rubi-rules*))))
      (assert-equal #f (has-form? (quote (quote q)) (nth r 4)))
      (assert-equal #t (has-form? (quote (rubi::rubi-expon Pq (quote x))) (nth r 4)))))
  (assert-equal #t (rubi::rubi-expensive-head? (quote rubi-polynomial-quotient)))
  (assert-equal #f (rubi::rubi-expensive-head? (quote rubi-freeq)))
  (assert-equal #t (rubi::rubi-form-expensive? (quote (and (rubi-eqq 1 (poly-q (+ 1 x))) (a))))))

(deftest "rubi/S12: SumSimplerQ[u,v], IntPart/FracPart по Rubi"
  ; рациональные u, v: v = 0 - нет, v > 0 - u < -1, v < 0 - u >= -1 (правила 1.1.1.2 #19: SumSimplerQ[m,1])
  (assert-equal #f (rubi::rubi-sum-simpler-q 2 0))
  (assert-equal #t (rubi::rubi-sum-simpler-q -3/2 1))
  (assert-equal #f (rubi::rubi-sum-simpler-q -1/2 1))
  (assert-equal #f (rubi::rubi-sum-simpler-q -1/2 -1))
  (assert-equal #t (rubi::rubi-sum-simpler-q 2 -1))
  (assert-equal #f (rubi::rubi-sum-simpler-q -3 -1))
  ; символьные: m - ничего не сокращается; k - 2 + 1 - рациональные слагаемые -2 и 1 сокращаются
  (assert-equal #f (rubi::rubi-sum-simpler-q (quote m) 1))
  (assert-equal #t (rubi::rubi-sum-simpler-q (quote (+ k -2)) 1))
  (assert-equal #f (rubi::rubi-sum-simpler-q (quote (+ k 1)) 1))
  ; IntPart/FracPart: усечение к нулю (Mathematica IntegerPart/FractionalPart), не floor
  (assert-equal -1 (rubi::rubi-int-part -3/2))
  (assert-equal -1/2 (rubi::rubi-frac-part -3/2))
  (assert-equal 3 (rubi::rubi-int-part 7/2))
  (assert-equal 1/2 (rubi::rubi-frac-part 7/2))
  (assert-equal 4 (rubi::rubi-int-part 4))
  (assert-equal 0 (rubi::rubi-frac-part 4))
  ; символьное: IntPart = 0, FracPart = u; сумма - по слагаемым
  (assert-equal 0 (rubi::rubi-int-part (quote x)))
  (assert-equal (quote x) (rubi::rubi-frac-part (quote x)))
  (assert-equal 3 (rubi::rubi-int-part (quote (+ x 7/2))))
  (assert-equal (quote (+ 1/2 x)) (rubi::rubi-frac-part (quote (+ x 7/2)))))

(deftest "rubi/S15: SumSimplerQ/SimplerQ по исходнику Rubi (IUF.m 681, 774-796), NumericFactor, IntPart с n"
  (assert-equal #t (rubi::rubi-sum-simpler-q (quote (+ -1 m)) 1))
  (assert-equal #t (rubi::rubi-sum-simpler-q (quote (+ 1 m)) -1))
  (assert-equal #f (rubi::rubi-sum-simpler-q (quote m) 1))
  (assert-equal #t (rubi::rubi-sum-simpler-q -3 1))
  (assert-equal #f (rubi::rubi-sum-simpler-q -1 1))
  (assert-equal #t (rubi::rubi-sum-simpler-q (quote (+ n (* 2 m))) (quote (* -1 m))))
  (assert-equal #f (rubi::rubi-sum-simpler-q (quote (+ 1 m)) -2))
  (assert-equal #t (rubi::rubi-sum-simpler-q (quote (+ -1/2 m)) 1))
  (assert-equal #t (rubi::rubi-simpler-q 0 -1))
  (assert-equal #f (rubi::rubi-simpler-q 1/2 2))
  (assert-equal #t (rubi::rubi-simpler-q 2 1/2))
  (assert-equal #t (rubi::rubi-simpler-q 1 -1))
  (assert-equal #f (rubi::rubi-simpler-q -1 1))
  (assert-equal #t (rubi::rubi-simpler-q 1/2 1/3))
  (assert-equal #t (rubi::rubi-simpler-q (quote x) (quote (^ x 2))))
  (assert-equal #f (rubi::rubi-simpler-q (quote (^ x 2)) (quote x)))
  (assert-equal 2 (rubi::rubi-numeric-factor (quote (+ (* 2 m) (* 4 n)))))
  (assert-equal -2 (rubi::rubi-numeric-factor (quote (+ (* -2 m) (* -4 n)))))
  (assert-equal (quote (+ m (* 2 n))) (rubi::rubi-nonnumeric-factors (quote (+ (* 2 m) (* 4 n)))))
  (assert-equal (quote (* 2 x)) (rubi::rubi-frac-part (quote (* 2 (+ 1/2 x)))))
  ; группировка x-свободных множителей слагаемого: ?b в (* ?b x) берёт все
  (assert-equal (quote (+ (* (* -1 r) x) (^ r 2) (^ x 2))) (rubi::rubi-group-free (quote (+ (* -1 r x) (^ r 2) (^ x 2))) (quote x))))

(deftest "rubi/S12: PosQ/NegQ (PosAux), BinomialQ/TrinomialQ/MonomialQ по структуре, EqQ/NeQ с одним аргументом"
  ; PosQ/NegQ: число по знаку, символ положителен, произведение - по знаку множителей, сумма - по первому члену
  (assert-equal #t (rubi::rubi-posq (quote x)))
  (assert-equal #f (rubi::rubi-negq (quote x)))
  (assert-equal #t (rubi::rubi-negq (quote (* -1 b))))
  (assert-equal #f (rubi::rubi-posq (quote (* -1 b))))
  (assert-equal #t (rubi::rubi-posq (quote (* -2 a (* -1 b)))))
  (assert-equal #t (rubi::rubi-negq (quote (+ -1 x))))
  (assert-equal #t (rubi::rubi-negq (quote (^ (* -1 b) 3))))
  (assert-equal #t (rubi::rubi-posq (quote (^ (* -1 b) 2))))
  (assert-equal #t (rubi::rubi-posq 3/2))
  (assert-equal #t (rubi::rubi-negq -2))
  (assert-equal #f (rubi::rubi-negq 0))
  (assert-equal #f (rubi::rubi-posq 0))
  ; BinomialQ: a + b x^n или b x^n, n != 0
  (assert-equal #t (rubi::rubi-binomial-q (quote (+ a (* b (^ x n)))) (quote x)))
  (assert-equal #t (rubi::rubi-binomial-q (quote (+ 1 (* 2 x))) (quote x)))
  (assert-equal #t (rubi::rubi-binomial-q (quote (* 3 (^ x 5))) (quote x)))
  (assert-equal #f (rubi::rubi-binomial-q (quote (+ 1 x (^ x 2))) (quote x)))
  (assert-equal #f (rubi::rubi-binomial-q (quote (^ (+ 1 x) 2)) (quote x)))
  (assert-equal #f (rubi::rubi-binomial-q 5 (quote x)))
  ; свободный множитель при двучлене (BinomialParts, ProductQ): правило 3015 пилота
  (assert-equal #t (rubi::rubi-binomial-q (quote (* c (+ a (* -1 b x)))) (quote x)))
  (assert-equal 7/2 (rubi::rubi-binomial-degree (quote (+ a (* b (^ x 7/2)))) (quote x)))
  ; TrinomialQ: a + b x^n + c x^(2n)
  (assert-equal #t (rubi::rubi-trinomial-q (quote (+ a (* b (^ x 3)) (* c (^ x 6)))) (quote x)))
  ; квадратный трёхчлен TrinomialQ не считает (IUF.m:571, Not[QuadraticQ], RUBI.S16)
  (assert-equal #f (rubi::rubi-trinomial-q (quote (+ a (* b x) (* c (^ x 2)))) (quote x)))
  (assert-equal #t (rubi::rubi-trinomial-q (quote (+ a (* b (^ x n)) (* c (^ x (* 2 n))))) (quote x)))
  (assert-equal #f (rubi::rubi-trinomial-q (quote (+ a (* b x) (* c (^ x 3)))) (quote x)))
  ; MonomialQ: c x^n
  (assert-equal #t (rubi::rubi-monomial-q (quote (* c (^ x n))) (quote x)))
  (assert-equal #t (rubi::rubi-monomial-q (quote x) (quote x)))
  (assert-equal #f (rubi::rubi-monomial-q (quote (+ 1 x)) (quote x)))
  (assert-equal #f (rubi::rubi-monomial-q 4 (quote x)))
  ; EqQ[u], NeQ[u] - сравнение с нулём
  (assert-equal #t (rubi::rubi-eqq 0))
  (assert-equal #t (rubi::rubi-eqq (quote (+ a (* -1 a)))))
  (assert-equal #t (rubi::rubi-neq (quote (+ a 1))))
  (assert-equal #f (rubi::rubi-neq 0))
  (assert-equal #t (rubi::rubi-eqq (quote a) (quote a))))

(deftest "rubi/S12: Sum, MatchQ с условием, Sign, Mod/GCD/Quotient на рациональных, SimplerSqrtQ и прочие утилиты"
  ; Sum[f, {k, lo, hi}]: макрос, k связан в теле (правило 1.1.2.8: Sum[Binomial[n,2k] c^(n-2k) d^(2k) x^(2k), {k,0,n/2}])
  (assert-equal (quote (+ 1 (* 6 (^ x 2)) (^ x 4)))
                (eval (quote (rubi::rubi-sum (* (binomial 4 (* 2 k)) (^ (quote x) (* 2 k))) (list k 0 (/ 4 2))))))
  (assert-equal (quote (+ 0 1)) (eval (quote (rubi::rubi-sum k (list k 0 (/ 3 2))))))
  (assert-equal 0 (eval (quote (rubi::rubi-sum k (list k 1 0)))))
  ; MatchQ[e, x^m_. u_. /; IntegerQ[m]] (правила 1.1.2.x #2, 1.2.2.5, 1.2.3.5)
  (assert-equal #t (eval (quote (rubi::rubi-matchq (quote (* (^ x 2) (+ a 1))) (condition (* (^ (quote x) ?m) ?u) (rubi::rubi-integerq ?m))))))
  (assert-equal #f (eval (quote (rubi::rubi-matchq (quote (* (^ x 1/2) (+ a 1))) (condition (* (^ (quote x) ?m) ?u) (rubi::rubi-integerq ?m))))))
  (assert-equal #f (eval (quote (rubi::rubi-matchq (quote (+ a 1)) (condition (* (^ (quote x) ?m) ?u) (rubi::rubi-integerq ?m))))))
  (assert-equal #f (eval (quote (rubi::rubi-matchq 5 (condition (* (^ (quote x) ?m) ?u) (rubi::rubi-integerq ?m))))))
  ; Sign, Mod, GCD, Quotient на рациональных (1.1.4.4, 1.2.3.4, 1.1.3.x)
  (assert-equal -1 (rubi::rubi-sign -5))
  (assert-equal 1 (rubi::rubi-sign 3/2))
  (assert-equal 0 (rubi::rubi-sign 0))
  (assert-equal 1/2 (rubi::rubi-mod 3/2 1))
  (assert-equal 1/2 (rubi::rubi-mod -3/2 1))
  (assert-equal 2 (rubi::rubi-mod 8 3))
  (assert-equal 1/2 (rubi::rubi-gcd 3/2 1))
  (assert-equal 6 (rubi::rubi-gcd 12 18))
  (assert-equal 3 (rubi::rubi-quotient 7/2 1))
  (assert-equal 2 (rubi::rubi-quotient 7 3))
  ; SimplerSqrtQ с двумя аргументами (1.1.2.3-1.1.2.5)
  ; по IUF.m:736 (RUBI.S16): LtQ[v,0] && Not[LtQ[u,0]] -> True; Sqrt[2], Sqrt[3] - одинаковый LeafCount -> False
  (assert-equal #f (rubi::rubi-simpler-sqrt-q 2 3))
  (assert-equal #t (rubi::rubi-simpler-sqrt-q 4 9))
  (assert-equal #f (rubi::rubi-simpler-sqrt-q -2 3))
  (assert-equal #t (rubi::rubi-simpler-sqrt-q 3 -2))
  ; Distrib, MinimumMonomialExponent, QuadraticProductQ (1.3.1, 1.3.2), Root - отказ без исключения
  (assert-equal (quote (+ (* a x) (* a 1))) (rubi::rubi-distrib (quote a) (quote (+ x 1))))
  (assert-equal 2 (rubi::rubi-minimum-monomial-exponent (quote (+ (* 3 (^ x 2)) (^ x 3))) (quote x)))
  (assert-equal #t (rubi::rubi-quadratic-product-q (quote (* (+ 1 (^ x 2)) (+ 2 x (^ x 2)))) (quote x)))
  (assert-equal #f (rubi::rubi-quadratic-product-q (quote (* (+ 1 x) (+ 2 x (^ x 2)))) (quote x)))
  (assert-equal (quote rubi-no-rule) (rubi::rubi-root 1 2)))

(deftest "rubi/S16: Rt/RtAux, PolyQ[u, x^v], Expon/Coeff, Match-предикаты, GtQ по значению константы, RemoveContent (по IUF.m)"
  ; Rt[u,n] = RtAux[TogetherSimplify[u],n] (IUF.m:7514-7604)
  (assert-equal (quote b) (rubi::rubi-rt (quote (^ b 2)) 2))
  (assert-equal (quote (^ (* -1 (^ b 2)) 1/2)) (rubi::rubi-rt (quote (* -1 (^ b 2))) 2))
  (assert-equal -2 (rubi::rubi-rt -8 3))
  (assert-equal (quote (* 2 (^ (+ a (* b x)) 1/2))) (rubi::rubi-rt (quote (* 4 (+ a (* b x)))) 2))
  (assert-equal (quote (^ (+ a (* b x)) 1/2)) (rubi::rubi-rt (quote (+ a (* b x))) 2))
  ; SplitProduct[SumBaseQ, u]: {множитель-сумма, остаток}; без такого множителя - ложь (в правилах 1.1.3.1/1.1.3.2)
  (assert-equal (quote ((+ b x) a)) (rubi::rubi-split-product (quote SumBaseQ) (quote (* a (+ b x)))))
  (assert-equal #f (rubi::rubi-split-product (quote SumBaseQ) (quote (* a b))))
  ; SimplerSqrtQ по Rt и LeafCount
  (assert-equal #f (rubi::rubi-simpler-sqrt-q (quote a) (quote b)))
  ; PolyQ[u, x^v] (IUF.m:512-533): раньше (^ x v) считался символом и многочленом объявлялось всё
  (assert-equal #t (rubi::rubi-poly-q (quote (+ 1 (* 2 (^ x 4)) (^ x 8))) (quote (^ x 4))))
  (assert-equal #f (rubi::rubi-poly-q (quote (+ 1 (* 2 (^ x 3)))) (quote (^ x 2))))
  (assert-equal #t (rubi::rubi-poly-q (quote (+ 1 (* 2 (^ x 4)) (^ x 8))) (quote (^ x 4)) 2))
  (assert-equal #f (rubi::rubi-poly-q (quote (+ 1 (* 2 (^ x 4)) (^ x 8))) (quote (^ x 4)) 3))
  (assert-equal #t (rubi::rubi-poly-q (quote (+ 1 (* 2 (^ x (* 2 n))) (^ x (* 4 n)))) (quote (^ x (* 2 n))) 2))
  (assert-equal 2 (rubi::rubi-expon (quote (+ 1 (* 2 (^ x 4)) (^ x 8))) (quote (^ x 4))))
  (assert-equal 2 (rubi::rubi-coeff (quote (+ 1 (* 2 (^ x 4)) (^ x 8))) (quote (^ x 4)) 1))
  ; Expon с Together для дроби, сокращающейся до многочлена (IUF.m:1239)
  (assert-equal 1 (rubi::rubi-expon (quote (/ (+ (^ x 2) -1) (+ x -1))) (quote x)))
  ; Match-предикаты - по образцу, без распределения/раскрытия (IUF.m:1419-1475)
  (assert-equal #f (rubi::rubi-binomial-match-q (quote (* c (+ a (* b x)))) (quote x)))
  (assert-equal #t (rubi::rubi-binomial-match-q (quote (+ a (* b (^ x n)))) (quote x)))
  (assert-equal #f (rubi::rubi-quadratic-match-q (quote (^ (+ x 1) 2)) (quote x)))
  (assert-equal #t (rubi::rubi-quadratic-match-q (quote (+ a (* c (^ x 2)))) (quote x)))
  (assert-equal #t (rubi::rubi-trinomial-match-q (quote (+ a (* b (^ x 3)) (* c (^ x 6)))) (quote x)))
  ; BinomialQ по раскрытому многочлену: (a+b x)(a-b x) = a^2 - b^2 x^2
  (assert-equal #t (rubi::rubi-binomial-q (quote (* (+ a (* b x)) (+ a (* -1 b x)))) (quote x)))
  ; QuadraticQ: одночлен a x^2 - не трёхчлен; TrinomialQ не включает квадратный трёхчлен и квадрат двучлена
  (assert-equal #f (rubi::rubi-quadratic-q (quote (* 3 (^ x 2))) (quote x)))
  (assert-equal #t (rubi::rubi-quadratic-q (quote (+ 1 (* 3 (^ x 2)))) (quote x)))
  (assert-equal #f (rubi::rubi-trinomial-q (quote (+ a (* b x) (* c (^ x 2)))) (quote x)))
  ; GtQ/LtQ по значению константного выражения; символы - ложь
  (assert-equal #t (rubi::rubi-gtq (quote pi) 3))
  (assert-equal #t (rubi::rubi-ltq (quote (sqrt 2)) 3/2))
  (assert-equal #t (rubi::rubi-gtq (quote (^ 2 1/2)) 1))
  (assert-equal #f (rubi::rubi-gtq (quote a) 0))
  (assert-equal #f (rubi::rubi-leq (quote (exp 2)) 7))
  ; RemoveContent: свободные множители отброшены, содержание вынесено, отрицательный первый член - смена знака
  (assert-equal (quote (+ 1 x)) (rubi::rubi-remove-content (quote (+ -2 (* -2 x))) (quote x)))
  (assert-equal (quote (+ 1 (* 2 x))) (rubi::rubi-remove-content (quote (* c (+ 2 (* 4 x)))) (quote x)))
  ; образец с Sqrt/Exp приводится к степеням, как выражение (раньше 505 правил главы 1 не срабатывали)
  (assert-equal (quote (^ (+ ?a (* ?b (^ x 2))) -1/2)) (rubi::rubi-pat-normalize (quote (/ 1 (sqrt (+ ?a (* ?b (^ x 2))))))))
  (assert-equal (quote (+ (exp 2) (exp 1) (exp x))) (rubi::rubi-restore-e (quote (+ (^ E 2) E (^ E x)))))
  ; догрузка глав по файлам: до предела часов, недогруженное - следующим вызовом; константа без x главы не грузит
  (assert-equal #t (rubi::rubi-algebraic-in? (quote (* (exp 2) x)) (quote x)))
  (assert-equal #f (rubi::rubi-algebraic-in? (quote (exp x)) (quote x))))

; RUBI.D2: журнал отказов (*rubi-trace*) - первый ложный конъюнкт, тупик подвыражения; по умолчанию выключен
(deftest "rubi/D2: журнал отказов - первый ложный конъюнкт и тупик, при выключенном флаге журнал пуст"
  (rubi-test-setup
   (list (list "r1" '(^ x ?n)
               '(and (rubi::rubi-freeq (list ?n) (quote x)) (rubi::rubi-eqq ?n 5))
               '(* (/ 1 (+ n 1)) (^ (quote x) (+ n 1))))))
  (assert-equal #f rubi::*rubi-trace*)
  (assert-equal 'unknown (rubi-integrate '(^ x 3) 'x))
  (assert-equal '() rubi::*rubi-trace-log*)
  (set! rubi::*rubi-trace* #t)
  (let ((r (rubi-integrate '(^ x 3) 'x))
        (log rubi::*rubi-trace-log*))
    (set! rubi::*rubi-trace* #f)
    (assert-equal 'unknown r)
    (assert-true (member? '(cond-fail "r1" 2 rubi::rubi-eqq (^ x 3)) log))
    (assert-true (member? '(dead (^ x 3) 1 1) log))
    (assert-true (member? '(seen (^ x 3)) log))))

; RUBI.D3: Plus во Flat (Mathematica) - `a_ + b_.*x_^2` берёт все x-свободные слагаемые как a_
(deftest "rubi/D3: x-свободные слагаемые суммы группируются во вложенную сумму"
  (assert-equal '(^ (+ (+ c (* -1 a d)) (* b (^ x 2))) -1/2)
                (rubi::rubi-group-free '(^ (+ c (* -1 a d) (* b (^ x 2))) -1/2) 'x))
  ; одно свободное слагаемое и сумма без x-зависимых не меняются
  (assert-equal '(+ c (* b x)) (rubi::rubi-group-free '(+ c (* b x)) 'x))
  (assert-equal '(+ c d) (rubi::rubi-group-free '(+ c d) 'x)))

; RUBI.E1: Mathematica EllipticF/E/Pi принимают параметр m = k^2, наши elliptic-f/e/pi - модуль k
(deftest "rubi/E1: перевод параметра m эллиптических функций в модуль k"
  (assert-equal '(elliptic-f p 2) (rubi::rubi-ell-convert '(elliptic-f p 4)))
  (assert-equal '(* 3 (elliptic-e p 0)) (rubi::rubi-ell-convert '(* 3 (elliptic-e p 0))))
  (assert-equal '(elliptic-pi n p 3) (rubi::rubi-ell-convert '(elliptic-pi n p 9)))
  (assert-true (rubi::rubi-has-ell? '(* 2 (elliptic-f p 4)))))

; RUBI.E1: произведение трёх корней линейных множителей - EllipticF; образец (^ (* u^1/2 v^1/2 w^1/2) -1) распределяется
(deftest "rubi/E1: 1/(sqrt sqrt sqrt) даёт EllipticF, ответ проходит int-check"
  ; файл делит окружение с тестами на ручных правилах: возвращаем настоящие правила
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (let ((r (rubi-integrate (math-read "1/(sqrt(1-2x)*sqrt(5x+3)*sqrt(3x+2))") 'x)))
    (assert-true (rubi::rubi-has-ell? r))
    (assert-true (int-check r (math-read "1/(sqrt(1-2x)*sqrt(5x+3)*sqrt(3x+2))") 'x))))

; RUBI.C1: деление с символьными коэффициентами, Simp[u,x] с неподвижной точкой, предохранитель роста
(deftest "rubi/C1: деление многочленов с коэффициентом b/a, Simp[u,x] и рост формы"
  ; PolynomialQuotient/Remainder[1 + x, 1 - b x/a, x]: частное -a/b, остаток 1 + a/b (раньше «0 и 1»)
  (assert-equal '(* -1 a (^ b -1)) (rubi::rubi-polynomial-quotient '(+ 1 x) '(+ 1 (* (* -1 (^ a -1) b) x)) 'x))
  (assert-equal '(+ 1 (* a (^ b -1))) (rubi::rubi-polynomial-remainder '(+ 1 x) '(+ 1 (* (* -1 (^ a -1) b) x)) 'x))
  (assert-equal 0 (rubi::rubi-polynomial-remainder '(+ (* (^ a -1) (^ x 2)) (* -1 (^ a -1) (^ b 2))) '(+ x (* -1 b)) 'x))
  (assert-equal '(0 5) (list (rubi::rubi-polynomial-quotient 5 '(+ a (* b x)) 'x) (rubi::rubi-polynomial-remainder 5 '(+ a (* b x)) 'x)))
  ; Simp[u,x]: x-свободные коэффициенты в канонической форме - повторное применение 1.1.1.2 #39 даёт то же выражение
  (let* ((c1 (rubi::rubi-simp '(/ (* b c) (- (* b c) (* a d))) 'x))
         (d1 (rubi::rubi-simp '(/ (* b d) (- (* b c) (* a d))) 'x))
         (c2 (rubi::rubi-simp (list '/ (list '* 'b c1) (list '- (list '* 'b c1) (list '* 'a d1))) 'x)))
    (assert-equal c1 c2))
  ; одноаргументный Simp - по-прежнему simplify
  (assert-equal 3 (rubi::rubi-simp '(+ 1 2)))
  ; предохранитель: растущая цепочка одного правила (размеры строго растут, 1,5 раза) - да; постоянный размер - нет
  (set! rubi::*rubi-stack* (list (list "R" '(+ 1 (* x x x x))) (list "R" '(+ 1 (* x x))) (list "R" '(+ 1 x))))
  (assert-true (rubi::rubi-growth-cycle? "R" '(+ 1 (* x x x x x x x x x x x))))
  (assert-equal #f (rubi::rubi-growth-cycle? "R" '(+ 1 (* x x x x))))
  (assert-equal #f (rubi::rubi-growth-cycle? "Q" '(+ 1 (* x x x x x x x x x x x))))
  (set! rubi::*rubi-stack* '()))

(deftest "rubi/J1: сомножители с одинаковым основанием склеиваются (u^a u^b = u^(a+b))"
  (assert-equal '(^ (+ c (^ x 2)) -2) (rubi::rubi-merge-bases '(* (^ (+ c (^ x 2)) -1) (^ (+ c (^ x 2)) -1))))
  ; сумма показателей 1 - основание; 0 - множитель исчезает; числа и нечисловые показатели не трогаются
  (assert-equal '(* 2 (^ (+ 1 x) 1/2) (^ y n) (^ y m) (^ 2 1/2))
                (rubi::rubi-merge-bases '(* 2 (^ x 2) x (^ (+ 1 x) -1/2) (+ 1 x) (^ y n) (^ y m) (^ x -3) (^ 2 1/2))))
  (assert-equal '(+ 1 x) (rubi::rubi-merge-bases '(* (^ (+ 1 x) 1/2) (^ (+ 1 x) 1/2))))
  ; разные основания (x^2+c и x^2+d) не склеиваются
  (assert-equal '(* (^ (+ c (^ x 2)) -1) (^ (+ d (^ x 2)) -1/2))
                (rubi::rubi-merge-bases '(* (^ (+ c (^ x 2)) -1) (^ (+ d (^ x 2)) -1/2))))
  ; 1/((x^2+c) sqrt(x^2+c) sqrt(x^2+c)) = (x^2+c)^-2: решается, ответ проходит int-check
  (let ((r (rubi-integrate (math-read "1/((x^2+c)*sqrt(x^2+c)*sqrt(x^2+c))") 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (int-check r (math-read "1/((x^2+c)*sqrt(x^2+c)*sqrt(x^2+c))") 'x))))

(deftest "rubi/J2: Expon[u,x,Min] с тремя аргументами (1.3.3-2 #17, 1.4.1 #24)"
  (assert-equal 2 (rubi::rubi-expon '(+ (* a (^ x 2)) (* b (^ x 3))) 'x 'Min))
  (assert-equal 3 (rubi::rubi-expon '(+ (* a (^ x 2)) (* b (^ x 3))) 'x))
  (assert-equal 0 (rubi::rubi-expon '(+ a (* b x)) 'x 'Min)))

(deftest "rubi/J3: ответ с AppellF1 проверяется в точках внутри круга сходимости"
  (let ((f '(* x (appell-f1 1 -1/6 -1/6 2 (* -1 b x) (* -1 d x))))
        (e '(* (^ (+ 1 (* b x)) 1/6) (^ (+ 1 (* d x)) 1/6))))
    (assert-true (rubi::rubi-int-check f e 'x))
    ; неверный ответ (множитель 2) отвергается
    (assert-equal #f (rubi::rubi-int-check (list '* 2 f) e 'x))))
