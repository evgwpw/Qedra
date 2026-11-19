; RUBI.CH4: глава 4 (sec/tan/cot) — 9 833 UNKNOWN в пилоте master 4180a93. Классификация 751 задачи по журналу
; (run-режим): check 569 (76 %), rhs-no-rule 115, бюджет 67, решено 2. Первые отвергнутые проверкой ответы —
; правила 9.3 #18 (245 задач) и 9.3 #38 (218): в теле 9.3 #18/#22-#24 (и 9.4 #18/#22-#24) модульные переменные
; оставались символами, а Mathematica `Set` (`q = expr`) переводился в наш `set` — конструктор множества из
; lib/set.lisp, — поэтому ответы приходили в виде `(* q r …)` с несвязанными q, r и проверка их отвергала.
; Тест охраняет: (1) присвоение в выражении даёт значение (begin (set! X V) X); (2) тела 9.3/9.4 больше не
; содержат вызова `(set `; (3) правило 9.3 #18 даёт ответ без свободных q/r, и этот ответ проходит int-check.
; (4) ac-norm сводит csc/cot/sec к отрицательным степеням sin/tan/cos; (5) фильтр движка принимает
; головы-синонимы и показатель с обратным знаком; (6) 4.5.1.2 и csc-вариант интегрируются.

(load (string-append lib-dir "rubi/utils.lisp"))

; другие файлы тестов подменяют правила Rubi игрушечными наборами — возвращаем настоящие
(define (rch4-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(deftest "rubi-ch4/1: присвоение в выражении — (begin (set! X V) X) отдаёт значение (в теле правила)"
  ; так генератор переводит Mathematica `Set`; прежний перевод в `set` давал множество и оставлял переменную символом
  (assert-equal 6 (eval '(let ((q 'q)) (begin (set! q (* 2 3)) q))))
  (assert-equal 10 (eval '(let ((r 'r)) (+ 4 (begin (set! r 6) r)))))
  ; и в условии and: (not (falseq (begin (set! r expr) r)))
  (assert-true (eval '(let ((r 'r)) (and (not (equal? (begin (set! r (+ 1 2)) r) 0)) (= r 3))))))

(deftest "rubi-ch4/2: в телах правил 9.3/9.4 нет вызова (set …) — только set!"
  (let ((t93 (read-text-file "lib/rubi/rules/9.3.body.lisp"))
        (t94 (read-text-file "lib/rubi/rules/9.4.body.lisp")))
    (assert-true (string-contains? t93 "(begin (set! "))
    (assert-true (string-contains? t94 "(begin (set! "))
    (assert-true (not (string-contains? t93 "(set r ")))
    (assert-true (not (string-contains? t93 "(set q ")))
    (assert-true (not (string-contains? t94 "(set r ")))))

(deftest "rubi-ch4/3: правило 9.3 #18 — ответ без свободных q/r и верный"
  (rch4-fresh)
  (rubi-integrate 1 'x)                       ; загрузка правил (первый вызов в процессе — долгий)
  (let* ((e (math-read "sin(x)^2/(a + b*sin(x)^2)"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r 'integrate)))
    (assert-true (not (contains-sym? r 'q)))
    (assert-true (not (contains-sym? r 'r)))
    (assert-true (int-check r e 'x))))

; RUBI.CH4: образцы 4.x написаны в csc/cot/sec (905/528/400 вхождений), а упрощатель порта сводит Sec[x] -> 1/Cos[x]
; (DeactivateTrig: cos(u)^-n). Нормализация образца в ac-norm переводит обратную голову в отрицательную степень
; прямой, а фильтр движка ослабляется в двух местах: головы csc/cot/sec считаются найденными при наличии
; sin/tan/cos (rubi-head-alias) и показатель образца принимается при наличии обратного по знаку
; (rubi-exps-subset?). Тесты 4–5 охраняют эти три места.
; RUBI.SYM.3: форма выбирается явно. Единая форма (*rubi-nf* #t) — автовычисление Mathematica:
; sec/csc/cot остаются своими головами; старая форма (#f) — ac-norm сводит их к степеням
; sin/cos/tan, tan/cot/sec/csc живут как отрицательные степени. Тест проверяет договорённость ТОЙ
; формы, которую выбирает, и возвращает флаги как были.
(define (with-form nf? f)
  (let ((saved *rubi-nf*))
    (set! *rubi-nf* nf?)
    (ac-trig-recip! (not nf?))
    (let ((r (f)))
      (set! *rubi-nf* saved)
      (ac-trig-recip! (not saved))
      r)))

(deftest "rubi-ch4/4: ac-norm — старая форма сводит csc/cot/sec, единая оставляет головами"
  (with-form #f
   (lambda ()
     (assert-equal '(^ (cos x) -1) (ac-norm '(sec x)))
     (assert-equal '(^ (sin x) -1) (ac-norm '(csc x)))
     (assert-equal '(^ (tan x) -1) (ac-norm '(cot x)))
     (assert-equal '(^ (cos x) -2) (ac-norm '(^ (sec x) 2)))
     ; в произведении каждая голова нормализуется независимо
     (assert-equal '(* (^ (cos x) -1) (^ (tan x) -1)) (ac-norm '(/ (sec x) (tan x))))))
  ; единая форма: ac-norm — только автовычисление, инертные головы не переписываются
  (with-form #t
   (lambda ()
     (assert-equal '(sec x) (ac-norm '(sec x)))
     (assert-equal '(csc x) (ac-norm '(csc x)))
     (assert-equal '(cot x) (ac-norm '(cot x)))
     (assert-equal '(^ (sec x) 2) (ac-norm '(^ (sec x) 2)))
     (assert-equal '(* (sec x) (^ (tan x) -1)) (ac-norm '(/ (sec x) (tan x)))))))

(deftest "rubi-ch4/5: фильтр движка — головы-синонимы и показатель с обратным знаком"
  ; sin в выражении закрывает требование головы csc (и так же tan/cot, cos/sec)
  (assert-equal '(sin csc) (rubi::rubi-head-alias 'sin))
  (assert-equal '(tan cot) (rubi::rubi-head-alias 'tan))
  (assert-equal '(cos sec) (rubi::rubi-head-alias 'cos))
  (assert-true (not (rubi::rubi-head-alias 'exp)))
  ; образец с показателем 2 подходит к выражению со степенью -2 (sec^2 -> cos^-2)
  (assert-true (rubi::rubi-exps-subset? (list 2) (list -2)))
  (assert-true (rubi::rubi-exps-subset? (list 2) (list 2)))
  (assert-true (not (rubi::rubi-exps-subset? (list 3) (list -2)))))

(deftest "rubi-ch4/6: 4.5.1.2 (sec^2/(a sec + a)) и csc-вариант теперь интегрируются"
  (rch4-fresh)
  ; RUBI.SYM.3: rch4-fresh перезагружает правила внутри вызова, и на холодную поиск sec-формы идёт
  ; ≈3,4 с (замер: sec^2/(a sec+a) — load 2,9 с + поиск 3,4 с), а бюджет вызова = 4 с минус загрузка.
  ; Поэтому, как в rubi-c (21k.4) и rubi-backtrack/1, бюджет движка на время теста поднимается.
  (let ((old rubi::rubi-time-limit))
    (set! rubi::rubi-time-limit 30.0)
    (rubi-integrate 1 'x)
    (let* ((e (math-read "sec(c+d*x)^2/(a*sec(c+d*x)+a)"))
           (r (rubi-integrate e 'x)))
      (assert-true (not (equal? r 'unknown)))
      (assert-true (not (contains-sym? r 'integrate)))
      (assert-true (int-check r e 'x)))
    (let* ((e (math-read "csc(c+d*x)/(a + a*csc(c+d*x))"))
           (r (rubi-integrate e 'x)))
      (assert-true (not (equal? r 'unknown)))
      (assert-true (int-check r e 'x)))
    (set! rubi::rubi-time-limit old)))

; RUBI.CH4.2: правило 9.3 #38 (/; утилита SubstForFractionalPowerOfQuotientOfLinears) раньше всегда падало:
; lib/rubi/utils.lisp давал заглушку `(define (rubi-subst-for-fractional-power-of-quotient-of-linears u x) u)`,
; и `(part lst 4)` в теле 9.3 #38 уходил за границу списка («nth: индекс 3 вне границ») — правило отсеивалось
; на каждой задаче, а интегралы с ((a+b x)/(c+d x))^(m/n) не брались вовсе. Реализовано по
; IUF.m:1724-1733 (QuotientOfLinearsQ), 1735-1760 (QuotientOfLinearsP), 1778-1795 (QuotientOfLinearsParts),
; 1831-1840 (FractionalPowerOfQuotientOfLinears), 1801-1811 (SubstForFractionalPowerOfQuotientOfLinears).
(deftest "rubi-ch4/7: QuotientOfLinearsParts/Q и SubstForFractionalPowerOfQuotientOfLinears"
  ; (a+b x)/(c+d x): коэффициенты числителя и знаменателя; свободные от x свёртки — False (b или d = 0)
  (assert-equal '(a b c d) (rubi::rubi-quotient-of-linears-parts '(/ (+ a (* b x)) (+ c (* d x))) 'x))
  (assert-equal '(2 3 4 5) (rubi::rubi-quotient-of-linears-parts '(/ (+ 2 (* 3 x)) (+ 4 (* 5 x))) 'x))
  (assert-true (rubi::rubi-quotient-of-linears-q '(/ (+ a (* b x)) (+ c (* d x))) 'x))
  (assert-true (not (rubi::rubi-quotient-of-linears-q '(+ a (* b x)) 'x)))
  (assert-true (not (rubi::rubi-quotient-of-linears-q '(* a b) 'x)))
  ; ((a+b x)/(c+d x))^(1/2): n = 2, замена та же база, свободный множитель — b*c - a*d
  (let ((s (rubi::rubi-subst-for-fractional-power-of-quotient-of-linears
            '(^ (/ (+ a (* b x)) (+ c (* d x))) 1/2) 'x)))
    (assert-true (pair? s))
    (assert-equal 2 (nth s 1))
    (assert-equal '(/ (+ a (* b x)) (+ c (* d x))) (nth s 2))
    (assert-equal '(* 1 (+ (* -1 a d) (* b c))) (nth s 3)))
  ; нет отношения линейных под дробной степенью — False (а не ошибка)
  (assert-true (not (rubi::rubi-subst-for-fractional-power-of-quotient-of-linears
                     '(^ (sin (+ a (* b x))) -1/2) 'x)))
  (assert-true (not (rubi::rubi-subst-for-fractional-power-of-quotient-of-linears
                     '(^ (+ a (* b x)) 1/2) 'x))))

(deftest "rubi-ch4/9: 4.1.0.1 #1 стоит с условием-прогрессом, непонимание != оставлено как обход"
  ; rubi-neq есть и работает (на случай, если правила начнут им пользоваться)
  (assert-equal #t (rubi::rubi-neq 'a 'b))
  (assert-equal #f (rubi::rubi-neq 'x 'x))
  ; RUBI.CH4.3: 4.1.0.1 #1 — Int[u,x] = Int[DeactivateTrig[u,x],x]; условие правила теперь «DeactivateTrig
  ; действительно меняет выражение» (иначе вложенный вызов дал бы Int того же выражения — самовызов).
  (let ((t (read-text-file "lib/rubi/rules/4.1.0.1.body.lisp")))
    (assert-true (string-contains? t "(not (equal? (rubi::rubi-deactivate-trig ?u (quote x)) ?u))")))
  ; `!=` (not-equal?) оставлено намеренно: замена на rubi-neq включает 1.1.3.4 #30 и теряет ответы (см. RUBI.ELL1
  ; в генераторе и замер RUBI.CH4.2.3: срез 1.1 1263 → 1262) — тест охраняет, что имя в телах по-прежнему not-equal?
  (assert-true (string-contains? (read-text-file "lib/rubi/rules/1.1.3.4.body.lisp") "not-equal?")))

(deftest "rubi-ch4/10: DeactivateTrig/FixInertTrigFunction по исходнику (IUF.m:6189-6484)"
  ; Уже нормализованная форма не меняется: голый sin/cos остаются как есть (условия формы C0c),
  ; поэтому шлюз на них не срабатывает — самовызова нет. Верно в обеих формах.
  (assert-equal '(cos x) (rubi::rubi-deactivate-trig '(cos x) 'x))
  (assert-equal '(sin x) (rubi::rubi-deactivate-trig '(sin x) 'x))
  ; FixInertTrigFunction: произведение двух голов сводится к одной (6237-6309, 6312-6318)
  (assert-equal '(* (^ (cos x) -3) (^ (sin x) -1))
                (rubi::rubi-fix-inert-trig-function '(* (^ (sec x) 3) (^ (sin x) -1)) 'x))
  ; Старая форма: sec^3 — «моном по одной голове», DeactivateTrig его не трогает (прогресса нет);
  ; вложенная структура унифицируется: cos -> sin(x+Pi/2) (6588-6590), шлюз видит изменение.
  (with-form #f
   (lambda ()
     (assert-equal '(^ (sec x) 3) (rubi::rubi-deactivate-trig '(^ (sec x) 3) 'x))
     (assert-true (not (rubi::rubi-inert-trig-progress? '(^ (sec x) 3) 'x)))
     (assert-equal '(^ (+ a (* b (sin (+ x (/ pi 2))))) 1/2)
                   (rubi::rubi-deactivate-trig '(^ (+ a (* b (cos x))) 1/2) 'x))
     (assert-true (not (equal? (rubi::rubi-deactivate-trig '(^ (+ a (* b (cos x))) 1/2) 'x)
                               '(^ (+ a (* b (cos x))) 1/2))))
     (assert-equal '(* (^ (sin x) -2) (^ (sin x) -3))
                   (rubi::rubi-fix-inert-trig-function '(* (^ (csc x) 2) (^ (csc x) 3)) 'x))
     (assert-equal '(* (^ (cot x) -2) (cot x))
                   (rubi::rubi-fix-inert-trig-function '(* (^ (tan x) 2) (cot x)) 'x))))
  ; Единая форма: ac-norm не сводит sec к cos^-1, поэтому DeactivateTrig видит инертную голову, а
  ; таблица Unify при *rubi-nf* активна (inert.lisp: rubi-inert-generated-active?) — форма меняется.
  ; Замена идёт клаузой Unify, а не FixInertTrigFunction, поэтому rubi-inert-trig-progress? (он мерит
  ; только шаг Fix) остаётся #f: изменение проверяем самим DeactivateTrig.
  (with-form #t
   (lambda ()
     (assert-equal '(^ (sin (+ (* 1/2 pi) x)) -3)
                   (rubi::rubi-deactivate-trig '(^ (sec x) 3) 'x))
     (assert-true (not (rubi::rubi-inert-trig-progress? '(^ (sec x) 3) 'x)))
     (assert-true (not (equal? (rubi::rubi-deactivate-trig '(^ (sec x) 3) 'x) '(^ (sec x) 3))))
     (assert-equal '(^ (+ a (* b (sin (+ (* 1/2 pi) x)))) 1/2)
                   (rubi::rubi-deactivate-trig '(^ (+ a (* b (cos x))) 1/2) 'x))
     ; Шаг FixInertTrigFunction для произведения csc-степеней в единой форме зависит от того, какие
     ; образцы таблицы Unify уже скомпилированы в этом процессе (кэш *rubi-inert-prep*), поэтому здесь
     ; не проверяется: ожидание зафиксировано в блоке старой формы, где оно устойчиво.
     )))



(deftest "rubi-ch4/8: интегралы ((a+b x)/(c+d x))^(m/n) берутся (правило 9.3 #38)"
  (rch4-fresh)
  (rubi-integrate 1 'x)
  (for-each
   (lambda (in)
     (let* ((e (math-read in)) (r (rubi-integrate e 'x)))
       (assert-true (not (equal? r 'unknown)))
       (assert-true (not (contains-sym? r 'integrate)))
       (assert-true (int-check r e 'x))))
   (list "sqrt((a+b*x)/(c+d*x))" "1/sqrt((a+b*x)/(c+d*x))" "((a+b*x)/(c+d*x))^(1/3)")))

(deftest "rubi-ch4/11: UnifyInertTrigFunction — произведения голов (IUF.m:6566-7361)"
  ; cos*csc -> sin[x+Pi/2]*(-sec[x+Pi/2]) (6566-6568: (a Cos)^m (b Csc)^n)
  (assert-equal (quote (* (sin (+ x (/ pi 2))) -1 (sec (+ x (/ pi 2)))))
                (rubi::rubi-inert-unify-product (quote (* (cos x) (csc x))) (quote x)))
  ; (g Csc)^p (a+b Cos)^m -> (g Sec[x-Pi/2])^p (a-b Sin[x-Pi/2])^m (6610-6612)
  (assert-equal (quote (* (^ (sec (- x (/ pi 2))) 2) (+ a (* b -1 (sin (- x (/ pi 2)))))))
                (rubi::rubi-inert-unify-product (quote (* (^ (csc x) 2) (+ a (* b (cos x))))) (quote x)))
  ; (g Cot)^p (a+b Cos)^m -> (-g Tan[x-Pi/2])^p (a-b Sin[x-Pi/2])^m (6627-6631)
  (assert-equal (quote (* -1 (tan (- x (/ pi 2))) (^ (+ a (* b -1 (sin (- x (/ pi 2))))) 3)))
                (rubi::rubi-inert-unify-product (quote (* (cot x) (^ (+ a (* b (cos x))) 3))) (quote x)))
  ; (a Cos)^m (b Cot)^n -> (a Sin[x+Pi/2])^m (-b Tan[x+Pi/2])^n (6878-6880)
  (assert-equal (quote (* (sin (+ x (/ pi 2))) (^ (+ a (* b -1 (tan (+ x (/ pi 2))))) 2)))
                (rubi::rubi-inert-unify-product (quote (* (cos x) (^ (+ a (* b (cot x))) 2))) (quote x)))
  ; (a+b (c Cos)^n)^p -> sin-форма (6861-6863), внутренняя степень сохраняется
  (assert-equal (quote (* (^ (+ a (* b (^ (sin (+ x (/ pi 2))) 2))) 3) (+ A (* B (^ (sin (+ x (/ pi 2))) 2)))))
                (rubi::rubi-inert-unify-product
                 (quote (* (^ (+ a (* b (^ (cos x) 2))) 3) (+ A (* B (^ (cos x) 2))))) (quote x)))
  ; произведение сумм одной головы (a+b Tan)^m (c+d Tan)^n клаузой не покрыто — форма не меняется
  (assert-true (not (rubi::rubi-inert-unify-product
                     (quote (* (^ (+ a (* b (tan x))) 2) (^ (+ c (* d (tan x))) 3))) (quote x))))
  ; входной шлюз: произведение двух голов нормализуется, Fix+Unify сводят его к одной голове.
  ; В старой форме sec записан степенью cos, в единой остаётся головой до DeactivateTrig.
  (with-form #f
   (lambda ()
     (assert-equal (quote (* (^ (sec x) -1) (^ (sin x) -1)))
                   (rubi::rubi-deactivate-trig (quote (* (cos x) (csc x))) (quote x)))))
  (with-form #t
   (lambda ()
     ; в единой форме произведение меняется: csc сводится к sin-форме (точный вид зависит от того,
     ; какие образцы таблицы Unify уже скомпилированы в процессе, поэтому проверяется свойство)
     (let ((v (rubi::rubi-deactivate-trig (quote (* (cos x) (csc x))) (quote x))))
       (assert-true (not (equal? v (quote (* (cos x) (csc x))))))
       (assert-true (rubi::rubi-has-head? v (quote sin)))))))

(deftest "rubi-ch4/13: sqrt(a+b sec^2) — порядок нормализаций (RUBI.CH4.5)"
  ; Порядок в исходнике: активированная форма (sec как голова) идёт в правило 4.5.7 #9, а не в
  ; DeactivateTrig/Unify: ac-norm порта сводит sec^2 к cos^-2, и клауза (a+b Cos)^n (IUF.m:6588)
  ; переписывала её в sin[x+Pi/2]^-2 — форма 4.5.7 #9 терялась (регрессия после CH4.3).
  (assert-true (rubi::rubi-inert-neg-trig-power-in-sum? (quote (^ (+ a (* b (^ (cos x) -2))) (/ 1 2)))))
  ; «cos-сумма» из отрицательной степени не нормализуется, произведение голов — нормализуется
  (assert-equal (quote (^ (+ a (* b (^ (cos x) -2))) (/ 1 2)))
                (rubi::rubi-deactivate-trig (quote (^ (+ a (* b (^ (cos x) -2))) (/ 1 2))) (quote x)))
  ; произведение голов: форма зависит от режима — старая (sec степенью cos) и единая (голова)
  (with-form #f
   (lambda ()
     (assert-equal (quote (* (^ (sec x) 2) (^ (sin x) -1)))
                   (rubi::rubi-deactivate-trig (quote (* (^ (cos x) -2) (csc x))) (quote x)))))
  (with-form #t
   (lambda ()
     ; в единой форме sec^2 остаётся головой, DeactivateTrig её сводит (точный вид зависит от
     ; скомпилированных образцов таблицы Unify — проверяется свойство)
     (let ((v (rubi::rubi-deactivate-trig (quote (* (^ (cos x) -2) (csc x))) (quote x))))
       (assert-true (not (equal? v (quote (* (^ (cos x) -2) (csc x))))))
       (assert-true (rubi::rubi-has-head? v (quote sin))))))
  ; интеграл берётся (база 5f4e465: ok; ветка CH4.3/4.4: unknown). Бюджет поднят, как в rubi-ch4/6:
  ; rch4-fresh перезагружает правила внутри вызова, и загрузка съедает лимит 4 с.
  (rch4-fresh)
  (let ((old rubi::rubi-time-limit))
    (set! rubi::rubi-time-limit 30.0)
    (let* ((e (math-read "sqrt(a + b*sec(x)^2)"))
           (r (rubi-integrate e 'x)))
      (assert-true (not (equal? r 'unknown)))
      (assert-true (int-check r e 'x)))
    (set! rubi::rubi-time-limit old)))

(deftest "rubi-ch4/14: FunctionOfTrig возвращает линейный аргумент v (IUF.m:4365-4392)"
  ; раньше утилита возвращала True/#f, и правила 4.7.5 #21/#22/#47/#48/#58/#67/#70/#72 строили
  ; (tan v) из #t — 4.7.5 в журнале отказов шло как rubi-no-rule
  (assert-equal 'x (rubi::rubi-function-of-trig '(^ (+ a (* b (^ (sec x) 2))) (/ 1 2)) 'x))
  (assert-equal '(+ c (* d x)) (rubi::rubi-function-of-trig '(^ (+ a (* b (tan (+ c (* d x))))) 3) 'x))
  ; гиперболическая голова: аргумент как I*v (4384)
  (assert-equal '(* %i (* 2 x)) (rubi::rubi-function-of-trig '(+ 1 (sinh (* 2 x))) 'x))
  (assert-equal 'x (rubi::rubi-function-of-trig '(+ (sin x) (cos x)) 'x))
  ; аргументы не пропорциональны — False (4377-4380)
  (assert-true (not (rubi::rubi-function-of-trig '(+ (sin x) (cos (* 2 x))) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig '(^ x 2) 'x))))
(deftest "rubi-ch4/12: TryPureTanSubst по исходнику (IUF.m:6099-6107)"
  ; False для ArcTan[c*(a+b*Tan[v])] с линейным v и FreeQ[{a,b,c},x]
  (assert-true (not (rubi::rubi-try-pure-tan-subst (quote (atan (* c (+ a (* b (tan x)))))) (quote x))))
  (assert-true (not (rubi::rubi-try-pure-tan-subst (quote (atan (+ a (tan (* c x))))) (quote x))))
  (assert-true (not (rubi::rubi-try-pure-tan-subst (quote (acot (* 2 (+ a (* b (cot x)))))) (quote x))))
  ; True во всех остальных случаях
  (assert-true (rubi::rubi-try-pure-tan-subst (quote (atan (+ a (* b (sin x))))) (quote x)))
  (assert-true (rubi::rubi-try-pure-tan-subst (quote (atan (+ a (* x (tan x))))) (quote x)))
  (assert-true (rubi::rubi-try-pure-tan-subst (quote (tan x)) (quote x))))
