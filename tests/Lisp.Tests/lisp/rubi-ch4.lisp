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
(deftest "rubi-ch4/4: ac-norm сводит csc/cot/sec к отрицательным степеням sin/tan/cos"
  (assert-equal '(^ (cos x) -1) (ac-norm '(sec x)))
  (assert-equal '(^ (sin x) -1) (ac-norm '(csc x)))
  (assert-equal '(^ (tan x) -1) (ac-norm '(cot x)))
  (assert-equal '(^ (cos x) -2) (ac-norm '(^ (sec x) 2)))
  ; в произведении каждая голова нормализуется независимо
  (assert-equal '(* (^ (cos x) -1) (^ (tan x) -1)) (ac-norm '(/ (sec x) (tan x)))))

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
  (rubi-integrate 1 'x)
  (let* ((e (math-read "sec(c+d*x)^2/(a*sec(c+d*x)+a)"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r 'integrate)))
    (assert-true (int-check r e 'x)))
  (let* ((e (math-read "csc(c+d*x)/(a + a*csc(c+d*x))"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (int-check r e 'x))))

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

(deftest "rubi-ch4/9: 4.1.0.1 #1 выключено (DeactivateTrig — тождество), непонимание != оставлено как обход"
  ; rubi-neq есть и работает (на случай, если правила начнут им пользоваться)
  (assert-equal #t (rubi::rubi-neq 'a 'b))
  (assert-equal #f (rubi::rubi-neq 'x 'x))
  ; 4.1.0.1 #1 — Int[u,x] = Int[DeactivateTrig[u,x],x]; DeactivateTrig в порте тождество, вложенный вызов съедал
  ; бюджет у 316 из 394 задач выборки главы 4. Правило выключено условием #f (замер — в tools/rubi/generate.mjs).
  (let ((t (read-text-file "lib/rubi/rules/4.1.0.1.body.lisp")))
    (assert-true (string-contains? t "(\"Rubi 4.1.0.1 #1\" (and (rubi::rubi-function-of-trig-of-linear-q ?u (quote x)) #f)")))
  ; `!=` (not-equal?) оставлено намеренно: замена на rubi-neq включает 1.1.3.4 #30 и теряет ответы (см. RUBI.ELL1
  ; в генераторе и замер RUBI.CH4.2.3: срез 1.1 1263 → 1262) — тест охраняет, что имя в телах по-прежнему not-equal?
  (assert-true (string-contains? (read-text-file "lib/rubi/rules/1.1.3.4.body.lisp") "not-equal?")))

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
