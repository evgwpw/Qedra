; RUBI.CH-A, фаза 2: утилиты глав 1.1.2–1.1.4 из lib/rubi/utils-a.lisp.
; Источник: Rubi 4.17.3.0 (commit 61e9c18) — файлы правил своих глав (в IntegrationUtilityFunctions.m этих
; клауз нет), ссылки на строку — в комментарии к каждому случаю.
; Общее имя rubi-int-binomial-q в lib/rubi/utils.lisp:599 реализует только 8-аргументную форму: вызов с семью
; аргументами возвращает #f, вызов с десятью попадает в ту же 8-аргументную ветку (аргументы сдвинуты) и даёт
; мусор, например (rubi::rubi-int-binomial-q 1 1 1 1 1 1 5 1/2 1/3 'x) = #t там, где Rubi (1.1.3.4.m:89) даёт #f.
; Маршрутизация 7/10 аргументов — в utils.lisp (диспетчер rubi-int-binomial-q, шаг RUBI.K1).
(load (string-append lib-dir "rubi/utils-a.lisp"))

; --- IntBinomialQ[a,b,c,n,m,p,x] — "1.1.3.2 (c x)^m (a+b x^n)^p.m", строка 118 ---

(deftest "rubi-A: IntBinomialQ 7 арг — IGtQ[p,0] (1.1.3.2.m:118)"
  ; p = 2 (целое > 0); m не число, n = 1/2 — остальные клаузы ложны
  (assert-equal #t (rubi::rubi-int-binomial-q7 'a 'b 'c 1/2 'm 2 'x)))

(deftest "rubi-A: IntBinomialQ 7 арг — RationalQ[m] и IntegersQ[n,2p] (1.1.3.2.m:118)"
  ; n = 6, p = 1/2: 2p = 1 — целое; RationalQ[1/2] — да
  (assert-equal #t (rubi::rubi-int-binomial-q7 'a 'b 'c 6 1/2 1/2 'x)))

(deftest "rubi-A: IntBinomialQ 7 арг — IntegerQ[(m+1)/n+p] (1.1.3.2.m:118)"
  ; n = 5, m = 1, p = 3/5: (m+1)/n + p = 2/5 + 3/5 = 1 — целое
  (assert-equal #t (rubi::rubi-int-binomial-q7 'a 'b 'c 5 1 3/5 'x)))

(deftest "rubi-A: IntBinomialQ 7 арг — n = 4 и IntegersQ[2m,4p] (1.1.3.2.m:118)"
  ; m = 1/2, p = 1/4: 2m = 1 и 4p = 1 — целые
  (assert-equal #t (rubi::rubi-int-binomial-q7 'a 'b 'c 4 1/2 1/4 'x)))

(deftest "rubi-A: IntBinomialQ 7 арг — n = 2, IntegerQ[6p] и IntegerQ[m-p] (1.1.3.2.m:118)"
  ; p = 1/3, m = 4/3: 6p = 2, m-p = 1 — целые, m — нет
  (assert-equal #t (rubi::rubi-int-binomial-q7 'a 'b 'c 2 4/3 1/3 'x)))

(deftest "rubi-A: IntBinomialQ 7 арг — ложь на символьных показателях (1.1.3.2.m:118)"
  ; n = 5, m = 1/2, p = 1/3: все клаузы ложны (n не 2/4/3-вид, показатели не целые)
  (assert-equal #f (rubi::rubi-int-binomial-q7 'a 'b 'c 5 1/2 1/3 'x)))

(deftest "rubi-A: IntBinomialQ 7 арг — аргументы правила 1.1.2.2 #8 (1.1.3.2.m:118)"
  ; правило 1.1.2.2 #8 зовёт (a b c 2 m p x) при m = -3, p = 1/2 (например ∫(a+b x²)^p/x³ dx)
  (assert-equal #t (rubi::rubi-int-binomial-q7 'a 'b 'c 2 -3 1/2 'x)))

; --- IntBinomialQ[a,b,c,d,e,m,n,p,q,x] — "1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m", строка 89 ---

(deftest "rubi-A: IntBinomialQ 10 арг — IntegersQ[p,q] (1.1.3.4.m:89)"
  ; p = -1, q = -2 — целые (IGtQ ложны)
  (assert-equal #t (rubi::rubi-int-binomial-q10 1 1 1 1 1 1 5 -1 -2 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — IGtQ[q,0] (1.1.3.4.m:89)"
  ; q = 2 — целое > 0, p = 1/2
  (assert-equal #t (rubi::rubi-int-binomial-q10 1 1 1 1 1 1 5 1/2 2 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — n = 2 и IntegersQ[m,2p,2q] (1.1.3.4.m:89)"
  (assert-equal #t (rubi::rubi-int-binomial-q10 1 1 1 1 1 1 2 1/2 1/2 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — n = 4 и IntegersQ[m,2p,q] (1.1.3.4.m:89)"
  ; n = 4: вторая пара (m,p,2q) ложна (2q = 2), работает (m,2p,q) = (1,1,1)
  (assert-equal #t (rubi::rubi-int-binomial-q10 1 1 1 1 1 1 4 1/2 1 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — n = 3, EqQ[b c-4 a d,0] (1.1.3.4.m:89)"
  ; b c - 4 a d = 4*1 - 4*1*1 = 0; q = 0, m = 1, p = 1/2: IntegersQ[(m-1)/3,q,p-1/2] = (0,0,0)
  (assert-equal #t (rubi::rubi-int-binomial-q10 1 4 1 1 1 1 3 1/2 0 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — n = 3, EqQ[b c+a d,0] (1.1.3.4.m:89)"
  ; b c + a d = 1 - 1 = 0; IntegersQ[m,q,3p] = (1,0,1)
  (assert-equal #t (rubi::rubi-int-binomial-q10 1 1 1 -1 1 1 3 1/3 0 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — ложь при n = 5 (1.1.3.4.m:89)"
  ; n = 5, m = 1, p = 1/2, q = 1/3 — ни одна клауза не проходит (у Rubi здесь False)
  (assert-equal #f (rubi::rubi-int-binomial-q10 1 1 1 1 1 1 5 1/2 1/3 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг — аргументы правила 1.1.2.4 (1.1.3.4.m:89)"
  ; правило 1.1.2.4 зовёт (a b c d e m 2 p q x); при m = -3, p = 1/2, q = 1/2:
  ; IntegersQ[m, 2p, 2q] = (-3, 1, 1) — целые, n = 2
  (assert-equal #t (rubi::rubi-int-binomial-q10 'a 'b 'c 'd 'e -3 2 1/2 1/2 'x)))

; --- устойчивость: условия правил зовут утилиты на параметрах (символах), а исключение условия дорого
; (перехват в глубоком стеке — 40-180 мс), поэтому на символьных аргументах ожидается #f без ошибки

(deftest "rubi-A: IntBinomialQ 7 арг на символах — ложь без ошибок (1.1.3.2.m:118)"
  (assert-equal #f (rubi::rubi-int-binomial-q7 'a 'b 'c 'n 'm 'p 'x)))

(deftest "rubi-A: IntBinomialQ 10 арг на символах — ложь без ошибок (1.1.3.4.m:89)"
  (assert-equal #f (rubi::rubi-int-binomial-q10 'a 'b 'c 'd 'e 'm 'n 'p 'q 'x)))
