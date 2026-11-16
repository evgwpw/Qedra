; RUBI.CH567: главы 5-7 (обратные тригонометрические, гиперболические, обратные гиперболические) —
; классификация выборки отказов `research/rubi/ch567-unknown-900.tsv` (300 задач на главу, журнал diagnose-run)
; дала: check 523, rhs-no-rule 223, budget 143, ok 11. Главный класс — ответы, отвергнутые проверкой
; (последние отказы: 9.3 #18/#17/#16/#66); структурных отказов «нет правила» почти нет.
; Тест охраняет перенесённые по исходнику утилиты глав 5-7:
;   InverseFunctionQ (IUF.m:303-304), InverseFunctionFreeQ (IUF.m:317-322) — раньше проверялась только
;   голова верхнего узла, поэтому (x*asin(x)) считалось свободным от обратных функций, а asin(a) — нет;
;   InverseFunctionOfLinear (IUF.m:6084-6092), FunctionOfInverseLinear (IUF.m:4234-4256) — были заглушкой
;   и отсутствовали.

(load (string-append lib-dir "rubi/utils.lisp"))

(deftest "rubi-ch567/1: InverseFunctionQ — обратные функции, лог, гиперболика (IUF.m:303-304)"
  (assert-true (rubi::rubi-inverse-function-q '(asin x)))
  (assert-true (rubi::rubi-inverse-function-q '(acot (* 2 x))))
  (assert-true (rubi::rubi-inverse-function-q '(asinh x)))
  (assert-true (rubi::rubi-inverse-function-q '(log x)))
  ; sinh — гиперболическая, а не обратная: $InverseHyperbolicFunctions = ArcSinh… (IUF.m:265-266)
  (assert-true (not (rubi::rubi-inverse-function-q '(sinh x))))
  (assert-true (not (rubi::rubi-inverse-function-q '(sin x))))
  (assert-true (not (rubi::rubi-inverse-function-q 'x))))

(deftest "rubi-ch567/2: InverseFunctionFreeQ — рекурсия по аргументам (IUF.m:317-322)"
  ; обратная функция со свободным от x аргументом — свободна (до шага возвращалось #f)
  (assert-true (rubi::rubi-inverse-function-free-q '(asin a) 'x))
  ; а произведение с asin(x) — нет (до шага голова '*' давала True)
  (assert-true (not (rubi::rubi-inverse-function-free-q '(* x (asin x)) 'x)))
  (assert-true (not (rubi::rubi-inverse-function-free-q '(exp (* x (asin x))) 'x)))
  (assert-true (not (rubi::rubi-inverse-function-free-q '(asin (* a x)) 'x)))
  (assert-true (not (rubi::rubi-inverse-function-free-q '(integrate (sin x) x) 'x)))
  ; без обратных функций и без x — свободно
  (assert-true (rubi::rubi-inverse-function-free-q '(sin a) 'x))
  (assert-true (rubi::rubi-inverse-function-free-q '(^ (+ a (* b (sin x))) 2) 'x)))

(deftest "rubi-ch567/3: InverseFunctionOfLinear — g[a+b x] внутри выражения (IUF.m:6084-6092)"
  ; раньше заглушка (#f) — правила 5.x/6.x/7.x с этой утилитой отсеивались всегда
  (assert-equal '(asin (+ a (* b x)))
                (rubi::rubi-inverse-function-of-linear '(* x (asin (+ a (* b x)))) 'x))
  (assert-equal '(atan (* 2 x))
                (rubi::rubi-inverse-function-of-linear '(^ (atan (* 2 x)) 3) 'x))
  ; аргумент не линейный, выражение свободно от x, или x — сам аргумент: False
  (assert-true (not (rubi::rubi-inverse-function-of-linear '(atan (^ x 2)) 'x)))
  (assert-true (not (rubi::rubi-inverse-function-of-linear '(asin a) 'x)))
  (assert-true (not (rubi::rubi-inverse-function-of-linear 'x 'x))))

(deftest "rubi-ch567/4: FunctionOfInverseLinear — функция от отношения линейных (IUF.m:4234-4256)"
  ; QuotientOfLinearsQ требует b != 0 и d != 0 (IUF.m:1731), поэтому Drop[parts,2] — знаменатель (2 3)
  (assert-equal '(2 3) (rubi::rubi-function-of-inverse-linear '(/ (+ 1 x) (+ 2 (* 3 x))) 'x))
  ; свободный множитель и свободное слагаемое выносятся (IUF.m:1780/1784)
  (assert-equal '(2 3) (rubi::rubi-function-of-inverse-linear '(* a (/ (+ 1 x) (+ 2 (* 3 x)))) 'x))
  ; а x-зависимый множитель вне отношения линейных — уже False (x не функция от 1/(a+b x))
  (assert-true (not (rubi::rubi-function-of-inverse-linear '(* x (/ (+ 1 x) (+ 2 (* 3 x)))) 'x)))
  ; свободное от x выражение возвращается как накопленный список (Null), сам x — False
  (assert-equal 'null (rubi::rubi-function-of-inverse-linear 'a 'x))
  (assert-true (not (rubi::rubi-function-of-inverse-linear 'x 'x)))
  ; 1/(a+b x) — НЕ отношение линейных по QuotientOfLinearsQ (числитель — константа, b = 0): False
  (assert-true (not (rubi::rubi-function-of-inverse-linear '(/ 1 (+ a (* b x))) 'x)))
  (assert-true (not (rubi::rubi-function-of-inverse-linear '(/ 1 (^ x 2)) 'x))))


(deftest "rubi-ch567/5: EulerIntegrandQ — подстановка Эйлера (IUF.m:5017-5039)"
  ; было заглушкой: правила 9.3 #55-#57 отсеивались всегда, и в журнале глав 5-7 первым ложным
  ; конъюнктом шло rubi-euler-integrand-q
  ; 5017: (a x + b U^n)^p, n+1/2 целое, U — квадратичный трёхчлен, p < 0 и U не двучлен
  (assert-true (rubi::rubi-euler-integrand-q
                (simplify (math-read "(a*x + b*(1 + x + x^2)^(3/2))^(-1)")) 'x))
  ; 5022: V^m (a x + b U^n)^p при U = V
  (assert-true (rubi::rubi-euler-integrand-q
                (simplify (math-read "(x^2+x+1)^(-1)*(a*x + b*(x^2+x+1)^(3/2))^(-1)")) 'x))
  ; 5034: U^n V^p при p < 0 (целом), n+1/2 целом, оба основания квадратичны
  (assert-true (rubi::rubi-euler-integrand-q
                (simplify (math-read "(x^2 + 1)^(-1/2)*(x^2 + x + 2)^(-1)")) 'x))
  ; двучленное основание при рациональном p < 0 — уже не Эйлер (5019: Not[BinomialQ[U,x]])
  (assert-true (not (rubi::rubi-euler-integrand-q
                     (simplify (math-read "(a*x + b*(1 + x^2)^(3/2))^(-1)")) 'x)))
  ; не квадратичное основание и не тригонометрия
  (assert-true (not (rubi::rubi-euler-integrand-q
                     (simplify (math-read "(a*x + b*(x^2)^(3/2))^(-1)")) 'x)))
  (assert-true (not (rubi::rubi-euler-integrand-q (simplify (math-read "sin(x)")) 'x))))
