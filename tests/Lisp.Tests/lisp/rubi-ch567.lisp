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

(deftest "rubi-ch567/6: DerivativeDivides — частное u/D[y,x], а не булево (IUF.m:7450-7462)"
  ; до RUBI.CH567.2 функция возвращала #t, и правила 9.3 #7-#24 умножали ответ на #t — int-check отвергал
  ; готовый ответ ((* poly #t), t_5_3_4/920); заодно был перепутан порядок аргументов diff (diff var expr)
  (assert-equal 1/2 (rubi::rubi-derivative-divides '(^ x 2) 'x 'x))
  ; y = a + b x: степень u на единицу меньше степени y — частное свободно от x
  (assert-equal (simplify '(/ 1 (* 2 b))) (rubi::rubi-derivative-divides '(^ (+ a (* b x)) 2) '(+ a (* b x)) 'x))
  ; y линейно по x (a_.*x) — подстановка не нужна, False (IUF.m:7452)
  (assert-true (not (rubi::rubi-derivative-divides 'x '(^ x 2) 'x)))
  (assert-true (not (rubi::rubi-derivative-divides '(* a x) '(^ x 2) 'x)))
  ; степень u не та (Exponent[u] != Exponent[y]-1), и D[y,x] не делит u
  (assert-true (not (rubi::rubi-derivative-divides '(^ x 2) 1 'x)))
  (assert-true (not (rubi::rubi-derivative-divides '(atan x) 'x 'x)))
  ; y не многочлен: EasyDQ[atan x] = True (голова-символ свободна от x, рекурсия в аргумент)
  (assert-equal 1 (rubi::rubi-derivative-divides '(atan x) '(/ 1 (+ 1 (^ x 2))) 'x))
  (assert-true (rubi::rubi-easy-dq '(atan x) 'x))
  (assert-true (not (rubi::rubi-easy-dq '(* (atan x) (sin x)) 'x)))
  (assert-true (rubi::rubi-easy-dq '(* a (^ (* b x) 2)) 'x))
  (assert-true (rubi::rubi-product-of-linear-powers-q '(* (^ (* a x) 2) (^ (+ b (* c x)) 3)) 'x))
  (assert-true (not (rubi::rubi-product-of-linear-powers-q '(* (atan x) x) 'x))))

(deftest "rubi-ch567/7: ответ 0 при ненулевом подынтегральном — вложенный отказ, а не ответ"
  ; -i/2*Int[u] + i/2*Int[u] при Int[u] = unknown сворачивается в 0 (правило 4.1.10 #13, t_6_1_1/38):
  ; такой «ответ» отвергался проверкой после полной работы поиска; теперь это вложенный отказ
  (assert-equal 'unknown (rubi-integrate (math-read "(c + d*x)^(3/2)*sinh(a + b*x)") 'x))
  ; а ответы, которые дают правила с DerivativeDivides, больше не содержат метки #t
  (let ((r (rubi-integrate (math-read "1/sqrt(a + b*asin(c*x))") 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r #t)))))

(deftest "rubi-ch567/8: I в записи Mathematica — мнимая единица (не параметр)"
  ; вход корпуса exp(-3*I*atan(a+b*x))/x^3: без перевода int-check считал I параметром (значение 1,7)
  ; и верный ответ отвергался (t_5_3_6/213)
  (assert-equal '(^ E (* 2 %i x)) (rubi::rubi-normalize-heads '(exp (* 2 I x))))
  (assert-equal '%i (rubi::rubi-normalize-heads 'I))
  ; I как параметр (значение 1,7) больше нигде не остаётся в нормализованном входе
  (assert-true (not (contains-sym? (rubi::rubi-normalize-heads '(exp (* 2 I x))) 'I))))


(deftest "rubi-ch567/9: SubstFor — замена образца v на x (IUF.m:5975-5980), 4-арг форма"
  ; RUBI.CH567.3: было наоборот (f с заменой x на u) и через `subst`, поэтому подстановка шла в обратную
  ; сторону, а при составном образце правило падало («подставлять можно только символы»). 4-арг форма
  ; SubstFor[w,v,u,x] = SimplifyIntegrand[w*SubstFor[v,u,x],x] (IUF.m:5976-5977) вообще была ошибкой
  ; арности — 104 места вызова в телах правил (4.7.5 #71/#72 и др.) не работали.
  ; Pq с заменой x^2 на x: x^4 = (x^2)^2 -> x^2 (Subst по степени, IUF.m:5159-5161)
  (assert-equal '(+ (^ x 2) x) (rubi::rubi-subst-for '(^ x 2) '(+ (^ x 4) (^ x 2)) 'x))
  (assert-equal '(^ x 2) (rubi::rubi-subst-for '(^ x 2) '(^ x 4) 'x))
  ; символьный образец и образец-степень с символьным показателем — точное совпадение узла
  (assert-equal '(+ a (* b u)) (rubi::rubi-subst-for 'x '(+ a (* b x)) 'u))
  (assert-equal '(+ a (* b u)) (rubi::rubi-subst-for '(^ x n) '(+ a (* b (^ x n))) 'u))
  ; 4 аргумента: множитель w уходит в произведение, результат упрощается
  (assert-equal (simplify '(+ (^ x 2) x)) (rubi::rubi-subst-for 1 '(^ x 2) '(+ (^ x 4) (^ x 2)) 'x))
  (assert-equal (simplify '(* 2 (+ c (* d x))))
                (rubi::rubi-subst-for 2 '(atan x) '(+ c (* d (atan x))) 'x)))

