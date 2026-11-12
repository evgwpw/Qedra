; RUBI.RULE a-d: дефекты правил/генератора/утилит Rubi, из-за которых правило с подходящим образцом
; не срабатывало или падало (research/rubi/class/REPORT.md, «Найденные ошибки»). Источник семантики —
; Rubi 4.17.3.0 (commit 61e9c18); ссылки «файл:строка» в комментариях к случаям.
; Утилиты приватны; грузим их так же, как rubi-A грузит utils-a.
(load (string-append lib-dir "rubi/utils.lisp"))

; свой стенд: не трогаем rubi-test-setup из rubi.lisp (файлы тестов делят окружение)
(define (rubi-rule-setup rules)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #t)
  (for-each (lambda (r) (rubi::rubi-add-rule (car r) (cadr r) (nth r 2) (nth r 3)))
            (reverse rules))
  (rubi::rubi-build-index))

; --- a) Int[{u..},x] и PolynomialDivide (Rubi.m:477, IUF.m:3298-3310) ---

(deftest "rubi-rule/a: PolynomialDivide — сумма quo + rem/v, а не пара (IUF.m:3298)"
  ; Раньше (list quo rem): правило Int[PolynomialDivide[...],x] получало список и отказывало.
  ; Сверка значением: r(a=2,b=3,x=5/3) = x^4/(a+b x^2).
  (let* ((r (rubi::rubi-polynomial-divide (^ 'x 4) '(+ a (* b (^ x 2))) 'x))
         (v (eval-num (subst (list (list 'a 2) (list 'b 3) (list 'x 5/3)) r)))
         (want (eval-num '(/ (^ 5/3 4) (+ 2 (* 3 (^ 5/3 2)))))))
    (assert-true (< (abs (- v want)) 1e-9))
    (assert-true (not (equal? (car r) 'list)))))

(deftest "rubi-rule/a: Int списка — поэлементно (Rubi.m:477)"
  (rubi-rule-setup (list (list "x" 'x '() '(* 1/2 (^ (quote x) 2)))
                         (list "x2" '(^ x 2) '() '(* 1/3 (^ (quote x) 3)))))
  (assert-equal (rubi::rubi-int-list (list 'x (list '^ 'x 2)) 'x)
                (list '(* 1/2 (^ x 2)) '(* 1/3 (^ x 3)))))

(deftest "rubi-rule/a: Int списка — неизвестный элемент даёт unknown"
  (rubi-rule-setup (list (list "x" 'x '() '(* 1/2 (^ (quote x) 2)))))
  (assert-equal 'unknown
                (rubi::rubi-int-list (list 'x (list '/ 1 (list 'log 'x))) 'x)))

; --- b) порядок аргументов D[u,x] в правых частях (генератор -> rubi::rubi-diff) ---

(deftest "rubi-rule/b: rubi-diff принимает D[u,x] (u первым), обёртка меняет порядок"
  (assert-equal (simplify '(* 3 (^ x 2)))
                (simplify (rubi::rubi-diff '(* x (^ x 2)) 'x))))

(deftest "rubi-rule/b: в сгенерированных правилах D идёт в порядке Mathematica"
  ; было (rubi::rubi-diff (quote x) u) — после переписывания имён diff получал выражение вместо символа
  (let ((txt (read-text-file (string-append lib-dir "rubi/rules/9.2-2.body.lisp"))))
    (assert-true (string-contains? txt "(rubi::rubi-diff u (quote x))"))))

; --- c) PolyQ[u,x] с ветвью PolynomialQ[Together[u],x] (IUF.m:501-503) ---

(deftest "rubi-rule/c: PolyQ через Together — сократимая дробь многочлен"
  (assert-equal #t (rubi::rubi-poly-q '(/ (^ x 2) x) 'x))
  (assert-equal #t (rubi::rubi-poly-q '(/ (^ x 2) x) 'x 1))
  (assert-equal #f (rubi::rubi-poly-q '(/ 1 x) 'x)))

(deftest "rubi-rule/c: Subst с образцом не-символом (1.1.3.2 #112, IUF.m Subst)"
  ; Было: генератор считал второй аргумент Subst переменной x и подставлял x целиком —
  ; выражение портилось, ответ не проходил int-check. Стало: подстановка по образцу (u /. pat -> val).
  (assert-true (string-contains? (read-text-file (string-append lib-dir "rubi/rules/1.1.3.2.body.lisp"))
                                 "rubi-subst-pat"))
  (assert-equal '(+ a (* b (^ x 3/2)))
                (simplify (rubi::rubi-subst-pat '(+ a (* b (^ y 3/2))) 'y 'x))))

; --- d) Module без нулей, арность ExpandToSum, Sum с переменной цикла, PosQ ---

(deftest "rubi-rule/d: Module[{aa,cc}] не подставляет 0 — нет деления на ноль (1.2.2.3 #87)"
  (let ((txt (read-text-file (string-append lib-dir "rubi/rules/1.2.2.3.body.lisp"))))
    (assert-true (string-contains? txt "(let ((aa (quote aa)) (cc (quote cc)))"))))

(deftest "rubi-rule/d: ExpandToSum[u,v,x] — три аргумента (IUF.m:3329)"
  (assert-equal (simplify '(+ (* a u) (* b u (^ x 2))))
                (simplify (rubi::rubi-expand-to-sum 'u '(+ a (* b (^ x 2))) 'x))))

(deftest "rubi-rule/d: Sum с переменной цикла в вычисленной форме (1.1.3.7 #27, 1.1.3.8 #16)"
  ; генератор передаёт (list (quote ii) 0 3); раньше let получал (quote ii) как имя — «неверный формат bindings».
  ; Переменная цикла в теле — голый ii (как в перегенерированных правилах).
  (assert-equal (simplify (rubi::rubi-sum (^ 'x ii) (list 'ii 0 3)))
                (simplify '(+ 1 x (^ x 2) (^ x 3)))))

(deftest "rubi-rule/d: PosQ с TogetherSimplify и числовым значением (IUF.m:605)"
  (assert-equal #t (rubi::rubi-posq '(- (^ 2 1/2) 1)))
  (assert-equal #f (rubi::rubi-posq '(- 1 (^ 2 1/2)))))

; --- e) Subst по образцу-степени (IUF.m:5154-5176) ---

(deftest "rubi-rule/e: Subst[u,(a x)^n,v] меняет степени, а не сравнивает структуру"
  ; IUF.m:5160: u = (a x)^m, m/n целое -> v^(m/n). Раньше образец x^(1/2) не совпадал с x^(-1/2)
  ; и в ответе оставалась разложенная степень c^(1/2) x^(-1/2) вместо (c x^q)^(1/2).
  (assert-equal '(^ w -1) (rubi::rubi-subst-pat '(^ y -1/2) '(^ y 1/2) 'w))
  (assert-equal '(^ w 10) (rubi::rubi-subst-pat '(^ y 5) '(^ y 1/2) 'w))
  (assert-equal '(* 3 (^ w -1)) (rubi::rubi-subst-pat '(* 3 (^ y -1/2)) '(^ y 1/2) 'w))
  ; символьный образец — обычная подстановка
  (assert-equal (simplify '(+ a (* b (^ x 2))))
                (simplify (rubi::rubi-subst-pat '(+ a (* b (^ y 2))) 'y 'x))))

(deftest "rubi-rule/e: sqrt(a + b*sqrt(c/x)) — ответ в форме (c x^-1)^(1/2), верен и при c<0"
  ; 1.1.3.2 #112 (Subst[x^(1/k),...]) не должен разлагать Sqrt[c/x] на Sqrt[c]/Sqrt[x]:
  ; проверяем и форму ответа, и численно d/dx F - f при c > 0 (x > 0) и c < 0 (x < 0).
  ; Правила главы 1 грузит сам движок (rubi-ensure, ≈1,7 с).
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (let* ((f '(^ (+ a (* b (^ (* c (^ x -1)) 1/2))) 1/2)))
    (let ((ans (rubi-integrate f 'x)))
      (assert-true (not (equal? ans 'unknown)))
      (assert-true (string-contains? (format "~s" ans) "(^ (* c (^ x -1)) 1/2)"))
      (for-each
       (lambda (pr)
         (let* ((c (car pr)) (x (cadr pr))
                (s (lambda (u) (subst (list (list 'a 2) (list 'b 3) (list 'c c) (list 'x x)) u)))
                (d (simplify (list '- (s (integrate::int-diff 'x ans)) (s f))))
                (v (eval-num d)))
           (assert-true (< (abs v) 1e-9))))
       (list (list 4 13/10) (list -4 -13/10))))))

(deftest "rubi-rule/e: Together в PolyQ только при наличии деления"
  ; Порог: без деления Together не зовём (на больших суммах это сотни мс).
  (assert-equal #f (rubi::rubi-has-division? '(+ a (* b (^ x 3)) (* c (^ x 6)))))
  (assert-equal #t (rubi::rubi-has-division? '(* x (/ 1 (+ a (* b x))))))
  (assert-equal #t (rubi::rubi-poly-q '(/ (^ x 2) x) 'x)))

(deftest "rubi-rule: поддельный ответ отвергается int-check"
  (rubi-rule-setup (list (list "подделка" '(/ 1 x) '() '(^ (quote x) 2))))
  (assert-equal 'unknown (rubi-integrate '(/ 1 x) 'x)))
