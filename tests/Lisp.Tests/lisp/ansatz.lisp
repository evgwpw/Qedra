; INT.ANSATZ.1: интегрирование анзацем (lib/integrate/ansatz.lisp) — ответ ищется как многочлен от кирпичиков
; подынтегрального с неизвестными коэффициентами; каждый ответ проходит int-check; нет решения — #f.

(define (az-solved f)
  (let ((F (int-ansatz f 'x)))
    (assert-true F)
    (assert-true (int-check F f 'x))
    F))

(deftest "ansatz: x·eˣ, x²·log x, x·e^(x²) — многочлен от кирпичиков"
  (az-solved '(* x (exp x)))
  (az-solved '(* (^ x 2) (log x)))
  (assert-equal (az-solved '(* x (exp (^ x 2)))) '(* 1/2 (exp (^ x 2)))))

(deftest "ansatz: (1+2x²)·e^(x²) = x·e^(x²)"
  (assert-equal (az-solved '(* (+ 1 (* 2 (^ x 2))) (exp (^ x 2)))) '(* x (exp (^ x 2)))))

(deftest "ansatz: eˣ·sin x и e^(2x)·cos x — синус и косинус как кирпичики на окружности"
  (az-solved '(* (exp x) (sin x)))
  (az-solved '(* (exp (* 2 x)) (cos x))))

(deftest "ansatz: логарифмическая часть — 1/(x log x) = log log x, e^x/(e^(2x)-1)"
  (assert-equal (az-solved '(/ 1 (* x (log x)))) '(log (log x)))
  (az-solved '(/ (exp x) (+ (exp (* 2 x)) -1))))

(deftest "ansatz: спецфункции — erf x и atan x"
  (let ((F (az-solved '(erf x))))
    (assert-true (contains-sym? F 'erf)))
  (az-solved '(atan x))
  (az-solved '(* x (atan x))))

(deftest "ansatz: корень √(x+1)·x"
  (az-solved '(* x (^ (+ x 1) 1/2))))

(deftest "ansatz: параметр — x·e^(ax) = (x/a − 1/a²)·e^(ax)"
  (az-solved '(* x (exp (* a x)))))

(deftest "ansatz: неэлементарные интегралы — честный отказ #f"
  (for-each (lambda (f) (assert-equal (int-ansatz f 'x 2) #f))
            '((/ (exp x) x) (exp (* x (exp x))) (/ (sin x) x) (/ 1 (log x)) (/ (log x) (+ 1 x)))))

; INT.ANSATZ.3: e^(x²) берёт комплексный (гауссов) анзац через erfi
(deftest "ansatz: e^(x²) = (√π/2)·erfi x — гауссов анзац"
  (assert-equal (az-solved '(exp (^ x 2))) '(* 1/2 (^ pi 1/2) (erfi x))))

(deftest "ansatz: весовой фильтр сокращает число неизвестных (параметры — вес из однородности f)"
  (az-solved '(* x (exp (* a x))))
  (let ((st (car (int-ansatz-stats))))
    ; (d без-фильтра с-фильтром фильтр-включён?)
    (assert-true (nth st 3))
    (assert-true (< (* 3 (nth st 2)) (nth st 1)))))

(deftest "ansatz: подделка отвергается int-check (ответ с неверной производной не возвращается)"
  (int-ansatz '(* x (exp x)) 'x)
  ; одно неизвестное x·eˣ с коэффициентом 1: F′ = (x+1)·eˣ ≠ x·eˣ
  (assert-equal (integrate::an-assemble '(* x (exp x)) '(* x (exp x)) '((mono 1 (1) () 0)) '(1) '() '()) #f)
  (assert-equal (int-check '(* x (exp x)) '(* x (exp x)) 'x) #f))

(deftest "ansatz: без бюджета на большие системы и без поддержки — #f, не ошибка"
  ; показатель с x, функция от параметров, комплексная единица
  (assert-equal (int-ansatz '(^ 2 x) 'x) #f)
  (assert-equal (int-ansatz '(^ x (* n x)) 'x) #f)
  (assert-equal (int-ansatz '(exp a) 'x) #f)
  (assert-equal (int-ansatz '(* %i x) 'x) #f))

(deftest "ansatz: without-ansatz отключает ступень и восстанавливает флаг"
  (without-ansatz (lambda () (assert-true (list? (integrate '(* x (exp x)) 'x)))))
  (assert-true (int-ansatz '(* x (exp x)) 'x)))

; INT.ANSATZ.2: символьный показатель (кирпичик θ = u^(q·n), θ′ = q·n·u′·θ/u; в коэффициентах знаменатели (q·n+k+j))
(deftest "ansatz: xⁿ, (a+bx)ⁿ, x^(2n+1) — первообразная с множителем 1/(n+1)"
  (assert-equal (az-solved '(^ x n)) '(* (^ x (+ 1 n)) (^ (+ 1 n) -1)))
  (az-solved '(^ (+ a (* b x)) n))
  (az-solved '(* x (^ (+ a (* b x)) n)))
  (az-solved '(^ x (+ 1 (* 2 n))))
  (az-solved '(^ (+ a (* b x)) (+ n -3))))

(deftest "ansatz: x^(n-1)·(1+xⁿ)² = (1+xⁿ)³/(3n); xⁿ·log x — знаменатель (n+1)²"
  (az-solved '(* (^ x (+ n -1)) (^ (+ 1 (^ x n)) 2)))
  (az-solved '(* (^ x n) (log x))))

(deftest "ansatz: условие n ≠ -1 записывается в канал условий"
  (let ((r (capture-conditions (lambda () (int-ansatz '(^ x n) 'x)))))
    (assert-true (car r))
    (assert-true (assoc '(/= (+ 1 n) 0) (cadr r)))))

(deftest "ansatz: неэлементарное с символьным показателем — #f (xⁿ·eˣ — неполная гамма)"
  (assert-equal (int-ansatz '(* (^ x n) (exp x)) 'x 2) #f)
  (assert-equal (int-ansatz '(/ (^ x n) (+ 1 x)) 'x 2) #f))

(deftest "ansatz: подъём констант — (lift …) в статистике, ответ проверен; по умолчанию выключен"
  (assert-equal (int-ansatz '(/ 1 (+ (^ x 4) 1)) 'x 2 3) #f)
  (assert-true (not (any? (lambda (s) (and (pair? s) (equal? (car s) 'lift))) (int-ansatz-stats))))
  (int-ansatz '(/ 1 (+ (^ x 4) 1)) 'x 2 3 #t)
  (assert-true (any? (lambda (s) (and (pair? s) (equal? (car s) 'lift))) (int-ansatz-stats)))
  (let ((F (int-ansatz '(* (exp x) (sin x)) 'x 3 3 #t)))
    (assert-true (int-check F '(* (exp x) (sin x)) 'x))))

; INT.ANSATZ.3: радикалы общего вида (подкоренное — многочлен от x и кирпичиков; точки по модулю P) и комплексный анзац ℚ(i)
(deftest "ansatz: квадратичное подкоренное — √(x²+1), x/√(x²+2x+3), 1/√(x²+1) с логарифмом (s + линейное)"
  (assert-true (contains-sym? (az-solved '(^ (+ 1 (^ x 2)) 1/2)) 'log))
  (az-solved '(* x (^ (+ 3 (* 2 x) (^ x 2)) -1/2)))
  (assert-equal (az-solved '(^ (+ 1 (^ x 2)) -1/2)) '(log (+ x (^ (+ 1 (^ x 2)) 1/2)))))

(deftest "ansatz: log(s ± r) от множителей знаменателя — √(1+eˣ), √(x²+1)/x, 1/(x√(x+1))"
  (az-solved '(^ (+ 1 (exp x)) 1/2))
  (az-solved '(/ (^ (+ 1 (^ x 2)) 1/2) x))
  (az-solved '(/ 1 (* x (^ (+ x 1) 1/2)))))

(deftest "ansatz: радикал от тригонометрии и экспоненты — sin x/√(cos x), cos(x)·√(1+sin x), форма sqrt"
  (az-solved '(/ (sin x) (^ (cos x) 1/2)))
  (assert-true (int-ansatz '(/ (sin x) (sqrt (cos x))) 'x))
  (az-solved '(* (cos x) (^ (+ 1 (sin x)) 1/2))))

(deftest "ansatz: несколько радикалов — √(x+√(x²-4)) (вложенный) и x·√(1+x)·√(1-x)"
  (az-solved '(^ (+ x (* -1 (^ (+ -4 (^ x 2)) 1/2))) 1/2))
  (az-solved '(* x (^ (+ 1 x) 1/2) (^ (+ 1 (* -1 x)) 1/2))))

(deftest "ansatz: подделка — √(x²+1) без логарифма не принимается int-check; корень 5-й степени — #f, не ошибка"
  (assert-true (not (int-check '(* 1/2 x (^ (+ 1 (^ x 2)) 1/2)) '(^ (+ 1 (^ x 2)) 1/2) 'x)))
  (assert-equal (int-ansatz '(^ (+ 1 (^ x 2)) 1/5) 'x 2) #f))

(deftest "ansatz: гауссовы показатели — e^(x²+x), x³e^(x²+x), x²e^(−x²) через erfi/erf"
  (let ((F (az-solved '(exp (+ (^ x 2) x)))))
    (assert-true (contains-sym? F 'erfi)))
  (az-solved '(* (^ x 3) (exp (+ (^ x 2) x))))
  (assert-true (contains-sym? (az-solved '(* (^ x 2) (exp (* -1 (^ x 2))))) 'erf)))

(deftest "ansatz: комплексный анзац ℚ(i) — e^(x²)·sin x, e^(−x²)·cos 2x: ответ с сопряжённой парой, вещественный"
  (let ((F (az-solved '(* (exp (^ x 2)) (sin x)))))
    (assert-true (contains-sym? F '%i))
    ; сопряжённость: замена i -> -i даёт то же выражение
    (assert-equal (simplify (replace-expr F '%i '(* -1 %i))) F))
  (az-solved '(* (exp (* -1 (^ x 2))) (cos (* 2 x))))
  (az-solved '(* (exp (* 2 (^ x 2))) (sin (* 3 x)))))

; INT.ANSATZ.4: скорость отказа
(define (az-stat-has? key)
  (any? (lambda (s) (and (pair? s) (equal? (car s) key))) (int-ansatz-stats)))

(deftest "ansatz: быстрый отказ — несовместность по первым строкам, степень без новых неизвестных пропускается, профиль этапов"
  ; exp(x³): неизвестных 6, 10, 14 — несовместность видна уже на rank + 1 строках (не nu + 5)
  (assert-equal (int-ansatz '(exp (^ x 3)) 'x) #f)
  (assert-true (az-stat-has? 'inconsistent))
  (assert-true (az-stat-has? 'prof))
  ; 1/(1+x⁵): кирпичиков нет — набор неизвестных не растёт с d, решается одна степень
  (assert-equal (int-ansatz '(^ (+ 1 (^ x 5)) -1) 'x) #f)
  (assert-equal (length (filter (lambda (s) (and (pair? s) (integer? (car s)))) (int-ansatz-stats))) 1))

(deftest "ansatz: решение с зависимыми строками — ранг меньше числа неизвестных (x·eˣ, sin/cos на окружности)"
  (az-solved '(* x (exp x)))
  (assert-true (az-stat-has? 'pts))
  (az-solved '(* (exp x) (^ (sin x) 2)))
  (az-solved '(* (^ (cos x) 2) (sin x))))

; INT.ANSATZ.5: параметры в гауссовых показателях
(deftest "ansatz: e^(−a x²)·cos(b x) с параметрами a, b — erf с комплексным сдвигом, ответ вещественный (сопряжённая пара)"
  (let ((F (az-solved '(* (exp (* -1 a (^ x 2))) (cos (* b x))))))
    (assert-true (contains-sym? F 'erf))
    (assert-equal (simplify (replace-expr F '%i '(* -1 %i))) F))
  (assert-true (contains-sym? (az-solved '(* (exp (* -1 a (^ x 2))) (sin (* b x)))) '%i)))

(deftest "ansatz: x^k·e^(a x²+b x+c), e^(a x²)·sinh(b x), e^(x²)·cos(a+b x) с параметрами"
  (az-solved '(* x (exp (+ (* a (^ x 2)) (* b x)))))
  (az-solved '(* (^ x 3) (exp (+ a (* b x) (* -1 c (^ x 2))))))
  (az-solved '(* (exp (* a (^ x 2))) (sinh (* b x))))
  (let ((F (az-solved '(* (exp (^ x 2)) (cos (+ a (* b x)))))))
    (assert-true (contains-sym? F 'erfi))))

(deftest "ansatz: параметрический гауссов — знак a известен (a = 2 > 0): erfi; неизвестен: erf(√(−a)·…) + условие a ≠ 0"
  (assert-true (contains-sym? (az-solved '(* (exp (* 2 (^ x 2))) (cos (* b x)))) 'erfi))
  (let ((F (az-solved '(exp (* a (^ x 2))))))
    (assert-true (contains-sym? F 'erf))
    (assert-true (not (contains-sym? F 'erfi)))))

(deftest "ansatz: подделка — гауссов ответ без множителя ½ или с неверным знаком сдвига не принимается int-check"
  (assert-true (not (int-check '(* (^ pi 1/2) (^ a -1/2) (erf (* (^ a 1/2) x))) '(exp (* -1 a (^ x 2))) 'x)))
  (assert-true (not (int-check '(* 1/2 (^ pi 1/2) (^ a -1/2) (erf (* (^ a 1/2) (+ x 1)))) '(exp (* -1 a (^ x 2))) 'x)))
  (assert-true (int-check '(* 1/2 (^ pi 1/2) (^ a -1/2) (erf (* (^ a 1/2) x))) '(exp (* -1 a (^ x 2))) 'x)))

; INT.ANSATZ.5: «тень» — порядок полюса ответа в нулях знаменателя
(define (az-nu)   ; число неизвестных при d = 1
  (let ((s (car (filter (lambda (s) (and (pair? s) (equal? (car s) 1))) (int-ansatz-stats))))) (nth s 2)))

(deftest "ansatz: тень — знаменатель (x+1)³ даёт полюс ответа ≤ 2: неизвестных меньше, ответ тот же"
  (let* ((f '(* (exp x) (+ (^ x 2) (* 2 x) -1) (^ (+ x 1) -3)))
         (F1 (az-solved f)) (nu1 (az-nu)) (sh (az-stat-has? 'shadow))
         (old integrate::int-ansatz-shadow))
    (set! integrate::int-ansatz-shadow #f)
    (let ((F0 (unwind-protect (az-solved f) (set! integrate::int-ansatz-shadow old))))
      (assert-true sh)
      (assert-true (< nu1 (az-nu)))
      (assert-true (equal? (simplify (together (list '+ F1 (list '* -1 F0)))) 0)))))

(deftest "ansatz: тень не трогает полюс 2-го порядка под логарифмом — log x/x² и (x cos x − sin x)/x² решаются"
  (az-solved '(* (log x) (^ x -2)))
  (az-solved '(* (+ (* x (cos x)) (* -1 (sin x))) (^ x -2)))
  ; произведение (1 + 1/x)/x² — полюс порядка 3 (не max множителей = 2): ответ −1/x − 1/(2x²) должен находиться
  (az-solved '(* (+ 1 (^ x -1)) (^ x -2))))

; INT.ANSATZ.6: ответы анзаца доходят до integrate; Lambert W; √b как константа
(define (az-full f)   ; integrate даёт полный ответ (без невычисленных остатков), проверенный int-check
  (let ((F (integrate f 'x)))
    (assert-true (not (integrate::int-has-integrate? F)))
    (assert-true (int-check F f 'x))
    F))

(deftest "ansatz/6: integrate берёт гауссовы ответы анзаца (были невычисленным интегралом или остатком ∫e^(bx−cx²))"
  (assert-true (contains-sym? (az-full '(* (exp (* -1 a (^ x 2))) (cos (* b x)))) 'erf))
  ; INT.SFREAL: erf с мнимым аргументом (−a)^(1/2)·x записывается как erfi(√a·x)
  (let ((F (az-full '(* (exp (* a (^ x 2))) (sinh (* b x))))))
    (assert-true (or (contains-sym? F 'erf) (contains-sym? F 'erfi))))
  (assert-true (contains-sym? (az-full '(* (^ x 3) (exp (+ a (* b x) (* -1 c (^ x 2)))))) 'erf)))

(deftest "ansatz/6: параметр под корнем — x·e^(−a x²+√b·x)"
  (let ((F (az-full '(* x (exp (+ (* -1 a (^ x 2)) (* (^ b 1/2) x)))))))
    (assert-true (contains-sym? F 'erf))))

(deftest "ansatz/6: после доказанной неэлементарности берётся только ответ в спецфункциях (условие risch-nonelementary снято)"
  (conditions-clear)
  (let ((F (integrate '(exp (+ (* -1 a (^ x 2)) (* b x))) 'x)))
    (assert-true (contains-sym? F 'erf))
    (assert-true (not (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary))) (conditions))))))

(deftest "ansatz/6: Lambert W как кирпичик — ∫W(x), ∫W(x)², ∫W(x)/x, ∫sin W(x)"
  (az-solved '(lambert_w x))
  (az-solved '(^ (lambert_w x) 2))
  (az-solved '(* (lambert_w x) (^ x -1)))
  (az-solved '(sin (lambert_w x)))
  (az-full '(lambert_w x)))

(deftest "ansatz/6: пример Райта — ω = W(eˣ), ответ log(x+ω) + sin ω"
  (let* ((w '(lambert_w (exp x)))
         (f (simplify (list '* (list '+ 1 (list '* w (list '+ 2 (list '* (list 'cos w) (list '+ 'x w)))))
                            (list '^ (list '* (list '+ 1 w) (list '+ 'x w)) -1))))
         (F (az-solved f)))
    (assert-true (contains-sym? F 'lambert_w))
    (assert-true (contains-sym? F 'sin))))

(deftest "ansatz/6: рациональная часть ответа — одна дробь (pmint)"
  (let ((F (az-solved (math "(x^7-24x^4-4x^2+8x-8)/(x^8+6x^6+12x^4+8x^2)"))))
    (assert-true (< (string-length (to-string F)) 130))))

(deftest "ansatz: ветвь при нормализации — √(x−1)·√(1/(x−1)) = −1 при x < 1, ложного ответа нет"
  (let* ((f (math "sqrt(x-1)*sqrt(1/(x-1))")) (F (int-ansatz f 'x)) (G (integrate f 'x)))
    (assert-true (or (not F) (int-check F f 'x)))
    (assert-true (or (contains-sym? G 'integrate) (int-check G f 'x)))))

(deftest "ansatz/6: примеры pmint через integrate"
  (az-full (math "(1+x+x*exp(x))*(x+log(x)+exp(x)-1)/((x+log(x)+exp(x))^2*x)"))
  (az-full (math "exp(-x^2)*erf(x)/(erf(x)^3-erf(x)^2-erf(x)+1)"))
  (az-full (math "(x^7-24x^4-4x^2+8x-8)/(x^8+6x^6+12x^4+8x^2)")))

; ---------- INT.ANSATZ.8: строгая часть метода Блейка (integrate/ansatz-cert.lisp) ----------
(define (c8-status f) (car (integrate::ce-hermite f 'x)))
(define (c8-ne-condition? f)
  (conditions-clear)
  (integrate f 'x)
  (any? (lambda (c) (and (pair? (car c)) (equal? (car (car c)) 'risch-nonelementary))) (conditions)))

(deftest "ansatz/8: эрмитова редукция — ответ B·√q без логарифмов (x²√(1+x³), x³/√(1+x⁴), 1/(x²√(1+x³)))"
  (for-each (lambda (f)
              (assert-equal (c8-status f) 'elementary)
              (let ((F (int-ansatz-hermite f 'x)))
                (assert-true F)
                (assert-true (int-check F f 'x))))
            (list '(* (^ x 2) (sqrt (+ 1 (^ x 3))))
                  '(/ (^ x 3) (sqrt (+ 1 (^ x 4))))
                  '(/ (^ x 2) (sqrt (+ 1 (^ x 3))))
                  (simplify (diff 'x '(* (/ 1 (+ x 3)) (sqrt (+ 3 (* 3 x) (^ x 2) (^ x 3))))))
                  (simplify (diff 'x '(* (/ (+ 1 x) (^ (+ x 2) 2)) (sqrt (+ 1 x (* 2 (^ x 4))))))))))

(deftest "ansatz/8: сертификат — первый, второй род и кратные полюсы над эллиптической/гиперэллиптической кривой"
  (for-each (lambda (f) (assert-equal (c8-status f) 'nonelementary))
            (list '(sqrt (+ 1 (^ x 3)))
                  '(/ 1 (sqrt (+ 1 (^ x 3))))
                  '(/ x (sqrt (+ 1 (^ x 3))))
                  '(sqrt (+ 1 (^ x 4)))
                  '(/ 1 (sqrt (+ 1 x (^ x 5))))
                  '(/ 1 (^ (+ 1 (^ x 3)) 3/2)))))

(deftest "ansatz/8: нет сертификата при ненулевом вычете (простой полюс, ∞) и вне класса"
  (for-each (lambda (f) (assert-true (not (equal? (c8-status f) 'nonelementary))))
            (list '(/ 1 (* (+ x 2) (sqrt (+ 1 x (^ x 5)))))       ; вычет в x = −2
                  '(/ (+ x 1) (* (^ x 2) (sqrt (+ 1 (^ x 3)))))   ; вычет в 0
                  '(sqrt (+ 1 x (^ x 4)))                          ; вычет на ∞ (x² + 1/(2x) + …)
                  '(/ 1 (sqrt (+ 1 (^ x 2))))                      ; род 0: asinh
                  '(+ (sqrt (+ 1 (^ x 3))) 1)                      ; не S·√q
                  '(* (exp x) (sqrt (+ 1 (^ x 3))))
                  '(* (sqrt (+ 1 (^ x 3))) a))))

(deftest "ansatz/8: условие risch-nonelementary от сертификата — в integrate; у элементарных его нет"
  (assert-true (c8-ne-condition? '(sqrt (+ 1 x (^ x 5)))))
  ; сертификат только от эрмитовой редукции (алгебраическая стратегия такие формы не доказывает): y⁻³ над кривой рода 2
  (assert-true (c8-ne-condition? '(* (/ 2 (^ (+ 3 (* 3 x) (* -1 (^ x 2)) (^ x 5) (^ x 6)) 2)) (sqrt (+ 3 (* 3 x) (* -1 (^ x 2)) (^ x 5) (^ x 6))))))
  (assert-true (c8-ne-condition? '(* (/ (+ -1 x (* 2 (^ x 2))) (^ (+ -1 x (^ x 2) (^ x 4)) 2)) (sqrt (+ -1 x (^ x 2) (^ x 4))))))
  (assert-true (not (c8-ne-condition? '(* (^ x 2) (sqrt (+ 1 (^ x 3)))))))
  (assert-true (not (c8-ne-condition? '(/ (^ x 3) (sqrt (+ 1 (^ x 4))))))))

(deftest "ansatz/8: подделки — случайные B·√q: после diff всегда «элементарно», сертификата нет"
  (let ((seed 3))
    (let loop ((i 0))
      (if (< i 12)
          (let* ((rnd (lambda (n) (begin (set! seed (modulo (+ (* seed 1103515245) 12345) 2147483648)) (modulo (quotient seed 65536) n))))
                 (q (simplify (list '+ 1 (list '* (+ 1 (rnd 3)) 'x) (list '^ 'x (+ 3 (rnd 4))))))
                 (B (case (rnd 3)
                      ((0) (list '+ 1 (list '* (+ 1 (rnd 3)) 'x)))
                      ((1) (list '/ 1 (list '+ 'x (+ 2 (rnd 3)))))
                      (else (list '/ (list '+ 1 'x) (list '^ 'x 2)))))
                 (f (simplify (diff 'x (list '* B (list 'sqrt q))))))
            (assert-true (not (equal? (c8-status f) 'nonelementary)))
            (assert-equal (c8-status f) 'elementary)
            (loop (+ i 1)))))))
