; Шаги алгебраического, смешанного и параметрического путей интегрирования (ключевые шаги alg-/mx-/gn-/pc-, видны в brief):
; кривая и род, Эрмит, вычеты и дивизор, граница кручения, главность, сертификат, причины отказов;
; внутренние diff/simplify/int-check в журнал не пишутся (тихий расчёт alg-run, как в risch/driver.lisp).

(define (stp-text thunk level)
  (let ((r (capture-step-log thunk level 'ru)))
    (steps-text (cadr r) (caddr r) 'ru)))
(define (stp-lines s) (+ 1 (length (filter (lambda (c) (equal? c "\n")) (string->list s)))))
(define (stp-has? s sub) (string-contains? s sub))
(define (stp-rules thunk) (step-rules (cadr (capture-step-log thunk))))

(define stp-P '(+ (* 4 (^ x 3)) (* -15 (^ x 2)) (* 8 x) 16))
(define stp-tors7 (list '/ '(- 28 (* 5 x)) (list '* 'x (list '^ stp-P 1/2))))
(define stp-nonel (list '/ 1 (list '* 'x (list '^ stp-P 1/2))))

(deftest "шаги Риша: кручение 7 — brief показывает кривую, Эрмит, вычеты ±7, B = 7, главность и сертификат"
  (let ((s (stp-text (lambda () (integrate stp-tors7 'x)) 'brief)))
    (assert-true (stp-has? s "Кривая подынтегрального выражения"))
    (assert-true (stp-has? s "род кривой g = 1"))
    (assert-true (stp-has? s "Редукция Эрмита"))
    (assert-true (stp-has? s "вычеты: 7 в (x = 0, y = 4); -7 в (x = 0, y = -4)"))
    (assert-true (stp-has? s "сумма вычетов = 0"))
    (assert-true (stp-has? s "δ = Σ m·res·P"))
    (assert-true (stp-has? s "B = НОД = 7"))
    (assert-true (stp-has? s "Проверка главности"))
    (assert-true (stp-has? s "Сертификат ответа"))
    (assert-true (<= (stp-lines s) 15))
    (assert-true (not (stp-has? s "Дифференцирование")))
    (assert-true (not (stp-has? s "Упрощение результата")))))

(deftest "шаги Риша: кручение 7 — полное дерево без шума diff/simplify, ключевые шаги в порядке алгоритма"
  (let ((rs (stp-rules (lambda () (integrate stp-tors7 'x)))))
    (assert-equal rs '(integration simplify-integrand alg-integration alg-curve alg-hermite alg-residues alg-torsion-bound
                       alg-principal alg-certificate))))

(deftest "шаги Риша: неэлементарный dx/(x√P) — причина отказа, B = 7 и n = 7 в шагах brief"
  (let ((s (stp-text (lambda () (integrate stp-nonel 'x)) 'brief)))
    (assert-true (stp-has? s "Неэлементарность доказана"))
    (assert-true (stp-has? s "B = НОД = 7"))
    (assert-true (stp-has? s "n·δ главный при n = 7"))
    (assert-true (stp-has? s "H − (1/28)·u′/u = (5/28)·dx/y"))
    (assert-true (stp-has? s "дифференциал 1-го рода (голоморфный во всех точках, ненулевой)"))
    (assert-true (<= (stp-lines s) 15))
    (assert-true (not (stp-has? s "Дифференцирование")))))

(deftest "шаги Риша: проверяемость — R(t) разложен, m, точки над F_p, n | B, L(−n·δ), результат не изменился"
  (let ((s (stp-text (lambda () (integrate stp-nonel 'x)) 'brief))
        (off (integrate stp-nonel 'x)))
    (assert-true (stp-has? s "R(t) = 743269860376576·t^6·(t^2 − 1/16)"))
    (assert-true (stp-has? s "m = 4 (наименьшее натуральное, при котором все m·res целые)"))
    (assert-true (stp-has? s "p = 3: #E(F_p) = 7 (аффинных 6: (0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2); на ∞: 1)"))
    (assert-true (stp-has? s "n | B = 7"))
    (assert-true (stp-has? s "L(−n·δ) = {u : div u ≥ n·δ}"))
    (assert-true (<= (stp-lines s) 16))
    (assert-equal off (car (capture-step-log (lambda () (integrate stp-nonel 'x)))))))

(deftest "шаги Риша: кручение 7 — R(t) = c·t^6·(t^2 − 49), результат тот же"
  (let ((s (stp-text (lambda () (integrate stp-tors7 'x)) 'brief)))
    (assert-true (stp-has? s "·t^6·(t^2 − 49)"))
    (assert-true (stp-has? s "m = 1 (наименьшее натуральное"))
    (assert-true (<= (stp-lines s) 16))
    (assert-equal (integrate stp-tors7 'x) (car (capture-step-log (lambda () (integrate stp-tors7 'x)))))))

(deftest "шаги Риша: R5.1 — над ℚ(√5): R(t) с моническим множителем, p инертно/расщеплено, #J, B"
  (let ((s (stp-text (lambda () (integrate '(/ 1 (* x (^ (+ (^ x 3) (* 3 x) 5) 1/2))) 'x)) 'brief)))
    (assert-true (stp-has? s "R(t) = 383180625·t^6·(t^2 − 1/5) с корнями"))
    (assert-true (not (stp-has? s "1/5(")))
    (assert-true (stp-has? s "p = 7 (инертно, поле вычетов F_(p²)): #J(F_(p²)) = L_p(1)·L_p(−1) = 63"))
    (assert-true (stp-has? s "p = 11 (расщеплено, поле вычетов F_p): #J(F_p) = L_p(1) = 9"))
    (assert-true (stp-has? s "B = НОД = 9"))))

(deftest "шаги Риша: ST.1c —сертификат закона сложения на E в шаге главности (порядок 7, порядок 1, не кручение)"
  (let ((s7 (stp-text (lambda () (integrate stp-nonel 'x)) 'brief))
        (s1 (stp-text (lambda () (integrate stp-tors7 'x)) 'brief))
        (sn (stp-text (lambda () (integrate '(/ 1 (* x (^ (+ (^ x 3) x 1) 1/2))) 'x)) 'brief)))
    (assert-true (stp-has? s7 "сертификат (закон сложения на E): T = (4, -8); 2T = (2, -2); 3T = (0, -4); 4T = (0, 4); 5T = (2, 2); 6T = (4, 8); 7T = O — порядок δ равен 7"))
    (assert-true (stp-has? s1 "сертификат (закон сложения на E): T = O — порядок δ равен 1"))
    (assert-true (stp-has? sn "сертификат (закон сложения на E): T = (1/4, -9/8); kT ≠ O для всех k | B = 1 — δ не кручение"))
    (assert-equal (integrate stp-nonel 'x) (car (capture-step-log (lambda () (integrate stp-nonel 'x)))))
    (assert-true (not (stp-has? s7 "расхождение сертификата")))))

(deftest "шаги Риша: отказ по теореме Чебышёва — шаг с условием на p, (m+1)/n"
  (let ((s (stp-text (lambda () (integrate '(sqrt (+ 1 (^ x 4))) 'x)) 'brief)))
    (assert-true (stp-has? s "Неэлементарность доказана"))
    (assert-true (stp-has? s "теорема Чебышёва"))
    (assert-true (stp-has? s "(m+1)/n = 1/4"))))

(deftest "шаги Риша: смешанный ∫√(eˣ+1) — подстановка t = exp(x), интеграл по t, обратная подстановка"
  (let ((s (stp-text (lambda () (integrate '(sqrt (+ (exp x) 1)) 'x)) 'brief)))
    (assert-true (stp-has? s "Подстановка t = θ(x)"))
    (assert-true (stp-has? s "t = exp(x)"))
    (assert-true (stp-has? s "Интеграл по t"))
    (assert-true (stp-has? s "Обратная подстановка"))
    (assert-true (<= (stp-lines s) 15))
    (assert-true (not (stp-has? s "Дифференцирование")))
    (assert-true (not (stp-has? s "Базис Грёбнера")))))

(deftest "шаги Риша: смешанный отказ — перенос вердикта на исходный интеграл"
  (let ((s (stp-text (lambda () (integrate '(/ (sqrt (+ (exp x) 1)) x) 'x)) 'brief)))
    (assert-true (stp-has? s "Рационализация кривой рода 0"))
    (assert-true (stp-has? s "Перенос отказа на исходный интеграл"))
    (assert-true (stp-has? s "Розенлихта"))
    (assert-true (<= (stp-lines s) 15))))

(deftest "шаги Риша: параметр — разбор случаев, по шагу на каждое условие ветви"
  (let ((s (stp-text (lambda () (integrate '(/ 1 (+ (^ x 2) a)) 'x)) 'brief)))
    (assert-true (stp-has? s "Решающее выражение"))
    (assert-true (stp-has? s "Случай по знаку или нулю параметра: a > 0"))
    (assert-true (stp-has? s "Случай по знаку или нулю параметра: a < 0"))
    (assert-true (stp-has? s "Случай по знаку или нулю параметра: a = 0"))
    (assert-true (stp-has? s "Сертификат ветвей"))
    (assert-true (<= (stp-lines s) 15))
    (assert-true (not (stp-has? s "Дифференцирование")))))

(deftest "шаги Риша: род 0 — параметризация кривой и интеграл по параметру"
  (let ((rs (stp-rules (lambda () (integrate '(/ 1 (+ x (sqrt (+ (^ x 2) 1)))) 'x)))))
    (assert-true (member? 'gn-integration rs))
    (assert-true (member? 'gn-parametrization rs))
    (assert-true (member? 'gn-rational-integral rs))
    (assert-true (member? 'alg-certificate rs))))

(deftest "шаги Риша: журнал выключен — ответ тот же, шагов нет"
  (let ((off (integrate stp-tors7 'x))
        (on (car (capture-step-log (lambda () (integrate stp-tors7 'x))))))
    (assert-equal off on)
    (assert-equal (step-log) '())))
