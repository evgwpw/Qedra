; units.lisp — тесты шага DIM.1: единицы, перевод, проверка размерности.

(deftest "dim1: перевод 1 км/ч = 5/18 м/с точно"
  (assert-equal (quantity-value (convert (quantity 1 '(/ km h)) '(/ m s))) 5/18))

(deftest "dim1: эВ, атм, миля, кВт·ч, кал — точные множители"
  (assert-equal (unit-factor 'eV) 1602176634/10000000000000000000000000000)
  (assert-equal (quantity-value (convert (quantity 1 'eV) 'J)) 1602176634/10000000000000000000000000000)
  (assert-equal (quantity-value (convert (quantity 1 'atm) 'Pa)) 101325)
  (assert-equal (quantity-value (convert (quantity 1 'mile) 'm)) 1609344/1000)
  (assert-equal (quantity-value (convert (quantity 1 '(* kW h)) 'J)) 3600000)
  (assert-equal (quantity-value (convert (quantity 1 'cal) 'J)) 4184/1000))

(deftest "dim1: приставки и масса"
  (assert-equal (unit-factor 'kg) 1)
  (assert-equal (unit-factor 'mg) 1/1000000)
  (assert-equal (unit-factor 'μm) 1/1000000)
  (assert-equal (unit-factor 'um) 1/1000000)
  (assert-equal (unit-factor 'hPa) 100)
  (assert-equal (unit-factor 'mL) 1/1000000)
  (assert-equal (unit-factor 'min) 60))

(deftest "dim1: производные единицы — размерности"
  (assert-equal (unit-dimension 'N) '(1 1 -2 0 0 0 0))
  (assert-equal (unit-dimension 'J) (unit-dimension '(* N m)))
  (assert-equal (unit-dimension 'W) (unit-dimension '(/ J s)))
  (assert-equal (unit-dimension 'Pa) (unit-dimension '(/ N (^ m 2))))
  (assert-equal (unit-dimension 'Ω) (unit-dimension '(/ V A)))
  (assert-equal (unit-dimension 'T) (unit-dimension '(/ Wb (^ m 2))))
  (assert-equal (unit-dimension 'N) (unit-dimension '(* kg m (^ s -2)))))

(deftest "dim1: dimension->string и same-dimension?"
  (assert-equal (dimension->string (unit-dimension 'J)) "L^2 M T^-2")
  (assert-equal (dimension->string (unit-dimension '(^ m 1/2))) "L^1/2")
  (assert-equal (dimension->string (unit-dimension '(/ m m))) "1")
  (assert-true (same-dimension? 'J 'eV))
  (assert-true (same-dimension? '(/ km h) '(/ m s)))
  (assert-true (not (same-dimension? 'J 'W))))

(deftest "dim1: фальшивка — перевод м в с и неизвестная единица — ошибки"
  (assert-error (convert (quantity 1 'm) 's))
  (assert-error (unit-dimension 'foo))
  (assert-error (unit-dimension '(^ m 0.5)))
  (assert-equal (try (convert (quantity 1 'm) 's) (lambda (e) (error-message e)))
                "convert: размерности различны: L и T"))

(deftest "dim1: сложение величин — разные единицы одной размерности и фальшивка"
  (assert-equal (quantity-value (quantity-add (quantity 1 'km) (quantity 500 'm))) 3/2)
  (assert-equal (quantity-unit (quantity-add (quantity 1 'km) (quantity 500 'm))) 'km)
  (assert-error (quantity-add (quantity 1 'kg) (quantity 1 'm))))

(deftest "dim1: умножение, деление, степень величин"
  (let ((v (quantity-div (quantity 100 'm) (quantity 10 's))))
    (assert-equal (quantity-value v) 10)
    (assert-equal (quantity-value (convert v '(/ km h))) 36))
  (let ((a (quantity-pow (quantity 3 'm) 2)))
    (assert-equal (quantity-value a) 9)
    (assert-equal (unit-dimension (quantity-unit a)) '(2 0 0 0 0 0 0)))
  (assert-equal (unit-dimension (quantity-unit (quantity-mul (quantity 2 'kg) (quantity 3 '(/ m (^ s 2))))))
                (unit-dimension 'N))
  (assert-error (quantity-pow (quantity 3 'm) 0.5)))

(deftest "dim1: круговой перевод точен для 5 пар единиц"
  (let ((check (lambda (q u2)
                 (equal? (convert (convert q u2) (quantity-unit q)) q))))
    (assert-true (check (quantity 7/3 'km) 'mile))
    (assert-true (check (quantity 13 'eV) 'cal))
    (assert-true (check (quantity 5 'atm) 'mmHg))
    (assert-true (check (quantity 2 '(/ km h)) '(/ ft min)))
    (assert-true (check (quantity 11 'lb) 'mg))))

(deftest "dim1: проверка размерности E = m c^2 — ok, E = m c — несоответствие"
  (let ((env '((E . J) (m . kg) (c . (/ m s)))))
    (assert-equal (dimension-check '(= E (* m (^ c 2))) env) (list 'ok (unit-dimension 'J)))
    (assert-equal (dimension-check '(= E (* m c)) env)
                  (list 'mismatch '(= E (* m c)) (unit-dimension 'J) (unit-dimension '(/ (* kg m) s))))))

(deftest "dim1: F = m a, кинетическая энергия, маятник — ok"
  (assert-equal (dimension-check '(= F (* m a)) '((F . N) (m . kg) (a . (/ m (^ s 2)))))
                (list 'ok (unit-dimension 'N)))
  (assert-equal (dimension-check '(= K (* 1/2 m (^ v 2))) '((K . J) (m . kg) (v . (/ m s))))
                (list 'ok (unit-dimension 'J)))
  (assert-equal (dimension-check '(= T (* 2 pi (sqrt (/ l g)))) '((T . s) (l . m) (g . (/ m (^ s 2)))))
                (list 'ok (unit-dimension 's))))

(deftest "dim1: exp от секунд и сумма метров с секундами — несоответствие в нужном месте"
  (let ((env '((t . s) (x . m))))
    (assert-equal (dimension-check '(exp t) env)
                  (list 'mismatch '(exp t) (unit-dimension 's) '(0 0 0 0 0 0 0)))
    (assert-equal (dimension-check '(+ x t) env)
                  (list 'mismatch '(+ x t) (unit-dimension 'm) (unit-dimension 's)))
    (assert-equal (dimension-check '(* 3 (sin (+ x t))) env)
                  (list 'mismatch '(+ x t) (unit-dimension 'm) (unit-dimension 's)))
    (assert-equal (dimension-check '(exp (/ x x)) env) (list 'ok '(0 0 0 0 0 0 0)))))

(deftest "dim1: показатели — рациональные; дробный показатель и нерациональный"
  (let ((env '((x . m) (n . kg))))
    (assert-equal (dimension-check '(^ x 3/2) env) (list 'ok '(3/2 0 0 0 0 0 0)))
    (assert-equal (dimension-check '(^ x 0.5) env)
                  (list 'mismatch '(^ x 0.5) (unit-dimension 'm) 'rational-exponent))
    (assert-equal (dimension-check '(^ x n) env)
                  (list 'mismatch '(^ x n) (unit-dimension 'm) 'rational-exponent))))

(deftest "dim1: dimension-check — неизвестный символ и операция — ошибка, не несоответствие"
  (assert-error (dimension-check '(+ x y) '((x . m))))
  (assert-error (dimension-check '(foo x) '((x . m)))))

(deftest "dim1: температура — аффинный перевод"
  (assert-equal (convert-temperature 100 '°C 'K) 7463/20)
  (assert-equal (convert-temperature 212 '°F '°C) 100)
  (assert-equal (convert-temperature 273 'K 'degC) -3/20)
  (assert-equal (convert-temperature 0 'degC 'degF) 32)
  (assert-error (convert-temperature 1 'm 'K))
  (assert-error (unit-dimension '°C)))

; ---------- DIM.2: π-теорема Бэкингема ----------
(define (dim2-rej? vs env gs) (equal? (pi-groups-check vs env gs) #f))
(define dim2-pend '((T . s) (l . m) (g . (/ m (^ s 2))) (m . kg)))
(define dim2-drag '((F . N) (rho . (/ kg (^ m 3))) (v . (/ m s)) (D . m) (mu . (* Pa s))))
(define dim2-pipe '((dp . Pa) (L . m) (D . m) (rho . (/ kg (^ m 3))) (v . (/ m s)) (mu . (* Pa s))))

(deftest "dim2: mmHg = 133.322387415 Па, Torr = 101325/760 Па"
  (assert-equal (unit-factor 'mmHg) 133322387415/1000000000)
  (assert-equal (unit-factor 'Torr) 101325/760)
  (assert-equal (unit-dimension 'Torr) (unit-dimension 'Pa)))

(deftest "dim2: dimension-matrix — нулевые строки опущены"
  (assert-equal (dimension-matrix '(T l g m) dim2-pend) '((0 1 1 0) (0 0 0 1) (1 0 -2 0)))
  (assert-equal (dimension-matrix '(a b) '((a . m) (b . (/ m s)))) '((1 1) (0 -1))))

(deftest "dim2: маятник — одна группа T²g/l, масса выпала"
  (assert-equal (pi-groups '(T l g m) dim2-pend) '((* (^ T 2) (^ l -1) (^ g 1))))
  (assert-equal (dimensional-solve 'T '(l g m) dim2-pend) '(= T (* C (^ l 1/2) (^ g -1/2)))))

(deftest "dim2: сопротивление — две группы, число Рейнольдса при повторяющихся rho v D"
  (let ((gs (pi-groups '(F rho v D mu) dim2-drag :repeating '(rho v D))))
    (assert-equal gs '((* (^ F 1) (^ rho -1) (^ v -2) (^ D -2)) (* (^ rho -1) (^ v -1) (^ D -1) (^ mu 1))))
    (assert-true (pi-groups-check '(F rho v D mu) dim2-drag gs)))
  (assert-equal (length (pi-groups '(F rho v D mu) dim2-drag)) 2)
  (assert-true (pi-groups-check '(F rho v D mu) dim2-drag (pi-groups '(F rho v D mu) dim2-drag))))

(deftest "dim2: перепад давления в трубе — три группы"
  (let ((gs (pi-groups '(dp L D rho v mu) dim2-pipe)))
    (assert-equal (length gs) 3)
    (assert-true (pi-groups-check '(dp L D rho v mu) dim2-pipe gs))
    (assert-equal (length (pi-groups '(dp L D rho v mu) dim2-pipe :repeating '(rho v D))) 3)))

(deftest "dim2: дальность полёта R = C v²/g"
  (assert-equal (dimensional-solve 'R '(v g) '((R . m) (v . (/ m s)) (g . (/ m (^ s 2)))))
                '(= R (* C (^ v 2) (^ g -1)))))

(deftest "dim2: Кеплер T = C sqrt(a³/(GM))"
  (assert-equal (dimensional-solve 'T '(a G M)
                                   '((T . s) (a . m) (G . (/ (^ m 3) (* kg (^ s 2)))) (M . kg)))
                '(= T (* C (^ a 3/2) (^ G -1/2) (^ M -1/2)))))

(deftest "dim2: скорость звука c = C sqrt(p/rho)"
  (assert-equal (dimensional-solve 'c '(p rho) '((c . (/ m s)) (p . Pa) (rho . (/ kg (^ m 3)))))
                '(= c (* C (^ p 1/2) (^ rho -1/2)))))

(deftest "dim2: несколько групп — форма Φ(π₁, π₂) = 0"
  (let ((r (dimensional-solve 'F '(rho v D mu) dim2-drag)))
    (assert-equal (car r) '=)
    (assert-equal (length (cdr (cadr r))) 2)
    (assert-equal (caddr r) 0)))

(deftest "dim2: недопустимый набор :repeating — ошибка"
  ; мало переменных; лишняя; повтор; не из списка; зависимые столбцы (T l g)
  (assert-error (pi-groups '(F rho v D mu) dim2-drag :repeating '(rho v)))
  (assert-error (pi-groups '(F rho v D mu) dim2-drag :repeating '(rho v D mu)))
  (assert-error (pi-groups '(F rho v D mu) dim2-drag :repeating '(D D rho)))
  (assert-error (pi-groups '(F rho v D mu) dim2-drag :repeating '(rho v x)))
  (assert-error (pi-groups '(T l g m) dim2-pend :repeating '(T l g))))

(deftest "dim2: сертификат отвергает подделки"
  (let ((vs '(T l g m)) (good '(* (^ T 2) (^ l -1) (^ g 1))))
    (assert-true (pi-groups-check vs dim2-pend (list good)))
    ; неверный показатель — не безразмерна
    (assert-true (dim2-rej? vs dim2-pend '((* (^ T 1) (^ l -1) (^ g 1)))))
    ; недостаточно групп: пустой набор при одной обязательной группе
    (assert-true (dim2-rej? vs dim2-pend '()))
    ; переменная не из vars (в env есть, в vars нет)
    (assert-true (dim2-rej? vs (cons '(z . m) dim2-pend)
                                   (list '(* (^ T 2) (^ l -1) (^ g 1) (^ z 0)))))
    ; группа с переменной вне vars и вне env
    (assert-true (dim2-rej? vs dim2-pend '((* (^ T 2) (^ l -1) (^ g 1) (^ q 1))))))
  (let ((g1 '(* (^ F 1) (^ rho -1) (^ v -2) (^ D -2))))
    (assert-true (dim2-rej? '(F rho v D mu) dim2-drag (list g1 g1)))
    (assert-true (dim2-rej? '(F rho v D mu) dim2-drag (list g1)))
    (assert-true (dim2-rej? '(F rho v D mu) dim2-drag
                                   (list g1 '(* (^ F 2) (^ rho -2) (^ v -4) (^ D -4)))))))

; ---------- ML.AUDIT: единицы во входном языке (--math) ----------
; Отвечают обёртки m-un-* из lib/mathlang/runtime.lisp (таблица m-aliases). Единица, формула и имена
; переменных передаются СТРОКАМИ: m, s, T в языке — обычные переменные, и их значения не влияют на разбор.
(deftest "units: величина, перевод и температура во входном языке (--math)"
  (assert-equal (math-eval "quantity(9.8, \"m/s^2\")") (quantity 9.8 '(/ m (^ s 2))))
  (assert-equal (math-eval "convert(quantity(36, \"km/h\"), \"m/s\")") (quantity 10 '(/ m s)))
  ; 1 км/ч = 5/18 м/с — точная дробь, не float
  (assert-equal (quantity-value (math-eval "convert(quantity(1, \"km/h\"), \"m/s\")")) 5/18)
  (assert-equal (math-eval "convert_temperature(100, \"degC\", \"K\")") 7463/20)
  ; значения переменных m и s на разбор единиц не влияют (единицы — строками)
  (assert-equal (math-eval "m := 5\ns := 2\nconvert(quantity(36, \"km/h\"), \"m/s\")") (quantity 10 '(/ m s)))
  ; неизвестная единица — ошибка, а не молчаливый ответ (проверка ленивая: при переводе)
  (assert-error-fn (lambda () (math-eval "convert(quantity(1, \"zz\"), \"m\")"))))

(deftest "units: проверка размерности и π-теорема во входном языке (--math)"
  (assert-equal (math-eval "dimension_check(\"T = 2*pi*sqrt(l/g)\", [\"T = s\", \"l = m\", \"g = m/s^2\"])") "ok: T")
  (let ((r (math-eval "dimension_check(\"T = 2*pi*l\", [\"T = s\", \"l = m\"])")))
    (assert-true (string? r))
    (assert-true (string-contains? r "mismatch")))
  ; маятник: одна безразмерная группа T²g/l
  (assert-equal (m-items (math-eval "pi_groups([\"l\",\"g\",\"T\"], [\"l = m\",\"g = m/s^2\",\"T = s\"])"))
                (list '(* (^ l 1) (^ g -1) (^ T -2))))
  ; сертификат принимает свои же группы
  (assert-equal #t (math-eval "pi_groups_check([\"l\",\"g\",\"T\"], [\"l = m\",\"g = m/s^2\",\"T = s\"], pi_groups([\"l\",\"g\",\"T\"], [\"l = m\",\"g = m/s^2\",\"T = s\"]))"))
  ; T = C·√(l/g)
  (assert-equal (math-eval "dimensional_solve(\"T\", [\"l\",\"g\"], [\"l = m\",\"g = m/s^2\",\"T = s\"])")
                '(= T (* C (^ l 1/2) (^ g -1/2))))
  ; классический метод с повторяющимися переменными l, g — та же одна группа
  (assert-equal 1 (length (m-items (math-eval "pi_groups([\"l\",\"g\",\"T\"], [\"l = m\",\"g = m/s^2\",\"T = s\"], [\"l\",\"g\"])")))))

