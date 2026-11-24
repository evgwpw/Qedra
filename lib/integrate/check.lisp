; integrate/check.lisp — проверка первообразной дифференцированием и вспомогательные численные функции (часть бывшего
; lib\integrate.lisp, шаг 21h'). Загружается после integrate/parts.lisp.
; int-check — документированный API; int-num используют limit и api.lisp
(module integrate
  (export int-check int-check-how int-num int-check-rubi int-check-rubi-how))

; ---------- проверка дифференцированием ----------

; точки и параметры — рациональные числа (Шаг 21h): суммы по корням (root-sum) в производной eval-num считает ТОЧНО в ℚ[t]/(Q),
; небольшие знаменатели (3/10, а не двоичная дробь 0.3) удерживают размер чисел в этой арифметике
(define int-test-points '(3/10 47/100 71/100 137/100 11/5))
(define int-test-params '(17/10 23/10 19/10 31/10 13/10 29/10 11/10 27/10))

; символы-параметры выражения (не головы функций, не x, не константы pi и %i)
(define (int-symbols e x)
  (cond ((and (symbol? e) (not (equal? e x)) (not (member? e '(pi %i)))) (list e))
        ; (root-sum t Q E): связанная переменная t — не параметр
        ((and (op-expr? e) (equal? (car e) 'root-sum) (= (length e) 4))
         (filter (lambda (s) (not (equal? s (cadr e))))
                 (int-dedupe (append (int-symbols (nth e 2) x) (int-symbols (nth e 3) x)))))
        ((op-expr? e) (int-dedupe (append-map (lambda (a) (int-symbols a x)) (cdr e))))
        (else '())))

; гиперболические функции — через exp/log (eval-num их не вычисляет)
(define (int-hyp e)
  (if (op-expr? e)
      (let ((args (map int-hyp (cdr e))) (h (car e)))
        (let ((u (if (null? args) #f (car args))))
          (cond ((equal? h 'sinh) (list '* 1/2 (list '+ (list 'exp u) (list '* -1 (list 'exp (list '* -1 u))))))
                ((equal? h 'cosh) (list '* 1/2 (list '+ (list 'exp u) (list 'exp (list '* -1 u)))))
                ((equal? h 'tanh) (let ((p (list 'exp u)) (m (list 'exp (list '* -1 u))))
                                    (list '* (list '+ p (list '* -1 m)) (list '^ (list '+ p m) -1))))
                ((equal? h 'sech) (list '* 2 (list '^ (list '+ (list 'exp u) (list 'exp (list '* -1 u))) -1)))
                ((equal? h 'csch) (list '* 2 (list '^ (list '+ (list 'exp u) (list '* -1 (list 'exp (list '* -1 u)))) -1)))
                ((equal? h 'coth) (let ((p (list 'exp u)) (m (list 'exp (list '* -1 u))))
                                    (list '* (list '+ p m) (list '^ (list '+ p (list '* -1 m)) -1))))
                ((equal? h 'asinh) (list 'log (list '+ u (list '^ (list '+ (list '^ u 2) 1) 1/2))))
                ((equal? h 'atanh) (list '* 1/2 (list 'log (list '* (list '+ 1 u) (list '^ (list '+ 1 (list '* -1 u)) -1)))))
                (else (cons h args)))))
      e))

; |значение| выражения в точке (x = p, параметры — фиксированные числа) или #f
(define (int-abs-at d x p vals)
  (try (num-abs (eval-num (int-hyp (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                          (replace-expr d x p) vals))))
       (lambda (err) #f)))

; tol — допуск невязки относительно 1 + |e|; pts — точки.
; Состояние: 'ok (невязка мала во всех вычислимых точках, их не меньше двух), 'bad (где-то велика),
; 'skip (вычислимых точек меньше двух — проверить нечем)
; Допуск относительный, поэтому при огромном |e| во всех точках (множитель e⁶⁴ и т. п.) невязка порядка 1 не видна:
; hebisch/9242 — ответ без слагаемого x при f = 1 + (8x+24)·e^(…−8x)/(x+4) проходил (|e| ≈ 1e28). Тогда
; дополнительно — дальние точки int-far-points, где такой множитель мал: расхождение в любой из них — 'bad.
(define int-far-points '(10 30 -10 -30))
(define int-far-big 1000000)        ; |e| больше этого во ВСЕХ вычислимых точках — смотреть дальние
(define (int-numeric-status-at dfe e x tol pts)
  (let* ((ps (int-symbols (list '+ dfe e) x))
         (vals (map2 list ps int-test-params))
         (bs '())
         ; по каждой точке: 'skip (не вычислилось), #t (невязка мала) или #f
         (rs (filter (lambda (r) (not (equal? r 'skip)))
                     (map (lambda (p)
                            (let ((a (int-abs-at dfe x p vals)) (b (int-abs-at e x p vals)))
                              (when b (set! bs (cons b bs)))
                              (if (and a b) (< a (* tol (+ 1 b))) 'skip)))
                          pts))))
    (cond ((< (length rs) 2) 'skip)
          ((not (every? (lambda (r) r) rs)) 'bad)
          ((and (pair? bs) (every? (lambda (b) (> b int-far-big)) bs)
                (any? (lambda (p)
                         ; переполнение double (∞, NaN) — точка не судит: f^(c(a+bx)²) при x = −10 даёт e⁹⁷⁵
                         (let ((a (int-abs-at dfe x p vals)) (b (int-abs-at e x p vals)))
                           (and a b (< a 1e300) (< b 1e300) (not (< a (* tol (+ 1 b)))))))
                       int-far-points))
           'bad)
          (else 'ok))))

; Шаг INT.BR: вещественное ли значение (допускается мнимый шум дробных степеней)
(define (int-real-val? v)
  (cond ((real-numeric? v) #t)
        ((and (op-expr? v) (equal? (car v) '+) (= (length v) 3) (real-numeric? (nth v 1))
              (op-expr? (nth v 2)) (equal? (car (nth v 2)) '*) (= (length (nth v 2)) 3)
              (equal? (nth (nth v 2) 2) '%i) (real-numeric? (nth (nth v 2) 1)))
         (< (abs (nth (nth v 2) 1)) 0.000000001))
        (else #f)))

; точки x < 0, где e определено и вещественно (при параметрах — пробные числа); #t, если таких не меньше двух
; WRONG.1: дальние точки — область √(x²−a²) начинается за |a| (|x| > 1.5 у √(4x²−9)); список из точек
; около нуля считал «при x < 0 подынтегральное не вещественно» и пропускал ветвь
(define int-neg-test-points '(-3/10 -47/100 -71/100 -137/100 -11/5 -267/100 -3 -37/10 -51/10 -73/10))
(define (int-real-on-neg? e x) (int-real-on-neg-all? (list e) x int-neg-test-points))

; ближайшие к нулю точки: проверка int-check только в них (дальше за корнем радикала главные значения √u·√v и √(u·v)
; расходятся знаком, хотя ответ на своём интервале верен)
(define int-neg-near-points '(-3/10 -47/100))

; то же для списка выражений: в точке вещественны ВСЕ (иначе ветви главных значений не обязаны сходиться);
; pts — точки; возвращает точки, где все выражения вычислились вещественно
(define (int-real-points-p es x pts params)
  (let* ((ps (int-dedupe (append-map (lambda (e) (int-symbols e x)) es)))
         (vals (map2 list ps params)))
    (filter (lambda (p)
              (every? (lambda (e)
                        (try (int-real-val? (eval-num (int-hyp (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                                                     (replace-expr e x p) vals))))
                             (lambda (err) #f)))
                      es))
            pts)))
(define (int-real-points es x pts) (int-real-points-p es x pts int-test-params))

; нужно хотя бы две вещественные точки (для двух точек — обе)
(define (int-real-on-neg-all? es x pts)
  (>= (length (int-real-points es x pts)) 2))

(define (int-numeric-zero-at? dfe e x tol pts) (equal? (int-numeric-status-at dfe e x tol pts) 'ok))

(define (int-numeric-zero? dfe e x) (int-numeric-zero-at? dfe e x 0.0000001 int-test-points))

; WRONG.2: F′ − f, раскрытая символьно. Если после expand остаётся ПРОСТОЕ (рациональное по x и параметрам)
; ненулевое выражение — ответ точной первообразной не является (например, потеряно слагаемое 14/x³ рядом
; с e^(e⁵)/x² ≈ 10⁶⁴); численная проверка этого не видит из-за относительного допуска.
(define (int-simple-residual? e)
  (cond ((or (number? e) (symbol? e)) #t)
        ((op-expr? e)
         (and (member? (car e) '(+ - * / ^))
              (if (equal? (car e) '^) (and (= (length e) 3) (integer? (nth e 2))) #t)
              (every? int-simple-residual? (cdr e))))
        (else #f)))
(define (int-residual-expanded F f x)
  (try (simplify (expand (list '- (int-diff x F) f))) (lambda (err) #f)))
; WRONG.2: слагаемые f; дробь с суммой в числителе раскладывается почленно (теряемое слагаемое 14/x³
; в hebisch/4973 записано именно так: (…+14)/x³).
(define (int-additive-terms f)
  (cond ((and (op-expr? f) (equal? (car f) '+) (> (length f) 2)) (cdr f))
        ((and (op-expr? f) (equal? (car f) '/) (= (length f) 3)
              (op-expr? (nth f 1)) (equal? (car (nth f 1)) '+) (> (length (nth f 1)) 2))
         (map (lambda (t) (list '/ t (nth f 2))) (cdr (nth f 1))))
        ; произведение с суммой-множителем: 14/x³ = x⁻³·(…+14) — раскладываем почленно (остальные множители в каждом)
        ((and (op-expr? f) (equal? (car f) '*)
              (any? (lambda (q) (and (op-expr? q) (equal? (car q) '+) (> (length q) 2))) (cdr f)))
         (let* ((fs (cdr f))
                (s (car (filter (lambda (q) (and (op-expr? q) (equal? (car q) '+) (> (length q) 2))) fs)))
                (others (filter (lambda (q) (not (equal? q s))) fs)))
           (map (lambda (t) (cons '* (append others (list t)))) (cdr s))))
        (else (list f))))
(define (int-f-term-abss f x p vals)
  (let loop ((ts (int-additive-terms f)) (mn #f) (mx #f))
    (if (null? ts)
        (and mn (cons mn mx))
        (let ((v (int-cx-at (car ts) x p vals)))
          (if (or (not v) (= (abs (car v)) 0))
              (loop (cdr ts) mn mx)
              (let ((a (abs (car v))))
                (loop (cdr ts) (if (or (not mn) (< a mn)) a mn) (if (or (not mx) (> a mx)) a mx))))))))
; есть ли в f слагаемые, различающиеся по модулю сильнее, чем видит относительный допуск double-проверки
(define (int-scale-disparity? f x)
  (let* ((ps (int-symbols f x)) (vals (map2 list ps int-test-params)))
    (any? (lambda (p)
            (let ((tm (try (int-f-term-abss f x p vals) (lambda (err) #f))))
              (and tm (cdr tm) (> (cdr tm) (* 1000000000000 (+ 1 (car tm)))))))
          int-test-points)))
; WRONG.2: потеря слагаемого ищется у любого ответа (подынтегральное может быть записано дробью); остаток
; подтверждаем together-нормализацией, чтобы несокращённый рациональный остаток верного ответа не считался ошибкой
; (x^6/(a+bx)^4 и подобные). Дорогие expand/together — только при гигантском разбросе слагаемых f.
(define (int-simple-residual-bad? F f x)
  (and (int-scale-disparity? f x)
       (let ((de (int-residual-expanded F f x)))
         (and (pair? de) (int-simple-residual? de)
              (let ((tg (try (simplify (together (list '- (int-diff x F) f))) (lambda (err) #f))))
                (and (pair? tg) (int-simple-residual? tg)))))))
; ---------- INT.NUMCHK: проверка САМОГО ответа численной производной ----------
; Проверки выше дифференцируют F формально (int-diff) и сверяют численно производную; тождества упрощения,
; верные «алгебраически» (√(u²) = u, √(−a)·√(−b) = √(a·b)), пропускают F, неверную как функция при главных
; значениях (INT.OWN.B13CHK: 13 ложных ответов старого пилота, research/intown/numchk-wrong.tsv).
; Здесь F проверяется как функция: центральная разность с шагом h и h/2 в вещественных точках x > 0 и x < 0.

; параметры: набор int-test-params (положительные). Второй набор с отрицательными значениями замерен и
; отброшен: у ответов с радикалами он переключает ветви самих формул (√(c/(a+bx)³) при c < 0 и т. п.), и
; проверка отвергала верные ответы (2 из 4 представителей класса на срезе 1.1); вещественность при x < 0
; уже покрывают точки −3/10 (int-real-on-neg-all?) и INT.BR.
(define int-numchk-params (list int-test-params))
; WRONG.1: при параметрах одного знака подынтегральное может быть нигде не вещественно (1/√(−b x²−π) при b > 0),
; проверка получала 'skip. Второй набор — те же значения со знаком минус; он пробуется, только если на первом
; наборе нет ни одной 'ok/-bad точки (верные ответы, принятые по положительному набору, не затрагиваются).
(define int-numchk-params-neg (list (map (lambda (v) (- 0 v)) int-test-params)))
(define int-numchk-tol 0.0001)      ; допуск |F′ − f| относительно 1 + |f|
(define int-numchk-h 1/1000)        ; шаг: h = |x|/1000
(define int-numchk-jump 0.01)       ; расхождение h и h/2 больше → скачок/особенность: точка пропускается
(define int-numchk-gross 100)       ; невязка больше 100·tol в одной точке — «грубо» (достаточно одной)
; *check-numeric-F* — включать ли проверку: #t, #f или 'risky (только ответы с ветвящимися головами — по
; умолчанию: замер шага INT.NUMCHK на срезах 1.1/1.2/4/6/7)
(define *check-numeric-F* 'risky)

; значение выражения в точке как комплекс (re . im) или #f (не вычислилось).
; Вещественное F — (v . 0); у ответов вида %i·atanh(…)/%i·log(…) значение комплексно, но мнимая часть
; постоянна по x (или это ветвь), поэтому сравнивается вещественная часть (см. int-F-point-verdict).
(define (int-cx-parts v)
  (cond ((real-numeric? v) (cons v 0.0))
        ((and (op-expr? v) (equal? (car v) '*) (= (length v) 3) (equal? (nth v 2) '%i)) (cons 0.0 (nth v 1)))
        ((and (op-expr? v) (equal? (car v) '+) (= (length v) 3) (real-numeric? (nth v 1)))
         (let ((q (int-cx-parts (nth v 2))))
           (and q (cons (+ (nth v 1) (car q)) (cdr q)))))
        (else #f)))
(define (int-cx-at e x p vals)
  (try (int-cx-parts (eval-num (int-hyp (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                              (replace-expr e x p) vals))))
       (lambda (err) #f)))


; вердикт по точке: 'skip (не вычислилось, скачок F или ветви), 'ok, 'bad (невязка), 'gross (невязка велика).
; Дёшево: сначала одна центральная разность с шагом h; если она уже сошлась с f — 'ok (2 eval-num).
; Иначе (подозрение) — шаг h/2, Ричардсон dr = (4·d(h/2) − d(h))/3 и проверка скачка |d(h) − d(h/2)|:
; большой скачок — особенность/ветвь, пропуск. Сравнивается ВЕЩЕСТВЕННАЯ часть: у ответов вида %i·atanh(…)
; и %i·log(…) мнимая часть постоянна (или это ветвь), а сама первообразная — вещественная часть.
; WRONG.2: при гигантском разбросе слагаемых f численную производную F не судим (округление double даёт
; ошибку порядка старшего слагаемого); потерю ловит символьный остаток — int-simple-residual-bad?.

(define (int-F-point-verdict F f x p vals)
  (let* ((h (if (> (abs p) 1/1000) (* (abs p) int-numchk-h) int-numchk-h))
         (fv (int-cx-at f x p vals))
         (fp (and fv (not (equal? h 0)) (int-cx-at F x (+ p h) vals)))
         (fm (and fp (int-cx-at F x (- p h) vals))))
    (if (or (not fv) (not fp) (not fm))
        'skip
        (let* ((scale (+ 1 (abs (car fv))))
               (d1 (/ (- (car fp) (car fm)) (* 2 h)))
               (err1 (abs (- d1 (car fv)))))
          (if (<= err1 (* int-numchk-tol scale))
              'ok
              (let* ((h2 (/ h 2))
                     (fp2 (int-cx-at F x (+ p h2) vals)) (fm2 (int-cx-at F x (- p h2) vals)))
                (if (or (not fp2) (not fm2))
                    'bad
                    (let* ((d2 (/ (- (car fp2) (car fm2)) h))
                           (dr (/ (- (* 4 d2) d1) 3))
                           (err (abs (- dr (car fv))))
                           (jump (abs (- d1 d2))))
                      (cond ((> jump (* int-numchk-jump scale)) 'skip)   ; скачок F или ветвь: судить нельзя
                            ((<= err (* int-numchk-tol scale)) 'ok)
                            ((> err (* int-numchk-gross int-numchk-tol scale)) 'gross)
                            (else 'bad))))))))))

; точки проверки: три штуки (стоимость одной проверки ≈ 18 eval-num): при x < 0 — если подынтегральное там
; вещественно (как int-real-on-neg-all?), иначе третья точка — ещё одна положительная
; WRONG.1: фиксированные точки (0,3; 0,71; 1,37) могут целиком лежать вне области (√(4x²−9) при |x| < 1,5,
; √(x²−a²), корень 4-й степени): проверка получала 'skip и пропускала ответ, неверный на другой ветви.
; Если в обычных точках подынтегральное не вещественно — берём по две вещественные точки с каждой стороны.
(define int-numchk-grid
  '(3/10 47/100 71/100 137/100 8/5 17/10 11/5 3 37/10 51/10 73/10
    -3/10 -47/100 -71/100 -137/100 -8/5 -17/10 -11/5 -3 -37/10 -51/10 -73/10))
(define (int-numchk-default-points-p f x params)
  (if (int-real-on-neg-all? (list f) x int-neg-near-points)
      (list 3/10 71/100 -3/10)
      (list 3/10 71/100 137/100)))
(define (int-numchk-stable? f x p params)
  (let ((h (if (> (abs p) 1/1000) (* (abs p) int-numchk-h) int-numchk-h)))
    (= 2 (length (int-real-points-p (list f) x (list (- p h) (+ p h)) params)))))
(define (int-numchk-points-for-p F f x params)
  (let ((def (int-numchk-default-points-p f x params)))
    ; точки выбираются по вещественности ПОДЫНТЕГРАЛЬНОГО: ответ F может быть комплексным
    ; (√b при отрицательном параметре), но производная на вещественной области обязана совпасть с f
    (let ((real-def (int-real-points-p (list f) x def params)))
      (if (= (length real-def) (length def))
          def
          (let* ((ps (filter (lambda (p) (int-numchk-stable? f x p params))
                             (int-real-points-p (list f) x int-numchk-grid params)))
                 (pos (filter (lambda (p) (> p 0)) ps))
                 (neg (filter (lambda (p) (< p 0)) ps))
                 (pick (append (take pos 2) (take neg 2))))
            (cond ((>= (length pick) 2) pick)
                  ((>= (length ps) 2) (take ps 3))
                  (else def)))))))
; три точки без ответа F (свёртка корней): обычный набор
(define (int-numchk-points f x) (int-numchk-default-points-p f x int-test-params))


; ответ с эллиптическими функциями: eval-num считает их ГЛАВНЫМ значением (F(φ|m) только при |φ| ≤ π/2),
; а формулы Rubi используют продолжение по периодам — при больших x это смена периода, а не ошибка ответа
; (замер: (a+b·x²)²√(c+d·x²)/x^(9/2), x = 1,37 — невязка 33 против 13,7 при верной формуле). Такие ответы
; численной проверкой F не судятся ('skip) — см. int-check-F-status.
(define (int-ell-answer? e)
  (cond ((op-expr? e)
         (or (member? (car e) '(elliptic-f elliptic-e elliptic-pi elliptic-k))
             (any? int-ell-answer? (cdr e))))
        (else #f)))

; ветвящиеся головы: дробные степени, log, atan, эллиптические, %i, root-sum, abs
(define (int-branch-risky? e)
  (cond ((op-expr? e)
         (let ((h (car e)))
           (or (and (equal? h '^) (= (length e) 3) (not (integer? (nth e 2))))
               (member? h '(sqrt log atan acot elliptic-f elliptic-e elliptic-pi root-sum abs %i))
               (any? int-branch-risky? (cdr e)))))
        (else #f)))

(define (int-check-F-on? F)
  (cond ((equal? *check-numeric-F* #t) #t)
        ((equal? *check-numeric-F* 'risky) (int-branch-risky? F))
        (else #f)))

; дробная степень НЕПОСРЕДСТВЕННО тригонометрической головы: только у таких выражений область
; вещественности может не покрывать фиксированные точки int-test-points (cos(x)^(-1/2) при x = 11/5).
; Степень произведения/суммы (sqrt(cos^-1 x·sin x), sqrt(tan x)) сюда не входит: там ответы Rubi
; (2F1, эллиптическая E) проверяются своими путями, и расширение приёма ломало INT.TQ.
(define (int-trig-base? b)
  (and (pair? b)
       (or (and (null? (cddr b)) (member? (car b) '(sin cos sec csc)))
           (and (equal? (car b) '^) (= (length b) 3) (number? (nth b 2))
                (pair? (nth b 1)) (null? (cddr (nth b 1)))
                (member? (car (nth b 1)) '(sin cos sec csc))))))
; одно семейство тригонометрии в подынтегральном: sin/csc либо cos/sec. Область вещественности
; такого выражения задаётся знаком одной функции, и фиксированные точки могут лежать вне неё;
; смесь семейств (INT.TQ: sin^(-1/2)·cos^(-1/2)) и tan/cot проверяются прежними путями —
; расширение приёма их ломало. Старая форма сводит cos к sin(u+pi/2), поэтому оба семейства допустимы.
(define (int-trig-family e)
  (cond ((not (op-expr? e)) #f)
        ((member? (car e) '(sin csc)) 'sin)
        ((member? (car e) '(cos sec)) 'cos)
        ((member? (car e) '(tan cot)) 'tan)
        (else
         (let loop ((l (cdr e)) (f #f))
           (if (null? l)
               f
               (let ((g (int-trig-family (car l))))
                 (cond ((not g) (loop (cdr l) f))
                       ((not f) (loop (cdr l) g))
                       ((equal? g f) (loop (cdr l) f))
                       (else 'mixed))))))))
(define (int-one-trig-family? e)
  (member? (int-trig-family e) '(sin cos)))
(define (int-trig-frac-power? e)
  (cond ((op-expr? e)
         (or (and (equal? (car e) '^) (= (length e) 3) (not (integer? (nth e 2)))
                  (int-trig-base? (nth e 1)))
             (any? int-trig-frac-power? (cdr e))))
        (else #f)))

; (int-check-F-status F f x) → 'ok (F′ = f численно), 'bad (F неверна как функция), 'skip (нечем проверить).
; 'bad: грубая невязка хотя бы в одной точке либо обычная невязка не меньше чем в двух (точка × набор параметров).
; Ответы с эллиптическими функциями не проверяются ('skip): eval-num считает elliptic-f главным значением
; (|φ| ≤ π/2), а формулы Rubi используют продолжение по периодам — вдали от нуля это смена периода, не ошибка
; ответа (замер: 2 из 2 верных ответов с elliptic-f на срезе 1.1 дали «gross» при x = 3/10 и 47/100).
; Ветвящиеся головы ищутся и в f: ответ без корней для f с корнями (√(x−1)·√(1/(x−1)) = −1 при x < 1, а анзац
; по нормализованному f давал x + 1) — тоже риск ветви.
(define (int-check-F-status F f x)
  (if (or (not (int-check-F-on? (list '+ F f))) (int-ell-answer? F))
      'skip
      (let ((r1 (try (int-check-F-status-try F f x int-numchk-params) (lambda (err) 'skip))))
        (cond ((or (equal? r1 'ok) (equal? r1 'bad)) r1)
              ; 'weak — на положительной группе были частичные совпадения. Отрицательный набор
              ; может дать полноценный 'ok (нужен heur/subst/ansatz); 'bad там — ложный gross
              ; верных ответов со спецфункциями, поэтому он не отвергает.
              ((equal? r1 'weak)
               (let ((r2 (try (int-check-F-status-try F f x int-numchk-params-neg) (lambda (err) 'skip))))
                 (if (equal? r2 'ok) 'ok 'skip)))
              (else
               (let ((r2 (try (int-check-F-status-try F f x int-numchk-params-neg) (lambda (err) 'skip))))
                 (cond ((equal? r2 'bad) 'bad)
                       ((equal? r2 'ok) 'ok)
                       (else 'skip))))))))

; один набор параметров; 'skip — пробуем следующий, 'weak — был частичный ok, но полного ok нет.
; LOSS.R145.2: при одном 'ok идём дальше по группе (следующий набор может дать ≥ 2 совпадений);
; 'weak возвращается только после исчерпания всей группы.
(define (int-check-F-status-try F f x psets)
  (int-check-F-status-try-loop F f x psets #f))
(define (int-check-F-status-try-loop F f x psets partial)
  (if (null? psets)
      (if partial 'weak 'skip)
      (let* ((pset (car psets))
             (ps (int-symbols (list '+ F f) x))
             (pts (int-numchk-points-for-p F f x pset))
             ; сравнивать имеет смысл только там, где подынтегральное вещественно: у комплексного f
             ; (1/√(−b x²−π) при b > 0) вещественная часть нулевая и любая F проходит
             (pts (int-real-points-p (list f) x pts pset))
             (vals (map2 list ps pset))
             (rs (map (lambda (p) (int-F-point-verdict F f x p vals)) pts))
             (cnt (lambda (s) (length (filter (lambda (r) (equal? r s)) rs)))))
        (cond ((< (length pts) 2) (int-check-F-status-try-loop F f x (cdr psets) partial))
              ((> (cnt 'gross) 0) 'bad)
              ((>= (cnt 'bad) 2) 'bad)
              ((>= (cnt 'ok) 2) 'ok)
              ((>= (cnt 'ok) 1) (int-check-F-status-try-loop F f x (cdr psets) #t))
              (else (int-check-F-status-try-loop F f x (cdr psets) partial))))))

; Финальная приёмка (INT.NUMCHK): ответ уходит пользователю — проверить сам F, а не только формальную производную.
; Зовётся из int-final (каскад) и rubi-integrate* (Rubi), а НЕ из поиска: на каждый кандидат поиска проверка
; F стоила бы десятки eval-num и съедала бюджет (замер: срез 1.1, −43 задачи из 1380, время +15 %).
; WRONG.1: параметры оракула бывают любого знака — ответ, верный при b > 0, но неверный при b < 0
; (ветвь √, atan), финальная приёмка проверяет ОБА знака набора параметров.
(define (int-check-F-status-any-signs F f x)
  (if (int-ell-answer? F)
      'skip
      (let ((r1 (try (int-check-F-status-try F f x int-numchk-params) (lambda (err) 'skip)))
            (r2 (try (int-check-F-status-try F f x int-numchk-params-neg) (lambda (err) 'skip))))
        (cond ((or (equal? r1 'bad) (equal? r2 'bad)) 'bad)
              ((or (equal? r1 'ok) (equal? r2 'ok)) 'ok)
              (else 'skip)))))
; WRONG.1: x⁻ᵏ внутри корня/дробной степени/atan — признак ответа, полученного выносом x из корня
; (верен лишь на одной ветви x > 0 или x < 0); только для таких ответов финальная приёмка смотрит оба знака
; параметров — у обычных ответов (x⁻ᵏ снаружи радикала) отрицательный набор даёт ложные «ветви».
(define (int-has-x-inv? e)
  (cond ((not (pair? e)) #f)
        ((and (equal? (car e) '^) (= (length e) 3) (equal? (cadr e) 'x)
              (number? (caddr e)) (< (caddr e) 0)) #t)
        (else (any? int-has-x-inv? (cdr e)))))
(define (int-xrecip-branch? e)
  (cond ((not (pair? e)) #f)
        ((and (member? (car e) '(sqrt atan asin acos))
              (pair? (cdr e)) (int-has-x-inv? (cadr e))) #t)
        ((and (equal? (car e) '^) (= (length e) 3) (number? (caddr e)) (not (integer? (caddr e)))
              (int-has-x-inv? (cadr e))) #t)
        (else (any? int-xrecip-branch? (cdr e)))))

(define (int-check-special? e)
  (cond ((not (pair? e)) #f)
        ((member? (car e) '(gamma hypergeometric-2f1 hypergeometric_pfq hypergeometric appell-f1
                            elliptic-f elliptic-e elliptic-pi elliptic-k polylog)) #t)
        (else (any? int-check-special? (cdr e)))))

(define (int-check-F-final-ok? F f x)
  (and (not (try (int-simple-residual-bad? F f x) (lambda (err) #f)))
       (let ((st (if (and (int-xrecip-branch? F) (null? (int-rootsums F)) (not (int-check-special? F)))
                     (try (int-check-F-status-any-signs F f x) (lambda (err) 'skip))
                     (try (int-check-F-status F f x) (lambda (err) 'skip)))))
         (not (equal? st 'bad)))))


; (int-check-how F e x) → чем доказано d/dx F = e: 'simplify | 'together (точно), 'numeric (в пробных точках),
; иначе 'bad (численно не сходится) или 'skip (численно проверить нечем). Шаг 22.6: сертификат derivative
(define (int-check-how F e0 x)
  (let* ((diffed (int-diff x F)) (e (simplify e0)))
    (let ((dfe (list '- diffed e)))
      (cond ((equal? (simplify dfe) 0) 'simplify)
            ((equal? (try (together dfe) (lambda (err) #f)) 0) 'together)
            ((int-simple-residual-bad? F e0 x) 'bad)
            (else (let ((st (int-numeric-status-at dfe e x 0.0000001 int-test-points)))
                    ; Шаг INT.BR: точки только x > 0 пропускали ответы, неверные при x < 0 (√(1−x²) = |x|·√(x⁻²−1));
                    ; где подынтегральное вещественно и при x < 0 — проверяем и там
                    (if (equal? st 'ok)
                        (if (and (int-real-on-neg-all? (list e F) x int-neg-near-points)
                                 (equal? (int-numeric-status-at dfe e x 0.0000001 int-neg-near-points) 'bad))
                            'bad
                            'numeric)
                        st)))))))

; (int-check F e x) → #t, если d/dx F = e: точно (simplify, together) либо численно
(define (int-check F e0 x)
  (let ((how (int-check-how F e0 x)))
    (or (equal? how 'simplify) (equal? how 'together) (equal? how 'numeric))))

; ---------- проверка ответа движка Rubi (шаг RUBI.SPEED.3) ----------

; RUBI.SPEED.3: Rubi перебирает десятки кандидатов на выражение, и почти все они отвергаются. Профиль показал,
; что 40–52 % времени уходит в int-check, а в нём ⅔ — together от d/dx F − e (≈0,35 с на больших ответах), хотя
; численная сверка даёт тот же исход за ≈0,08 с. Порядок здесь — по стоимости: simplify (точно, дёшево) →
; численная сверка → together только когда численно проверить нечем (skip). Набор принятых ответов тот же:
; 'numeric и 'together оба означают «принято» (int-check тоже их не различает).
; Каскад integrate не затронут: int-check/int-check-how остаются как были (на статус numeric опирается RUBI.6.6).
; *check-rubi-together-after-bad* — развилка замера: при численном 'bad пробовать together или сразу отвергать.
; Замерено на трёх наборах (RUBI.SPEED.3): с together после bad — 395 ok (ok-sample), 20 (speed-edge),
; 48 (speed-slow); без together — 395, 24, 50 при дословно тех же ответах (расхождений 0). По умолчанию #f:
; численное 'bad' на 5 точках у ошибочных первообразных together не подтверждает, а верные ответы со
; спецфункциями принимает отдельная проверка 2F1/AppellF1 в движке, а не эта функция.
(define *check-rubi-together-after-bad* #f)

; (int-check-rubi-how F e x) → 'simplify | 'numeric | 'together (принято), 'bad (неверно), 'skip (проверить нечем).
; INT.NUMCHK: после формальной проверки (int-check-rubi-formal) — численная проверка самого F (int-check-F-status):
; ответ, у которого d/dx F = f лишь формально (ветви √(u²), √(−a)√(−b)), отклоняется и здесь. Поиск Rubi зовёт
; формальную часть напрямую (rubi-int-check-search), чтобы не платить за проверку на каждом кандидате.
(define (int-check-rubi-how F e0 x)
  (let ((how (int-check-rubi-formal F e0 x)))
    (if (and (not (equal? how 'bad)) (equal? (int-check-F-status F (simplify e0) x) 'bad))
        'bad
        how)))

(define (int-check-rubi-formal F e0 x)
  (let ((diffed (int-diff x F)) (e (simplify e0)))
    (let ((dfe (list '- diffed e)))
      (cond ((equal? (simplify dfe) 0) 'simplify)
            (else (let* ((st (int-numeric-status-at dfe e x 0.0000001 int-test-points))
                         ; RUBI.GW.ORDER: у подынтегральных с дробными степенями фиксированные точки
                         ; int-test-points (до x = 11/5) могут лежать вне области вещественности
                         ; (cos(x)^(-1/2): cos < 0 при x = 11/5, корень комплексный) — верный ответ
                         ; получал 'bad. Перепроверяем на точках из области (int-numchk-points), но
                         ; принимаем только 'ok: 'skip исходной проверки должен дойти до together
                         ; (ответы 2F1 у INT.TQ иначе отвергались).
                         (st (let ((st2 (if (and (equal? st 'bad) (int-trig-frac-power? e)
                                                 (int-one-trig-family? e))
                                            (int-numeric-status-at dfe e x 0.0000001 (int-numchk-points e x))
                                            st)))
                               (if (equal? st2 'ok) 'ok st))))
                    (cond ((equal? st 'ok)
                           ; Шаг INT.BR (та же логика, что в int-check-how): точки только x > 0 пропускали ответы,
                           ; неверные при x < 0; где подынтегральное вещественно и при x < 0 — проверяем и там
                           (if (and (int-real-on-neg-all? (list e F) x int-neg-near-points)
                                    (equal? (int-numeric-status-at dfe e x 0.0000001 int-neg-near-points) 'bad))
                               'bad
                               'numeric))
                          ((and (equal? st 'bad) (not *check-rubi-together-after-bad*)) 'bad)
                          (else (let ((tg (try (together dfe) (lambda (err) #f))))
                                  (if (equal? tg 0) 'together (if (equal? st 'skip) 'skip 'bad)))))))))))

; (int-check-rubi F e x) → #t, если d/dx F = e: точно либо численно
(define (int-check-rubi F e0 x)
  (let ((how (int-check-rubi-how F e0 x)))
    (or (equal? how 'simplify) (equal? how 'together) (equal? how 'numeric))))

; (Шаг 21c: значения функций в точке — sin(π/2), exp(0), atan(1), 0^p, ... — считает сам simplify;
;  прежний обход int-fold / int-fold-call удалён)

; логарифм неположительного числа (особенность или ветвь) — определённый интеграл не вычисляем
(define (int-bad-log? e)
  (cond ((and (op-expr? e) (equal? (car e) 'log) (= (length e) 2) (real-numeric? (cadr e)) (<= (cadr e) 0)) #t)
        ((op-expr? e) (any? int-bad-log? (cdr e)))
        (else #f)))

; числовое значение предела (число, либо вычисляемое выражение вроде (exp 1)) или #f (символ)
(define (int-num v)
  (if (real-numeric? v)
      v
      (let ((n (try (eval-num v) (lambda (err) #f))))
        (if (and n (real-numeric? n)) n #f))))

; вещественный корень знаменателя в [a, b] (для символьных пределов — любой вещественный корень)
(define (int-singular? e x a b)
  (let ((den (try (denom e) (lambda (err) 1))) (na (int-num a)) (nb (int-num b)))
    (and (not (x-free? den x))
         (numeric-poly? den x)
         (any? (lambda (r) (or (not (and na nb))
                               (and (<= na r) (<= r nb))))
               (real-roots den x)))))
