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
                         (let ((a (int-abs-at dfe x p vals)) (b (int-abs-at e x p vals)))
                           (and a b (not (< a (* tol (+ 1 b)))))))
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
(define int-neg-test-points '(-3/10 -47/100 -71/100 -137/100 -11/5))
(define (int-real-on-neg? e x) (int-real-on-neg-all? (list e) x int-neg-test-points))

; ближайшие к нулю точки: проверка int-check только в них (дальше за корнем радикала главные значения √u·√v и √(u·v)
; расходятся знаком, хотя ответ на своём интервале верен)
(define int-neg-near-points '(-3/10 -47/100))

; то же для списка выражений: в точке вещественны ВСЕ (иначе ветви главных значений не обязаны сходиться);
; pts — точки, нужны хотя бы две вещественные (для двух точек — обе)
(define (int-real-on-neg-all? es x pts)
  (let* ((ps (int-dedupe (append-map (lambda (e) (int-symbols e x)) es)))
         (vals (map2 list ps int-test-params))
         (n (length (filter (lambda (p)
                              (every? (lambda (e)
                                        (try (int-real-val? (eval-num (int-hyp (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                                                                     (replace-expr e x p) vals))))
                                             (lambda (err) #f)))
                                      es))
                            pts))))
    (>= n 2)))

(define (int-numeric-zero-at? dfe e x tol pts) (equal? (int-numeric-status-at dfe e x tol pts) 'ok))

(define (int-numeric-zero? dfe e x) (int-numeric-zero-at? dfe e x 0.0000001 int-test-points))
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
(define (int-numchk-points f x)
  (if (int-real-on-neg-all? (list f) x int-neg-near-points)
      (list 3/10 71/100 -3/10)
      (list 3/10 71/100 137/100)))


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
      (let* ((ps (int-symbols (list '+ F f) x))
             (pts (int-numchk-points f x))
             (rs (append-map (lambda (pset)
                               (let ((vals (map2 list ps pset)))
                                 (map (lambda (p) (int-F-point-verdict F f x p vals)) pts)))
                             int-numchk-params))
             (n-of (lambda (s) (length (filter (lambda (r) (equal? r s)) rs)))))
        (cond ((> (n-of 'gross) 0) 'bad)
              ((>= (n-of 'bad) 2) 'bad)
              ((>= (n-of 'ok) 2) 'ok)
              (else 'skip)))))

; Финальная приёмка (INT.NUMCHK): ответ уходит пользователю — проверить сам F, а не только формальную производную.
; Зовётся из int-final (каскад) и rubi-integrate* (Rubi), а НЕ из поиска: на каждый кандидат поиска проверка
; F стоила бы десятки eval-num и съедала бюджет (замер: срез 1.1, −43 задачи из 1380, время +15 %).
(define (int-check-F-final-ok? F f x)
  (not (equal? (try (int-check-F-status F f x) (lambda (err) 'skip)) 'bad)))


; (int-check-how F e x) → чем доказано d/dx F = e: 'simplify | 'together (точно), 'numeric (в пробных точках),
; иначе 'bad (численно не сходится) или 'skip (численно проверить нечем). Шаг 22.6: сертификат derivative
(define (int-check-how F e0 x)
  (let ((diffed (int-diff x F)) (e (simplify e0)))
    (let ((dfe (list '- diffed e)))
      (cond ((equal? (simplify dfe) 0) 'simplify)
            ((equal? (try (together dfe) (lambda (err) #f)) 0) 'together)
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
            (else (let ((st (int-numeric-status-at dfe e x 0.0000001 int-test-points)))
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
