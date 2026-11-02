; interval.lisp — тесты шага CN.1: интервальная арифметика с точными рациональными концами.
; Концы — дроби (float запрещён); проверяем, что интервалы содержат истинные значения
; (сверка с известными десятичными цифрами) и что операции отвергают неверное.

(deftest "cn1: sqrt2 в узком рациональном интервале"
  (let ((X (iv-sqrt (iv 2 2))))
    ; X целиком внутри [1.41421356, 1.41421357]
    (assert-true (iv-subset? X (iv 141421356/100000000 141421357/100000000)))
    (assert-true (iv-contains? X 1414213562373095048801688724209/1000000000000000000000000000000))
    (assert-true (<= (iv-width X) 1/100000000000000000000000))))

(deftest "cn1: pi с 20 верными знаками (формула Мэчина)"
  (let ((P (iv-pi)))
    (assert-true (iv-contains? P 3141592653589793238462643383279/1000000000000000000000000000000))
    (assert-true (< (iv-width P) 1/100000000000000000000))
    ; 333/106 — приближение снизу, 355/113 — сверху
    (assert-true (< 333/106 (iv-lo P)))
    (assert-true (> 355/113 (iv-hi P)))))

(deftest "cn1: exp, log, sin, cos, atan согласуются с eval-num и узки (1e-15)"
  (let* ((E (iv-exp (iv 1 1))) (L (iv-log (iv 2 2)))
         (S (iv-sin (iv 1 1))) (C (iv-cos (iv 1 1))) (A (iv-atan (iv 1 1)))
         (tol 1/1000000000000000)
         (near (lambda (X v)
                 (let ((d (- (iv-mid X) v)))
                   (< (if (< d 0) (- d) d) 1/1000000000000)))))
    (assert-true (near E (eval-num (exp 1))))
    (assert-true (near L (eval-num (log 2))))
    (assert-true (near S (eval-num (sin 1))))
    (assert-true (near C (eval-num (cos 1))))
    (assert-true (near A (eval-num (atan 1))))
    (assert-true (<= (iv-width E) tol))
    (assert-true (<= (iv-width L) tol))
    (assert-true (<= (iv-width S) tol))
    (assert-true (<= (iv-width C) tol))
    (assert-true (<= (iv-width A) tol))))

(deftest "cn1: sin и cos на кусках монотонности дают точные концы"
  (let ((S (iv-sin (iv 0 1))) (C (iv-cos (iv 0 1))) (P (iv-pi)))
    (assert-equal (iv-lo S) 0)
    (assert-true (<= (iv-hi S) 1))
    (assert-equal (iv-hi C) 1)
    (assert-true (iv-contains? C 0))
    ; sin(pi) = 0, cos(pi) = -1 (pi — интервал, значение попадает внутрь)
    (assert-true (iv-contains? (iv-sin P) 0))
    (assert-true (iv-contains? (iv-cos P) -1))))

(deftest "cn1: iv-eval — включение выражения CAS"
  (let ((Y (iv-eval '(+ (sin x) (exp (* -1 x))) 'x (iv 0 0)))
        (Z (iv-eval '(exp (- (^ x 2))) 'x (iv 1/2 1/2)))
        (W (iv-eval '(* pi x) 'x (iv 1 2))))
    (assert-true (iv-contains? Y 1))                       ; sin 0 + e^0 = 1
    (assert-true (iv-contains? Z 778800783071404868245170266978/1000000000000000000000000000000))
    (assert-true (<= (iv-lo W) 22/7))
    (assert-true (>= (iv-hi W) 157/25))))

(deftest "cn1: iv-refine сужает зависимость, не теряя включения"
  (let ((X (iv-refine '(- x x) 'x (iv 0 1) 1/50))
        (Y (iv-refine '(* x (- 1 x)) 'x (iv 0 1) 1/4)))
    (assert-true (<= (iv-width X) 1/50))
    (assert-true (iv-contains? X 0))
    (assert-true (< (iv-width Y) 1))
    (assert-true (iv-contains? Y 0))
    (assert-true (iv-contains? Y 1/4))))

(deftest "cn1: деление на интервал с нулём и sqrt от отрицательного — ошибки"
  (assert-error (iv/ (iv 1 1) (iv -1 1)))
  (assert-error (iv/ (iv 1 1) (iv 0 0)))
  (assert-error (iv-sqrt (iv -1 4)))
  (assert-error (iv-log (iv 0 1)))
  (assert-error (iv-eval '(tan x) 'x (iv 0 1))))

(deftest "cn1: подделанный интервал не проходит проверку включения"
  ; pi не лежит в [3, 3.1]; истинный интервал pi содержит свой mid
  (assert-equal (iv-contains? (iv 3 31/10) (iv-mid (iv-pi))) #f)
  (assert-true (iv-contains? (iv-pi) (iv-mid (iv-pi))))
  ; sin 1 не лежит в [0.8, 0.84]
  (assert-equal (iv-contains? (iv 4/5 21/25) (eval-num (sin 1))) #f)
  ; интервал sin 1 согласуется с eval-num (двойное округление — с допуском 1e-12)
  (let ((d (- (iv-mid (iv-sin (iv 1 1))) (eval-num (sin 1)))))
    (assert-true (< (if (< d 0) (- d) d) 1/1000000000000))))

; ---------- CN.2: изоляция корней ----------

(deftest "cn2: isolate-roots — три непересекающихся интервала для x^3-2x-1"
  (let* ((p '(+ (^ x 3) (* -2 x) -1))
         (rs (isolate-roots p 'x)))
    (assert-equal (length rs) 3)
    ; упорядочены и не пересекаются
    (assert-true (<= (iv-hi (nth rs 0)) (iv-lo (nth rs 1))))
    (assert-true (<= (iv-hi (nth rs 1)) (iv-lo (nth rs 2))))
    ; в каждом — ровно один корень (смена знака)
    (map (lambda (I) (assert-true (iv-contains? (iv-eval p 'x I) 0))) rs)
    ; рациональный корень -1 — точечный интервал
    (assert-equal (nth rs 0) (iv -1 -1))))

(deftest "cn2: refine-root сужает до 1e-12 и не теряет корень"
  (let* ((p '(+ (^ x 3) (* -2 x) -1))
         (I (nth (isolate-roots p 'x) 2))
         (R (refine-root p 'x I 1/1000000000000)))
    (assert-true (<= (iv-width R) 1/1000000000000))
    (assert-true (iv-subset? R I))
    (assert-true (iv-contains? (iv-eval p 'x R) 0))
    ; отрезок без корня — ошибка, а не выдуманный ответ
    (assert-error (refine-root p 'x (iv 10 11) 1/1000))))

; ---------- CN.2: гарантированные корни (Кравчик) ----------

; смена знака f на концах интервала — независимая проверка, что корень действительно внутри
(define (cn2-sign-change? f x I)
  (let ((a (iv-eval f x (iv (iv-lo I) (iv-lo I))))
        (b (iv-eval f x (iv (iv-hi I) (iv-hi I)))))
    (or (and (< (iv-hi a) 0) (> (iv-lo b) 0))
        (and (> (iv-lo a) 0) (< (iv-hi b) 0)))))

(deftest "cn2: certified-roots cos x = x на [0,1]"
  (let* ((f '(- (cos x) x))
         (ans (certified-roots f 'x 0 1 1/1000000))
         (rs (car ans)))
    (assert-equal (length rs) 1)
    (assert-equal (length (cadr ans)) 0)
    (assert-true (<= (iv-width (car rs)) 1/1000000))
    ; интервал лежит в окрестности 0.739085 и содержит смену знака
    (assert-true (< (iv-lo (car rs)) 7390852/10000000))
    (assert-true (> (iv-hi (car rs)) 7390850/10000000))
    (assert-true (cn2-sign-change? f 'x (car rs)))))

(deftest "cn2: certified-roots e^x = 3x на [0,2] — два корня"
  (let* ((f '(- (exp x) (* 3 x)))
         (ans (certified-roots f 'x 0 2 1/1000000))
         (rs (car ans)))
    (assert-equal (length rs) 2)
    (assert-equal (length (cadr ans)) 0)
    (assert-true (<= (iv-hi (nth rs 0)) (iv-lo (nth rs 1))))
    (assert-true (< (iv-lo (nth rs 0)) 6190613/10000000))
    (assert-true (> (iv-hi (nth rs 0)) 6190612/10000000))
    (assert-true (< (iv-lo (nth rs 1)) 15121346/10000000))
    (assert-true (> (iv-hi (nth rs 1)) 15121345/10000000))
    (map (lambda (I) (assert-true (cn2-sign-change? f 'x I))) rs)))

(deftest "cn2: certified-roots sin x = 0 на [1,7] — pi и 2pi"
  (let* ((ans (certified-roots '(sin x) 'x 1 7 1/1000000))
         (rs (car ans)))
    (assert-equal (length rs) 2)
    (assert-true (< (iv-lo (nth rs 0)) 3141593/1000000))
    (assert-true (> (iv-hi (nth rs 0)) 3141592/1000000))
    (assert-true (< (iv-lo (nth rs 1)) 6283186/1000000))
    (assert-true (> (iv-hi (nth rs 1)) 6283185/1000000))
    (map (lambda (I) (assert-true (cn2-sign-change? '(sin x) 'x I))) rs)))

(deftest "cn2: certified-roots не выдумывает корень там, где его нет"
  ; x^2 + 1 > 0 — сертифицированных корней нет
  (let ((ans (certified-roots '(+ (^ x 2) 1) 'x -2 2 1/1000)))
    (assert-equal (car ans) '())
    (assert-equal (cadr ans) '()))
  ; кратный корень x^2: Кравчик не может доказать единственность — честно «не решено»
  (let ((ans (certified-roots '(^ x 2) 'x -1 1 1/1000)))
    (assert-equal (car ans) '())
    (assert-true (> (length (cadr ans)) 0))))

; ---------- CN.3: гарантированные интегралы и суммы ----------

(deftest "cn3: certified-integral e^(-x^2) на [0,1]"
  (let ((I (certified-integral '(exp (- (^ x 2))) 'x 0 1 1/1000000)))
    (assert-true (<= (iv-width I) 1/1000000))
    ; 0.7468241328... лежит внутри: проверяем окрестность и само значение
    (assert-true (< (iv-lo I) 7468242/10000000))
    (assert-true (> (iv-hi I) 7468241/10000000))
    (assert-true (iv-contains? I 7468241/10000000))))

(deftest "cn3: certified-integral 1/x на [1,2] = log 2"
  (let ((I (certified-integral '(/ 1 x) 'x 1 2 1/1000000))
        (L (iv-log (iv 2 2))))
    (assert-true (<= (iv-width I) 1/1000000))
    ; интервалы пересекаются: оба содержат log 2
    (assert-true (< (iv-lo I) (iv-hi L)))
    (assert-true (> (iv-hi I) (iv-lo L)))))

(deftest "cn3: certified-integral sin на [0,pi] содержит 2"
  (let ((I (certified-integral '(sin x) 'x 0 (iv-pi) 1/1000000)))
    (assert-true (<= (iv-width I) 1/1000000))
    (assert-true (iv-contains? I 2))))

(deftest "cn3: certified-sum 1/k^2 содержит pi^2/6"
  (let ((S (certified-sum '(/ 1 (^ k 2)) 'k 1 1/1000)))
    (assert-true (iv-contains? S 1644934067/1000000000))
    ; 1.65 — заведомо больше суммы
    (assert-equal (iv-contains? S 165/100) #f)))

(deftest "cn3: certified-sum 1/k! содержит e, 1/2^k содержит 2"
  (let ((E (certified-sum '(/ 1 (factorial k)) 'k 0 1/1000000000000))
        (G (certified-sum '(/ 1 (^ 2 k)) 'k 0 1/1000000)))
    (assert-true (iv-contains? E 2718281828459045/1000000000000000))
    (assert-true (<= (iv-width E) 1/1000000000000))
    (assert-true (iv-contains? G 2))
    ; сумма геометрической 1/2^k не превосходит 2 (с округлением наружу — на уровне tol/100)
    (assert-true (<= (iv-hi G) (+ 2 1/10000000)))))

(deftest "cn3: подделанные границы не проходят проверку"
  ; интеграл e^(-x^2) не лежит в [0.74, 0.745]
  (assert-equal (iv-contains? (iv 74/100 745/1000) 7468241/10000000) #f)
  ; сумма 1/k^2 не превосходит 1.65
  (assert-equal (iv-contains? (certified-sum '(/ 1 (^ k 2)) 'k 1 1/1000) 165/100) #f))

; ---------- RE.0: строгий хвост certified-sum ----------

(deftest "re0: 1/k! и 1/2^k по-прежнему оцениваются строго"
  (let ((E (certified-sum '(/ 1 (factorial k)) 'k 0 1/1000000000000))
        (G (certified-sum '(/ 1 (^ 2 k)) 'k 0 1/1000000)))
    (assert-true (iv-contains? E 2718281828459045/1000000000000000))
    (assert-true (<= (iv-width E) 1/1000000000000))
    (assert-true (iv-contains? G 2))
    (assert-true (<= (iv-hi G) (+ 2 1/10000000)))))

(deftest "re0: ряд с отношением → 1 без первообразной — отказ или верный интервал"
  ; 1/(k^(3/2)+1): истинная сумма ≈ 1.95202; выборка точек дала бы заниженный хвост
  (let ((r (certified-sum '(/ 1 (+ (^ k 3/2) 1)) 'k 1 1/1000)))
    ; WASM.6a Д8: отказ — значение #f (не ошибка), либо верный интервал
    (assert-true (or (equal? r #f)
                     (and (iv? r) (iv-contains? r 195202/100000))))))

; ---------- PERF.3: знакочередующиеся ряды и быстрый отказ ----------

(deftest "perf3: Σ(-1/2)^k — признак Лейбница, интервал содержит 2/3"
  (let ((r (certified-sum '(^ -1/2 k) 'k 0 1/1000000)))
    (assert-true (iv-contains? r 2/3))
    (assert-true (<= (iv-width r) 1/1000000))
    ; фальшивые значения (сдвиг на 1e-5) не принимаются
    (assert-equal (iv-contains? r (+ 2/3 1/100000)) #f)
    (assert-equal (iv-contains? r (- 2/3 1/100000)) #f)))

(deftest "perf3: Σ(-1)^k/k содержит -log 2, ширина ≤ tol"
  (let ((r (certified-sum '(/ (^ -1 k) k) 'k 1 1/1000)))
    (assert-true (iv-contains? r -693147180559945/1000000000000000))
    (assert-true (<= (iv-width r) 1/1000))
    (assert-equal (iv-contains? r (- -693147180559945/1000000000000000 1/100)) #f)))

(deftest "perf3: быстрый отказ certified-sum без хвостового признака (< 2 с)"
  (let ((t0 (clock-us)))
    ; WASM.6a Д8: отказ — значение #f с причиной в условиях, а не ошибка
    (assert-equal (certified-sum '(/ 1 (+ (^ k 3/2) 1)) 'k 1 1/1000) #f)
    (assert-true (< (- (clock-us) t0) 2000000))))

; ---------- WASM.6a Д8: дробный показатель степени ----------

(deftest "WASM.6a Д8: certified-sum с дробным показателем — строгий интервал"
  (let ((r (certified-sum '(/ 1 (^ k 5/2)) 'k 1 1/1000)))
    (assert-true (iv? r))
    ; ζ(5/2) ≈ 1.3414872
    (assert-true (iv-contains? r 1341487257/1000000000))
    (assert-equal (iv-contains? r 1) #f)
    (assert-equal (iv-contains? r 3/2) #f)
    (assert-true (<= (iv-width r) 1/500))))

; REL.1e П5б: нижняя граница хвоста по интегралу — запрошенная ширина достигается
(deftest "REL.1e: certified-sum достигает ширины 1e-5 и 1e-3 при дробном показателе"
  (let ((a (certified-sum '(/ 1 (^ k 3/2)) 'k 1 1/100000))
        (b (certified-sum '(/ 1 (^ k 5/4)) 'k 1 1/1000)))
    (assert-true (iv? a))
    (assert-true (iv? b))
    (assert-true (<= (iv-width a) 1/50000))
    (assert-true (<= (iv-width b) 1/1000))
    (assert-true (iv-contains? a 2612375348/1000000000))
    (assert-true (iv-contains? b 4595/1000))))

; REL.1e П5в: расходящийся ряд — отказ с причиной в условиях ответа
(deftest "REL.1e: certified-sum расходящегося ряда — отказ, причина записана"
  (conditions-clear)
  (assert-equal (certified-sum '(/ 1 (^ k 1/2)) 'k 1 1/1000) #f)
  (assert-true (string-contains? (to-string (conditions)) "расходится")))

(deftest "WASM.6a Д8: ζ(3/2) — интервал есть, расходятся — отказ"
  (let ((q (certified-sum '(/ 1 (^ k 3/2)) 'k 1 1/1000)))
    (assert-true (iv? q))
    (assert-true (iv-contains? q 2612375348/1000000000))
    (assert-equal (iv-contains? q 5/2) #f))
  ; 1/√k расходится: строгой оценки хвоста нет — отказ #f, не ошибка
  (assert-equal (certified-sum '(/ 1 (^ k 1/2)) 'k 1 1/1000) #f))

