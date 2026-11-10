; interval.lisp — интервальная арифметика с рациональными концами (шаг CN.1).
; Теорема о включении: если каждая операция возвращает интервал, содержащий все значения
; аргументов, то и составное выражение — тоже. Поэтому концы интервалов — ТОЧНЫЕ дроби
; (float запрещён), а значения exp/log/sin/cos/atan/pi получаются рядами Тейлора
; с явной оценкой остатка. Результат всегда верен, но может быть широким.
; Представление: (iv lo hi), lo <= hi, lo/hi — целые или рациональные.

(module interval
  (export iv? iv iv-lo iv-hi iv-width iv-mid iv-contains? iv-subset?
          iv+ iv- iv* iv/ iv-neg iv^ iv-sqrt iv-exp iv-log iv-sin iv-cos iv-atan
          iv-pi iv-e iv-eval iv-refine iv-set-precision! iv-precision
          isolate-roots refine-root certified-roots
          certified-integral certified-sum))

; ---------- точные помощники ----------

; (iv-rat? x) — x целое или рациональное (float не годится для концов)
(define (iv-rat? x) (or (integer? x) (equal? (type-of x) 'rational)))

(define (iv-abs-rat x) (if (< x 0) (- x) x))
(define (iv-min-rat a b) (if (<= a b) a b))
(define (iv-max-rat a b) (if (>= a b) a b))

; (iv-rat-pow q n) — q^n для точного q и целого n >= 0
(define (iv-rat-pow q n)
  (if (= n 0) 1 (/ (^ (numer q) n) (^ (denom q) n))))

; (iv-pow2-int k) — 2^k для целого k (в том числе отрицательного)
(define (iv-pow2-int k)
  (if (>= k 0) (^ 2 k) (/ 1 (^ 2 (- k)))))

; точность внутренних рядов: 1e-30 (концы — дроби, поэтому это лишь ориентир для остатка)
(define iv-eps (/ 1 (^ 10 30)))

; (iv-isqrt n) — floor(sqrt(n)) для целого n >= 0 (Ньютон на BigInt, без float)
(define (iv-isqrt-step n x)
  (let ((y (floor (/ (+ x (floor (/ n x))) 2))))
    (if (< y x) (iv-isqrt-step n y) x)))
(define (iv-isqrt n) (if (< n 2) n (iv-isqrt-step n n)))

; ---------- интервал и доступ ----------

; (iv lo hi) — интервал [lo, hi]; концы точные, lo <= hi
(define (iv lo hi)
  (if (not (and (iv-rat? lo) (iv-rat? hi)))
      (error "interval: концы должны быть точными числами (целыми или дробями)" lo hi))
  (if (> lo hi) (error "interval: левый конец больше правого" lo hi))
  (list 'iv lo hi))

; (iv? x) — x является интервалом
(define (iv? x)
  (and (list? x) (not (null? x)) (equal? (car x) 'iv) (= (length x) 3)))

; (iv-lo X), (iv-hi X) — концы интервала
(define (iv-lo X) (nth X 1))
(define (iv-hi X) (nth X 2))

; (iv-width X) — длина интервала (точная дробь)
(define (iv-width X) (- (iv-hi X) (iv-lo X)))

; (iv-mid X) — середина интервала (точная дробь)
(define (iv-mid X) (/ (+ (iv-lo X) (iv-hi X)) 2))

; (iv-contains? X q) — лежит ли точное число q в X
(define (iv-contains? X q) (and (<= (iv-lo X) q) (<= q (iv-hi X))))

; (iv-subset? A B) — A целиком внутри B
(define (iv-subset? A B) (and (>= (iv-lo A) (iv-lo B)) (<= (iv-hi A) (iv-hi B))))

; ---------- арифметика ----------

; (iv+ A B ...) — сумма интервалов: [a+c, b+d]
(define (iv-add2 A B) (iv (+ (iv-lo A) (iv-lo B)) (+ (iv-hi A) (iv-hi B))))
(define (iv+ &rest xs) (foldl iv-add2 (iv 0 0) xs))

; (iv-neg A) — [-b, -a]
(define (iv-neg A) (iv (- (iv-hi A)) (- (iv-lo A))))

; (iv- A [B]) — разность (или унарный минус)
(define (iv- A &rest rest)
  (if (null? rest)
      (iv-neg A)
      (iv-add2 A (iv-neg (car rest)))))

; (iv* A B ...) — произведение: минимум и максимум четырёх произведений концов
(define (iv-mul2 A B)
  (let* ((p1 (* (iv-lo A) (iv-lo B))) (p2 (* (iv-lo A) (iv-hi B)))
         (p3 (* (iv-hi A) (iv-lo B))) (p4 (* (iv-hi A) (iv-hi B))))
    (iv (iv-min-rat (iv-min-rat p1 p2) (iv-min-rat p3 p4))
        (iv-max-rat (iv-max-rat p1 p2) (iv-max-rat p3 p4)))))
(define (iv* &rest xs) (foldl iv-mul2 (iv 1 1) xs))

; (iv-scale X q) — умножение интервала на точное положительное q (быстрый частный случай)
(define (iv-scale X q) (iv (* (iv-lo X) q) (* (iv-hi X) q)))

; (iv-recip X) — 1/X; интервал, содержащий 0, делить нельзя
(define (iv-recip X)
  (if (and (<= (iv-lo X) 0) (>= (iv-hi X) 0))
      (error "interval: деление на интервал, содержащий 0" X)
      (iv (/ 1 (iv-hi X)) (/ 1 (iv-lo X)))))

; (iv/ A B ...) — деление на интервал, не содержащий 0
(define (iv/ A &rest rest)
  (foldl (lambda (acc B) (iv-mul2 acc (iv-recip B))) A rest))

; (iv^ X n) — целая степень; для чётной степени знак учитывается автоматически
(define (iv-pow-pos X n)
  (if (= n 1)
      X
      (let* ((h (iv-pow-pos X (quotient n 2)))
             (sq (iv-mul2 h h)))
        (if (= (* 2 (quotient n 2)) n) sq (iv-mul2 sq X)))))
(define (iv^ X n)
  (if (not (integer? n))
      (error "interval: степень должна быть целой" n))
  (cond ((= n 0) (iv 1 1))
        ((< n 0) (iv-recip (iv-pow-pos X (- n))))
        (else (iv-pow-pos X n))))

; ---------- квадратный корень ----------

; нижняя/верхняя рациональные границы sqrt(q) с точностью 1e-30 (q >= 0)
; sqrt(a/b) = sqrt(a*b)/b; floor берётся целочисленным Ньютоном.
(define iv-sqrt-prec (^ 10 30))
(define (iv-sqrt-bounds q)
  (if (< q 0)
      (error "interval: sqrt от отрицательного числа" q)
      (let* ((a (numer q)) (b (denom q))
             (n (* a b iv-sqrt-prec iv-sqrt-prec))
             (s (iv-isqrt n))
             (lo (/ s (* b iv-sqrt-prec))))
        (list lo (if (= (* s s) n) lo (/ (+ s 1) (* b iv-sqrt-prec)))))))

; (iv-sqrt X) — sqrt на неотрицательном интервале (монотонна: по концам)
(define (iv-sqrt X)
  (if (< (iv-lo X) 0)
      (error "interval: sqrt от интервала с отрицательным концом" X))
  (let ((lo (iv-sqrt-bounds (iv-lo X))) (hi (iv-sqrt-bounds (iv-hi X))))
    (iv (car lo) (cadr hi))))

; ---------- WASM.6a Д8: рациональные степени ----------

; (iv-iroot n q) — floor(n^(1/q)) для целого n >= 0 и целого q >= 1 (Ньютон на BigInt, без float)
(define (iv-iroot-step n q x)
  (let ((y (floor (/ (+ (* (- q 1) x) (floor (/ n (^ x (- q 1))))) q))))
    (if (< y x) (iv-iroot-step n q y) x)))
(define (iv-iroot n q) (if (or (< n 2) (= q 1)) n (iv-iroot-step n q n)))

; точность границ дробных степеней: 1e-12 (для сумм с tol 1e-3…1e-12 точности хватает с запасом;
; 1e-30 давал дроби в сотни цифр и замедлял certified-sum на порядки)
(define iv-rpow-prec (^ 10 12))

; нижняя/верхняя рациональные границы r^(1/q) с точностью iv-rpow-prec (r >= 0, q >= 1)
(define (iv-nroot-bounds r q)
  (if (= r 0)
      (list 0 0)
      (let* ((a (numer r)) (b (denom r)) (p iv-rpow-prec)
             (n (* a (^ b (- q 1)) (^ p q)))
             (s (iv-iroot n q))
             (lo (/ s (* b p))))
        (list lo (if (= (^ s q) n) lo (/ (+ s 1) (* b p)))))))

; (iv-rpow X p q) — X^(p/q) для X >= 0: корень по концам (монотонен), затем целая степень
(define (iv-rpow X p q)
  (if (< (iv-lo X) 0)
      (error "interval: дробная степень от интервала с отрицательным концом" X)
      (let ((lo (iv-nroot-bounds (iv-lo X) q)) (hi (iv-nroot-bounds (iv-hi X) q)))
        (iv^ (iv (car lo) (cadr hi)) p))))

; ---------- pi, e ----------

; (iv-atan-alt x) — atan(x) для |x| <= 1 знакочередующимся рядом
; atan x = x - x^3/3 + x^5/5 - ...; остаток не больше первого отброшенного члена.
; Именованного let в языке нет — шаг ряда вынесен в отдельную функцию.
(define (iv-atan-alt-step x k tk s sgn)
  (let ((s1 (+ s (* sgn tk))))
    (if (< tk iv-eps)
        (if (= sgn 1) (iv (- s1 tk) s1) (iv s1 (+ s1 tk)))
        (iv-atan-alt-step x (+ k 1)
                          (/ (* tk x x (+ (* 2 k) 1)) (+ (* 2 k) 3))
                          s1
                          (- sgn)))))
(define (iv-atan-alt x) (iv-atan-alt-step x 0 x 0 1))

; (iv-pi-raw) — pi через формулу Мэчина: pi = 16*atan(1/5) - 4*atan(1/239)
(define (iv-pi-raw)
  (let* ((a (iv-atan-alt 1/5)) (b (iv-atan-alt 1/239)))
    (iv (- (* 16 (iv-lo a)) (* 4 (iv-hi b)))
        (- (* 16 (iv-hi a)) (* 4 (iv-lo b))))))

; (iv-pi) — строгий интервал для pi (вычисляется один раз)
(define iv-pi-cache #f)
(define (iv-pi)
  (if iv-pi-cache
      iv-pi-cache
      (begin (set! iv-pi-cache (iv-pi-raw)) iv-pi-cache)))

; (iv-e) — строгий интервал для e = exp(1)
(define iv-e-cache #f)
(define (iv-e)
  (if iv-e-cache
      iv-e-cache
      (begin (set! iv-e-cache (iv-exp (iv 1 1))) iv-e-cache)))

; (iv-set-precision! d) — точность рядов и корней 10^-d (по умолчанию 30); кэши pi, e, log 2 сбрасываются.
; Все результаты остаются строгими включениями, меняется только ширина (R4: уточнение при проверке нуля констант).
(define iv-digits 30)
(define (iv-set-precision! d)
  (set! iv-digits d)
  (set! iv-eps (/ 1 (^ 10 d)))
  (set! iv-sqrt-prec (^ 10 d))
  (set! iv-pi-cache #f)
  (set! iv-e-cache #f)
  (set! iv-log2-cache #f)
  d)
; (iv-precision) — текущее число десятичных знаков
(define (iv-precision) iv-digits)

; ---------- exp ----------

; (iv-exp-rem m j) — оценка хвоста ряда exp: 2*m^j/j! (при |x| <= m <= 1/2, e^m <= 2)
(define (iv-exp-rem m j) (/ (* 2 (iv-rat-pow m j)) (factorial j)))

; (iv-exp-taylor Y) — e^Y для интервала Y с |Y| <= 1/2; ряд с остатком в форме Лагранжа
(define (iv-exp-taylor-step Y m j p f s)
  (let* ((j1 (+ j 1))
         (f1 (* f j1))
         (p1 (iv-mul2 p Y))
         (s1 (iv+ s (iv-scale p1 (/ 1 f1)))))
    (if (< (iv-exp-rem m j1) iv-eps)
        (let ((r (iv-exp-rem m j1)))
          (iv (- (iv-lo s1) r) (+ (iv-hi s1) r)))
        (iv-exp-taylor-step Y m j1 p1 f1 s1))))
(define (iv-exp-taylor Y)
  (let ((m (iv-max-rat (iv-abs-rat (iv-lo Y)) (iv-abs-rat (iv-hi Y)))))
    (iv-exp-taylor-step Y m 0 (iv 1 1) 1 (iv 1 1))))

; (iv-exp-shift m) — наименьшее k с m/2^k <= 1/2 (аргумент для сведения к ряду)
(define (iv-exp-shift-step m k p)
  (if (<= m (/ p 2)) k (iv-exp-shift-step m (+ k 1) (* p 2))))
(define (iv-exp-shift m) (iv-exp-shift-step m 0 1))

; (iv-square-n r k) — r^(2^k) повторным возведением в квадрат
(define (iv-square-n r i k)
  (if (= i k) r (iv-square-n (iv-mul2 r r) (+ i 1) k)))

; (iv-exp-point q) — e^q для точного q; e^x = (e^(x/2^k))^(2^k)
(define (iv-exp-point q)
  (cond ((< q 0) (iv-recip (iv-exp-point (- q))))
        ((<= q 1/2) (iv-exp-taylor (iv q q)))
        (else
         (let* ((k (iv-exp-shift q))
                (y (/ q (iv-pow2-int k)))
                (s (iv-exp-taylor (iv y y))))
           (iv-square-n s 0 k)))))

; (iv-exp X) — e^x на интервале (монотонна: по концам)
(define (iv-exp X) (iv (iv-lo (iv-exp-point (iv-lo X))) (iv-hi (iv-exp-point (iv-hi X)))))

; ---------- log ----------

; (iv-log2-floor q) — floor(log2 q) для точного q > 0
(define (iv-log2-floor-big q k p)
  (if (<= (* 2 p) q) (iv-log2-floor-big q (+ k 1) (* 2 p)) k))
(define (iv-log2-floor-small q k r)
  (if (>= r 1) k (iv-log2-floor-small q (- k 1) (* 2 r))))
(define (iv-log2-floor q)
  (if (>= q 1) (iv-log2-floor-big q 0 1) (iv-log2-floor-small q 0 q)))

; (iv-log-atanh z) — log((1+z)/(1-z))/2 = z + z^3/3 + ... для 0 <= z <= 3/5; все члены положительны
(define (iv-log-atanh-step z k p s)
  (let* ((k1 (+ k 1))
         (p1 (* p z z))
         (t1 (/ p1 (+ (* 2 k1) 1)))
         (s1 (+ s t1)))
    (if (< (* t1 25/16) iv-eps)
        (iv (* 2 s1) (* 2 (+ s1 (* t1 25/16))))
        (iv-log-atanh-step z k1 p1 s1))))
(define (iv-log-atanh z) (if (= z 0) (iv 0 0) (iv-log-atanh-step z 0 z z)))

; (iv-log2) — строгий интервал для log 2 = 2*atanh(1/3) (вычисляется один раз)
(define iv-log2-cache #f)
(define (iv-log2)
  (if iv-log2-cache
      iv-log2-cache
      (begin (set! iv-log2-cache (iv-log-atanh 1/3)) iv-log2-cache)))

; (iv-log-point q) — log q для точного q > 0: сведение q = M*2^k, M in [1,2)
(define (iv-log-point q)
  (cond ((<= q 0) (error "interval: log от неположительного числа" q))
        ((< q 1) (iv-neg (iv-log-point (/ 1 q))))
        (else
         (let* ((k (iv-log2-floor q))
                (m (/ q (iv-pow2-int k)))
                (z (/ (- m 1) (+ m 1)))
                (l (iv-log-atanh z))
                (klog2 (iv* (iv-log2) (iv k k))))
           (iv+ klog2 l)))))

; (iv-log X) — log на строго положительном интервале (монотонна: по концам)
(define (iv-log X)
  (if (<= (iv-lo X) 0)
      (error "interval: log от интервала, содержащего неположительные числа" X))
  (iv (iv-lo (iv-log-point (iv-lo X))) (iv-hi (iv-log-point (iv-hi X)))))

; ---------- sin, cos ----------

; (iv-sin-terms m n term) — минимальное n с m^(2n+3)/(2n+3)! < 1e-30
(define (iv-sin-terms m n term)
  (if (< term iv-eps)
      n
      (iv-sin-terms m (+ n 1) (/ (* term m m) (* (+ (* 2 n) 4) (+ (* 2 n) 5))))))
(define (iv-sin-terms-of m) (iv-sin-terms m 0 (/ (* m m m) 6)))

; (iv-sin-point-fast x) — sin x для точного |x| <= 2.
; Слагаемые приводятся к общему знаменателю Q = D^(2n+1)*(2n+1)!:
; числитель j-го члена = N^(2j+1)*D^(2(n-j))*(2n+1)!/(2j+1)! — целые, без gcd на каждом шаге;
; сокращение дроби одно, в конце. Остаток — по Лагранжу: |R| <= m^(2n+3)/(2n+3)!.
(define (iv-sin-num-step N2 D2 n j powN powD R T)
  (if (> j n)
      T
      (let* ((term (* powN powD R))
             (T1 (if (= (remainder j 2) 0) (+ T term) (- T term))))
        (iv-sin-num-step N2 D2 n (+ j 1)
                         (* powN N2)
                         (quotient powD D2)
                         (if (= j n) R (quotient R (* (+ (* 2 j) 2) (+ (* 2 j) 3))))
                         T1))))
(define (iv-sin-point-fast x)
  (if (= x 0)
      (iv 0 0)
      (let* ((m (iv-abs-rat x))
             (n (iv-sin-terms-of m))
             (N (numer x)) (D (denom x))
             (N2 (* N N)) (D2 (* D D))
             (fact (factorial (+ (* 2 n) 1)))
             (T (iv-sin-num-step N2 D2 n 0 N (iv-rat-pow D (* 2 n)) fact 0))
             (Q (* (iv-rat-pow D (+ (* 2 n) 1)) fact))
             (S (/ T Q))
             (r (/ (iv-rat-pow m (+ (* 2 n) 3)) (factorial (+ (* 2 n) 3)))))
        (iv (- S r) (+ S r)))))

; (iv-sin-series X) — sin на интервале X, |X| <= 2: концы + поправка Липшица (|sin'| <= 1)
(define (iv-sin-series X)
  (let* ((w (iv-width X))
         (a (iv-sin-point-fast (iv-lo X)))
         (b (iv-sin-point-fast (iv-hi X))))
    (iv (- (iv-min-rat (iv-lo a) (iv-lo b)) w)
        (+ (iv-max-rat (iv-hi a) (iv-hi b)) w))))

; (iv-sin-point x) — sin в точке
(define (iv-sin-point x) (iv-sin-point-fast x))

; (iv-nearest-int q) — ближайшее целое к точному q
(define (iv-nearest-int q) (floor (+ q 1/2)))

; (iv-intersect A B) — пересечение интервалов (или #f, если пусто)
(define (iv-intersect A B)
  (let ((lo (iv-max-rat (iv-lo A) (iv-lo B))) (hi (iv-min-rat (iv-hi A) (iv-hi B))))
    (if (> lo hi) #f (iv lo hi))))

; (iv-sin X) — sin на интервале: приведение по 2*pi, затем кусок монотонности или ряд
(define (iv-sin X)
  (let* ((pi (iv-pi))
         (two-pi (iv-scale pi 2))
         (k (iv-nearest-int (iv-mid (iv/ X two-pi))))
         (r (iv- X (iv* two-pi (iv k k))))
         (hp (iv-scale pi 1/2))
         (tp (iv-scale pi 3/2))
         (m (iv-max-rat (iv-abs-rat (iv-lo r)) (iv-abs-rat (iv-hi r))))
         (res
          (cond ((and (>= (iv-lo r) (- (iv-hi hp))) (<= (iv-hi r) (iv-lo hp)))
                 (iv (iv-lo (iv-sin-point (iv-lo r))) (iv-hi (iv-sin-point (iv-hi r)))))
                ((and (>= (iv-lo r) (iv-hi hp)) (<= (iv-hi r) (iv-lo tp)))
                 (iv (iv-lo (iv-sin-point (iv-hi r))) (iv-hi (iv-sin-point (iv-lo r)))))
                ((<= m 2) (iv-sin-series r))
                ((<= (iv-hi r) (- (iv-hi hp))) (iv-neg (iv-sin (iv+ r pi))))
                ((>= (iv-lo r) (iv-hi tp)) (iv-neg (iv-sin (iv- r pi))))
                (else (iv -1 1)))))
    (iv-intersect res (iv -1 1))))

; (iv-cos X) — cos x = sin(x + pi/2)
(define (iv-cos X) (iv-sin (iv+ X (iv-scale (iv-pi) 1/2))))

; ---------- atan ----------

; (iv-atan-small X) — atan на X внутри [-1,1]: |x| <= 1/2 — ряд,
; иначе atan x = pi/4 + atan((x-1)/(x+1)) (аргумент попадает в [-1/3, 0])
(define (iv-atan-small X)
  (cond ((<= (iv-hi X) 1/2)
         (iv (iv-lo (iv-atan-alt (iv-lo X))) (iv-hi (iv-atan-alt (iv-hi X)))))
        ((>= (iv-lo X) 1/2)
         (let ((t (iv/ (iv- X (iv 1 1)) (iv+ X (iv 1 1)))))
           (iv+ (iv-scale (iv-pi) 1/4) (iv-atan-small t))))
        ((<= (iv-hi X) -1/2)
         (iv-neg (iv-atan-small (iv-neg X))))
        (else
         (iv-union-list (list (iv-atan-small (iv (iv-lo X) 1/2))
                              (iv-atan-small (iv 1/2 (iv-hi X))))))))

; (iv-atan-point q) — atan q для точного q
(define (iv-atan-point q)
  (cond ((< q 0) (iv-neg (iv-atan-point (- q))))
        ((> q 1) (iv- (iv-scale (iv-pi) 1/2) (iv-atan-point (/ 1 q))))
        (else (iv-atan-small (iv q q)))))

; (iv-atan X) — atan на интервале (монотонна: по концам)
(define (iv-atan X) (iv (iv-lo (iv-atan-point (iv-lo X))) (iv-hi (iv-atan-point (iv-hi X)))))

; ---------- вычисление выражений ----------

; (iv-eval e x X) — включение значения выражения e при x из X:
; поддерживаются + - * / ^ exp log sin cos atan sqrt и константы pi, e
(define (iv-eval e x X)
  (cond ((iv-rat? e) (iv e e))
        ((equal? (type-of e) 'float)
         (error "iv-eval: float недопустим, нужно точное число" e))
        ((symbol? e)
         (cond ((equal? e x) X)
               ((or (equal? e 'pi) (equal? e '%pi)) (iv-pi))
               ((or (equal? e 'e) (equal? e '%e)) (iv-e))
               (else (error "iv-eval: неизвестный символ" e))))
        ((list? e)
         (let ((h (car e)) (args (cdr e)))
           (cond ((equal? h '+) (apply iv+ (map (lambda (a) (iv-eval a x X)) args)))
                 ((equal? h '*)
                  (if (null? args) (iv 1 1)
                      (apply iv* (map (lambda (a) (iv-eval a x X)) args))))
                 ((equal? h '-)
                  (cond ((null? args) (error "iv-eval: пустой минус"))
                        ((null? (cdr args)) (iv-neg (iv-eval (car args) x X)))
                        (else (apply iv- (map (lambda (a) (iv-eval a x X)) args)))))
                 ((equal? h '/)
                  (cond ((null? args) (error "iv-eval: пустой /"))
                        ((null? (cdr args)) (iv/ (iv 1 1) (iv-eval (car args) x X)))
                        (else (apply iv/ (map (lambda (a) (iv-eval a x X)) args)))))
                 ((equal? h '^)
                  (let ((base (iv-eval (car args) x X))
                        (k (iv-eval (cadr args) x X)))
                    (cond ((or (not (iv? k)) (not (= (iv-lo k) (iv-hi k))))
                           (error "iv-eval: показатель степени должен быть постоянным" (cadr args)))
                          ((integer? (iv-lo k)) (iv^ base (iv-lo k)))
                          ; Д8 (WASM.6a): рациональный показатель при неотрицательном основании
                          ((>= (iv-lo base) 0)
                           (iv-rpow base (numer (iv-lo k)) (denom (iv-lo k))))
                          (else (error "iv-eval: дробная степень отрицательного основания" (cadr args))))))
                 ((equal? h 'exp) (iv-exp (iv-eval (car args) x X)))
                 ((equal? h 'log) (iv-log (iv-eval (car args) x X)))
                 ((equal? h 'sin) (iv-sin (iv-eval (car args) x X)))
                 ((equal? h 'cos) (iv-cos (iv-eval (car args) x X)))
                 ((equal? h 'atan) (iv-atan (iv-eval (car args) x X)))
                 ((equal? h 'sqrt) (iv-sqrt (iv-eval (car args) x X)))
                 ((equal? h 'factorial)
                  (let ((n (iv-eval (car args) x X)))
                    (if (or (not (= (iv-lo n) (iv-hi n))) (not (integer? (iv-lo n)))
                            (< (iv-lo n) 0))
                        (error "iv-eval: factorial от нецелого или отрицательного" (car args))
                        (iv (factorial (iv-lo n)) (factorial (iv-lo n))))))
                 ((equal? h 'binomial)
                  (let ((n (iv-eval (car args) x X)) (m (iv-eval (cadr args) x X)))
                    (if (or (not (= (iv-lo n) (iv-hi n))) (not (integer? (iv-lo n)))
                            (not (= (iv-lo m) (iv-hi m))) (not (integer? (iv-lo m))))
                        (error "iv-eval: binomial от нецелых" (car args) (cadr args))
                        (iv (binomial (iv-lo n) (iv-lo m)) (binomial (iv-lo n) (iv-lo m))))))
                 (else (error "iv-eval: операция не поддерживается" h)))))
        (else (error "iv-eval: недопустимое выражение" e))))

; ---------- уточнение бисекцией ----------

; (iv-union-list items) — выпуклая оболочка интервалов
(define (iv-union-list xs)
  (foldl (lambda (acc Y) (iv (iv-min-rat (iv-lo acc) (iv-lo Y)) (iv-max-rat (iv-hi acc) (iv-hi Y))))
         (car xs) (cdr xs)))

; индекс самого широкого элемента списка
(define (iv-widest-step items i best bw)
  (if (>= i (length items))
      best
      (let ((w (iv-width (car (nth items i)))))
        (if (> w bw) (iv-widest-step items (+ i 1) i w) (iv-widest-step items (+ i 1) best bw)))))
(define (iv-widest-index items) (iv-widest-step items 0 0 -1))

; замена элемента i на список замен (список растёт на 1)
(define (iv-splice items i repl)
  (append (take items i) (append repl (drop items (+ i 1)))))

; (iv-refine e x X tol) — бисекция X, пока ширина включения не станет <= tol
; (или пока не исчерпан лимит 200 делений); возвращает интервал-оболочку
(define (iv-refine-step e x items n tol)
  (let ((u (iv-union-list (map cadr items))))
    (if (or (<= (iv-width u) tol) (>= n 200))
        u
        (let* ((i (iv-widest-index items))
               (p (car (nth items i)))
               (m (iv-mid p)))
          (if (<= (iv-width p) 0)
              u
              (iv-refine-step
               e x
               (iv-splice items i
                          (list (list (iv (iv-lo p) m) (iv-eval e x (iv (iv-lo p) m)))
                                (list (iv m (iv-hi p)) (iv-eval e x (iv m (iv-hi p))))))
               (+ n 1) tol))))))
(define (iv-refine e x X tol)
  (iv-refine-step e x (list (list X (iv-eval e x X))) 0 tol))

; ================= CN.2: изоляция корней =================

; (iv-root-far r B) — [-B, B], содержащий алгебраическое число r (B удваивается)
(define (iv-root-far r B)
  (if (and (< (alg-compare r B) 0) (> (alg-compare r (- B)) 0))
      (iv (- B) B)
      (iv-root-far r (* 2 B))))

; (iv-bisect-alg r I tol) — бисекция I по точному сравнению с алгебраическим r
(define (iv-bisect-alg r I tol)
  (if (<= (iv-width I) tol)
      I
      (let* ((m (iv-mid I)) (c (alg-compare r m)))
        (cond ((= c 0) (iv m m))
              ((< c 0) (iv-bisect-alg r (iv (iv-lo I) m) tol))
              (else (iv-bisect-alg r (iv m (iv-hi I)) tol))))))

; (iv-root-interval r tol) — рациональный интервал вокруг корня (точного или алгебраического)
(define (iv-root-interval r tol)
  (if (iv-rat? r) (iv r r) (iv-bisect-alg r (iv-root-far r 1) tol)))

; (iv-root-inside? r I) — корень r лежит в I
(define (iv-root-inside? r I)
  (if (iv-rat? r)
      (iv-contains? I r)
      (and (>= (alg-compare r (iv-lo I)) 0) (<= (alg-compare r (iv-hi I)) 0))))

; (iv-separator r1 r2 lo hi) — рациональное q с r1 < q < r2 (бисекция)
(define (iv-separator r1 r2 lo hi n)
  (let ((q (/ (+ lo hi) 2)))
    (cond ((and (< (alg-compare r1 q) 0) (> (alg-compare r2 q) 0)) q)
          ((>= (alg-compare r1 q) 0) (iv-separator r1 r2 q hi (- n 1)))
          (else (iv-separator r1 r2 lo q (- n 1))))))

; развести пересекающиеся соседние интервалы (корни различны, поэтому разделитель есть)
(define (iv-disjoint-pass items acc)
  (if (null? items)
      (reverse acc)
      (if (null? acc)
          (iv-disjoint-pass (cdr items) (list (car items)))
          (let* ((cur (car items)) (prev (car acc))
                 (r1 (car prev)) (r2 (car cur))
                 (I1 (cdr prev)) (I2 (cdr cur)))
            (if (<= (iv-hi I1) (iv-lo I2))
                (iv-disjoint-pass (cdr items) (cons cur acc))
                (let ((q (iv-separator r1 r2 (iv-lo I2) (iv-hi I1) 200)))
                  (iv-disjoint-pass (cdr items)
                                    (cons (cons r2 (iv q (iv-hi I2)))
                                          (cons (cons r1 (iv (iv-lo I1) q)) (cdr acc))))))))))

; (isolate-roots p x) — непересекающиеся рациональные интервалы, в каждом ровно один
; вещественный корень многочлена p (изоляция — Штурм, real-roots; концы — точные дроби)
(define (isolate-roots p x)
  (let ((pairs (map (lambda (r) (cons r (iv-root-interval r 1/100000000000000000000)))
                    (real-roots p x))))
    (map cdr (iv-disjoint-pass pairs '()))))

; (refine-root p x I tol) — сузить интервал I (ровно один корень p) до ширины <= tol
(define (refine-root-find rs I)
  (cond ((null? rs) #f)
        ((iv-root-inside? (car rs) I) (car rs))
        (else (refine-root-find (cdr rs) I))))
(define (refine-root p x I tol)
  (let ((r (refine-root-find (real-roots p x) I)))
    (if (not r)
        (error "refine-root: в интервале нет вещественного корня" I)
        (if (iv-rat? r) (iv r r) (iv-bisect-alg r I tol)))))

; ================= CN.2: гарантированные корни (Кравчик) =================

; сетка 1e-20: концы сертифицированных интервалов округляются НАРУЖУ, иначе знаменатели
; (π в аргументе sin/cos + факториалы ряда) растут лавинообразно и следующий вызов cos
; в середине такого интервала считается минутами.
(define iv-round-prec (^ 10 20))
(define (iv-round-out X)
  (iv (/ (floor (* (iv-lo X) iv-round-prec)) iv-round-prec)
      (/ (- (floor (* (- (iv-hi X)) iv-round-prec))) iv-round-prec)))

; (cr-narrow f df x X Y K tol n) — уточнение сертифицированного интервала оператором Кравчика
(define (cr-narrow f df x X Y K tol n)
  (let ((Xn (iv-intersect X K)))
    (cond ((not Xn) X)
          ((or (= n 0) (<= (iv-width Xn) tol) (>= (iv-width Xn) (iv-width X)))
           (iv-round-out Xn))
          (else
           (let* ((Xr (iv-round-out Xn))
                  (m (iv-mid Xr)) (mx (iv m m))
                  (Kn (iv+ (iv- mx (iv* Y (iv-eval f x mx)))
                           (iv* (iv- (iv 1 1) (iv* Y (iv-eval df x Xr)))
                                (iv- Xr mx)))))
             (cr-narrow f df x Xr Y Kn tol (- n 1)))))))

; (cr-split f df x work cert unres X d tol maxd) — деление клетки или честная запись в «не решено»
(define (cr-split f df x work cert unres X d tol maxd)
  (if (or (>= d maxd) (<= (iv-width X) 1/1000000000000000))
      (cr-run f df x (cdr work) tol maxd cert (cons X unres))
      (let ((m (iv-mid X)))
        (cr-run f df x
                (cons (cons (iv (iv-lo X) m) (+ d 1))
                      (cons (cons (iv m (iv-hi X)) (+ d 1)) (cdr work)))
                tol maxd cert unres))))

; (cr-run f df x work tol maxd cert unres) — обход клеток; сертификат — K(X) внутри X
(define (cr-run f df x work tol maxd cert unres)
  (if (null? work)
      (list (reverse cert) (reverse unres))
      (let* ((item (car work)) (X (car item)) (d (cdr item))
             (fX (iv-eval f x X)))
        (if (not (iv-contains? fX 0))
            (cr-run f df x (cdr work) tol maxd cert unres)
            (let* ((m (iv-mid X)) (mx (iv m m))
                   (fm (iv-eval f x mx))
                   (dfX (iv-eval df x X))
                   (dm (iv-eval df x mx)))
              (if (iv-contains? dm 0)
                  (cr-split f df x work cert unres X d tol maxd)
                  (let* ((Y (iv-recip dm))
                         (K (iv+ (iv- mx (iv* Y fm))
                                 (iv* (iv- (iv 1 1) (iv* Y dfX))
                                      (iv- X mx)))))
                    (if (and (> (iv-lo K) (iv-lo X)) (< (iv-hi K) (iv-hi X)))
                        (cr-run f df x (cdr work) tol maxd
                                (cons (cr-narrow f df x X Y K tol 15) cert) unres)
                        (cr-split f df x work cert unres X d tol maxd)))))))))

; слияние перекрывающихся интервалов (один корень мог сертифицироваться в соседних клетках)
(define (iv-merge-pass lst acc)
  (cond ((null? lst) (reverse acc))
        ((null? acc) (iv-merge-pass (cdr lst) (list (car lst))))
        (else
         (let ((cur (car lst)) (prev (car acc)))
           (if (<= (iv-lo cur) (iv-hi prev))
               (iv-merge-pass (cdr lst)
                              (cons (iv (iv-lo prev) (iv-max-rat (iv-hi prev) (iv-hi cur))) (cdr acc)))
               (iv-merge-pass (cdr lst) (cons cur acc)))))))
(define (iv-merge-sorted lst)
  (iv-merge-pass (sort lst (lambda (A B) (< (iv-lo A) (iv-lo B)))) '()))

; (certified-roots f x a b tol) — (сертифицированные неразрешимые)
; На клетке X: если K(X) = m - Y*f(m) + (1 - Y*f'(X))*(X - m) лежит внутри X (Y = 1/f'(m)),
; то по теореме Кравчика в X ровно один корень. Клетки без смены знака f отбрасываются,
; остальные делятся до глубины 40; не доказанные — во втором списке (честно).
(define (certified-roots f x a b tol)
  (let* ((df (diff x f))
         (A (iv-bound a)) (B (iv-bound b))
         (r (cr-run f df x (list (cons (iv (iv-lo A) (iv-hi B)) 0)) tol 40 '() '())))
    (list (iv-merge-sorted (car r)) (iv-merge-sorted (cadr r)))))

; ================= CN.3: гарантированные интегралы =================

; (ci-panel f f2 f4 f5 x lo hi) — интервал для ∫ по панели [lo,hi]:
; формула Тейлора 4-го порядка в середине + остаток через max|f^(5)|:
; ∫ ≈ h*f(m) + h^3/24*f''(m) + h^5/1920*f''''(m), |R| <= M5*h^6/23040
(define (ci-panel f f2 f4 f5 x lo hi)
  (let* ((m (/ (+ lo hi) 2))
         (h (- hi lo))
         (fm (iv-eval f x (iv m m)))
         (f2m (iv-eval f2 x (iv m m)))
         (f4m (iv-eval f4 x (iv m m)))
         (f5x (iv-eval f5 x (iv lo hi)))
         (m5 (iv-max-rat (iv-abs-rat (iv-lo f5x)) (iv-abs-rat (iv-hi f5x))))
         (h3 (/ (* h h h) 24))
         (h5 (/ (iv-rat-pow h 5) 1920))
         (c (iv+ (iv* fm (iv h h))
                 (iv* f2m (iv h3 h3))
                 (iv* f4m (iv h5 h5))))
         (r (/ (* m5 (iv-rat-pow h 6)) 23040)))
    (iv (- (iv-lo c) r) (+ (iv-hi c) r))))

; (ci-init ...) — n равных панелей на [lo,hi]
(define (ci-init-step f f2 f4 f5 x lo hi n i acc)
  (if (= i n)
      (reverse acc)
      (let* ((a (+ lo (/ (* (- hi lo) i) n)))
             (b (+ lo (/ (* (- hi lo) (+ i 1)) n))))
        (ci-init-step f f2 f4 f5 x lo hi n (+ i 1)
                      (cons (list a b (ci-panel f f2 f4 f5 x a b)) acc)))))

(define (ci-total panels)
  (foldl (lambda (acc p) (iv+ acc (nth p 2))) (iv 0 0) panels))

(define (ci-widest-step panels i best bw)
  (if (>= i (length panels))
      best
      (let ((w (iv-width (nth (nth panels i) 2))))
        (if (> w bw)
            (ci-widest-step panels (+ i 1) i w)
            (ci-widest-step panels (+ i 1) best bw)))))
(define (ci-widest panels) (ci-widest-step panels 0 0 -1))

; (ci-loop ...) — делим панель с наибольшей шириной, пока общая ширина > tol (лимит 300 панелей)
(define (ci-loop f f2 f4 f5 x panels tol n)
  (let ((total (ci-total panels)))
    (if (or (<= (iv-width total) tol) (>= n 300))
        total
        (let* ((i (ci-widest panels))
               (p (nth panels i))
               (lo (nth p 0)) (hi (nth p 1)) (m (/ (+ lo hi) 2))
               (p1 (list lo m (ci-panel f f2 f4 f5 x lo m)))
               (p2 (list m hi (ci-panel f f2 f4 f5 x m hi)))
               (new (append (take panels i) (cons p1 (cons p2 (drop panels (+ i 1)))))))
          (ci-loop f f2 f4 f5 x new tol (+ n 1))))))

; (iv-bound v) — граница отрезка: число, интервал или константное выражение (pi, e)
(define (iv-bound v)
  (cond ((iv? v) v)
        ((number? v) (iv v v))
        (else (iv-eval v 'iv-const (iv 0 0)))))

; (certified-integral f x a b tol) — интервал, содержащий ∫_a^b f.
; a и b — точные числа или интервалы; если интервалы, к ядру добавляется
; M*(ширина a + ширина b) (M = sup|f| на оболочке) — оценка изменения интеграла.
(define (certified-integral f x a b tol)
  (let* ((A (iv-bound a))
         (B (iv-bound b))
         (lo (iv-lo A)) (hi (iv-hi B))
         (f1 (diff x f)) (f2 (diff x f1)) (f3 (diff x f2))
         (f4 (diff x f3)) (f5 (diff x f4)))
    (if (> lo hi)
        (error "certified-integral: левая граница больше правой" a b)
        (let* ((core (ci-loop f f2 f4 f5 x
                              (ci-init-step f f2 f4 f5 x lo hi 8 0 '()) tol 0))
               (fv (iv-eval f x (iv lo hi)))
               (M (iv-max-rat (iv-abs-rat (iv-lo fv)) (iv-abs-rat (iv-hi fv))))
               (extra (* M (+ (iv-width A) (iv-width B)))))
          (iv (- (iv-lo core) extra) (+ (iv-hi core) extra))))))

; ================= CN.3: гарантированные суммы =================

; (cs-partial term k a n acc) — частичная сумма a..n (интервалы, точные слагаемые)
; grid — шаг округления НАРУЖУ накопленной суммы: без него знаменатели слагаемых
; перемножаются (НОК k·10^12), и сумма 8192 членов идёт минутами (WASM.6a Д8)
; (cs-round-to X q) — округление концов наружу до шага 1/q (q — целое)
(define (cs-round-to X q)
  (iv (/ (floor (* (iv-lo X) q)) q) (/ (ceiling (* (iv-hi X) q)) q)))

(define (cs-partial term k a n acc grid)
  (if (> a n)
      acc
      (cs-partial term k (+ a 1) n
                  (cs-round-to (iv+ acc (iv-eval term k (iv a a))) grid)
                  grid)))

; ---------- RE.0: строгая оценка отношения t(k+1)/t(k) на [N, ∞) ----------

; (cs-ratio-expr t k) — ρ(k) = t(k+1)/t(k) как выражение, разбирая t как произведение
; атомов: число → 1, k → (k+1)/k, (factorial (k+m)) → k+m+1, (^ base e) с целым e → ρ(base)^e.
; Если форма не разбирается (например, (^ k 3/2) в сумме) — #f (честный отказ, не выборка).
(define (cs-ratio-product fs k)
  (if (null? fs)
      1
      (let ((r (cs-ratio-expr (car fs) k)))
        (if (not r)
            #f
            (let ((rest (cs-ratio-product (cdr fs) k)))
              (if rest (simplify (list '* r rest)) #f))))))

(define (cs-ratio-expr t k)
  (cond ((number? t) 1)
        ((symbol? t) (if (equal? t k) (simplify (/ (+ k 1) k)) #f))
        ((pair? t)
         (let ((h (car t)))
           (cond ((equal? h '*) (cs-ratio-product (cdr t) k))
                 ((equal? h '/)
                  (let ((a (cs-ratio-expr (cadr t) k)) (b (cs-ratio-expr (caddr t) k)))
                    (if (and a b) (simplify (/ a b)) #f)))
                 ((equal? h '^)
                  (let ((e (caddr t)) (base (cadr t)))
                    (cond ((integer? e)
                           (let ((r (cs-ratio-expr base k)))
                             (if r (simplify (list '^ r e)) #f)))
                          ; (^ c k) с постоянным c: отношение равно c
                          ((and (equal? e k) (number? base)) base)
                          (else #f))))
                 ((equal? h 'factorial)
                  (let ((arg (cadr t)))
                    (cond ((equal? arg k) (simplify (+ k 1)))
                          ((and (pair? arg) (equal? (car arg) '+)
                                (equal? (cadr arg) k) (number? (caddr arg)))
                           (simplify (+ k (caddr arg) 1)))
                          (else #f))))
                 (else #f))))
        (else #f)))

; (cs-ratio-bound rho k N) — верхняя граница ρ на [N, ∞): подстановка k = 1/s,
; s ∈ [0, 1/N], интервальная оценка; #f, если выражение не рационально по s
; или не определено на всём отрезке.
(define (cs-ratio-range rho k N)
  (let* ((q1 (try (simplify (together rho)) (lambda (e) #f))))
    (if (not q1)
        #f
        (let ((sub (try (subst (list k (/ 1 'rs-s)) q1) (lambda (e) #f))))
          (if (not sub)
              #f
              (let ((q2 (try (simplify (together sub)) (lambda (e) #f))))
                (if (not q2)
                    #f
                    (let ((r (try (iv-eval q2 'rs-s (iv 0 (/ 1 N))) (lambda (e) #f))))
                      (if (iv? r) r #f)))))))))

(define (cs-ratio-bound rho k N)
  (let ((r (cs-ratio-range rho k N)))
    (if (and r (< (iv-hi r) 1)) r #f)))

; (cs-tail-geom term k N) — хвост по геометрической мажоранте t(N+1)/(1-q),
; q — СТРОГАЯ верхняя граница отношения t(k+1)/t(k) на всём [N, ∞).
(define (cs-tail-geom term k N)
  (let* ((rho (cs-ratio-expr term k))
         (tN (try (iv-eval term k (iv N N)) (lambda (e) #f)))
         (tN1 (try (iv-eval term k (iv (+ N 1) (+ N 1))) (lambda (e) #f))))
    (if (or (not rho) (not tN) (not tN1) (<= (iv-hi tN) 0) (<= (iv-hi tN1) 0))
        #f
        (let ((q (cs-ratio-bound rho k N)))
          (if (not q)
              #f
              (iv 0 (/ (iv-hi tN1) (- 1 (iv-hi q)))))))))

; (cs-hard-limit? F k) — первообразная, для которой limit заведомо дорог и обычно не
; даёт числа: дробная степень вместе с log/atan (вроде 1/(k^(3/2)+1): ≈ 8 с и отказ).
; Это только быстрый отказ от дорогой попытки, на строгость не влияет.
(define (cs-scan F)
  ; список флагов: 1 — дробная степень, 2 — log/atan
  (cond ((not (pair? F)) '())
        ((and (equal? (car F) '^) (pair? (cdr F)) (pair? (cddr F))
              (number? (caddr F)) (not (integer? (caddr F))))
         (cons 1 (cs-scan (cadr F))))
        ((or (equal? (car F) 'log) (equal? (car F) 'atan))
         (cons 2 (apply append (map cs-scan (cdr F)))))
        (else (apply append (map cs-scan (cdr F))))))

(define (cs-hard-limit? F k)
  (let ((fl (cs-scan F)))
    (and (member? 1 fl) (member? 2 fl))))

; (cs-tail-int term k N) — хвост по интегральному признаку для Σ_{k>N}:
; ∫_{N+1}^∞ f ≤ Σ_{N+1}^∞ f ≤ f(N+1) + ∫_{N+1}^∞ f
; (нижняя граница — REL.1e: без неё ширина не опускалась ниже самого интеграла)
(define (cs-tail-int term k N)
  (let* ((M (+ N 1))
         (F (integrate term k)))
    (if (or (not (list? F)) (null? F) (equal? (car F) 'integrate) (cs-hard-limit? F k))
        #f
        (let ((Finf (limit F k 'inf)))
          (if (and (number? Finf) (not (equal? (type-of Finf) 'float)))
              (let ((FM (simplify (subst (list k M) F))))
                (cond ((and (number? FM) (not (equal? (type-of FM) 'float)) (>= (- Finf FM) 0))
                       (cs-tail-bounds term k M (- Finf FM)))
                      ; F(M) с радикалом (k^(−3/2) → 1/√M) — нижняя граница интервальной оценкой
                      (else
                       (let ((fi (try (iv-eval F k (iv M M)) (lambda (e) #f))))
                         (if (and (iv? fi) (>= (- Finf (iv-lo fi)) 0))
                             (cs-tail-bounds term k M (- Finf (iv-lo fi)))
                             #f)))))
              #f)))))

; [J, J + f(M)] — хвост от M; f(M) берём интервально (верхняя граница)
(define (cs-tail-bounds term k M J)
  (let ((fM (try (iv-eval term k (iv M M)) (lambda (e) #f))))
    (if (and (iv? fM) (>= (iv-hi fM) 0))
        (iv J (+ J (iv-hi fM)))
        #f)))

(define (cs-tail term k N)
  (let ((t (cs-tail-int term k N))) (if t t (cs-tail-geom term k N))))

;  PERF.3: знакочередующиеся ряды. ρ(k) = t(k+1)/t(k) ∈ [-q, 0) на [N, ∞) (строго
; по интервальной оценке, q < 1) => члены чередуют знак, |t| убывает геометрически
; к 0 (признак Лейбница): хвост лежит между 0 и t(N+1).
; (cs-abs-term t k) — |t| для t = (-1)^k · a(k) в простых формах, иначе #f
(define (cs-abs-term t k)
  (cond ((equal? t (list '^ -1 k)) 1)
        ((and (pair? t) (equal? (car t) '/) (equal? (cadr t) (list '^ -1 k)))
         (list '/ 1 (caddr t)))
        ((and (pair? t) (equal? (car t) '*) (member? (list '^ -1 k) (cdr t)))
         (cons '* (filter (lambda (x) (not (equal? x (list '^ -1 k)))) (cdr t))))
        (else #f)))

; 'ok — чередование и убывание к 0 доказаны; 'bad — знак чередуется, но убывание
; не доказано (быстрый отказ); #f — ряд не знакочередующийся (обычный путь).
; Если |ρ| ≤ 1 лишь в пределе (как (-1)^k/k), предел |t| → 0 берётся из limit.
(define (cs-alternating? term k N)
  (let ((rho (cs-ratio-expr term k)))
    (if (not rho)
        #f
        (let ((r (cs-ratio-range rho k N)))
          (cond ((not (and r (< (iv-hi r) 0))) #f)
                ((> (iv-lo r) -1) 'ok)
                ((and (>= (iv-lo r) -1)
                      (let ((a (cs-abs-term term k)))
                        (and a (equal? (try (limit a k 'inf) (lambda (e) #f)) 0))))
                 'ok)
                (else 'bad))))))

(define (cs-alt-choose term k N tol)
  (let ((t1 (iv-eval term k (iv (+ N 1) (+ N 1)))))
    (if (or (<= (max (abs (iv-lo t1)) (abs (iv-hi t1))) tol) (> N 4096))
        N
        (cs-alt-choose term k (* 2 N) tol))))

(define (cs-alt-sum term k a tol N0)
  (let* ((N (cs-alt-choose term k N0 tol))
         (q (/ (* 100 (+ N 2)) tol))
         (S (cs-partial term k a N (iv 0 0) q))
         (t1 (iv-eval term k (iv (+ N 1) (+ N 1)))))
    (iv (+ (iv-lo S) (min 0 (iv-lo t1))) (+ (iv-hi S) (max 0 (iv-hi t1))))))

; (cs-choose term k N tol n) — удвоение N, пока ширина хвоста > tol (не больше 14 раз);
; #f — если отношение не разбирается и первообразной нет (отказ, не ошибка: WASM.6a Д8)
(define (cs-choose term k N tol n)
  (if (> n 14)
      N
      (let ((t (cs-tail term k N)))
        (cond ((not t)
               (if (and (= n 0) (not (cs-ratio-expr term k)))
                   #f
                   (cs-choose term k (* 2 N) tol (+ n 1))))
              ((<= (iv-width t) tol) N)
              ((> N 4096) N)
              (else (cs-choose term k (* 2 N) tol (+ n 1)))))))

; (certified-sum term k a tol) — интервал для Σ_{k=a}^∞ term при положительных
; убывающих членах: частичная сумма + строгая оценка хвоста (интегральный
; признак, иначе геометрическая мажоранта по проверенному отношению).
; Если строгая оценка невозможна — честный отказ #f с причиной в условий ответа
; (WASM.6a Д8: раньше была ошибка, а не отказ).
(define (cs-refuse reason term)
  (record-condition (list 'certified-sum-refused term) reason)
  #f)

; REL.1e: расходимость по интегральному признаку — ∫_a^∞ f = ∞ (и f положительна, убывает).
; Дорогую первообразную (cs-hard-limit?) не считаем: вызывается только после отказа оценки хвоста.
(define (cs-divergent? term k a)
  (let ((F (integrate term k)))
    (and (list? F) (not (null? F)) (not (equal? (car F) 'integrate))
         (not (cs-hard-limit? F k))
         (equal? (try (limit F k 'inf) (lambda (e) #f)) 'inf))))

(define (certified-sum term k a tol)
  (cond ((not (integer? a)) (cs-refuse "certified-sum: нижняя граница должна быть целой" term))
        (else
      (let ((alt (try (cs-alternating? term k (+ a 8)) (lambda (e) 'unknown))))
        (cond ((equal? alt 'bad)
               (cs-refuse "certified-sum: знакочередующийся ряд, убывание членов к 0 не доказано" term))
              ((equal? alt 'ok)
               (let ((r (try (cs-alt-sum term k a tol (+ a 8)) (lambda (e) #f))))
                 (if (iv? r) r (cs-refuse "certified-sum: хвост знакочередующегося ряда не оценивается" term))))
              (else
               (let ((r (try
                         (let* ((N (cs-choose term k (+ a 8) tol 0)))
                           (if (not N)
                               #f
                               (let* ((q (/ (* 100 (+ N 2)) tol))
                                      (S (cs-partial term k a N (iv 0 0) q))
                                      (t (cs-tail term k N)))
                                 (if t (iv (+ (iv-lo S) (iv-lo t)) (+ (iv-hi S) (iv-hi t))) #f))))
                         (lambda (e) #f))))
                 (if (iv? r) r
                     (if (cs-divergent? term k a)
                         (cs-refuse "certified-sum: ряд расходится (интегральный признак: ∫ f = ∞)" term)
                         (cs-refuse "certified-sum: не удалось строго оценить хвост (нет ни отношения, ни первообразной)" term)))))))))
)