; numtheory.lisp — Шаг NT.1: теория чисел на целых числах.
;
; Каждый ответ проверяется перед возвратом (сертификат, который можно проверить независимо):
;   invmod — a·a⁻¹ ≡ 1 (mod m); egcd — s·a + t·b = g и g | a, g | b; sqrtmod — r² ≡ a (mod p);
;   crt — x ≡ rᵢ (mod mᵢ) и M = НОК(mᵢ); order — a^d ≡ 1 и a^(d/q) ≢ 1 для всех простых q | d;
;   totient — φ = n·∏(p−1)/p совпадает с ∏ p^(k−1)(p−1); divisors — ∏(kᵢ+1) делителей, каждый делит n;
;   factor-integer — произведение множителей равно n, каждый множитель проходит prime?.
; Приватные предикаты-сертификаты (nt-…-ok?) вызываются и публичными функциями, и тестами (numtheory::имя).
;
; Простота: Миллер–Рабин, базы 2…37 детерминированны при n < 3.3·10^24; выше — вероятностный ответ
; с честной пометкой в канале условий (record-condition probable-prime). Факторизация: пробное деление
; до 1000, затем ρ Полларда (Брент) — ответ всегда проверен сертификатом, при неудаче ρ — ошибка.

(module numtheory
  (export powmod invmod egcd jacobi sqrtmod crt totient divisors order primitive-root
          prime? next-prime primes-up-to factor-integer pratt-certificate pratt-check
          solve-linear-diophantine pell pell-negative pell-solutions
          sum-of-two-squares pythagorean-triples
          dioph-linear dioph-linear-system dioph-linear-system-check sqrt-cf-period dioph-pell-negative dioph-pell
          two-squares three-squares four-squares pythagorean-hypotenuse pythagorean-leg
          multiplicative-order discrete-log dioph-check))

; ---------- малые помощники ----------

; модуль целого
(define (nt-abs n) (if (< n 0) (- n) n))

; целый квадратный корень (Ньютон), n ≥ 0
(define (nt-isqrt n)
  (if (< n 0) (error "nt-isqrt: отрицательное число")
      (if (= n 0) 0
          (let loop ((x n))
            (let ((y (quotient (+ x (quotient n x)) 2)))
              (if (< y x) (loop y) x))))))

; вынесение двоек: (нечётная часть количество), n > 0
(define (nt-strip-twos n)
  (let loop ((n n) (s 0))
    (if (even? n) (loop (quotient n 2) (+ s 1)) (list n s))))

; ---------- решето простых ----------

; (primes-up-to n) — список простых ≤ n по возрастанию (решето Эратосфена)
(define (primes-up-to n)
  (if (or (not (integer? n)) (< n 2))
      '()
      (let ((v (make-vector (+ n 1) #t)))
        (vset! v 0 #f)
        (vset! v 1 #f)
        (let sieve ((i 2))
          (if (<= (* i i) n)
              (begin
                (if (vref v i)
                    (let mark ((j (* i i)))
                      (if (<= j n)
                          (begin (vset! v j #f) (mark (+ j i))))))
                (sieve (+ i 1)))))
        (let collect ((i n) (acc '()))
          (if (< i 2)
              acc
              (collect (- i 1) (if (vref v i) (cons i acc) acc)))))))

; простые до 1000 — для пробного деления при факторизации и проверке простоты
(define nt-small-primes (primes-up-to 1000))

; ---------- возведение в степень по модулю ----------

; (powmod a e m) — a^e mod m (двоичное возведение); e ≥ 0, m ≥ 1
(define (powmod a e m)
  (cond ((not (integer? a)) (error "powmod: основание — целое"))
        ((not (integer? e)) (error "powmod: показатель — целое"))
        ((< e 0) (error "powmod: показатель — целое ≥ 0"))
        ((not (integer? m)) (error "powmod: модуль — целое"))
        ((< m 1) (error "powmod: модуль — целое ≥ 1"))
        ((= m 1) 0)
        (else
         (let loop ((b (modulo a m)) (ex e) (acc 1))
           (cond ((= ex 0) acc)
                 ((odd? ex) (loop (modulo (* b b) m) (quotient ex 2) (modulo (* acc b) m)))
                 (else (loop (modulo (* b b) m) (quotient ex 2) acc)))))))

; ---------- простота: Миллер–Рабин ----------

; граница точности баз 2…37 (n < 3 317 044 064 679 887 385 961 981)
(define nt-mr-limit 3317044064679887385961981)
(define nt-mr-bases '(2 3 5 7 11 13 17 19 23 29 31 37))

; (nt-mr-pass? n a) — проходит ли нечётное n > 3 проверку по базе a (a — не свидетель)
(define (nt-mr-pass? n a)
  (let ((a (modulo a n)))
    (if (= a 0)
        #t                                     ; база кратна n — сведений нет (для n < 37² это уже разобрано)
        (let* ((st (nt-strip-twos (- n 1)))
               (t (car st))
               (s (cadr st))
               (x (powmod a t n)))
          (cond ((or (= x 1) (= x (- n 1))) #t)
                (else
                 ; возводим в квадрат s−1 раз и ищем −1: x_j = a^(t·2^j), j = 1 … s−1
                 (let loop ((i 1) (x x))
                   (if (>= i s)
                       #f
                       (let ((x2 (modulo (* x x) n)))
                         (if (= x2 (- n 1)) #t (loop (+ i 1) x2)))))))))))

; наименьший простой делитель n среди простых до 1000 (или #f)
(define (nt-small-prime-factor n)
  (let loop ((ps nt-small-primes))
    (cond ((null? ps) #f)
          ((> (* (car ps) (car ps)) n) #f)
          ((= (modulo n (car ps)) 0) (car ps))
          (else (loop (cdr ps))))))

; (prime? n [:certificate]) — простое ли n. До 3.3·10^24 базы 2…37 дают точный ответ; выше — вероятностный
; (запись в канал условий: probable-prime). С флагом :certificate — сертификат Пратта (NT.2) или #f.
(define (prime? n &rest opts)
  (cond ((not (integer? n)) (error "prime?: аргумент — целое число"))
        ((< n 2) #f)
        ((< n 4) (if (and (pair? opts) (equal? (car opts) ':certificate))
                     (pratt-certificate n) #t))
        ((even? n) #f)
        ((nt-small-prime-factor n) #f)
        (else
         (let ((probable (every? (lambda (a) (nt-mr-pass? n a)) nt-mr-bases)))
           (cond ((not probable) #f)
                 ((and (pair? opts) (equal? (car opts) ':certificate))
                  (pratt-certificate n))
                 ((>= n nt-mr-limit)
                  (begin
                    (record-condition (list 'probable-prime n)
                                      "prime?: n ≥ 3.3·10^24 — ответ вероятностный (Миллер–Рабин, 12 баз)")
                    #t))
                 (else #t))))))

; (next-prime n) — наименьшее простое > n
(define (next-prime n)
  (if (not (integer? n))
      (error "next-prime: n — целое число")
      (if (< n 2)
          2
          (let loop ((k (+ n 1)))
            (if (prime? k) k (loop (+ k 1)))))))

; ---------- расширенный Евклид ----------

; (g s t) для a ≥ 0, b ≥ 0: g = s·a + t·b
(define (nt-egcd-pos a b)
  (if (= b 0)
      (list a 1 0)
      (let* ((q (quotient a b))
             (r (modulo a b))
             (sub (nt-egcd-pos b r)))
        (list (car sub) (caddr sub) (- (cadr sub) (* q (caddr sub)))))))

; (nt-egcd-ok? a b g s t) — сертификат: s·a + t·b = g, g ≥ 0 делит a и b
(define (nt-egcd-ok? a b g s t)
  (and (= (+ (* s a) (* t b)) g)
       (>= g 0)
       (or (= g 0) (and (= (modulo a g) 0) (= (modulo b g) 0)))))

; (egcd a b) → (g s t), s·a + t·b = g = НОД(a, b) ≥ 0
(define (egcd a b)
  (if (or (not (integer? a)) (not (integer? b)))
      (error "egcd: аргументы — целые числа")
      (let* ((sa (if (< a 0) -1 1))
             (sb (if (< b 0) -1 1))
             (r (nt-egcd-pos (nt-abs a) (nt-abs b)))
             (g (car r))
             (s (* sa (cadr r)))
             (t (* sb (caddr r))))
        (if (nt-egcd-ok? a b g s t)
            (list g s t)
            (error "egcd: сертификат s·a + t·b = g не прошёл")))))

; (invmod a m) — обратный к a по модулю m, или #f, если обратного нет
(define (invmod a m)
  (cond ((not (integer? a)) (error "invmod: a — целое число"))
        ((not (integer? m)) (error "invmod: модуль — целое число"))
        ((< m 1) (error "invmod: модуль — целое ≥ 1"))
        ((= m 1) 0)
        (else
         (let* ((r (egcd a m))
                (g (car r)))
           (if (not (= g 1))
               #f                                  ; a и m не взаимно просты
               (let ((inv (modulo (cadr r) m)))
                 (if (= (modulo (* a inv) m) 1)
                     inv
                     (error "invmod: сертификат a·a⁻¹ ≡ 1 не прошёл"))))))))

; ---------- символ Якоби ----------

; цикл Якоби: a ≥ 0, n — положительное нечётное
(define (nt-jacobi-loop a n res)
  (if (= a 0)
      (if (= n 1) res 0)
      (let* ((st (nt-strip-twos a))
             (a1 (car st))
             (s (cadr st))
             (res1 (if (and (odd? s) (member? (modulo n 8) '(3 5))) (- res) res)))
        (nt-jacobi-loop (modulo n a1) a1
                        (if (and (= (modulo n 4) 3) (= (modulo a1 4) 3)) (- res1) res1)))))

; (nt-jacobi-euler-ok? a p j) — для простого p: j равен a^((p−1)/2) mod p, записанному как ±1/0
; (критерий Эйлера; используется как сертификат символа Якоби)
(define (nt-jacobi-euler-ok? a p j)
  (let ((e (powmod a (quotient (- p 1) 2) p)))
    (= j (cond ((= e 1) 1) ((= e (- p 1)) -1) (else 0)))))

; (jacobi a n) — символ Якоби (a/n) ∈ {−1, 0, 1}; n — положительное нечётное
(define (jacobi a n)
  (if (or (not (integer? a)) (not (integer? n)))
      (error "jacobi: аргументы — целые числа")
      (if (or (< n 1) (even? n))
          (error "jacobi: n — положительное нечётное")
          (let* ((a1 (modulo a n))
                 (res (nt-jacobi-loop a1 n 1)))
            (if (and (prime? n) (not (nt-jacobi-euler-ok? a1 n res)))
                (error "jacobi: сертификат (критерий Эйлера) не прошёл")
                res)))))

; ---------- квадратный корень по модулю простого (Тонелли–Шенкс) ----------

; наименьший квадратичный невычет по нечётному простому p (начинаем с 2)
(define (nt-nonresidue p)
  (let loop ((z 2))
    (if (= (jacobi z p) -1) z (loop (+ z 1)))))

; наименьшее i ∈ [1, m) с t^(2^i) ≡ 1 (mod p), иначе #f (t ≠ 1)
(define (nt-least-nonone t m p)
  (let loop ((i 1) (x (modulo (* t t) p)))
    (cond ((>= i m) #f)
          ((= x 1) i)
          (else (loop (+ i 1) (modulo (* x x) p))))))

; (nt-tonelli a p) — корень из a по простому p ≡ 1 (mod 4), a — ненулевой вычет
(define (nt-tonelli a p)
  (let* ((st (nt-strip-twos (- p 1)))
         (q (car st))
         (s (cadr st)))
    (let loop ((m s)
               (c (powmod (nt-nonresidue p) q p))
               (t (powmod a q p))
               (r (powmod a (quotient (+ q 1) 2) p)))
      (if (= t 1)
          r
          (let ((i (nt-least-nonone t m p)))
            (if (not i)
                (error "sqrtmod: Тонелли-Шенкс — не найден порядок t")
                (let ((b (powmod c (^ 2 (- m i 1)) p)))
                  (loop i
                        (modulo (* b b) p)
                        (modulo (* t (* b b)) p)
                        (modulo (* r b) p)))))))))

; (nt-sqrt-root? a p r) — сертификат: r — корень из a по модулю p, 0 ≤ r < p
(define (nt-sqrt-root? a p r)
  (and (integer? r)
       (>= r 0)
       (< r p)
       (= (modulo (* r r) p) (modulo a p))))

; (sqrtmod a p) — квадратный корень из a по модулю простого p; #f, если a — невычет
(define (sqrtmod a p)
  (cond ((not (integer? a)) (error "sqrtmod: a — целое число"))
        ((not (integer? p)) (error "sqrtmod: p — целое число"))
        ((< p 2) (error "sqrtmod: p — простое число ≥ 2"))
        ((not (prime? p)) (error "sqrtmod: p должно быть простым"))
        ((= p 2) (modulo a 2))
        (else
         (let ((a1 (modulo a p)))
           (cond ((= a1 0) 0)
                 ((not (= (jacobi a1 p) 1)) #f)      ; квадратичный невычет — корня нет
                 (else
                  (let* ((r0 (if (= (modulo p 4) 3)
                                 (powmod a1 (quotient (+ p 1) 4) p)
                                 (nt-tonelli a1 p)))
                         (r (min r0 (- p r0))))      ; канонический (меньший) корень
                    (if (nt-sqrt-root? a1 p r)
                        r
                        (error "sqrtmod: сертификат r² ≡ a (mod p) не прошёл")))))))))

; ---------- Китайская теорема об остатках ----------

; слияние сравнения x (mod M) с r (mod m) → (x' M') или #f (несовместны)
(define (nt-crt-merge x M r m)
  (if (not (integer? r)) (error "crt: остатки — целые числа"))
  (let* ((g (gcd M m))
         (r1 (modulo r m))
         (diff (modulo (- r1 x) g)))
    (if (not (= diff 0))
        #f                                          ; x и r разные по модулю НОД — несовместны
        (let* ((m1 (quotient M g))
               (m2 (quotient m g)))
          (if (= m2 1)
              (list x M)                            ; m | M и условие уже выполнено
              (let* ((inv (invmod (modulo m1 m2) m2))
                     (t (modulo (* (quotient (- r1 x) g) inv) m2))
                     (x2 (+ x (* M t)))
                     (M2 (* M m2)))
                (list (modulo x2 M2) M2)))))))

; (nt-crt-ok? rs ms x M) — сертификат: x ∈ [0, M), x ≡ rᵢ (mod mᵢ) и M = НОК(mᵢ)
(define (nt-crt-ok? rs ms x M)
  (and (>= x 0)
       (< x M)
       (= M (foldl lcm 1 ms))
       (every? (lambda (p) (= (modulo (- x (car p)) (cadr p)) 0)) (map2 list rs ms))))

; (crt rs ms) → (x M) — решение системы x ≡ rᵢ (mod mᵢ); модули не обязаны быть взаимно простыми;
; несовместная система → #f. Возвращается наименьшее неотрицательное x.
(define (crt rs ms)
  (if (not (= (length rs) (length ms)))
      (error "crt: длины списков остатков и модулей должны совпадать")
      (if (null? rs)
          (list 0 1)
          (if (not (every? (lambda (m) (and (integer? m) (>= m 1))) ms))
              (error "crt: модули — целые ≥ 1")
              (let loop ((i 0) (x 0) (M 1) (ok #t))
                (cond ((not ok) #f)
                      ((= i (length rs))
                       (if (nt-crt-ok? rs ms x M)
                           (list x M)
                           (error "crt: сертификат решения не прошёл")))
                      (else
                       (let ((r (nt-crt-merge x M (nth rs i) (nth ms i))))
                         (if r
                             (loop (+ i 1) (car r) (cadr r) #t)
                             (loop (+ i 1) x M #f))))))))))

; ---------- функция Эйлера и делители ----------

; (totient n) — φ(n), n ≥ 1; сертификат: ∏(p−1)/p·n = ∏ p^(k−1)(p−1)
(define (totient n)
  (if (or (not (integer? n)) (< n 1))
      (error "totient: n — целое ≥ 1")
      (let* ((fac (factor-integer n))
             (phi (foldl (lambda (acc pk) (quotient (* acc (- (car pk) 1)) (car pk))) n fac))
             (direct (foldl (lambda (acc pk)
                              (* acc (^ (car pk) (- (cadr pk) 1)) (- (car pk) 1)))
                            1 fac)))
        (if (not (= phi direct))
            (error "totient: сертификат φ = ∏ p^(k−1)(p−1) не прошёл")
            phi))))

; все делители по разложению: домножаем каждое p в степенях 0…k
(define (nt-divisors-from fac acc)
  (if (null? fac)
      acc
      (let ((p (car (car fac))) (k (cadr (car fac))))
        (nt-divisors-from (cdr fac)
                          (append-map (lambda (d)
                                        (map (lambda (j) (* d (^ p j))) (range (+ k 1))))
                                      acc)))))

; (divisors n) — положительные делители |n| по возрастанию; у нуля делителей нет (ошибка)
(define (divisors n)
  (if (not (integer? n))
      (error "divisors: аргумент — целое число")
      (if (= n 0)
          (error "divisors: у нуля бесконечно много делителей")
          (let* ((fac (factor-integer (nt-abs n)))
                 (ds (sort (nt-divisors-from fac '(1)) <))
                 (cnt (foldl (lambda (acc pk) (* acc (+ (cadr pk) 1))) 1 fac)))
            (if (not (= (length ds) cnt))
                (error "divisors: сертификат — число делителей не равно ∏(kᵢ+1)")
                (if (not (every? (lambda (d) (= (modulo (nt-abs n) d) 0)) ds))
                    (error "divisors: сертификат — найденный делитель не делит n")
                    ds))))))

; ---------- мультипликативный порядок и первообразный корень ----------

; делим порядок на простые q, пока a^(d/q) ≡ 1
(define (nt-order-divide a n d qs)
  (if (null? qs)
      d
      (let ((q (car qs)))
        (let loop ((d d))
          (if (and (= (modulo d q) 0) (= (powmod a (quotient d q) n) 1))
              (loop (quotient d q))
              (nt-order-divide a n d (cdr qs)))))))

; (nt-order-ok? a n d) — сертификат порядка: a^d ≡ 1 и a^(d/q) ≢ 1 для всех простых q | d
(define (nt-order-ok? a n d)
  (and (>= d 1)
       (= (powmod a d n) 1)
       (every? (lambda (q) (not (= (powmod a (quotient d q) n) 1)))
               (map car (factor-integer d)))))

; (order a n) — мультипликативный порядок a по модулю n; #f, если n < 2 или НОД(a, n) ≠ 1
(define (order a n)
  (cond ((or (not (integer? a)) (not (integer? n))) (error "order: аргументы — целые числа"))
        ((< n 2) #f)
        ((not (= (gcd a n) 1)) #f)
        (else
         (let* ((a1 (modulo a n))
                (d (nt-order-divide a1 n (totient n) (map car (factor-integer (totient n))))))
           (if (nt-order-ok? a1 n d)
               d
               (error "order: сертификат порядка не прошёл"))))))

; (nt-primitive-ok? g p) — сертификат первообразного корня: g^(p−1) ≡ 1 и g^((p−1)/q) ≢ 1 для q | p−1
(define (nt-primitive-ok? g p)
  (let ((phi (- p 1)))
    (and (= (powmod g phi p) 1)
         (every? (lambda (q) (not (= (powmod g (quotient phi q) p) 1)))
                 (map car (factor-integer phi))))))

; (primitive-root p) — наименьший первообразный корень по модулю простого p; #f, если p не простое
(define (primitive-root p)
  (cond ((not (integer? p)) (error "primitive-root: p — целое число"))
        ((not (prime? p)) #f)
        ((= p 2) 1)
        (else
         (let loop ((g 2))
           (cond ((>= g p) #f)
                 ((nt-primitive-ok? g p) g)
                 (else (loop (+ g 1))))))))

; ---------- факторизация: пробное деление + ρ Полларда (Брент) ----------

; (nt-brent n c) — нетривиальный делитель n или #f; многочлен x² + c
(define (nt-brent n c)
  (let ((m 128) (y 2) (r 1) (q 1) (g 1) (x 2) (ys 2) (guard 0))
    (while (and (= g 1) (< guard 100000))
      (set! x y)
      (let ((i 0))
        (while (< i r)
          (set! y (modulo (+ (* y y) c) n))
          (set! i (+ i 1))))
      (let ((k 0))
        (while (and (< k r) (= g 1))
          (set! ys y)
          (let ((i 0) (lim (min m (- r k))))
            (while (< i lim)
              (set! y (modulo (+ (* y y) c) n))
              (set! q (modulo (* q (nt-abs (- x y))) n))
              (set! i (+ i 1))))
          (set! g (gcd q n))
          (set! k (+ k m))))
      (set! r (* 2 r))
      (set! guard (+ guard 1)))
    (cond ((= g 1) #f)
          ((< g n) g)
          (else                                        ; g = n: возврат назад по ys в поисках делителя
           (let ((gg 1))
             (while (= gg 1)
               (set! ys (modulo (+ (* ys ys) c) n))
               (set! gg (gcd (nt-abs (- x ys)) n)))
             (if (< gg n) gg #f))))))

; делитель n методом ρ (перебор констант c)
(define (nt-pollard-factor n)
  (let loop ((c 1))
    (if (> c 40)
        #f
        (let ((d (nt-brent n c)))
          (if (and d (> d 1) (< d n)) d (loop (+ c 1)))))))

; простой делитель n (n ≥ 2): пробное деление, затем prime?, затем ρ; не найден — ошибка
(define (nt-least-factor n)
  (let ((sp (nt-small-prime-factor n)))
    (cond (sp sp)
          ((prime? n) n)
          (else
           (let ((sq (nt-isqrt n)))
             (if (= (* sq sq) n)
                 sq                                   ; точный квадрат: делитель известен сразу
                 (let ((d (nt-pollard-factor n)))
                   (if d d (error "factor-integer: делитель не найден (ρ Полларда не сработал)")))))))))

; простые множители n (n ≥ 1) с повторениями, по возрастанию
(define (nt-prime-factors n)
  (if (= n 1)
      '()
      (let ((d (nt-least-factor n)))
        (cons d (nt-prime-factors (quotient n d))))))

; группировка отсортированного списка простых в ((p k) …)
(define (nt-group-primes ps)
  (if (null? ps)
      '()
      (let ((p (car ps)))
        (let loop ((l (cdr ps)) (k 1))
          (if (and (pair? l) (= (car l) p))
              (loop (cdr l) (+ k 1))
              (cons (list p k) (nt-group-primes l)))))))

; (nt-factor-ok? fac n) — сертификат разложения n: произведение = n, множители просты, кратности ≥ 1
(define (nt-factor-ok? fac n)
  (and (= (foldl (lambda (acc pk) (* acc (^ (car pk) (cadr pk)))) 1 fac) n)
       (every? (lambda (pk) (and (integer? (car pk)) (>= (cadr pk) 1) (prime? (car pk)))) fac)))

; разложение n ≥ 1 с проверкой сертификата
(define (nt-factor-positive n)
  (let ((fac (nt-group-primes (sort (nt-prime-factors n) <))))
    (if (nt-factor-ok? fac n)
        fac
        (error "factor-integer: сертификат разложения не прошёл"))))

; (factor-integer n) → ((p1 k1) …) по возрастанию p; у отрицательного n первым идёт (-1 1);
; 0 не раскладывается (ошибка), 1 → ()
(define (factor-integer n)
  (cond ((not (integer? n)) (error "factor-integer: аргумент — целое число"))
        ((= n 0) (error "factor-integer: ноль не раскладывается на простые множители"))
        ((= n 1) '())
        ((= n -1) '((-1 1)))
        ((< n 0) (cons '(-1 1) (nt-factor-positive (- n))))
        (else (nt-factor-positive n))))

; ---------- NT.2: сертификаты простоты Пратта ----------

(define (nt-pratt-distinct ps)
  (if (null? ps) '()
      (if (member? (car ps) (cdr ps))
          (nt-pratt-distinct (cdr ps))
          (cons (car ps) (nt-pratt-distinct (cdr ps))))))

; свидетель: a^(n−1) ≡ 1 и a^((n−1)/q) ≢ 1 для всех простых q | n−1
(define (nt-pratt-witness n qs)
  (let loop ((a 2))
    (if (and (= (powmod a (- n 1) n) 1)
             (every? (lambda (q) (not (= (powmod a (quotient (- n 1) q) n) 1))) qs))
        a
        (loop (+ a 1)))))

; (pratt-certificate n) → (n a ((q cert) …)); q — все простые делители n−1 с кратностями
(define (pratt-certificate n)
  (cond ((not (integer? n)) (error "pratt-certificate: n — целое число"))
        ((not (prime? n)) (error "pratt-certificate: n не простое"))
        ((< n 3) (list n 1 '()))
        (else
         (let* ((fac (factor-integer (- n 1)))
                ; все простые делители с кратностями: произведение q = n−1
                (qall (append-map (lambda (pk)
                                    (map (lambda (i) (car pk)) (range (cadr pk))))
                                  fac))
                (qs (nt-pratt-distinct qall))
                (a (nt-pratt-witness n qs)))
           (list n a (map (lambda (q) (list q (pratt-certificate q))) qall))))))

; (pratt-check cert) — независимая проверка: только powmod, произведения и рекурсия
(define (pratt-check cert)
  (and (list? cert) (= (length cert) 3)
       (let ((n (nth cert 0)) (a (nth cert 1)) (subs (nth cert 2)))
         (and (integer? n) (> n 1) (integer? a) (list? subs)
              (= (foldl (lambda (acc pr) (* acc (car pr))) 1 subs) (- n 1))
              (= (powmod a (- n 1) n) 1)
              (every? (lambda (pr)
                        (and (pair? pr) (= (length pr) 2)
                             (equal? (car (cadr pr)) (car pr))
                             (pratt-check (cadr pr))))
                      subs)
              (every? (lambda (q) (not (= (powmod a (quotient (- n 1) q) n) 1)))
                      (nt-pratt-distinct (map car subs)))))))

; ---------- NT.4: линейное диофантово уравнение ----------

; (nt-dio-ok? a b c x0 y0 dx dy) — сертификат: a·x0 + b·y0 = c, a·dx + b·dy = 0, шаг (dx, dy) примитивен
(define (nt-dio-ok? a b c x0 y0 dx dy)
  (and (integer? x0) (integer? y0) (integer? dx) (integer? dy)
       (= (+ (* a x0) (* b y0)) c)
       (= (+ (* a dx) (* b dy)) 0)
       (not (and (= dx 0) (= dy 0)))
       (= (gcd (nt-abs dx) (nt-abs dy)) 1)))

; (solve-linear-diophantine a b c) → ((x0 y0) (dx dy)): x = x0 + dx·k, y = y0 + dy·k (k ∈ ℤ);
; #f — решений нет; a = b = 0, c = 0 — ошибка (решение — любая пара, одной серией не записать)
(define (solve-linear-diophantine a b c)
  (if (or (not (integer? a)) (not (integer? b)) (not (integer? c)))
      (error "solve-linear-diophantine: коэффициенты — целые числа")
      (let* ((r (egcd a b))
             (g (car r))
             (s (cadr r))
             (t (caddr r)))
        (if (step-log-enabled?)
            (record-step 'dio-bezout "Расширенный Евклид"
                         (string-append "g = НОД(" (to-string a) ", " (to-string b) ") = " (to-string g)
                                        " = " (to-string s) "·a + " (to-string t) "·b")
                         (list a b c) (list g s t) 'main))
        (cond ((and (= a 0) (= b 0))
               (if (= c 0)
                   (error "solve-linear-diophantine: 0·x + 0·y = 0 — решения все пары")
                   #f))
              ((not (= (modulo c g) 0))
               (if (step-log-enabled?)
                   (record-step 'dio-none "Решений нет"
                                (string-append "НОД " (to-string g) " не делит " (to-string c))
                                (list a b c) #f 'main))
               #f)
              (else
               (let* ((kk (quotient c g))
                      (dx (quotient b g))
                      (dy (- (quotient a g)))
                      (x1 (* s kk))
                      (y1 (* t kk))
                      (x0 (if (= dx 0) x1 (modulo x1 (nt-abs dx))))
                      (y0 (if (= dx 0) y1 (quotient (- c (* a x0)) b))))
                 (if (nt-dio-ok? a b c x0 y0 dx dy)
                     (begin
                       (if (step-log-enabled?)
                           (begin
                             (record-step 'dio-particular "Частное решение"
                                          (string-append "a·x0 + b·y0 = " (to-string (+ (* a x0) (* b y0)))
                                                         " = c: проверено")
                                          (list a b c) (list x0 y0) 'main)
                             (record-step 'dio-general "Общее решение"
                                          (string-append "x = x0 + dx·k, y = y0 + dy·k; a·dx + b·dy = "
                                                         (to-string (+ (* a dx) (* b dy))) ": проверено")
                                          (list x0 y0) (list dx dy) 'main)))
                       (list (list x0 y0) (list dx dy)))
                     (error "solve-linear-diophantine: сертификат решения не прошёл"))))))))

; ---------- NT.4: уравнение Пелля ----------

; (nt-pell-norm D x y) — норма x² − D·y²
(define (nt-pell-norm D x y) (- (* x x) (* D y y)))

; целый квадрат?
(define (nt-square-int? n)
  (let ((r (nt-isqrt n))) (= (* r r) n)))

; первая подходящая дробь √D с нормой target (1 или −1); для −1 поиск обрывается на конце периода
; (для +1 решение существует всегда, может лежать за первым периодом — идём до первой находки)
(define (nt-cf-first-norm D target)
  (let ((a0 (nt-isqrt D)))
    (let loop ((m 0) (d 1) (a a0) (p2 0) (p1 1) (q2 1) (q1 0) (i 0) (guard 0))
      (if (> guard 1000000)
          #f
          (let* ((p (+ (* a p1) p2))
                 (q (+ (* a q1) q2)))
            (cond ((and (> q 0) (= (nt-pell-norm D p q) target)) (list p q))
                  ((and (= target -1) (> i 0) (= a (* 2 a0))) #f)
                  (else
                   (let* ((m1 (- (* d a) m))
                          (d1 (quotient (- D (* m1 m1)) d))
                          (a1 (quotient (+ a0 m1) d1)))
                     (loop m1 d1 a1 p1 p q1 q (+ i 1) (+ guard 1))))))))))

; (nt-pell-ok? D x y) — сертификат фундаментального решения: x² − D·y² = 1, x, y > 0
; и это первая подходящая дробь √D с нормой 1 (меньших решений нет)
(define (nt-pell-ok? D x y)
  (and (integer? x) (integer? y) (> x 0) (> y 0)
       (= (nt-pell-norm D x y) 1)
       (equal? (nt-cf-first-norm D 1) (list x y))))

; (nt-pell-neg-ok? D x y) — сертификат фундаментального решения x² − D·y² = −1
(define (nt-pell-neg-ok? D x y)
  (and (integer? x) (integer? y) (> x 0) (> y 0)
       (= (nt-pell-norm D x y) -1)
       (equal? (nt-cf-first-norm D -1) (list x y))))

; (pell D) → (x y) — фундаментальное решение x² − D·y² = 1; #f, если D — квадрат или D < 2
(define (pell D)
  (cond ((not (integer? D)) (error "pell: D — целое число"))
        ((< D 2) #f)
        ((nt-square-int? D) #f)
        (else
         (let ((r (nt-cf-first-norm D 1)))
           (if (and r (nt-pell-ok? D (car r) (cadr r)))
               (begin
                 (if (step-log-enabled?)
                     (begin
                       (record-step 'pell-cf "Цепная дробь √D"
                                    (string-append "период цепной дроби √" (to-string D) ": "
                                                   (to-string (try (sqrt-cf-period D) (lambda (e) 'unknown))))
                                    D (try (sqrt-cf-period D) (lambda (e) 'unknown)) 'main)
                       (record-step 'pell-solution "Фундаментальное решение"
                                    (string-append "x² − " (to-string D) "·y² = 1")
                                    D r 'main)
                       (record-step 'pell-check "Проверка решения"
                                    (string-append (to-string (car r)) "² − " (to-string D) "·"
                                                   (to-string (cadr r)) "² = 1: проверено")
                                    r #t 'main)))
                 r)
               (error "pell: сертификат x² − D·y² = 1 не прошёл"))))))

; (pell-negative D) → (x y) — фундаментальное решение x² − D·y² = −1 или #f, если его нет
; (существует тогда и только тогда, когда период цепной дроби √D нечётен)
(define (pell-negative D)
  (cond ((not (integer? D)) (error "pell-negative: D — целое число"))
        ((< D 2) #f)
        ((nt-square-int? D) #f)
        (else
         (let ((r (nt-cf-first-norm D -1)))
           (if (and r (nt-pell-neg-ok? D (car r) (cadr r)))
               (begin
                 (if (step-log-enabled?)
                     (record-step 'pell-negative "Отрицательное уравнение Пелля"
                                  (string-append "период √" (to-string D) " нечётен ⇒ решение x² − "
                                                 (to-string D) "·y² = −1 существует; проверено")
                                  D r 'main))
                 r)
               (begin
                 (if (step-log-enabled?)
                     (record-step 'pell-negative "Отрицательное уравнение Пелля"
                                  (string-append "период √" (to-string D)
                                                 " чётен ⇒ x² − D·y² = −1 решений не имеет")
                                  D #f 'main))
                 #f))))))

; (pell-solutions D k) → ((x1 y1) … (xk yk)) — первые k решений по возрастанию: (x1 + y1√D)^n;
; #f, если D — квадрат; при k < 1 → ()
(define (pell-solutions D k)
  (cond ((not (integer? D)) (error "pell-solutions: D — целое число"))
        ((not (integer? k)) (error "pell-solutions: k — целое число"))
        ((< k 1) '())
        (else
         (let ((r (pell D)))
           (if (not r)
               #f
               (let loop ((n 1) (x (car r)) (y (cadr r)) (acc '()))
                 (if (> n k)
                     (reverse acc)
                     (if (not (= (nt-pell-norm D x y) 1))
                         (error "pell-solutions: сертификат x² − D·y² = 1 не прошёл")
                         (loop (+ n 1)
                               (+ (* x (car r)) (* D y (cadr r)))
                               (+ (* x (cadr r)) (* y (car r)))
                               (cons (list x y) acc))))))))))

; ---------- NT.4: сумма двух квадратов ----------

; (a b)·(c d) в смысле (a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²
(define (nt-two-sq-mul p q)
  (list (- (* (car p) (car q)) (* (cadr p) (cadr q)))
        (+ (* (car p) (cadr q)) (* (cadr p) (car q)))))

; возведение пары в степень k ≥ 0
(define (nt-two-sq-pow p k)
  (let loop ((b p) (e k) (acc (list 1 0)))
    (cond ((= e 0) acc)
          ((odd? e) (loop (nt-two-sq-mul b b) (quotient e 2) (nt-two-sq-mul acc b)))
          (else (loop (nt-two-sq-mul b b) (quotient e 2) acc)))))

; (nt-cornacchia p r) — p = a² + b² для простого p ≡ 1 (mod 4), r² ≡ −1 (mod p)
(define (nt-cornacchia p r)
  (let loop ((a p) (b r))
    (cond ((= b 0) #f)
          ((<= (* b b) p)
           (let ((c (nt-isqrt (- p (* b b)))))
             (if (= (* c c) (- p (* b b)))
                 (list (max b c) (min b c))
                 #f)))
          (else (loop b (modulo a b))))))

; представление простого p ≡ 1 (mod 4) суммой двух квадратов
(define (nt-two-sq-prime p)
  (let ((pair (nt-cornacchia p (sqrtmod (- p 1) p))))
    (if (and pair (= (+ (* (car pair) (car pair)) (* (cadr pair) (cadr pair))) p))
        pair
        (error "sum-of-two-squares: Корнаккия не нашёл представление"))))

; (nt-two-sq-ok? n a b) — сертификат: a, b ≥ 0 и a² + b² = n
(define (nt-two-sq-ok? n a b)
  (and (integer? a) (integer? b) (>= a 0) (>= b 0) (= (+ (* a a) (* b b)) n)))

; (sum-of-two-squares n) → (a b), a ≥ b ≥ 0, a² + b² = n; #f, если представления нет
; (критерий: каждый простой p ≡ 3 (mod 4) входит в n с чётной кратностью)
(define (sum-of-two-squares n)
  (cond ((not (integer? n)) (error "sum-of-two-squares: n — целое число"))
        ((< n 0) #f)
        ((= n 0) (list 0 0))
        (else
         (let ((fac (factor-integer n)))
           (if (any? (lambda (pk) (and (= (modulo (car pk) 4) 3) (odd? (cadr pk)))) fac)
               #f
               (let loop ((fs fac) (acc (list 1 0)))
                 (if (null? fs)
                     (let ((a (nt-abs (car acc))) (b (nt-abs (cadr acc))))
                       (if (nt-two-sq-ok? n a b)
                           (if (>= a b) (list a b) (list b a))
                           (error "sum-of-two-squares: сертификат a² + b² = n не прошёл")))
                     (let* ((p (car (car fs)))
                            (k (cadr (car fs)))
                            (pair (cond ((= p 2) (nt-two-sq-pow (list 1 1) k))
                                        ((= (modulo p 4) 1) (nt-two-sq-pow (nt-two-sq-prime p) k))
                                        (else (list (^ p (quotient k 2)) 0)))))
                       (loop (cdr fs) (nt-two-sq-mul acc pair))))))))))

; ---------- NT.4: пифагоровы тройки ----------

; (nt-pyth-ok? a b c) — сертификат примитивной тройки: a² + b² = c², a, b, c > 0, НОД(a, b) = 1
(define (nt-pyth-ok? a b c)
  (and (integer? a) (integer? b) (integer? c)
       (> a 0) (> b 0) (> c 0)
       (= (+ (* a a) (* b b)) (* c c))
       (= (gcd a b) 1)))

; порядок троек: по гипотенузе, затем по меньшему катету
(define (nt-triple< p q)
  (or (< (caddr p) (caddr q))
      (and (= (caddr p) (caddr q)) (< (car p) (car q)))))

; (pythagorean-triples bound) — примитивные тройки (a b c), a < b, c ≤ bound, по возрастанию c
; (формула Евклида: m > n, НОД(m, n) = 1, m + n нечётно)
(define (pythagorean-triples bound)
  (if (not (integer? bound))
      (error "pythagorean-triples: граница — целое число")
      (if (< bound 5)
          '()
          (let ((acc '()))
            (let loop-m ((m 2))
              (if (> (+ (* m m) 1) bound)
                  (sort acc nt-triple<)
                  (begin
                    (let loop-n ((n 1))
                      (if (< n m)
                          (begin
                            (if (and (<= (+ (* m m) (* n n)) bound)
                                     (= (gcd m n) 1)
                                     (odd? (+ m n)))
                                (let* ((a (- (* m m) (* n n)))
                                       (b (* 2 m n))
                                       (c (+ (* m m) (* n n)))
                                       (lo (min a b))
                                       (hi (max a b)))
                                  (if (nt-pyth-ok? lo hi c)
                                      (set! acc (cons (list lo hi c) acc))
                                      (error "pythagorean-triples: сертификат тройки не прошёл"))))
                            (loop-n (+ n 1)))))
                    (loop-m (+ m 1)))))))))

; ---------- NT.2: диофантовы уравнения с сертификатами ----------
; Отказ — список (none причина…): причина проверяема (НОД, вектор-сертификат, чётный период, простое ≡ 3 mod 4).

; ---- векторы ----
(define (dio-dot u v) (foldl (lambda (acc p) (+ acc p)) 0 (map2 * u v)))
(define (dio-unit n i) (map (lambda (j) (if (= j i) 1 0)) (range n)))
(define (dio-zeros n) (map (lambda (j) 0) (range n)))
(define (dio-vsub u v q) (map2 (lambda (x y) (- x (* q y))) u v))

; (dioph-linear a b c) → ((x0 y0) (dx dy)) как solve-linear-diophantine, либо (none g), g = НОД(a, b) ∤ c
; (a = b = 0: c = 0 → (all), иначе (none 0))
(define (dioph-linear a b c)
  (cond ((not (and (integer? a) (integer? b) (integer? c))) (error "dioph-linear: коэффициенты — целые числа"))
        ((and (= a 0) (= b 0)) (if (= c 0) (list 'all) (list 'none 0)))
        (else
         (let ((g (gcd (nt-abs a) (nt-abs b))))
           (if (= (modulo c g) 0)
               (solve-linear-diophantine a b c)
               (list 'none g))))))

; столбец — (a-столбец u-столбец): u — накопленное унимодулярное преобразование (A·U = H)
(define (dio-col-sub col m q)
  (list (dio-vsub (car col) (car m) q) (dio-vsub (cadr col) (cadr m) q)))
(define (dio-col-neg col)
  (list (map (lambda (x) (- x)) (car col)) (map (lambda (x) (- x)) (cadr col))))

; евклидово исключение по строке r: (ведущий-столбец-или-#f остальные)
(define (dio-reduce-row cols r)
  (let loop ((cs cols))
    (let ((nz (filter (lambda (c) (not (= (nth (car c) r) 0))) cs)))
      (cond ((null? nz) (list #f cs))
            ((null? (cdr nz)) (list (car nz) (filter (lambda (c) (not (equal? c (car nz)))) cs)))
            (else
             (let* ((mn (foldl (lambda (best c)
                                 (if (< (nt-abs (nth (car c) r)) (nt-abs (nth (car best) r))) c best))
                               (car nz) (cdr nz)))
                    (pv (nth (car mn) r)))
               (loop (map (lambda (c)
                            (if (or (equal? c mn) (= (nth (car c) r) 0))
                                c
                                (dio-col-sub c mn (quotient (nth (car c) r) pv))))
                          cs))))))))

; столбцовая форма Эрмита: (ведущие нулевые) — ведущие: ((строка столбец) …), нулевые — столбцы с H-столбцом 0
(define (dio-hnf A n)
  (let ((m (length A)))
    (let loop ((r 0)
               (cs (map (lambda (j) (list (map (lambda (row) (nth row j)) A) (dio-unit n j))) (range n)))
               (piv '()))
      (if (= r m)
          (list (reverse piv) cs)
          (let* ((res (dio-reduce-row cs r)) (p (car res)))
            (if p
                (loop (+ r 1) (cadr res)
                      (cons (list r (if (< (nth (car p) r) 0) (dio-col-neg p) p)) piv))
                (loop (+ r 1) (cadr res) piv)))))))

; сертификат несовместности: w ∈ ℚ^m, wᵀA целый вектор, wᵀb не целое
(define (dio-system-none-ok? A b w)
  (and (= (length w) (length A))
       (every? (lambda (j) (integer? (dio-dot w (map (lambda (row) (nth row j)) A))))
               (range (length (car A))))
       (not (integer? (dio-dot w b)))))

; (dioph-linear-system-check A b res) → #t/#f: res = (x0 базис) — A·x0 = b, A·vᵢ = 0 (целые);
; res = (none w) — сертификат несовместности над ℤ (wᵀA целое, wᵀb нет)
(define (dioph-linear-system-check A b res)
  (if (and (pair? res) (equal? (car res) 'none))
      (and (pair? (cdr res)) (dio-system-none-ok? A b (cadr res)))
      (and (pair? res) (pair? (cdr res))
           (every? integer? (car res))
           (every? (lambda (p) (= (dio-dot (car p) (car res)) (cadr p))) (map2 list A b))
           (every? (lambda (v) (and (every? integer? v)
                                    (every? (lambda (row) (= (dio-dot row v) 0)) A)))
                   (cadr res)))))

; (dioph-linear-system A b) — целые решения A·x = b (A — список строк):
; (x0 (v1 … vk)): x = x0 + Σ tᵢ·vᵢ, tᵢ ∈ ℤ, v — базис решётки решений A·v = 0; или (none w), w — рациональный
; вектор-сертификат (wᵀA целое, wᵀb нет). Метод: столбцовая форма Эрмита H = A·U, прямая подстановка H·y = b.
(define (dioph-linear-system A b)
  (let* ((m (length A)) (n (length (car A)))
         (hn (dio-hnf A n))
         (piv (car hn)) (zero (cadr hn)))
    (let loop ((ps piv)
               (vals b)
               (C (map (lambda (i) (dio-unit m i)) (range m)))
               (x (dio-zeros n)))
      (if (null? ps)
          (let ((bad (filter (lambda (i) (not (= (nth vals i) 0))) (range m))))
            (if (null? bad)
                (let ((res (list x (map cadr zero))))
                  (if (dioph-linear-system-check A b res)
                      res
                      (error "dioph-linear-system: сертификат решения не прошёл")))
                (let* ((i (car bad))
                       (w (map (lambda (c) (/ c (* 2 (nth vals i)))) (nth C i))))
                  (if (dio-system-none-ok? A b w)
                      (list 'none w)
                      (error "dioph-linear-system: сертификат несовместности не прошёл")))))
          (let* ((r (car (car ps))) (col (cadr (car ps)))
                 (h (car col)) (pv (nth h r)) (v (nth vals r)))
            (if (not (= (modulo v pv) 0))
                (let ((w (map (lambda (c) (/ c pv)) (nth C r))))
                  (if (dio-system-none-ok? A b w)
                      (list 'none w)
                      (error "dioph-linear-system: сертификат несовместности не прошёл")))
                (let ((y (quotient v pv)) (cy (map (lambda (c) (/ c pv)) (nth C r))))
                  (loop (cdr ps)
                        (dio-vsub vals h y)
                        (map2 (lambda (ci hi) (dio-vsub ci cy hi)) C h)
                        (map2 (lambda (xi ui) (+ xi (* y ui))) x (cadr col))))))))))

; ---- Пелль: период, отрицательное, обобщённое ----

; (sqrt-cf-period D) — длина периода цепной дроби √D (D > 0 не квадрат)
(define (sqrt-cf-period D)
  (if (or (not (integer? D)) (< D 2) (nt-square-int? D))
      (error "sqrt-cf-period: D — целое, не квадрат, D ≥ 2")
      (let ((a0 (nt-isqrt D)))
        (let loop ((m 0) (d 1) (a a0) (n 0))
          (let* ((m1 (- (* d a) m))
                 (d1 (quotient (- D (* m1 m1)) d))
                 (a1 (quotient (+ a0 m1) d1)))
            (if (= a1 (* 2 a0)) (+ n 1) (loop m1 d1 a1 (+ n 1))))))))

; (dioph-pell-negative D) → (x y): x² − D·y² = −1, фундаментальное; либо (none even-period L) — период L чётен
(define (dioph-pell-negative D)
  (let ((L (sqrt-cf-period D)))
    (if (odd? L)
        (let ((r (pell-negative D)))
          (if (and r (= (nt-pell-norm D (car r) (cadr r)) -1))
              r
              (error "dioph-pell-negative: нечётный период, но решения нет")))
        (list 'none 'even-period L))))

(define (dio-pair<? p q)
  (or (< (car p) (car q)) (and (= (car p) (car q)) (< (cadr p) (cadr q)))))

; сортировка с удалением повторов
(define (dio-sort-uniq lst)
  (let loop ((l (sort lst dio-pair<?)) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? acc) (equal? (car acc) (car l))) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

(define dio-pell-cap 200000)

; верхняя граница y для классов x² − D·y² = N (Нагель): y₁·√|N| / √(2(x₁ ± 1)), (x₁ y₁) = pell(D)
(define (dio-pell-ybound D N)
  (let* ((f (pell D)) (x1 (car f)) (y1 (cadr f)))
    (+ 1 (nt-isqrt (quotient (* y1 y1 (nt-abs N)) (* 2 (if (> N 0) (+ x1 1) (- x1 1))))))))

; (dioph-pell D N) — решения x² − D·y² = N.
;  D > 0 не квадрат: список представителей классов (x y), y ≥ 0, знак x любой (все решения — ±(x + y√D)·εᵏ, k ∈ ℤ,
;  ε — фундаментальная единица); перебор y ≤ границы Нагеля, при границе > 200000 — (unknown y-граница);
;  (none y-граница) — перебор завершён, классов нет. D квадрат, D < 0 — все решения (конечный список);
;  N = 0 и D квадрат — (unknown infinite).
(define (dioph-pell D N)
  (cond ((not (and (integer? D) (integer? N))) (error "dioph-pell: D, N — целые"))
        ((= D 0) (error "dioph-pell: D ≠ 0"))
        ((and (> D 0) (nt-square-int? D))
         (let ((s (nt-isqrt D)))
           (if (= N 0)
               (list 'unknown 'infinite)
               (let ((sols (append-map
                            (lambda (d)
                              (append-map
                               (lambda (u)
                                 (let ((v (quotient N u)))
                                   (if (and (= (modulo (+ u v) 2) 0) (= (modulo (- v u) (* 2 s)) 0))
                                       (list (list (quotient (+ u v) 2) (quotient (- v u) (* 2 s))))
                                       '())))
                               (list d (- d))))
                            (divisors (nt-abs N)))))
                 (let ((r (dio-sort-uniq sols)))
                   (if (null? r) (list 'none 0) r))))))
        ((< D 0)
         (if (< N 0)
             (list 'none 0)
             (let* ((yb (nt-isqrt (quotient N (- D))))
                    (sols (append-map
                           (lambda (y)
                             (let* ((t (- N (* (- D) y y))) (x (nt-isqrt t)))
                               (if (= (* x x) t)
                                   (list (list x y) (list (- x) y) (list x (- y)) (list (- x) (- y)))
                                   '())))
                           (range (+ yb 1)))))
               (let ((r (dio-sort-uniq sols)))
                 (if (null? r) (list 'none yb) r)))))
        ((= N 0) (list (list 0 0)))
        ((= N 1) (list (list -1 0) (list 1 0)))
        ((= N -1)
         (let ((r (dioph-pell-negative D)))
           (if (equal? (car r) 'none)
               (list 'none (caddr r))
               (list (list (- (car r)) (cadr r)) r))))
        (else
         (let ((yb (dio-pell-ybound D N)))
           (if (> yb dio-pell-cap)
               (list 'unknown yb)
               (let loop ((y 0) (acc '()))
                 (if (> y yb)
                     (let ((r (dio-sort-uniq acc)))
                       (if (null? r)
                           (list 'none yb)
                           (if (every? (lambda (p) (= (nt-pell-norm D (car p) (cadr p)) N)) r)
                               r
                               (error "dioph-pell: сертификат x² − D·y² = N не прошёл"))))
                     (let* ((t (+ N (* D y y))))
                       (if (< t 0)
                           (loop (+ y 1) acc)
                           (let ((x (nt-isqrt t)))
                             (if (= (* x x) t)
                                 (loop (+ y 1)
                                       (if (= x 0)
                                           (cons (list 0 y) acc)
                                           (cons (list x y) (cons (list (- x) y) acc))))
                                 (loop (+ y 1) acc))))))))))))

; ---- суммы квадратов ----

(define (dio-gauss-conj p) (list (car p) (- (cadr p))))

; (a b) → (max(|a|,|b|) min(|a|,|b|))
(define (dio-abs-pair p)
  (let ((a (nt-abs (car p))) (b (nt-abs (cadr p)))) (if (>= a b) (list a b) (list b a))))

; пустой результат append/filter — настоящий ()
(define (dio-list l) (if (null? l) '() l))

; (two-squares n) — все представления n = a² + b², a ≥ b ≥ 0, по убыванию a: ((a b) …);
; (none p): простое p ≡ 3 (mod 4) входит в n в нечётной степени (сертификат отказа); n < 0 → (none -1)
; Гауссовы целые: каждому простому p ≡ 1 (mod 4) в степени k отвечают π^i·π̄^(k−i), i = 0…k.
(define (two-squares n)
  (cond ((not (integer? n)) (error "two-squares: n — целое число"))
        ((< n 0) (list 'none -1))
        ((= n 0) (list (list 0 0)))
        (else
         (let* ((fac (factor-integer n))
                (bad (filter (lambda (pk) (and (= (modulo (car pk) 4) 3) (odd? (cadr pk)))) fac)))
           (if (pair? bad)
               (begin
                 (if (step-log-enabled?)
                     (record-step 'sq-none "Представления нет"
                                  (string-append "простое " (to-string (car (car bad)))
                                                 " ≡ 3 (mod 4) входит в нечётной степени")
                                  n #f 'main))
                 (list 'none (car (car bad))))
               (let loop ((fs fac) (cands (list (list 1 0))))
                 (if (null? fs)
                     (let ((r (dio-sort-uniq (map dio-abs-pair cands))))
                       (if (every? (lambda (p) (nt-two-sq-ok? n (car p) (cadr p))) r)
                           (begin
                             (if (step-log-enabled?)
                                 (begin
                                   (record-step 'sq-representation "Найденное представление"
                                                (string-append (to-string (car (car r))) "² + "
                                                               (to-string (cadr (car r))) "² = n")
                                                (car r) r 'main)
                                   (record-step 'sq-check "Проверка суммы квадратов"
                                                "a² + b² = n: проверено" r #t 'main)))
                             (reverse r))
                           (error "two-squares: сертификат a² + b² = n не прошёл")))
                     (let* ((p (car (car fs))) (k (cadr (car fs)))
                            (opts (cond ((= p 2) (list (nt-two-sq-pow (list 1 1) k)))
                                        ((= (modulo p 4) 1)
                                         (let ((pi1 (nt-two-sq-prime p)))
                                           (map (lambda (i)
                                                  (nt-two-sq-mul (nt-two-sq-pow pi1 i)
                                                                 (nt-two-sq-pow (dio-gauss-conj pi1) (- k i))))
                                                (range (+ k 1)))))
                                        (else (list (list (^ p (quotient k 2)) 0))))))
                       (loop (cdr fs)
                             (append-map (lambda (c) (map (lambda (o) (nt-two-sq-mul c o)) opts)) cands))))))))))

; n = 4^a·(8b + 7)? → (a r), r = 8b + 7, иначе #f (условие Лежандра для трёх квадратов)
(define (dio-legendre n)
  (let loop ((m n) (a 0))
    (cond ((= (modulo m 4) 0) (loop (quotient m 4) (+ a 1)))
          ((= (modulo m 8) 7) (list a m))
          (else #f))))

(define (dio-sorted-desc lst) (sort lst >))

; (three-squares n) → (a b c), a ≥ b ≥ c ≥ 0, a² + b² + c² = n; (none legendre a r), n = 4^a·r, r ≡ 7 (mod 8)
(define (three-squares n)
  (cond ((not (integer? n)) (error "three-squares: n — целое число"))
        ((< n 0) (list 'none 'negative))
        ((= n 0) (list 0 0 0))
        ((dio-legendre n)
         (if (step-log-enabled?)
             (record-step 'sq-none "Представления нет"
                          (string-append "n = 4^" (to-string (car (dio-legendre n))) "·(8b + 7): критерий Лежандра")
                          n (cons 'none (cons 'legendre (dio-legendre n))) 'main))
         (cons 'none (cons 'legendre (dio-legendre n))))
        (else
         (let loop ((c (nt-isqrt n)))
           (if (< c 0)
               (error "three-squares: не найдено (противоречит теореме Гаусса)")
               (let* ((r (- n (* c c))))
                 (if (= (modulo r 4) 3)
                     (loop (- c 1))
                     (let ((s (sum-of-two-squares r)))
                       (if s
                           (let ((res (dio-sorted-desc (list (car s) (cadr s) c))))
                             (if (= (+ (* (car res) (car res)) (* (cadr res) (cadr res)) (* (caddr res) (caddr res))) n)
                                 (begin
                                   (if (step-log-enabled?)
                                       (begin
                                         (record-step 'sq-representation "Найденное представление"
                                                      "a² + b² + c² = n" n res 'main)
                                         (record-step 'sq-check "Проверка суммы квадратов"
                                                      "a² + b² + c² = n: проверено" res #t 'main)))
                                   res)
                                 (error "three-squares: сертификат не прошёл")))
                           (loop (- c 1)))))))))))

; (four-squares n) → (a b c d), a ≥ b ≥ c ≥ d ≥ 0, сумма квадратов n (Лагранж): a, b — наибольшие при
; условии, что остаток — сумма двух квадратов (остаток мал, поэтому факторизация дешёвая)
(define (four-squares n)
  (cond ((not (integer? n)) (error "four-squares: n — целое число"))
        ((< n 0) (list 'none 'negative))
        (else
         (let loop-a ((a (nt-isqrt n)))
           (if (< a 0)
               (error "four-squares: не найдено (противоречит теореме Лагранжа)")
               (let ((ra (- n (* a a))))
                 (let loop-b ((b (nt-isqrt ra)))
                   (if (< b 0)
                       (loop-a (- a 1))
                       (let ((r (- ra (* b b))))
                         (if (= (modulo r 4) 3)
                             (loop-b (- b 1))
                             (let ((s (sum-of-two-squares r)))
                               (if s
                                   (let ((res (dio-sorted-desc (list a b (car s) (cadr s)))))
                                     (if (= (foldl (lambda (acc x) (+ acc (* x x))) 0 res) n)
                                         (begin
                                           (if (step-log-enabled?)
                                               (begin
                                                 (record-step 'sq-representation "Найденное представление"
                                                              "a² + b² + c² + d² = n" n res 'main)
                                                 (record-step 'sq-check "Проверка суммы квадратов"
                                                              "a² + b² + c² + d² = n: проверено" res #t 'main)))
                                           res)
                                         (error "four-squares: сертификат не прошёл")))
                                   (loop-b (- b 1))))))))))))))

; (pythagorean-hypotenuse c) — все тройки (a b c), a < b, a² + b² = c² (не только примитивные), по возрастанию a
(define (pythagorean-hypotenuse c)
  (if (or (not (integer? c)) (< c 1))
      (error "pythagorean-hypotenuse: c — натуральное")
      (let ((reps (two-squares (* c c))))
        (dio-list (map (lambda (p) (list (cadr p) (car p) c))
                       (filter (lambda (p) (and (> (cadr p) 0) (> (car p) (cadr p)))) reps))))))

; (pythagorean-leg a) — все тройки (a b c): a — катет, b — другой катет, c — гипотенуза, по возрастанию c.
; c − b = d, c + b = e, d·e = a², d < e одной чётности
(define (pythagorean-leg a)
  (if (or (not (integer? a)) (< a 1))
      (error "pythagorean-leg: a — натуральное")
      (let ((a2 (* a a)))
        (dio-list (sort (append-map
               (lambda (d)
                 (let ((e (quotient a2 d)))
                   (if (and (< d e) (= (modulo (+ d e) 2) 0))
                       (list (list a (quotient (- e d) 2) (quotient (+ e d) 2)))
                       '())))
               (divisors a2))
              (lambda (p q) (< (caddr p) (caddr q))))))))

; ---- дискретный логарифм ----

; (multiplicative-order a n) — порядок a по модулю n (синоним order)
(define (multiplicative-order a n) (order a n))

; шаг малого-шага/большого-шага: d ∈ [0, q) с g^d ≡ h (mod p), g^q ≡ 1; #f, если нет
(define (dio-bsgs g h q p)
  (let* ((m (+ (nt-isqrt q) 1))
         (tbl (make-hash))
         (step (invmod (powmod g m p) p)))
    (let fill ((j 0) (cur 1))
      (if (< j m)
          (begin
            (if (not (hash-has? tbl cur)) (hash-set! tbl cur j))
            (fill (+ j 1) (modulo (* cur g) p)))
          #f))
    (let giant ((i 0) (y h))
      (if (> i m)
          #f
          (if (hash-has? tbl y)
              (let ((d (modulo (+ (* i m) (hash-ref tbl y)) q)))
                (if (= (powmod g d p) h) d #f))
              (giant (+ i 1) (modulo (* y step) p)))))))

; логарифм по подгруппе порядка q^e (Полиг–Хеллман): x mod q^e с gi^x ≡ hi, или #f
(define (dio-ph-prime-power gi hi q e p)
  (let ((gamma (powmod gi (^ q (- e 1)) p)))
    (let loop ((i 0) (x 0))
      (if (= i e)
          x
          (let* ((hh (powmod (modulo (* hi (invmod (powmod gi x p) p)) p) (^ q (- e 1 i)) p))
                 (d (dio-bsgs gamma hh q p)))
            (if d
                (loop (+ i 1) (+ x (* d (^ q i))))
                #f))))))

; (discrete-log g h p) → k ∈ [0, order g): g^k ≡ h (mod p), либо (none причина).
; Порядок n = order(g, p) (по разложению), Полиг–Хеллман по q^e ‖ n, в простых подгруппах — BSGS (≈ √q шагов), затем КТО.
; Модуль p может быть составным (g, h — взаимно просты с ним). Ответ проверен g^k ≡ h.
(define (discrete-log g h p)
  (cond ((not (and (integer? g) (integer? h) (integer? p))) (error "discrete-log: g, h, p — целые"))
        ((< p 2) (error "discrete-log: модуль ≥ 2"))
        (else
         (let ((g1 (modulo g p)) (h1 (modulo h p)))
           (cond ((not (= (gcd g1 p) 1)) (list 'none 'not-unit))
                 ((not (= (gcd h1 p) 1)) (list 'none 'not-in-subgroup))
                 (else
                  (let* ((n (order g1 p)) (fac (factor-integer n)))
                    (if (= n 1)
                        (if (= h1 1) 0 (list 'none 'not-in-subgroup))
                        (let ((rs (map (lambda (pk)
                                         (let* ((qe (^ (car pk) (cadr pk)))
                                                (gi (powmod g1 (quotient n qe) p))
                                                (hi (powmod h1 (quotient n qe) p)))
                                           (dio-ph-prime-power gi hi (car pk) (cadr pk) p)))
                                       fac)))
                          (if (any? (lambda (x) (not x)) rs)
                              (list 'none 'not-in-subgroup)
                              (let ((k (car (crt rs (map (lambda (pk) (^ (car pk) (cadr pk))) fac)))))
                                (if (= (powmod g1 k p) h1)
                                    k
                                    (list 'none 'not-in-subgroup)))))))))))))

; ---- проверка подстановкой ----

; (dioph-check eq vars solution) → #t/#f: подстановка целых solution вместо vars. eq — (= л п), (congruent л п m)
; или выражение (= 0); значения вычисляются eval (допустимы powmod и т. п.). Нецелое решение, ошибка — #f
(define (dioph-check eq vars solution)
  (try
   (if (or (not (= (length vars) (length solution))) (not (every? integer? solution)))
       #f
       (let* ((rules (map2 list vars solution))
              (ev (lambda (e) (eval (subst rules e)))))
         (cond ((and (pair? eq) (equal? (car eq) '=))
                (= (ev (cadr eq)) (ev (caddr eq))))
               ((and (pair? eq) (equal? (car eq) 'congruent))
                (let ((m (ev (nth eq 3))))
                  (= (modulo (- (ev (cadr eq)) (ev (caddr eq))) m) 0)))
               (else (= (ev eq) 0)))))
   (lambda (e) #f)))
