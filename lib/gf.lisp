; gf.lisp — Шаг NT.3: конечные поля GF(pⁿ) и многочлены над GF(p).
;
; Представление (по образцу lib\algnum.lisp — поле ℚ(α)):
;   ПОЛЕ — вектор #(p m n var): p — простое, m — коэффициенты неприводимого монического m (по возрастанию),
;     n = deg m, var — переменная m (нужна только для разбора выражения m);
;   ЭЛЕМЕНТ — список коэффициентов (c0 … c_{n−1}) по возрастанию, 0 ≤ cᵢ < p; ноль — ();
;   многочлены над GF(p) (gf-poly-gcd, gf-factor) — такие же списки любой степени.
;
; Сертификаты (задание NT.3): каждый ответ проверяется перед возвратом, независимо от того, как он получен:
;   gf-field — m неприводим (Рабин); gf+ и gf- — r + b = a; gf* — r/b = a (через обратный);
;   gf-inv — a·a⁻¹ = 1; gf/ — r·b = a; gf-power — вторая схема возведения (слева направо);
;   gf-order и gf-primitive? — a^d = 1 и a^(d/q) ≠ 1 для всех простых q | d;
;   gf-irreducible? — критерий Рабина (x^(p^n) ≡ x и НОД(x^(p^(n/q)) − x, f) = 1);
;   gf-factor — lc·∏ fᵢ^kᵢ = f и каждый fᵢ моничен и неприводим (Рабин).
; Приватные предикаты-сертификаты (gf::gf-…-ok?) вызываются и публичными функциями, и тестами с подделками.
;
; Имена: gf-pow занято (экспорт модуля summation) — возведение в степень в поле называется gf-power.
; Генератора случайных чисел в библиотеке нет: gf-random-irreducible берёт кандидатов из LCG-последовательности
; (134775813·s + 1 mod 2^32), а при неудаче перебирает монические многочлены по порядку; ответ всегда проверен.

(module gf
  (export gf-field gf-elt gf->int gf+ gf- gf* gf/ gf-inv gf-power gf-order
          gf-irreducible? gf-random-irreducible gf-primitive? gf-poly-gcd gf-factor))

; ---------- списки коэффициентов над GF(p) (по возрастанию) ----------

(define (gf-int-list? l)
  (cond ((null? l) #t)
        ((integer? (car l)) (gf-int-list? (cdr l)))
        (else #f)))

; (gf-as-cs x what) — x → список коэффициентов: целое → (c); список целых → как есть
(define (gf-as-cs x what)
  (cond ((integer? x) (list x))
        ((gf-int-list? x) x)
        (else (error (string-append what ": ожидается целое или список целых коэффициентов (по возрастанию)")))))

; убрать нули в конце списка (по возрастанию это старшие коэффициенты)
(define (gf-strip-top cs)
  (if (and (pair? cs) (= (car cs) 0)) (gf-strip-top (cdr cs)) cs))

; (gf-cs p cs) — канонический вид: коэффициенты по модулю p, старшие нули убраны
(define (gf-cs p cs)
  (reverse (gf-strip-top (reverse (map (lambda (c) (modulo c p)) cs)))))

(define (gf-deg a) (if (null? a) -1 (- (length a) 1)))
(define (gf-lc a) (if (null? a) 0 (last a)))
(define (gf-is-const a) (or (null? a) (null? (cdr a))))

; единица-константа (ненулевая константа) как многочлен
(define (gf-unit? a) (or (null? a) (and (null? (cdr a)) (not (= (car a) 0)))))

; дополнить нулями (старшими) до длины n
(define (gf-pad-to cs n)
  (if (>= (length cs) n) cs (append cs (map (lambda (i) 0) (range (- n (length cs)))))))

; покомпонентная операция с выравниванием длин (недостающие коэффициенты — 0)
(define (gf-pzip f a b)
  (cond ((null? a) (map (lambda (y) (f 0 y)) b))
        ((null? b) (map (lambda (x) (f x 0)) a))
        (else (cons (f (car a) (car b)) (gf-pzip f (cdr a) (cdr b))))))

(define (gf-padd p a b) (gf-cs p (gf-pzip (lambda (x y) (+ x y)) a b)))
(define (gf-psub p a b) (gf-cs p (gf-pzip (lambda (x y) (- x y)) a b)))
(define (gf-pscale p a c) (gf-cs p (map (lambda (x) (* x c)) a)))

; произведение — свёртка коэффициентов
(define (gf-pmul p a b)
  (if (or (null? a) (null? b))
      '()
      (let loop ((i 0) (acc '()))
        (if (>= i (length a))
            (gf-cs p acc)
            (let ((ai (nth a i)))
              (loop (+ i 1)
                    (gf-pzip (lambda (x y) (+ x y)) acc
                             (append (map (lambda (k) 0) (range i))
                                     (map (lambda (c) (* ai c)) b)))))))))

; a / старший коэффициент (моническая нормировка)
(define (gf-pmonic p a)
  (if (null? a) '() (gf-pscale p a (invmod (gf-lc a) p))))

; (gf-pdivmod p a b) → (q r): деление с остатком, a = q·b + r, deg r < deg b; b ≠ 0.
; Остаток не зависит от нормировки делителя, частное — зависит: оно домножается на 1/lc(b)
; (внутри деление идёт на монический bm = b/lc(b), поэтому q = q_bm·lc(b)⁻¹).
(define (gf-pdivmod p a b)
  (if (null? b)
      (error "gf: деление на нулевой многочлен")
      (let* ((s (invmod (gf-lc b) p))
             (bm (gf-pscale p b s))
             (n (gf-deg b)))
        (let loop ((r (gf-cs p a)) (q '()))
          (if (< (gf-deg r) n)
              (list (gf-pscale p (gf-cs p q) s) r)
              (let* ((k (- (gf-deg r) n))
                     (c (gf-lc r))
                     (term (append (map (lambda (i) 0) (range k)) (list c))))
                (loop (gf-psub p r (gf-pmul p term bm)) (gf-padd p q term))))))))

; остаток от деления на m (m ≠ 0)
(define (gf-pmod p a m)
  (if (null? m)
      (error "gf: остаток по нулевому модулю")
      (cadr (gf-pdivmod p a m))))

; НОД (монический)
(define (gf-pgcd p a b)
  (let loop ((a (gf-cs p a)) (b (gf-cs p b)))
    (if (null? b) (gf-pmonic p a) (loop b (gf-pmod p a b)))))

; a^k mod m (k ≥ 0, m ≠ 0)
(define (gf-ppowmod p a k m)
  (let loop ((b (gf-pmod p a m)) (e k) (acc (gf-cs p '(1))))
    (cond ((= e 0) (gf-pmod p acc m))
          ((odd? e) (loop (gf-pmod p (gf-pmul p b b) m) (quotient e 2) (gf-pmod p (gf-pmul p acc b) m)))
          (else (loop (gf-pmod p (gf-pmul p b b) m) (quotient e 2) acc)))))

; a^k без модуля (k ≥ 0)
(define (gf-ppow p a k)
  (let loop ((b a) (e k) (acc (gf-cs p '(1))))
    (cond ((= e 0) acc)
          ((odd? e) (loop (gf-pmul p b b) (quotient e 2) (gf-pmul p acc b)))
          (else (loop (gf-pmul p b b) (quotient e 2) acc)))))

; производная
(define (gf-pderiv p a)
  (if (or (null? a) (null? (cdr a)))
      '()
      (let loop ((i 1) (rest (cdr a)) (acc '()))
        (if (null? rest)
            (gf-cs p (reverse acc))
            (loop (+ i 1) (cdr rest) (cons (* i (car rest)) acc))))))

; (gf-ppow-root p f) — h с h(x)ᵖ = f (то есть f = h(xᵖ)); иначе ошибка
(define (gf-ppow-root p f)
  (let loop ((i 0) (rest f) (acc '()))
    (cond ((null? rest) (gf-cs p (reverse acc)))
          ((= (modulo i p) 0) (loop (+ i 1) (cdr rest) (cons (car rest) acc)))
          ((= (modulo (car rest) p) 0) (loop (+ i 1) (cdr rest) acc))
          (else (error "gf: многочлен не является p-й степенью")))))

; (gf-idx->poly p idx) — многочлен с номером idx: цифры по основанию p (младшая первой)
(define (gf-idx->poly p idx)
  (if (= idx 0)
      '()
      (let loop ((v idx) (acc '()))
        (if (= v 0) (gf-cs p (reverse acc)) (loop (quotient v p) (cons (modulo v p) acc))))))

; (gf-bits k) — двоичные цифры k ≥ 1 от старшей к младшей
(define (gf-bits k)
  (let loop ((v k) (acc '()))
    (if (= v 0) acc (loop (quotient v 2) (cons (modulo v 2) acc)))))

; (gf-poly-less? a b) — порядок многочленов: по степени, затем лексикографически по старшим коэффициентам
(define (gf-poly-less? a b)
  (cond ((< (gf-deg a) (gf-deg b)) #t)
        ((> (gf-deg a) (gf-deg b)) #f)
        ((null? a) #f)
        ((null? b) #t)
        (else (let ((x (last a)) (y (last b)))
                (cond ((< x y) #t)
                      ((> x y) #f)
                      (else (gf-poly-less? (butlast a) (butlast b))))))))

; ---------- неприводимость: критерий Рабина ----------

; (gf-irreducible-cs? f p) — f моничен (иначе нормируется), deg f ≥ 1
; Рабин: f неприводим ⇔ x^(pⁿ) ≡ x (mod f) и НОД(x^(p^(n/q)) − x, f) = 1 для каждого простого q | n
(define (gf-irreducible-cs? f p)
  (let ((n (gf-deg f)))
    (cond ((< n 1) #f)
          ((not (= (gf-lc f) 1)) (gf-irreducible-cs? (gf-pmonic p f) p))
          ((= n 1) #t)
          (else
           (let ((x (gf-cs p '(0 1))))
             (and (gf-unit? (gf-pgcd p f (gf-pderiv p f)))            ; бесквадратен
                  (equal? (gf-ppowmod p x (^ p n) f) x)               ; x^(pⁿ) ≡ x (mod f)
                  (every? (lambda (q)
                            (gf-unit? (gf-pgcd p
                                               (gf-psub p (gf-ppowmod p x (^ p (quotient n q)) f) x)
                                               f)))
                          (map car (factor-integer n)))))))))

; (gf-irreducible? f p) — неприводим ли многочлен f над GF(p)
(define (gf-irreducible? f p)
  (if (not (and (integer? p) (> p 1) (prime? p)))
      (error "gf-irreducible?: p должно быть простым")
      (gf-irreducible-cs? (gf-cs p (gf-as-cs f "gf-irreducible?")) p)))

; ---------- разложение на множители ----------

; (gf-sqfree p f) → ((g k) …): бесквадратные попарно взаимно простые g с кратностями k, ∏ gᵏ = f (f моничен)
; Цепочка НОД: w = f / НОД(f, f') = произведение всех различных неприводимых множителей,
; g = НОД(f, f'); на шаге i: z = НОД(w, g), fᵢ = w/z, w ← z, g ← g/z.
; Множители с кратностью, делящейся на p, в НОД(f, f') не видны — остаток возводится в p-ю степень обратно.
(define (gf-sqfree p f)
  (let ((d (gf-pderiv p f)))
    (cond ((null? d)                                  ; f = h(xᵖ): множители те же, кратности × p
           (map (lambda (gk) (list (car gk) (* (cadr gk) p)))
                (gf-sqfree p (gf-ppow-root p f))))
          (else
           (let* ((g0 (gf-pgcd p f d))
                  (w0 (car (gf-pdivmod p f g0))))
             (let loop ((i 1) (w w0) (g g0) (acc '()))
               (cond ((gf-unit? w)
                      (let* ((prod (foldl (lambda (a2 gk) (gf-pmul p a2 (gf-ppow p (car gk) (cadr gk))))
                                          (gf-cs p '(1)) acc))
                             (res (car (gf-pdivmod p f prod))))
                        (if (gf-unit? res)
                            (reverse acc)
                            (append (reverse acc)
                                    (map (lambda (gk) (list (car gk) (* (cadr gk) p)))
                                         (gf-sqfree p (gf-ppow-root p res)))))))
                     (else
                      (let* ((z (gf-pgcd p w g))
                             (fi (car (gf-pdivmod p w z))))
                        (loop (+ i 1) z (car (gf-pdivmod p g z))
                              (if (gf-unit? fi) acc (cons (list fi i) acc))))))))))))

; (gf-ddf p f) → ((h d) …): h — произведение всех неприводимых множителей f степени d
; (f моничен и бесквадратен); остаток должен быть неприводим, поэтому d = deg остатка
(define (gf-ddf p f)
  (let loop ((d 1) (g (gf-cs p f)) (xp (gf-cs p '(0 1))) (acc '()))
    (cond ((gf-unit? g) (reverse acc))
          ((> (* 2 d) (gf-deg g)) (reverse (cons (list g (gf-deg g)) acc)))
          (else
           (let* ((xq (gf-ppowmod p xp p g))                     ; x^(p^d) mod g
                  (h (gf-pgcd p (gf-psub p xq (gf-cs p '(0 1))) g)))
             (if (gf-unit? h)
                 (loop (+ d 1) g xq acc)
                 (let ((g2 (car (gf-pdivmod p g h))))
                   (loop (+ d 1) g2 (gf-pmod p xq g2) (cons (list h d) acc)))))))))

; (gf-edf-trace p h d a) — след-отображение для p = 2: a + a² + a⁴ + … + a^(2^(d−1)) (d слагаемых,
; то есть Tr из GF(2^d) в GF(2) для каждого из множителей h)
(define (gf-edf-trace p h d a)
  (let loop ((j 1) (cur a) (acc a))
    (if (>= j d)
        acc
        (let ((cur2 (gf-ppowmod p cur 2 h)))
          (loop (+ j 1) cur2 (gf-padd p acc cur2))))))

; (gf-edf p h d) → неприводимые множители h (Кантор–Цассенхаус; каждый степени d, deg h = m·d)
; Кандидат a перебирается по порядку номеров (гарантирует завершение; для чётного p — след-отображение)
(define (gf-edf p h d)
  (if (= (gf-deg h) d)
      (list h)
      (let ((total (^ p (gf-deg h))))
        (let loop ((idx 1))
          (if (> idx total)
              (error "gf-edf: Кантор-Цассенхаус не нашёл расщепление")
              (let* ((a (gf-pmod p (gf-idx->poly p idx) h))
                     (t (if (= p 2)
                            (gf-edf-trace p h d a)
                            (gf-psub p (gf-ppowmod p a (quotient (- (^ p d) 1) 2) h) (gf-cs p '(1))))))
                (let ((g (gf-pgcd p t h)))
                  (if (and (not (gf-unit? g)) (< (gf-deg g) (gf-deg h)))
                      (append (gf-edf p g d) (gf-edf p (car (gf-pdivmod p h g)) d))
                      (loop (+ idx 1))))))))))

; (gf-factor-squarefree p g) — неприводимые множители бесквадратного g (список; g моничен, ≠ const)
(define (gf-factor-squarefree p g)
  (append-map (lambda (hd) (gf-edf p (car hd) (cadr hd))) (gf-ddf p g)))

; (gf-factor-ok? fac f p) — сертификат разложения fac = (lc ((fᵢ kᵢ) …)):
; lc ≠ 0 (mod p), каждый fᵢ моничен и неприводим (Рабин), произведение lc·∏ fᵢ^kᵢ = f
(define (gf-factor-ok? fac f p)
  (and (list? fac)
       (= (length fac) 2)
       (integer? (car fac))
       (not (= (modulo (car fac) p) 0))
       (list? (cadr fac))
       (every? (lambda (fk)
                 (and (pair? fk)
                      (= (length fk) 2)
                      (pair? (car fk))
                      (integer? (cadr fk))
                      (>= (cadr fk) 1)
                      (= (gf-lc (car fk)) 1)
                      (gf-irreducible-cs? (car fk) p)))
               (cadr fac))
       (let ((prod (foldl (lambda (acc fk) (gf-pmul p acc (gf-ppow p (car fk) (cadr fk))))
                          (gf-cs p '(1)) (cadr fac))))
         (equal? (gf-pscale p prod (car fac)) (gf-cs p (gf-as-cs f "gf-factor-ok?"))))))

; (gf-factor f p) → (lc ((f1 k1) …)): lc — старший коэффициент (число), fᵢ — монические неприводимые;
; для нулевого многочлена — ошибка, для константы lc ≠ 0 → (lc ())
(define (gf-factor f p)
  (if (not (and (integer? p) (> p 1) (prime? p)))
      (error "gf-factor: p должно быть простым")
      (let ((cs (gf-cs p (gf-as-cs f "gf-factor"))))
        (cond ((null? cs) (error "gf-factor: нулевой многочлен не раскладывается"))
              ((gf-is-const cs) (list (car cs) '()))
              (else
               (let* ((pairs (sort (append-map (lambda (gk)
                                                 (map (lambda (h) (list h (cadr gk)))
                                                      (gf-factor-squarefree p (car gk))))
                                               (gf-sqfree p (gf-pmonic p cs)))
                                   (lambda (x y) (gf-poly-less? (car x) (car y)))))
                      (res (list (gf-lc cs) pairs)))
                 (if (gf-factor-ok? res cs p)
                     res
                     (error "gf-factor: сертификат (произведение и неприводимость) не прошёл"))))))))

; ---------- поле GF(pⁿ) ----------

(define (gf-f-p F) (vref F 0))     ; p — простое
(define (gf-f-cs F) (vref F 1))    ; коэффициенты m по возрастанию
(define (gf-f-n F) (vref F 2))     ; deg m
(define (gf-f-var F) (vref F 3))   ; переменная m

; (gf-field p m t) — поле GF(pⁿ): p — простое, m — неприводимый над GF(p) многочлен степени n ≥ 1
; (список коэффициентов по возрастанию либо выражение от t), t — переменная m
(define (gf-field p m t)
  (if (not (and (integer? p) (> p 1) (prime? p)))
      (error "gf-field: p должно быть простым")
      (let ((raw (if (and (pair? m) (symbol? (car m))) (coefficients m t) (gf-as-cs m "gf-field"))))
        (cond ((not (gf-int-list? raw)) (error "gf-field: коэффициенты m должны быть целыми"))
              (else
               (let* ((cs (gf-cs p raw))
                      (n (gf-deg cs)))
                 (cond ((null? cs) (error "gf-field: m — ненулевой многочлен"))
                       ((< n 1) (error "gf-field: степень m должна быть ≥ 1"))
                       ((not (= (gf-lc cs) 1)) (error "gf-field: m должен быть моническим"))
                       ((not (gf-irreducible-cs? cs p))
                        (error "gf-field: m приводим над GF(p) — поле не строится"))
                       (else (vector p cs n t)))))))))

; (gf-elt F x) — элемент поля: список коэффициентов (берутся первые n) или целое (цифры по основанию p)
(define (gf-elt F x)
  (let* ((p (gf-f-p F))
         (n (gf-f-n F))
         (cs (cond ((integer? x)
                    (if (< x 0)
                        (error "gf-elt: целое должно быть неотрицательным")
                        (gf-idx->poly p (modulo x (^ p n)))))
                   ((gf-int-list? x) x)
                   (else (error "gf-elt: элемент — целое или список целых коэффициентов (по возрастанию)")))))
    (gf-cs p (take cs (min n (length cs))))))

; (gf->int F a) — целое по цифрам коэффициентов (обратно к gf-elt для целых)
(define (gf->int F a)
  (let ((p (gf-f-p F)))
    (let loop ((cs (gf-elt F a)) (k 1) (acc 0))
      (if (null? cs) acc (loop (cdr cs) (* k p) (+ acc (* (car cs) k)))))))

; (gf-mul-raw F a b) — произведение элементов по модулю m (без проверки)
(define (gf-mul-raw F a b)
  (gf-pmod (gf-f-p F) (gf-pmul (gf-f-p F) a b) (gf-f-cs F)))

; коэффициенты Безу над GF(p)[x]: (g s t), s·a + t·b = g (g моничен)
(define (gf-bezout p a b)
  (let loop ((r0 (gf-cs p a)) (r1 (gf-cs p b))
             (s0 (gf-cs p '(1))) (s1 '())
             (t0 '()) (t1 (gf-cs p '(1))))
    (if (null? r1)
        (if (null? r0)
            (list '() '() '())
            (let ((c (invmod (gf-lc r0) p)))
              (list (gf-pscale p r0 c) (gf-pscale p s0 c) (gf-pscale p t0 c))))
        (let* ((dr (gf-pdivmod p r0 r1))
               (q (car dr))
               (r2 (cadr dr)))
          (loop r1 r2 s1 (gf-psub p s0 (gf-pmul p q s1)) t1 (gf-psub p t0 (gf-pmul p q t1)))))))

; обратный элемент (без проверки): #f, если a = 0 или НОД(a, m) ≠ 1 (для неприводимого m — только a = 0)
(define (gf-inv-raw F a)
  (if (null? a)
      #f
      (let* ((p (gf-f-p F))
             (r (gf-bezout p a (gf-f-cs F))))
        (if (gf-unit? (car r))
            (gf-pmod p (cadr r) (gf-f-cs F))
            #f))))

; (gf-inv-ok? F a b) — сертификат: b ненулевой и a·b = 1 в F
(define (gf-inv-ok? F a b)
  (let ((x (gf-elt F a))
        (y (gf-elt F b)))
    (and (pair? y) (equal? (gf-mul-raw F x y) (gf-cs (gf-f-p F) '(1))))))

; (gf-inv F a) — обратный элемент поля; #f для нуля
(define (gf-inv F a)
  (let* ((x (gf-elt F a))
         (r (gf-inv-raw F x)))
    (cond ((not r) #f)
          ((not (gf-inv-ok? F x r)) (error "gf-inv: сертификат a·a⁻¹ = 1 не прошёл"))
          (else r))))

; (gf+ F a b) — сложение элементов (степени < n, редукция не нужна)
(define (gf+ F a b)
  (let* ((p (gf-f-p F))
         (x (gf-elt F a))
         (y (gf-elt F b))
         (r (gf-padd p x y)))
    (if (equal? (gf-psub p r y) x)
        r
        (error "gf+: сертификат (r + b = a) не прошёл"))))

; (gf- F a b) — вычитание элементов
(define (gf- F a b)
  (let* ((p (gf-f-p F))
         (x (gf-elt F a))
         (y (gf-elt F b))
         (r (gf-psub p x y)))
    (if (equal? (gf-padd p r y) x)
        r
        (error "gf-: сертификат (r + b = a) не прошёл"))))

; (gf* F a b) — умножение по модулю m; сертификат r/b = a (для ненулевого b)
(define (gf* F a b)
  (let* ((x (gf-elt F a))
         (y (gf-elt F b))
         (r (gf-mul-raw F x y)))
    (if (or (null? y)
            (let ((q (gf-inv-raw F y)))
              (and q (equal? (gf-mul-raw F r q) x))))
        r
        (error "gf*: сертификат (r / b = a) не прошёл"))))

; (gf/ F a b) — деление; сертификат r·b = a
(define (gf/ F a b)
  (let ((x (gf-elt F a))
        (y (gf-elt F b)))
    (if (null? y)
        (error "gf/: деление на нуль поля")
        (let* ((inv (gf-inv-raw F y))
               (r (gf-mul-raw F x inv)))
          (if (equal? (gf-mul-raw F r y) x)
              r
              (error "gf/: сертификат (r·b = a) не прошёл"))))))

; возведение в степень справа налево (основная схема)
(define (gf-pow-rl F x k)
  (let loop ((b x) (e k) (acc (gf-cs (gf-f-p F) '(1))))
    (cond ((= e 0) acc)
          ((odd? e) (loop (gf-mul-raw F b b) (quotient e 2) (gf-mul-raw F acc b)))
          (else (loop (gf-mul-raw F b b) (quotient e 2) acc)))))

; возведение в степень слева направо (независимая проверка)
(define (gf-pow-lr F x k)
  (let loop ((bs (cdr (gf-bits k))) (acc x))
    (if (null? bs)
        acc
        (loop (cdr bs)
              (if (= (car bs) 1) (gf-mul-raw F (gf-mul-raw F acc acc) x) (gf-mul-raw F acc acc))))))

; (gf-power F a k) — a^k, k — целое (отрицательное — через обратный); сертификат — вторая схема
(define (gf-power F a k)
  (if (not (integer? k))
      (error "gf-power: показатель — целое число")
      (let* ((p (gf-f-p F))
             (x (gf-elt F a)))
        (cond ((= k 0) (gf-cs p '(1)))
              ((< k 0)
               (let ((inv (gf-inv F x)))
                 (if (not inv)
                     (error "gf-power: у нуля нет обратного")
                     (let* ((e (- k))
                            (r (gf-pow-rl F inv e)))
                       (if (equal? (gf-mul-raw F r (gf-pow-rl F x e)) (gf-cs p '(1)))
                           r
                           (error "gf-power: сертификат r·a^|k| = 1 не прошёл"))))))
              (else
               (let ((r (gf-pow-rl F x k)))
                 (if (equal? r (gf-pow-lr F x k))
                     r
                     (error "gf-power: сертификат (схема слева направо) не прошёл"))))))))

; (gf-order-ok? F a d) — сертификат порядка: a^d = 1 и a^(d/q) ≠ 1 для всех простых q | d
(define (gf-order-ok? F a d)
  (let ((one (gf-cs (gf-f-p F) '(1))))
    (and (integer? d)
         (>= d 1)
         (equal? (gf-power F a d) one)
         (every? (lambda (q) (not (equal? (gf-power F a (quotient d q)) one)))
                 (map car (factor-integer d))))))

; (gf-order F a) — порядок a в мультипликативной группе GF(pⁿ)*; #f для нуля
(define (gf-order F a)
  (let* ((p (gf-f-p F))
         (x (gf-elt F a)))
    (if (null? x)
        #f
        (let* ((nn (- (^ p (gf-f-n F)) 1))
               (one (gf-cs p '(1)))
               (d (foldl (lambda (acc q)
                           (let loop ((d acc))
                             (if (and (= (modulo d q) 0)
                                      (equal? (gf-pow-rl F x (quotient d q)) one))
                                 (loop (quotient d q))
                                 d)))
                         nn
                         (map car (factor-integer nn)))))
          (if (gf-order-ok? F x d)
              d
              (error "gf-order: сертификат порядка не прошёл"))))))

; (gf-primitive? a F) — порождает ли a мультипликативную группу (порядок равен pⁿ − 1)
(define (gf-primitive? a F)
  (let ((x (gf-elt F a)))
    (and (not (null? x)) (= (gf-order F x) (- (^ (gf-f-p F) (gf-f-n F)) 1)))))

; ---------- многочлены над GF(p): НОД ----------

; (gf-pgcd-ok? p a b r) — сертификат НОД: r моничен, делит a и b, a/r и b/r взаимно просты
(define (gf-pgcd-ok? p a b r)
  (cond ((null? r) (and (null? a) (null? b)))
        ((not (= (gf-lc r) 1)) #f)
        ((not (null? (gf-pmod p a r))) #f)
        ((not (null? (gf-pmod p b r))) #f)
        (else
         (gf-unit? (gf-pgcd p (car (gf-pdivmod p a r)) (car (gf-pdivmod p b r)))))))

; (gf-poly-gcd f g p) — НОД многочленов над GF(p) (монический), списки коэффициентов по возрастанию
(define (gf-poly-gcd f g p)
  (if (not (and (integer? p) (> p 1) (prime? p)))
      (error "gf-poly-gcd: p должно быть простым")
      (let* ((a (gf-cs p (gf-as-cs f "gf-poly-gcd")))
             (b (gf-cs p (gf-as-cs g "gf-poly-gcd")))
             (r (gf-pgcd p a b)))
        (if (gf-pgcd-ok? p a b r)
            r
            (error "gf-poly-gcd: сертификат (r | a, r | b, a/r и b/r взаимно просты) не прошёл")))))

; ---------- случайный неприводимый многочлен ----------

(define *gf-rng* 20261022)

; линейный конгруэнтный генератор: берутся старшие 16 бит состояния (младшие биты LCG коррелированы)
(define (gf-rng-next)
  (set! *gf-rng* (modulo (+ (* 1664525 *gf-rng*) 1013904223) 4294967296))
  (quotient *gf-rng* 65536))

; монический многочлен степени n со случайными младшими коэффициентами
(define (gf-random-monic p n)
  (gf-cs p (append (map (lambda (i) (modulo (gf-rng-next) p)) (range n)) (list 1))))

; (gf-random-irreducible p n) — неприводимый монический многочлен степени n над GF(p):
; до 200 кандидатов из генератора, затем перебор монических многочленов по порядку; ответ проверен Рабином
(define (gf-random-irreducible p n)
  (if (or (not (integer? p)) (< p 2) (not (prime? p)) (not (integer? n)) (< n 1))
      (error "gf-random-irreducible: p — простое, n — целое ≥ 1")
      (let ((total (^ p n)))
        (let loop ((k 0))
          (cond ((< k 200)
                 (let ((f (gf-random-monic p n)))
                   (if (gf-irreducible-cs? f p) f (loop (+ k 1)))))
                ((> total 1000000)
                 (error "gf-random-irreducible: неприводимый многочлен не найден за 200 проб"))
                (else
                 (let scan ((i 0))
                   (if (>= i total)
                       (error "gf-random-irreducible: неприводимый многочлен не найден")
                       (let ((f (gf-cs p (append (gf-pad-to (gf-idx->poly p i) n) (list 1)))))
                         (if (gf-irreducible-cs? f p) f (scan (+ i 1))))))))))))
