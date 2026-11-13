; cantor.lisp — тесты шага R5.3a: арифметика Кантора якобиана y² = P(x), deg P нечётна.

(define cnt-inf (list 'inf 'ram))

; место (a b): b — число, ram или элемент ℚ(√…) как в hyp-principal
(define (cnt-pl a b)
  (if (equal? b 'ram)
      (list a 'ram)
      (list a (integrate::ib-k-scale (integrate::ib-k-sqrt-rat (* b b)) (if (< b 0) -1 1)))))

; точки (a b n), a = inf — O
(define (cnt-div pts)
  (map (lambda (t) (cons (if (equal? (car t) 'inf) cnt-inf (cnt-pl (car t) (cadr t))) (nth t 2))) pts))

(define (cnt-nums n) (map (lambda (i) (+ i 1)) (range n)))

; (hyp-principal ⇔ cantor-zero?) для n = 1…N: список (n zero? verdict)
(define (cnt-table P pts N)
  (let* ((C (cantor-curve P 'x)) (D (cnt-div pts)) (cd (cantor-from-points C D)))
    (map (lambda (n)
           (let ((r (hyp-principal (dv-scale D n) P 'x)))
             (list n (cantor-zero? (cantor-mul C n cd)) (if (pair? r) (car r) r))))
         (cnt-nums N))))

; согласие: Кантор «нуль» ⇒ principal; Кантор «не нуль» ⇒ не principal (unknown допустим)
(define (cnt-agree? tbl)
  (every? (lambda (r) (if (cadr r) (equal? (caddr r) 'principal) (not (equal? (caddr r) 'principal)))) tbl))

(define (cnt-pt->rep pt)
  (if (equal? pt 'O) '((1) ()) (list (list (- (car pt)) 1) (list (cadr pt)))))

(deftest "cantor: род 1, y² = 4x³ − 15x² + 8x + 16 (lc ≠ 1): (0,4) − O порядка 7, kD = ec-multiples"
  (let* ((P '(+ (* 4 (^ x 3)) (* -15 (^ x 2)) (* 8 x) 16))
         (C (cantor-curve P 'x))
         (Dl (list (cons (list 0 4) 1) (cons cnt-inf -1)))
         (D (cantor-from-points C Dl))
         (ms (ec-multiples P 'x Dl 7)))
    (assert-equal '((0 1) (4)) D)
    (assert-true (cantor-valid? C D))
    (assert-equal 7 (cantor-order-upto C D 20))
    (assert-true (cantor-zero? (cantor-mul C 7 D)))
    (assert-true (every? (lambda (km) (equal? (cnt-pt->rep (cadr km)) (cantor-mul C (car km) D))) ms))
    (assert-true (every? (lambda (k) (not (cantor-zero? (cantor-mul C k D)))) (cnt-nums 6)))
    ; сложение, удвоение, отрицательные кратные
    (assert-equal (cantor-mul C 2 D) (cantor-double C D))
    (assert-true (cantor-zero? (cantor-add C (cantor-mul C 3 D) (cantor-mul C 4 D))))
    (assert-true (cantor-zero? (cantor-add C (cantor-mul C 3 D) (cantor-mul C -3 D))))))

(deftest "cantor: группа — ассоциативность, обратный, отрицательные n (род 2)"
  (let* ((P '(+ (^ x 5) (- x) 1))
         (C (cantor-curve P 'x))
         (A (cantor-from-points C (list (cons (list 0 1) 1) (cons cnt-inf -1))))
         (B (cantor-from-points C (list (cons (list 1 1) 1) (cons cnt-inf -1))))
         (E (cantor-from-points C (list (cons (list -1 -1) 1) (cons cnt-inf -1)))))
    (assert-true (cantor-valid? C A))
    (assert-equal (cantor-add C (cantor-add C A B) E) (cantor-add C A (cantor-add C B E)))
    (assert-equal (cantor-add C A B) (cantor-add C B A))
    (assert-true (cantor-zero? (cantor-add C A (cantor-neg C A))))
    (assert-equal (cantor-neg C (cantor-mul C 5 A)) (cantor-mul C -5 A))
    (assert-equal (cantor-add C (cantor-mul C 3 A) (cantor-mul C 4 A)) (cantor-mul C 7 A))
    (assert-true (cantor-zero? (cantor-mul C 0 A)))
    (assert-true (cantor-valid? C (cantor-mul C 11 (cantor-add C A B))))))

(deftest "cantor: род 2, x⁵ + 1 — Кантор против hyp-principal (L(D))"
  (let ((P '(+ (^ x 5) 1)))
    ; (0,1) − O: порядок 5
    (let ((t1 (cnt-table P '((0 1 1) (inf 0 -1)) 6)))
      (assert-equal '(#f #f #f #f #t #f) (map cadr t1))
      (assert-equal '(not-principal not-principal not-principal not-principal principal not-principal) (map caddr t1)))
    ; (−1,0) − O: порядок 2
    (let ((t2 (cnt-table P '((-1 ram 1) (inf 0 -1)) 2)))
      (assert-equal '(#f #t) (map cadr t2))
      (assert-equal '(not-principal principal) (map caddr t2)))
    ; (0,1) + (−1,0) − 2O: порядок 10; hyp-principal для кратных мест — unknown/не главен, но 10 — principal
    (let ((t3 (cnt-table P '((0 1 1) (-1 ram 1) (inf 0 -2)) 10)))
      (assert-equal '(#f #f #f #f #f #f #f #f #f #t) (map cadr t3))
      (assert-equal 'principal (caddr (nth t3 9)))
      (assert-true (cnt-agree? t3)))))

(deftest "cantor: род 2, y² = 4x⁵ + 1 (lc ≠ 1) и x⁵ − x + 1, x⁵ − x"
  (assert-equal '(#f #f #f #f #t #f) (map cadr (cnt-table '(+ (* 4 (^ x 5)) 1) '((0 1 1) (inf 0 -1)) 6)))
  ; (0,1) − O на x⁵ − x + 1 — не кручение (порядок > 6), hyp-principal согласен
  (let ((t (cnt-table '(+ (^ x 5) (- x) 1) '((0 1 1) (inf 0 -1)) 6)))
    (assert-equal '(#f #f #f #f #f #f) (map cadr t))
    (assert-true (cnt-agree? t)))
  ; x⁵ − x: точка ветвления
  (let ((t (cnt-table '(+ (^ x 5) (- x)) '((0 ram 1) (inf 0 -1)) 2)))
    (assert-equal '(#f #t) (map cadr t))
    (assert-true (cnt-agree? t))))

(deftest "cantor: род 3 и 4 — x⁷ + 1 (порядок 7, 2), x⁹ + 1 (9, 2), x⁷ + x + 1 (не кручение)"
  (let ((t7 (cnt-table '(+ (^ x 7) 1) '((0 1 1) (inf 0 -1)) 8)))
    (assert-equal '(#f #f #f #f #f #f #t #f) (map cadr t7))
    (assert-true (cnt-agree? t7))
    (assert-equal 'principal (caddr (nth t7 6))))
  (let ((t9 (cnt-table '(+ (^ x 9) 1) '((0 1 1) (inf 0 -1)) 10)))
    (assert-equal '(#f #f #f #f #f #f #f #f #t #f) (map cadr t9))
    (assert-true (cnt-agree? t9)))
  (let ((t (cnt-table '(+ (^ x 9) 1) '((-1 ram 1) (inf 0 -1)) 3)))
    (assert-equal '(#f #t #f) (map cadr t))
    (assert-true (cnt-agree? t)))
  (let ((t (cnt-table '(+ (^ x 7) x 1) '((0 1 1) (inf 0 -1)) 5)))
    (assert-equal '(#f #f #f #f #f) (map cadr t))
    (assert-true (cnt-agree? t))))

(deftest "cantor: δ из вычетов ∫dx/(x√P) — порядок = показатель логарифма, или не кручение"
  (let ((go (lambda (P)
              (let* ((C (cantor-curve P 'x))
                     (rd (residue-divisors (hyp-residues '(/ 1 (* x y)) P 'x))))
                (cantor-order-upto C (cantor-from-points C (cadr (car (cdr rd)))) 30)))))
    (assert-equal 7 (go '(+ (^ x 7) 1)))
    (assert-equal 9 (go '(+ (^ x 9) 1)))
    (assert-equal 5 (go '(+ (^ x 5) 1)))
    (assert-equal #f (go '(+ (^ x 7) x 1)))))

(deftest "cantor: 𝔽_p — порядок образа делит #J(𝔽_p), для кручения порядка n равен n"
  (let* ((P '(+ (^ x 7) 1)) (C (cantor-curve P 'x))
         (D (cantor-from-points C (list (cons (list 0 1) 1) (cons cnt-inf -1)))))
    (assert-equal 7 (cantor-order-mod-p C D 3))
    (assert-equal 7 (cantor-order-mod-p C D 5))
    (assert-equal 7 (cantor-order-mod-p C D 11))
    (assert-equal 28 (hyp-jacobian-order P 'x 3)))
  ; не кручение: порядок mod p делит #J, разный на разных p
  (let* ((P '(+ (^ x 9) (* 3 (^ x 7)) (* -2 (^ x 3)) x 1)) (C (cantor-curve P 'x))
         (D (cantor-from-points C (list (cons (list 1 2) 1) (cons cnt-inf -1))))
         (o3 (cantor-order-mod-p C D 3)) (o5 (cantor-order-mod-p C D 5)))
    (assert-equal 14 o3)
    (assert-equal 0 (remainder (integrate::hyp-jacobian-pick P 'x 3) o3))
    (assert-equal 0 (remainder (integrate::hyp-jacobian-pick P 'x 5) o5))
    (assert-true (not (= o3 o5)))
    ; плохое p (p = 2, не простое, знаменатель)
    (assert-equal #f (cantor-order-mod-p C D 2))
    (assert-equal #f (cantor-order-mod-p C D 9))
    (assert-equal #f (cantor-mod-p '((1/3 1) (1)) 3))
    (assert-equal '((2 1) (1)) (cantor-mod-p '((1/3 1) (1)) 5))))

(deftest "cantor: подделки и вырожденный ввод"
  (let* ((P '(+ (^ x 5) 1)) (C (cantor-curve P 'x)))
    ; u ∤ v² − P
    (assert-true (not (cantor-valid? C '((0 1) (2)))))
    (assert-true (not (cantor-valid? C '((-1 1) (3)))))
    (assert-error (cantor-add C '((0 1) (2)) '((1) ())))
    (assert-error (cantor-mul C 3 '((0 1) (2))))
    ; u не монический, deg v ≥ deg u, deg u > g, не список
    (assert-true (not (cantor-valid? C '((0 2) (1)))))
    (assert-true (not (cantor-valid? C '((1) (1)))))
    (assert-true (not (cantor-valid? C '((0 1) (1 1)))))
    (assert-true (not (cantor-valid? C '((0 0 0 1) (1)))))
    (assert-true (not (cantor-valid? C '(() ()))))
    (assert-true (not (cantor-valid? C '())))
    (assert-true (not (cantor-valid? C 5)))
    (assert-true (not (cantor-valid? C '((0 1.0) (1)))))
    ; нуль — только ((1) ()); вырожденное — не нуль
    (assert-true (cantor-zero? '((1) ())))
    (assert-true (not (cantor-zero? '(() ()))))
    (assert-true (not (cantor-zero? '())))
    (assert-true (not (cantor-zero? '((1) (0)))))
    (assert-true (not (cantor-zero? '((1) (1)))))
    ; точки: не на кривой, не над ℚ, на ∞ не ram
    (assert-error (cantor-from-points C (list (cons (list 0 2) 1))))
    (assert-error (cantor-from-points C (list (cons (list 1 'ram) 1))))
    (assert-error (cantor-from-points C (list (cons (list 'inf 1) 1))))
    (assert-error (cantor-from-points C 'bad))
    (assert-true (cantor-zero? (cantor-from-points C '())))
    (assert-true (cantor-zero? (cantor-from-points C (list (cons cnt-inf 3)))))
    ; reduce: u ∤ v² − P
    (assert-error (cantor-reduce C '(0 1) '(2)))
    (assert-error (cantor-reduce C '() '(1)))
    ; чётная степень, особая кривая, род 0, не многочлен, плохое p
    (assert-error (cantor-curve '(+ (^ x 4) 1) 'x))
    (assert-error (cantor-curve '(* (^ x 2) (+ x 1)) 'x))
    (assert-error (cantor-curve '(+ (^ x 3) (* 2 (^ x 2)) x) 'x))
    (assert-error (cantor-curve '(+ x 1) 'x))
    (assert-error (cantor-curve '(+ (^ x 3) a) 'x))
    (assert-error (cantor-curve P 'x 2))
    (assert-error (cantor-curve P 'x 5))      ; x⁵ + 1 ≡ (x+1)⁵ mod 5 — особая
    (assert-equal #f (cantor-curve-mod-p C 5))))

(deftest "cantor: cantor-reduce приводит произвольную пару (u = (y − v)-норма большой степени)"
  (let* ((P '(+ (^ x 3) 1)) (C (cantor-curve P 'x))
         ; u = x²(x − 2)·… : берём u = (x)(x − 2)(x + 1) = v²−P при v = ?  — используем нули (0,1), (2,3), (-1,0)
         (D1 (cantor-from-points C (list (cons (list 0 1) 1))))
         (D2 (cantor-from-points C (list (cons (list 2 3) 1))))
         (D3 (cantor-from-points C (list (cons (list -1 'ram) 1))))
         (s (cantor-add C (cantor-add C D1 D2) D3)))
    ; интерполяция v по трём точкам: v(0) = 1, v(2) = 3, v(−1) = 0 → v = x² − ... (деg 2)
    ; v = a x² + b x + 1: v(2) = 4a + 2b + 1 = 3, v(−1) = a − b + 1 = 0 → a = 0, b = 1  → v = x + 1
    (assert-equal s (cantor-reduce C '(0 -2 -1 1) '(1 1)))
    (assert-true (cantor-valid? C s))))

(deftest "cantor: род 9 над 𝔽₃ — n = 7, 100, 1000 быстро, порядок согласован"
  (let* ((P '(+ (^ x 19) (* 3 (^ x 7)) (* -2 (^ x 3)) x 1))
         (C0 (cantor-curve P 'x))
         (D0 (cantor-from-points C0 (list (cons (list 1 2) 1) (cons cnt-inf -1))))
         (C (cantor-curve-mod-p C0 3)) (D (cantor-mod-p D0 3)))
    (assert-true (cantor-valid? C D))
    (assert-true (every? (lambda (n) (cantor-valid? C (cantor-mul C n D))) '(7 100 1000)))
    (assert-equal (cantor-mul C 1000 D) (cantor-mul C 8 (cantor-mul C 125 D)))
    (assert-equal (cantor-mul C 1000 D) (cantor-add C (cantor-mul C 900 D) (cantor-mul C 100 D)))))

(deftest "cantor: над ℚ — рост коэффициентов, точность"
  (let* ((P '(+ (^ x 9) (* 3 (^ x 7)) (* -2 (^ x 3)) x 1)) (C (cantor-curve P 'x))
         (D (cantor-from-points C (list (cons (list 1 2) 1) (cons cnt-inf -1))))
         (R (cantor-mul C 7 D)))
    (assert-true (cantor-valid? C R))
    (assert-true (cantor-valid? C (cantor-mul C 20 D)))
    (assert-equal (cantor-mul C 20 D) (cantor-add C (cantor-mul C 13 D) R))
    (assert-true (not (cantor-zero? R)))))

; ---------- R5.3b: Кантор в лог-части алгебраического Риша ----------

(define cnb-D (cnt-div (list (list 0 1 1) (list 0 -1 -1))))   ; δ = (0, 1) − (0, −1)
(define cnb-H '(/ 1 (* x y)))                                   ; ∫ dx/(x y)

(deftest "cantor R5.3b: x^9+1 — кручение 9 (p = 5: p = 3 плохое), m·δ = 0 над ℚ, лог-часть — ответ с сертификатом"
  (let* ((P '(+ (^ x 9) 1)) (r (cantor-torsion-check P 'x cnb-D)))
    (assert-equal 'torsion (car r))
    (assert-equal 5 (nth r 1))                 ; p = 3 | disc P — не используется
    (assert-equal 9 (nth r 2))
    (assert-true (nth r 4))
    (assert-true (not (member? 3 (nth r 3))))
    (let ((lp (hyp-log-part cnb-H P 'x)))
      (assert-equal 'logs (car lp))
      (assert-equal 9 (cadr (car (caddr lp))))
      (assert-true (hyp-log-check cnb-H P 'x lp)))))

(deftest "cantor R5.3b: x^5+1, x^7+1 — кручение 5 и 7, ответ проходит hyp-log-check; q = 5 для x^5+1 не используется (плохое)"
  (let* ((P5 '(+ (^ x 5) 1)) (P7 '(+ (^ x 7) 1))
         (r5 (cantor-torsion-check P5 'x cnb-D)) (r7 (cantor-torsion-check P7 'x cnb-D)))
    (assert-equal 5 (nth r5 2))
    (assert-true (not (member? 5 (nth r5 3))))
    (assert-equal 7 (nth r7 2))
    (assert-true (not (member? 7 (nth r7 3))))
    (assert-true (hyp-log-check cnb-H P5 'x (hyp-log-part cnb-H P5 'x)))
    (assert-true (hyp-log-check cnb-H P7 'x (hyp-log-part cnb-H P7 'x)))))

(deftest "cantor R5.3b: не кручение — x^7+x+1, x^9+3x^7−2x^3+x+1, x^11+x+1: доказанный отказ"
  (let ((Ps (list '(+ (^ x 7) x 1) '(+ (^ x 9) (* 3 (^ x 7)) (* -2 (^ x 3)) x 1) '(+ (^ x 11) x 1))))
    (assert-true (every? (lambda (P) (equal? 'non-torsion (car (cantor-torsion-check P 'x cnb-D)))) Ps))
    (assert-true (every? (lambda (P) (equal? 'nonelementary (hyp-log-part cnb-H P 'x))) Ps))
    (assert-true (every? (lambda (P) (equal? 'non-torsion (hyp-torsion-order cnb-D P 'x))) Ps))))

(deftest "cantor R5.3b: подделка — настоящее кручение никогда не объявляется «не кручение» (δ, 2δ, −δ, 4δ на x^9+1, x^7+1)"
  (let ((P9 '(+ (^ x 9) 1)) (P7 '(+ (^ x 7) 1))
        (Ds (list cnb-D (cnt-div (list (list 0 1 2) (list 0 -1 -2))) (cnt-div (list (list 0 1 -1) (list 0 -1 1)))
                  (cnt-div (list (list 0 1 4) (list 0 -1 -4))))))
    (assert-true (every? (lambda (D) (equal? 'torsion (car (cantor-torsion-check P9 'x D)))) Ds))
    (assert-true (every? (lambda (D) (equal? 'torsion (car (cantor-torsion-check P7 'x D)))) Ds))))

(deftest "cantor R5.3b: порядок и таблица kδ — x^5+1: порядок 5, пары Мамфорда"
  (let* ((P '(+ (^ x 5) 1)) (r (cantor-torsion-check P 'x cnb-D)) (tb (cantor-multiples P 'x cnb-D 5)))
    (assert-equal 5 (nth r 2))
    (assert-equal '((1 ((0 0 1) (1))) (2 ((0 1) (-1))) (3 ((0 1) (1))) (4 ((0 0 1) (-1))) (5 ((1) ()))) tb)))

(deftest "cantor R5.3b: род 1 и чётная степень — Кантор не применяется (старый путь)"
  (assert-equal #f (cantor-torsion-check '(+ (^ x 3) 1) 'x cnb-D))
  (assert-equal #f (cantor-torsion-check '(+ (^ x 6) x 1) 'x cnb-D)))

; Rubi (запасная ступень integrate) здесь выключен: тест про шаги Кантора; с Rubi ответ на неэлементарную часть
; (₂F₁) зависит от того, уложится ли Rubi в бюджет, — два вызова integrate могли вернуть разное (плавающий тест)
(deftest "cantor R5.3b: шаги — Кантор в brief (порядок, q, над ℚ, таблица), английский без русских букв, ответ не меняется"
 (without-rubi (lambda ()
  (let* ((e '(/ (+ 1 (* 2 x)) (* x (^ (+ (^ x 5) 1) 1/2))))
         (cap (capture-step-log (lambda () (integrate e 'x)) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru))
         (cape (capture-step-log (lambda () (integrate e 'x)) 'brief 'en))
         (en (steps-text (cadr cape) (caddr cape) 'en)))
    (assert-true (string-contains? ru "Кантор: ord_p(δ) = 5 (p = 3); 5·δ mod q: 0 (q = 7, 11, 13); над ℚ: 5·δ = 0"))
    (assert-true (string-contains? ru "kδ — пары Мамфорда (u, v): 1δ = (x^2, 1); 2δ = (x, -1)"))
    (assert-true (string-contains? ru "5δ = O"))
    (assert-true (string-contains? en "Cantor: ord_p(δ) = 5"))
    (assert-true (string-contains? en "Mumford pairs"))
    (assert-equal (integrate e 'x) (car cap))))))

(deftest "cantor R5.3b: шаги — не кручение: причина отказа с q и ord_p"
  (let* ((e '(/ 1 (* x (^ (+ (^ x 7) x 1) 1/2))))
         (cap (capture-step-log (lambda () (integrate e 'x)) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru)))
    (assert-true (string-contains? ru "Кантор: ord_p(δ) = 17 (p = 3); 17·δ mod q: ≠ 0 (q = 5) ⇒ δ не кручение"))
    (assert-true (string-contains? ru "Неэлементарность доказана"))))

; ---------- R5.3c1: чётная степень, рациональный корень (x = a + 1/z) ----------

(define cne-P1 '(+ (^ x 6) x))                                       ; корень 0, Q = z⁵ + 1
(define cne-P2 '(+ (^ (- x 2) 6) (- x 2)))                           ; корни 1, 2 (берётся 1)
(define cne-P3 '(+ (^ x 8) x))                                       ; род 3, Q = z⁷ + 1
(define cne-P4 '(+ (^ x 6) (* 18 x)))                                ; P(2) = 100
(define (cne-inf s) (cons (cnt-pl 'inf s) (if (> s 0) 1 -1)))        ; ±∞ с кратностью ±1
(define cne-D1 (list (cne-inf 1) (cons (list -1 'ram) -1)))          ; (∞⁺) − (−1, 0): порядок 10
(define cne-D2 (list (cne-inf 1) (cons (list 1 'ram) -1)))
(define cne-D3 (list (cne-inf 1) (cne-inf -1)))                      ; ∞⁺ − ∞⁻
(define cne-D4 (list (cons (cnt-pl 2 10) 1) (cons (cnt-pl 2 -10) -1)))

; (n нуль-Кантор? вердикт L(D)) по n = 1…N
(define (cne-table P D N)
  (map (lambda (km)
         (let ((r (hyp-principal (dv-scale D (car km)) P 'x)))
           (list (car km) (equal? (cadr km) '((1) ())) (if (pair? r) (car r) r))))
       (cantor-multiples P 'x D N)))

(deftest "cantor R5.3c1: перенос мест — образ лежит на w² = Q(z), нужные точки"
  (let* ((M (integrate::cn-model cne-P1 'x cne-D1)) (C (cantor-curve (car M) 'z)))
    (assert-equal 'z (cadr M))
    (assert-equal '(0 (+ 1 (^ z 5))) (nth M 3))
    ; (∞⁺) ↦ (0, 1); (−1, 0) ↦ (z = −1, w = 0)
    (assert-equal (list (cons (list 0 1) 1) (cons (list -1 'ram) -1)) (nth M 2))
    (assert-true (cantor-valid? C (cantor-from-points C (nth M 2))))
    ; ветвление в a = 0 уходит на ∞, ∞⁻ ↦ (0, −1)
    (let ((M3 (integrate::cn-model cne-P1 'x (list (cons (list 0 'ram) 1) (cne-inf -1)))))
      (assert-equal (list (cons (list 'inf 'ram) 1) (cons (list 0 -1) -1)) (nth M3 2)))
    ; корень 1 для P2: x = 1 + 1/z, точка x = 2 ↦ z = 1 (корень 2)
    (let ((M2 (integrate::cn-model cne-P2 'x cne-D2)))
      (assert-equal 1 (car (nth M2 3)))
      (assert-equal (list (cons (list 0 1) 1) (cons (list 'inf 'ram) -1)) (nth M2 2)))
    ; нечётная степень — без замены
    (assert-equal #f (nth (integrate::cn-model '(+ (^ x 5) 1) 'x cnb-D) 3))))

(deftest "cantor R5.3c1: подделка — точка не на кривой, место не над ℚ, нет корня, род 1"
  (let ((fake (list (cons (list -1 5) 1) (cons (list -1 -5) -1))))
    ; (−1, 5) ↦ (−1, −5) не лежит на w² = z⁵ + 1
    (assert-equal #f (cantor-torsion-check cne-P1 'x fake))
    (assert-equal #f (cantor-torsion-check cne-P1 'x (list (cons (list 1 (integrate::ib-k-sqrt-rat 2)) 1)
                                                         (cons (list 1 (integrate::dv-k-neg (integrate::ib-k-sqrt-rat 2))) -1)))))
  (assert-equal #f (cantor-torsion-check '(+ (^ x 6) x 1) 'x cnb-D))
  (assert-equal #f (cantor-torsion-check '(* x (+ (^ x 3) 1)) 'x cnb-D))
  (assert-equal #f (integrate::cn-model '(+ (^ x 6) x 1) 'x cnb-D)))

(deftest "cantor R5.3c1: x⁶ + x — порядок 10 и 5, Кантор против L(D) по n = 1…10"
  (let ((r (cantor-torsion-check cne-P1 'x cne-D1)) (t1 (cne-table cne-P1 cne-D1 10))
        (r3 (cantor-torsion-check cne-P1 'x cne-D3)) (t3 (cne-table cne-P1 cne-D3 6)))
    (assert-equal 'torsion (car r))
    (assert-equal 10 (nth r 2))
    (assert-true (nth r 4))
    (assert-equal '(#f #f #f #f #f #f #f #f #f #t) (map cadr t1))
    (assert-true (cnt-agree? t1))
    (assert-equal 5 (nth r3 2))
    (assert-equal '(#f #f #f #f #t #f) (map cadr t3))
    (assert-true (cnt-agree? t3))))

(deftest "cantor R5.3c1: (x−2)⁶ + (x−2) (корень 1), x⁸ + x (род 3) — Кантор против L(D)"
  (let ((t2 (cne-table cne-P2 cne-D2 10)) (t3 (cne-table cne-P3 cne-D3 8)))
    (assert-equal 10 (nth (cantor-torsion-check cne-P2 'x cne-D2) 2))
    (assert-equal '(#f #f #f #f #f #f #f #f #f #t) (map cadr t2))
    (assert-true (cnt-agree? t2))
    (assert-equal 7 (nth (cantor-torsion-check cne-P3 'x cne-D3) 2))
    (assert-equal '(#f #f #f #f #f #f #t #f) (map cadr t3))
    (assert-true (cnt-agree? t3))))

(deftest "cantor R5.3c1: не кручение — x⁶ + 18x, δ = (2,10) − (2,−10): доказанный отказ, согласие с L(D)"
  (let ((r (cantor-torsion-check cne-P4 'x cne-D4)) (t4 (cne-table cne-P4 cne-D4 6)))
    (assert-equal 'non-torsion (car r))
    (assert-true (every? (lambda (row) (not (cadr row))) t4))
    (assert-true (cnt-agree? t4))
    (assert-equal 'non-torsion (hyp-torsion-order cne-D4 cne-P4 'x))
    (assert-equal 'nonelementary (hyp-log-part '(/ 1 (* (- x 2) y)) cne-P4 'x))))

(deftest "cantor R5.3c1: ответ integrate при чётной степени — x²/√(x⁶+x) = (1/5)·log(…), отказ для 1/((x−2)√(x⁶+18x))"
  (let ((e '(/ (^ x 2) (^ (+ (^ x 6) x) 1/2))))
    (assert-equal '(* 1/5 (log (+ 1/2 (^ x 5) (* (^ x 2) (^ (+ x (^ x 6)) 1/2))))) (integrate e 'x))
    (assert-equal 10 (car (hyp-torsion-order cne-D1 cne-P1 'x)))
    (assert-equal 'nonelementary
                  (hyp-log-part '(/ 1 (* (- x 2) y)) cne-P4 'x))))

(deftest "cantor R5.3c1: шаги — замена x = a + 1/z, Кантор, английский без русских букв"
  (let* ((e '(/ 1 (* (- x 2) (^ (+ (^ x 6) (* 18 x)) 1/2))))
         (cap (capture-step-log (lambda () (integrate e 'x)) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru))
         (cape (capture-step-log (lambda () (integrate e 'x)) 'brief 'en))
         (en (steps-text (cadr cape) (caddr cape) 'en)))
    (assert-true (string-contains? ru "замена x = 1/z: w² = Q(z) = 1 + 18z^5"))
    (assert-true (string-contains? ru "Кантор: ord_p(δ) = 25"))
    (assert-true (string-contains? ru "δ не кручение"))
    (assert-true (string-contains? en "substitution x = 1/z"))
    (assert-true (string-contains? en "birational isomorphism"))
    (assert-true (string-contains? en "Cantor: ord_p(δ) = 25"))
    (assert-true (not (any? (lambda (w) (string-contains? en w)) '("замена" "перенесены" "сохраняются" "изоморфизм" "кручение" "модели"))))))

; ---------- R5.3c2: места над K = ℚ(√d) ----------

(define (cnk-pl a d s) (list a (integrate::ib-k-scale (integrate::ib-k-sqrt-rat d) s)))
; δ = (a, √d) − (a, −√d); a = inf — две точки на ∞ (чётная степень)
(define (cnk-D a d) (list (cons (cnk-pl a d 1) 1) (cons (cnk-pl a d -1) -1)))
(define cnk-zero '(((1 0)) ()))

; (n нуль-Кантор над K? вердикт hyp-principal-ev) по n = 1…N
(define (cnk-table P D d N)
  (map (lambda (km)
         (let ((r (integrate::hyp-principal-ev (dv-scale D (car km)) P 'x d)))
           (list (car km) (equal? (cadr km) cnk-zero) (if (pair? r) (car r) r))))
       (cantor-multiples P 'x D N d)))

; редукция элемента K (a b) по 𝔭: √d ↦ s
(define (cnk-red p s c) (modulo (+ (integrate::cn-in p (car c)) (* s (integrate::cn-in p (cadr c)))) p))

(deftest "cantor R5.3c2: арифметика над K — валидность, группа, согласие с редукцией по 𝔭 (x⁵+3, K = ℚ(√3))"
  (let* ((P '(+ (^ x 5) 3)) (C (integrate::cn-curve-k P 'x 3))
         (A (cantor-from-points C (list (cons (cnk-pl 0 3 1) 1) (cons cnt-inf -1))))
         (B (cantor-from-points C (list (cons (list 1 2) 1) (cons cnt-inf -1))))
         (E (cantor-from-points C (list (cons (cnk-pl 0 3 -1) 1) (cons cnt-inf -1))))
         (D (cantor-from-points C (cnk-D 0 3))))
    (assert-true (cantor-valid? C A))
    (assert-true (cantor-valid? C D))
    (assert-equal '(((0 0) (0 0) (1 0)) ((0 1))) D)                 ; δ = 2(P − ∞): u = x², v = √3
    (assert-equal (cantor-add C (cantor-add C A B) E) (cantor-add C A (cantor-add C B E)))
    (assert-true (integrate::cn-zero-raw? (cantor-add C A (cantor-neg C A))))
    (assert-true (integrate::cn-zero-raw? (cantor-mul C 5 D)))
    (assert-true (not (integrate::cn-zero-raw? (cantor-mul C 4 D))))
    ; редукция по 𝔭 = (11, √3 − 5) — гомоморфизм: (kD) mod 𝔭 = k·(D mod 𝔭)
    (let* ((p 11) (s (sqrtmod 3 11)) (Cp (cantor-curve P 'x p))
           (red (lambda (D1) (list (map (lambda (c) (cnk-red p s c)) (car D1)) (map (lambda (c) (cnk-red p s c)) (cadr D1)))))
           (Dp (red D)))
      (assert-equal 5 s)
      (assert-true (cantor-valid? Cp Dp))
      (assert-true (every? (lambda (k) (equal? (red (cantor-mul C k D)) (cantor-mul Cp k Dp))) '(1 2 3 4 5 6 7))))))

(deftest "cantor R5.3c2: порядок и главность — x⁵+3 (порядок 5), Кантор над K против hyp-principal-ev по n = 1…6"
  (let* ((P '(+ (^ x 5) 3)) (D (cnk-D 0 3)) (t5 (cnk-table P D 3 6)) (r (cantor-torsion-check P 'x D 3)))
    (assert-equal 'torsion (car r))
    (assert-equal 5 (nth r 2))
    (assert-true (nth r 4))                                          ; m·δ = 0 над K проверено
    (assert-equal '(#f #f #f #f #t #f) (map cadr t5))
    (assert-true (cnt-agree? t5))))

(deftest "cantor R5.3c2: не кручение — x⁵+x+5 (K = ℚ(√5)) и x⁷+x+3 (ℚ(√3)): отказ доказан, согласие с L(D)"
  (let* ((P '(+ (^ x 5) x 5)) (D (cnk-D 0 5)) (t5 (cnk-table P D 5 6)) (r (cantor-torsion-check P 'x D 5))
         (P7 '(+ (^ x 7) x 3)) (r7 (cantor-torsion-check P7 'x (cnk-D 0 3) 3)))
    (assert-equal 'non-torsion (car r))
    (assert-true (every? (lambda (row) (not (cadr row))) t5))
    (assert-true (cnt-agree? t5))
    (assert-equal 'non-torsion (car r7))
    (assert-equal 'nonelementary (hyp-log-part '(/ 1 (* x y)) P7 'x))
    (assert-equal 'nonelementary (hyp-log-part '(/ 1 (* x y)) P 'x))))

(deftest "cantor R5.3c2: порядок 7 и 5 — x⁷+3 (ℚ(√3)), x⁵+5 (ℚ(√5)); логарифмическая часть = ответ с сертификатом"
  (let* ((P7 '(+ (^ x 7) 3)) (r7 (cantor-torsion-check P7 'x (cnk-D 0 3) 3))
         (P5 '(+ (^ x 5) 5)) (r5 (cantor-torsion-check P5 'x (cnk-D 0 5) 5))
         (H '(/ 1 (* x y))) (lg (hyp-log-part H P7 'x)))
    (assert-equal 7 (nth r7 2))
    (assert-equal 5 (nth r5 2))
    (assert-true (nth r7 4))
    (assert-true (nth r5 4))
    (assert-equal 'logs (car lg))
    (assert-true (hyp-log-check H P7 'x lg))
    (assert-equal 'principal (car (integrate::hyp-principal-ev (dv-scale (cnk-D 0 3) 7) P7 'x 3)))))

(deftest "cantor R5.3c2: √d ↦ s mod p — один корень на все точки, только расщеплённые p, s² ≡ d"
  (let* ((P '(+ (^ x 5) 3)) (D (cnk-D 0 3)) (r (cantor-torsion-check P 'x D 3)) (sq (nth (nth r 6) 1)))
    ; p = 3 (ветвление), 5 и 7 (инертны для ℚ(√3)) не используются; 11, 13 — расщеплены
    (assert-true (every? (lambda (pr) (= 1 (jacobi 3 (car pr)))) sq))
    (assert-true (every? (lambda (pr) (= 0 (modulo (- (* (cdr pr) (cdr pr)) 3) (car pr)))) sq))
    (assert-true (not (any? (lambda (pr) (member? (car pr) '(3 5 7))) sq)))
    (assert-equal '(#f #f #f #t) (map (lambda (p) (integrate::cn-k-split-prime? P 'x 3 p)) '(3 5 7 11)))
    ; оба корня дают согласованный (сопряжённый) образ: −s ↦ −v, порядок тот же; смешанный выбор (√d в одной точке, −√d в другой)
    ; дал бы δ ↦ P − P = 0, порядок 1 — поэтому s одно на все точки
    (let* ((C (cantor-curve P 'x)) (p 11) (s (sqrtmod 3 11))
           (r1 (integrate::cn-k-reduce C D p 3 s)) (r2 (integrate::cn-k-reduce C D p 3 (- p s)))
           (Cp (car r1)) (mixed (cantor-from-points Cp (list (cons (list 0 s) 1) (cons (list 0 s) -1)))))
      (assert-equal 5 (cantor-order-upto Cp (cdr r1) 20))
      (assert-equal 5 (cantor-order-upto Cp (cdr r2) 20))
      (assert-equal (cantor-neg Cp (cdr r1)) (cdr r2))
      (assert-equal 1 (cantor-order-upto Cp mixed 5)))))

(deftest "cantor R5.3c2: подделки — точка не на кривой, место над другим ℚ(√d′), g = 1, нужный K не тот"
  (let ((P '(+ (^ x 5) 3)) (C (integrate::cn-curve-k '(+ (^ x 5) 3) 'x 3)))
    ; (0, √5) не лежит на y² = x⁵ + 3
    (assert-error (cantor-from-points C (cnk-D 0 5)))
    (assert-equal #f (cantor-torsion-check P 'x (cnk-D 0 5) 3))
    ; дивизор над ℚ(√5), а d = 3 — не ℚ(√3); и наоборот
    (assert-equal #f (cantor-torsion-check '(+ (^ x 5) 5) 'x (cnk-D 0 5) 3))
    (assert-equal #f (cantor-torsion-check '(+ (^ x 5) 3) 'x (cnk-D 0 3) 5))
    ; род 1 — Кантор не применяется
    (assert-equal #f (cantor-torsion-check '(+ (^ x 3) 3) 'x (cnk-D 0 3) 3))
    ; абсцисса вне ℚ
    (assert-equal #f (cantor-torsion-check P 'x (list (cons (list (integrate::ib-k-sqrt-rat 2) (cadr (cnk-pl 0 3 1))) 1)
                                                      (cons (list (integrate::ib-k-sqrt-rat 2) (cadr (cnk-pl 0 3 -1))) -1)) 3))
    ; мусор вместо места — тоже #f, не ошибка
    (assert-equal #f (cantor-torsion-check P 'x (list (cons (list 0 (list 0 1)) 1) (cons (list 0 7) -1)) 3))))

(deftest "cantor R5.3c2: граница B — порядок спуском от B; B·δ ≠ 0 по модулю 𝔭 ⇒ не кручение"
  (let* ((P7 '(+ (^ x 7) 3)) (D7 (cnk-D 0 3)) (Pn '(+ (^ x 7) x 3)) (Dn (cnk-D 0 3))
         (ra (cantor-torsion-check P7 'x D7 3 (* 7 13 17)))
         (rb (cantor-torsion-check Pn 'x Dn 3 (* 7 13 17)))
         (rc (cantor-torsion-check Pn 'x Dn 3 1)))
    (assert-equal 'torsion (car ra))
    (assert-equal 7 (nth ra 2))
    ; (границу B подставляет вызывающий: порядок кручения делит B; ord_𝔭(δ) = 12 ∤ 1547 ⇒ B·δ ≠ 0 ⇒ δ не кручение)
    (assert-equal '(non-torsion bound) (list (car rb) (nth rb 4)))
    (assert-equal 'non-torsion (car rc))))

(deftest "cantor R5.3c2: чётная степень над K — 3x⁶+x (∞±, порядок 5), x⁶+3x в (2, ±√70) не кручение"
  (let* ((P1 '(+ (* 3 (^ x 6)) x)) (D1 (cnk-D 'inf 3)) (r1 (cantor-torsion-check P1 'x D1 3))
         (P2 '(+ (^ x 6) (* 3 x))) (r2 (cantor-torsion-check P2 'x (cnk-D 2 70) 70)))
    (assert-equal 'torsion (car r1))
    (assert-equal 5 (nth r1 2))
    (assert-equal '(0 (+ 3 (^ z 5))) (nth r1 5))
    (assert-true (nth r1 4))
    (assert-equal 'non-torsion (car r2))
    ; ∞± — положительная кратность на ∞: hyp-principal-ev (z-модель с √d) не умеет — расхождение записывается условием
    (assert-equal 'unknown (integrate::hyp-principal-ev (dv-scale D1 5) P1 'x 3))
    (let ((res (integrate::dv-cantor-order-ev (dv-normalize D1) P1 'x 3)))
      (assert-equal 'unknown res))))

(deftest "cantor R5.3c2: x¹⁵ − 2x⁹ + x⁴ + 3, δ = 2(P − ∞) над ℚ(√3): ни у одного из p порядок не ≤ 60 (g = 7)"
  (let* ((P '(+ (^ x 15) (* -2 (^ x 9)) (^ x 4) 3)) (r (cantor-torsion-check P 'x (cnk-D 0 3) 3)))
    (assert-equal 'order-large (car r))
    (assert-equal 60 (nth r 2))
    (assert-true (every? (lambda (p) (= 1 (jacobi 3 p))) (nth r 3)))))

(deftest "cantor R5.3c2: шаги — Кантор над ℚ(√3): порядок, q, таблица kδ; английский без русских букв"
  (let* ((P '(+ (^ x 5) 3)) (H '(/ 1 (* x y)))
         (cap (capture-step-log (lambda () (integrate::alg-run (lambda () (hyp-log-part H P 'x)))) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru))
         (cape (capture-step-log (lambda () (integrate::alg-run (lambda () (hyp-log-part H P 'x)))) 'brief 'en))
         (en (steps-text (cadr cape) (caddr cape) 'en)))
    (assert-equal 'logs (car (car cap)))
    (assert-true (string-contains? ru "Кантор над ℚ(√3): ord_𝔭(δ) = 5 (p = 11, √3 ≡ 5 mod 11); 5·δ mod 𝔮: 0 (q = 13, √3 ≡ 4 mod 13"))
    (assert-true (string-contains? ru "над K: 5·δ = 0 ⇒ порядок δ равен 5"))
    (assert-true (string-contains? ru "1δ = (x^2, 3^(1/2)); 2δ = (x, -3^(1/2))"))
    (assert-true (string-contains? ru "5δ = O"))
    (assert-true (string-contains? en "Cantor over ℚ(√3): ord_𝔭(δ) = 5"))
    (assert-true (string-contains? en "over K: 5·δ = 0"))
    (assert-true (string-contains? en "Mumford pairs"))
    (assert-true (not (any? (lambda (w) (string-contains? en w)) '("Кантор" "расщепляется" "кручение" "над K"))))))

(deftest "cantor R5.3c2: шаги — не кручение над K, отказ с q; ответ integrate не меняется"
  (let* ((e '(/ 1 (* x (^ (+ (^ x 7) x 3) 1/2))))
         (cap (capture-step-log (lambda () (integrate e 'x)) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru))
         (cape (capture-step-log (lambda () (integrate e 'x)) 'brief 'en))
         (en (steps-text (cadr cape) (caddr cape) 'en)))
    (assert-true (string-contains? ru "Кантор над ℚ(√3): ord_𝔭(δ) = 12 (p = 11, √3 ≡ 5 mod 11); 12·δ mod 𝔮: ≠ 0 (q = 13, √3 ≡ 4 mod 13) ⇒ δ не кручение"))
    (assert-true (string-contains? ru "Неэлементарность доказана"))
    (assert-true (string-contains? en "Cantor over ℚ(√3)"))
    (assert-true (string-contains? en "is not torsion"))
    (assert-equal (integrate e 'x) (car cap))))
