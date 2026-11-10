; specfun.lisp — специальные функции: Γ, B, ψ, гипергеометрические ₚFq, hyperexpand, тождества с условиями (шаг SFn.1)
; Γ: (sf-gamma z) — точные значения (целые, полуцелые), полюсы → (complex-infinity); (specfun-simplify e) — рекуррентность
; Γ(z+1) = zΓ(z) (класс z+k сводится к наименьшему сдвигу), отражение Γ(z)Γ(1−z) = π/sin πz (z ∉ ℤ — условие),
; B(a,b) = Γ(a)Γ(b)/Γ(a+b), ψ (digamma) со сдвигом; удвоение Лежандра: specfun-duplication / -collapse.
; ₚFq: (hyper (a…) (b…) z); hyper-term/-series (точные), hyper-reduce (сокращение a = b, a = 0, обрыв при a = −n),
; hyperexpand (таблица ₀F₀, ₁F₀, ₀F₁, ₁F₁, ₂F₁ + Чу—Вандермонд при z = 1 + Гаусс при Re(c−a−b) > 0), hyper-diff.
; Сертификат: (specfun-check lhs rhs vars) — #t (точно), numeric (3 рациональные точки; ряд с доказанной оценкой хвоста
; при |z| < 1 / p ≤ q), #f (опровергнуто), unknown; specfun-check-numeric — только числа, без разложения.
; Внутренние имена: sf-.
(module specfun
  (export sf-gamma sf-beta sf-digamma specfun-simplify specfun-duplication specfun-duplication-collapse
          hyper-term hyper-series hyper-reduce hyperexpand hyper-diff hyper-eval
          bessel-j bessel-y bessel-i bessel-k airy-ai airy-bi airy-ai-prime airy-bi-prime
          legendre-p legendre-q
          hypergeometric-2f1 appell-f1 hypergeometric-2f1-num appell-f1-num
          specfun-check specfun-check-numeric))

; ---------- общее ----------

(define (sf-head? e h) (and (pair? e) (equal? (car e) h)))
(define (sf-rat? x) (or (integer? x) (equal? (type-of x) 'rational)))
(define (sf-pole? q) (and (integer? q) (<= q 0)))
(define (sf-list e) (if (or (null? e) (equal? e 'nil)) '() e))
(define (sf-sum l) (cond ((null? l) 0) ((null? (cdr l)) (car l)) (else (simplify (cons '+ l)))))
(define (sf-mul l) (cond ((null? l) 1) ((null? (cdr l)) (simplify (car l))) (else (simplify (cons '* l)))))
(define (sf-neg e) (simplify (list '* -1 e)))
(define (sf-add a b) (simplify (list '+ a b)))
(define (sf-inv e) (simplify (list '^ e -1)))
(define (sf-frac q) (- q (floor q)))
(define (sf-fact n) (let loop ((i 2) (acc 1)) (if (> i n) acc (loop (+ i 1) (* acc i)))))
(define (sf-harm n) (let loop ((i 1) (s 0)) (if (> i n) s (loop (+ i 1) (+ s (/ 1 i))))))
(define (sf-sqrtpi) (simplify '(^ pi 1/2)))
(define (sf-nth e i) (nth e i))

; ---------- Γ: точные значения ----------

; целое n ≥ 1 → (n−1)!; n ≤ 0 → 'pole; полуцелое → r·√π; иначе #f
(define (sf-gamma-const q)
  (cond ((integer? q) (if (>= q 1) (sf-fact (- q 1)) 'pole))
        ((and (sf-rat? q) (= (denom q) 2) (< (abs q) 2000))
         (let ((n (- q 1/2)))
           (if (>= n 0)
               (simplify (list '* (/ (sf-fact (* 2 n)) (* (^ 4 n) (sf-fact n))) (sf-sqrtpi)))
               (let ((m (- 0 n)))
                 (simplify (list '* (/ (* (^ -4 m) (sf-fact m)) (sf-fact (* 2 m))) (sf-sqrtpi)))))))
        (else #f)))

; ---------- Γ: произведения (рекуррентность, отражение, удвоение) ----------

; фактор → (основание . целая степень)
(define (sf-pe f) (if (and (sf-head? f '^) (integer? (caddr f))) (cons (cadr f) (caddr f)) (cons f 1)))
(define (sf-pe-expr p) (if (= (cdr p) 1) (car p) (list '^ (car p) (cdr p))))
(define (sf-gam? p) (sf-head? (car p) 'gamma))

; атомы: точные Γ(рационального) → (extra . G) | 'pole | 'zero; G — список (аргумент . степень)
(define (sf-atoms gs)
  (let loop ((l gs) (extra '()) (G '()))
    (if (null? l)
        (cons extra (reverse G))
        (let* ((g (car (car l))) (e (cdr (car l))) (a (cadr g)))
          (if (sf-rat? a)
              (let ((v (sf-gamma-const a)))
                (cond ((equal? v 'pole) (if (> e 0) 'pole 'zero))
                      (v (loop (cdr l) (cons (list '^ v e) extra) G))
                      (else (loop (cdr l) extra (cons (cons a e) G)))))
              (loop (cdr l) extra (cons (cons a e) G)))))))

; пара (i j token) с совпадением mt по аргументам одного знака степени, либо #f
(define (sf-find-pair G mt)
  (let ((n (length G)))
    (let loop ((i 0))
      (if (>= i n)
          #f
          (let inner ((j (+ i 1)))
            (if (>= j n)
                (loop (+ i 1))
                (let ((gi (nth G i)) (gj (nth G j)))
                  (let ((tk (if (> (* (cdr gi) (cdr gj)) 0) (mt (car gi) (car gj)) #f)))
                    (if tk (list i j tk) (inner (+ j 1)))))))))))

(define (sf-drop2 G i j)
  (let loop ((l G) (k 0) (acc '()))
    (cond ((null? l) (reverse acc))
          ((or (= k i) (= k j)) (loop (cdr l) (+ k 1) acc))
          (else (loop (cdr l) (+ k 1) (cons (car l) acc))))))

; mk: (token m) → (множитель . новая запись G или #f); → (G' . extra')
(define (sf-apply-pairs G mt mk extra)
  (let ((hit (sf-find-pair G mt)))
    (if (not hit)
        (cons G extra)
        (let* ((gi (nth G (car hit))) (gj (nth G (cadr hit)))
               (ei (cdr gi)) (ej (cdr gj))
               (m (if (> ei 0) (min ei ej) (- 0 (min (- 0 ei) (- 0 ej)))))
               (r (mk (caddr hit) m))
               (rest (sf-drop2 G (car hit) (cadr hit)))
               (left (filter (lambda (p) (not (= (cdr p) 0)))
                             (list (cons (car gi) (- ei m)) (cons (car gj) (- ej m)))))
               (newg (if (cdr r) (list (cdr r)) '())))
          (sf-apply-pairs (append rest left newg) mt mk (cons (car r) extra))))))

; π/sin(πa); условие z ∉ ℤ для нерационального a
(define (sf-refl a)
  (begin
    (if (not (sf-rat? a))
        (record-condition (list '/= (list 'sin (list '* 'pi a)) 0) "Γ(z)Γ(1−z) = π/sin πz: z не целое"))
    (simplify (list '* 'pi (list '^ (list 'sin (list '* 'pi a)) -1)))))

; пара с a + b = целое m: Γ(a)Γ(b) = π/sin(πa) · (1−a)_{m−1}  (при m − 1 < 0 — деление на (1−a−j))
(define (sf-refl-mt a b)
  (let ((s (sf-add a b))) (if (integer? s) (cons a s) #f)))
(define (sf-refl-mk tk m)
  (let ((a (car tk)) (mm (cdr tk)))
    (cons (list '^ (simplify (list '* (sf-refl a) (sf-shift-mult (sf-add 1 (sf-neg a)) 0 (- mm 1)))) m) #f)))

; Γ(a)Γ(a+1/2) = 2^{1−2a}√π Γ(2a)
(define (sf-dup-mt a b)
  (cond ((equal? (sf-add b (sf-neg a)) 1/2) a)
        ((equal? (sf-add a (sf-neg b)) 1/2) b)
        (else #f)))
(define (sf-dup-mk a m)
  (cons (list '^ (simplify (list '* (list '^ 2 (list '+ 1 (list '* -2 a))) (sf-sqrtpi))) m)
        (cons (simplify (list '* 2 a)) m)))

; аргумент → (основание . рациональная часть)
(define (sf-split a)
  (cond ((sf-rat? a) (cons 0 a))
        ((sf-head? a '+)
         (cons (sf-sum (filter (lambda (t) (not (sf-rat? t))) (cdr a)))
               (sf-sum (filter sf-rat? (cdr a)))))
        (else (cons a 0))))

(define (sf-classes items)
  (foldl (lambda (acc it)
           (let* ((key (list (car it) (sf-frac (cadr it)))) (hit (assoc key acc)))
             (if hit
                 (map (lambda (c) (if (equal? (car c) key) (cons key (append (cdr c) (list it))) c)) acc)
                 (append acc (list (cons key (list it)))))))
         '() items))

; Γ(base+kmin+d) = [(base+kmin)_d]·Γ(base+kmin)
(define (sf-shift-mult base kmin d)
  (cond ((= d 0) 1)
        ((> d 0) (sf-mul (map (lambda (j) (sf-add base (+ kmin j))) (range d))))
        (else (sf-inv (sf-mul (map (lambda (j) (sf-add base (- kmin (+ j 1)))) (range (- 0 d))))))))

; класс → (запись G | #f . список множителей)
(define (sf-class-shift c)
  (let* ((key (car c)) (base (car key)) (its (cdr c))
         (ks (map cadr its))
         (kmin (if (equal? base 0) (cadr key) (foldl min (car ks) ks)))
         (etot (foldl + 0 (map caddr its)))
         (extras (map (lambda (it) (list '^ (sf-shift-mult base kmin (- (cadr it) kmin)) (caddr it))) its)))
    (cons (if (= etot 0) #f (cons (sf-add base kmin) etot)) extras)))

; G → (G' . extra): все Γ(z+k) одного класса сводятся к Γ(z+kmin); константы — к Γ(дробной части)
(define (sf-canon G)
  (let* ((items (map (lambda (p) (let ((s (sf-split (car p)))) (list (car s) (cdr s) (cdr p)))) G))
         (rs (map sf-class-shift (sf-classes items))))
    (cons (filter (lambda (x) x) (map car rs)) (append-map cdr rs))))

(define (sf-flatten fs) (append-map (lambda (f) (if (sf-head? f '*) (cdr f) (list f))) fs))

; произведение упрощённых множителей
(define (sf-prod-simplify fs0)
  (let* ((fs (sf-flatten fs0))
         (parts (map sf-pe fs))
         (gs (filter sf-gam? parts))
         (others (filter (lambda (p) (not (sf-gam? p))) parts)))
    (if (null? gs)
        (sf-mul fs)
        (let ((at (sf-atoms gs)))
          (cond ((equal? at 'pole) '(complex-infinity))
                ((equal? at 'zero) 0)
                (else
                 (let* ((r1 (sf-apply-pairs (cdr at) sf-refl-mt sf-refl-mk '()))
                        (r2 (sf-canon (car r1)))
                        (r3 (sf-apply-pairs (car r2) sf-refl-mt sf-refl-mk '())))
                   (sf-mul (append (map sf-pe-expr others) (car at) (cdr r1) (cdr r2) (cdr r3)
                                   (map (lambda (p) (list '^ (list 'gamma (car p)) (cdr p))) (car r3)))))))))))

; сборка пар Γ(z)Γ(z+1/2) → Γ(2z) в произведении
(define (sf-prod-collapse fs0)
  (let* ((fs (sf-flatten fs0))
         (parts (map sf-pe fs))
         (gs (filter sf-gam? parts))
         (others (filter (lambda (p) (not (sf-gam? p))) parts)))
    (if (null? gs)
        (sf-mul fs)
        (let ((r (sf-apply-pairs (map (lambda (p) (cons (cadr (car p)) (cdr p))) gs) sf-dup-mt sf-dup-mk '())))
          (sf-mul (append (map sf-pe-expr others) (cdr r)
                          (map (lambda (p) (list '^ (list 'gamma (car p)) (cdr p))) (car r))))))))

; ---------- ψ ----------

; целое n ≥ 1 → −γ + H_{n−1}; полуцелое → −γ − 2 ln 2 + …; полюс → 'pole; иначе #f
(define (sf-digamma-const q)
  (cond ((integer? q)
         (if (>= q 1) (simplify (list '+ (list '* -1 'euler-gamma) (sf-harm (- q 1)))) 'pole))
        ((and (sf-rat? q) (= (denom q) 2) (< (abs q) 2000))
         (let ((n (- q 1/2)) (base '(+ (* -1 euler-gamma) (* -2 (log 2)))))
           (if (>= n 0)
               (simplify (list '+ base (* 2 (foldl + 0 (map (lambda (k) (/ 1 (- (* 2 (+ k 1)) 1))) (range n))))))
               (simplify (list '+ base
                               (- 0 (foldl + 0 (map (lambda (j) (/ 1 (- 1/2 (+ j 1)))) (range (- 0 n))))))))))
        (else #f)))

; (sf-digamma z): точное значение или ψ(w) + сдвиг на целое
(define (sf-digamma z)
  (let ((v (if (sf-rat? z) (sf-digamma-const z) #f)))
    (cond ((equal? v 'pole) '(complex-infinity))
          (v v)
          (else
           (let* ((s (sf-split z)) (k (cdr s)) (n (floor k)) (w (sf-add (car s) (- k n))))
             (cond ((= n 0) (list 'psi z))
                   ((> n 0) (sf-add (list 'psi w) (sf-sum (map (lambda (j) (sf-inv (sf-add w j))) (range n)))))
                   (else (sf-add (list 'psi w)
                                 (sf-neg (sf-sum (map (lambda (j) (sf-inv (sf-add w (- 0 (+ j 1))))) (range (- 0 n)))))))))))))

; ---------- B ----------

(define (sf-beta a b)
  (cond ((or (sf-pole? a) (sf-pole? b)) '(complex-infinity))
        ((and (sf-rat? a) (sf-rat? b) (sf-pole? (+ a b))) 0)
        ((or (and (sf-rat? a) (sf-rat? b))
             (and (integer? a) (> a 0)) (and (integer? b) (> b 0)))
         (sf-prod-simplify (list (list 'gamma a) (list 'gamma b) (list '^ (list 'gamma (sf-add a b)) -1))))
        (else (list 'beta a b))))

; ---------- общий упроститель ----------

(define (sf-simp e)
  (cond ((not (pair? e)) e)
        ((sf-head? e 'hyper)
         (hyper-reduce (list 'hyper (map sf-simp (sf-list (nth e 1))) (map sf-simp (sf-list (nth e 2))) (sf-simp (nth e 3)))))
        ((equal? (car e) '*) (sf-prod-simplify (map sf-simp (cdr e))))
        ((equal? (car e) 'gamma) (sf-prod-simplify (list (list 'gamma (sf-simp (cadr e))))))
        ((equal? (car e) '^)
         (let ((b (sf-simp (cadr e))) (x (sf-simp (caddr e))))
           (cond ((and (integer? x) (sf-head? b 'gamma)) (sf-prod-simplify (list (list '^ b x))))
                 ((and (integer? x) (sf-head? b 'complex-infinity)) (if (< x 0) 0 b))
                 (else (simplify (list '^ b x))))))
        ((equal? (car e) 'beta) (sf-beta (sf-simp (cadr e)) (sf-simp (caddr e))))
        ((or (equal? (car e) 'psi) (equal? (car e) 'digamma)) (sf-digamma (sf-simp (cadr e))))
        (else (simplify (cons (car e) (map sf-simp (cdr e)))))))

(define (specfun-simplify e) (sf-simp (simplify e)))

; (sf-gamma z) — Γ(z): точное значение, полюс → (complex-infinity), иначе упрощённая форма
(define (sf-gamma z) (specfun-simplify (list 'gamma z)))

; Γ(2z) → 2^{2z−1}/√π · Γ(z)Γ(z+1/2) во всём выражении (условие: 2z не полюс Γ)
(define (specfun-duplication e)
  (cond ((not (pair? e)) e)
        ((and (sf-head? e 'gamma) (sf-head? (cadr e) '*) (equal? (cadr (cadr e)) 2) (= (length (cadr e)) 3))
         (let ((z (caddr (cadr e))))
           (begin
             (record-condition (list 'not-gamma-pole (cadr e)) "удвоение Лежандра: 2z не целое ≤ 0")
             (simplify (list '* (list '^ 2 (list '+ -1 (list '* 2 z))) (list '^ (sf-sqrtpi) -1)
                             (list 'gamma z) (list 'gamma (list '+ z 1/2)))))))
        (else (simplify (cons (car e) (map specfun-duplication (cdr e)))))))

; Γ(z)Γ(z+1/2) → 2^{1−2z}√π Γ(2z) во всех произведениях
(define (specfun-duplication-collapse e)
  (let ((s (simplify e)))
    (cond ((not (pair? s)) s)
          ((equal? (car s) '*) (sf-prod-collapse (map specfun-duplication-collapse (cdr s))))
          (else (simplify (cons (car s) (map specfun-duplication-collapse (cdr s))))))))

; ---------- ₚFq: точные члены и редукции ----------

(define (sf-hyper? e) (and (sf-head? e 'hyper) (= (length e) 4)))
(define (sf-A h) (sf-list (nth h 1)))
(define (sf-B h) (sf-list (nth h 2)))
(define (sf-Z h) (nth h 3))
(define (sf-mk A B z) (list 'hyper A B z))

; коэффициент c_{k+1} из c_k: c_k·∏(a+k)/(∏(b+k)·(k+1))
(define (sf-next-coef h c k)
  (simplify (list '* c (sf-mul (map (lambda (a) (sf-add a k)) (sf-A h)))
                  (sf-inv (sf-mul (map (lambda (b) (sf-add b k)) (sf-B h))))
                  (/ 1 (+ k 1)))))

; k-й член ряда (точный)
(define (hyper-term h k)
  (let loop ((i 0) (c 1))
    (if (= i k)
        (simplify (list '* c (list '^ (sf-Z h) k)))
        (loop (+ i 1) (sf-next-coef h c i)))))

; сумма членов k = 0..n
(define (hyper-series h n)
  (let loop ((k 0) (c 1) (acc '()))
    (let ((acc2 (cons (simplify (list '* c (list '^ (sf-Z h) k))) acc)))
      (if (>= k n)
          (sf-sum (reverse acc2))
          (loop (+ k 1) (sf-next-coef h c k) acc2)))))

(define (sf-remove-one x l)
  (cond ((null? l) '())
        ((equal? x (car l)) (cdr l))
        (else (cons (car l) (sf-remove-one x (cdr l))))))

; сокращение a = b (кроме целых ≤ 0) → (A' . B')
(define (sf-cancel A B)
  (let loop ((l A) (A2 '()) (B2 B))
    (cond ((null? l) (cons (reverse A2) B2))
          ((and (not (sf-pole? (car l))) (member? (car l) B2))
           (loop (cdr l) A2 (sf-remove-one (car l) B2)))
          (else (loop (cdr l) (cons (car l) A2) B2)))))

; сокращения: z = 0 → 1; a = b сокращаются; a = 0 → 1; a = −n → многочлен степени n
(define (hyper-reduce h)
  (if (not (sf-hyper? h))
      h
      (let* ((z (sf-Z h)) (c (sf-cancel (sf-A h) (sf-B h))) (A (car c)) (B (cdr c))
             (negs (filter sf-pole? A)))
        (cond ((and (sf-rat? z) (= z 0)) 1)
              ((member? 0 A) 1)
              ((not (null? negs))
               (let ((n (- 0 (foldl max (car negs) negs))))
                 (if (any? (lambda (b) (and (sf-pole? b) (<= (- 0 b) n))) B)
                     (begin (record-condition (list 'hyper-undefined (sf-mk A B z)) "параметр b — целое ≤ 0 не позже обрыва ряда")
                            (sf-mk A B z))
                     (hyper-series (sf-mk A B z) n))))
              ((any? sf-pole? B)
               (begin (record-condition (list 'hyper-undefined (sf-mk A B z)) "параметр b — целое ≤ 0: ряд не определён")
                      (sf-mk A B z)))
              (else (sf-mk A B z))))))

; d/dz ₚFq(a;b;z) = (∏a/∏b) ₚFq(a+1;b+1;z)
(define (hyper-diff h)
  (simplify (list '* (sf-mul (sf-A h)) (sf-inv (sf-mul (sf-B h)))
                  (sf-mk (map (lambda (a) (sf-add a 1)) (sf-A h)) (map (lambda (b) (sf-add b 1)) (sf-B h)) (sf-Z h)))))

; ---------- hyperexpand ----------

; структурный корень: u² = w → u | #f
(define (sf-sqrt-exact w)
  (cond ((sf-rat? w)
         (if (< w 0) #f (let ((r (simplify (list '^ w 1/2)))) (if (sf-rat? r) r #f))))
        ((and (sf-head? w '^) (integer? (caddr w)) (= (modulo (caddr w) 2) 0))
         (let ((k (quotient (caddr w) 2))) (if (= k 1) (cadr w) (simplify (list '^ (cadr w) k)))))
        ((sf-head? w '*)
         (let ((us (map sf-sqrt-exact (cdr w))))
           (if (every? (lambda (u) u) us) (sf-mul us) #f)))
        (else #f)))

; w = u² → (pos . u); w = −u² → (neg . u); иначе (gen . √w)
(define (sf-even w)
  (let ((u1 (sf-sqrt-exact w)))
    (if u1
        (cons 'pos u1)
        (let ((u2 (sf-sqrt-exact (sf-neg w))))
          (if u2 (cons 'neg u2) (cons 'gen (simplify (list '^ w 1/2))))))))

(define (sf-over f u) (simplify (list '* (list f u) (sf-inv u))))
(define (sf-sorted l) (sort l <))
(define (sf-same? l target) (and (every? sf-rat? l) (equal? (sf-sorted l) target)))

; таблица стандартных случаев → выражение | #f
(define (sf-hx-table h)
  (let* ((A (sf-A h)) (B (sf-B h)) (w (sf-Z h)) (p (length A)) (q (length B)))
    (cond
      ((and (= p 0) (= q 0)) (simplify (list 'exp w)))
      ((and (= p 1) (= q 0)) (simplify (list '^ (sf-add 1 (sf-neg w)) (sf-neg (car A)))))
      ((and (= p 0) (= q 1) (equal? (car B) 1/2))
       (let ((ev (sf-even (simplify (list '* 4 w)))))
         (cond ((equal? (car ev) 'neg) (simplify (list 'cos (cdr ev))))
               (else (simplify (list 'cosh (cdr ev)))))))
      ((and (= p 0) (= q 1) (equal? (car B) 3/2))
       (let ((ev (sf-even (simplify (list '* 4 w)))))
         (cond ((equal? (car ev) 'neg) (sf-over 'sin (cdr ev)))
               (else (sf-over 'sinh (cdr ev))))))
      ((and (= p 1) (= q 1) (equal? A '(1)) (equal? B '(2)))
       (simplify (list '* (list '+ (list 'exp w) -1) (sf-inv w))))
      ((and (= p 1) (= q 1) (equal? A '(1/2)) (equal? B '(3/2)))
       (let* ((ev (sf-even w)) (u (cdr ev)))
         (simplify (list '* (sf-sqrtpi) 1/2 (list (if (equal? (car ev) 'neg) 'erf 'erfi) u) (sf-inv u)))))
      ((and (= p 2) (= q 1) (sf-same? A '(1 1)) (equal? B '(2)))
       (simplify (list '* -1 (list 'log (sf-add 1 (sf-neg w))) (sf-inv w))))
      ((and (= p 2) (= q 1) (sf-same? A '(1/2 1)) (equal? B '(3/2)))
       (let ((ev (sf-even w)))
         (sf-over (if (equal? (car ev) 'neg) 'atan 'atanh) (cdr ev))))
      ((and (= p 2) (= q 1) (sf-same? A '(1/2 1/2)) (equal? B '(3/2)))
       (let ((ev (sf-even w)))
         (sf-over (if (equal? (car ev) 'neg) 'asinh 'asin) (cdr ev))))
      ((and (= p 2) (= q 1) (sf-same? A '(1 1)) (equal? B '(3/2)))
       (let* ((ev (sf-even w)) (u (cdr ev)))
         (simplify (list '* (list (if (equal? (car ev) 'neg) 'asinh 'asin) u) (sf-inv u)
                         (list '^ (sf-add 1 (sf-neg w)) -1/2)))))
      ((and (= p 2) (= q 1) (equal? (car B) 1/2) (sf-half-pair A))
       (let ((a (sf-half-pair A)) (ev (sf-even w)))
         (if (equal? (car ev) 'neg)
             #f
             (let ((u (cdr ev)) (e (sf-neg (simplify (list '* 2 a)))))
               (simplify (list '* 1/2 (list '+ (list '^ (sf-add 1 u) e) (list '^ (sf-add 1 (sf-neg u)) e))))))))
      ((and (= p 2) (= q 1) (equal? (car B) 3/2) (sf-half-pair A)
            (not (equal? (sf-half-pair A) 1/2)))
       (let ((a (sf-half-pair A)) (ev (sf-even w)))
         (if (equal? (car ev) 'neg)
             #f
             (let* ((u (cdr ev)) (e (sf-add 1 (sf-neg (simplify (list '* 2 a))))))
               (simplify (list '* (list '+ (list '^ (sf-add 1 u) e) (list '* -1 (list '^ (sf-add 1 (sf-neg u)) e)))
                               (sf-inv (simplify (list '* 2 u e)))))))))
      ; SFn.2b: ₀F₁(;2/3;x³/9) и ₀F₁(;4/3;x³/9) — комбинации Ai, Bi (u = кубический корень из 9w)
      ((and (= p 0) (= q 1) (equal? (car B) 2/3))
       (let ((u (sf-cube (simplify (list '* 9 w)))))
         (and u
              (simplify (list '* (sf-gamma 2/3) (list '^ 3 2/3) 1/2
                              (list '+ (list 'airy-ai u)
                                    (list '* (list '^ 3 -1/2) (list 'airy-bi u))))))))
      ((and (= p 0) (= q 1) (equal? (car B) 4/3))
       (let ((u (sf-cube (simplify (list '* 9 w)))))
         (and u (not (equal? (simplify u) 0))
              (simplify (list '* (sf-gamma 1/3) (list '^ 3 1/3) 1/2 (list '^ u -1)
                              (list '- (list '* (list '^ 3 -1/2) (list 'airy-bi u))
                                    (list 'airy-ai u)))))))
      ; SFn.2b: ₀F₁(;b; ±u²/4) = Γ(b)(u/2)^{1−b}·J_{b−1}(u) / I_{b−1}(u)
      ((and (= p 0) (= q 1) (sf-rat? (car B)) (not (sf-pole? (car B))))
       (let* ((b (car B)) (ev (sf-even (simplify (list '* 4 w)))))
         (and (not (equal? (car ev) 'gen))
              (let* ((u (cdr ev))
                     (nu (sf-add b -1))
                     (pref (simplify (list '* (sf-gamma b)
                                           (list '^ (list '* 1/2 u) (sf-add 1 (sf-neg b)))))))
                (simplify (list '* pref
                                (list (if (equal? (car ev) 'neg) 'bessel-j 'bessel-i) nu u)))))))
      (else #f))))

; структурный куб: w = u³ → u | #f
(define (sf-cube w)
  (and (pair? w) (equal? (car w) '^) (= (length w) 3) (equal? (caddr w) 3)
       (cadr w)))

; SFn.2b: ₂F₁(−n, n+1; 1; z) = P_n(1 − 2z)
(define (sf-legendre-hyper h)
  (and (= (length (sf-A h)) 2) (= (length (sf-B h)) 1)
       (equal? (car (sf-B h)) 1)
       (let* ((A (sf-A h)) (a1 (car A)) (a2 (cadr A))
              (n (cond ((and (sf-pole? a1) (equal? a2 (sf-add 1 (sf-neg a1)))) (sf-neg a1))
                       ((and (sf-pole? a2) (equal? a1 (sf-add 1 (sf-neg a2)))) (sf-neg a2))
                       (else #f))))
         (and n (<= n 60)
              (legendre-p n (simplify (list '- 1 (list '* 2 (sf-Z h)))))))))

; A = (a, a+1/2) (в любом порядке) → a; иначе #f
(define (sf-half-pair A)
  (and (= (length A) 2)
       (let ((d (sf-add (cadr A) (sf-neg (car A)))))
         (cond ((equal? d 1/2) (car A))
               ((equal? d -1/2) (cadr A))
               (else #f)))))

; Чу—Вандермонд: ₂F₁(−n, b; c; 1) = (c−b)_n/(c)_n
(define (sf-chu h)
  (and (= (length (sf-A h)) 2) (= (length (sf-B h)) 1) (equal? (sf-Z h) 1)
       (let* ((A (sf-A h)) (c (car (sf-B h)))
              (negs (filter (lambda (a) (and (sf-pole? a) (< a 0))) A)))
         (and (not (null? negs)) (not (sf-pole? c))
              (let* ((a1 (car negs)) (n (- 0 a1))
                     (b (if (equal? a1 (car A)) (cadr A) (car A))))
                (and (<= n 500)
                     (simplify (list '* (sf-mul (map (lambda (j) (sf-add (sf-add c (sf-neg b)) j)) (range n)))
                                     (sf-inv (sf-mul (map (lambda (j) (sf-add c j)) (range n))))))))))))

; Гаусс: ₂F₁(a,b;c;1) = Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b)), условие Re(c−a−b) > 0
(define (sf-gauss h)
  (and (= (length (sf-A h)) 2) (= (length (sf-B h)) 1) (equal? (sf-Z h) 1)
       (let* ((a (car (sf-A h))) (b (cadr (sf-A h))) (c (car (sf-B h)))
              (s (sf-add c (sf-neg (sf-add a b)))))
         (cond ((sf-pole? c) #f)
               ((and (sf-rat? s) (<= s 0))
                (begin (record-condition (list '> s 0) "Гаусс: Re(c−a−b) > 0 не выполнено — ряд при z = 1 расходится") #f))
               (else
                (begin
                  (if (not (sf-rat? s)) (record-condition (list '> s 0) "Гаусс: сумма при z = 1 требует Re(c−a−b) > 0"))
                  (sf-prod-simplify (list (list 'gamma c) (list 'gamma s)
                                          (list '^ (list 'gamma (sf-add c (sf-neg a))) -1)
                                          (list '^ (list 'gamma (sf-add c (sf-neg b))) -1)))))))))

(define (sf-hx-one h)
  (let ((lg (sf-legendre-hyper h)))
    (if lg
        lg
        (let ((v (sf-chu h)))
          (if v
              v
              (let ((r (hyper-reduce h)))
                (if (not (sf-hyper? r))
                    r
                    (let ((tb (sf-hx-table r)))
                      (if tb
                          tb
                          (let ((g (sf-gauss r))) (if g g r)))))))))))

; все гипергеометрические подвыражения → элементарные/другие функции там, где есть формула
(define (hyperexpand e)
  (cond ((not (pair? e)) e)
        ((sf-hyper? e)
         (sf-hx-one (list 'hyper (map simplify (sf-list (nth e 1))) (map simplify (sf-list (nth e 2))) (simplify (nth e 3)))))
        (else (simplify (cons (car e) (map hyperexpand (cdr e)))))))

; ---------- числа: ряд с доказанной оценкой хвоста ----------

(define sf-err 0.0)

(define (sf-fpow x n) (let loop ((i 0) (r 1.0)) (if (>= i n) r (loop (+ i 1) (* r x)))))
(define (sf-int-fl? x) (= x (floor x)))
(define (sf-fpole? x) (and (<= x 0) (sf-int-fl? x)))

; t_{k+1}/t_k
(define (sf-ratio A B z k)
  (/ (* z (foldl (lambda (acc a) (* acc (+ a k))) 1.0 A))
     (* (+ k 1) (foldl (lambda (acc b) (* acc (+ b k))) 1.0 B))))

; (сумма . t_N) для членов 0..N
(define (sf-fsum A B z n)
  (let loop ((k 0) (t 1.0) (s 0.0))
    (let ((s2 (+ s t)))
      (if (>= k n) (cons s2 t) (loop (+ k 1) (* t (sf-ratio A B z k)) s2)))))

; ρ_N ≥ sup_{k ≥ N} |t_{k+1}/t_k|: |z|(N+B)^p/((N−B)^q (N+1)), B = max(1,|a|,|b|); убывает по k
(define (sf-rho A B z n bm)
  (/ (* (abs z) (sf-fpow (+ n bm) (length A)))
     (* (sf-fpow (- n bm) (length B)) (+ n 1))))

(define (sf-series-bound A B z)
  (let ((bm (foldl max 1.0 (map abs (append A B)))))
    (let try-n ((n (+ (ceiling (* 2 bm)) 2)))
      (cond ((> n 6000) #f)
            ((> (sf-rho A B z n bm) 0.5) (try-n (+ n 10)))
            (else
             (let* ((r (sf-fsum A B z n)) (rho (sf-rho A B z n bm))
                    (err (+ (* (abs (cdr r)) 2 rho) (* 1e-14 (+ n 1) (+ 1 (abs (car r)))))))
               (if (<= err (* 1e-13 (+ 1 (abs (car r)))))
                   (cons (car r) err)
                   (if (>= n 3000) #f (try-n (* 2 n))))))))))

; (значение . оценка ошибки) | #f
(define (sf-hyper-num A B z)
  (let ((negs (filter sf-fpole? A)))
    (cond ((not (null? negs))
           (let ((n (- 0 (foldl max (car negs) negs))))
             (if (any? (lambda (b) (and (sf-fpole? b) (<= (- 0 b) n))) B)
                 #f
                 (let ((r (sf-fsum A B z (floor n))))
                   (cons (car r) (* 1e-14 (+ n 1) (+ 1 (abs (car r)))))))))
          ((any? sf-fpole? B) #f)
          ((> (length A) (+ (length B) 1)) #f)
          ((and (= (length A) (+ (length B) 1)) (>= (abs z) 1)) #f)
          (else (sf-series-bound A B z)))))

(define (sf-fl x)
  (let ((v (eval-num (sf-lower x))))
    (if (number? v) v (error "specfun: не число" x))))

; ₚFq в точке (числа): ряд; при |z| ≥ 1 — через hyperexpand
(define (sf-hyper-eval e)
  (let* ((A (map sf-fl (sf-list (nth e 1)))) (B (map sf-fl (sf-list (nth e 2)))) (z (sf-fl (nth e 3)))
         (r (sf-hyper-num A B z)))
    (if r
        (begin (set! sf-err (+ sf-err (cdr r))) (car r))
        (let ((x (hyperexpand e)))
          (if (sf-hyper? x) (error "specfun: ряд не сходится, формулы нет") (sf-lower x))))))

(define (sf-lower e)
  (cond ((not (pair? e)) (if (equal? e 'euler-gamma) 0.5772156649015329 e))
        ((sf-hyper? e) (sf-hyper-eval e))
        (else
         (let ((h (car e)) (as (map sf-lower (cdr e))))
           (cond ((equal? h 'beta)
                  (list '* (list 'gamma (car as)) (list 'gamma (cadr as))
                        (list '^ (list 'gamma (list '+ (car as) (cadr as))) -1)))
                 ((equal? h 'factorial) (list 'gamma (list '+ (car as) 1)))
                 ((equal? h 'cosh) (list '* 1/2 (list '+ (list 'exp (car as)) (list 'exp (list '* -1 (car as))))))
                 ((equal? h 'sinh) (list '* 1/2 (list '+ (list 'exp (car as)) (list '* -1 (list 'exp (list '* -1 (car as)))))))
                 ((equal? h 'asinh)
                  (list 'log (list '+ (car as) (list '^ (list '+ (list '^ (car as) 2) 1) 1/2))))
                 ((equal? h 'atanh)
                  (list '* 1/2 (list 'log (list '* (list '+ 1 (car as)) (list '^ (list '+ 1 (list '* -1 (car as))) -1)))))
                 (else (cons h as)))))))

; число | #f (не число, комплексное, полюс, расходимость)
(define (sf-nu e)
  (let ((r (try (eval-num (sf-lower e)) (lambda (er) #f))))
    (if (and (number? r) (< (abs r) 1e300)) r #f)))

; числовое значение гипергеометрической функции (числовые параметры) | #f
(define (hyper-eval h)
  (begin (set! sf-err 0.0) (sf-nu h)))

; ---------- сертификат ----------

(define sf-cands '(1/3 2/5 -1/4 3/7 1/6 -2/9 4/9 1/5 5/8 -3/8 1/7 2/7 3/10 -1/5 7/9 1/4))
(define (sf-next-rand s) (modulo (+ (* s 1103515245) 12345) 2147483648))

(define (sf-point vs seed)
  (let loop ((l vs) (s seed) (rules '()))
    (if (null? l)
        (cons (reverse rules) s)
        (let ((s2 (sf-next-rand s)))
          (loop (cdr l) s2 (cons (list (car l) (nth sf-cands (modulo (quotient s2 65536) 16))) rules))))))

; подстановка по узлам: списки параметров hyper — не выражения (голова a не подставилась бы через subst)
(define (sf-at rules e)
  (cond ((null? rules) e)
        ((sf-hyper? e) (list 'hyper (map (lambda (x) (sf-at rules x)) (sf-list (nth e 1)))
                             (map (lambda (x) (sf-at rules x)) (sf-list (nth e 2))) (sf-at rules (nth e 3))))
        ((pair? e) (cons (car e) (map (lambda (x) (sf-at rules x)) (cdr e))))
        (else (subst rules e))))

; (specfun-check-numeric lhs rhs vars) → numeric | #f | unknown: до 3 рациональных точек
(define (specfun-check-numeric lhs rhs vars)
  (let ((vs (if (symbol? vars) (list vars) vars)))
    (let loop ((tries 0) (valid 0) (seed 20240601))
      (cond ((>= valid (if (null? vs) 1 3)) 'numeric)
            ((>= tries 40) 'unknown)
            (else
             (let* ((pt (sf-point vs seed)) (rules (car pt)) (seed2 (cdr pt)))
               (begin
                 (set! sf-err 0.0)
                 (let* ((lv (try (sf-nu (sf-at rules lhs)) (lambda (er) #f)))
                        (rv (try (sf-nu (sf-at rules rhs)) (lambda (er) #f))))
                   (cond ((and lv rv)
                          (if (<= (abs (- lv rv)) (+ sf-err (* 1e-9 (+ 1 (abs lv) (abs rv)))))
                              (loop (+ tries 1) (+ valid 1) seed2)
                              #f))
                         (else (loop (+ tries 1) valid seed2)))))))))))

(define (sf-zero? d) (or (equal? d 0) (equal? (try (simplify (expand d)) (lambda (e) d)) 0)))

; ---------- SFn.2a: головы Бесселя, Эйри, Лежандра ----------

; полуцелое ν: 2ν — нечётное целое
(define (sf-half-int? nu)
  (and (sf-rat? nu) (integer? (* 2 nu)) (not (= 0 (remainder (* 2 nu) 2)))))

; √(2/(πx)) и √(π/(2x))
(define (sf-bess-root x)
  (simplify (list '* (list '^ 2 1/2) (list '^ 'pi -1/2) (list '^ x -1/2))))
(define (sf-bess-kroot x)
  (simplify (list '* (list '^ 'pi 1/2) (list '^ 2 -1/2) (list '^ x -1/2))))

; J: J_{a+1} = (2a/x)J_a − J_{a−1}, базы J_{±1/2}
(define (sf-j-half nu x)
  (let* ((r (sf-bess-root x))
         (jm (simplify (list '* r (list 'cos x))))
         (jp (simplify (list '* r (list 'sin x)))))
    (cond ((= nu 1/2) jp)
          ((= nu -1/2) jm)
          ((> nu 1/2)
           (let loop ((a 1/2) (prev jm) (cur jp))
             (if (= a nu) cur
                 (loop (+ a 1) cur
                       (simplify (list '- (list '* (/ (* 2 a) x) cur) prev))))))
          (else
           (let loop ((a -1/2) (cur jm) (nxt jp))
             (if (= a nu) cur
                 (loop (- a 1)
                       (simplify (list '- (list '* (/ (* 2 a) x) cur) nxt))
                       cur)))))))

; Y: та же рекуррентность, базы Y_{1/2} = −cos·r, Y_{−1/2} = sin·r
(define (sf-y-half nu x)
  (let* ((r (sf-bess-root x))
         (ym (simplify (list '* r (list 'sin x))))
         (yp (simplify (list '* -1 r (list 'cos x)))))
    (cond ((= nu 1/2) yp)
          ((= nu -1/2) ym)
          ((> nu 1/2)
           (let loop ((a 1/2) (prev ym) (cur yp))
             (if (= a nu) cur
                 (loop (+ a 1) cur
                       (simplify (list '- (list '* (/ (* 2 a) x) cur) prev))))))
          (else
           (let loop ((a -1/2) (cur ym) (nxt yp))
             (if (= a nu) cur
                 (loop (- a 1)
                       (simplify (list '- (list '* (/ (* 2 a) x) cur) nxt))
                       cur)))))))

; I: I_{a+1} = I_{a−1} − (2a/x)I_a
(define (sf-i-half nu x)
  (let* ((r (sf-bess-root x))
         (im (simplify (list '* r (list 'cosh x))))
         (ip (simplify (list '* r (list 'sinh x)))))
    (cond ((= nu 1/2) ip)
          ((= nu -1/2) im)
          ((> nu 1/2)
           (let loop ((a 1/2) (prev im) (cur ip))
             (if (= a nu) cur
                 (loop (+ a 1) cur
                       (simplify (list '- prev (list '* (/ (* 2 a) x) cur)))))))
          (else
           (let loop ((a -1/2) (cur im) (nxt ip))
             (if (= a nu) cur
                 (loop (- a 1)
                       (simplify (list '+ nxt (list '* (/ (* 2 a) x) cur)))
                       cur)))))))

; K: K_{a+1} = K_{a−1} + (2a/x)K_a; K_{±1/2} = √(π/(2x))·e^{−x}
(define (sf-k-half nu x)
  (let ((kp (simplify (list '* (sf-bess-kroot x) (list 'exp (list '* -1 x))))))
    (cond ((or (= nu 1/2) (= nu -1/2)) kp)
          ((> nu 1/2)
           (let loop ((a 1/2) (prev kp) (cur kp))
             (if (= a nu) cur
                 (loop (+ a 1) cur
                       (simplify (list '+ prev (list '* (/ (* 2 a) x) cur)))))))
          (else
           (let loop ((a -1/2) (cur kp) (nxt kp))
             (if (= a nu) cur
                 (loop (- a 1)
                       (simplify (list '- nxt (list '* (/ (* 2 a) x) cur)))
                       cur)))))))

; (bessel-j ν x): полуцелое ν при |ν| ≤ 9/2 — элементарно; x = 0: J_0 = 1, J_ν = 0 (ν > 0)
(define (bessel-j nu x)
  (cond ((sf-half-int? nu) (if (<= (abs nu) 9/2) (sf-j-half nu x) (list 'bessel-j nu x)))
        ((and (sf-rat? nu) (equal? (simplify x) 0))
         (cond ((= nu 0) 1) ((> nu 0) 0) (else (list 'bessel-j nu x))))
        (else (list 'bessel-j nu x))))

(define (bessel-y nu x)
  (if (and (sf-half-int? nu) (<= (abs nu) 9/2))
      (sf-y-half nu x)
      (list 'bessel-y nu x)))

(define (bessel-i nu x)
  (cond ((sf-half-int? nu) (if (<= (abs nu) 9/2) (sf-i-half nu x) (list 'bessel-i nu x)))
        ((and (sf-rat? nu) (equal? (simplify x) 0))
         (cond ((= nu 0) 1) ((> nu 0) 0) (else (list 'bessel-i nu x))))
        (else (list 'bessel-i nu x))))

(define (bessel-k nu x)
  (if (and (sf-half-int? nu) (<= (abs nu) 9/2))
      (sf-k-half nu x)
      (list 'bessel-k nu x)))

; Эри: головы (значения — eval-num; Ai″ = x·Ai даёт diff)
(define (airy-ai x) (list 'airy-ai x))
(define (airy-bi x) (list 'airy-bi x))
(define (airy-ai-prime x) (list 'airy-ai-prime x))
(define (airy-bi-prime x) (list 'airy-bi-prime x))

; Полином Лежандра: целое n ≥ 0 → многочлен по рекуррентности (k+1)P_{k+1} = (2k+1)xP_k − kP_{k−1}
(define (legendre-p n x)
  (if (and (integer? n) (>= n 0) (<= n 60))
      (let loop ((k 0) (pm 0) (p 1))
        (if (= k n) p
            (loop (+ k 1) p
                  (simplify (expand (list '* (/ 1 (+ k 1))
                                          (list '- (list '* (+ (* 2 k) 1) x p)
                                                 (list '* k pm))))))))
      (list 'legendre-p n x)))

(define (legendre-q n x) (list 'legendre-q n x))

; ---------- SF.HYP: ₂F₁(a,b;c;z) и F₁ Аппеля — головы hypergeometric-2f1 / appell-f1 ----------
; Символьно: hypergeometric-2f1 сводится к hyperexpand (таблица ₚFq, DLMF 15.4: z = 0, a = 0, a = −n, c = b, ₂F₁(1,1;2;z),
; ₂F₁(½,½;3/2;z) …, Гаусс при z = 1), иначе голова остаётся. Числа — функции для крючка eval-num (define-numeric внизу):
; hypergeometric-2f1-num / appell-f1-num → число | #f (не вычислено: ветвь z > 1, вне области, полюс).
; Области ₂F₁: многочлен (a или b — целое ≤ 0) при любом z; |z| ≤ 0.9 — ряд (комплексный z, |z| ≤ 0.97);
; z < −0.9 — Пфафф 15.8.1 (w = z/(z−1) ≤ 0.9; до 0.99 при целом a−b), при больших |z| и нецелом a−b — 15.8.2 (1/z);
; 0.9 < z < 1 — связь с 1−z (15.8.4 / A&S 15.3.6, нецелое c−a−b; при целом — ряд до z ≤ 0.98); z = 1 — Гаусс при c−a−b > 0.
; F₁: двойной ряд по строкам, |x|, |y| ≤ 0.9 (иначе #f).

(define (sf-h-complex? x) (equal? (type-of x) 'complex))
(define (sf-h-npi? x)      ; целое ≤ 0 (вещественное число)
  (and (not (sf-h-complex? x)) (number? x) (<= x 0) (= x (floor x))))
(define (sf-h-mod z) (num-abs z))
; расстояние d до ближайшего целого > 1e-3 (формулы связи с нецелой разностью параметров)
(define (sf-h-nonint? d) (> (abs (- d (floor (+ d 0.5)))) 0.001))
(define (sf-h-pow x y) (eval-num (list '^ x y)))       ; x > 0
(define (sf-h-gam x) (let ((v (eval-num (list 'gamma x)))) (and (number? v) v)))

; Σ (a)_k (b)_k z^k / ((c)_k k!)
(define (sf-h-series a b c z)
  (let ((kmin (+ 6 (ceiling (+ (sf-h-mod a) (sf-h-mod b) (sf-h-mod c))))))
    (let loop ((k 0) (t 1.0) (s 0.0))
      (let ((s2 (+ s t)))
        (if (or (and (>= k kmin) (<= (sf-h-mod t) (* 1e-17 (sf-h-mod s2)))) (> k 20000))
            s2
            (loop (+ k 1) (* t (/ (* (+ a k) (+ b k) z) (* (+ c k) (+ k 1)))) s2))))))

; z < −0.9
(define (sf-h-neg a b c z)
  (let ((w (/ z (- z 1.0))))
    (cond ((<= w 0.9) (* (sf-h-pow (- 1.0 z) (- 0 a)) (sf-h-series a (- c b) c w)))   ; Пфафф, DLMF 15.8.1
          ((sf-h-nonint? (- a b))                                                      ; DLMF 15.8.2 (A&S 15.3.7)
           (let ((g1 (sf-h-gam c)) (g2 (sf-h-gam (- b a))) (g3 (sf-h-gam b)) (g4 (sf-h-gam (- c a)))
                 (g5 (sf-h-gam (- a b))) (g6 (sf-h-gam a)) (g7 (sf-h-gam (- c b))) (iz (/ 1.0 z)))
             (and g1 g2 g3 g4 g5 g6 g7
                  (+ (* (/ (* g1 g2) (* g3 g4)) (sf-h-pow (- 0 z) (- 0 a))
                        (sf-h-series a (+ (- a c) 1.0) (+ (- a b) 1.0) iz))
                     (* (/ (* g1 g5) (* g6 g7)) (sf-h-pow (- 0 z) (- 0 b))
                        (sf-h-series b (+ (- b c) 1.0) (+ (- b a) 1.0) iz))))))
          ((<= w 0.99) (* (sf-h-pow (- 1.0 z) (- 0 a)) (sf-h-series a (- c b) c w)))
          (else #f))))

; 0.9 < z < 1
(define (sf-h-near1 a b c z)
  (let ((d (- c (+ a b))) (u (- 1.0 z)))
    (if (sf-h-nonint? d)                                                               ; DLMF 15.8.4 (A&S 15.3.6)
        (let ((g1 (sf-h-gam c)) (g2 (sf-h-gam d)) (g3 (sf-h-gam (- c a))) (g4 (sf-h-gam (- c b)))
              (g5 (sf-h-gam (- 0 d))) (g6 (sf-h-gam a)) (g7 (sf-h-gam b)))
          (and g1 g2 g3 g4 g5 g6 g7
               (+ (* (/ (* g1 g2) (* g3 g4)) (sf-h-series a b (+ (- 1.0 d) 0.0) u))
                  (* (/ (* g1 g5) (* g6 g7)) (sf-h-pow u d)
                     (sf-h-series (- c a) (- c b) (+ d 1.0) u)))))
        (if (<= z 0.98) (sf-h-series a b c z) #f))))

; z = 1, Гаусс (DLMF 15.4.20), c − a − b > 0
(define (sf-h-at1 a b c)
  (let ((d (- c (+ a b))))
    (and (> d 0)
         (let ((g1 (sf-h-gam c)) (g2 (sf-h-gam d)) (g3 (sf-h-gam (- c a))) (g4 (sf-h-gam (- c b))))
           (and g1 g2 g3 g4 (/ (* g1 g2) (* g3 g4)))))))

(define (sf-h2f1-num a b c z)
  (cond ((sf-h-npi? c) #f)
        ((or (sf-h-complex? a) (sf-h-complex? b) (sf-h-complex? c) (sf-h-complex? z))
         (if (<= (sf-h-mod z) 0.97) (sf-h-series a b c z) #f))
        ((or (sf-h-npi? a) (sf-h-npi? b)) (sf-h-series a b c z))
        ((<= (abs z) 0.9) (sf-h-series a b c z))
        ((< z -0.9) (sf-h-neg a b c z))
        ((< z 1.0) (sf-h-near1 a b c z))
        ((= z 1.0) (sf-h-at1 a b c))
        (else #f)))

(define (hypergeometric-2f1-num a b c z)
  (try (sf-h2f1-num a b c z) (lambda (e) #f)))

; F₁ = Σ_m (a)_m (b₁)_m x^m /((c)_m m!) · ₂F₁(a+m, b₂; c+m; y)  (DLMF 16.13.1, ряд по строкам)
(define (sf-h-appell a b1 b2 c x y)
  (cond ((sf-h-npi? c) #f)
        ((or (> (sf-h-mod x) 0.9) (> (sf-h-mod y) 0.9)) #f)
        (else
         (let ((kmin (+ 6 (ceiling (+ (sf-h-mod a) (sf-h-mod b1) (sf-h-mod b2) (sf-h-mod c))))))
           (let loop ((m 0) (t 1.0) (s 0.0))
             (let* ((row (* t (sf-h-series (+ a m) b2 (+ c m) y))) (s2 (+ s row)))
               (if (or (and (>= m kmin) (<= (sf-h-mod row) (* 1e-17 (sf-h-mod s2)))) (> m 3000))
                   s2
                   (loop (+ m 1) (* t (/ (* (+ a m) (+ b1 m) x) (* (+ c m) (+ m 1)))) s2))))))))

(define (appell-f1-num a b1 b2 c x y)
  (try (sf-h-appell a b1 b2 c x y) (lambda (e) #f)))

; все аргументы — числа, хотя бы один float → числа (ответ | #f); иначе #f
(define (sf-h-floats? args)
  (and (every? number? args) (any? (lambda (v) (equal? (type-of v) 'float)) args)))
(define (sf-h-fl v) (if (sf-h-complex? v) v (* 1.0 v)))

(define (hypergeometric-2f1 a b c z)
  (let ((num (and (sf-h-floats? (list a b c z))
                  (hypergeometric-2f1-num (sf-h-fl a) (sf-h-fl b) (sf-h-fl c) (sf-h-fl z)))))
    (cond (num num)
          (else
           (let ((r (try (hyperexpand (list 'hyper (list a b) (list c) z)) (lambda (e) #f))))
             (if (and r (not (sf-hyper? r))) r (list 'hypergeometric-2f1 a b c z)))))))

; F₁(a; b₁, b₂; c; x, y): y = 0, x = 0, b₂ = 0, b₁ = 0 → ₂F₁; x = y → ₂F₁(a, b₁+b₂; c; x) (Чу—Вандермонд для (b₁)_m(b₂)_n)
(define (appell-f1 a b1 b2 c x y)
  (let ((num (and (sf-h-floats? (list a b1 b2 c x y))
                  (appell-f1-num (sf-h-fl a) (sf-h-fl b1) (sf-h-fl b2) (sf-h-fl c) (sf-h-fl x) (sf-h-fl y)))))
    (cond (num num)
          ((or (equal? y 0) (equal? b2 0)) (hypergeometric-2f1 a b1 c x))
          ((or (equal? x 0) (equal? b1 0)) (hypergeometric-2f1 a b2 c y))
          ((equal? x y) (hypergeometric-2f1 a (simplify (list '+ b1 b2)) c x))
          (else (list 'appell-f1 a b1 b2 c x y)))))

; крючок eval-num (SolveNum.numericHooks): головы получают числовое значение без правок F#
(define sf-h-hooks
  (list (define-numeric 'hypergeometric-2f1 hypergeometric-2f1-num)
        (define-numeric 'appell-f1 appell-f1-num)))

; (specfun-check lhs rhs vars) → #t (после hyperexpand и specfun-simplify разность 0) | numeric | #f | unknown
(define (specfun-check lhs rhs vars)
  (let ((ex (try (let ((d (list '+ (hyperexpand lhs) (list '* -1 (hyperexpand rhs)))))
                   (or (sf-zero? (specfun-simplify d))
                       (sf-zero? (specfun-simplify (specfun-duplication-collapse d)))))
                 (lambda (e) #f))))
    (if ex #t (specfun-check-numeric lhs rhs vars))))
