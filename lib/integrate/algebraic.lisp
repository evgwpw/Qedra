; algebraic.lisp — целый базис и алгебраический Эрмит для y^n = P(x) (шаг A4.1a).
; Элемент K = ℚ(x)[y]/(y^n − P) представляется вектором коэффициентов (a₀ … a_{n−1}) при y^i
; с общим знаменателем D(x): A = (Σ aᵢy^i)/D. Производная: y′ = P′y/(nP).
(module integrate
  (export radical-integral-basis integral-basis-check alg-hermite-reduce
          alg-hermite-reduce-general alg-basis-M-general alg-hermite-at-infinity-general
          alg-integrate-verdict-general alg-holomorphic-check))

; ---------- многочлены от x ----------

(define (alg-padd a b) (expand (list '+ a b)))
(define (alg-psub a b) (expand (list '- a b)))
(define (alg-pmul a b)
  (cond ((or (equal? a 0) (equal? b 0)) 0)
        ((equal? a 1) b)
        ((equal? b 1) a)
        (else (expand (list '* a b)))))
(define (alg-pmod p g x) (if (equal? g 0) p (poly-remainder (expand p) g x)))
(define (alg-pquo p g x) (poly-quotient (expand p) g x))
(define (alg-pzero? p) (equal? (expand p) 0))

(define (alg-deg p x)
  (let ((d (try (degree p x) (lambda (err) -1))))
    (if (integer? d) d -1)))

; бесквадратное разложение P: список ((g₁ e₁) …), gᵢ взаимно просты, ∏gᵢ^eᵢ = P с точностью до константы
(define (alg-sqfree-pairs P)
  (let ((fl (try (factor-list (expand P)) (lambda (err) #f))))
    (and fl (pair? (cdr fl)) (cdr fl))))

; ---------- целый базис ----------

; dᵢ = ∏ gⱼ^{⌊i·eⱼ/n⌋} — знаменатель wᵢ = yⁱ/dᵢ (Бронштейн, ISSAC'98, §2.1);
; степени eⱼ ≥ n сокращаются автоматически полом в числителе.
(define (alg-basis-d i fs n)
  (foldl (lambda (acc ge)
           (alg-pmul acc (list '^ (car ge) (quotient (* i (cadr ge)) n))))
         1 fs))

; (radical-integral-basis P n x) → (список w₀ … w_{n−1}, дискриминант базиса) | #f
(define (radical-integral-basis P n x)
  (if (or (not (integer? n)) (< n 1)) #f
      (let ((fs (alg-sqfree-pairs P)))
        (if (not fs) #f
            (let* ((ds (map (lambda (i) (alg-basis-d i fs n)) (range n)))
                   (ws (map (lambda (i) (simplify (list '/ (list '^ 'y i) (nth ds i)))) (range n)))
                   (prod (foldl (lambda (acc d) (alg-pmul acc d)) 1 ds))
                   (disc (simplify (list '* (list '^ n n)
                                         (list '^ P (- n 1))
                                         (list '^ prod -2)))))
              (list ws disc))))))

; ---------- сертификат целого базиса ----------

; (integral-basis-check P n x basis) → #t/#f
; (а) целость: числитель wᵢ = yⁱ и dᵢⁿ | Pⁱ; (б) максимальность: дискриминант базиса
; n^n·P^{n−1}/∏dᵢ² с точностью до константы равен ∏gⱼ^{n−gcd(n,eⱼ)}.
(define (integral-basis-check P n x basis)
  (and (list? basis) (= (length basis) n)
       (let loop ((i 0) (prod 1))
         (if (= i n)
             (let* ((exp-disc (simplify (list '* (list '^ n n) (list '^ P (- n 1))
                                             (list '^ prod -2))))
                    (fs (alg-sqfree-pairs P))
                    (exp-ind (foldl (lambda (acc ge)
                                      (alg-pmul acc (list '^ (car ge)
                                                          (- n (gcd n (cadr ge))))))
                                    1 fs))
                    (ratio (try (together (list '/ exp-disc exp-ind)) (lambda (err) #f))))
               (and (number? ratio) (not (equal? ratio 0))))
             (let* ((w (nth basis i))
                    (u (try (together w) (lambda (err) #f)))
                    (num (and u (numer u)))
                    (d (and u (denom u))))
               (if (not (and num d (not (contains-sym? d 'y))
                             (alg-pzero? (alg-psub num (list '^ 'y i)))
                             (alg-pzero? (alg-pmod (list '^ P i) (list '^ d n) x))))
                   #f
                   (loop (+ i 1) (alg-pmul prod d))))))))

; ---------- нормальная форма элемента K ----------

(define (alg-ydeg e)
  (let ((d (try (degree e 'y) (lambda (err) 0))))
    (if (integer? d) d 0)))

(define (alg-yfree? e) (not (contains-sym? e 'y)))

; y^k → P^⌊k/n⌋·y^(k mod n): свёртка многочлена по y в вектор длины n
(define (alg-reduce-vec cs n P)
  (let loop ((k (- (length cs) 1)) (v (map (lambda (i) 0) (range n))))
    (if (< k 0)
        v
        (let* ((c (nth cs k))
               (t (alg-pmul c (list '^ P (quotient k n))))
               (r (mod k n)))
          (loop (- k 1) (map2 (lambda (a i) (if (= i r) (alg-padd a t) a)) v (range n)))))))

; разбор дроби: (числитель . знаменатель); together представляет дроби отрицательными степенями,
; а numer/denom разбирают только одну из них — поэтому обходим произведение сами.
(define (alg-split e)
  (cond ((and (pair? e) (equal? (car e) '/) (= (length e) 3))
         (let ((a (alg-split (cadr e))) (b (alg-split (caddr e))))
           (cons (alg-pmul (car a) (cdr b)) (alg-pmul (cdr a) (car b)))))
        ((and (pair? e) (equal? (car e) '*))
         (let loop ((fs (cdr e)) (n 1) (d 1))
           (if (null? fs)
               (cons n d)
               (let ((p (alg-split (car fs))))
                 (loop (cdr fs) (alg-pmul n (car p)) (alg-pmul d (cdr p)))))))
        ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (integer? (caddr e)) (< (caddr e) 0))
         (cons 1 (list '^ (cadr e) (- (caddr e)))))
        (else (cons e 1))))

(define (alg-den a) (cdr (alg-split (together a))))
(define (alg-num a) (car (alg-split (together a))))

; общий знаменатель коэффициентов вектора (многочлены от x)
(define (alg-vec-D vec)
  (foldl (lambda (acc a) (poly-lcm acc (expand (alg-den a)))) 1 vec))

; знаменатель с y: после умножения на y^t (t = (−m) mod n) степень y кратна n,
; тогда y^{nq} = P^q; если после свёртки остаётся y — знаменатель не такого вида, #f
(define (alg-y-den-reduce e n P)
  (let* ((cs (map (lambda (k) (expand (coeff e 'y k))) (range (+ (alg-ydeg e) 1))))
         (v (alg-reduce-vec cs n P)))
    (if (every? (lambda (i) (equal? (nth v i) 0)) (cdr (range n)))
        (nth v 0)
        #f)))

; (alg-nf e P n x) → (вектор . D) | #f; e = (Σ aᵢyⁱ)/D, aᵢ — многочлены от x
(define (alg-nf e P n x)
  (let ((u (try (together e) (lambda (err) #f))))
    (if (not u)
        #f
        (let* ((sp (alg-split u)) (num0 (car sp)) (den0 (cdr sp))
               (clean (alg-yfree? den0))
               (num (if clean num0 (expand (list '* num0 (list '^ 'y (mod (- n (mod (alg-ydeg den0) n)) n))))))
               (den (if clean den0 (alg-y-den-reduce
                                     (expand (list '* den0 (list '^ 'y (mod (- n (mod (alg-ydeg den0) n)) n))))
                                     n P))))
          (if (not den)
              #f
              (let* ((cs (map (lambda (k)
                                (together (list '/ (expand (coeff num 'y k)) den)))
                              (range (+ (alg-ydeg num) 1))))
                     (v0 (alg-reduce-vec cs n P))
                     (D (alg-vec-D v0)))
                (cons (map (lambda (a) (expand (together (list '* a D)))) v0)
                      D)))))))

; (alg-vexpr (a₀ … a_{n−1})) → Σ aᵢyⁱ
(define (alg-vexpr vec)
  (simplify (cons '+ (map2 (lambda (a i) (list '* a (list '^ 'y i))) vec (range (length vec))))))

; производная элемента: y′ = P′y/(nP); коэффициенты aᵢ/D дифференцируются как функции от x
(define (alg-der-e e P n x)
  (let ((nf (alg-nf e P n x)))
    (and nf
         (let* ((vec (car nf)) (D (cdr nf)) (Pp (diff x P)))
           (alg-vexpr
            (map2 (lambda (a i)
                    (together (list '+
                                    (diff x (together (list '/ a D)))
                                    (if (= i 0)
                                        0
                                        (together (list '* a i Pp
                                                        (list '^ (list '* n P D) -1)))))))
                  vec (range n)))))))

; ---------- линейная система над ℚ ----------

(define (alg-transpose cols)
  (let ((h (if (null? cols) 0 (length (car cols)))))
    (map (lambda (r) (map (lambda (c) (nth c r)) cols)) (range h))))

; (alg-solve M b) → u: M·u = b | #f (M — строки, числа)
(define (alg-solve M b)
  (let* ((rows (map2 (lambda (row bi) (append row (list (- bi)))) M b))
         (ns (try (nullspace rows) (lambda (err) '()))))
    (let loop ((vs ns))
      (if (null? vs)
          #f
          (let* ((v (car vs)) (s (nth v (- (length v) 1))))
            (if (equal? s 0)
                (loop (cdr vs))
                (map (lambda (k) (/ (nth v k) s)) (range (- (length v) 1)))))))))

; ---------- алгебраический Эрмит в целом базисе ----------

(define (alg-coeffs-of p x dg)
  (map (lambda (t) (coeff p x t)) (range dg)))

; (alg-basis-info P n x) → (ds Q E): ds = (d₀ … d_{n−1}) из radical-integral-basis,
; Q = lcm(dᵢ), E = n·P·Q — общий знаменатель производных wᵢ′.
(define (alg-basis-info P n x)
  (let* ((fs (alg-sqfree-pairs P))
         (ds (map (lambda (i) (alg-basis-d i fs n)) (range n)))
         (Q (foldl (lambda (acc d) (poly-lcm acc d)) 1 ds)))
    (list ds Q (alg-pmul (list '* n P) Q))))

; wᵢ = yⁱ/dᵢ; wᵢ′ = (i·P′/(nP) − dᵢ′/dᵢ)·wᵢ = (i·P′·dᵢ − n·P·dᵢ′)/(n·P·dᵢ)·wᵢ.
; Поэтому w′ = M·w/E с E = n·P·Q (Q = lcm(dᵢ)) и Mᵢ = (i·P′·dᵢ − n·P·dᵢ′)·(Q/dᵢ) — многочлены от x.
(define (alg-basis-M i d Q P n x)
  (if (= i 0)
      0
      (alg-pmul (expand (list '- (list '* i (diff x P) d)
                              (list '* n P (diff x d))))
                (alg-pquo Q d x))))

; A = (Σ bᵢwᵢ)/D: bᵢ = aᵢ·dᵢ (yⁱ = dᵢwᵢ), aᵢ — коэффициенты степенного базиса
(define (alg-nf-w A P n x)
  (let ((nf (alg-nf A P n x)))
    (and nf
         (let* ((fs (alg-sqfree-pairs P))
                (ds (map (lambda (i) (alg-basis-d i fs n)) (range n))))
           (cons (map2 (lambda (a d) (alg-pmul a d)) (car nf) ds) (cdr nf))))))

; кратность V в E (V бесквадратен): сколько раз V делит E
(define (alg-val V E x)
  (let loop ((s 0) (cur E))
    (if (and (> (alg-deg cur x) 0) (alg-pzero? (alg-pmod cur V x)))
        (loop (+ s 1) (alg-pquo cur V x))
        s)))

; столбец уравнения D′·(V·(E·Bᵢ′ + Mᵢ·Bᵢ) − (k−1)·E·V′·Bᵢ) ≡ E·bᵢ (mod V^{s+1}),
; Bᵢ = x^j; V^{s+1} — модуль, s = v_V(E)
(define (alg-hermite-col-w i j V k Dp E Mi n x Mv)
  (let* ((dgv (alg-deg Mv x))
         (xj (list '^ x j))
         (xj1 (if (= j 0) 0 (list '^ x (- j 1))))
         (t1 (alg-pmul (list '* E j) (alg-pmul V xj1)))
         (t2 (alg-pmul (alg-psub (alg-pmul V Mi)
                                 (alg-pmul (list '* (- k 1) E) (diff x V)))
                       xj))
         (comp (alg-pmod (alg-pmul Dp (expand (list '+ t1 t2))) Mv x)))
    (append (map (lambda (z) 0) (range (* dgv i)))
            (alg-coeffs-of comp x dgv)
            (map (lambda (z) 0) (range (* dgv (- n i 1)))))))

; решить систему Трагера по модулю V^{s+1} (V — любой множитель D, в т. ч. V | P);
; s = v_V(E): при V | P множитель E обращается в нуль по модулю V, и сравнение по V
; вырождается — нужен модуль V^{s+1} (броню «V^k(A − U′) делится на V^{s+1}»).
(define (alg-hermite-solve bw D V k P n x ds Q E)
  (let* ((dg (alg-deg V x))
         (s (alg-val V E x))
         (Mv (expand (list '^ V (+ s 1))))
         (dgv (alg-deg Mv x))
         (Dp (alg-pquo D (list '^ V k) x))
         (Ms (map (lambda (i) (alg-basis-M i (nth ds i) Q P n x)) (range n)))
         (cols (append-map (lambda (i)
                             (map (lambda (j)
                                    (alg-hermite-col-w i j V k Dp E (nth Ms i) n x Mv))
                                  (range dg)))
                           (range n)))
         (rhs (append-map (lambda (b)
                            (alg-coeffs-of (alg-pmod (alg-pmul E b) Mv x) x dgv))
                          bw))
         (sol (and (pair? cols) (alg-solve (alg-transpose cols) rhs))))
    (and sol
         (map2 (lambda (i d)
                 (together (list '/ (simplify (cons '+ (map2 (lambda (c j) (list '* c (list '^ x j)))
                                                              (map (lambda (j) (nth sol (+ (* i dg) j)))
                                                                   (range dg))
                                                              (range dg))))
                                  (alg-pmul d (list '^ V (- k 1))))))
               (range n) ds))))

(define (alg-max-pair ps)
  (foldl (lambda (a p) (if (> (cadr p) (cadr a)) p a)) (car ps) ps))

; привести элемент к виду (Σ aᵢyⁱ)/D с aᵢ — многочленами (свёртка y^n = P)
(define (alg-normalize e P n x)
  (let ((nf (alg-nf e P n x)))
    (if (not nf)
        e
        (alg-vexpr (map (lambda (a) (together (list '/ a (cdr nf)))) (car nf))))))

; (alg-hermite-reduce A P n x) → (G H): ∫A = G + ∫H; у H знаменатель бесквадратный в целом базисе.
; Система Трагера разрешима для любого множителя V знаменателя (V | P — точки ветвления — тоже):
; в целом базисе wᵢ модуль целых замкнут относительно производной, а V бесквадратен.
(define (alg-hermite-reduce A P n x)
  (let ((info (alg-basis-info P n x)))
    (let loop ((cur A) (G 0) (guard 0))
      (if (> guard 40)
          #f
          (let ((nf (alg-nf-w cur P n x)))
            (if (not nf)
                #f
                (let* ((bw (car nf)) (D (cdr nf))
                       (fs (alg-sqfree-pairs D))
                       (high (if fs (filter (lambda (ge) (> (cadr ge) 1)) fs) '())))
                  (if (null? high)
                      (list (simplify G) (simplify (alg-normalize cur P n x)))
                      (let* ((ge (alg-max-pair high))
                             (U (alg-hermite-solve bw D (car ge) (cadr ge) P n x
                                                   (car info) (cadr info) (caddr info))))
                        (if (not U)
                            (list (simplify G) (simplify (alg-normalize cur P n x)))
                            (loop (together (list '- cur (alg-der-e (alg-vexpr U) P n x)))
                                  (together (list '+ G (alg-vexpr U)))
                                  (+ guard 1))))))))))))

; ---------- A4.3: Эрмит в общем базисе A4.2 ----------
; F ∈ ℚ[x][y] унитарен по y, n = deg_y F; элемент — пара (вектор . D): Σ aᵢyⁱ/D.
; y′ = −F_x/F_y (mod F): F_y обращается через fm-solve над ℚ(x). Матрица M полная:
; wᵢ′ = (1/E)·Σ_j M[j][i]·w_j; столбец уравнения Трагера для компоненты c берёт M[c][i].

(define (alg-g-ydeg e y)
  (let ((d (try (degree e y) (lambda (err) -1)))) (if (integer? d) d -1)))

; остаток по модулю F: вычитаем lc·y^{d−n}·F, пока deg_y ≥ n
(define (alg-g-ymod p F n y)
  (let loop ((p (expand p)) (guard 0))
    (if (or (> guard 300) (< (alg-g-ydeg p y) n))
        (expand p)
        (let* ((d (alg-g-ydeg p y))
               (lc (expand (coeff p y d)))
               (red (expand (list '* lc (list '^ y (- d n)) F))))
          (loop (expand (list '- p red)) (+ guard 1))))))

(define (alg-g-vexpr vec y)
  (simplify (cons '+ (map2 (lambda (a i) (list '* a (list '^ y i)))
                           vec (range (length vec))))))

(define (alg-g-vec-D vec)
  (foldl (lambda (acc a) (poly-lcm acc (expand (cdr (alg-split (together a)))))) 1 vec))

; (num . den) с раскрытыми вложенными дробями, в том числе внутри сумм:
; Σ nᵢ/dᵢ = (Σ nᵢ·∏_{j≠i}dⱼ) / ∏ dⱼ. alg-split такие суммы не разбирает.
(define (alg-split-full e)
  (cond ((not (pair? e)) (cons e 1))
        ((and (equal? (car e) '/) (= (length e) 3))
         (let ((a (alg-split-full (cadr e))) (b (alg-split-full (caddr e))))
           (cons (alg-pmul (car a) (cdr b)) (alg-pmul (cdr a) (car b)))))
        ((equal? (car e) '*)
         (let loop ((fs (cdr e)) (n 1) (d 1))
           (if (null? fs) (cons n d)
               (let ((p (alg-split-full (car fs))))
                 (loop (cdr fs) (alg-pmul n (car p)) (alg-pmul d (cdr p)))))))
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (caddr e)) (< (caddr e) 0))
         (cons 1 (list '^ (cadr e) (- (caddr e)))))
        ((equal? (car e) '^) (cons e 1))
        (else
         (let ((neg (equal? (car e) '-)))
           (let loop ((ts (cdr e)) (first? #t) (n 0) (d 1))
             (if (null? ts)
                 (cons (expand n) (expand d))
                 (let* ((t1 (if (and neg (not first?)) (list '* -1 (car ts)) (car ts)))
                        (p (alg-split-full t1)))
                   (if (equal? (cdr p) d)    ; общий знаменатель — без лишнего умножения
                       (loop (cdr ts) #f (alg-padd n (car p)) d)
                       (let ((n1 (alg-pmul n (cdr p)))
                             (d1 (alg-pmul d (cdr p))))
                         (loop (cdr ts) #f
                               (alg-padd n1 (alg-pmul (car p) d))
                               d1))))))))))

; e = (Σ aᵢyⁱ)/D | #f. Знаменатель с y снимается обратным по модулю F:
; e = num/den, den·inv ≡ 1 (mod F) ⇒ e ≡ num·inv (mod F), знаменатель — только по x.
(define (alg-g-nf e F n x y)
  (let ((u (try (together e) (lambda (err) #f))))
    (and u
         (let* ((sp (try (alg-split-full u) (lambda (err) #f))) (num (car sp)) (den (cdr sp)))
           (if (contains-sym? den y)
               (let ((inv (alg-g-inv-mod den F n x y)))
                 (and inv (alg-g-nf (together (list '* num (alg-g-vexpr inv y))) F n x y)))
               (let ((r (try (alg-g-ymod num F n y) (lambda (err) #f))))
                 (and r
                      (let* ((vec0 (map (lambda (k) (together (list '/ (expand (coeff r y k)) den)))
                                        (range n)))
                             (D (alg-g-vec-D vec0)))
                        (cons (map (lambda (a) (expand (together (list '* a D)))) vec0) D)))))))))

; a·y^j по модулю F
(define (alg-g-mulvar a j F n y)
  (alg-g-ymod (expand (list '* a (list '^ y j))) F n y))

; (alg-g-inv-mod a F n x y) → вектор u: a·u ≡ 1 (mod F) | #f — столбцы a·y^j,
; решение fm-solve над ℚ(x) (коэффициенты — рациональные функции от x)
(define (alg-g-inv-mod a F n x y)
  (let* ((fm (field-ratfun x))
         (cols (map (lambda (j)
                      (map (lambda (k) (together (coeff (alg-g-mulvar a j F n y) y k))) (range n)))
                    (range n)))
         (M (map (lambda (k) (map (lambda (j) (nth (nth cols j) k)) (range n))) (range n)))
         (b (cons 1 (map (lambda (i) 0) (range (- n 1)))))
         (res (try (fm-solve fm M b) (lambda (err) #f))))
    (and res (car res))))

; y′ = −F_x/F_y (mod F)
(define (alg-g-yprime F n x y)
  (let ((inv (alg-g-inv-mod (diff y F) F n x y)))
    (and inv (map (lambda (c) (together (list '* -1 (diff x F) c))) inv))))

; производная элемента → (вектор . D): ∂x e + ∂y e·y′, ∂y сдвигает коэффициенты (j+1)a_{j+1}
(define (alg-g-der e F n x y)
  (let ((nf (alg-g-nf e F n x y)))
    (and nf
         (let* ((vec (car nf)) (D (cdr nf)) (yp (alg-g-yprime F n x y)))
           (and yp
                (let* ((px (map (lambda (a) (diff x (together (list '/ a D)))) vec))
                       (py (map (lambda (j)
                                  (if (< (+ j 1) n)
                                      (together (list '/ (list '* (+ j 1) (nth vec (+ j 1))) D))
                                      0))
                                (range n)))
                       (E (together (list '+ (alg-g-vexpr px y)
                                          (list '* (alg-g-vexpr py y) (alg-g-vexpr yp y))))))
                  (alg-g-nf E F n x y)))))))

; пара (вектор . D) → выражение
(define (alg-g-expr nf y)
  (and nf (together (list '/ (alg-g-vexpr (car nf) y) (cdr nf)))))

; (alg-basis-M-general basis F n x y) → (M . E): wᵢ′ = (1/E)·Σ_j M[j][i]·w_j
(define (alg-basis-M-general basis F n x y)
  (let* ((nfs (map (lambda (w) (alg-g-nf w F n x y)) basis))
         (rows (map (lambda (nf) (map (lambda (a) (together (list '/ a (cdr nf)))) (car nf)))
                    nfs))
         (fm (field-ratfun x))
         (W (map (lambda (k) (map (lambda (j) (nth (nth rows j) k)) (range n))) (range n)))
         (sols (map (lambda (i)
                      (let ((dnf (alg-g-der (nth basis i) F n x y)))
                        (and dnf
                             (let* ((b (map (lambda (a) (together (list '/ a (cdr dnf)))) (car dnf)))
                                    (res (try (fm-solve fm W b) (lambda (err) #f))))
                               (and res (car res))))))
                    (range n))))
    (and (not (member? #f sols))
         (let* ((E (foldl (lambda (acc s)
                            (foldl (lambda (a c) (poly-lcm a (expand (cdr (alg-split (together c))))))
                                   acc s))
                          1 sols))
                (M (map (lambda (j) (map (lambda (i) (expand (together (list '* E (nth (nth sols i) j)))))
                                        (range n)))
                        (range n))))
           (cons M E)))))

; A = (Σ bᵢwᵢ)/D; W — строки w_j в базисе y
(define (alg-g-nfw A basis W F n x y)
  (let ((nf (alg-g-nf A F n x y)))
    (and nf
         (let* ((a (map (lambda (z) (together (list '/ z (cdr nf)))) (car nf)))
                (fm (field-ratfun x))
                (res (try (fm-solve fm W a) (lambda (err) #f))))
           (and res
                (let* ((b (car res))
                       (D (foldl (lambda (acc c) (poly-lcm acc (expand (cdr (alg-split (together c)))))) 1 b)))
                  (cons (map (lambda (c) (expand (together (list '* c D)))) b) D)))))))

; решение линейной системы над ℚ (переопределённой): последняя координата ядра ≠ 0
(define (alg-lin-solve M b)
  (let* ((rows (map2 (lambda (row bi) (append row (list (- bi)))) M b))
         (ns (try (nullspace rows) (lambda (err) '()))))
    (let loop ((vs ns))
      (if (null? vs)
          #f
          (let* ((v (car vs)) (s (nth v (- (length v) 1))))
            (if (equal? s 0)
                (loop (cdr vs))
                (map (lambda (k) (/ (nth v k) s)) (range (- (length v) 1)))))))))

(define (alg-g-coeffs p x dg) (map (lambda (t) (coeff p x t)) (range dg)))

; столбец неизвестной (i, j): B_i = x^j; Mcol = i-й столбец M (M[c][i] по c).
; Уравнение: Dp·(V·(E·B_i′ + Σ_i B_i M[c][i]) − (k−1)E·V′·B_i) ≡ E·b_c (mod V^{s+1}).
(define (alg-hermite-col-general i j V k Dp E Mcol n x Mv)
  (let* ((dgv (alg-deg Mv x))
         (xj (list '^ x j))
         (xj1 (if (= j 0) 0 (list '^ x (- j 1)))))
    (append-map
     (lambda (c)
       (let ((core (if (= c i)
                       (alg-psub (alg-pmul V (expand (list '+ (list '* E j xj1)
                                                           (list '* (nth Mcol c) xj))))
                                 (alg-pmul (list '* (- k 1) E (diff x V)) xj))
                       (alg-pmul V (list '* (nth Mcol c) xj)))))
         (alg-g-coeffs (alg-pmod (alg-pmul Dp core) Mv x) x dgv)))
     (range n))))

; B_i: решение системы Трагера по модулю V^{s+1}, s = v_V(E)
(define (alg-hermite-solve-general bw D V k M E n x)
  (let* ((dg (alg-deg V x))
         (s (let loop ((s 0) (cur (expand E)))
              (if (and (> (alg-deg cur x) 0) (alg-pzero? (alg-pmod cur V x)))
                  (loop (+ s 1) (alg-pquo cur V x))
                  s)))
         (Mv (expand (list '^ V (+ s 1))))
         (dgv (alg-deg Mv x))
         (Dp (alg-pquo D (list '^ V k) x))
         (cols (append-map (lambda (i)
                             (map (lambda (j) (alg-hermite-col-general i j V k Dp E
                                                                       (map (lambda (r) (nth r i)) M)
                                                                       n x Mv))
                                  (range dg)))
                           (range n)))
         (rhs (append-map (lambda (b) (alg-g-coeffs (alg-pmod (alg-pmul E b) Mv x) x dgv)) bw))
         (Mt (map (lambda (r) (map (lambda (c) (nth c r)) cols)) (range (length rhs))))
         (sol (and (pair? cols) (alg-lin-solve Mt rhs))))
    (and sol
         (map (lambda (i)
                (simplify (cons '+ (map2 (lambda (c j) (list '* c (list '^ x j)))
                                         (map (lambda (j) (nth sol (+ (* i dg) j))) (range dg))
                                         (range dg)))))
              (range n)))))

; один шаг редукции: (cur G флаг) или #f
(define (alg-hermite-step-general cur G basis W M E F n x y)
  (let ((nfw (alg-g-nfw cur basis W F n x y)))
    (if (not nfw)
        #f
        (let* ((bw (car nfw)) (D (cdr nfw))
               (fl (try (factor-list (expand D)) (lambda (err) #f))))
          (if (not fl)
              #f
              (let ((high (filter (lambda (ge) (> (cadr ge) 1)) (cdr fl))))
                (if (null? high)
                    (list cur G 'done)
                    (let* ((ge (foldl (lambda (a p) (if (> (cadr p) (cadr a)) p a)) (car high) high))
                           (V (car ge)) (k (cadr ge))
                           (Bs (alg-hermite-solve-general bw D V k M E n x)))
                      (if (not Bs)
                          (list cur G 'done)
                          (let ((U (together (list '/ (cons '+ (map2 (lambda (b w) (list '* b w))
                                                                   Bs basis))
                                                   (list '^ V (- k 1))))))
                            (let ((dU (alg-g-expr (alg-g-der U F n x y) y)))
                              (if (not dU)
                                  #f
                                  (list (together (list '- cur dU))
                                        (together (list '+ G U)) 'go)))))))))))))

; R1.1: знаменатель без кратных множителей ⇒ конечные полюсы простые,
; Эрмиту нечего снимать (базис и M в этом случае не нужны — экономия секунд)
(define (alg-den-squarefree? D x)
  (or (number? D)
      (let ((fl (try (factor-list (expand D)) (lambda (err) #f))))
        (and fl (every? (lambda (ge) (<= (cadr ge) 1)) (cdr fl))))))

; (alg-hermite-reduce-general A F x y) → (G H) | #f: ∫A = G + ∫H в общем базисе A4.2
(define (alg-hermite-reduce-general A F x y)
  (let ((n (alg-g-ydeg F y)))
    (and (> n 0)
         (let ((nf0 (try (alg-g-nf A F n x y) (lambda (err) #f))))
           (if (and nf0 (alg-den-squarefree? (cdr nf0) x))
               (list 0 (simplify (alg-g-expr nf0 y)))
               (let ((basis (try (integral-basis F x y) (lambda (err) #f))))
                 (and basis
                      (let* ((nfs (map (lambda (w) (alg-g-nf w F n x y)) basis))
                             (rows (map (lambda (nf)
                                          (map (lambda (a) (together (list '/ a (cdr nf)))) (car nf)))
                                        nfs))
                             (W (map (lambda (k)
                                       (map (lambda (j) (nth (nth rows j) k)) (range n)))
                                     (range n)))
                             (MB (alg-basis-M-general basis F n x y)))
                        (and MB
                             (let ((M (car MB)) (E (cdr MB)))
                               (let loop ((cur A) (G 0) (guard 0))
                                 (if (> guard 40)
                                     #f
                                     (let ((r (alg-hermite-step-general cur G basis W M E F n x y)))
                                       (cond ((not r) #f)
                                             ((equal? (caddr r) 'done)
                                              (list (simplify (cadr r))
                                                    (simplify (alg-g-expr (alg-g-nf (car r) F n x y) y))))
                                             (else (loop (car r) (cadr r) (+ guard 1)))))))))))))))))



; ---------- A4.3: полюсы на бесконечности для общего F ----------

; a, где F(a,y) бесквадратен по y (a — не корень disc_y F)
(define (alg-g-inf-a F x y)
  (let ((dc (try (resultant F (diff y F) y) (lambda (err) #f))))
    (and dc
         (let loop ((as '(0 1 -1 2 -2 3 -3)))
           (and (pair? as)
                (let ((v (try (simplify (subst (list (list x (car as))) dc)) (lambda (err) #f))))
                  (if (and (number? v) (not (equal? v 0))) (car as) (loop (cdr as)))))))))

; g(z) = z^d·f(a + 1/z) — многочлен (f — многочлен от x степени d)
(define (alg-g-shift-poly f x a z d)
  (if (< d 0)
      0
      (let ((s (subst (list (list x (if (equal? a 0)
                                        (list '^ z -1)
                                        (list '+ a (list '^ z -1)))))
                      f)))
        (expand (numer (together (list '* (list '^ z d) s)))))))

; Q(z,w) = z^{Mn}·F(a+1/z, w/z^M), M = max_{i<n} ⌈deg_x fᵢ/(n−i)⌉; Q унитарен по w.
; Член i: fᵢ(a+1/z) = gᵢ/z^{dᵢ} ⇒ gᵢ·wⁱ·z^{M(n−i)−dᵢ}, показатель ≥ 0 по выбору M.
(define (alg-g-inf-shift F n x y a z w)
  (let* ((cs (map (lambda (i) (expand (coeff F y i))) (range n)))
         (ds (map (lambda (f) (alg-deg f x)) cs))
         (M (foldl (lambda (acc i)
                     (let ((d (nth ds i)))
                       (if (< d 0)
                           acc
                           (max acc (quotient (+ d (- n i) -1) (- n i))))))
                   0 (range n))))
    (list (expand (cons '+
                        (append
                         (map (lambda (i)
                                (let ((d (nth ds i)))
                                  (if (< d 0)
                                      0
                                      (list '* (alg-g-shift-poly (nth cs i) x a z d)
                                            (list '^ w i)
                                            (list '^ z (- (* M (- n i)) d))))))
                              (range n))
                         (list (list '^ w n)))))
          M)))

; обратная замена: z = 1/(x−a), w = y·(x−a)^{−M}
(define (alg-g-inf-back e a M x y)
  (let ((cx (if (equal? a 0) x (list '- x a))))
    (subst (list (list 'z (list '^ cx -1))
                 (list 'w (list '* y (list '^ cx (- M)))))
           e)))

; (alg-hermite-at-infinity-general A F x y) → (G H) | #f: снять полюсы дифференциала на ∞.
; A dx = −A(a+1/z, w/z^M)/z² dz; Эрмит общего вида по Q в точке z = 0; обратно —
; G как элемент, H с якобианом dz/dx = −1/(x−a)².
(define (alg-hermite-at-infinity-general A F x y)
  (let* ((n (alg-g-ydeg F y))
         (a (alg-g-inf-a F x y)))
    (if (or (< n 1) (not a))
        #f
        (let* ((sh (alg-g-inf-shift F n x y a 'z 'w))
               (Q (car sh)) (M (cadr sh))
               (s (subst (list (list x (if (equal? a 0)
                                          (list '^ 'z -1)
                                          (list '+ a (list '^ 'z -1))))
                               (list y (list '* 'w (list '^ 'z (- M)))))
                         A))
               (Az (together (list '/ (list '- s) (list '^ 'z 2))))
               (R (alg-hermite-reduce-general Az Q 'z 'w)))
          (and R
               (let* ((G (alg-g-inf-back (car R) a M x y))
                      (Hb (alg-g-inf-back (cadr R) a M x y))
                      (Hb2 (together (list '* Hb -1 (list '^ (if (equal? a 0) x (list '- x a)) -2)))))
                 (list (simplify (alg-g-expr (alg-g-nf G F n x y) y))
                       (simplify (alg-g-expr (alg-g-nf Hb2 F n x y) y)))))))))



; ---------- A4.3: вердикт первого рода в общем базисе ----------

; линейный множитель g = x + c → корень a = −c (иначе #f)
(define (alg-linear-root g x)
  (if (= (alg-deg g x) 1)
      (let ((c (expand (coeff g x 0)))) (if (number? c) (- c) #f))
      #f))

; минимальная степень t с ненулевым коэффициентом (многочлен/сумма) | #f.
; Выражение без t — порядок 0 (если не нуль).
(define (alg-t-ord p t)
  (let ((q (try (expand p) (lambda (err) #f))))
    (and q
         (if (contains-sym? q t)
             (let ((d (try (degree q t) (lambda (err) -1))))
               (and (integer? d)
                    (let loop ((k 0))
                      (cond ((> k d) #f)
                            ((equal? (simplify (coeff q t k)) 0) (loop (+ k 1)))
                            (else k)))))
             (if (equal? (simplify q) 0) #f 0)))))

; нормирование отношения по t: ord(num) − ord(den) | #f
(define (alg-t-val e t)
  (let ((u (try (together e) (lambda (err) #f))))
    (and u
         (let* ((sp (alg-split u)) (num (car sp)) (den (cdr sp)))
           (let ((dn (alg-t-ord den t)) (nn (alg-t-ord num t)))
             (and dn nn (- nn dn)))))))

; ветвь (q ((c e) …)) → (q . y(t)), y = Σ c·t^{e·q}
(define (alg-branch-series br t)
  (let ((q (car br)))
    (cons q (expand (cons '+ (map (lambda (ce)
                                    (list '* (car ce) (list '^ t (* (cadr ce) q))))
                                  (cadr br)))))))

; голоморфность H·dx в конечной точке a (g = x − a — линейный множитель D):
; ветви Пюизё F(x+a, y), v(H) + (q−1) ≥ 0
(define (alg-g-holo-at? g H F n x y)
  (let ((a (alg-linear-root g x)))
    (if (not a)
        'unknown
        (let* ((Fa (subst (list (list x (list '+ x a))) F))
               (Ha (subst (list (list x (list '+ x a))) H))
               (brs (try (puiseux Fa x y 8) (lambda (err) #f))))
          (if (not brs)
              'unknown
              (let loop ((bs brs))
                (if (null? bs)
                    #t
                    (let* ((s (alg-branch-series (car bs) 't))
                           (q (car s)) (yt (cdr s))
                           (Ht (subst (list (list x (list '^ 't q)) (list y yt)) Ha))
                           (v (alg-t-val Ht 't)))
                      (cond ((not v) 'unknown)
                            ((>= (+ v (- q 1)) 0) (loop (cdr bs)))
                            (else #f))))))))))

; голоморфность на ∞: z-модель Q(z,w), ветви при z = 0, v(H) + (q−1) ≥ 0
(define (alg-g-holo-infty? H F n x y)
  (let ((a (alg-g-inf-a F x y)))
    (if (not a)
        'unknown
        (let* ((sh (alg-g-inf-shift F n x y a 'z 'w))
               (Q (car sh)) (M (cadr sh))
               (s (subst (list (list x (if (equal? a 0)
                                          (list '^ 'z -1)
                                          (list '+ a (list '^ 'z -1))))
                               (list y (list '* 'w (list '^ 'z (- M)))))
                         H))
               (Hz (together (list '* s -1 (list '^ 'z -2))))
               (brs (try (puiseux Q 'z 'w 4) (lambda (err) #f))))
          (if (not brs)
              'unknown
              (let loop ((bs brs))
                (if (null? bs)
                    #t
                    (let* ((s2 (alg-branch-series (car bs) 't))
                           (q (car s2)) (wt (cdr s2))
                           (Ht (subst (list (list 'z (list '^ 't q)) (list 'w wt)) Hz))
                           (v (alg-t-val Ht 't)))
                      (cond ((not v) 'unknown)
                            ((>= (+ v (- q 1)) 0) (loop (cdr bs)))
                            (else #f))))))))))

; (alg-g-holomorphic? H F n x y) → #t (доказано) | #f (полюс) | 'unknown
(define (alg-g-holomorphic? H F n x y)
  (if (equal? (simplify H) 0)
      #t
      (let ((nf (alg-g-nf H F n x y)))
        (if (not nf)
            'unknown
            (let* ((D (cdr nf))
                   (fl (try (factor-list (expand D)) (lambda (err) #f))))
              (if (not fl)
                  'unknown
                  (let loop ((fs (cdr fl)))
                    (cond ((null? fs) (alg-g-holo-infty? H F n x y))
                          ((not (alg-linear-root (car (car fs)) x)) 'unknown)
                          (else (let ((r (alg-g-holo-at? (car (car fs)) H F n x y)))
                                  (if (equal? r #t) (loop (cdr fs)) r)))))))))))

; (alg-integrate-verdict-general A F x y) → (elementary G) | (nonelementary G H) | unknown
(define (alg-integrate-verdict-general A F x y)
  (let ((n (alg-g-ydeg F y)))
    (if (< n 1)
        'unknown
        (let ((R (alg-hermite-reduce-general A F x y)))
          (if (not R)
              'unknown
              (let ((G (car R)) (H (cadr R)))
                (if (equal? (simplify H) 0)
                    (list 'elementary (simplify G))
                    (let ((Ri (if (equal? (alg-g-holo-infty? H F n x y) #t)
                                  (list 0 H)      ; полюсов на ∞ нет — шаг не нужен
                                  (alg-hermite-at-infinity-general H F x y))))
                      (if (not Ri)
                          'unknown
                          (let ((G2 (simplify (together (list '+ G (car Ri)))))
                                (H2 (cadr Ri)))
                            (if (equal? (simplify H2) 0)
                                (list 'elementary G2)
                                ; A5.7: остаток с простыми полюсами — логарифмическая часть Трагера
                                (let ((lg (try (gv-log-part H2 F x y) (lambda (e) 'unknown))))
                                  (cond
                                    ((and (list? lg) (equal? (car lg) 'logs))
                                     (list 'elementary (simplify (gv-logs->expr G2 lg))))
                                    ((equal? lg 'nonelementary)
                                     (list 'nonelementary G2 (simplify H2)))
                                    ((equal? (alg-g-holomorphic? H2 F n x y) #t)
                                     (list 'nonelementary G2 (simplify H2)))
                                    (else 'unknown))))))))))))))

; ---------- A4.3r: полюсы на бесконечности и вердикт первого рода ----------

; a ∉ корней P: замена x = a + 1/z переводит ∞ в z = 0 и не задевает ветвление P
(define (alg-inf-a P x)
  (let loop ((as '(0 1 -1 2 -2 3)))
    (and (pair? as)
         (let ((v (try (simplify (subst (list (list x (car as))) P)) (lambda (err) #f))))
           (if (and (number? v) (not (equal? v 0))) (car as) (loop (cdr as)))))))

; Q(z) = z^N·P(a + 1/z); N = n·⌈deg P/n⌉ делает правую часть многочленом
(define (alg-inf-shift P x a z N)
  (let ((s (subst (list (list x (if (equal? a 0)
                                    (list '^ z -1)
                                    (list '+ a (list '^ z -1)))))
                  P)))
    (expand (numer (together (list '* (list '^ z N) s))))))

; обратная замена элемента: z = 1/(x−a), y_z = y/(x−a)^M (y — генератор z-модели)
(define (alg-inf-back G a M x)
  (let ((cx (if (equal? a 0) x (list '- x a))))
    (subst (list (list 'z (list '^ cx -1))
                 (list 'y (list '* 'y (list '^ cx (- M)))))
           G)))

; обратная замена коэффициента при dz: H dz = H·(dz/dx) dx, dz/dx = −1/(x−a)^2
(define (alg-inf-back-diff H a M x)
  (let ((cx (if (equal? a 0) x (list '- x a))))
    (together (list '* (alg-inf-back H a M x) -1 (list '^ cx -2)))))

; (alg-hermite-at-infinity A P n x) → (G H) | #f: снять полюсы дифференциала на ∞.
; x = a + 1/z, w = y·z^M (M = ⌈deg P/n⌉, w^n = Q), A dx = −A(a+1/z)/z² dz; Эрмит A4.1b
; по z сокращает z = 0, G — поправка к ответу, H — остаток; оба — в исходной модели (y^n = P).
(define (alg-hermite-at-infinity A P n x)
  (let* ((d (alg-deg P x))
         (a (alg-inf-a P x)))
    (if (or (< d 1) (not a))
        #f
        (let* ((M (quotient (+ d (- n 1)) n))
               (N (* n M))
               (Q (alg-inf-shift P x a 'z N))
               (s (subst (list (list x (if (equal? a 0)
                                          (list '^ 'z -1)
                                          (list '+ a (list '^ 'z -1))))
                               (list 'y (list '* 'y (list '^ 'z (- M)))))
                         A))
               (Az (together (list '/ (list '- s) (list '^ 'z 2))))
               (R (alg-hermite-reduce Az Q n 'z)))
          (and R
               (list (simplify (alg-normalize (alg-inf-back (car R) a M x) P n x))
                     (simplify (alg-normalize (alg-inf-back-diff (cadr R) a M x) P n x))))))))

; кратность g в P (0, если g не делит P нацело)
(define (alg-mult g P x)
  (let loop ((s 0) (cur (expand P)))
    (if (or (< (alg-deg cur x) 1) (not (alg-pzero? (alg-pmod cur g x))))
        s
        (loop (+ s 1) (alg-pquo cur g x)))))

(define (alg-min-list xs) (foldl (lambda (a b) (if (< b a) b a)) (car xs) xs))

; вклад одной неприводимой g (m — кратность в D, e — в P) в голоморфность H·dx.
; Ветвление: E = n/gcd(n,e) — индекс, Y = e/gcd(n,e) — v(y), v(g) = E, v(dx) = E−1,
; v(wᵢ) = i·Y − E·⌊i·e/n⌋; для H = Σ bᵢwᵢ/D v(bᵢ) = E·ord_g(bᵢ). Нужно
; min_i[v(bᵢ)+v(wᵢ)] − m·E + (E−1) ≥ 0 (достаточно).
(define (alg-factor-holo? g m e bw n x)
  (let* ((dd (gcd n e)) (E (quotient n dd)) (Y (quotient e dd)))
    (let loop ((i 0) (vals '()))
      (if (= i n)
          (or (null? vals)
              (>= (+ (alg-min-list vals) (- (* m E)) (- E 1)) 0))
          (let ((b (nth bw i)))
            (if (equal? (expand b) 0)
                (loop (+ i 1) vals)
                (loop (+ i 1)
                      (cons (- (+ (* E (alg-mult g b x)) (* i Y))
                               (* E (quotient (* i e) n)))
                            vals))))))))

; (alg-holo-finite? H P n x) → #t/#f/'unknown: полюсы H·dx в конечных точках
(define (alg-holo-finite? H P n x)
  (let ((nf (alg-nf-w H P n x)))
    (if (not nf)
        'unknown
        (let ((bw (car nf)) (D (cdr nf)))
          (if (not (alg-yfree? D))
              'unknown
              (let ((fl (try (factor-list (expand D)) (lambda (err) #f))))
                (if (not fl)
                    'unknown
                    (let loop ((fs (cdr fl)))
                      (cond ((null? fs) #t)
                            ((not (alg-factor-holo? (car (car fs)) (cadr (car fs))
                                                    (alg-mult (car (car fs)) P x) bw n x))
                             #f)
                            (else (loop (cdr fs))))))))))))

; (alg-holo-infty? H P n x) → #t/'unknown: оценка нормирований на ∞ (достаточное условие).
; E = n/gcd(n,deg P), Y = deg P/gcd(n,deg P); v(x) = −E, v(y) = −Y, v(dx) = −E−1,
; v(wᵢ) = −i·Y + E·deg dᵢ. Для каждого члена bᵢwᵢ/D:
; −E·deg bᵢ − i·Y + E·deg dᵢ + E·deg D − E − 1 ≥ 0.
(define (alg-holo-infty? H P n x)
  (let* ((nf (alg-nf-w H P n x))
         (bw (car nf)) (D (cdr nf))
         (d (alg-deg P x)))
    (if (< d 1)
        'unknown
        (let* ((dd (gcd n d)) (E (quotient n dd)) (Y (quotient d dd))
               (ds (car (alg-basis-info P n x)))
               (Dd (alg-deg D x)))
          (if (< Dd 0)
              'unknown
              (let loop ((i 0))
                (cond ((= i n) #t)
                      ((equal? (expand (nth bw i)) 0) (loop (+ i 1)))
                      (else
                       (let ((bi (alg-deg (nth bw i) x)))
                         (if (< bi 0)
                             'unknown
                             (if (>= (+ (* -1 E bi) (* -1 i Y)
                                        (* E (alg-deg (nth ds i) x))
                                        (* E Dd) (- E) -1)
                                     0)
                                 (loop (+ i 1))
                                 'unknown)))))))))))

; (alg-holomorphic? H P n x) → #t (доказано) | #f (есть полюс) | 'unknown
(define (alg-holomorphic? H P n x)
  (if (equal? (simplify H) 0)
      #t
      (let ((f (alg-holo-finite? H P n x)))
        (if (equal? f #t) (alg-holo-infty? H P n x) f))))

; Шаг A5.4b: публичная проверка голоморфности остатка (для divisor.lisp)
(define (alg-holomorphic-check H P n x) (alg-holomorphic? H P n x))

; (alg-integrate-verdict A P n x) → (elementary G) | (nonelementary G H) | unknown
; Теорема (Trager гл. 5, Bronstein §2): после редукции Эрмита остаток H без полюсов;
; тогда ∫H элементарен ⇔ H = 0. Голоморфность проверяется по конечным точкам и по ∞.
(define (alg-integrate-verdict A P n x)
  (let ((R (alg-hermite-reduce A P n x)))
    (if (not R)
        'unknown
        (let ((G (simplify (car R))) (H (simplify (cadr R))))
          (if (equal? H 0)
              (list 'elementary G)
              (if (equal? (alg-holomorphic? H P n x) #t)
                  (list 'nonelementary G H)
                  'unknown))))))

; ---------- стратегия integrate ----------

; радикалы выражения: (база q), база канонизирована expand (порядок слагаемых не важен)
(define (alg-rad-nodes e)
  (cond ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (number? (caddr e)) (not (integer? (caddr e))))
         (list (list (expand (cadr e)) (denom (caddr e)))))
        ((and (pair? e) (equal? (car e) 'sqrt) (= (length e) 2))
         (list (list (expand (cadr e)) 2)))
        ((pair? e) (append-map alg-rad-nodes e))
        (else '())))

; (P q), если все радикалы — степени P^{k/q} одного P; иначе #f
(define (alg-single-radical e)
  (let ((ns (alg-rad-nodes e)))
    (and (pair? ns)
         (let ((P (car (car ns))) (q (cadr (car ns))))
           (and (> q 1)
                (every? (lambda (z) (and (equal? (car z) P) (= (cadr z) q))) ns)
                (list P q))))))

; замена радикала P^{k/n} (и √P) на y
(define (alg-rad-subst e P n)
  (cond ((and (pair? e) (equal? (car e) '^) (= (length e) 3) (equal? (expand (cadr e)) P)
              (number? (caddr e)) (not (integer? (caddr e))) (= (denom (caddr e)) n))
         (list '^ 'y (numer (caddr e))))
        ((and (pair? e) (equal? (car e) 'sqrt) (= (length e) 2)
              (equal? (expand (cadr e)) P) (= n 2))
         'y)
        ((pair? e) (map (lambda (z) (alg-rad-subst z P n)) e))
        (else e)))

(define (alg-rad-back e P n)
  (subst (list (list 'y (list '^ P (/ 1 n)))) e))

; INT.FIX2.d: ответ с дробной степенью выражения от x верен только на одной ветви радикала;
; проверяем по отрицательным точкам и записываем условие x > 0 (blake 783/784/847)
(define (alg-frac-power? e x)
  (and (pair? e)
       (or (and (equal? (car e) '^) (= (length e) 3) (number? (caddr e))
                (not (integer? (caddr e))) (contains-sym? (cadr e) x))
           (any? (lambda (a) (alg-frac-power? a x)) (cdr e)))))

; ответ по элементу G: обратная замена радикала и сертификат int-check
(define (alg-int-answer G P n e x)
  (let ((ans (try (simplify (alg-rad-back G P n)) (lambda (err) #f))))
    (if (and ans (int-check ans e x))
        (begin
          (if (and (alg-frac-power? ans x)
                   (not (equal? (int-numeric-status-at (list '- (int-diff x ans) (simplify e)) e x 1e-8 int-cheb-neg-points) 'ok)))
              (record-condition (list '> x 0)
                                "integrate: ответ с дробной степенью от x верен при x > 0 (ветвь радикала)"))
          (alg-note-cert ans e 'diff) ans)
        #f)))

; ключевой шаг «сертификат»: how = diff (производная ответа = подынтегральная, int-check) | exact (точная проверка в поле K(x, y))
(define (alg-note-cert ans e how)
  (alg-step 'alg-certificate "Сертификат ответа"
            (if (equal? how 'exact)
                "точная проверка в поле K(x, y): H = Σ (q/(m·n))·u′/u (hyp-log-check); численная проверка неустойчива из-за сокращения"
                "производная ответа совпадает с подынтегральной функцией (int-check)")
            (list 'd/dx ans) e))

; то же, но логарифмическая часть уже проверена ТОЧНО (hyp-log-check в поле K(x, y)): численный int-check
; может ложно отвергнуть log(A + B·y) при сокращении A ≈ −B·y (в double теряются знаки; пример
; ∫(28 − 5x)/(x√(4x³ − 15x² + 8x + 16)), кручение 7) — тогда достаточно точного сертификата + проверки,
; что int-check хотя бы в части точек сошёлся (int-check-how ≠ bad исключено: принимаем по точному)
(define (alg-int-answer-exact G P n e x exact-ok)
  (let ((ans (try (simplify (alg-rad-back G P n)) (lambda (err) #f))))
    (cond ((not ans) #f)
          ((int-check ans e x) (alg-note-cert ans e 'diff) ans)
          (exact-ok
           (begin (record-condition (list 'certificate-exact-log)
                                    "ответ проверен точно в поле K(x, y) (hyp-log-check); численная проверка неустойчива (сокращение)")
                  (alg-note-cert ans e 'exact)
                  ans))
          (else #f))))

; ---------- A4.3: стратегия для двух квадратичных радикалов ----------
; y = √a + √b, F = (y² − a − b)² − 4ab; обратно √a = (y² + a − b)/(2y), √b = (y² − a + b)/(2y).

(define (alg-uniq l)
  (foldl (lambda (acc x) (if (member? x acc) acc (append acc (list x)))) '() l))

; два различных квадратичных радикала (a b) | #f
(define (alg-two-radicals e)
  (let ((bs (alg-uniq (map car (filter (lambda (z) (= (cadr z) 2)) (alg-rad-nodes e))))))
    (and (= (length bs) 2) bs)))

; замена √a и √b через y: (^ a k/2) → a^{⌊k/2⌋}·√a (k нечётно)
(define (alg-two-rad-subst e a b)
  (let ((ya (list '/ (list '+ (list '^ 'y 2) a (list '* -1 b)) (list '* 2 'y)))
        (yb (list '/ (list '- (list '+ (list '^ 'y 2) b) a) (list '* 2 'y))))
    (let loop ((z e))
      (cond ((not (pair? z)) z)
            ((and (equal? (car z) '^) (= (length z) 3) (number? (caddr z))
                  (equal? (denom (caddr z)) 2))
             (let* ((k (numer (caddr z)))
                    (base (expand (cadr z)))
                    (r (cond ((equal? base (expand a)) ya)
                             ((equal? base (expand b)) yb)
                             (else #f))))
               (if r
                   (cond ((= k 1) r)
                         ((> k 1) (list '* (list '^ base (quotient k 2)) r))
                         ((= k -1) (list '/ 1 r))
                         (else (list '/ 1 (list '* (list '^ base (quotient (- k) 2)) r))))
                   (map (lambda (w) (loop w)) z))))
            ((and (equal? (car z) 'sqrt) (= (length z) 2)
                  (equal? (expand (cadr z)) (expand a))) ya)
            ((and (equal? (car z) 'sqrt) (= (length z) 2)
                  (equal? (expand (cadr z)) (expand b))) yb)
            (else (map (lambda (w) (loop w)) z))))))

(define (alg-two-rad-back G a b)
  (subst (list (list 'y (list '+ (list '^ a 1/2) (list '^ b 1/2)))) G))

(define (alg-int-two e x a b)
  (let* ((F (expand (list '- (list '^ (list '- (list '^ 'y 2) a b) 2)
                          (list '* 4 a b))))
         (Az (alg-two-rad-subst e a b)))
    (alg-step 'alg-curve "Кривая подынтегрального выражения"
              "y = √a + √b заменяет оба радикала: кривая F(x, y) = 0, F = (y² − a − b)² − 4ab"
              (int-form e x) (list '= (int-p F) 0))
    (let ((v (try (alg-integrate-verdict-general Az F x 'y) (lambda (err) 'unknown))))
      (cond ((and (pair? v) (equal? (car v) 'elementary))
             (let ((ans (try (simplify (alg-two-rad-back (cadr v) a b)) (lambda (err) #f))))
               (alg-step 'alg-hermite "Редукция Эрмита"
                         "в общем целом базисе поля K(x, y): остаток H = 0, ответ — алгебраическая часть G"
                         (int-form Az x) (cadr v))
               (if (and ans (int-check ans e x)) (begin (alg-note-cert ans e 'diff) ans) #f)))
            ((and (pair? v) (equal? (car v) 'nonelementary))
             (begin
               (record-condition
                (list 'risch-nonelementary (int-unevaluated e x '()))
                "интеграл 1-го рода: остаток H голоморфен во всех точках и H ≠ 0 — элементарной первообразной нет (Лиувилль, Трагер гл. 5)")
               (alg-refuse! "остаток H голоморфен во всех точках и H ≠ 0 — интеграл 1-го рода неэлементарен (Лиувилль, Трагер гл. 5)" e x)
               #f))
            (else #f)))))

; последняя из алгебраических: Эрмит (конечные полюсы) → полюсы на ∞ (x = a + 1/z);
; если остаток H ≠ 0 голоморфен во всех точках — доказанная неэлементарность 1-го рода.
; Шаги (журнал): рамка alg-integration с ключевыми шагами внутри (кривая, Эрмит, вычеты, дивизор, кручение, главность,
; логарифмическая часть, сертификат, причина отказа); расчёт тихий (alg-run). Доказанный отказ (alg-refused: путь записал
; условие risch-nonelementary) — рамка остаётся с причиной: путь временно возвращает 'alg%refused, снаружи — #f.
(define (alg-refuse! why e x)
  (set! alg-refused #t)
  (set! alg-why why)
  (alg-step 'alg-refusal "Неэлементарность доказана" why (int-form e x) 'nonelementary))

; наш ли вход: один радикал от многочлена или два квадратичных радикала (иначе рамки шагов и попыток не заводим)
(define (alg-applicable? e x)
  (let ((sr (alg-single-radical e)))
    (if sr
        (polynomial? (car sr) x)
        (and (alg-two-radicals e) #t))))

(define (alg-int-strategy e x d)
  (if (alg-applicable? e x) (alg-int-strategy-framed e x d) #f))

(define (alg-int-strategy-framed e x d)
  (set! alg-refused #f)
  (set! alg-why "")
  (let ((r (with-step ('alg-integration "Алгебраическое интегрирование: редукция Эрмита и метод Трагера" (int-form e x)
                       :after (lambda (v) (if (equal? v 'alg%refused) 'nonelementary v)))
             (alg-run (lambda ()
                        (let ((v (alg-int-strategy-raw e x d)))
                          (or v (and alg-refused 'alg%refused))))))))
    (if (equal? r 'alg%refused) #f r)))

; род кривой y² = P (P бесквадратен): ⌊(deg P − 1)/2⌋; иначе #f
(define (alg-genus2 P x)
  (let ((ps (try (alg-sqfree-pairs P) (lambda (err) #f))))
    (and ps (= (length ps) 1) (= (cadr (car ps)) 1)
         (let ((dg (try (degree P x) (lambda (err) #f))))
           (and dg (>= dg 1) (quotient (- dg 1) 2))))))

(define (alg-int-strategy-raw e x d)
  (let ((sr (alg-single-radical e)))
    (if sr
        (let* ((P (car sr)) (n (cadr sr))
               (A (if (polynomial? P x) (alg-rad-subst e P n) 0)))
          ; P — многочлен от x (sin x + x² и т. п. — не наш случай, сразу #f)
          (if (not (contains-sym? A 'y))
              #f
              (begin
                (alg-step 'alg-curve "Кривая подынтегрального выражения"
                          (let ((g (if (= n 2) (alg-genus2 P x) #f)))
                            (string-append "радикал заменён на y: кривая y^" (to-string n) " = P(x)"
                                           (if g (string-append "; род кривой g = " (to-string g)) "")))
                          (int-form e x) (list '= (list '^ 'y n) (int-p P)))
                (alg-int-hermite e x P n A))))
        (let ((tr (alg-two-radicals e)))
          (if (not tr)
              #f
              (alg-int-two e x (car tr) (cadr tr)))))))

(define (alg-int-hermite e x P n A)
  (let ((R (alg-hermite-reduce A P n x)))
    (if (not R)
        #f
        (let ((G (car R)) (H (cadr R)))
          (alg-step 'alg-hermite "Редукция Эрмита"
                    (if (equal? (simplify H) 0)
                        "∫A = G, остаток H = 0: у подынтегральной функции только алгебраическая часть"
                        "∫A = G + ∫H: G — алгебраическая часть, у остатка H знаменатель без кратных множителей")
                    (int-form A x)
                    (if (equal? (simplify H) 0)
                        (simplify G)
                        (if (equal? (simplify G) 0) (int-form (simplify H) x) (list '+ (simplify G) (int-form (simplify H) x)))))
          (if (equal? (simplify H) 0)
              (alg-int-answer G P n e x)
              (alg-int-infinity e x P n A G H))))))

; полюсы на ∞: поправка G + G∞; если остаток нулевой — ответ, иначе вердикт/отказ.
; Если H цел в конечных точках (знаменатель 1), полиномиальную часть берёт общий
; интегратор (по частям) — не перебиваем его формой ответа.
(define (alg-int-infinity e x P n A G H)
  (let ((nf (alg-nf-w H P n x)))
    (if (or (not nf) (number? (cdr nf)))
        (alg-int-refuse e x P n A G H)
        (let ((Ri (alg-hermite-at-infinity H P n x)))
          (if (and Ri (equal? (simplify (cadr Ri)) 0))
              (begin
                (alg-step 'alg-infinity "Полюсы на бесконечности"
                          "замена x = a + 1/z переводит ∞ в z = 0; полюсы дифференциала сняты поправкой G∞, остаток равен 0"
                          (int-form H x) (simplify (car Ri)))
                (alg-int-answer (together (list '+ G (car Ri))) P n e x))
              ; R1-хвост: полюсы на ∞ сняты частично (G∞), остаток H′ — для логарифмической части; прежде в лог-часть шёл
              ; неприведённый H, и точная часть (x²/y = (2/3)y′) делала невозможными u и вердикт
              ; (G∞ годится как точная часть, только если регулярна в конечных точках: знаменатель нормальной формы — число;
              ; иначе поправка вносит полюс в x = a и допустима лишь при нулевом остатке)
              (if (and Ri (list? Ri) (= 2 (length Ri)) (not (equal? (simplify (cadr Ri)) 0)) (= n 2)
                       (let ((nfg (try (alg-nf (car Ri) P n x) (lambda (err) #f))))
                         (and nfg (pair? nfg) (number? (cdr nfg)))))
                  (begin
                    (if (not (equal? (simplify (car Ri)) 0))
                        (alg-step 'alg-infinity "Полюсы на бесконечности"
                                  "замена x = a + 1/z переводит ∞ в z = 0; снята точная часть G∞, остаток H′ идёт в логарифмическую часть"
                                  (int-form H x) (list '+ (simplify (car Ri)) (int-form (simplify (cadr Ri)) x))))
                    (alg-int-refuse e x P n A (together (list '+ G (car Ri))) (cadr Ri)))
                  (alg-int-refuse e x P n A G H)))))))

; доказанная неэлементарность 1-го рода — через канал условий, как у эллиптики;
; Шаг A5.4: сначала логарифмическая часть Трагера (n = 2, третий род) — гипотеза A5
(define (alg-int-refuse e x P n A G H)
  (let* ((lg0 (if (= n 2)
                  (alg-attempt (lambda () (try (hyp-log-part H P x) (lambda (err) 'unknown))))
                  'unknown))
         (lg3 (if (= n 3)
                  (alg-attempt (lambda () (try (hypn3-log-part H P x) (lambda (err) 'unknown))))
                  'unknown))
         ; R1.1: hyp-* не всегда даёт сертификат вычетов на ветвлении (полюс
         ; в точке ветвления) — та же функция в модели F = y² − P через gv-*
         (lg (cond ((and (= n 3) (or (and (list? lg3) (equal? (car lg3) 'logs)) (equal? lg3 'nonelementary))) lg3)
                   ((and (= n 2) (equal? lg0 'unknown))
                    (alg-attempt (lambda () (try (gv-log-part H (expand (list '- (list '^ 'y 2) P)) x 'y)
                                                 (lambda (err) 'unknown)))))
                   (else lg0))))
    ; при успехе hyp-log-part ответ показывают шаги главности (функция u); остальные пути (n = 3, gv-) — отдельный шаг
    (if (and (list? lg) (equal? (car lg) 'logs) (not (and (= n 2) (equal? lg lg0))))
        (alg-step 'alg-log-part "Логарифмическая часть"
                  "H dx = Σ (q/(m·n))·d(log u): найдены функции u, проверка H − Σ (q/(m·n))·u′/u = 0 точная"
                  (int-form H x) (if (= n 3) (hypn3-logs->expr 0 lg) (hyp-logs->expr 0 lg))))
    (cond
      ; R1-хвост: сумма по корням g (места над ℚ(α) степени ≥ 3) — root-sum; ответ — только через int-check
      ((and (list? lg) (equal? (car lg) 'logs-sum))
       (let* ((Gs (try (simplify (list '+ G (cadr lg))) (lambda (err) #f)))
              (exact? (and (pair? (cddr lg)) (caddr lg)))
              (ans (and Gs (if exact? (alg-int-answer-exact Gs P n e x #t) (alg-int-answer Gs P n e x)))))
         (if ans ans #f)))
      ((and (list? lg) (equal? (car lg) 'logs))
       (let ((ans (alg-int-answer-exact (if (= n 3)
                                            (hypn3-logs->expr G lg)
                                            (hyp-logs->expr G lg))
                                        P n e x
                                        ; точный сертификат: G = 0 (вся функция — лог-часть) и hyp-log-check
                                        (and (= n 2) (equal? G 0) (equal? lg lg0)
                                             (equal? #t (try (hyp-log-check H P x lg) (lambda (err) #f)))))))
         (if ans ans #f)))
      ((equal? lg 'nonelementary)
       (begin
         (record-condition
          (list 'risch-nonelementary (int-unevaluated e x '()))
          "интеграл 3-го рода: вычеты и граница кручения Трагера A5 отвергают все n (δ не кручение) либо остаток голоморфен и не 0 либо имеет неснимаемый полюс порядка ≥ 2 (2-й род, A5.4c) — элементарной первообразной нет")
         (alg-refuse! (if (equal? alg-why "")
                          "вычеты и граница кручения Трагера отвергают все n, либо остаток голоморфен и не 0, либо у него неснимаемый полюс порядка ≥ 2 (2-й род)"
                          alg-why)
                      e x)
         #f))
      (else
       (let ((v (alg-integrate-verdict A P n x)))
         (if (and (pair? v) (equal? (car v) 'nonelementary))
             (begin
               (record-condition
                (list 'risch-nonelementary (int-unevaluated e x '()))
                "интеграл 1-го рода: остаток H голоморфен во всех точках и H ≠ 0 — элементарной первообразной нет (Лиувилль, Трагер гл. 5)")
               (alg-refuse! "остаток H голоморфен во всех точках и H ≠ 0 — интеграл 1-го рода неэлементарен (Лиувилль, Трагер гл. 5)" e x)
               #f)
             #f))))))

(int-add-strategy alg-int-strategy)



; ---------- INT.FIX2.e: exp(c·atan u) и exp(c·atanh u) — алгебраические функции ----------
; exp(i·atan u) = (1 + i·u)/√(1 + u²), exp(atanh u) = √((1 + u)/(1 − u)):
; при целом k = c/i (atan) или k = c (atanh) экспонента — степень алгебраической дроби, и интеграл берёт
; алгебраическая стратегия. u линейно по x (Rubi t_5_3_6: exp(k·i·atan(a·x)) с полиномиальными множителями).
(define (alg-atan-kernel? z x)
  (and (pair? z) (member? (car z) '(atan atanh)) (= (length z) 2)
       (try (and (polynomial? (cadr z) x) (= (degree (cadr z) x) 1)) (lambda (err) #f)) #t))

; показатель exp → (kind u k) или #f
(define (alg-exp-atan-split a x)
  (let* ((fs (if (and (pair? a) (equal? (car a) '*) (pair? (cdr a))) (cdr a) (list a)))
         (at (filter (lambda (f) (and (pair? f) (member? (car f) '(atan atanh)))) fs)))
    (and (= (length at) 1) (alg-atan-kernel? (car at) x)
         (let* ((kv (car at)) (u (cadr kv))
                (c (try (simplify (list '* a (list '^ kv -1))) (lambda (err) #f))))
           (and c (x-free? c x)
                (every? (lambda (v) (equal? v '%i)) (variables c))
                (list (car kv) u (simplify (list '* (if (equal? (car kv) 'atan) (list '* -1 '%i) 1) c))))))))

; exp(c·atan u) → (^ ((1 + i·u)/√(1+u²)) k); exp(c·atanh u) → (^ ((1+u)/√(1−u²)) k)
(define (alg-exp-atan-rewrite k x)
  (and (pair? k) (equal? (car k) 'exp) (= (length k) 2)
       (let ((sp (alg-exp-atan-split (cadr k) x)))
         (and sp (integer? (nth sp 2))
              (let* ((kind (nth sp 0)) (u (nth sp 1)) (kk (nth sp 2))
                     (base (if (equal? kind 'atan)
                               (simplify (list '* (list '+ 1 (list '* '%i u))
                                               (list '^ (list '+ 1 (list '^ u 2)) -1/2)))
                               (simplify (list '* (list '+ 1 u)
                                               (list '^ (list '+ 1 (list '* -1 (list '^ u 2))) -1/2))))))
                (list '^ base kk))))))

(define (alg-walk-exp-atan e x)
  (cond ((not (pair? e)) (list e #f))
        ((equal? (car e) (quote exp))
         (let ((r (alg-exp-atan-rewrite e x))) (if r (list r #t) (list e #f))))
        (else
         (let* ((rs (map (lambda (a) (alg-walk-exp-atan a x)) (cdr e)))
                (ch (any? (lambda (r) (cadr r)) rs)))
           (list (cons (car e) (map car rs)) ch)))))

(define (int-trigexp-atan e x d)
  (and (< d int-max-depth)
       (let* ((rw (alg-walk-exp-atan e x)))
         (and (cadr rw)
              (let ((e2 (try (expand (simplify (car rw))) (lambda (err) #f))))
                (and e2 (not (equal? e2 e))
                     (with-step ('int-substitution "Экспонента от арктангенса — алгебраическая форма" (int-form e2 x)
                                 :comment "exp(i·atan u) = (1 + i·u)/√(1 + u²): интеграл сводится к алгебраическому"
                                 :after int-p)
                       (let ((r (int-go e2 x (+ d 1))))
                         (if (and r (int-check r e x)) r
                             (begin (attempt-fail "алгебраическая форма не проинтегрирована") #f))))))))))

(int-add-strategy int-trigexp-atan)


; ---------- INT.FIX2.e (продолжение): k кратно 1/2 — подстановка s = (1+iu)/(1−iu), z = s^(1/4) ----------
; exp(c·atan u) = s^(k/2), k = c/i, s = exp(2i·atan u); при 2k ∈ ℤ замена z^4 = s делает подынтегральное
; рациональным по z (u линейно по x). Дробные степени двух линейных множителей — то же, что подстановка Чебышёва.
(define (alg-one-atan-exp e x)
  (let ((hits (alg-collect-atan-exp e x)))
    (and (= (length hits) 1) (car hits))))

(define (alg-collect-atan-exp e x)
  (if (not (pair? e))
      '()
      (let ((inner (apply append (map (lambda (a) (alg-collect-atan-exp a x)) (cdr e)))))
        (if (and (equal? (car e) 'exp) (= (length e) 2))
            (let* ((sp (alg-exp-atan-split (cadr e) x)))
              (if sp (append inner (list (list e (nth sp 0) (nth sp 1) (nth sp 2)))) inner))
            inner))))

(define (int-atan-exp e x d)
  (let ((sp (and (< d int-max-depth) (alg-one-atan-exp e x))))
    (if (not sp) #f
        (let* ((node (car sp)) (kind (cadr sp)) (u (caddr sp)) (k (nth sp 3)))
          (if (or (not (equal? kind 'atan)) (not (integer? (* 2 k))) (= (* 2 k) 0)) #f
              (let* ((a (try (coeff u x 1) (lambda (err) #f)))
                     (b (try (coeff u x 0) (lambda (err) #f)))
                     (z (int-uvar d))
                     (t4 (list '^ z 4))
                     (u-z (list '/ (list '- t4 1) (list '* '%i (list '+ t4 1))))
                     (xz (list '/ (list '- u-z b) a))
                     (jac (simplify (list '/ (list '* 8 (list '^ z 3))
                                          (list '* '%i a (list '^ (list '+ t4 1) 2))))))
                (if (or (not a) (not b) (not (x-free? a x)) (not (x-free? b x)) (equal? a 0)) #f
                    (let* ((e2 (simplify (list '* (replace-expr (replace-expr e node (list '^ z (* 2 k))) x xz) jac))))
                      (if (or (contains-sym? e2 'exp) (contains-sym? e2 'atan)) #f
                          (with-step ('int-substitution "Экспонента от арктангенса — подстановка s = exp(2i·atan u)"
                                      (int-form e x)
                                      :comment "s^(k/2) при s = z^4: подынтегральное рационально по z"
                                      :after int-p)
                            (let* ((r (int-go e2 z (+ d 1)))
                                   (back (and r (simplify (replace-expr r z
                                            (list '^ (list '/ (list '+ 1 (list '* '%i u)) (list '- 1 (list '* '%i u))) 1/4))))))
                              (cond ((not r) (begin (attempt-fail "подстановка не проинтегрирована") #f))
                                    ((int-check back e x) back)
                                    (else (attempt-fail "ответ подстановки не прошёл проверку") #f)))))))))))))

(int-add-strategy int-atan-exp)
