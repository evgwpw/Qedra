; multiint.lisp — Шаг MINT.a: кратные интегралы одной записью, замена переменных с якобианом, интегралы первого рода.
;
; Диапазон — список (переменная нижний верхний); (переменная) без пределов — неопределённый интеграл.
; Кратный интеграл: первый диапазон — ВНЕШНИЙ интеграл, последний — ВНУТРЕННИЙ (как в учебниках и Mathematica):
; (integrate-multi f '((x 0 1) (y 0 x))) = ∫₀¹ (∫₀ˣ f dy) dx; пределы внутреннего могут зависеть от внешних переменных.
; Реализация — вложенные integrate изнутри наружу; не взялся внутренний — невычисленная вложенная запись.
;
; Модуль якобиана: |det ∂x/∂u| нужен ВСЕГДА (площадь не бывает отрицательной). Знак определяет mi-sign по областям
; интегрирования: «≥ 0» (pos), «≤ 0» (neg), «= 0» (zero) или unk. Рассуждение строгое (интервальное по знакам):
; переменная диапазона — по знакам его пределов (рекурсивно, пределы могут зависеть от внешних переменных);
; sin/cos от переменной с пределами вида q·π — точно по целым частям q; чётная степень — pos; константы и параметры — sign-of
; (декларации, assuming). Не вышло — остаётся (abs …), и интеграл честно не берётся.
;
; Ответы первого рода: ∫ f ds = ∫ f(φ(t))·|φ′(t)| dt и ∫∫ f dS = ∫∫ f(r)·√(EG − F²) du dv; корень берётся по множителям
; (√(g²) → |g| → g при известном знаке), поэтому для символьных параметров (радиус R) нужна декларация R > 0
; (assuming ((R (interval 0 'inf))) …), иначе ответ содержит |R|.

(module multiint
  (export integrate-multi integrate-change jacobian-det line-integral arc-length surface-integral surface-area
          integrate-region region-swap green-check stokes-surface-check gauss-check))

; ---------- упрощение ----------

(define (mi-simp e)
  (let ((s (simplify e)))
    (if (pair? s) (try (simplify (trigsimp s)) (lambda (er) s)) s)))

; наименьшее по размеру из simplify, trigsimp, factor
(define (mi-best e)
  (let ((s (mi-simp e)))
    (if (not (pair? s))
        s
        (let ((f (try (mi-simp (factor s)) (lambda (er) s))))
          (if (< (trigsimp-size f) (trigsimp-size s)) f s)))))

; ---------- знаки ----------

(define (mi-s* a b)
  (cond ((or (equal? a 'zero) (equal? b 'zero)) 'zero)
        ((or (equal? a 'unk) (equal? b 'unk)) 'unk)
        ((equal? a b) 'pos)
        (else 'neg)))

(define (mi-s+ a b)
  (cond ((equal? a 'zero) b)
        ((equal? b 'zero) a)
        ((equal? a b) a)
        (else 'unk)))

(define (mi-const-sign e)
  (cond ((equal? e 'inf) 'pos)
        ((equal? e '-inf) 'neg)
        (else
         (let ((s (try (sign-of e) (lambda (er) 'unknown))))
           (cond ((member? s '(positive nonnegative)) 'pos)
                 ((member? s '(negative nonpositive)) 'neg)
                 ((equal? s 'zero) 'zero)
                 (else 'unk))))))

(define (mi-remove v env) (filter (lambda (r) (not (equal? (car r) v))) env))

; кратное π: e = q·π с рациональным q — q, иначе #f
(define (mi-pi-mult e)
  (cond ((and (number? e) (not (equal? (type-of e) 'float)) (= e 0)) 0)
        ((equal? e 'pi) 1)
        ((and (pair? e) (equal? (car e) '*) (= (length e) 3) (number? (cadr e))
              (not (equal? (type-of (cadr e)) 'float)) (equal? (caddr e) 'pi))
         (cadr e))
        (else #f)))

; знак sin (shift = 0) или cos (shift = 1/2) на отрезке переменной r = (v lo hi) с пределами q·π
(define (mi-trig-sign r shift)
  (let ((a (mi-pi-mult (cadr r))) (b (mi-pi-mult (caddr r))))
    (if (or (not a) (not b))
        'unk
        (let* ((lo (+ (if (< a b) a b) shift)) (hi (+ (if (< a b) b a) shift)))
          (if (= (floor lo) (- (ceiling hi) 1))
              (if (= (modulo (floor lo) 2) 0) 'pos 'neg)
              'unk)))))

(define (mi-var-sign r env)
  (let* ((env2 (mi-remove (car r) env))
         (a (mi-sign (cadr r) env2))
         (b (mi-sign (caddr r) env2)))
    (cond ((and (equal? a 'zero) (equal? b 'zero)) 'zero)
          ((and (member? a '(pos zero)) (member? b '(pos zero))) 'pos)
          ((and (member? a '(neg zero)) (member? b '(neg zero))) 'neg)
          (else 'unk))))

(define (mi-sign e env)
  (cond ((number? e) (cond ((> e 0) 'pos) ((< e 0) 'neg) (else 'zero)))
        ((symbol? e)
         (let ((r (assoc e env)))
           (if (and r (= (length r) 3)) (mi-var-sign r env) (mi-const-sign e))))
        ((not (pair? e)) 'unk)
        ((equal? (car e) '+) (foldl (lambda (acc a) (mi-s+ acc (mi-sign a env))) 'zero (cdr e)))
        ((equal? (car e) '*) (foldl (lambda (acc a) (mi-s* acc (mi-sign a env))) 'pos (cdr e)))
        ((and (equal? (car e) '^) (= (length e) 3))
         (let ((n (caddr e)) (s (mi-sign (cadr e) env)))
           (cond ((and (integer? n) (= (modulo n 2) 0)) 'pos)
                 ((integer? n) s)
                 ((equal? s 'pos) 'pos)
                 (else 'unk))))
        ((and (member? (car e) '(sin cos)) (= (length e) 2) (symbol? (cadr e)))
         (let ((r (assoc (cadr e) env)))
           (if (and r (= (length r) 3)) (mi-trig-sign r (if (equal? (car e) 'sin) 0 1/2)) 'unk)))
        ((member? (car e) '(exp abs)) 'pos)
        ((and (equal? (car e) 'sqrt) (= (length e) 2) (member? (mi-sign (cadr e) env) '(pos zero))) 'pos)
        ((any? (lambda (r) (contains-sym? e (car r))) env) 'unk)
        (else (mi-const-sign e))))

; |b| с учётом знака
(define (mi-abs b env)
  (let ((s (mi-sign b env)))
    (cond ((equal? s 'pos) b)
          ((equal? s 'neg) (mi-simp (list '* -1 b)))
          ((equal? s 'zero) 0)
          (else (simplify (list 'abs b))))))

; |e| для произведения — по множителям
(define (mi-abs-prod e env)
  (if (and (pair? e) (equal? (car e) '*))
      (mi-simp (cons '* (map (lambda (a) (mi-abs a env)) (cdr e))))
      (mi-abs e env)))

; √e, e ≥ 0: по множителям; чётная степень g^(2k) → |g|^k
(define (mi-sqrt e env)
  (cond ((number? e) (simplify (list 'sqrt e)))
        ((and (pair? e) (equal? (car e) '*))
         (mi-simp (cons '* (map (lambda (a) (mi-sqrt a env)) (cdr e)))))
        ((and (pair? e) (equal? (car e) '^) (integer? (caddr e)) (= (modulo (caddr e) 2) 0))
         (mi-simp (list '^ (mi-abs (cadr e) env) (/ (caddr e) 2))))
        (else (simplify (list 'sqrt e)))))

; ---------- якобиан ----------

(define (mi-minor m j) (map (lambda (row) (append (take row j) (drop (drop row j) 1))) (cdr m)))

(define (mi-det m)
  (if (null? (cdr m))
      (car (car m))
      (list '+ (foldl (lambda (acc j)
                        (list '+ acc (list '* (if (= (modulo j 2) 0) 1 -1) (list-ref-mi (car m) j)
                                           (mi-det (mi-minor m j)))))
                      0 (range (length (car m)))))))

(define (list-ref-mi l i) (nth l i))

; (jacobian-det phi vars) — det ∂φᵢ/∂vⱼ (упрощённый)
(define (jacobian-det phi vars)
  (if (not (= (length phi) (length vars)))
      (error "jacobian-det: число функций не равно числу переменных")
      (mi-best (mi-det (map (lambda (p) (map (lambda (v) (diff v p)) vars)) phi)))))

; ---------- кратный интеграл ----------

(define (mi-int1 e r)
  (if (null? (cdr r))
      (integrate e (car r))
      (integrate e (car r) (cadr r) (caddr r))))

; оборачивание в невычисленные integrate: rs — диапазоны от внутреннего к внешнему
(define (mi-wrap v rs)
  (foldl (lambda (acc r) (append (list 'integrate acc) r)) v rs))

(define (mi-nest e rs)
  (if (null? rs)
      e
      (let ((v (mi-int1 e (car rs))))
        (if (and (pair? v) (contains-sym? v 'integrate))
            (mi-wrap v (cdr rs))
            (mi-nest v (cdr rs))))))

(define (mi-check-ranges rs)
  (for-each (lambda (r)
              (if (not (and (pair? r) (symbol? (car r)) (or (= (length r) 1) (= (length r) 3))))
                  (error "integrate: диапазон — [переменная, нижний, верхний] или [переменная]")
                  #t))
            rs))

(define (mi-multi-raw f ranges)
  (begin
    (mi-check-ranges ranges)
    (let ((v (mi-nest f (reverse ranges))))
      (if (pair? v) (try (simplify v) (lambda (er) v)) v))))

; (integrate-multi f ((x a b) (y c d) …)) — первый диапазон внешний, последний внутренний.
; Двойной интеграл, у которого внутренний не взялся: если область «между графиками» обращается (шаг MINT.b) —
; пересчёт для другого порядка (Фубини, с записью условия fubini-swap); иначе — невычисленная запись как есть.
(define (integrate-multi f ranges)
  (let ((v (mi-multi-raw f ranges)))
    (if (and (pair? v) (contains-sym? v 'integrate) (= (length ranges) 2)
             (every? (lambda (r) (= (length r) 3)) ranges))
        (let ((w (mr-try-swap f (car ranges) (cadr ranges))))
          (if w w v))
        v)))

; ---------- замена переменных ----------

; subs — polar, cylindrical, spherical или список ((x e1) (y e2) …) / ((= x e1) …) / (x e1)
(define (mi-std-subs name us)
  (cond ((and (equal? name 'polar) (= (length us) 2))
         (list (list 'x (list '* (nth us 0) (list 'cos (nth us 1))))
               (list 'y (list '* (nth us 0) (list 'sin (nth us 1))))))
        ((and (equal? name 'cylindrical) (= (length us) 3))
         (list (list 'x (list '* (nth us 0) (list 'cos (nth us 1))))
               (list 'y (list '* (nth us 0) (list 'sin (nth us 1))))
               (list 'z (nth us 2))))
        ((and (equal? name 'spherical) (= (length us) 3))
         (list (list 'x (list '* (nth us 0) (list 'sin (nth us 1)) (list 'cos (nth us 2))))
               (list 'y (list '* (nth us 0) (list 'sin (nth us 1)) (list 'sin (nth us 2))))
               (list 'z (list '* (nth us 0) (list 'cos (nth us 1))))))
        (else (error "integrate_change: polar — 2 диапазона, cylindrical и spherical — 3"))))

(define (mi-norm-sub s)
  (cond ((and (pair? s) (equal? (car s) '=) (= (length s) 3)) (list (cadr s) (caddr s)))
        ((and (pair? s) (= (length s) 2) (symbol? (car s))) s)
        (else (error "integrate_change: подстановка — x = выражение"))))

; (integrate-change f subs ranges): ranges — диапазоны НОВЫХ переменных (первый — внешний)
(define (integrate-change f subs ranges)
  (begin
    (mi-check-ranges ranges)
    (let* ((us (map car ranges))
           (ss (if (symbol? subs) (mi-std-subs subs us) (map mi-norm-sub subs)))
           (olds (map car ss))
           (news (map cadr ss)))
      (if (not (= (length olds) (length us)))
          (error "integrate_change: число подстановок не равно числу диапазонов")
          (let* ((j (jacobian-det news us))
                 (aj (mi-abs-prod j ranges))
                 (g (mi-simp (list '* (subst ss f) aj))))
            (integrate-multi g ranges))))))

; ---------- первого рода ----------

(define (mi-sumsq l) (list '+ (foldl (lambda (acc a) (list '+ acc (list '^ a 2))) 0 l)))

; ∫ f ds по кривой φ(t), t ∈ [a, b]: (line-integral f vars phi (t a b))
(define (line-integral f vars phi range)
  (begin
    (mi-check-ranges (list range))
    (if (not (and (= (length vars) (length phi)) (= (length range) 3)))
        (error "line_integral: ожидается line_integral(f, [x, y, …], [φ₁, φ₂, …], [t, a, b])")
        (let* ((t (car range))
               (ds (mi-sqrt (mi-best (mi-sumsq (map (lambda (p) (diff t p)) phi))) (list range)))
               (g (mi-simp (list '* (subst (map2 list vars phi) f) ds))))
          (integrate-multi g (list range))))))

(define (arc-length phi range)
  (line-integral 1 (range-vars-mi (length phi)) phi range))

(define (range-vars-mi n) (map (lambda (i) (nth '(x1 x2 x3 x4 x5 x6) i)) (range n)))

(define (mi-dot a b) (list '+ (foldl (lambda (acc i) (list '+ acc (list '* (nth a i) (nth b i)))) 0 (range (length a)))))

; ∫∫ f dS по поверхности r(u, v): (surface-integral f vars phi (u a b) (v c d)); u — внешний, v — внутренний
(define (surface-integral f vars phi ru rv)
  (begin
    (mi-check-ranges (list ru rv))
    (if (not (and (= (length vars) (length phi)) (= (length ru) 3) (= (length rv) 3)))
        (error "surface_integral: ожидается surface_integral(f, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d])")
        (let* ((u (car ru)) (v (car rv))
               (pu (map (lambda (p) (diff u p)) phi))
               (pv (map (lambda (p) (diff v p)) phi))
               (e (mi-simp (mi-dot pu pu))) (g0 (mi-simp (mi-dot pv pv))) (ff (mi-simp (mi-dot pu pv)))
               (n2 (mi-best (list '+ (list '* e g0) (list '* -1 (list '^ ff 2)))))
               (dS (mi-sqrt n2 (list ru rv)))
               (g (mi-simp (list '* (subst (map2 list vars phi) f) dS))))
          (integrate-multi g (list ru rv))))))

(define (surface-area phi ru rv)
  (surface-integral 1 (range-vars-mi (length phi)) phi ru rv))

; ---------- шаг MINT.b: области, смена порядка интегрирования (Фубини), проверки Грина / Стокса / Гаусса ----------
;
; Область — данные:
;   (rect (x a b) (y c d))                      прямоугольник
;   (between (x a b) (y g1 g2))                 a ≤ x ≤ b, g1(x) ≤ y ≤ g2(x); внешняя переменная — первая
;   (triangle (x y) (x1 y1) (x2 y2) (x3 y3))    треугольник с числовыми вершинами
;   (disk (x y) (cx cy) r), (annulus (x y) (cx cy) r1 r2)   круг, кольцо — полярные координаты (integrate-change)
; (integrate-region f область) берёт интеграл в заданном порядке; не взялся внутренний — пересчитывает область для
; другого порядка и берёт в нём (запись условия fubini-swap). Перестановка для «между графиками» — только если одна граница
; постоянна (горизонтальная/вертикальная прямая), а другая строго монотонна на [a, b] (знак производной по mi-sign) и
; обращается: решение g(x) = y проверяется численно в трёх внутренних точках. Иначе — отказ (невычисленная запись).

(define (mr-numval e)
  (let ((r (try (eval-num e) (lambda (er) #f)))) (if (number? r) r #f)))

; монотонность h по x на [a, b]: inc, dec или #f
(define (mr-monotone h x a b)
  (let* ((d (try (simplify (diff x h)) (lambda (er) #f)))
         (s (if d (mi-sign d (list (list x a b))) 'unk)))
    (cond ((equal? s 'pos) 'inc) ((equal? s 'neg) 'dec) (else #f))))

; x = h⁻¹(y): ветвь решения h(x) = y, совпадающая с x на [a, b] (проверка в точках a + (b−a)k/4), иначе #f
(define (mr-inverse h x y a b)
  (let* ((av (mr-numval a)) (bv (mr-numval b))
         (xs (map (lambda (k) (+ av (* (- bv av) (/ k 4)))) '(1 2 3)))
         (ys (map (lambda (xv) (mr-numval (subst (list (list x xv)) h))) xs))
         (cands (try (set->list (solve (list '= h y) x)) (lambda (er) '()))))
    (if (any? (lambda (v) (not v)) ys)
        #f
        (let ((ok (filter (lambda (c)
                            (every? (lambda (p)
                                      (let ((r (mr-numval (subst (list (list y (cadr p))) c))))
                                        (and r (< (abs (- r (car p))) 1e-9))))
                                    (map2 list xs ys)))
                          cands)))
          (if (null? ok) #f (simplify (car ok)))))))

(define (mr-at h x v) (simplify (subst (list (list x v)) h)))

; обратный порядок для области «между графиками»: список кусков (внешний внутренний) или #f
(define (mr-swap-pieces ro ri)
  (let* ((x (car ro)) (a (cadr ro)) (b (caddr ro))
         (y (car ri)) (g1 (simplify (cadr ri))) (g2 (simplify (caddr ri)))
         (c1 (not (contains-sym? g1 x))) (c2 (not (contains-sym? g2 x)))
         (av (mr-numval a)) (bv (mr-numval b)))
    (cond ((and c1 c2) (list (list ri ro)))
          ((contains-sym? (list g1 g2) y) #f)
          ((not (and av bv (< av bv))) #f)
          ((and c1 (not c2)) (mr-swap-low g1 g2 x a b y))
          ((and c2 (not c1)) (mr-swap-high g1 g2 x a b y))
          (else #f))))

; (region-swap (x a b) (y g1 g2)) — куски ((внешний внутренний) …) того же множества в порядке y-внешний, либо #f (отказ)
(define (region-swap ro ri) (try (mr-swap-pieces ro ri) (lambda (er) #f)))

; нижняя граница постоянна (c), верхняя h(x) монотонна
(define (mr-swap-low c h x a b y)
  (let ((m (mr-monotone h x a b)))
    (if (not m)
        #f
        (let ((hi (mr-inverse h x y a b)) (ya (mr-at h x a)) (yb (mr-at h x b)))
          (if (not hi)
              #f
              (if (equal? m 'inc)
                  (and (mr-leq c ya)
                       (append (if (mr-lt c ya) (list (list (list y c ya) (list x a b))) '())
                               (list (list (list y ya yb) (list x hi b)))))
                  (and (mr-leq c yb)
                       (append (if (mr-lt c yb) (list (list (list y c yb) (list x a b))) '())
                               (list (list (list y yb ya) (list x a hi)))))))))))

; верхняя граница постоянна (d), нижняя h(x) монотонна
(define (mr-swap-high h d x a b y)
  (let ((m (mr-monotone h x a b)))
    (if (not m)
        #f
        (let ((lo (mr-inverse h x y a b)) (ya (mr-at h x a)) (yb (mr-at h x b)))
          (if (not lo)
              #f
              (if (equal? m 'inc)
                  (and (mr-leq yb d)
                       (append (list (list (list y ya yb) (list x a lo)))
                               (if (mr-lt yb d) (list (list (list y yb d) (list x a b))) '())))
                  (and (mr-leq ya d)
                       (append (list (list (list y yb ya) (list x lo b)))
                               (if (mr-lt ya d) (list (list (list y ya d) (list x a b))) '())))))))))

(define (mr-cmp a b) (let ((p (mr-numval a)) (q (mr-numval b))) (if (and p q) (- p q) #f)))
(define (mr-leq a b) (let ((r (mr-cmp a b))) (and r (<= r 1e-12))))
(define (mr-lt a b) (let ((r (mr-cmp a b))) (and r (> (- r) 1e-12))))

; куски → значение: 0 куски — 0; не взялся хотя бы один — невычисленная сумма
(define (mr-eval-pieces f pieces)
  (if (null? pieces)
      0
      (simplify (cons '+ (map (lambda (rs) (mi-multi-raw f rs)) pieces)))))

(define (mr-done? v) (not (and (pair? v) (contains-sym? v 'integrate))))

; попытка поменять порядок в двойном интеграле: значение или #f
(define (mr-try-swap f ro ri)
  (let ((pieces (try (mr-swap-pieces ro ri) (lambda (er) #f))))
    (if (not pieces)
        #f
        (let ((v (mr-eval-pieces f pieces)))
          (if (mr-done? v)
              (begin
                (record-condition '(fubini-swap) "integrate: порядок интегрирования изменён (Фубини), пределы пересчитаны")
                v)
              #f)))))

; ---- треугольник ----
(define (mr-line p q vo)   ; точки (outer inner)
  (simplify (list '+ (cadr p)
                  (list '* (/ (- (cadr q) (cadr p)) (- (car q) (car p))) (list '- vo (car p))))))

(define (mr-tri-pieces vo vi p1 p2 p3)
  (let* ((s (sort (list p1 p2 p3) (lambda (u w) (< (car u) (car w)))))
         (pa (nth s 0)) (pb (nth s 1)) (pc (nth s 2))
         (xa (car pa)) (xb (car pb)) (xc (car pc)))
    (if (= xa xc)
        '()
        (let* ((l13 (lambda (v) (mr-line pa pc v)))
               (yb13 (+ (cadr pa) (* (/ (- (cadr pc) (cadr pa)) (- xc xa)) (- xb xa)))))
          (if (= yb13 (cadr pb))
              '()
              (let* ((below (< (cadr pb) yb13))
                     (mk (lambda (x0 x1 other)
                           (list (list vo x0 x1)
                                 (if below (list vi other (l13 vo)) (list vi (l13 vo) other))))))
                (append (if (< xa xb) (list (mk xa xb (mr-line pa pb vo))) '())
                        (if (< xb xc) (list (mk xb xc (mr-line pb pc vo))) '()))))))))

(define (mr-check-point p)
  (if (and (pair? p) (= (length p) 2) (number? (car p)) (number? (cadr p)))
      p
      (error "triangle: вершины — пары чисел")))

(define (mr-region-plans reg)   ; (порядок₁ порядок₂): список кусков или #f
  (let ((k (car reg)))
    (cond ((equal? k 'rect)
           (list (list (list (cadr reg) (caddr reg))) (list (list (caddr reg) (cadr reg)))))
          ((equal? k 'between)
           (list (list (list (cadr reg) (caddr reg)))
                 (try (mr-swap-pieces (cadr reg) (caddr reg)) (lambda (er) #f))))
          ((equal? k 'triangle)
           (let* ((vs (cadr reg)) (ps (map mr-check-point (cddr reg))))
             (if (not (and (= (length vs) 2) (= (length ps) 3)))
                 (error "triangle: ожидается (triangle (x y) (x1 y1) (x2 y2) (x3 y3))")
                 (list (mr-tri-pieces (car vs) (cadr vs) (nth ps 0) (nth ps 1) (nth ps 2))
                       (mr-tri-pieces (cadr vs) (car vs)
                                      (reverse (nth ps 0)) (reverse (nth ps 1)) (reverse (nth ps 2)))))))
          (else (error "integrate_region: область — rect, between, triangle, disk или annulus")))))

; ---- круг и кольцо ----
(define (mr-polar-region f reg)
  (let* ((vs (cadr reg)) (c (caddr reg))
         (r1 (if (equal? (car reg) 'disk) 0 (nth reg 3)))
         (r2 (if (equal? (car reg) 'disk) (nth reg 3) (nth reg 4))))
    (if (not (and (= (length vs) 2) (= (length c) 2)))
        (error "integrate_region: ожидается (disk (x y) (cx cy) r) или (annulus (x y) (cx cy) r1 r2)")
        (integrate-change f
                          (list (list (car vs) (list '+ (car c) (list '* 'rho_ (list 'cos 'th_))))
                                (list (cadr vs) (list '+ (cadr c) (list '* 'rho_ (list 'sin 'th_)))))
                          (list (list 'rho_ r1 r2) (list 'th_ 0 (list '* 2 'pi)))))))

(define (integrate-region f reg)
  (if (or (not (pair? reg)) (not (symbol? (car reg))))
      (error "integrate_region: область — (rect …), (between …), (triangle …), (disk …) или (annulus …)")
      (if (member? (car reg) '(disk annulus))
          (mr-polar-region f reg)
          (let* ((plans (mr-region-plans reg))
                 (v1 (mr-eval-pieces f (car plans))))
            (if (mr-done? v1)
                v1
                (let ((v2 (if (cadr plans) (mr-eval-pieces f (cadr plans)) #f)))
                  (if (and v2 (mr-done? v2))
                      (begin
                        (record-condition '(fubini-swap) "integrate_region: порядок интегрирования изменён (Фубини), пределы пересчитаны")
                        v2)
                      v1)))))))

; ---- вердикт: exact / numeric / mismatch / unknown ----
(define (mr-verdict lhs rhs)
  (if (or (not (mr-done? lhs)) (not (mr-done? rhs)))
      'unknown
      (let ((d (mi-best (list '+ lhs (list '* -1 rhs)))))
        (cond ((equal? d 0) 'exact)
              ((mr-numval d) (if (< (abs (mr-numval d)) 1e-8) 'numeric 'mismatch))
              (else 'unknown)))))

(define (mr-dot-vec a b) (mi-dot a b))

; ∮ F·dr по кривой φ(t), t ∈ [a, b]
(define (mr-circulation F vars phi range)
  (let* ((t (car range))
         (g (mi-simp (mr-dot-vec (map (lambda (e) (subst (map2 list vars phi) e)) F)
                                 (map (lambda (p) (diff t p)) phi)))))
    (mi-multi-raw g (list range))))

; (green-check P Q (x y) phi (t a b) область) → (∮ P dx + Q dy, ∬ (Q_x − P_y) dA, вердикт)
(define (green-check P Q vars phi range reg)
  (begin
    (mi-check-ranges (list range))
    (if (not (and (= (length vars) 2) (= (length phi) 2) (= (length range) 3)))
        (error "green_check: ожидается green_check(P, Q, [x, y], [φ₁, φ₂], [t, a, b], область)")
        (let* ((lhs (mr-circulation (list P Q) vars phi range))
               (rhs (integrate-region (mi-simp (list '+ (diff (car vars) Q) (list '* -1 (diff (cadr vars) P)))) reg)))
          (list lhs rhs (mr-verdict lhs rhs))))))

(define (mr-cross a b)
  (list (list '+ (list '* (nth a 1) (nth b 2)) (list '* -1 (nth a 2) (nth b 1)))
        (list '+ (list '* (nth a 2) (nth b 0)) (list '* -1 (nth a 0) (nth b 2)))
        (list '+ (list '* (nth a 0) (nth b 1)) (list '* -1 (nth a 1) (nth b 0)))))

; ∬ G·(r_u × r_v) du dv — поток векторного поля G (в координатах vars) через поверхность r(u, v), ориентация — порядок u, v
(define (mr-flux G vars phi ru rv)
  (let* ((u (car ru)) (v (car rv))
         (n (mr-cross (map (lambda (p) (diff u p)) phi) (map (lambda (p) (diff v p)) phi)))
         (g (mi-simp (mr-dot-vec (map (lambda (e) (subst (map2 list vars phi) e)) G) n))))
    (mi-multi-raw g (list ru rv))))

(define (mr-curl F vars)
  (let ((x (nth vars 0)) (y (nth vars 1)) (z (nth vars 2)))
    (list (mi-simp (list '+ (diff y (nth F 2)) (list '* -1 (diff z (nth F 1)))))
          (mi-simp (list '+ (diff z (nth F 0)) (list '* -1 (diff x (nth F 2)))))
          (mi-simp (list '+ (diff x (nth F 1)) (list '* -1 (diff y (nth F 0))))))))

; (stokes-surface-check F (x y z) r (u a b) (v c d) phi (t a b)) → (∮_C F·dr, ∬ rot F·dS, вердикт)
; поверхность — r(u, v) на прямоугольнике параметров, C — её граница (ориентация согласована с нормалью r_u × r_v — на совести вызывающего)
(define (stokes-surface-check F vars r ru rv phi range)
  (begin
    (mi-check-ranges (list ru rv range))
    (if (not (and (= (length vars) 3) (= (length F) 3) (= (length r) 3) (= (length phi) 3)))
        (error "stokes_check: ожидается stokes_check(F, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d], [φ₁, φ₂, φ₃], [t, a, b])")
        (let* ((lhs (mr-circulation F vars phi range))
               (rhs (mr-flux (mr-curl F vars) vars r ru rv)))
          (list lhs rhs (mr-verdict lhs rhs))))))

; (gauss-check F (x y z) r (u a b) (v c d) объём): объём — (spherical R1 R2 R3) / (cylindrical …) / ((x a b) (y c d) (z e f))
(define (gauss-check F vars r ru rv vol)
  (begin
    (mi-check-ranges (list ru rv))
    (if (not (and (= (length vars) 3) (= (length F) 3) (= (length r) 3) (pair? vol)))
        (error "gauss_check: ожидается gauss_check(F, [x, y, z], [r₁, r₂, r₃], [u, a, b], [v, c, d], объём)")
        (let* ((dv (mi-simp (cons '+ (map (lambda (i) (diff (nth vars i) (nth F i))) (range 3)))))
               (lhs (mr-flux F vars r ru rv))
               (rhs (if (symbol? (car vol))
                        (integrate-change dv (car vol) (cdr vol))
                        (integrate-multi dv vol))))
          (list lhs rhs (mr-verdict lhs rhs))))))
