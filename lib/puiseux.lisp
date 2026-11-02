; puiseux.lisp — ряды Пюизё (Ньютон–Пюизё) для алгебраических кривых (21m A2.1)
;
; Теорема Ньютона–Пюизё: корни F(x, y) = 0 (F ∈ ℚ[x, y]) в окрестности x = 0 — конечные
; наборы рядов y = Σ cᵢ x^{i/q} с cᵢ из конечного расширения ℚ.
;
; Алгоритм (Walker, гл. IV):
;   1. F(0, y) ≠ 0 — ветви регулярны: ряд Тейлора неопределёнными коэффициентами (q = 1).
;   2. Иначе: многоугольник Ньютона → ребро с наклоном v/h (НОД(h, v) = 1, h > 0) →
;      характеристический многочлен φ(T) ребра → корень c над текущим полем K (ℚ или ℚ(α)) →
;      подстановка x = ξ^h, y = ξ^v·(c + z) → F₁(ξ, z) с F₁(0, z) = 0 → рекурсия.
;   Ветвь накапливается: y = a₀(x) + x^μ·(c + …).
;
; Представление ветви: (q terms) — terms: список (коэффициент-выражение, рациональный показатель),
;   упорядоченный по возрастанию показателя; y = Σ cᵢ x^{eᵢ}, знаменатель всех eᵢ делит q.
;   Коэффициенты — выражения через радикалы/root-of (alg->expr из algnum).
;
; Точность: рациональная арифметика и ℚ(α) (algnum); float — только вложение поля.
;
; Публичный интерфейс: newton-polygon, puiseux, puiseux-check, puiseux-terms, puiseux-at.
; Все внутренние имена — с префиксом px-.

(module puiseux
  (export newton-polygon puiseux puiseux-check puiseux-terms puiseux-at px-cached
          puiseux-rational algebraic-series algebraic-series->expr
          algebraic-series-coeff algebraic-series?))

; ---------- маленькие утилиты ----------

(define (px-drop l k)
  (if (or (<= k 0) (null? l)) l (px-drop (cdr l) (- k 1))))

(define (px-make-list n v)
  (if (<= n 0) '() (cons v (px-make-list (- n 1) v))))

(define (px-list-set l k v)
  (append (take l k) (list v) (px-drop l (+ k 1))))

; тождественный нуль после упрощения
(define (px-zero-expr? c) (equal? (simplify c) 0))

; ---------- многоугольник Ньютона ----------

; векторное произведение (a→b)×(a→c): > 0 — c слева от ab
(define (px-cross a b c)
  (let ((bax (- (nth b 0) (nth a 0))) (bay (- (nth b 1) (nth a 1)))
        (cax (- (nth c 0) (nth a 0))) (cay (- (nth c 1) (nth a 1))))
    (- (* bax cay) (* bay cax))))

; нижняя ломаная выпуклой оболочки (цепочка Эндрю), вершины по возрастанию x
(define (px-lower-hull pts)
  (let* ((pts (sort pts (lambda (a b)
                          (if (= (nth a 0) (nth b 0))
                              (< (nth a 1) (nth b 1))
                              (< (nth a 0) (nth b 0))))))
         (uniq (let loop ((l pts) (acc '()))
                 (cond ((null? l) (reverse acc))
                       ((and (pair? acc) (= (nth (car l) 0) (nth (car acc) 0)))
                        (loop (cdr l) acc))
                       (else (loop (cdr l) (cons (car l) acc)))))))
    (if (= (length uniq) 1) (list (car uniq))
        (let loop ((rest (cdr uniq)) (h (list (car uniq))))
          (if (null? rest) h
              (let push ((p (car rest)) (stk h))
                (if (and (>= (length stk) 2)
                         (<= (px-cross (nth stk 1) (nth stk 0) p) 0))
                    (push p (cdr stk))
                    (loop (cdr rest) (cons p stk)))))))))

; F → список мономов (c vx vy): численный коэффициент и целые степени по x и y
(define (px-monomials F x y)
  (let ((cs (coefficients F y)))
    (let loop ((i 0) (l cs) (acc '()))
      (if (null? l) acc
          (let* ((a (car l))
                 (acs (if (px-zero-expr? a) '() (coefficients a x))))
            (loop (+ i 1) (cdr l)
                  (let iloop ((k 0) (cl acs) (acc2 acc))
                    (if (null? cl) acc2
                        (iloop (+ k 1) (cdr cl)
                               (if (px-zero-expr? (car cl)) acc2
                                   (cons (list (simplify (car cl)) k i) acc2)))))))))))

; опорные точки (vx vy)
(define (px-support-points F x y)
  (map (lambda (m) (list (nth m 1) (nth m 2))) (px-monomials F x y)))

; (newton-polygon F x y) → список рёбер нижней ломаной, по возрастанию vx:
;   (vx0 vy0 vx1 vy1 h v): ребро из (vx0,vy0) в (vx1,vy1); подстановка ветви x = ξ^h, y = ξ^v,
;   где h·vx + v·vy одинаково на ребре ⇒ v/h = −Δvx/Δvy — рациональный показатель ветви
;   y ~ c·x^{v/h}; h > 0, v > 0, НОД(h, v) = 1 (для нижней ломаной с F(0,0)=0).
(define (newton-polygon F x y)
  (let ((hull (reverse (px-lower-hull (px-support-points F x y)))))
    (if (< (length hull) 2) '()
        (let loop ((l hull) (acc '()))
          (if (null? (cdr l)) (reverse acc)
              (let* ((p0 (car l)) (p1 (cadr l))
                     (dvx (- (nth p1 0) (nth p0 0)))
                     (dvy (- (nth p1 1) (nth p0 1))))
                (if (= dvy 0) (loop (cdr l) acc)
                    (let* ((g (gcd dvx (abs dvy)))
                           (hh (quotient (abs dvy) g))
                           (vv (quotient dvx g))
                           (vv (if (< dvy 0) vv (- vv))))
                      (loop (cdr l)
                            (cons (list (nth p0 0) (nth p0 1) (nth p1 0) (nth p1 1)
                                        hh vv)
                                  acc))))))))))

; характеристический многочлен ребра (коэффициенты по возрастанию):
; φ(T) = Σ_{мономы на ребре} c·T^{vy} — из баланса h·vx + v·vy = m на ребре:
; после x = ξ^h, y = ξ^v·T каждый моном ребра даёт ξ^m·c·T^{vy}; φ(T) = 0 — уравнение на c.
(define (px-edge-charpoly F x y edge)
  (let* ((vx0 (nth edge 0)) (vy0 (nth edge 1)) (vx1 (nth edge 2))
         (hh (nth edge 4)) (vh (nth edge 5))
         (m (+ (* hh vx0) (* vh vy0)))
         (on (filter (lambda (mm)
                       (= (+ (* hh (nth mm 1)) (* vh (nth mm 2))) m))
                     (px-monomials F x y)))
         (deg (foldl (lambda (acc mm) (max acc (nth mm 2))) 0 on)))
    (if (null? on) (error "px-edge-charpoly: ребро без мономов")
        (let loop ((l on) (cs (px-make-list (+ deg 1) 0)))
          (if (null? l)
              (let trim ((l2 (reverse cs)))
                (if (and (pair? l2) (= (car l2) 0)) (trim (cdr l2)) (reverse l2)))
              (let* ((mm (car l)) (vy (nth mm 2)))
                (loop (cdr l)
                      (px-list-set cs vy (+ (nth cs vy) (nth mm 0))))))))))

; =====================================================================
; арифметика коэффициентов: K = #f (ℚ) или algnum-поле; элемент — число либо alg-элемент
; =====================================================================

(define (px-el-zero? K a) (if K (alg-zero? K a) (= a 0)))
(define (px-el-zero K) (if K '() 0))
(define (px-el-one K) (if K (alg-elt K '(1)) 1))
(define (px-el-add K a b) (if K (alg-add K a b) (simplify (+ a b))))
(define (px-el-neg K a) (if K (alg-negate K a) (simplify (- a))))
(define (px-el-sub K a b) (if K (alg-sub K a b) (simplify (- a b))))
(define (px-el-mul K a b) (if K (alg-mul K a b) (simplify (* a b))))
(define (px-el-div K a b) (if K (alg-div K a b) (simplify (/ a b))))
(define (px-el-pow K a n)
  (if K (alg-pow K a n)
      (if (= n 0) 1 (let loop ((k 1) (r a)) (if (= k n) r (loop (+ k 1) (simplify (* r a))))))))
(define (px-el-from-rat K q) (if K (alg-elt K (list q)) q))

; ---------- одномерные многочлены над K (по возрастанию) ----------

(define (px-poly-trim p K)
  (let loop ((l (reverse p)))
    (if (and (pair? l) (px-el-zero? K (car l))) (loop (cdr l)) (reverse l))))

(define (px-pad-to K p n)
  (append p (px-make-list (- n (length p)) (px-el-zero K))))

(define (px-poly-add K p q)
  (let ((n (max (length p) (length q))))
    (px-poly-trim
     (map2 (lambda (a b) (px-el-add K a b)) (px-pad-to K p n) (px-pad-to K q n)) K)))

(define (px-poly-neg K p) (map (lambda (a) (px-el-neg K a)) p))
(define (px-poly-sub K p q) (px-poly-add K p (px-poly-neg K q)))

(define (px-poly-mul K p q)
  (if (or (null? p) (null? q)) '()
      (let ((acc (px-make-list (- (+ (length p) (length q) 1) 1) (px-el-zero K))))
        (let loop ((i 0) (pl p) (acc acc))
          (if (null? pl) (px-poly-trim acc K)
              (loop (+ i 1) (cdr pl)
                    (let loop2 ((j 0) (ql q) (acc2 acc))
                      (if (null? ql) acc2
                          (loop2 (+ j 1) (cdr ql)
                                 (px-list-set acc2 (+ i j)
                                   (px-el-add K (nth acc2 (+ i j))
                                              (px-el-mul K (car pl) (car ql)))))))))))))

; монизация
(define (px-monicize K p)
  (let* ((p (px-poly-trim p K))
         (lc (last p))
         (inv (px-el-div K (px-el-one K) lc)))
    (map (lambda (a) (px-el-mul K a inv)) p)))

; многочлен из чисел → выражение от v
(define (px-nums->expr cs v)
  (simplify (cons '+ (map2 (lambda (c k) (if (= k 0) c (list '* c (list '^ v k))))
                           cs (range (length cs))))))

; элемент K → выражение; вложение вещественное — alg->expr (точно, радикалы);
; комплексное — subst t := emb (приближение double через %i; различает сопряжённые ветви,
; puiseux-check проверяет такие ветви численно через eval-num)
(define (px-el->expr K a)
  (if (not K) a
      (if (px-embed-real? K)
          (alg->expr K a)
          (simplify (subst (list (px-field-var K) (alg-field-embed K))
                           (algnum::ag-poly-expr K a))))))

; переменная минмногочлена поля K — первый подходящий символ из типичных имён
(define (px-field-var K)
  (let ((m (alg-field-minpoly K)))
    (let loop ((cands '(t u w s z x)))
      (if (null? cands) (error "px-field-var: переменная m не найдена")
          (if (contains-sym? m (car cands)) (car cands) (loop (cdr cands)))))))


; вложение поля вещественно? (число/algebraic без %i — да; комплексное приближение — нет)
(define (px-embed-real? K)
  (let ((e (alg-field-embed K)))
    (or (and (number? e) (not (px-has-i? e)))
        (and (alg? e) (not (px-has-i? (alg-field-embed K)))))))

(define (px-has-i? e)
  (and (list? e) (contains-sym? e '%i)))




; ---------- факторизация и корни над K ----------

; факторизация p над K → список (g k); g — список коэффициентов-элементов по возрастанию
(define (px-factor-pairs K p)
  (if K
      (cdr (alg-factor K p 'T))
      (let ((fl (cdr (factor-list (px-nums->expr p 'T)))))
        (map (lambda (fk)
               (list (coefficients (nth fk 0) 'T) (nth fk 1)))
             fl))))

; корни p над K → список (K' c); на каждый неприводимый множитель степени ≥ 2 — один корень
; в расширении (сопряжённые не раскрываются на этом уровне; их даёт puiseux через кратности).
; deg 1: корень −g0. ℚ: расширение alg-field; K=ℚ(α): resultant + alg-primitive.
(define (px-poly-roots K p)
  (if (null? p) (error "px-poly-roots: нулевой многочлен")
      (let* ((mono (px-monicize K p))
             (facs (px-factor-pairs K mono)))
        (let loop ((fs facs) (acc '()))
          (if (null? fs) acc
              (let* ((g (car (car fs)))
                     (d (- (length g) 1)))
                (loop (cdr fs)
                      (cond ((= d 0) acc)
                            ((= d 1) (cons (list K (px-el-div K (px-el-neg K (nth g 0)) (nth g 1))) acc))
                            (else (append (px-root-via-extension K g) acc))))))))))

; все корни неприводимого g (deg ≥ 2) над K в расширении K' ⊇ K.
; ℚ-случай: alg-field требует моничный целый m ⇒ замена t = u/M (M = НОК знаменателей):
; ψ(u) = M^d·g_monic(u/M) — моничный целый; корень g = u/M. ВСЕ корни — через все вложения поля:
; alg-field m t emb с emb из real-roots (точные algebraic) и nroots (комплексные приближения double);
; элемент (0 … 1/M) при каждом вложении — соответствующий корень.
(define (px-root-via-extension K g)
  (if (not K)
      (let* ((res (px-int-scale g))
             (m (px-nums->expr (nth res 0) 't)) (M (nth res 1))
             (embs (px-all-embeddings m 't)))
        (map (lambda (e)
               (list (alg-field (simplify m) 't e)
                     (alg-elt (alg-field (simplify m) 't e)
                              (list 0 (simplify (list '/ 1 M))))))
             embs))
      (let* ((m1 (alg-field-minpoly K))
             (m2 (px-nums->expr (map (lambda (a) (px-el->expr K a)) g) 't))
             (pr (alg-primitive m1 m2)))
        (if (not pr) (error "px-root-via-extension: alg-primitive не нашёл поле")
            (list (list (nth pr 0) (nth pr 2)))))))

; все вложения моничного целого неприводимого m: real-roots + комплексные.
; A2.2: квадратичные (deg 2) с отрицательным дискриминантом — ТОЧНЫЕ радикальные вложения
; (−p ± √(p²−4q))/2 (комплексные через %i·√|D|): subst с ними сокращается точно (ζ³ = 1 и т.п.),
; регулярный хвост считается точно (деление нормализуется alg-simplify). Deg ≥ 3 — double (nroots).
(define (px-all-embeddings m t)
  (let ((rr (real-roots m t)) (nr (nroots m t)))
    (append (if (null? rr) '() rr)
            (let ((cplx (filter (lambda (z) (not (px-real-root? z rr))) nr)))
              (if (and (null? rr) (= (length cplx) 2) (px-quadratic? m t))
                  (px-quadratic-embeddings m t)
                  cplx)))))

; m — квадратичный по t (степень ровно 2, t³ нет)?
(define (px-quadratic? m t)
  (and (= (px-deg-in m t) 2)))

; степень expr по переменной t (старшая)
(define (px-deg-in e t)
  (let ((cs (coefficients e t)))
    (if (null? cs) 0 (- (length cs) 1))))

; точные комплексные корни квадратичного m = t² + p·t + q (D = p²−4q < 0):
; (−p ± √D)/2 — радикальные expr с %i, различают сопряжённые
(define (px-quadratic-embeddings m t)
  (let* ((p (coeff m t 1)) (q (coeff m t 0))
         (D (simplify (list '- (list '^ p 2) (list '* 4 q)))))
    (list (simplify (list '/ (list '+ (list '* -1 p) (list '^ D 1/2)) 2))
          (simplify (list '/ (list '+ (list '* -1 p) (list '* -1 (list '^ D 1/2))) 2)))))

; корень из nroots совпадает (приближённо) с одним из real-roots?
(define (px-real-root? z rr)
  (let ((zv (px-num-val z)))
    (any? (lambda (r) (< (abs (- zv (px-num-val r))) 1e-7)) rr)))

; приближённое числовое значение (algebraic / expr от %i / number)
(define (px-num-val v)
  (let ((nv (eval-num v)))
    (if (number? nv) nv (px-num-real (simplify nv)))))

; вещественная часть числа/expr от %i
(define (px-num-real v)
  (cond ((number? v) v)
        ((and (list? v) (equal? (car v) '+))
         (let loop ((ts (cdr v)) (acc 0))
           (cond ((null? ts) acc)
                 ((or (equal? (car ts) '%i)
                      (and (list? (car ts)) (equal? (car (car ts)) '*)
                           (equal? (last (car ts)) '%i)))
                  (loop (cdr ts) acc))
                 (else (loop (cdr ts) (+ acc (car ts)))))))
        (else 0)))

; g (рац. cs по возрастанию, любой старший) → (m M): монизируем, затем t = u/M:
; m = M^d·g_monic(u/M) — моничный целый (по u, по возрастанию); корень g = u/M
(define (px-int-scale g)
  (let* ((lc (last g))
         (inv (simplify (list '/ 1 lc)))
         (gm (map (lambda (c) (simplify (list '* inv c))) g))
         (d (- (length gm) 1))
         (M (foldl (lambda (a c) (px-lcm a (px-denom c))) 1 gm)))
    (list (map2 (lambda (c k)
                  (simplify (list '* (px-pow-int M (- d k)) c)))
                gm (range (length gm)))
          M)))

; знаменатель рационального числа: наименьшее D ≥ 1 с D·c ∈ ℤ
; (раньше был inv-тест: 1/(8/27) = 27/8 не целое → ложная ошибка)
(define (px-denom c)
  (cond ((integer? c) 1)
        ((equal? (type-of c) 'rational)
         (let loop ((D 2))
           (cond ((> D 100000) (error "px-denom: слишком большой знаменатель"))
                 ((integer? (simplify (list '* D c))) D)
                 (else (loop (+ D 1))))))
        (else (error "px-denom: не рациональное число"))))

(define (px-lcm a b) (quotient (* a b) (gcd a b)))

(define (px-pow-int a n)
  (if (<= n 0) 1 (let loop ((k 1) (r a)) (if (= k n) r (loop (+ k 1) (* r a))))))



; =====================================================================
; ядро: цикл Ньютона–Пюизё
; =====================================================================

; подстановка в F (выражение от x и z): x := ξ^h, z := ξ^v·(c + w);
; результат — многочлен от (ξ, w); затем делим на наименьшую степень ξ (выносим общий множитель,
; т.к. F(0,0)=0 гарантирует неотрицательную валюацию)
(define (px-substitute F x z h v c K' xi w)
  (let* ((F1 (simplify (subst (list x (list '^ xi h)) F)))
         (F2 (simplify (expand (subst (list z (list '* (list '^ xi v)
                                              (list '+ (px-el->expr K' c) w))) F1))))
         (val (px-valuation F2 xi)))
    (if (or (not val) (= val 0)) F2
        (px-shift-laurent F2 xi val))))

; вынести ξ^val из Лорановского выражения: перестроить по коэффициентам
; (coefficients понимает ξ с отрицательными степенями; собираем многочлен со сдвигом −val)
(define (px-shift-laurent F xi val)
  (let* ((cs (coefficients F xi)))
    (simplify (expand
               (cons '+ (map2 (lambda (c k) (list '* c (list '^ xi (+ k (- val)))))
                              cs (range (length cs))))))))

; валюация выражения по xi (младшая степень, может быть отрицательной); #f если 0/константа≠0
(define (px-valuation e xi)
  (if (px-zero-expr? e) 0
      (let ((cs (coefficients e xi)))
        (if (null? cs) 0
            (let loop ((l cs) (k 0))
              (cond ((null? l) #f)
                    ((px-zero-expr? (car l)) (loop (cdr l) (+ k 1)))
                    (else k)))))))


; регулярность: F(0, w) = a·w (линейно по w при ξ = 0)


; деление выражений с радикалами/%i: simplify; если застряло (^ X -1) — рационализация
; знаменателя в форме a+b·R, R² ∈ ℚ (один квадратичный «базис», напр. √d·%i): inv = (a−bR)/(a²−b²R²).
; Результат остаётся в той же канонической форме (a'+b'R), что и ζ-термы — check сокращает точно.
; Сложные случаи — alg-simplify (denest) как запасной путь, дальше — как есть.
(define (px-div-expr a b)
  (let ((r (simplify (list '/ a b))))
    (if (px-has-neg-pow? r)
        (let ((rr (px-rationalize r)))
          (if rr rr
              (try (simplify (alg-simplify r)) (lambda (err) r))))
        r)))

; r содержит (^ X -1) при X = a+bR (R²∈ℚ, a,b∈ℚ) → заменить деление рационализацией; #f если не разобралось
(define (px-rationalize r)
  (let* ((neg (px-find-neg-pow r)))
    (if (not neg) #f
        (let* ((X (nth neg 1))
               (ab (px-lin-rad-coeffs X)))
          (and ab
               (let* ((a (nth ab 0)) (bb (nth ab 1)) (R (nth ab 2))
                      (q (nth ab 3))
                      (den (simplify (list '- (list '^ a 2) (list '* (list '^ bb 2) q))))
                      (inv (list '/ (list '- a (list '* bb R)) den)))
                 (simplify (px-replace-subtree r neg inv))))))))

; первый узел (^ X -1) в expr (поиск в глубину); #f если нет
(define (px-find-neg-pow e)
  (cond ((not (list? e)) #f)
        ((and (equal? (car e) '^) (number? (nth e 2)) (< (nth e 2) 0)) e)
        (else (let loop ((l (cdr e)))
                (cond ((null? l) #f)
                      ((px-find-neg-pow (car l)) (px-find-neg-pow (car l)))
                      (else (loop (cdr l))))))))

; заменить поддерево old на new (первое вхождение)
(define (px-replace-subtree e old new)
  (cond ((equal? e old) new)
        ((not (list? e)) e)
        (else (map (lambda (u) (px-replace-subtree u old new)) e))))

; X = a + b·R, R — произведение нерациональных множителей (√d, %i), R² ∈ ℚ:
; → (a b R q) или #f. Термы X обязаны быть рациональными либо c·R с ОДНИМ и тем же R.
(define (px-lin-rad-coeffs X)
  (let* ((Xs (simplify (expand X)))
         (terms (if (and (list? Xs) (equal? (car Xs) '+)) (cdr Xs) (list Xs))))
    (let loop ((ts terms) (a 0) (bb #f) (R #f) (q #f))
      (cond ((null? ts) (and bb (list a bb R q)))
            ((number? (car ts)) (loop (cdr ts) (simplify (list '+ a (car ts))) bb R q))
            ((and (list? (car ts)) (equal? (car (car ts)) '*))
             (let* ((fs (cdr (car ts)))
                    (cs (filter (lambda (f) (number? f)) fs))
                    (rs (filter (lambda (f) (not (number? f))) fs))
                    (c (if (null? cs) 1 (simplify (cons '* cs))))
                    (rr (if (= (length rs) 1) (car rs) (simplify (cons '* rs)))))
               (if (or (not (number? c)) (null? rs)) #f
                   (let ((q2 (simplify (list '^ rr 2))))
                     (if (not (number? q2)) #f
                         (if (and R (not (equal? R rr))) #f
                             (loop (cdr ts) a
                                   (if bb (simplify (list '+ bb c)) c) rr q2)))))))
            ((and (list? (car ts)) (equal? (car (car ts)) '^))
             ; одиночный радикал-терм (* 1 R): пропустим через тот же путь
             (let* ((rr (car ts)) (q2 (simplify (list '^ rr 2))))
               (if (not (number? q2)) #f
                   (if (and R (not (equal? R rr))) #f
                       (loop (cdr ts) a
                             (if bb (simplify (list '+ bb 1)) 1) rr q2)))))
            (else #f)))))

; в expr есть (^ … -1) (несокращённое деление)?
(define (px-has-neg-pow? e)
  (and (list? e)
       (try (let loop ((l e))
              (cond ((not (list? l)) #f)
                    ((and (equal? (car l) '^)
                          (number? (nth l 2)) (< (nth l 2) 0)) #t)
                    (else (any? loop l))))
            (lambda (err) #f))))

; регулярный случай: неявная функция (ряд Ньютона). Инвариант: F(ξ, z) регулярна
; (F(ξ,0) ≠ 0 при ξ≠0, F_z(0,0) ≠ 0 — но коэффициент при z может иметь порядок vb ≥ 0 по ξ).
; Координата z связана с исходной рядом z = P(ξ) + ξ^shift·z_cur; шаг:
;   A(ξ) = F(ξ,0), B(ξ) = (∂F/∂z)(ξ,0); va = порядок A, vb = порядок B, va > vb;
;   член d·ξ^k, k = va−vb, d = −fa/fb — его АБСОЛЮТНАЯ позиция в ряду z: shift + k
;   (ошибка A2.1: позиция считалась как k относительно текущей координаты — показатели съезжали);
;   подстановка z := d·ξ^k + ξ^k·z₁, shift' = shift + k.
; Возврат: коэффициенты ряда z(ξ) при ξ¹ … ξⁿ (нули включены).
; --- Шаг A5.P: инкрементальный ряд ---
; F хранится набором серий A_j(ξ) при z^j (индекс списка = степень ξ, длина n+1).
; Шаг Ньютона z := ξ^k(d + z₁) пересчитывает серии по биному:
;   B_i = Σ_{j≥i} A_j·ξ^{k·j}·C(j,i)·d^{j−i},
; без subst/expand всего F на каждом члене. Старшие степени ξ не влияют на младшие,
; поэтому серия усекается до n+1.

(define (px-s-zero? a) (or (equal? a 0) (equal? (simplify a) 0)))

(define (px-s-add a b)
  (cond ((px-s-zero? a) b)
        ((px-s-zero? b) a)
        ((and (number? a) (number? b)) (+ a b))
        (else (simplify (expand (list '+ a b))))))

(define (px-s-mul a b)
  (cond ((px-s-zero? a) 0)
        ((px-s-zero? b) 0)
        ((and (number? a) (number? b)) (* a b))
        ((equal? a 1) b)
        ((equal? b 1) a)
        (else (simplify (expand (list '* a b))))))

(define (px-s-pow a j)
  (cond ((= j 0) 1)
        ((= j 1) a)
        (else (px-s-mul a (px-s-pow a (- j 1))))))

(define (px-binom n k)
  (if (or (< k 0) (> k n)) 0
      (let loop ((i 0) (r 1))
        (if (= i k) r (loop (+ i 1) (quotient (* r (- n i)) (+ i 1)))))))

(define (px-ser-pad s N)
  (append s (px-make-list (- (+ N 1) (length s)) 0)))

(define (px-ser-add a b N)
  (map2 (lambda (x y) (px-s-add x y)) (px-ser-pad a N) (px-ser-pad b N)))

(define (px-ser-scale s c N)
  (if (px-s-zero? c)
      (px-make-list (+ N 1) 0)
      (map (lambda (x) (px-s-mul x c)) (px-ser-pad s N))))

(define (px-ser-shift s k N)
  (if (>= k (+ N 1))
      (px-make-list (+ N 1) 0)
      (take (append (px-make-list k 0) (px-ser-pad s N)) (+ N 1))))

; порядок серии (индекс первого ненулевого коэффициента); #f — нулевая
(define (px-ser-ord s)
  (let loop ((l s) (k 0))
    (cond ((null? l) #f)
          ((px-s-zero? (car l)) (loop (cdr l) (+ k 1)))
          (else k))))

; z := ξ^k(d + z₁) в наборе серий cs (A_0 … A_m)
(define (px-z-rebase cs k d N)
  (let ((m (- (length cs) 1)))
    (let loop ((i 0) (acc '()))
      (if (> i m) (reverse acc)
          (let inner ((j i) (s (px-make-list (+ N 1) 0)))
            (if (> j m) (loop (+ i 1) (cons s acc))
                (let* ((c (px-binom j i))
                       (dj (px-s-pow d (- j i)))
                       (term (px-ser-shift (nth cs j) (* k j) N)))
                  (inner (+ j 1)
                         (px-ser-add s (px-ser-scale term (px-s-mul c dj) N) N)))))))))

(define (px-regular-series F xi z n)
  (let* ((cs0 (map (lambda (c) (coefficients (expand c) xi))
                   (coefficients (expand F) z))))
    (if (< (length cs0) 2)
        '()
        (let loop ((acc '()) (cs cs0) (shift 0))
          (if (>= (length acc) n) acc
              (let* ((A (nth cs 0)) (B (nth cs 1))
                     (va (px-ser-ord A)) (vb (px-ser-ord B))
                     (fa (if va (nth A va) #f))
                     (fb (if vb (nth B vb) #f)))
                (if (or (not va) (not vb) (not fa) (not fb)
                        (px-s-zero? fa) (px-s-zero? fb)) acc
                    (let* ((k (- va vb))
                           (pos (+ shift k))
                           (d (px-div-expr (list '* -1 fa) fb)))
                      (if (or (< k 1) (> pos n) (< pos (length acc))) acc
                          (loop (append acc (px-make-list (- pos 1 (length acc)) 0) (list d))
                                (px-z-rebase cs k d n)
                                (+ shift k)))))))))))

; порядок выражения по xi (валюация, младшая степень); #f если тождественный нуль/константа≠0
(define (px-ord e xi)
  (if (px-zero-expr? e) #f
      (let ((cs (coefficients e xi)))
        (let loop ((l cs) (k 0))
          (cond ((null? l) #f)
                ((px-zero-expr? (car l)) (loop (cdr l) (+ k 1)))
                (else k))))))

; свободный по ξ член коэффициента при z¹: (∂F/∂z)(0, 0); свободный по ξ член коэффициента при z¹: (∂F/∂z)(0, 0)


; =====================================================================
; ветви: рекурсия Ньютона–Пюизё
; =====================================================================

; шаг 1: если F(0, y) ≠ 0 — регулярные ветви (корни F(0,y) не равны 0 одновременно с F_y);
;   общий случай ниже покрывает и это: F(0, y) ≠ 0 → все ветви регулярны в каждой точке y₀ = корне F(0,y).
; Реализация: раскрываем F по y вокруг каждого корня y₀ многочлена F(0, y) (в ℚ или расширении).

; F(0, y) — многочлен от y (коэффициенты — константы); корни с кратностями:
; → список (K' y₀ k): y₀ — элемент K' (расширение), k — кратность в F(0,y)
(define (px-roots-at-zero F x y)
  (let* ((F0 (simplify (subst (list x 0) F)))
         (cs (coefficients F0 y)))
    (if (every? px-zero-expr? cs)
        (error "px-roots-at-zero: F(0,y) ≡ 0 — кривая содержит компоненту x = 0")
        (px-poly-roots-with-mult #f cs))))

; все корни с кратностями: факторизация + для неприводимого g deg≥2 — все deg g корней
; (генерирующая даёт один; остальные получаем... в классическом режиме раскрываем через
; кратность: если g неприводим deg d с кратностью k, то d ветвей с q = d·… — на этом уровне
; возвращаем (K' β k) один раз, а puiseux учтёт d сопряжённых ветвей умножением на d.
; ВНИМАНИЕ: для корректного разложения по всем сопряжённым классический алгоритм требует
; перебора всех корней φ; здесь реализуем через вложения: пробуем все корни factor-list
; для ℚ; для ℚ(α) — только генерирующая (Duval-группировка — A2.2).
(define (px-poly-roots-with-mult K cs)
  (let* ((mono (px-monicize K cs))
         (facs (px-factor-pairs K mono)))
    (let loop ((fs facs) (acc '()))
      (if (null? fs)
          acc
          (let* ((fk (car fs))
                 (g (car fk))
                 (k (nth fk 1))
                 (d (- (length g) 1)))
            (loop (cdr fs)
                  (cond ((= d 0) acc)
                        ((= d 1)
                         (cons (list K (px-el-div K (px-el-neg K (nth g 0)) (nth g 1)) k) acc))
                        ((not K)
                         (let* ((res (px-int-scale g))
                                (m (px-nums->expr (nth res 0) 't))
                                (M (nth res 1))
                                (embs (px-all-embeddings m 't)))
                           (append
                            (map (lambda (e)
                                   (let ((L (alg-field (simplify m) 't e)))
                                     (list L (alg-elt L (list 0 (simplify (list '/ 1 M)))) k)))
                                 embs)
                            acc)))
                        (else
                          (let* ((m1 (alg-field-minpoly K))
                                 (m2 (px-nums->expr (map (lambda (a) (px-el->expr K a)) g) 't))
                                 (pr (alg-primitive m1 m2)))
                            (if (not pr)
                                (error "px-poly-roots-with-mult: alg-primitive не нашёл поле")
                                (cons (list (nth pr 0) (nth pr 2) k d) acc)))))))))))





; ---------- цикл Ньютона вокруг точки (0, y₀) ----------
; вход: G — F после сдвига y := y₀ + z (выражение от x и z, G(0,0) = 0);
; K — текущее поле; terms — накопленные члены ((элемент показатель)); q — знаменатель;
; mu — минимальный показатель оставшейся части (y = A(x) + x^mu·(остальное)).
; Схема шага: G регулярна (G(0,z) = a·z, a≠0) → ряд Тейлора; иначе: многоугольник G →
; первое ребро (h, v) → φ(T) → корень c (расширение K') → x = ξ^h, z = ξ^v(c+z₁) → рекурсия.



; регулярность в нуле: G(0, z) = a·z, a ≠ 0
(define (px-regular-at-zero? G x z)
  (let* ((G0 (simplify (subst (list x 0) G))))
    (and (not (px-zero-expr? G0))
         (let ((cs (coefficients G0 z)))
           (and (>= (length cs) 2)
                (px-zero-expr? (car cs))
                (not (px-zero-expr? (nth cs 1))))))))

; ceil рационального
(define (px-ceil r)
  (cond ((and (number? r) (>= r 0)) (ceiling r))
        ((number? r) (ceiling r))
        (else 6)))

; члены ряда Тейлора: ds при ξ¹…; показатели mu + i/q
(define (px-taylor-terms ds mu q)
  (let loop ((l ds) (i 1) (acc '()))
    (if (null? l) (reverse acc)
        (loop (cdr l) (+ i 1)
              (if (equal? (simplify (car l)) 0) acc
                  (cons (list (car l) (simplify (list '+ mu (list '/ i q)))) acc))))))

; продолжение после корня c ребра (h, v):
; z = ξ^v·(c + z₁), x = ξ^h ⇒ y = A(x) + x^{mu + v/h}·(c + z₁(x^{1/h}))
; рекурсия по G₁(ξ, z₁) с пересчётом: mu' = (mu + v/h) − mu… аккуратно: члены регистрируются
; напрямую в терминах x: новый член (c, mu + v/h); хвост — по ξ = x^{1/h}: показатель члена
; (d_i, xi^i) ↦ x^{(mu + v/h) + i/(q·h)}. Поэтому рекурсию ведём в координатах ξ.



; =====================================================================
; публичный API
; =====================================================================

; (puiseux F x y n) → список ветвей (q (c1 e1) (c2 e2) …), y = Σ cᵢ x^{eᵢ};
; eᵢ — рациональные со знаменателем q; коэффициенты — выражения (радикалы/root-of).
; Порядок: бесквадратность по y (радикал факторизации), корни F(0, y) (с кратностями),
; для каждого — сдвиг y := y₀ + z и полный перебор ветвей Ньютона.
; puiseux проверяет себя: каждая ветвь обязана пройти puiseux-check, иначе ошибка.
(define (puiseux F x y n)
  (let* ((F (simplify F))
         (sqf (px-sqfree-y F))
         (roots (px-roots-at-zero sqf x y)))
    (let loop ((rs roots) (acc '()))
      (if (null? rs)
          (px-verify-branches F x y (reverse acc) n)
          (let* ((r (car rs))
                 (K (nth r 0)) (y0 (nth r 1)))
            (loop (cdr rs)
                  (append acc
                          (px-branches-around sqf x y K y0 n))))))))

; самопроверка: puiseux проверяет каждую ветвь перед возвратом
(define (px-verify-branches F x y brs n)
  (let loop ((l brs))
    (if (null? l) brs
        (if (puiseux-check F x y (car l) n)
            (loop (cdr l))
            (error "puiseux: ветвь не прошла самопроверку (подстановка не обнуляет ряд)")))))

; элемент → выражение (K = #f — число уже выражение)
(define (px-term->expr K a)
  (if (not K) a (px-el->expr K a)))

; бесквадратность по y: радикал факторизации (произведение неприводимых по одному разу)
(define (px-sqfree-y F)
  (let ((fl (cdr (factor-list F))))
    (if (null? fl) F
        (simplify (cons '* (map (lambda (fk) (nth fk 0)) fl))))))

; ветви вокруг точки y₀ (в z-координатах): список (q terms); terms — (коэф-выражение показатель).
; Все коэффициенты — ВЫРАЖЕНИЯ (элементы полей конвертируются в точках создания через px-el->expr);
; поле K используется внутри вычислений, наружу не выдаётся.
(define (px-branches-around F x y K y0 n)
  (let* ((z (gensym "pxz"))
         (y0e (px-el->expr K y0))
         (G (simplify (expand (subst (list y (list '+ y0e z)) F))))
         (brs (px-all-branches G x z K n 0)))
    (map (lambda (br)
           (list (nth br 0)
                 (if (px-el-zero? K y0)
                     (nth br 1)
                     (cons (list y0e 0) (nth br 1)))))
         brs)))


; полный перебор ветвей: на каждом шаге Ньютона ветвимся на все корни характеристического φ.
; Возврат: список (q terms); terms — (коэф-выражение показатель), коэффициенты — выражения.
(define (px-all-branches G x z K n depth)
  (if (> depth 30) '()
      (if (px-regular-at-zero? G x z)
          (let* ((ds (px-regular-series G x z (px-ceil n))))
            (list (list 1 (px-taylor-terms ds 0 1))))
          (let* ((edges (newton-polygon G x z)))
            (if (null? edges) (list (list 1 '()))
                (let* ((edge (car edges))
                       (phi (px-edge-charpoly G x z edge)))
                  (if (null? phi) (list (list 1 '()))
                      (let ((rcs (px-poly-roots K phi)))
                        (apply append
                               (map (lambda (rc)
                                      (px-branches-after-root G x z K n edge rc depth))
                                    rcs))))))))))

; шаг: корень c ребра (h, v) — подстановка x = ξ^h, z = ξ^v(c + z₁) и рекурсия;
; пересчёт показателей: μ' = v/h, знаменатель q' = q·h (на верхнем уровне q=1);
; терм ряда — (px-el->expr K2 c, μ'); хвост: терм (d, i) по ξ ↦ показатель x = μ' + i/h.
; Ряд в координатах ξ нужен до порядка n·h (порядок по x — n); лишние термы (показатель > n) отбрасываем.
(define (px-branches-after-root G x z K n edge rc depth)
  (let* ((K2 (nth rc 0)) (c (nth rc 1))
         (hh (nth edge 4)) (vh (nth edge 5))
         (xi (gensym "pxi")) (z1 (gensym "pxz1"))
         (G1 (px-substitute G x z hh vh c K2 xi z1))
         (mu2 (simplify (list '/ vh hh)))
         (q2 hh)
         (term2 (if (or (px-el-zero? K2 c) (> mu2 n)) '()
                    (list (list (px-el->expr K2 c) mu2)))))
    (map (lambda (br)
           (list (* q2 (nth br 0))
                 (append term2
                         (filter (lambda (tm) (<= (nth tm 1) n))
                                 (map (lambda (tm)
                                        (list (nth tm 0)
                                              (simplify (list '+ mu2 (list '/ (nth tm 1) hh)))))
                                      (nth br 1))))))
         (px-all-branches G1 xi z1 K2 (* n hh) (+ depth 1)))))
; ---------- проверка и утилиты ----------

; (puiseux-terms br) → список (c e)
(define (puiseux-terms br) (nth br 1))

; (puiseux-rational F x y n) → список групп Дюваля: ((q термы) кратность):
; сопряжённые над ℚ((x)) ветви — одной группой (неприводимый фактор F над ℚ((x))).
; Реализация: полный перебор ветвей (puiseux, A2.1) + склейка по сопряжённости:
; ветви y₁, y₂ в одной группе ⟺ одинаковые q и показатели, и y₂ получается из y₁
; подстановкой ξ ↦ ζ^k·ξ (ζ = e^{2πi/q}, действие на показатели m_j: c_j ↦ ζ^{k·m_j}·c_j)
; и/или сопряжением поля коэффициентов (√d ↦ −√d). Проверка — численная (eval-num при
; ξ = 1/2, допуск 1e-6): эвристика, но с сильно различающимися рядами ложных склеек нет;
; раскрытие группы = подстановка ζ^k и сопряжения (проверяется puiseux-ветвями).
; Представитель группы — первая ветвь; кратность — число ветвей в группе.
(define (puiseux-rational F x y n)
  (let* ((bs (puiseux F x y n)))
    (let loop ((rest bs) (groups '()))
      (if (null? rest)
          (reverse groups)
          (let* ((b (car rest))
                 (mates (filter (lambda (b2) (px-conjugate-branches? b b2)) (cdr rest)))
                 (others (filter (lambda (b2) (not (px-conjugate-branches? b b2))) (cdr rest))))
            (loop others (cons (list b (+ 1 (length mates))) groups)))))))

; ветви сопряжены над ℚ((x))? (одинаковые q и показатели; точная проверка:
; ∃k < q, ∃τ ∈ {id, сопряжение радикалов}: ∀j: c2_j = ζ_q^{k·m_j}·τ(c1_j), m_j = q·e_j — целые;
; равенство — через alg-simplify (каноническая форма в поле радикалов, denest);
; ζ_q выражается радикалами для q ∈ {2, 3, 4, 6} — прочие q не склеиваются)
(define (px-conjugate-branches? b1 b2)
  (let ((q1 (nth b1 0)) (q2 (nth b2 0))
        (t1 (nth b1 1)) (t2 (nth b2 1)))
    (and (= q1 q2)
         (equal? (map (lambda (tm) (nth tm 1)) t1)
                 (map (lambda (tm) (nth tm 1)) t2))
         (px-conj-terms? q1 t1 t2))))

; ∃k, τ: все термы соответствуют c2_j = ζ^{k·m_j}·τ(c1_j)
(define (px-conj-terms? q t1 t2)
  (let ((zeta (px-root-of-unity q)))
    (and zeta
         (let k-loop ((k 0))
           (cond ((= k q) #f)
                 ((or (px-conj-terms-k tau-id zeta k q t1 t2)
                      (and (px-has-radical? (cons 'list (append (map car t1) (map car t2))))
                           (px-conj-terms-k px-conj-expr zeta k q t1 t2)))
                  #t)
                 (else (k-loop (+ k 1))))))))

; все j: c2_j = ζ^{k·m_j}·τ(c1_j)? Сравнение ТОЧНОЕ через разбор квадратичных форм
; a+b·R (px-lin-rad-coeffs, R² ∈ ℚ — единый радикальный базис, напр. √d·%i);
; ζ-степени раскрываются expand'ом; fallback — численное равенство (eval-num, 1e-7)
(define (px-conj-terms-k tau zeta k q t1 t2)
  (let loop ((a t1) (b t2))
    (cond ((null? a) #t)
          ((null? b) #f)
          (else (let* ((c1 (tau (nth (car a) 0)))
                       (c2 (nth (car b) 0))
                       (m (* q (nth (car a) 1)))
                       (zk (if (= m 0) 1 (simplify (expand (list '^ (px-zeta-k zeta k) m))))))
                  (if (not (integer? m)) #f
                      (let ((ok (px-rad-equal? c2 (list '* zk c1))))
                        (if ok (loop (cdr a) (cdr b)) #f))))))))

; точное равенство expr = expr в квадратичном поле a+b·R (R²∈ℚ): разбор обеих сторон
; (после expand) и сравнение (a b); fallback — численно (|u−v| < 1e-7)
(define (px-rad-equal? u v)
  (let ((d (simplify (expand (list '- u v)))))
    (or (equal? d 0)
        (let ((ab (px-lin-rad-coeffs d)))
          (if (and ab (equal? (nth ab 0) 0) (equal? (nth ab 1) 0))
              #t
              (let ((nu (px-num-val u)) (nv (px-num-val v)))
                (and (number? nu) (number? nv)
                     (< (abs (- nu nv)) 1e-7)
                     (< (abs (- (px-num-real (simplify u)) (px-num-real (simplify v)))) 1e-7))))))))


; (algebraic-series F x y a n [ветвь]) → объект puiseux-series: усечённый ряд Пюизё
; выбранной ветви алгебраической функции F(x, y) = 0 в точке x = a.
; a = 0: ветви Пюизё (дробные показатели; формат series целочисленный — свой объект);
; a ≠ 0: сдвиг x := x + a и ветви в 0 (обычно регулярные, q = 1).
; ветвь — номер (1-based, по порядку puiseux) или ветвь-объект (q terms); по умолчанию 1.
; Поля объекта: (x a q terms); сборка в выражение — (algebraic-series->expr s),
; терм — (algebraic-series-coeff s k) (1-based).
(define (algebraic-series F x y a n &rest opts)
  (let* ((br (if (null? opts) 1 (car opts)))
         (Fa (if (equal? a 0) F (simplify (expand (subst (list x (list '+ a x)) F)))))
         (bs (puiseux Fa x y n))
         (b (if (number? br) (nth bs (- br 1)) br)))
    (if (not b) (error "algebraic-series: ветвь не найдена")
        (make-object 'puiseux-series x a (nth b 0) (nth b 1)))))

; объект → выражение Σ cᵢ (x − a)^{eᵢ} (eᵢ = m/q от точки a)
(define (algebraic-series->expr s)
  (let* ((x (object-ref s 0)) (a (object-ref s 1)) (q (object-ref s 2)) (ts (object-ref s 3)))
    (simplify (expand
               (cons '+ (map (lambda (tm)
                               (list '* (nth tm 0)
                                     (list '^ (list '- x a) (list '/ (* q (nth tm 1)) q))))
                             ts))))))

; коэффициент терма k (1-based) или #f
(define (algebraic-series-coeff s k)
  (let* ((ts (object-ref s 3)))
    (if (and (>= k 1) (<= k (length ts)))
        (nth (nth ts (- k 1)) 0)
        #f)))

; проверка типа
(define (algebraic-series? s)
  (and (object? s) (equal? (object-type s) 'puiseux-series)))


; ζ_q как выражение через радикалы (q ∈ {1, 2, 3, 4, 6}); #f — не выражается
(define (px-root-of-unity q)
  (case q
    ((1) 1)
    ((2) -1)
    ((3) '(/ (+ -1 (^ -3 1/2)) 2))
    ((4) '%i)
    ((6) '(/ (+ 1 (^ -3 1/2)) 2))
    (else #f)))

; ζ^k (по таблице первообразного корня)
(define (px-zeta-k zeta k)
  (if (= k 0) 1
      (if (= k 1) zeta
          (simplify (list '^ zeta k)))))

(define (tau-id e) e)

; сопряжение радикалов: (^ d 1/2) ↦ −(^ d 1/2), %i ↦ −%i (рекурсивно)
(define (px-conj-expr e)
  (cond ((not (list? e)) e)
        ((equal? e '%i) (list '* -1 '%i))
        ((and (equal? (car e) '^) (equal? (nth e 2) 1/2))
         (list '* -1 e))
        (else (map px-conj-expr e))))

; в структуре есть радикал или %i?
(define (px-has-radical? e)
  (cond ((not (list? e)) (equal? e '%i))
        ((equal? e '%i) #t)
        ((and (equal? (car e) '^) (equal? (nth e 2) 1/2)) #t)
        (else (any? px-has-radical? (cdr e)))))



; (puiseux-check F x y br n) → #t/#f: подстановка x = s^q, y = Σ cᵢ s^{eᵢ·q};
; все коэффициенты по s до порядка n·q (включительно) должны обращаться в нуль.
; Рациональные — точно (simplify = 0); радикалы/root-of/%i — численно (eval-num, |c| < 1e-8).
; Независимая проверка (не использует внутренности puiseux).
(define (puiseux-check F x y br n)
  (let* ((q (nth br 0)) (ts (nth br 1))
         (s (gensym "pxs"))
         (yexpr (simplify (expand (cons '+ (map (lambda (tm)
                                                  (list '* (nth tm 0)
                                                        (list '^ s (* q (nth tm 1)))))
                                                ts)))))
         (Fx (simplify (expand (subst (list x (list '^ s q)) F))))
         (Fsub (simplify (expand (subst (list y yexpr) Fx))))
         (cs (coefficients Fsub s))
         ; замечание ревью: остаток O(s^{qn}) не доказывает верность ряда до x^n — ошибка δ·x^e в ветви даёт
         ; остаток порядка e + ord F_y; поэтому граница = q·n + ord_s F_y(ветвь) + 1
         (Fy (simplify (expand (subst (list y yexpr) (simplify (expand (subst (list x (list '^ s q)) (diff y F))))))))
         (vy (px-first-nonzero (coefficients Fy s) 0))
         (limit (and vy (+ 1 (* q n) vy))))
    (and limit
     (let check ((l cs) (i 0))
      (cond ((null? l) #t)
            ((>= i limit) #t)
            ((px-coef-zero? (car l)) (check (cdr l) (+ i 1)))
            (else #f))))))

; коэффициент — ноль: рациональное — точно (simplify = 0); радикалы/%i — точная нормальная форма
; в поле радикалов (alg-simplify из denest, A2.2); численный fallback (|c| < 1e-8) — только при сбое
(define (px-coef-zero? c)
  (or (px-zero-expr? c)
      (let ((cv (simplify c)))
        (and (not (and (number? cv) (not (equal? (type-of cv) 'float))))
             (or (equal? (try (alg-simplify cv) (lambda (err) #f)) 0)
                 (let ((v (px-expr-abs cv))) (and (number? v) (< v 1e-8))))))))

; номер первого ненулевого коэффициента или #f
(define (px-first-nonzero l i)
  (cond ((null? l) #f)
        ((px-coef-zero? (car l)) (px-first-nonzero (cdr l) (+ i 1)))
        (else i)))

; |коэффициент|: точно-ноль — 0; expr от %i/float — численно (разбор re/im); прочее — eval-num
(define (px-expr-abs c)
  (let ((cv (simplify c)))
    (cond ((equal? cv 0) 0)
          ((number? cv) (abs cv))
          (else (let ((v (eval-num cv)))
                  (if (number? v) (abs v)
                      (algnum::ag-num-abs v)))))))

; (puiseux-at br x v) — приближённое значение ветви в точке x = v (float, прикидка)
(define (puiseux-at br x v)
  (error "puiseux-at: численная оценка — используйте подстановку и numeric-инструменты хоста"))

; ---------- Шаг A5.P: кэш ветвей по F ----------
; puiseux даёт n+1 член на ветвь, и первые члены не зависят от n:
; храним самый длинный результат и усекаем его для меньших n (рост без пересчёта с нуля).

(define px-cache '())

(define (px-cache-find F lst)
  (cond ((null? lst) #f)
        ((equal? (car (car lst)) F) (car lst))
        (else (px-cache-find F (cdr lst)))))

(define (px-trunc-branches brs n)
  (map (lambda (b) (list (car b) (take (cadr b) (+ n 1)))) brs))

; (px-cached F x y n) — то же, что (puiseux F x y n), но с кэшем по F
(define (px-cached F x y n)
  (let ((e (px-cache-find F px-cache)))
    (cond
      ((and e (>= (cadr e) n)) (px-trunc-branches (caddr e) n))
      (else
       (let ((brs (puiseux F x y n)))
         (if (pair? brs)
             (begin
               (set! px-cache
                     (take (cons (list F n brs)
                                 (if e (filter (lambda (z) (not (equal? (car z) F))) px-cache) px-cache))
                           8))
               brs)
             brs))))))
