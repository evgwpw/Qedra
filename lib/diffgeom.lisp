; Шаг DG: дифференциальная геометрия кривых и поверхностей.
; Кривая r(t) — список компонент (ℝ² или ℝ³); поверхность r(u, v) — список из трёх компонент.
; Спецификация параметра: символ t (символьный ответ), (t t0) — значение в точке, (t a b) — символ с отрезком (для знаков корней).
; Корни норм — по множителям: √g² → |g|, знак доказывается объявлениями (assuming), отрезком и интервальной оценкой; иначе остаётся abs.
;
; Соглашения. Кривизна в ℝ² — со знаком: κ = (x′y″ − y′x″)/|r′|³ (положительна при повороте против часовой стрелки);
; в ℝ³ — |r′ × r″|/|r′|³ ≥ 0. Нормаль кривой в ℝ² — левая: N = (−T_y, T_x); в ℝ³ — главная: N = B × T.
; Нормаль поверхности n = r_u × r_v / |r_u × r_v|; L, M, N — проекции r_uu, r_uv, r_vv на n; H = (EN − 2FM + GL)/(2(EG − F²)) — знак по ориентации n.
(module diffgeom
  (export curve-speed curve-tangent curve-normal curve-binormal frenet-frame curvature torsion curvature-radius
          first-form second-form gauss-curvature mean-curvature principal-curvatures surface-normal graph-surface
          gauss-bonnet-check))

; ---------- упрощение ----------

(define (dg-simp e)
  (let ((s (simplify e)))
    (if (pair? s) (try (simplify (trigsimp s)) (lambda (er) s)) s)))

(define (dg-best e) (multiint::mi-best e))

(define (dg-zero? e) (and (number? e) (= e 0)))

(define (dg-all-zero? l) (every? dg-zero? l))

(define (dg-dot a b) (dg-best (apply + (map2 * a b))))

(define (dg-scale l s) (map (lambda (c) (dg-simp (* c s))) l))

(define (dg-cross a b)
  (list (dg-simp (- (* (nth a 1) (nth b 2)) (* (nth a 2) (nth b 1))))
        (dg-simp (- (* (nth a 2) (nth b 0)) (* (nth a 0) (nth b 2))))
        (dg-simp (- (* (nth a 0) (nth b 1)) (* (nth a 1) (nth b 0))))))

; ---------- знак: интервальная оценка для сумм с числовыми коэффициентами ----------

(define (dg-iv+ a b) (list (+ (car a) (car b)) (+ (cadr a) (cadr b))))

(define (dg-iv* a b)
  (let ((ps (list (* (car a) (car b)) (* (car a) (cadr b)) (* (cadr a) (car b)) (* (cadr a) (cadr b)))))
    (list (foldl min (car ps) (cdr ps)) (foldl max (car ps) (cdr ps)))))

(define (dg-ipow n x) (if (= n 0) 1 (* x (dg-ipow (- n 1) x))))

(define (dg-iv-pow a n)
  (let ((lo (dg-ipow n (car a))) (hi (dg-ipow n (cadr a))))
    (cond ((= (modulo n 2) 1) (list lo hi))
          ((and (<= (car a) 0) (>= (cadr a) 0)) (list 0 (max lo hi)))
          (else (list (min lo hi) (max lo hi))))))

; отрезок значений выражения или #f
(define (dg-ival e)
  (cond ((number? e) (list e e))
        ((not (pair? e)) #f)
        ((and (member? (car e) '(sin cos)) (= (length e) 2)) (list -1 1))
        ((member? (car e) '(+ *))
         (let ((ivs (map dg-ival (cdr e))))
           (if (any? not ivs)
               #f
               (foldl (if (equal? (car e) '+) dg-iv+ dg-iv*) (car ivs) (cdr ivs)))))
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (caddr e)) (> (caddr e) 0))
         (let ((a (dg-ival (cadr e)))) (if a (dg-iv-pow a (caddr e)) #f)))
        (else #f)))

; знак замкнутой константы (без свободных символов) по значению с запасом 1e-9; иначе unk
(define (dg-nsign e)
  (let ((v (try (eval-num e) (lambda (er) #f))))
    (cond ((not (number? v)) 'unk) ((> v 1e-9) 'pos) ((< v -1e-9) 'neg) (else 'unk))))

(define (dg-isign e)
  (let ((iv (dg-ival e)))
    (cond ((and iv (> (car iv) 0)) 'pos)
          ((and iv (< (cadr iv) 0)) 'neg)
          (else (dg-nsign e)))))

; |c| → ±c у замкнутых констант (после подстановки точки)
(define (dg-res-abs e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'abs) (= (length e) 2))
         (let* ((a (dg-res-abs (cadr e))) (s (dg-nsign a)))
           (cond ((equal? s 'pos) a) ((equal? s 'neg) (list '* -1 a)) (else (list 'abs a)))))
        (else (cons (car e) (map dg-res-abs (cdr e))))))

; |b| : multiint::mi-abs, затем интервальная оценка
(define (dg-fact? b env)
  (any? (lambda (r) (and (equal? (car r) 'dg-fact) (equal? (cadr r) (dg-simp b)))) env))

(define (dg-abs b env)
  (let ((a (multiint::mi-abs b env)))
    (if (and (pair? a) (equal? (car a) 'abs))
        (let ((s (if (dg-fact? b env) 'pos (dg-isign b))))
          (cond ((equal? s 'pos) b)
                ((equal? s 'neg) (dg-simp (list '* -1 b)))
                (else a)))
        a)))

; √e, e ≥ 0: по множителям; чётная степень g^(2k) → |g|^k; иначе корень остаётся
(define (dg-sqrt e env)
  (cond ((number? e) (simplify (list 'sqrt e)))
        ((and (pair? e) (equal? (car e) '*))
         (dg-simp (cons '* (map (lambda (a) (dg-sqrt a env)) (cdr e)))))
        ((and (pair? e) (equal? (car e) '^) (integer? (caddr e)) (= (modulo (caddr e) 2) 0))
         (dg-simp (list '^ (dg-abs (cadr e) env) (/ (caddr e) 2))))
        ((and (pair? e) (equal? (car e) '+))
         (let ((f (try (simplify (factor e)) (lambda (er) e))))
           (if (and (pair? f) (member? (car f) '(* ^)) (not (equal? f e)))
               (dg-sqrt f env)
               (simplify (list 'sqrt e)))))
        (else (simplify (list 'sqrt e)))))

; ---------- разбор спецификаций ----------

; → (символ точка-или-#f отрезок-или-#f)
(define (dg-parse s)
  (cond ((symbol? s) (list s #f #f))
        ((and (pair? s) (symbol? (car s)) (= (length s) 2)) (list (car s) (cadr s) #f))
        ((and (pair? s) (symbol? (car s)) (= (length s) 3)) (list (car s) #f s))
        (else (error "diffgeom: параметр — символ t, (t точка) или (t a b)"))))

(define (dg-check-curve r)
  (if (and (list? r) (member? (length r) '(2 3)))
      #t
      (error "diffgeom: кривая — вектор из 2 или 3 компонент")))

(define (dg-nth-diff t r k)
  (if (= k 0) r (dg-nth-diff t (map (lambda (c) (dg-simp (diff t c))) r) (- k 1))))

; значения в точке (если задана) — подстановкой и упрощением
(define (dg-at specs l)
  (foldl (lambda (acc sp)
           (if (cadr sp)
               (map (lambda (c) (dg-simp (subst (list (car sp) (cadr sp)) c))) acc)
               acc))
         l specs))

(define (dg-env specs) (filter (lambda (x) x) (map caddr specs)))

; результат: подставить точку (если задана), упростить, раскрыть |c| у замкнутых констант
(define (dg-fin specs e)
  (if (any? cadr specs)
      (dg-unsqrt (dg-simp (dg-res-abs (car (dg-at specs (list e))))))
      (dg-unsqrt e)))

; (√S)^(2m) → S^m (верно для любого S); результат упрощается заново
(define (dg-unsqrt e)
  (if (dg-has-sqrt-even? e) (dg-simp (dg-unsqrt1 e)) e))

(define (dg-sqrt-even-pow? e)
  (and (pair? e) (equal? (car e) '^) (= (length e) 3) (integer? (caddr e)) (= (modulo (caddr e) 2) 0)
       (pair? (cadr e)) (equal? (car (cadr e)) 'sqrt) (= (length (cadr e)) 2)))

(define (dg-has-sqrt-even? e)
  (and (pair? e) (or (dg-sqrt-even-pow? e) (any? dg-has-sqrt-even? (cdr e)))))

(define (dg-unsqrt1 e)
  (cond ((not (pair? e)) e)
        ((dg-sqrt-even-pow? e) (list '^ (dg-unsqrt1 (cadr (cadr e))) (/ (caddr e) 2)))
        (else (cons (car e) (map dg-unsqrt1 (cdr e))))))

(define (dg-fin-l specs l) (map (lambda (e) (dg-fin specs e)) l))

; ---------- кривые ----------

; символьные производные порядка 1..k; в заданной точке r′ = 0 — ошибка
(define (dg-curve-d r spec k)
  (let* ((sp (dg-parse spec)) (t (car sp)))
    (begin
      (dg-check-curve r)
      (if (and (cadr sp) (dg-all-zero? (dg-at (list sp) (dg-nth-diff t r 1))))
          (error "diffgeom: вырожденная точка, r′ = 0 (скорость равна нулю)")
          #t)
      (map (lambda (i) (dg-nth-diff t r (+ i 1))) (range k)))))

(define (dg-cspecs spec) (list (dg-parse spec)))

(define (dg-sp-of d1 env)
  (let ((s (dg-sqrt (dg-dot d1 d1) env)))
    (if (dg-zero? s)
        (error "diffgeom: вырожденная параметризация, r′ = 0 (скорость равна нулю)")
        s)))

; векторное произведение r′ × r″ (ℝ³) или скаляр x′y″ − y′x″ (ℝ²)
(define (dg-w r d1 d2)
  (if (= (length r) 3)
      (dg-cross d1 d2)
      (list (dg-simp (- (* (nth d1 0) (nth d2 1)) (* (nth d1 1) (nth d2 0)))))))

; |r′|
(define (curve-speed r spec)
  (let ((d (dg-curve-d r spec 1)) (specs (dg-cspecs spec)))
    (dg-fin specs (dg-sp-of (car d) (dg-env specs)))))

; единичная касательная T = r′/|r′|
(define (curve-tangent r spec)
  (let* ((specs (dg-cspecs spec)) (d (dg-curve-d r spec 1)) (sp (dg-sp-of (car d) (dg-env specs))))
    (dg-fin-l specs (dg-scale (car d) (dg-simp (list '^ sp -1))))))

; κ: в ℝ² со знаком, в ℝ³ неотрицательная
(define (curvature r spec)
  (let* ((specs (dg-cspecs spec)) (env (dg-env specs)) (d (dg-curve-d r spec 2))
         (sp (dg-sp-of (car d) env)) (w (dg-w r (car d) (cadr d))))
    (dg-fin specs
            (cond ((dg-all-zero? w) 0)
                  ((= (length r) 2) (dg-simp (list '* (car w) (list '^ sp -3))))
                  (else (dg-simp (list '* (dg-sqrt (dg-dot w w) env) (list '^ sp -3))))))))

; радиус кривизны 1/|κ|; прямая — ошибка
(define (curvature-radius r spec)
  (let ((k (curvature r spec)) (env (dg-env (dg-cspecs spec))))
    (if (dg-zero? k)
        (error "curvature_radius: кривизна равна нулю (прямая или точка спрямления) — радиус не определён")
        (dg-res-abs (dg-abs (dg-simp (list '^ k -1)) env)))))

; бинормаль B = (r′ × r″)/|r′ × r″|, только ℝ³
(define (curve-binormal r spec)
  (let* ((specs (dg-cspecs spec)) (env (dg-env specs)) (d (dg-curve-d r spec 2)))
    (if (not (= (length r) 3))
        (error "binormal: определена только для кривой в ℝ³")
        (let ((w (dg-w r (car d) (cadr d))))
          (if (or (dg-all-zero? w) (dg-all-zero? (dg-at specs w)))
              (error "binormal: r′ × r″ = 0 (прямая или точка спрямления) — бинормаль не определена")
              (dg-fin-l specs (dg-scale w (dg-simp (list '^ (dg-sqrt (dg-dot w w) env) -1)))))))))

; главная нормаль: ℝ³ — N = B × T; ℝ² — левая нормаль (−T_y, T_x)
(define (curve-normal r spec)
  (if (= (length r) 2)
      (let ((tg (curve-tangent r spec)))
        (list (dg-simp (list '* -1 (nth tg 1))) (nth tg 0)))
      (dg-cross (curve-binormal r spec) (curve-tangent r spec))))

; репер Френе: (T N B) в ℝ³, (T N) в ℝ²
(define (frenet-frame r spec)
  (if (= (length r) 2)
      (list (curve-tangent r spec) (curve-normal r spec))
      (let ((tg (curve-tangent r spec)) (b (curve-binormal r spec)))
        (list tg (dg-cross b tg) b))))

; кручение τ = (r′, r″, r‴)/|r′ × r″|², только ℝ³
(define (torsion r spec)
  (let ((d (dg-curve-d r spec 3)))
    (if (not (= (length r) 3))
        (error "torsion: определено только для кривой в ℝ³")
        (let* ((specs (dg-cspecs spec)) (w (dg-w r (car d) (cadr d))) (n2 (dg-dot w w)))
          (begin
            (dg-sp-of (car d) (dg-env specs))
            (if (or (dg-zero? n2) (dg-zero? (car (dg-at specs (list n2)))))
                (error "torsion: не определено — r′ × r″ = 0 (прямая или точка спрямления)")
                (dg-fin specs (dg-best (list '* (dg-dot w (caddr d)) (list '^ n2 -1))))))))))

; ---------- поверхности ----------

(define (dg-check-surface r)
  (if (and (list? r) (= (length r) 3))
      #t
      (error "diffgeom: поверхность — вектор из трёх компонент r(u, v)")))

; данные поверхности (символьные): (E F G Lt Mt Nt w2 env specs W), Lt = r_uu·W и т. д. (без деления на |W|);
; в заданной точке r_u × r_v = 0 — ошибка
(define (dg-surface r us vs)
  (let* ((su (dg-parse us)) (sv (dg-parse vs)) (u (car su)) (v (car sv)) (specs (list su sv)))
    (begin
      (dg-check-surface r)
      (let* ((ru (dg-nth-diff u r 1)) (rv (dg-nth-diff v r 1))
             (ruu (dg-nth-diff u r 2)) (rvv (dg-nth-diff v r 2))
             (ruv (map (lambda (c) (dg-simp (diff v c))) ru))
             (e (dg-dot ru ru)) (f (dg-dot ru rv)) (g (dg-dot rv rv))
             (w (dg-cross ru rv)))
        (if (or (dg-all-zero? w) (dg-all-zero? (dg-at specs w)))
            (error "diffgeom: вырожденная параметризация, r_u × r_v = 0 (EG − F² = 0)")
            (list e f g (dg-dot ruu w) (dg-dot ruv w) (dg-dot rvv w)
                  (dg-best (- (* e g) (* f f))) (dg-env specs) specs w))))))

(define (dg-nondeg-w2 s)
  (if (dg-zero? (nth s 6))
      (error "diffgeom: вырожденная параметризация, r_u × r_v = 0 (EG − F² = 0)")
      (nth s 6)))

; |r_u × r_v| = √(EG − F²)
(define (dg-sw s) (dg-sqrt (dg-nondeg-w2 s) (nth s 7)))

; первая квадратичная форма (E F G)
(define (first-form r u v)
  (let ((s (dg-surface r u v))) (dg-fin-l (nth s 8) (list (nth s 0) (nth s 1) (nth s 2)))))

; нормаль n = r_u × r_v/|r_u × r_v|
(define (surface-normal r u v)
  (let ((s (dg-surface r u v)))
    (dg-fin-l (nth s 8) (dg-scale (nth s 9) (dg-simp (list '^ (dg-sw s) -1))))))

; вторая квадратичная форма (L M N) относительно n = r_u × r_v/|…|
(define (second-form r u v)
  (let* ((s (dg-surface r u v)) (k (dg-simp (list '^ (dg-sw s) -1))))
    (dg-fin-l (nth s 8) (list (dg-simp (list '* (nth s 3) k)) (dg-simp (list '* (nth s 4) k)) (dg-simp (list '* (nth s 5) k))))))

; K = (LN − M²)/(EG − F²) = (L̃Ñ − M̃²)/(EG − F²)² — без корня, знак нормали не нужен
(define (gauss-curvature r u v)
  (let* ((s (dg-surface r u v)) (w2 (dg-nondeg-w2 s)))
    (dg-fin (nth s 8)
            (dg-best (list '* (list '+ (list '* (nth s 3) (nth s 5)) (list '* -1 (list '^ (nth s 4) 2)))
                           (list '^ w2 -2))))))

; числитель EÑ − 2FM̃ + GL̃
(define (dg-hnum s)
  (dg-best (list '+ (list '* (nth s 0) (nth s 5)) (list '* -2 (nth s 1) (nth s 4)) (list '* (nth s 2) (nth s 3)))))

; H = (EN − 2FM + GL)/(2(EG − F²)); знак — по ориентации n = r_u × r_v/|…|
(define (mean-curvature r u v)
  (let* ((s (dg-surface r u v)) (w2 (dg-nondeg-w2 s)) (wn (dg-sw s)))
    (dg-fin (nth s 8) (dg-best (list '* (dg-hnum s) (list '^ (dg-simp (list '* 2 w2 wn)) -1))))))

; главные кривизны: корни κ² − 2Hκ + K = 0, (κ₁ κ₂) = (H − √(H² − K), H + √(H² − K))
(define (principal-curvatures r u v)
  (let* ((s (dg-surface r u v)) (w2 (dg-nondeg-w2 s)) (wn (dg-sw s))
         (hn (dg-hnum s))
         (kn (list '+ (list '* (nth s 3) (nth s 5)) (list '* -1 (list '^ (nth s 4) 2))))
         (dn (dg-best (list '+ (list '^ hn 2) (list '* -4 w2 kn))))
         (den (dg-simp (list '* 2 w2 wn))))
    (if (and (number? dn) (< dn 0))
        (error "principal_curvatures: дискриминант отрицателен — ошибка параметризации")
        (let ((sq (dg-sqrt dn (nth s 7))) (inv (dg-simp (list '^ den -1))))
          (dg-fin-l (nth s 8)
                    (list (dg-best (list '* (list '+ hn (list '* -1 sq)) inv))
                          (dg-best (list '* (list '+ hn sq) inv))))))))

; z = f(x, y) как поверхность (x, y, f)
(define (graph-surface f x y) (list x y f))

; ---------- Гаусс–Бонне: ∬ K dA = 2πχ для замкнутой поверхности ----------

; (gauss-bonnet-check r (u a b) (v c d) χ) → (вердикт ∬K dA 2πχ): exact | numeric | mismatch | unknown
; поверхность должна быть замкнутой и накрываться параметризацией один раз (иначе вердикт mismatch — не ошибка теоремы)
; необязательные выражения после χ — утверждения «> 0 на всей области» (знак под корнем, например R + a cos v при R > a); пишутся в условия
(define (gauss-bonnet-check r ru rv chi &rest facts)
  (begin
    (if (not (and (pair? ru) (pair? rv) (= (length ru) 3) (= (length rv) 3) (symbol? (car ru)) (symbol? (car rv))))
        (error "gauss_bonnet_check: ожидается gauss_bonnet_check(r, [u, a, b], [v, c, d], χ)")
        #t)
    (if (not (integer? chi))
        (error "gauss_bonnet_check: χ — целое число")
        #t)
    (let* ((s (dg-surface r (car ru) (car rv)))
           (w2 (dg-nondeg-w2 s))
           (env (append (list ru rv) (map (lambda (f) (list 'dg-fact (dg-simp f))) facts)))
           (k (dg-best (list '* (list '+ (list '* (nth s 3) (nth s 5)) (list '* -1 (list '^ (nth s 4) 2)))
                             (list '^ w2 -2))))
           (integrand (dg-best (list '* k (dg-sqrt w2 env))))
           (lhs (integrate-multi integrand (list ru rv)))
           (rhs (dg-simp (list '* 2 chi 'pi))))
      (begin
        (for-each (lambda (f) (record-condition (list 'positive f) "gauss_bonnet_check: принято, что выражение положительно на области"))
                  facts)
        (list (multiint::mr-verdict lhs rhs) lhs rhs)))))
