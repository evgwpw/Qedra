; field.lisp — Шаг FLD.1: «алгоритм один раз для любого поля» (в духе доменов Axiom).
;
; ПОЛЕ — вектор #(имя char zero one add sub neg mul inv zero? equal? from-rat ->expr pth-root):
;   add/sub/mul — (f a b), neg/inv/zero?/->expr — (f a), equal? — (f a b), from-rat — рациональное → элемент
;   (в GF(p) — по модулю p), pth-root — корень p-й степени (только char p > 0; иначе #f).
; Конструкторы оборачивают готовые модули: field-Q, field-algnum (algnum), field-gf / field-gfpn (gf), field-ratfun (ℚ(x)).
; Многочлены над полем — плотные списки элементов, младшая степень первой, ноль — (): fp-*.
; Матрицы — списки строк: fm-*. Вектор — список элементов.
;
; Сертификаты: fp-divmod (a = q·b + r, deg r < deg b), fp-egcd (s·a + t·b = g, g | a, g | b), fp-gcd (g | a, g | b,
; a/g и b/g взаимно просты — тождество Безу), fp-sqfree (lc·∏ gᵢ^i = f, gᵢ бесквадратны и взаимно просты);
; fm-nullspace (A·v = 0, число = n − rank, независимы), fm-solve (A·x = b + ядро), fm-inverse (A·B = B·A = I).
; Проверки доступны отдельно (…-check возвращают #t/#f) — на них тесты подкладывают подделки.
; fm-det сертификата не имеет (проверка — только косвенная: det ≠ 0 ⇔ rank = n).
; Ограничение: в характеристике p fp-sqfree требует pth-root поля (есть у field-gf и field-gfpn).

(module field
  (export field-Q field-algnum field-gf field-gfpn field-ratfun
          field-name field-char field-zero field-one field-add field-sub field-neg field-mul field-div field-inv
          field-zero? field-equal? field-from-rational field->expr field-pow
          fp-trim fp-add fp-sub fp-neg fp-mul fp-scale fp-deg fp-lc fp-monic fp-divmod fp-gcd fp-egcd fp-deriv fp-sqfree
          fp-eval fp-compose fp-equal?
          fp-divmod-check fp-gcd-check fp-egcd-check fp-sqfree-check
          fm-mul fm-mat-vec fm-identity fm-rref fm-rank fm-nullspace fm-det fm-solve fm-inverse
          fm-nullspace-check fm-solve-check fm-inverse-check))

; ---------- запись поля ----------

(define (fld-make name ch zero one add sub neg mul inv zero? equal from-rat ->expr proot)
  (vector name ch zero one add sub neg mul inv zero? equal from-rat ->expr proot))

(define (field-name F) (vref F 0))
(define (field-char F) (vref F 1))
(define (field-zero F) (vref F 2))
(define (field-one F) (vref F 3))
(define (field-add F a b) ((vref F 4) a b))
(define (field-sub F a b) ((vref F 5) a b))
(define (field-neg F a) ((vref F 6) a))
(define (field-mul F a b) ((vref F 7) a b))
(define (field-zero? F a) ((vref F 9) a))
(define (field-equal? F a b) ((vref F 10) a b))
(define (field->expr F a) ((vref F 12) a))

; обратный: на нуле — ошибка
(define (field-inv F a)
  (if (field-zero? F a)
      (error "field-inv: деление на нуль в поле" (field-name F))
      ((vref F 8) a)))
(define (field-div F a b) (field-mul F a (field-inv F b)))

; рациональное (целое или дробь, не float) → элемент поля
(define (field-from-rational F r)
  (if (and (number? r) (not (equal? (type-of r) 'float)))
      ((vref F 11) r)
      (error "field-from-rational: ожидается целое или рациональное число")))

; a^k, k ≥ 0 (бинарное возведение)
(define (field-pow F a k)
  (cond ((< k 0) (error "field-pow: показатель должен быть ≥ 0"))
        ((= k 0) (field-one F))
        ((= (modulo k 2) 0) (let ((h (field-pow F a (quotient k 2)))) (field-mul F h h)))
        (else (field-mul F a (field-pow F a (- k 1))))))

(define (fld-proot F)
  (let ((r (vref F 13)))
    (if r r (error "fp-sqfree: у поля нет корня p-й степени (характеристика"  (field-char F) ")"))))

; ---------- конструкторы ----------

; ℚ
(define (field-Q)
  (fld-make "Q" 0 0 1
            (lambda (a b) (+ a b)) (lambda (a b) (- a b)) (lambda (a) (- a))
            (lambda (a b) (* a b)) (lambda (a) (/ 1 a))
            (lambda (a) (equal? a 0)) (lambda (a b) (= a b))
            (lambda (r) r) (lambda (a) a) #f))

; ℚ(α) из (alg-field m t)
(define (field-algnum F)
  (fld-make "Q(alg)" 0 '() '(1)
            (lambda (a b) (alg-add F a b)) (lambda (a b) (alg-sub F a b)) (lambda (a) (alg-negate F a))
            (lambda (a b) (alg-mul F a b)) (lambda (a) (alg-inv F a))
            (lambda (a) (null? a)) (lambda (a b) (null? (alg-sub F a b)))
            (lambda (r) (if (= r 0) '() (list r)))
            (lambda (a) (alg->expr F a)) #f))

; рациональное → элемент GF(p) (целое по модулю p)
(define (fld-rat-mod r p)
  (let ((d (denom r)))
    (if (= (modulo d p) 0)
        (error "field-from-rational: знаменатель делится на характеристику" p)
        (modulo (* (numer r) (invmod d p)) p))))

; GF(p), p простое: элементы — целые 0 … p−1
(define (field-gf p)
  (if (not (and (integer? p) (> p 1) (prime? p)))
      (error "field-gf: p должно быть простым")
      (fld-make (string-append "GF(" (to-string p) ")") p 0 1
                (lambda (a b) (modulo (+ a b) p)) (lambda (a b) (modulo (- a b) p)) (lambda (a) (modulo (- a) p))
                (lambda (a b) (modulo (* a b) p)) (lambda (a) (invmod a p))
                (lambda (a) (= a 0)) (lambda (a b) (= a b))
                (lambda (r) (fld-rat-mod r p)) (lambda (a) a)
                (lambda (a) a))))

; GF(pⁿ) из (gf-field p m t): элементы — списки коэффициентов
(define (field-gfpn F)
  (let ((p (vref F 0)) (n (vref F 2)) (v (vref F 3)))
    (fld-make (string-append "GF(" (to-string p) "^" (to-string n) ")") p '() '(1)
              (lambda (a b) (gf+ F a b)) (lambda (a b) (gf- F a b)) (lambda (a) (gf- F '() a))
              (lambda (a b) (gf* F a b)) (lambda (a) (gf-inv F a))
              (lambda (a) (null? a)) (lambda (a b) (equal? a b))
              (lambda (r) (gf-elt F (list (fld-rat-mod r p))))
              (lambda (a) (simplify (cons '+ (map2 (lambda (c i) (list '* c (list '^ v i))) a (range (length a))))))
              (lambda (a) (if (null? a) a (gf-power F a (^ p (- n 1))))))))

; ℚ(x): элементы — выражения (нормализуются together); равенство — нулевая разность
(define (field-ratfun x)
  (let ((norm (lambda (e) (together e))))
    (fld-make (string-append "Q(" (to-string x) ")") 0 0 1
              (lambda (a b) (norm (+ a b))) (lambda (a b) (norm (- a b))) (lambda (a) (norm (- a)))
              (lambda (a b) (norm (* a b))) (lambda (a) (norm (/ 1 a)))
              (lambda (a) (equal? (norm a) 0)) (lambda (a b) (equal? (norm (- a b)) 0))
              (lambda (r) r) (lambda (a) (norm a)) #f)))

; ---------- многочлены ----------

(define (fp-trim-rev F r) ; r — старшие первыми
  (if (and (pair? r) (field-zero? F (car r))) (fp-trim-rev F (cdr r)) r))
(define (fp-trim F a) (reverse (fp-trim-rev F (reverse a))))
(define (fp-deg a) (- (length a) 1))   ; для обрезанного; ноль → −1
(define (fp-lc a) (last a))

(define (fp-zip F f a b)
  (cond ((and (null? a) (null? b)) '())
        ((null? a) (cons (f (field-zero F) (car b)) (fp-zip F f a (cdr b))))
        ((null? b) (cons (f (car a) (field-zero F)) (fp-zip F f (cdr a) b)))
        (else (cons (f (car a) (car b)) (fp-zip F f (cdr a) (cdr b))))))

(define (fp-add F a b) (fp-trim F (fp-zip F (lambda (x y) (field-add F x y)) a b)))
(define (fp-sub F a b) (fp-trim F (fp-zip F (lambda (x y) (field-sub F x y)) a b)))
(define (fp-neg F a) (map (lambda (x) (field-neg F x)) a))
(define (fp-scale F c a)
  (if (field-zero? F c) '() (fp-trim F (map (lambda (x) (field-mul F c x)) a))))
(define (fp-equal? F a b) (null? (fp-sub F a b)))

(define (fp-mul F a b)
  (if (or (null? a) (null? b)) '()
      (let loop ((as a) (shift '()) (acc '()))
        (if (null? as) acc
            (loop (cdr as) (cons (field-zero F) shift)
                  (fp-add F acc (append shift (fp-scale F (car as) b))))))))

(define (fp-monic F a)
  (if (null? a) a (fp-scale F (field-inv F (fp-lc a)) a)))

; деление с остатком: старшие первыми, фиксированная длина остатка
(define (fp-divmod-raw F a b)
  (let* ((da (fp-deg a)) (db (fp-deg b)))
    (if (< da db) (list '() a)
        (let ((ib (field-inv F (fp-lc b)))
              (bt (cdr (reverse b))))   ; b без старшего, старшие первыми
          (let loop ((r (reverse a)) (k (+ (- da db) 1)) (q '()))
            (if (= k 0)
                (list (fp-trim F q) (fp-trim F (reverse r)))
                (let* ((c (field-mul F (car r) ib))
                       (tl (cdr r))
                       (sub (map (lambda (x) (field-mul F c x)) bt))
                       (r2 (append (fp-zip F (lambda (x y) (field-sub F x y)) (take tl (length sub)) sub)
                                   (drop tl (length sub)))))
                  (loop r2 (- k 1) (cons c q)))))))))

(define (fp-divmod-check F a b q r)
  (and (fp-equal? F a (fp-add F (fp-mul F q b) r))
       (< (fp-deg r) (fp-deg b))
       (equal? r (fp-trim F r))))

(define (fp-divmod F a b)
  (let ((b (fp-trim F b)) (a (fp-trim F a)))
    (if (null? b) (error "fp-divmod: деление на нулевой многочлен")
        (let ((qr (fp-divmod-raw F a b)))
          (if (fp-divmod-check F a b (car qr) (cadr qr))
              qr
              (error "fp-divmod: сертификат a = q·b + r не прошёл"))))))

(define (fp-quo F a b) (car (fp-divmod-raw F a b)))
(define (fp-rem F a b) (cadr (fp-divmod-raw F a b)))

; расширенный Евклид без проверки: (g s t), g монический (или ноль)
(define (fp-egcd-raw F a b)
  (let loop ((r0 (fp-trim F a)) (r1 (fp-trim F b)) (s0 (list (field-one F))) (s1 '()) (t0 '()) (t1 (list (field-one F))))
    (if (null? r1)
        (if (null? r0) (list '() '() '())
            (let ((u (field-inv F (fp-lc r0))))
              (list (fp-scale F u r0) (fp-scale F u s0) (fp-scale F u t0))))
        (let* ((qr (fp-divmod-raw F r0 r1)) (q (car qr)))
          (loop r1 (cadr qr) s1 (fp-sub F s0 (fp-mul F q s1)) t1 (fp-sub F t0 (fp-mul F q t1)))))))

; g моничен/нуль, g | a, g | b, s·a + t·b = g
(define (fp-egcd-check F a b res)
  (let ((g (car res)) (s (cadr res)) (t (caddr res)))
    (and (or (null? g) (field-equal? F (fp-lc g) (field-one F)))
         (fp-equal? F g (fp-add F (fp-mul F s a) (fp-mul F t b)))
         (if (null? g) (and (null? (fp-trim F a)) (null? (fp-trim F b)))
             (and (null? (fp-rem F (fp-trim F a) g)) (null? (fp-rem F (fp-trim F b) g)))))))

(define (fp-egcd F a b)
  (let ((res (fp-egcd-raw F a b)))
    (if (fp-egcd-check F a b res) res
        (error "fp-egcd: сертификат s·a + t·b = g не прошёл"))))

; g | a, g | b, моничен, a/g и b/g взаимно просты (Безу для частных)
(define (fp-gcd-check F a b g)
  (let ((a (fp-trim F a)) (b (fp-trim F b)))
    (if (null? g) (and (null? a) (null? b))
        (and (field-equal? F (fp-lc g) (field-one F))
             (null? (fp-rem F a g)) (null? (fp-rem F b g))
             (let ((e (fp-egcd-raw F (fp-quo F a g) (fp-quo F b g))))
               (and (fp-egcd-check F (fp-quo F a g) (fp-quo F b g) e)
                    (fp-equal? F (car e) (list (field-one F)))))))))

(define (fp-gcd F a b)
  (let ((g (car (fp-egcd-raw F a b))))
    (if (fp-gcd-check F a b g) g
        (error "fp-gcd: сертификат НОД не прошёл"))))

; производная (коэффициент при x^i умножается на i как элемент поля)
(define (fp-deriv F a)
  (if (null? a) '()
      (fp-trim F (map2 (lambda (c i) (field-mul F (field-from-rational F (+ i 1)) c)) (cdr a) (range (- (length a) 1))))))

(define (fp-eval F a x)
  (foldl (lambda (acc c) (field-add F (field-mul F acc x) c)) (field-zero F) (reverse a)))

; a(b)
(define (fp-compose F a b)
  (foldl (lambda (acc c) (fp-add F (fp-mul F acc b) (if (field-zero? F c) '() (list c)))) '() (reverse a)))

; корень p-й степени из многочлена от x^p
(define (fp-pth-root F c)
  (let ((p (field-char F)) (pr (fld-proot F)))
    (let loop ((cs c) (i 0) (acc '()))
      (if (null? cs) (fp-trim F (reverse acc))
          (loop (cdr cs) (+ i 1) (if (= (modulo i p) 0) (cons (pr (car cs)) acc) acc))))))
(define (fp-sqf-monic F f)
  (let* ((d (fp-deriv F f)) (c (car (fp-egcd-raw F f d))) (w (fp-quo F f c)))
    (let loop ((w w) (c c) (i 1) (acc '()))
      (if (<= (fp-deg w) 0)
          (if (> (fp-deg c) 0)
              (let ((p (field-char F)))
                (if (= p 0) (error "fp-sqfree: внутренняя ошибка (char 0)")
                    (append acc (map (lambda (gi) (list (car gi) (* p (cadr gi))))
                                     (fp-sqf-monic F (fp-pth-root F c))))))
              acc)
          (let* ((y (car (fp-egcd-raw F w c))) (z (fp-quo F w y))
                 (acc2 (if (> (fp-deg z) 0) (append acc (list (list z i))) acc)))
            (loop y (fp-quo F c y) (+ i 1) acc2))))))

; проверка: res = (lc ((g i) …)); lc·∏ gᵢ^i = f; gᵢ монические бесквадратные, взаимно простые, кратности различны
(define (fp-pow F a k) (if (= k 0) (list (field-one F)) (fp-mul F a (fp-pow F a (- k 1)))))
(define (fp-sqfree-check F f res)
  (let* ((f (fp-trim F f)) (lc (car res)) (fs (cadr res)))
    (and (equal? (field-zero? F lc) (null? f))
         (fp-equal? F f (fp-scale F lc (foldl (lambda (acc gi) (fp-mul F acc (fp-pow F (car gi) (cadr gi))))
                                              (list (field-one F)) fs)))
         (every? (lambda (gi)
                   (let ((g (car gi)))
                     (and (> (fp-deg g) 0) (> (cadr gi) 0)
                          (field-equal? F (fp-lc g) (field-one F))
                          (fp-equal? F (car (fp-egcd-raw F g (fp-deriv F g))) (list (field-one F))))))
                 fs)
         (let loop ((l fs))
           (or (null? l)
               (and (every? (lambda (gj) (and (not (= (cadr (car l)) (cadr gj)))
                                              (fp-equal? F (car (fp-egcd-raw F (car (car l)) (car gj))) (list (field-one F)))))
                            (cdr l))
                    (loop (cdr l))))))))

; (fp-sqfree F f) → (lc ((g i) …)) по возрастанию кратности; f = 0 → (zero ())
(define (fp-sqfree F f)
  (let ((f (fp-trim F f)))
    (let ((res (if (null? f) (list (field-zero F) '())
                   (list (fp-lc f)
                         (sort (if (<= (fp-deg f) 0) '() (fp-sqf-monic F (fp-monic F f)))
                               (lambda (x y) (< (cadr x) (cadr y))))))))
      (if (fp-sqfree-check F f res) res
          (error "fp-sqfree: сертификат lc·∏ gᵢ^i = f не прошёл")))))

; ---------- матрицы ----------

(define (fm-cols m) (if (null? m) 0 (length (car m))))

(define (fm-identity F n)
  (map (lambda (i) (map (lambda (j) (if (= i j) (field-one F) (field-zero F))) (range n))) (range n)))

(define (fm-dot F u v)
  (foldl (lambda (acc x) (field-add F acc x)) (field-zero F) (map2 (lambda (a b) (field-mul F a b)) u v)))

(define (fm-transpose m)
  (if (null? m) '() (map (lambda (j) (map (lambda (r) (nth r j)) m)) (range (fm-cols m)))))

(define (fm-mat-vec F m v) (map (lambda (r) (fm-dot F r v)) m))

(define (fm-mul F a b)
  (let ((bt (fm-transpose b)))
    (if (and (pair? a) (pair? b) (not (= (fm-cols a) (length b))))
        (error "fm-mul: размеры не согласованы")
        (map (lambda (r) (map (lambda (c) (fm-dot F r c)) bt)) a))))

(define (fm-row-sub F r s c)   ; r − c·s
  (map2 (lambda (x y) (field-sub F x (field-mul F c y))) r s))

; (fm-rref F m) → (R pivots): приведённая ступенчатая форма (Гаусс–Жордан), номера ведущих столбцов
(define (fm-rref F m)
  (let ((n (fm-cols m)))
    (let loop ((j 0) (rows m) (r 0) (pivs '()))
      (if (or (>= j n) (>= r (length rows)))
          (list rows (reverse pivs))
          (let* ((top (take rows r)) (rest (drop rows r))
                 (k (let find ((l rest) (i 0))
                      (cond ((null? l) #f)
                            ((not (field-zero? F (nth (car l) j))) i)
                            (else (find (cdr l) (+ i 1)))))))
            (if (not k) (loop (+ j 1) rows r pivs)
                (let* ((pr0 (nth rest k))
                       (pr (map (lambda (x) (field-mul F x (field-inv F (nth pr0 j)))) pr0))
                       (others (append (take rest k) (drop rest (+ k 1))))
                       (elim (lambda (row) (fm-row-sub F row pr (nth row j)))))
                  (loop (+ j 1) (append (map elim top) (list pr) (map elim others)) (+ r 1) (cons j pivs)))))))))

(define (fm-rank F m) (length (cadr (fm-rref F m))))

(define (fm-zero-vec? F v) (every? (lambda (x) (field-zero? F x)) v))

(define (fm-nullspace-raw F m)
  (if (null? m) '()
      (let* ((n (fm-cols m)) (res (fm-rref F m)) (R (car res)) (pivs (cadr res))
             (free (filter (lambda (j) (not (member? j pivs))) (range n))))
        (map (lambda (f)
               (map (lambda (j)
                      (cond ((= j f) (field-one F))
                            ((member? j pivs) (field-neg F (nth (nth R (fm-index j pivs)) f)))
                            (else (field-zero F))))
                    (range n)))
             free))))

(define (fm-index x l) (let loop ((l l) (i 0)) (if (equal? (car l) x) i (loop (cdr l) (+ i 1)))))

(define (fm-nullspace-check F m basis)
  (let ((n (fm-cols m)))
    (and (every? (lambda (v) (and (= (length v) n) (not (fm-zero-vec? F v))
                                  (fm-zero-vec? F (fm-mat-vec F m v))))
                 basis)
         (= (length basis) (- n (fm-rank F m)))
         (or (null? basis) (= (fm-rank F basis) (length basis))))))

(define (fm-nullspace F m)
  (let ((b (fm-nullspace-raw F m)))
    (if (fm-nullspace-check F m b) b
        (error "fm-nullspace: сертификат A·v = 0 не прошёл"))))

; определитель (прямой ход Гаусса); квадратная матрица, пустая → 1
(define (fm-det F m)
  (if (and (pair? m) (not (= (fm-cols m) (length m))))
      (error "fm-det: матрица не квадратная")
      (let loop ((rows m) (d (field-one F)))
        (if (null? rows) d
            (let ((k (let find ((l rows) (i 0))
                       (cond ((null? l) #f)
                             ((not (field-zero? F (car (car l)))) i)
                             (else (find (cdr l) (+ i 1)))))))
              (if (not k) (field-zero F)
                  (let* ((pr (nth rows k))
                         (others (append (take rows k) (drop rows (+ k 1))))
                         (sgn (if (= (modulo k 2) 0) d (field-neg F d)))
                         (ip (field-inv F (car pr)))
                         (red (map (lambda (row) (cdr (fm-row-sub F row pr (field-mul F (car row) ip)))) others)))
                    (loop red (field-mul F sgn (car pr))))))))))

(define (fm-solve-check F m b res)
  (and res
       (let ((x (car res)) (basis (cadr res)))
         (and (= (length x) (fm-cols m))
              (equal? (map2 (lambda (u v) (field-equal? F u v)) (fm-mat-vec F m x) b)
                      (map (lambda (r) #t) b))
              (fm-nullspace-check F m basis)))))

; (fm-solve F A b) → (x nullspace-basis) или #f, если несовместна; общее решение x + Σ cᵢ·basisᵢ
(define (fm-solve F m b)
  (if (not (= (length m) (length b)))
      (error "fm-solve: длина b не равна числу строк")
      (let* ((n (fm-cols m))
             (aug (map2 (lambda (r x) (append r (list x))) m b))
             (res (fm-rref F aug)) (R (car res)) (pivs (cadr res)))
        (if (member? n pivs) #f
            (let* ((x (map (lambda (j) (if (member? j pivs) (last (nth R (fm-index j pivs))) (field-zero F)))
                           (range n)))
                   (ans (list x (fm-nullspace-raw F m))))
              (if (fm-solve-check F m b ans) ans
                  (error "fm-solve: сертификат A·x = b не прошёл")))))))

(define (fm-equal? F a b)
  (and (= (length a) (length b))
       (every? (lambda (p) (every? (lambda (t) t) (map2 (lambda (x y) (field-equal? F x y)) (car p) (cdr p))))
               (map2 (lambda (r s) (cons r s)) a b))))

(define (fm-inverse-check F m inv)
  (and inv
       (let ((n (length m)))
         (and (= (length inv) n)
              (fm-equal? F (fm-mul F m inv) (fm-identity F n))
              (fm-equal? F (fm-mul F inv m) (fm-identity F n))))))

; обратная матрица или #f для вырожденной; пустая → ()
(define (fm-inverse F m)
  (let ((n (length m)))
    (cond ((= n 0) '())
          ((not (= (fm-cols m) n)) (error "fm-inverse: матрица не квадратная"))
          (else
           (let* ((aug (map2 (lambda (r e) (append r e)) m (fm-identity F n)))
                  (res (fm-rref F aug)) (pivs (cadr res)))
             (if (not (equal? (take pivs (min n (length pivs))) (range n))) #f
                 (let ((inv (map (lambda (r) (drop r n)) (car res))))
                   (if (fm-inverse-check F m inv) inv
                       (error "fm-inverse: сертификат A·A⁻¹ = I не прошёл")))))))))
