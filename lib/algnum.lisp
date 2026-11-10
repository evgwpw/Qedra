; algnum.lisp — поле ℚ(α) = ℚ[t]/(m): арифметика по модулю m, минимальный многочлен, норма (21m A1.1)
;
; Lisp-тип на списках,
; F# не трогаем; встроенные alg+ alg- alg* alg-neg alg-compare alg-refine (арифметика LispAlgebraic, ℝ)
; НЕ переопределяем — имена модуля alg-field alg-elt и т. д. с ними не пересекаются (alg- и alg* заняты
; builtin — не экспортируем, в A1.2 имена alg-poly-gcd тоже свободны).
;
; ---------- Представление ----------
; ПОЛЕ — вектор #(m cs var emb): m — монический неприводимый над ℚ (каноническое выражение от var);
;   cs — коэффициенты m ПО ВОЗРАСТАНИЮ (c0 … cn, cn = 1); emb — вложение α: LispAlgebraic (вещественный корень
;   из real-roots) | комплексное приближение-выражение (+ a (* b %i)) из nroots (решение §5 п. 3, double) | #f.
; ЭЛЕМЕНТ — список рациональных коэффициентов ПО ВОЗРАСТАНИЮ (c0 … c_{n−1}), n = deg m; ноль — ().
; Умножение — по модулю m; обратный — расширенный Евклид над ℚ (по образцу rs-gcdex из lib/risch/field.lisp).
;
; Сертификаты (задание A1 «Обязательно»): каждая функция с ответом проверяет его перед возвратом:
;   alg-field: m неприводим (factor-list — один множитель); alg-inv: a·a⁻¹ ≡ 1 (mod m);
;   alg-minpoly: minpoly(p)(p) = 0 в ℚ(α); alg->expr: подстановка α в m даёт 0.

(module algnum
  (export alg-field alg-elt alg-field-minpoly alg-field-embed
           alg-add alg-sub alg-mul alg-div alg-inv alg-negate alg-pow alg-zero? alg-equal?
           alg-norm alg-minpoly alg->expr expr->alg
           alg-poly-div alg-poly-gcd alg-poly-sqfree alg-primitive
           alg-factor alg-factor-check factor-over))

; ---------- вспомогательные (списки по возрастанию) ----------

; рациональное число (integer/rational, без float)
(define (ag-rat? x) (and (number? x) (or (integer? x) (equal? (type-of x) 'rational))))

; убрать старшие нули (список по возрастанию — нули в конце); нулевой многочлен → ()
(define (ag-trim-loop cs)
  (if (and (pair? cs) (equal? (car cs) 0))
      (ag-trim-loop (cdr cs))
      cs))
(define (ag-trim cs) (reverse (ag-trim-loop (reverse cs))))

; добить нулями до длины n
(define (ag-pad cs n)
  (if (>= (length cs) n) cs (append cs (map (lambda (i) 0) (range (- n (length cs)))))))

; ---------- поле ----------

; коэффициенты канонического выражения m по возрастанию (coefficients уже даёт (c0 … cn)), проверка: моничный
(define (ag-field-coeffs m t)
  (let* ((cs (coefficients m t)))
    (if (or (null? cs) (not (ag-rat? (nth cs (- (length cs) 1)))))
        (error "alg-field: многочлен не над Q")
        (if (not (equal? (nth cs (- (length cs) 1)) 1))
            (error "alg-field: m должен быть моническим (старший коэффициент 1)")
            cs))))

; неприводимость над ℚ: factor-list даёт ровно один множитель кратности 1, совпадающий с m
; проверка неприводимости: factor-list выносит content, поэтому множитель сравнивается
; с m с точностью до рациональной константы (старшие коэффициенты обоих ≠ 0)
(define (ag-check-irreducible m)
  (let* ((fl (factor-list m))
         (body (cdr fl)))
    (if (and (= (length body) 1)
             (equal? (nth (nth body 0) 1) 1)
             (ag-prop-eq? (simplify (nth (nth body 0) 0)) (simplify m)))
        #t
        (error "alg-field: многочлен приводим над Q — поле не строится"))))

; p и q задают один полином с точностью до константы (по коэффициентам при x^k)?
(define (ag-prop-eq? p q)
  (let* ((d (max (degree p 'x) (degree q 'x)))
         (cp (coeff p 'x (degree p 'x)))
         (cq (coeff q 'x (degree q 'x))))
    (let loop ((k 0))
      (cond ((> k d) #t)
            ((not (equal? (simplify (* cp (coeff q 'x k)))
                          (simplify (* cq (coeff p 'x k))))) #f)
            (else (loop (+ k 1)))))))

; вложение по умолчанию: вещественный корень m (real-roots), иначе комплексное приближение double (nroots)
(define (ag-default-embed m t)
  (let ((rr (real-roots m t)))
    (if (null? rr)
        (let ((nr (nroots m t)))
          (if (null? nr) (error "alg-field: у многочлена нет корней") (nth nr 0)))
        (nth rr 0))))

; (alg-field m t [вложение]) → #(m cs t emb); m — монический неприводимый над ℚ, t — его переменная
(define (alg-field m t &rest opts)
  (ag-field-coeffs m t)
  (ag-check-irreducible m)
  (let ((emb (if (null? opts) (ag-default-embed m t) (car opts))))
    (vector m (ag-field-coeffs m t) t emb)))

(define (ag-f-m F) (vref F 0))    ; m — каноническое выражение
(define (ag-f-cs F) (vref F 1))   ; коэффициенты m по возрастанию
(define (ag-f-var F) (vref F 2))  ; символ генерирующей (переменная m)
(define (ag-f-emb F) (vref F 3))  ; вложение

(define (alg-field-minpoly F) (ag-f-m F))
(define (alg-field-embed F) (ag-f-emb F))

; ---------- элемент ----------

; (alg-elt F coeffs) → элемент: рациональные по возрастанию, длина ≤ deg m, старшие нули убраны
(define (alg-elt F cs)
  (let* ((n (- (length (ag-f-cs F)) 1))          ; степень элемента < deg m
         (c (take cs (min n (length cs)))))
    (if (let loop ((l c)) (cond ((null? l) #f) ((not (ag-rat? (car l))) #t) (else (loop (cdr l)))))
        (error "alg-elt: коэффициенты — только рациональные числа")
        (ag-trim c))))

; ---------- арифметика по модулю m ----------

; умножение многочленов из ℚ[t] (по возрастанию, без редукции): столбиками
(define (ag-mul-raw a b)
  (if (or (null? a) (null? b)) '()
      (let ((n (+ (length a) (length b) -1)))
        (let loop ((i 0) (acc (map (lambda (k) 0) (range n))))
          (if (>= i (length a)) acc
              (let ((row (append (map (lambda (k) 0) (range i))
                                 (map (lambda (c) (* (nth a i) c)) b))))
                (loop (+ i 1) (map2 + acc (ag-pad row n)))))))))

; редукция по модулю m (cs — по возрастанию, mc длины n+1 со старшим 1 при x^n):
; список c длины k задаёт степень k−1; при k−1 ≥ n вычитаем lc·x^{k−1−n}·m(x) (lc — старший коэф),
; сдвинутый m имеет длину (k−1−n)+(n+1) = k — старший член сокращается точно
(define (ag-reduce-loop F cs)
  (let* ((mc (ag-f-cs F)) (n (- (length mc) 1)))
    (let loop ((c cs))
      (let ((k (length c)))
        (if (<= k n) (ag-trim c)
            (let ((lc (nth c (- k 1))))
              (if (equal? lc 0)
                  (loop (ag-trim c))
                  (let ((mm (append (map (lambda (j) 0) (range (- k 1 n))) mc)))
                    (loop (ag-trim (map2 - c (map (lambda (x) (* lc x)) mm))))))))))))

(define (ag-reduce F cs) (ag-reduce-loop F cs))

; сложение/вычитание списков
(define (ag-add-lists a b)
  (let ((n (max (length a) (length b))))
    (ag-trim (map2 + (ag-pad a n) (ag-pad b n)))))

(define (alg-add F a b) (ag-add-lists a b))
(define (alg-negate F a) (map (lambda (c) (- c)) a))
(define (alg-sub F a b)
  (let ((n (max (length a) (length b))))
    (ag-trim (map2 - (ag-pad a n) (ag-pad b n)))))
(define (alg-mul F a b) (ag-reduce F (ag-mul-raw a b)))
(define (alg-zero? F a) (null? a))
(define (alg-equal? F a b) (null? (alg-sub F a b)))

; ---------- расширенный Евклид над ℚ[t] (списки по возрастанию) ----------

; (q r) — деление с остатком; b ≠ 0
(define (ag-divmod a b)
  (if (null? b) (error "alg-inv: деление на ноль")
      (let ((db (- (length b) 1)) (lb (last b)))
        (let loop ((r a) (q '()))
          (let ((dr (- (length r) 1)))
            (if (or (null? r) (< dr db)) (list (ag-trim q) r)
                (let* ((k (- dr db))
                       (c (/ (nth r dr) lb))
                       (term (ag-pad (append (map (lambda (i) 0) (range k))
                                             (map (lambda (x) (* c x)) b))
                             (+ dr 1))))
                  (loop (ag-trim (map2 - (ag-pad r (+ dr 1)) term))
                        (ag-set-at q k c)))))))))

; q с q[k] = c (список по возрастанию)
(define (ag-set-at q k c)
  (let ((qq (ag-pad q (+ k 1))))
    (ag-trim (map2 (lambda (x i) (if (= i k) c x)) qq (range (length qq))))))

; (g u v): g = u·a + v·b (g — НОД, может быть ненормированным)
(define (ag-gcdex a b)
  (if (null? b)
      (list a '(1) '())
      (let* ((qr (ag-divmod a b))
             (r (nth qr 1))
             (sub (ag-gcdex b r)))
        (list (nth sub 0)
              (nth sub 2)
              (ag-add-lists (nth sub 1)
                            (map (lambda (x) (- x)) (ag-mul-raw (nth qr 0) (nth sub 2))))))))

; обратный в ℚ(α): Евклид с a и m; сертификат a·a⁻¹ ≡ 1 (mod m)
(define (alg-inv F a)
  (if (null? a) (error "alg-inv: деление на ноль")
      (let* ((gex (ag-gcdex a (ag-f-cs F)))
             (g (nth gex 0)))
        (if (not (= (length g) 1))
            (error "alg-inv: элемент необратим (m неприводим — внутренняя ошибка)")
            (let* ((c (nth g 0))
                   (u (map (lambda (x) (/ x c)) (nth gex 1)))
                   (inv (ag-reduce F u)))
              (if (alg-equal? F (alg-mul F a inv) '(1))
                  inv
                  (error "alg-inv: сертификат a·a⁻¹ = 1 не прошёл")))))))

(define (alg-div F a b) (alg-mul F a (alg-inv F b)))

; целая степень (бинарное возведение); отрицательная — через обратный
(define (alg-pow F a n)
  (if (not (integer? n)) (error "alg-pow: степень — целое")
      (let loop ((b (if (< n 0) (alg-inv F a) a))
                 (e (abs n))
                 (acc '(1)))
        (cond ((= e 0) acc)
              ((even? e) (loop (alg-mul F b b) (quotient e 2) acc))
              (else (loop b (- e 1) (alg-mul F acc b)))))))

; ---------- норма и минимальный многочлен ----------

; элемент → многочлен p(var) (каноническое выражение)
(define (ag-poly-expr F a)
  (let ((v (ag-f-var F)))
    (simplify (cons '+ (map2 (lambda (c k) (list '* c (list '^ v k))) a (range (length a)))))))

; норма N(a) = res_var(m(var), p(var)) ∈ ℚ (у 0 → 0)
(define (alg-norm F a)
  (if (null? a) 0
      (simplify (resultant (ag-f-m F) (ag-poly-expr F a) (ag-f-var F)))))

; численное значение элемента по вложению (float; комплексное вложение — тоже expr от %i, eval-num не берёт
; мнимую часть — используем subst + упрощение, ниже ag-num-abs)
(define (ag-elt-val F a)
  (let ((emb (ag-f-emb F)))
    (cond ((equal? emb #f) (error "alg-minpoly: поле без вложения — нельзя выбрать множитель"))
          (else (simplify (subst (list (ag-f-var F) emb) (ag-poly-expr F a)))))))

; |z| численного значения (float, algebraic или expr от %i): float — abs, algebraic — 0 если z = 0,
; иначе большое число (точное сравнение alg-compare); (+ a (* b %i)) — sqrt(a²+b²)
(define (ag-num-abs v)
  (cond ((number? v) (if (< v 0) (- v) v))
        ((alg? v) (if (= v 0) 0 1000))
        ((and (list? v) (equal? (car v) '+))
         (let* ((terms (cdr v))
                (im (let loop ((ts terms) (acc 0))
                      (cond ((null? ts) acc)
                            ((and (list? (car ts)) (equal? (car (car ts)) '*)
                                  (equal? (last (car ts)) '%i))
                             (loop (cdr ts) (+ acc (abs (nth (car ts) 1)))))
                            ((equal? (car ts) '%i) (loop (cdr ts) (+ acc 1)))
                            (else (loop (cdr ts) acc)))))
                (re (let loop ((ts terms) (acc 0))
                      (cond ((null? ts) acc)
                            ((or (equal? (car ts) '%i)
                                 (and (list? (car ts)) (equal? (car (car ts)) '*)
                                      (equal? (last (car ts)) '%i)))
                             (loop (cdr ts) acc))
                            (else (loop (cdr ts) acc))))))
           (sqrt (+ (* im im) (* re re)))))
        ((and (list? v) (equal? (car v) '*)) (ag-num-abs (nth v 1)))
        ((and (list? v) (equal? (car v) '^)) (abs (nth v 2)))
        (else 0)))

; (alg-minpoly F a x) → минимальный многочлен a (каноническое выражение по x):
; res = res_t(m(t), x − p(t)) = ∏_σ (x − p(σ(α))) делится на minpoly(a); выбираем неприводимый множитель,
; обнуляющийся на численном значении элемента. Сертификат: Σ cᵢ·aⁱ = 0 в ℚ(α) (коэффициенты множителя по x).
(define (alg-minpoly F a x)
  (if (null? a) x
      (let* ((p (ag-poly-expr F a))
             (res (resultant (ag-f-m F) (list '- x p) (ag-f-var F)))
             (fl (factor-list res))
             (cands (map (lambda (fk) (nth fk 0)) (cdr fl)))
             (aval (ag-elt-val F a)))
        (let pick ((cs cands))
          (if (null? cs)
              (error "alg-minpoly: не найден множитель, обнуляющийся в элементе (вложение неточно?)")
              (let ((cv (ag-num-abs (simplify (subst (list 'x aval) (car cs))))))
                (if (< cv 1e-6)
                    (let ((mp (car cs)))
                      (if (ag-check-minpoly F a mp x)
                          mp
                          (error "alg-minpoly: сертификат minpoly(a)(a) = 0 не прошёл")))
                    (pick (cdr cs)))))))))

; Σ cᵢ·aⁱ = 0 в ℚ(α)?
; сертификат minpoly: p неприводим над ℚ (иначе (x²−2)(x−5) «прошёл» бы для √2 — замечание ревью) и p(a) = 0
(define (ag-check-minpoly F a p x)
  (and (ag-irreducible? p) (ag-vanishes? F a p x)))

(define (ag-irreducible? m)
  (let ((body (cdr (factor-list m))))
    (and (= (length body) 1) (equal? (nth (nth body 0) 1) 1))))

(define (ag-vanishes? F a p x)
  (let ((cs (coefficients p x)))
    (let loop ((i 0) (acc '()))
      (if (>= i (length cs)) (null? acc)
          (let ((ci (nth cs i)))
            (loop (+ i 1)
                  (if (equal? ci 0) acc
                      (alg-add F acc (ag-reduce F (ag-mul-raw (ag-trim (list ci)) (alg-pow F a i)))))))))))

; ---------- выражения ----------

; (alg->expr F a) → выражение: deg m = 2 и вещественное вложение — через радикал (^ d 1/2);
; иначе через (root-of m t). Генерирующая — символ t (переменная m).
(define (alg->expr F a)
  (let ((m (ag-f-m F)) (v (ag-f-var F)))
    (if (null? a) 0
        (let ((p (ag-poly-expr F a)))
          (if (and (= (length (ag-f-cs F)) 3) (not (equal? (ag-f-emb F) #f)))
              (let* ((cs (ag-f-cs F))
                     (b (nth cs 1))
                     (c (nth cs 0))
                     (d (simplify (list '- (list '^ b 2) (list '* 4 c))))
                     (sqr (simplify (list '^ d 1/2)))
                     (emb (ag-f-emb F)))
                (if (or (number? emb) (alg? emb))
                    (let* ((sgn (cond ((and (number? emb) (< emb 0)) -1)
                                      ((and (alg? emb) (< emb 0)) -1)
                                      ((and (number? emb) (> emb 0)) 1)
                                      ((and (alg? emb) (> emb 0)) 1)
                                      (else (error "alg->expr: вложение — нуль"))))
                           (alpha (simplify (list '/ (list '+ (if (= sgn 1) sqr (list '- 0 sqr)) (list '- b)) 2))))
                      (simplify (subst (list v alpha) p)))
                    (error "alg->expr: комплексное вложение — печать через root-of")))
              (simplify (subst (list v (list 'root-of m v)) p)))))))

; =====================================================================
; 21m A1.2: многочлены ℚ(α)[x] (коэффициенты-элементы) и примитивный элемент
; =====================================================================

; ---------- арифметика ℚ(α)[x] (по образцу lib/risch/field.lisp) ----------
; ap — список коэффициентов-элементов ПО ВОЗРАСТАНИЮ; нулевой коэффициент — '(); нулевой многочлен — ()

(define (ap-trim p)
  (let loop ((q (reverse p)))
    (if (and (pair? q) (null? (car q))) (loop (cdr q)) (reverse q))))
(define (ap-deg p) (- (length p) 1))
(define (ap-pad p n)
  (if (>= (length p) n) p (append p (map (lambda (i) '()) (range (- n (length p)))))))

(define (ap-add F a b)
  (let ((n (max (length a) (length b))))
    (ap-trim (map2 (lambda (x y) (alg-add F x y)) (ap-pad a n) (ap-pad b n)))))
(define (ap-sub F a b)
  (let ((n (max (length a) (length b))))
    (ap-trim (map2 (lambda (x y) (alg-sub F x y)) (ap-pad a n) (ap-pad b n)))))
(define (ap-neg F a) (map (lambda (c) (alg-negate F c)) a))
(define (ap-mul F a b)
  (if (or (null? a) (null? b)) '()
      (let ((n (+ (length a) (length b) -1)))
        (let loop ((i 0) (acc (map (lambda (k) '()) (range n))))
          (if (>= i (length a)) acc
              (let ((row (append (map (lambda (k) '()) (range i))
                                 (map (lambda (c) (alg-mul F (nth a i) c)) b))))
                (loop (+ i 1)
                      (map2 (lambda (x y) (alg-add F x y)) acc (ap-pad row n)))))))))

(define (ap-scale F c a) (if (null? a) '() (ap-trim (map (lambda (x) (alg-mul F c x)) a))))

; деление с остатком в ℚ(α)[x] (коэффициенты — в поле, деления точные): (q r)
(define (ap-divmod F a b)
  (if (null? b) (error "alg-poly-div: деление на ноль")
      (let ((db (ap-deg b)) (lb (last b)))
        (let loop ((r a) (q '()))
          (let ((dr (ap-deg r)))
            (if (or (null? r) (< dr db)) (list (ap-trim q) r)
                (let* ((k (- dr db))
                       (c (alg-div F (nth r dr) lb))
                       (term (ap-pad (append (map (lambda (i) '()) (range k))
                                             (map (lambda (x) (alg-mul F c x)) b))
                             (+ dr 1))))
                  (loop (ap-trim (map2 (lambda (x y) (alg-sub F x y)) (ap-pad r (+ dr 1)) term))
                        (ap-set-at F q k c)))))))))

; q с q[k] = c
(define (ap-set-at F q k c)
  (let ((qq (ap-pad q (+ k 1))))
    (ap-trim (map2 (lambda (x i) (if (= i k) c x)) qq (range (length qq))))))

(define (ap-equal? F a b) (null? (ap-sub F a b)))

; (alg-poly-div F a b) → (q r); сертификат: a = q·b + r и deg r < deg b
(define (alg-poly-div F a b)
  (let ((qr (ap-divmod F a b)))
    (if (and (ap-equal? F a (ap-add F (ap-mul F (nth qr 0) b) (nth qr 1)))
             (< (ap-deg (nth qr 1)) (ap-deg b)))
        qr
        (error "alg-poly-div: сертификат a = q·b + r не прошёл"))))

; НОД в ℚ(α)[x] (Евклид; нормировка моническая)
(define (ap-gcd F a b)
  (let loop ((x a) (y b))
    (if (null? y) (ap-monic F x)
        (loop y (nth (ap-divmod F x y) 1)))))
(define (ap-monic F p)
  (if (null? p) p
      (ap-scale F (alg-inv F (last p)) p)))

; (alg-poly-gcd F a b) → монический НОД; сертификат: g | a, g | b
(define (alg-poly-gcd F a b)
  (let ((g (ap-gcd F a b)))
    (if (and (null? (nth (ap-divmod F a g) 1))
             (null? (nth (ap-divmod F b g) 1)))
        g
        (error "alg-poly-gcd: сертификат делимости не прошёл"))))

; формальная производная по x (коэффициент при x^i умножить на i)
(define (ap-deriv F p)
  (if (null? p) '()
      (let ((n (length p)))
        (ap-trim (map (lambda (i)
                        (if (= i 0) '() (alg-mul F (ag-trim (list i)) (nth p i))))
                      (range n))))))

; (alg-poly-sqfree F p) → бесквадратная часть p / gcd(p, p′) (моническая); сертификат: q·g = p
(define (alg-poly-sqfree F p)
  (if (null? p) '()
      (let* ((dp (ap-deriv F p))
             (g (ap-gcd F p dp)))
        (if (>= (ap-deg g) (ap-deg p)) (ap-monic F p)
            (let ((q (nth (ap-divmod F p g) 0)))
              (if (null? (nth (ap-divmod F (ap-mul F q g) p) 1))
                  (ap-monic F q)
                  (error "alg-poly-sqfree: сертификат не прошёл")))))))


; ---------- примитивный элемент (PRIMELT: Trager 1976 §2; перебор s) ----------

; (expr->alg F e) — рациональная функция от t (генерирующей поля). Вход прогоняем через together:
; каноническая дробь — (* p (^ q -1)) либо полином от t с головами + * ^; «-» на входе упрощается.
(define (expr->alg F e)
  (expr->alg-nf F (simplify (together e))))

(define (expr->alg-nf F e)
  (cond ((ag-rat? e) (ag-trim (list e)))
        ((and (symbol? e) (contains-sym? (ag-f-m F) e)) '(0 1))   ; генерирующая (переменная m)
        ((and (list? e) (equal? (car e) '+))
         (foldl (lambda (acc u) (alg-add F acc (expr->alg-nf F u))) '() (cdr e)))
        ((and (list? e) (equal? (car e) '*))
         (foldl (lambda (acc u) (alg-mul F acc (expr->alg-nf F u))) '(1) (cdr e)))
        ((and (list? e) (equal? (car e) '^) (integer? (nth e 2)))
         (if (equal? (nth e 2) -1)
             (alg-inv F (expr->alg-nf F (nth e 1)))   ; (* p (^ q -1)) — деление
             (alg-pow F (expr->alg-nf F (nth e 1)) (nth e 2))))
        ((and (list? e) (equal? (car e) '-))   ; неканонический минус — если survived simplify
         (alg-sub F (expr->alg-nf F (nth e 1)) (expr->alg-nf F (nth e 2))))
        (else (error "expr->alg: выражение должно быть рациональной функцией от генерирующей поля"))))

; ---------- примитивный элемент (Trager 1976 §2, перебор s = 1, −1, 2, …) ----------

; res_y(m1(x − s·y), m2(y)) — многочлен от x (γ = α + s·β: m1(γ − s·y) = 0 и m2(y) = 0);
; в m1 заменяем ЕГО переменную t на (x − s·y), в m2 — t на y
(define (ag-prim-res m1 m2 s)
  (resultant (subst (list 't (list '- 'x (list '* s 'y))) m1)
             (subst (list 't 'y) m2)
             'y))

; бесквадратная часть многочлена от x: произведение неприводимых множителей по одному разу
(define (ag-radical m x)
  (let ((body (cdr (factor-list m))))
    (if (null? body) m
        (simplify (cons '* (map (lambda (fk) (nth fk 0)) body))))))



; монизация многочлена-выражения по 'x (alg-field требует монический m): делим коэффициенты на старший
(define (ag-monic-by-coeffs f0)
  (let* ((d (degree f0 'x))
         (lc (coeff f0 'x d))
         (ks (ag-range0 d)))
    (simplify
     (cons '+ (map (lambda (k)
                     (let ((c (simplify (list '/ (coeff f0 'x k) lc))))
                       (if (= k 0) c (list '* c (list '^ 'x k)))))
                   ks)))))

; примитивная целочисленная форма: тот же полином с точностью до рациональной константы,
; при котором factor-list выдает ровно один множитель, равный ему самому
; (content уже вынесен). Реализация: m·D/НОД, где D подбирается так, что
; factor-list(m·D) = (c (m·D 1)) — перебор малых D.
(define (ag-prim-part f0)
  (let loop ((D 1))
    (let* ((fm (simplify (cons '+ (map (lambda (k)
                                         (let ((c (* D (coeff f0 'x k))))
                                           (if (= k 0) c (list '* c (list '^ 'x k)))))
                                       (ag-range0 (degree f0 'x))))))
            (fl (try (factor-list fm) (lambda (e) '(0)))))
      (cond ((> D 64) (simplify f0))
            ((and (= (length (cdr fl)) 1)
                  (equal? (simplify (nth (nth (cdr fl) 0) 0)) (simplify fm)))
             fm)
            (else (loop (* D 2)))))))

(define (ag-range0 n)
  (let loop ((k 0) (acc '()))
    (if (> k n) (reverse acc) (loop (+ k 1) (cons k acc)))))

; (alg-primitive m1 m2) → (Fg alpha beta s): γ = α + s·β, Fg = ℚ(γ);
;   alpha, beta — α, β как элементы ℚ(γ). Сертификаты: m1(α) = 0, m2(β) = 0 в ℚ(γ), γ = α + s·β.
; Перебор s: res бесквадратен (deg бескв. части = deg m1 · deg m2 ⇒ [ℚ(α,β):ℚ] = произведение).
(define (alg-primitive m1 m2)
  (let ((dd (* (degree m1 't) (degree m2 't))))
    (let loop ((s 1))
      (let* ((res (ag-prim-res m1 m2 s))
             (sqf (ag-radical res 'x)))
        (if (not (= (degree sqf 'x) dd))
            (loop (if (> s 0) (- s) (+ (- s) 1)))
            ; res бесквадратен; [ℚ(α,β):ℚ] может быть меньше deg m1 · deg m2 (например, ℚ(√2, ⁴√2)) —
            ; тогда res приводим: поле γ строится по неприводимому множителю (замечание ревью)
            (let try-f ((fs (map (lambda (fk) (nth fk 0)) (cdr (factor-list res)))))
              (if (null? fs)
                  (loop (if (> s 0) (- s) (+ (- s) 1)))
                  (let* ((f0 (car fs))
                         (Fg (alg-field (ag-monic-by-coeffs f0) 'x))
                         (alpha (ag-prim-alpha Fg m1 m2 s)))
                    (if (not alpha)
                        (try-f (cdr fs))
                        (let* ((beta (alg-div Fg (alg-sub Fg '(0 1) alpha) (ag-trim (list s))))
                               (ok1 (ag-check-minpoly Fg alpha m1 't))
                               (ok2 (ag-check-minpoly Fg beta m2 't)))
                          (if (and ok1 ok2)
                              (list Fg alpha beta s)
                              (try-f (cdr fs)))))))))))))

; восстановление α как элемента ℚ(γ): линейный НОД в ℚ(γ)[u] многочленов
;   A(u) = m1(u)  и  B(u) = s^{d2}·m2((γ − u)/s) (оба обращаются в 0 в u = α);
; корень линейного НОДа g = u + c → α = −c.
(define (ag-prim-alpha Fg m1 m2 s)
  (let* ((d2 (degree m2 't))
         (B (simplify (list '* (list '^ s d2)
                             (subst (list 't (list '/ (list '- 'g 'u) s)) m2))))
         ; γ — генерирующая Fg; подставляем её символ вместо g
         (Bg (simplify (subst (list 'g (ag-f-var Fg)) B)))
         (Au (subst (list 't 'u) m1))
         (Acs (map (lambda (c) (expr->alg Fg c)) (coefficients Au 'u)))
         (Bcs (map (lambda (c) (expr->alg Fg c)) (coefficients Bg 'u)))
         (g (ap-gcd Fg (ap-trim Acs) (ap-trim Bcs))))
    (if (= (ap-deg g) 1)
        (alg-negate Fg (nth g 0))
        #f)))

; =====================================================================
; 21m A1.3: факторизация в ℚ(α)[x] — норма Трагера (Trager 1976 §3)
; =====================================================================

; ---------- вспомогательное для ℚ(α)[x] ----------

; целая неотрицательная степень ap-многочлена (бинарно)
(define (ap-pow-poly F p n)
  (if (not (and (integer? n) (>= n 0))) (error "ap-pow-poly: степень — целое ≥ 0")
      (let loop ((b p) (e n) (acc (list (alg-elt F '(1)))))
        (cond ((= e 0) acc)
              ((even? e) (loop (ap-mul F b b) (quotient e 2) acc))
              (else (loop b (- e 1) (ap-mul F acc b)))))))

; ap-многочлен → каноническое выражение по x (коэффициенты через alg->expr)
(define (ap-to-expr F p x)
  (if (null? p) 0
      (simplify (cons '+ (map2 (lambda (c k)
                                 (if (= k 0) (alg->expr F c)
                                     (list '* (alg->expr F c) (list '^ x k))))
                               p (range (length p)))))))

; то же, но коэффициенты — многочлены от генерирующей t (без вложения; для норм и подстановки α в конце)
(define (ap-to-expr-raw F p x)
  (if (null? p) 0
      (simplify (cons '+ (map2 (lambda (c k)
                                 (if (= k 0) (ag-poly-expr F c)
                                     (list '* (ag-poly-expr F c) (list '^ x k))))
                               p (range (length p)))))))

; выражение по x с коэффициентами в ℚ(α) (рациональные функции от генерирующей t) → ap-многочлен;
; после expand коэффициенты при x^k уже x-свободны — subst x→0 для чистоты
(define (expr->ap F e x)
  (let ((cs (coefficients (simplify (expand e)) x)))
    (ap-trim (map (lambda (c) (expr->alg F (simplify (subst (list x 0) c)))) cs))))

; ---------- бесквадратное разложение в ℚ(α)[x]: f = c·∏ gᵢ^i ----------

; (ag-sqfree-pairs F p) → ((g1 k1) …), gᵢ монические бесквадратные попарно взаимно простые, ∏gᵢ^kᵢ = monic(p).
; Классическая схема: v = gcd(p, p′), w = p/v; на шаге i: y = gcd(w, v), gᵢ = w/y, w ← y, v ← v/y.
(define (ag-sqfree-pairs F p)
  (if (null? p) '()
      (let* ((mono (ap-monic F p))
             (dp (ap-deriv F mono))
             (v (if (null? dp) mono (ap-gcd F mono dp)))
             (w (nth (ap-divmod F mono v) 0)))
        (let loop ((w w) (v v) (i 1) (acc '()))
          (if (or (null? w) (<= (ap-deg w) 0))
              (reverse acc)
              (let* ((y (ap-gcd F w v))
                     (gj (nth (ap-divmod F w y) 0))
                     (nv (nth (ap-divmod F v y) 0)))
                (loop y nv (+ i 1)
                      (if (or (null? gj) (<= (ap-deg gj) 0))
                          acc
                          (cons (list (ap-monic F gj) i) acc)))))))))

; ---------- норма Трагера ----------

; норма N(y) = res_t(m(t), f(y − s·t)) ∈ ℚ[y] — каноническое выражение по y; f — ap-многочлен по x
(define (ag-norm-shift F f s y)
  (let* ((fe (ap-to-expr-raw F f 'x))
         (shifted (simplify (subst (list 'x (list '- y (list '* s (ag-f-var F)))) fe)))
         (tg (simplify (together shifted))))
    (resultant (ag-f-m F) tg (ag-f-var F))))

; сдвиги без повторов: 0, 1, −1, 2, −2, … (n штук)
(define (ag-shift-seq n)
  (let loop ((s 0) (k 0) (acc '()))
    (if (>= k n) (reverse acc)
        (if (= s 0) (loop 1 (+ k 1) (cons 0 acc))
            (loop (if (> s 0) (- s) (+ (- s) 1)) (+ k 1) (cons s acc))))))

; норма бесквадратна? (все кратности factor-list = 1; сбой факторизации — #f)
(define (ag-norm-sqfree? N y)
  (let ((fl (try (factor-list N) (lambda (err) #f))))
    (and fl (every? (lambda (fk) (= (nth fk 1) 1)) (cdr fl)))))

; норма g(x − s·α) неприводима над ℚ? (ровно один множитель кратности 1)
(define (ag-factor-irreducible? F g s)
  (let* ((N (ag-norm-shift F g s 'y))
         (fl (try (factor-list N) (lambda (err) #f))))
    (and fl (= (length (cdr fl)) 1) (= (nth (nth (cdr fl) 0) 1) 1))))

; (alg-factor-irred F f) → список неприводимых множителей монического бесквадратного ap-многочлена f;
; перебор s до бесквадратной нормы; gᵢ = gcd(f, Nᵢ(x + s·α)); сертификат: сумма степеней = deg f И
; норма каждого gᵢ (с тем же s) неприводима над ℚ (⇒ gᵢ неприводим над ℚ(α)).
(define (alg-factor-irred F f)
  (let ((d (ap-deg f)))
    (if (<= d 1)
        (list f)
        (let try-s ((ss (ag-shift-seq (+ d d))))
          (if (null? ss) (error "alg-factor: не найден сдвиг с бесквадратной нормой")
              (let* ((s (car ss))
                     (N (ag-norm-shift F f s 'y)))
                (if (or (equal? N 0) (not (ag-norm-sqfree? N 'y))) (try-s (cdr ss))
                    (let* ((fl (cdr (factor-list N)))
                           (Nis (map (lambda (fk) (nth fk 0)) fl))
                           (gs (map (lambda (Ni)
                                      (let* ((Nie (subst (list 'y (list '+ 'x (list '* s (ag-f-var F)))) Ni))
                                             (g (ap-gcd F f (expr->ap F Nie 'x))))
                                        (if (or (null? g) (<= (ap-deg g) 0)) #f g)))
                                    Nis))
                           (nz (filter (lambda (g) g) gs)))
                      (if (not (= (foldl (lambda (acc g) (+ acc (ap-deg g))) 0 nz) d))
                          (try-s (cdr ss))
                          (if (every? (lambda (g) (ag-factor-irreducible? F g s)) nz)
                              nz
                              (try-s (cdr ss))))))))))))

; (alg-factor F f x) → (lc ((g1 k1) (g2 k2) …)): факторизация ap-многочлена f над полем F;
; gᵢ — монические ap-многочлены, kᵢ — кратности, lc — старший коэффициент f (элемент ℚ(α)).
; Сертификат (alg-factor-check): произведение = f точно; каждый gᵢ неприводим.
(define (alg-factor F f x)
  (if (null? f) (error "alg-factor: нулевой многочлен")
      (let* ((lc (last f))
             (pairs (ag-sqfree-pairs F f))
             (irreds (map (lambda (pr) (map (lambda (g) (list g (cadr pr)))
                                            (alg-factor-irred F (car pr))))
                          pairs)))
        (list lc (apply append irreds)))))

; (alg-factor-check F f x ans) → #t/#f — независимая проверка сертификата:
; (1) lc·∏ gᵢ^kᵢ = f в ℚ(α)[x]; (2) каждый gᵢ степени ≥ 2 неприводим — свой перебор сдвига s
;     (существование s с неприводимой нормой гарантирует теорема Трагера).
(define (alg-factor-check F f x ans)
  (and (list? ans) (= (length ans) 2) (list? (nth ans 1))
       (let ((lc (nth ans 0)) (pairs (nth ans 1)))
         (and (ap-equal? F
                         (ap-scale F lc
                           (foldl (lambda (acc pr) (ap-mul F acc (ap-pow-poly F (car pr) (cadr pr))))
                                  (list (alg-elt F '(1))) pairs))
                         f)
              (every? (lambda (pr)
                        (let ((g (car pr)))
                          (or (<= (ap-deg g) 1)
                              (let find-s ((ss (ag-shift-seq 16)))
                                (and (not (null? ss))
                                     (or (ag-factor-irreducible? F g (car ss))
                                         (find-s (cdr ss))))))))
                    pairs)))))

; ---------- удобная форма: factor-over ----------

; (factor-over p x α) → (lc ((f1 k1) …)): разложение многочлена p по x над ℚ(α);
; α = (^ d 1/2) — ℚ(√d), %i — ℚ(i), (root-of m t) — ℚ(корень m). lc и множители — выражения (alg->expr).
; Поле — вложение по умолчанию (вещественный корень m, если есть); сертификат — alg-factor-check,
; не прошёл — ошибка.
(define (factor-over p x alpha)
  (let* ((m (cond ((and (list? alpha) (equal? (car alpha) '^)
                        (rational-number? (nth alpha 2))
                        (let ((n (/ 1 (nth alpha 2)))) (and (integer? n) (>= n 2))))
                   ; α = e^(1/n), n ≥ 2 ⇒ m = tⁿ − e (n = 1/(степень))
                   (simplify (list '+ (list '^ 't (/ 1 (nth alpha 2))) (list '* -1 (nth alpha 1)))))
                  ((equal? alpha '%i) (list '+ (list '^ 't 2) 1))
                  ((and (list? alpha) (equal? (car alpha) 'root-of)) (nth alpha 1))
                  (else (error "factor-over: генерирующая — (^ e 1/n) (n ≥ 2, например (^ 2 1/3)), %i или (root-of m t)"))))
         (F (alg-field m 't))
         ; вхождения генерирующей в p → t (α как подвыражение, целиком)
         (pt (replace-expr p alpha 't))
         (f (expr->ap F pt x))
         (r (alg-factor F f x))
         ; печать коэффициентов: многочлен от t, затем t → α (само выражение-генерирующая)
         (pr (lambda (g) (simplify (subst (list 't alpha) (ap-to-expr-raw F g x))))))
    (if (not (alg-factor-check F f x r))
        (error "factor-over: сертификат факторизации не прошёл")
        (cons (simplify (subst (list 't alpha) (ag-poly-expr F (nth r 0))))
              (map (lambda (pq) (list (pr (car pq)) (cadr pq))) (nth r 1))))))





