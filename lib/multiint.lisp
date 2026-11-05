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
  (export integrate-multi integrate-change jacobian-det line-integral arc-length surface-integral surface-area))

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

; (integrate-multi f ((x a b) (y c d) …)) — первый диапазон внешний, последний внутренний
(define (integrate-multi f ranges)
  (begin
    (mi-check-ranges ranges)
    (let ((v (mi-nest f (reverse ranges))))
      (if (pair? v) (try (simplify v) (lambda (er) v)) v))))

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
