; summation/product.lisp — Шаг 21l.8: символьное произведение и combsimp-минимум.
; product: ∏_{k=a}^{b} t(k) с символьной верхней границей. Каскад: константа → qᵏ →
; рациональное/полиномиальное тело (factor → линейные множители → Γ-отношения).
; Проверка — product-check: прямой счёт ∏ в целых точках против eval-num(ответа).
; combsimp (минимум): x·Γ(x) → x! (Γ(x+1); канонично — факториал, т.к. simplify
; разворачивает Γ(x+1) в x·Γ(x)); Γ-отношения с общим линейным основанием → многочлен.

(module summation
  (export product-symbolic product-check product-check-how combsimp
          combsimp-walk combsimp-walk-generic combsimp-mul-gamma combsimp-mul-nary
          combsimp-mul-pows combsimp-gf-ratio combsimp-gf-split combsimp-gf-find-pair
          combsimp-pow-split combsimp-find-gamma combsimp-find-match combsimp-remove2
          combsimp-remove1 combsimp-find-gamma-pow combsimp-fgp combsimp-find-l-pow
          combsimp-flp combsimp-remove-idxs combsimp-rmv combsimp-lin-diff
          combsimp-prod-lin gf-arg gf-shift gf-pow product-as-frac product-lin-mul
          product-constant product-qpow product-rational product-hyper product-direct product-fact-to-gamma))

; ---------- вспомогательное ----------

; (product тело k lo hi) — невычисленная форма
(define (product-unevaluated body k lo hi)
  (list 'product (simplify body) k (simplify lo) (simplify hi)))

; прямой счёт ∏_{k=a}^{b} t(k)
(define (product-direct-from body k kk b acc)
  (cond ((> kk b) acc)
        (else (product-direct-from body k (+ kk 1) b
                (* acc (simplify (subst (list '= k kk) body)))))))
(define (product-direct body k a b)
  (if (> a b) 1 (product-direct-from body k a b 1)))

; ---------- L0: тривиальное ----------

; тело не зависит от k: ∏ c = c^(b−a+1); пустой числовой диапазон → 1
(define (product-constant body k lo hi)
  (and (sum-k-free? body k)
       (cond ((and (number? lo) (number? hi) (> lo hi)) 1)
             ((and (number? lo) (number? hi)) (simplify (list '^ body (+ (- hi lo) 1))))
             (else (simplify (list '^ body (list '+ (list '- hi lo) 1)))))))

; ---------- L1: qᵏ ----------

; ∏_{k=a}^{b} q^k = q^{(a+b)(b−a+1)/2}; q ≠ 1 (q=1 — константа, L0)
(define (product-qpow body k lo hi)
  (and (op-expr? body) (equal? (car body) '^) (= (length body) 3)
       (equal? (caddr body) k)
       (sum-k-free? (cadr body) k)
       (not (and (number? (cadr body)) (= (cadr body) 1)))
       (sum-guard (lambda ()
         (simplify (list '^ (cadr body)
                         (list '/ (list '* (list '+ lo hi) (list '+ (list '- hi lo) 1)) 2)))))))

; ---------- L2: факторизация тела → Γ-отношения ----------

; разложение многочлена по k на константу и линейные множители (k + v).
; Возвращает (константа . ((1 . v1) (1 . v2) ...)) либо #f (нелинейный множитель/отказ).
(define (product-lin-mul p k)
  (let ((f (sum-guard (lambda () (factor p)))))
    (cond ((not f) #f)
          (else (product-lin-from-factor f k (cons 1 '()))))))

; обход factor-формы; acc = (константа . список пар (1 . v)); #f — нелинейный множитель
(define (product-lin-from-factor f k acc)
  (cond ((sum-k-free? f k) (cons (simplify (list '* (car acc) f)) (cdr acc)))
        ; n-арное произведение: обходим все множители
        ((and (op-expr? f) (equal? (car f) '*) (>= (length f) 3))
         (product-lin-from-factor-list (cdr f) k acc))
        ; степень с целым показателем >= 1: m повторов основания
        ((and (op-expr? f) (equal? (car f) '^) (= (length f) 3)
              (integer? (caddr f)) (>= (caddr f) 1))
         (product-lin-from-factor
           (if (= (caddr f) 1) (cadr f) (cons '* (m-repeat (caddr f) (cadr f))))
           k acc))
        (else
         (let ((l (sum-guard (lambda () (hyper-lin f k)))))
           (cond ((not l) #f)
                 ((not (= (car l) 1)) #f)
                 (else (cons (car acc) (append (cdr acc) (list (cons 1 (cdr l)))))))))))

; обход списка множителей n-арного произведения
(define (product-lin-from-factor-list fs k acc)
  (cond ((null? fs) acc)
        (else (let ((r (product-lin-from-factor (car fs) k acc)))
                (and r (product-lin-from-factor-list (cdr fs) k r))))))

; список из n повторений x
(define (m-repeat n x)
  (if (<= n 0) '() (cons x (m-repeat (- n 1) x))))

; разложение рационального тела на (num . den) — полиномы по k:
; (/ a b) → (a . b); произведения и целые степени (в т.ч. отрицательные) разбиваются
(define (product-as-frac e)
  (cond ((and (op-expr? e) (equal? (car e) '/) (= (length e) 3))
         (cons (cadr e) (caddr e)))
        ((and (op-expr? e) (equal? (car e) '^) (= (length e) 3)
              (integer? (caddr e)) (< (caddr e) 0))
         (cons 1 (if (= (caddr e) -1) (cadr e) (list '^ (cadr e) (- 0 (caddr e))))))
        ((and (op-expr? e) (equal? (car e) '^) (= (length e) 3)
              (integer? (caddr e)) (>= (caddr e) 1))
         (cons e 1))
        ((and (op-expr? e) (equal? (car e) '*) (>= (length e) 3))
         (let ((r (product-as-frac-list (cdr e) (cons 1 1))))
           (and r (cons (simplify (car r)) (simplify (cdr r))))))
        ; прочее (полином/сумма) — числитель; если не полином по k, откажет product-lin-mul
        ((op-expr? e) (cons e 1))
        (else #f)))

; свёртка списка множителей в пару (num . den)
(define (product-as-frac-list fs acc)
  (cond ((null? fs) acc)
        (else (let ((p (product-as-frac (car fs))))
                (and p (product-as-frac-list (cdr fs)
                         (cons (simplify (list '* (car acc) (car p)))
                               (simplify (list '* (cdr acc) (cdr p))))))))))

; рациональное тело: num/den — полиномы по k; тело-сумма — together сначала.
; Каждый линейный множитель (k+c) → ∏_{j=0}^{M−1} (lo+j+c) = Γ(lo+c+M)/Γ(lo+c).
(define (product-rational body k lo hi)
  (sum-guard (lambda ()
    (let ((b (product-as-frac (if (and (op-expr? body) (equal? (car body) '/))
                                  body
                                  (sum-guard (lambda () (together body)))))))
      (and b
           (let* ((M (list '+ (list '- hi lo) 1))
                  (nf (product-lin-mul (car b) k))
                  (df (product-lin-mul (cdr b) k)))
             (and nf df
                  (simplify (list '*
                                  (list '^ (list '/ (car nf) (car df)) M)
                                  (product-gamma-list (cdr nf) lo M)
                                  (product-gamma-recip (cdr df) lo M))))))))))

; полиномиальное тело (без знаменателя): константа^M · Γ-отношения
(define (product-hyper body k lo hi)
  (sum-guard (lambda ()
    (let* ((M (list '+ (list '- hi lo) 1))
           (pf (product-lin-mul body k)))
      (and pf
           (simplify (list '*
                           (list '^ (car pf) M)
                           (product-gamma-list (cdr pf) lo M))))))))

; произведение Γ(lo+c+M)/Γ(lo+c) по списку пар (1 . c)
(define (product-gamma-list cs lo M)
  (if (null? cs)
      1
      (simplify (list '*
                      (list '/ (list 'gamma (list '+ lo (cdr (car cs)) M))
                            (list 'gamma (list '+ lo (cdr (car cs)))))
                      (product-gamma-list (cdr cs) lo M)))))

; произведение Γ(lo+c)/Γ(lo+c+M) по списку пар (знаменатель)
(define (product-gamma-recip cs lo M)
  (if (null? cs)
      1
      (simplify (list '*
                      (list '/ (list 'gamma (list '+ lo (cdr (car cs))))
                            (list 'gamma (list '+ lo (cdr (car cs)) M)))
                      (product-gamma-recip (cdr cs) lo M)))))

; ---------- combsimp (минимум) ----------

; x·Γ(x) → x! — бинарное произведение (* A (Γ L)) или (* (Γ L) A), A совпадает с L
(define (combsimp-mul-gamma e)
  (and (op-expr? e) (equal? (car e) '*) (= (length e) 3)
       (or
        (let ((a (cadr e)) (g (caddr e)))
          (and (op-expr? g) (equal? (car g) 'gamma) (= (length g) 2)
               (equal? (simplify a) (simplify (cadr g)))
               (list 'factorial (cadr g))))
        (let ((a (caddr e)) (g (cadr e)))
          (and (op-expr? g) (equal? (car g) 'gamma) (= (length g) 2)
               (equal? (simplify a) (simplify (cadr g)))
               (list 'factorial (cadr g)))))))

; обход выражения: сначала локальные правила, затем спуск в поддеревья
; правило n-арного произведения: множитель (Γ L) и множитель L → (factorial L)
(define (combsimp-mul-nary e)
  (let ((fs (cdr e)))
    (let ((g (combsimp-find-gamma fs)))
      (and g
           (let ((other (combsimp-find-match (car g) (cdr fs))))
             (and other
                  (let ((rest (combsimp-remove2 fs (car g) other)))
                    (simplify (cons '* (cons (list 'factorial (cadr (car g))) rest))))))))))


; ---- правило степеней: (^ (Γ L) j) с множителем L^i (i, j целые, знаки согласованы)
; → (^ (factorial L) use) · остаток Γ^|j−use| ----
; разбор множителя: (база . показатель) для (^ b j) и (b . 1) для прочих
(define (combsimp-pow-split f)
  (cond ((and (op-expr? f) (equal? (car f) '^) (= (length f) 3) (integer? (caddr f)))
         (cons (cadr f) (caddr f)))
        (else (cons f 1))))

(define (combsimp-mul-pows e)
  (let* ((fs (cdr e))
         (pairs (map combsimp-pow-split fs)))
    (let ((gm (combsimp-find-gamma-pow pairs)))
      (and gm
           (let* ((gbase (car (nth pairs gm)))         ; (Γ L)
                  (L (cadr gbase))
                  (j (cdr (nth pairs gm))))
             (let ((lm (combsimp-find-l-pow pairs L gm)))
               (and lm
                    (let* ((i (cdr (nth pairs lm)))
                           (same-sign (or (and (> j 0) (> i 0)) (and (< j 0) (< i 0))))
                           (use (if same-sign
                                    (if (> j 0) (min j i) (- 0 (min (- 0 j) (- 0 i))))
                                    0))
                           (rest (combsimp-remove-idxs fs gm lm))
                           (extra (if (and same-sign (> (abs j) (abs use)))
                                      (list (list '^ gbase (- j use))) '()))
                           (fl (list 'factorial L))
                           (flp (cond ((= use 1) (list fl))
                                      ((= use -1) (list (list '^ fl -1)))
                                      (else (list (list '^ fl use))))))
                      (and same-sign (not (= use 0))
                           (simplify (cons '* (append flp extra rest))))))))))))

; индекс первого множителя (^ (Γ L) j), j целое
(define (combsimp-find-gamma-pow pairs)
  (combsimp-fgp pairs 0))
(define (combsimp-fgp pairs idx)
  (cond ((null? pairs) #f)
        ((and (op-expr? (car (car pairs))) (equal? (car (car (car pairs))) 'gamma)
              (= (length (car (car pairs))) 2))
         idx)
        (else (combsimp-fgp (cdr pairs) (+ idx 1)))))

; индекс множителя L^i (i ≠ 0), не равного skip
(define (combsimp-find-l-pow pairs L skip)
  (combsimp-flp pairs L skip 0))
(define (combsimp-flp pairs L skip idx)
  (cond ((null? pairs) #f)
        ((= idx skip) (combsimp-flp (cdr pairs) L skip (+ idx 1)))
        ((= (cdr (car pairs)) 0) (combsimp-flp (cdr pairs) L skip (+ idx 1)))
        ((equal? (simplify (car (car pairs))) (simplify L)) idx)
        (else (combsimp-flp (cdr pairs) L skip (+ idx 1)))))

; ---- правило Γ/factorial-отношений с общим линейным основанием ----
; разбор множителя: → тройка (arg shift . pow) либо #f
; (gamma X) → (X 0 . 1); (factorial X) → (X 1 . 1) — factorial = Γ(arg+1);
; (^ g j) → показатели перемножаются
(define (combsimp-gf-split f)
  (cond ((and (op-expr? f) (equal? (car f) 'gamma) (= (length f) 2))
         (cons (cadr f) (cons 0 1)))
        ((and (op-expr? f) (equal? (car f) 'factorial) (= (length f) 2))
         (cons (cadr f) (cons 1 1)))
        ((and (op-expr? f) (equal? (car f) '^) (= (length f) 3) (integer? (caddr f)))
         (let ((inner (combsimp-gf-split (cadr f))))
           (and inner (cons (car inner) (cons (car (cdr inner)) (caddr f))))))
        (else #f)))

; доступ к полям тройки (improper — только car/cdr)
(define (gf-arg s) (car s))
(define (gf-shift s) (car (cdr s)))
(define (gf-pow s) (cdr (cdr s)))

; целое c, если a = b + c (разность — целая константа), иначе #f
(define (combsimp-lin-diff a b)
  (let ((d (sum-guard (lambda () (simplify (list '- a b))))))
    (and (number? d) (integer? d) d)))

; в n-арном произведении найти Γ-множитель A (показатель +1 либо −1) и B
; (противоположный показатель), Γ-аргументы (сдвиг factorial учтён) отличаются
; на целое c > 0; заменить пару на ∏_{i=0}^{c−1} (argB + i)
(define (combsimp-gf-ratio e)
  (let ((fs (cdr e)))
    (let ((res (combsimp-gf-find-pair fs)))
      (and res
           (let* ((ia (nth res 0)) (ib (nth res 1))
                  (A (nth fs ia)) (B (nth fs ib))
                  (sa (combsimp-gf-split A)) (sb (combsimp-gf-split B))
                  (arga (list '+ (gf-arg sa) (gf-shift sa)))
                  (argb (list '+ (gf-arg sb) (gf-shift sb)))
                  (c (combsimp-lin-diff arga argb)))
             (and c (> c 0)
                  (let* ((rest (combsimp-remove-idxs fs ia ib))
                         (prod (combsimp-prod-lin argb 0 (- c 1))))
                    (simplify (cons '* (cons prod rest))))))))))

; ∏_{i=lo}^{hi} (L + i)
(define (combsimp-prod-lin L lo hi)
  (if (> lo hi)
      1
      (simplify (list '* (list '+ L lo) (combsimp-prod-lin L (+ lo 1) hi)))))

; поиск пары индексов: Γ-множитель p=+1 и Γ-множитель p=−1, Γ-аргументы отличаются
; на целое > 0; порядок любой
(define (combsimp-gf-find-pair fs)
  (or (combsimp-gfp fs fs 0 1)
      (combsimp-gfp fs fs 0 -1)))
(define (combsimp-gfp fs all idx want)
  (cond ((null? fs) #f)
        (else
         (let ((s (combsimp-gf-split (car fs))))
           (cond ((and s (= (gf-pow s) want))
                  (let ((b (combsimp-gfp-neg all (list '+ (gf-arg s) (gf-shift s)) 0 idx (- 0 want))))
                    (or b (combsimp-gfp (cdr fs) all (+ idx 1) want))))
                 (else (combsimp-gfp (cdr fs) all (+ idx 1) want)))))))

; ищем множитель с показателем want2 и Γ-аргументом Arg − c, c целое > 0
(define (combsimp-gfp-neg all Arg idx skip want2)
  (cond ((null? all) #f)
        ((= idx skip) (combsimp-gfp-neg (cdr all) Arg (+ idx 1) skip want2))
        (else
         (let ((s (combsimp-gf-split (car all))))
           (cond ((not s) (combsimp-gfp-neg (cdr all) Arg (+ idx 1) skip want2))
                 ((= (gf-pow s) want2)
                  (let* ((arg2 (list '+ (gf-arg s) (gf-shift s)))
                         (c (combsimp-lin-diff Arg arg2)))
                    (if (and c (> c 0)) (list skip idx) (combsimp-gfp-neg (cdr all) Arg (+ idx 1) skip want2))))
                 (else (combsimp-gfp-neg (cdr all) Arg (+ idx 1) skip want2)))))))

(define (combsimp-flp pairs L skip idx)
  (cond ((null? pairs) #f)
        ((= idx skip) (combsimp-flp (cdr pairs) L skip (+ idx 1)))
        ((= (cdr (car pairs)) 0) (combsimp-flp (cdr pairs) L skip (+ idx 1)))
        ((equal? (simplify (car (car pairs))) (simplify L)) idx)
        (else (combsimp-flp (cdr pairs) L skip (+ idx 1)))))

; удалить элементы с индексами a и b (0-based) из списка
(define (combsimp-remove-idxs fs a b)
  (combsimp-rmv fs (min a b) (max a b) 0))
(define (combsimp-rmv fs lo hi idx)
  (cond ((null? fs) '())
        ((or (= idx lo) (= idx hi)) (combsimp-rmv (cdr fs) lo hi (+ idx 1)))
        (else (cons (car fs) (combsimp-rmv (cdr fs) lo hi (+ idx 1))))))


; первый множитель вида (Γ L)
(define (combsimp-find-gamma fs)
  (cond ((null? fs) #f)
        ((and (op-expr? (car fs)) (equal? (car (car fs)) 'gamma) (= (length (car fs)) 2))
         (list (car fs)))
        (else (combsimp-find-gamma (cdr fs)))))

; множитель, равный L (кроме Γ-множителей)
(define (combsimp-find-match L fs)
  (cond ((null? fs) #f)
        ((and (op-expr? (car fs)) (equal? (car (car fs)) 'gamma)) (combsimp-find-match L (cdr fs)))
        ((equal? (simplify (car fs)) (simplify L)) (car fs))
        (else (combsimp-find-match L (cdr fs)))))

; удалить первое вхождение g и x из списка множителей
(define (combsimp-remove2 fs g x)
  (cond ((null? fs) '())
        ((equal? (car fs) g) (combsimp-remove1 (cdr fs) x))
        ((equal? (car fs) x) (combsimp-remove1 (cdr fs) g))
        (else (cons (car fs) (combsimp-remove2 (cdr fs) g x)))))
(define (combsimp-remove1 fs x)
  (cond ((null? fs) '())
        ((equal? (car fs) x) (cdr fs))
        (else (cons (car fs) (combsimp-remove1 (cdr fs) x)))))



; обход выражения: сначала локальные правила, затем спуск в поддеревья
(define (combsimp-walk e)
  (let ((r (combsimp-mul-gamma e)))
    (if r
        (combsimp-walk r)
        (if (and (op-expr? e) (equal? (car e) '*) (>= (length e) 3))
            (let ((r2 (or (combsimp-mul-nary e) (combsimp-mul-pows e) (combsimp-gf-ratio e))))
              (if r2 (combsimp-walk r2)
                  (combsimp-walk-generic e)))
            (combsimp-walk-generic e)))))

; общий обход: перестроить поддеревья
(define (combsimp-walk-generic e)
  (if (and (list? e) (not (null? e)) (not (equal? (car e) 'quote)))
      (simplify (cons (car e) (map combsimp-walk (cdr e))))
      e))

; combsimp: simplify + правила до фикс-поинта
(define (combsimp e)
  (let* ((s (simplify e))
         (r (combsimp-walk s)))
    (if (equal? r s)
        r
        (combsimp r))))

; ---------- каскад ----------

(define (product-symbolic-bare body k lo hi)
  (or (product-constant body k lo hi)
      (product-qpow body k lo hi)
      (product-rational body k lo hi)
      (product-hyper body k lo hi)))

; публичный вход: (product-symbolic тело k lo hi); inf — невычисленная форма;
; ответ — Γ-форма/полином/факториал после combsimp-полировки; отказ — (product ...)
(define (product-symbolic body k lo hi)
  (if (not (symbol? k)) (error "product-symbolic: переменная — символ"))
  (cond ((or (equal? lo 'inf) (equal? hi 'inf) (equal? lo '-inf) (equal? hi '-inf))
         (product-unevaluated body k lo hi))
        ((and (number? lo) (number? hi) (> lo hi)) 1)
        (else
          (let ((r (product-symbolic-bare body k lo hi)))
            (cond ((not r) (product-unevaluated body k lo hi))
                  (else (combsimp r)))))))

; ---------- проверка ----------

; factorial(x) → gamma(x+1): eval-num не вычисляет factorial напрямую
(define (product-fact-to-gamma e)
  (cond ((and (op-expr? e) (equal? (car e) 'factorial) (= (length e) 2))
         (list 'gamma (list '+ (cadr e) 1)))
        ((and (list? e) (not (null? e)) (not (equal? (car e) 'quote)))
         (cons (car e) (map product-fact-to-gamma (cdr e))))
        (else e)))

; одна точка: свободные символы заменены целыми vals → прямой счёт против eval-num(F)
(define (product-check-at F body k syms vals lo hi)
  (sum-guard
   (lambda ()
     (let* ((pairs (map2 (lambda (s v) (cons s v)) syms vals))
            (e-body (product-fact-to-gamma (sum-subst-many body pairs)))
            (lo2 (eval-num (sum-subst-many lo pairs)))
            (hi2 (eval-num (sum-subst-many hi pairs)))
            (e-F (product-fact-to-gamma (sum-subst-many F pairs)))
            (nf (eval-num e-F)))
       (and (number? lo2) (number? hi2) (sum-int? lo2) (sum-int? hi2) (number? nf)
            (<= (abs (- hi2 lo2)) 63)
            (let ((nd (eval-num (product-direct e-body k lo2 hi2))))
              (and (number? nd) (not (= nd 0))
                   (< (abs (/ (- nd nf) nd)) 1e-6))))))))

(define (product-check-combos F body k syms lo hi vals)
  (cond ((= (length vals) (length syms))
         (product-check-at F body k syms vals lo hi))
        (else (product-check-try-vals F body k syms lo hi vals sum-check-values))))

(define (product-check-try-vals F body k syms lo hi acc vs)
  (cond ((null? vs) #f)
        ; acc уже полный (в т.ч. пустые syms → проверка без подстановок) — не наращиваем дальше
        ((>= (length acc) (length syms)) (product-check-at F body k syms acc lo hi))
        (else (or (product-check-combos F body k syms lo hi (append acc (list (car vs))))
                  (product-check-try-vals F body k syms lo hi acc (cdr vs))))))

; чем проверено ∏ = F: 'numeric (прямой счёт в целых точках сошёлся) / 'skip
(define (product-check-how F body k lo hi)
  (let ((syms (sum-free-syms F k '())))
    (cond ((not (list? syms)) 'skip)
          ((> (length syms) 3) 'skip)
          ((product-check-try-vals F body k syms lo hi '() sum-check-values) 'numeric)
          (else 'skip))))

; (product-check F тело k lo hi) — 'numeric / 'skip
(define (product-check F body k lo hi)
  (product-check-how F body k lo hi))

