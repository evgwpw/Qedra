; galois.lisp — группа Галуа многочлена степени ≤ 7 (шаг GAL)
; G ⊆ S_n действует на корнях. GAL.1: инварианты (Дедекинд, дискриминант),
; неприводимость, таблица транзитивных групп степени ≤ 7.
(module galois
  (export galois-poly-degree galois-disc galois-disc-square? galois-irreducible?
          galois-cycle-types galois-cycle-types-check
          gal-transitive-groups gal-transitive-table-ok?
          gal-group-elements gal-cycle-types-of
          gal-group-lookup gal-cycle-type-member?
          galois-group galois-group-check
          galois-solvability solvable-by-radicals?))

; ---------- вспомогательное ----------

; список a…b
(define (gal-upto a b)
  (if (> a b) '() (cons a (gal-upto (+ a 1) b))))

; все элементы списка удовлетворяют предикату?
(define (gal-all? f lst)
  (cond ((null? lst) #t)
        ((f (car lst)) (gal-all? f (cdr lst)))
        (else #f)))

; n копий v
(define (gal-replicate n v)
  (if (<= n 0) '() (cons v (gal-replicate (- n 1) v))))

; ---------- коэффициенты и дискриминант ----------

; степень многочлена f по x (наибольший i ≤ 64 с ненулевым коэффициентом)
(define (galois-poly-degree f x)
  (let loop ((i 64))
    (cond ((< i 0) 0)
          ((not (= (coeff f x i) 0)) i)
          (else (loop (- i 1))))))

; коэффициенты по возрастанию (a0 … a_n), n = степень
(define (gal-coeffs f x)
  (map (lambda (i) (coeff f x i)) (gal-upto 0 (galois-poly-degree f x))))

; старший коэффициент
(define (gal-lc f x)
  (coeff f x (galois-poly-degree f x)))

; производная f по x как выражение (почленно)
(define (gal-deriv-expr f x)
  (let ((n (galois-poly-degree f x)))
    (simplify
     (cons '+ (map (lambda (i) (list '* i (list '* (coeff f x i) (list '^ x (- i 1)))))
                   (gal-upto 1 n))))))

; дискриминант f: (−1)^{n(n−1)/2}·res(f, f′)/lc(f) — рациональное число
(define (galois-disc f x)
  (let* ((n (galois-poly-degree f x))
         (lc (gal-lc f x))
         (r (resultant f (gal-deriv-expr f x) x))
         (sign (if (even? (/ (* n (- n 1)) 2)) 1 -1))
         (val (simplify (list '/ (list '* sign r) lc))))
    (if (number? val) val (error "galois-disc: дискриминант не число"))))

; целое n ≥ 0 — точный квадрат? (через factor-integer: все кратности чётные)
(define (gal-int-square? n)
  (cond ((< n 0) #f)
        ((= n 0) #t)
        (else (gal-all? (lambda (e) (even? (car (cdr e))))
                        (factor-integer n)))))

; рациональное q — точный квадрат? (0 — квадрат)
(define (gal-rat-square? q)
  (cond ((and (number? q) (integer? q)) (gal-int-square? q))
        ((number? q)
         (and (>= (numer q) 0)
              (gal-int-square? (numer q)) (gal-int-square? (denom q))))
        (else #f)))

; дискриминант — точный квадрат в ℚ ⇔ G ⊆ A_n
(define (galois-disc-square? f x)
  (gal-rat-square? (galois-disc f x)))

; ---------- неприводимость ----------

; факторизация f над ℚ через builtin factor-list → (содержание (f1 k1) (f2 k2) …);
; возвращаем список пар ((многочлен кратность) …)
(define (gal-factor-list f)
  (cdr (factor-list f)))

; f неприводим над ℚ? (один множитель степени deg f; константа-содержание
; игнорируется)
(define (galois-irreducible? f x)
  (let ((fs (gal-factor-list f)))
    (and (= (length fs) 1)
         (= (galois-poly-degree (car (car fs)) x) (galois-poly-degree f x)))))

; ---------- разложение mod p и циклотипы (Дедекинд) ----------

; коэффициент → вычет mod p (рациональные — через numer/denom, p ∤ denom
; гарантируется проверкой p ∤ lc)
(define (gal-cmod c p)
  (mod (numer c) p))

; тип разложения mod p по коэффициентам cs (целые/рациональные, по возрастанию):
; список степеней неприводимых множителей; #f, если старший коэффициент ≡ 0 (mod p).
; Только для p ∤ disc (многочлен mod p без кратных множителей): распределение
; по степеням (DDF, gcd(x^(p^d) − x, g)) — множители не выписываются
(define (gal-modp-type-cs cs p)
  (let ((cm (map (lambda (c) (gal-cmod c p)) cs)))
    (cond ((= (car (reverse cm)) 0) #f)
          (else
           (let* ((g (gf::gf-pmonic p (gf::gf-cs p cm)))
                  (ddf (gf::gf-ddf p g)))
             (apply append
                    (map (lambda (e)
                           (gal-replicate (/ (- (length (car e)) 1) (car (cdr e)))
                                          (car (cdr e))))
                         ddf)))))))

(define (gal-modp-type f x p)
  (gal-modp-type-cs (gal-coeffs f x) p))

; (galois-cycle-types f x primes) — алист ((циклотип . частота) …) наблюдённых
; типов Фробениуса для простых p ∤ disc·lc (теорема Дедекинда)
(define (galois-cycle-types f x primes)
  (let* ((disc (galois-disc f x))
         (lc (gal-lc f x))
         (h (make-hash)))
    (gal-scan-primes! h f x disc lc primes)
    (map (lambda (k) (cons k (hash-ref h k))) (hash-keys h))))

; (galois-cycle-types-check f x primes res) — независимый пересчёт
(define (galois-cycle-types-check f x primes res)
  (and (list? res)
       (let ((fresh (galois-cycle-types f x primes)))
         (and (= (length res) (length fresh))
              (gal-all? (lambda (e)
                          (let ((m (assoc (car e) fresh)))
                            (and m (= (cdr m) (cdr e)))))
                        res)
              (gal-all? (lambda (e) (= (apply + (car e)) (galois-poly-degree f x)))
                        res)))))

; ---------- элементы группы и циклотипы ----------

; все элементы группы G = (gens n): BFS по слоям от тождественной,
; дедупликация хешем (линейно по порядку группы)
(define (gal-group-elements G)
  (let* ((gens (car G))
         (n (car (cdr G)))
         (seen (make-hash))
         (out '()))
    (hash-set! seen (vector->list (perm-id n)) #t)
    (let loop ((frontier (list (perm-id n))))
      (cond ((null? frontier) (reverse out))
            (else
             (let ((next '()))
               (for-each
                (lambda (g)
                  (set! out (cons g out))
                  (for-each
                   (lambda (r)
                     (let* ((ng (perm-mul g r)) (k (vector->list ng)))
                       (cond ((hash-has? seen k) #f)
                             (else (hash-set! seen k #t)
                                   (set! next (cons ng next))))))
                   gens))
                frontier)
               (loop (reverse next))))))))

; циклотип перестановки степени n: длины ВСЕХ циклов (включая единичные)
; по убыванию — разбиение числа n; сопоставим с типами Дедекинда
(define (gal-perm-cycle-type p)
  (let* ((cs (map length (perm->cycles p)))
         (fixed (- (length (vector->list p)) (apply + cs))))
    (sort (append cs (gal-replicate fixed 1)) >)))

; все циклотипы группы (без повторов; порядок вставки)
(define (gal-cycle-types-of G)
  (let ((h (make-hash)))
    (for-each (lambda (g) (hash-set! h (gal-perm-cycle-type g) #t))
              (gal-group-elements G))
    (hash-keys h)))

; циклотип ct встречается в группе?
(define (gal-cycle-type-member? G ct)
  (let ((ts (gal-cycle-types-of G)))
    (let loop ((l ts))
      (cond ((null? l) #f)
            ((equal? (car l) ct) #t)
            (else (loop (cdr l)))))))

; ---------- таблица транзитивных групп степени ≤ 7 ----------
; строка: (имя порядок gens ∈A_n? разрешима?); gens — список образующих,
; каждый — циклы на точках 1..n. Данные: GAP transgrp (hulpke/transgrp,
; lib/trans.grp; число групп по степеням: 1,1,2,5,5,16,7).

(define *gal-transitive-table*
  '((1 ((C1 1 () #t #t)))
    (2 ((C2 2 (((1 2))) #f #t)))
    (3 ((C3 3 (((1 2 3))) #t #t)
        (S3 6 (((1 3)) ((1 2))) #f #t)))
    (4 ((C4 4 (((1 2 3 4))) #f #t)
        (V4 4 (((1 4) (2 3)) ((1 2) (3 4))) #t #t)
        (D4 8 (((1 2 3 4)) ((1 3))) #f #t)
        (A4 12 (((1 3 4)) ((2 3 4))) #t #t)
        (S4 24 (((1 4)) ((1 2)) ((2 3))) #f #t)))
    (5 ((C5 5 (((1 2 3 4 5))) #t #t)
        (D5 10 (((1 2 3 4 5)) ((1 4) (2 3))) #t #t)
        (F20 20 (((1 2 3 4 5)) ((1 2 4 3))) #f #t)
        (A5 60 (((1 4 5)) ((2 4 5)) ((3 4 5))) #t #f)
        (S5 120 (((1 5)) ((1 2)) ((2 3)) ((3 4))) #f #f)))
    (6 ((C6 6 (((1 2 3 4 5 6))) #f #t)
        (S3d6 6 (((1 3 5) (2 4 6)) ((1 4) (2 3) (5 6))) #f #t)
        (D6 12 (((1 2 3 4 5 6)) ((1 4) (2 3) (5 6))) #f #t)
        (A4d6 12 (((1 4) (2 5)) ((1 3 5) (2 4 6))) #t #t)
        (F18 18 (((2 4 6)) ((1 4) (2 5) (3 6))) #f #t)
        (2A4d6 24 (((3 6)) ((1 3 5) (2 4 6))) #f #t)
        (S4d6 24 (((1 4) (2 5)) ((1 3 5) (2 4 6)) ((1 5) (2 4))) #t #t)
        (S4c6 24 (((1 4) (2 5)) ((1 3 5) (2 4 6)) ((1 5) (2 4) (3 6))) #f #t)
        (F18x2 36 (((2 4 6)) ((1 5) (2 4)) ((1 4) (2 5) (3 6))) #f #t)
        (F36 36 (((2 4 6)) ((1 5) (2 4)) ((1 4 5 2) (3 6))) #t #t)
        (2S4d6 48 (((3 6)) ((1 3 5) (2 4 6)) ((1 5) (2 4))) #f #t)
        (PSL25d6 60 (((1 2 3 4 6)) ((1 4) (5 6))) #t #f)
        (F36x2 72 (((2 4 6)) ((2 4)) ((1 4) (2 5) (3 6))) #f #t)
        (PGL25d6 120 (((1 2 3 4 6)) ((1 2) (3 4) (5 6))) #f #f)
        (A6 360 (((1 5 6)) ((2 5 6)) ((3 5 6)) ((4 5 6))) #t #f)
        (S6 720 (((1 6)) ((1 2)) ((2 3)) ((3 4)) ((4 5))) #f #f)))
    (7 ((C7 7 (((1 2 3 4 5 6 7))) #t #t)
        (D7 14 (((1 2 3 4 5 6 7)) ((1 6) (2 5) (3 4))) #f #t)
        (F21 21 (((1 2 3 4 5 6 7)) ((1 2 4) (3 6 5))) #t #t)
        (F42 42 (((1 2 3 4 5 6 7)) ((1 3 2 6 4 5))) #f #t)
        (PSL32d7 168 (((1 2 3 4 5 6 7)) ((1 2) (3 6))) #t #f)
        (A7 2520 (((1 6 7)) ((2 6 7)) ((3 6 7)) ((4 6 7)) ((5 6 7))) #t #f)
        (S7 5040 (((1 7)) ((1 2)) ((2 3)) ((3 4)) ((4 5)) ((5 6))) #f #f)))))

; транзитивные группы степени n: список строк таблицы; #f при n > 7
(define (gal-transitive-groups n)
  (let ((m (assoc n *gal-transitive-table*)))
    (if m (car (cdr m)) #f)))

; группа из строки таблицы: (gens n)
(define (gal-row->group row n)
  (list (map perm-from-cycles (car (cdr (cdr row)))) n))

; строка таблицы по имени группы
(define (gal-group-lookup n name)
  (let loop ((rows (gal-transitive-groups n)))
    (cond ((null? rows) #f)
          ((equal? (car (car rows)) name) (car rows))
          (else (loop (cdr rows))))))

; порядок транзитивной группы степени ≤ 7 — группа разрешима? (порядки
; неразрешимых: 60 = PSL(2,5), 120 = PGL(2,5), 168 = PSL(3,2), 360, 720,
; 2520, 5040; среди транзитивных степеней ≤ 7 других с такими порядками нет)
(define (gal-solvable-order? ord)
  (not (or (= ord 60) (= ord 120) (= ord 168) (= ord 2520)
           (= ord 360) (= ord 720) (= ord 5040))))

; (gal-transitive-table-ok? n) — сверка таблицы с вычисленным: порядок
; (group-order), число элементов BFS = порядок, транзитивность (орбита точки 1
; — все n точек), флаг A_n (все элементы чётные), флаг разрешимости (по
; порядку — см. gal-solvable-order?)
(define (gal-transitive-table-ok? n)
  (gal-all?
   (lambda (row)
     (let* ((G (gal-row->group row n))
            (ord (group-order G))
            (elts (gal-group-elements G))
            (orbit (group-orbit (car G) 1))
            (in-an (gal-all? (lambda (p) (= (perm-sign p) 1)) elts)))
       (and (= ord (car (cdr row)))
            (= (length elts) ord)
            (equal? (length orbit) n)
            (equal? in-an (car (cdr (cdr (cdr row)))))
            (equal? (gal-solvable-order? ord)
                    (car (cdr (cdr (cdr (cdr row)))))))))
   (gal-transitive-groups n)))

; ---------- GAL.2: определение группы с сертификатом ----------

; Данные строк таблицы: (имя циклотипы орбиты-на-парах орбиты-на-тройках
; орбиты-на-упорядоченных-парах); размеры орбит по возрастанию. Получены
; вычислением по группе (BFS по элементам, орбиты по образующим), тест
; «GAL: данные строк» сверяет их заново — здесь они кешируются один раз.
(define *gal-row-data*
  '((C5 ((5) (1 1 1 1 1)) (5 5) (5 5) (5 5 5 5))
    (D5 ((5) (2 2 1) (1 1 1 1 1)) (5 5) (5 5) (10 10))
    (F20 ((5) (4 1) (2 2 1) (1 1 1 1 1)) (10) (10) (20))
    (A5 ((5) (3 1 1) (2 2 1) (1 1 1 1 1)) (10) (10) (20))
    (S5 ((5) (4 1) (3 2) (3 1 1) (2 2 1) (2 1 1 1) (1 1 1 1 1)) (10) (10) (20))
    (C6 ((6) (3 3) (2 2 2) (1 1 1 1 1 1)) (3 6 6) (2 6 6 6) (6 6 6 6 6))
    (S3d6 ((3 3) (2 2 2) (1 1 1 1 1 1)) (3 3 3 6) (2 6 6 6) (6 6 6 6 6))
    (D6 ((6) (3 3) (2 2 2) (2 2 1 1) (1 1 1 1 1 1)) (3 6 6) (2 6 12) (6 12 12))
    (A4d6 ((3 3) (2 2 1 1) (1 1 1 1 1 1)) (3 12) (4 4 6 6) (6 12 12))
    (F18 ((6) (3 3) (3 1 1 1) (2 2 2) (1 1 1 1 1 1)) (6 9) (2 18) (6 6 18))
    (2A4d6 ((6) (3 3) (2 2 2) (2 2 1 1) (2 1 1 1 1) (1 1 1 1 1 1)) (3 12) (6 6 8) (6 12 12))
    (S4d6 ((4 2) (3 3) (2 2 1 1) (1 1 1 1 1 1)) (3 12) (4 4 12) (6 24))
    (S4c6 ((3 3) (4 1 1) (2 2 2) (2 2 1 1) (1 1 1 1 1 1)) (3 12) (8 12) (6 24))
    (F18x2 ((6) (3 3) (3 1 1 1) (2 2 2) (2 2 1 1) (1 1 1 1 1 1)) (6 9) (2 18) (12 18))
    (F36 ((4 2) (3 3) (3 1 1 1) (2 2 1 1) (1 1 1 1 1 1)) (6 9) (2 18) (12 18))
    (2S4d6 ((6) (4 2) (3 3) (4 1 1) (2 2 2) (2 2 1 1) (2 1 1 1 1) (1 1 1 1 1 1)) (3 12) (8 12) (6 24))
    (PSL25d6 ((5 1) (3 3) (2 2 1 1) (1 1 1 1 1 1)) (15) (10 10) (30))
    (F36x2 ((6) (4 2) (3 3) (3 2 1) (3 1 1 1) (2 2 2) (2 2 1 1) (2 1 1 1 1) (1 1 1 1 1 1)) (6 9) (2 18) (12 18))
    (PGL25d6 ((6) (5 1) (4 1 1) (3 3) (2 2 2) (2 2 1 1) (1 1 1 1 1 1)) (15) (20) (30))
    (A6 ((5 1) (4 2) (3 3) (3 1 1 1) (2 2 1 1) (1 1 1 1 1 1)) (15) (20) (30))
    (S6 ((6) (5 1) (4 2) (4 1 1) (3 3) (3 2 1) (3 1 1 1) (2 2 2) (2 2 1 1) (2 1 1 1 1) (1 1 1 1 1 1)) (15) (20) (30))
    (C7 ((7) (1 1 1 1 1 1 1)) (7 7 7) (7 7 7 7 7) (7 7 7 7 7 7))
    (D7 ((7) (2 2 2 1) (1 1 1 1 1 1 1)) (7 7 7) (7 7 7 14) (14 14 14))
    (F21 ((7) (3 3 1) (1 1 1 1 1 1 1)) (21) (7 7 21) (21 21))
    (F42 ((7) (6 1) (3 3 1) (2 2 2 1) (1 1 1 1 1 1 1)) (21) (14 21) (42))
    (PSL32d7 ((7) (4 2 1) (3 3 1) (2 2 1 1 1) (1 1 1 1 1 1 1)) (21) (7 28) (42))
    (A7 ((7) (5 1 1) (4 2 1) (3 3 1) (3 2 2) (3 1 1 1 1) (2 2 1 1 1) (1 1 1 1 1 1 1)) (21) (35) (42))
    (S7 ((7) (6 1) (5 2) (5 1 1) (4 3) (4 2 1) (4 1 1 1) (3 3 1) (3 2 2) (3 2 1 1) (3 1 1 1 1) (2 2 2 1) (2 2 1 1 1) (2 1 1 1 1 1) (1 1 1 1 1 1 1)) (21) (35) (42))))

; циклотипы строки таблицы (из данных; для строки вне данных — вычислением)
(define (gal-row-types row)
  (let ((d (assoc (car row) *gal-row-data*)))
    (if d
        (car (cdr d))
        (gal-cycle-types-of (gal-row->group row (gal-row-degree row))))))

; максимум в списке чисел
(define (gal-max-list l m)
  (cond ((null? l) m)
        ((> (car l) m) (gal-max-list (cdr l) (car l)))
        (else (gal-max-list (cdr l) m))))

; все точки генератора (списка циклов)
(define (gal-gen-points cycles acc)
  (cond ((null? cycles) acc)
        (else (gal-gen-points (cdr cycles) (append acc (car cycles))))))

; степень строки таблицы (максимум точек во всех циклах всех генераторов)
(define (gal-row-degree row)
  (gal-max-list
   (apply append (map (lambda (g) (gal-gen-points g '()))
                      (car (cdr (cdr row)))))
   1))

(define (gal-row-has-type? row n ct)
  (let ((ts (gal-row-types row)))
    (let loop ((l ts))
      (cond ((null? l) #f)
            ((equal? (car l) ct) #t)
            (else (loop (cdr l)))))))

; ---------- сверка данных строк с вычислением (для тестов) ----------

; все k-подмножества списка
(define (gal-subsets k l)
  (cond ((= k 0) '(()))
        ((null? l) '())
        (else (append (map (lambda (s) (cons (car l) s)) (gal-subsets (- k 1) (cdr l)))
                      (gal-subsets k (cdr l))))))

; все упорядоченные пары различных точек 0..n−1
(define (gal-ordered-pairs n)
  (apply append
         (map (lambda (i)
                (map (lambda (j) (list i j))
                     (filter (lambda (j) (not (= i j))) (gal-upto 0 (- n 1)))))
              (gal-upto 0 (- n 1)))))

; образ набора точек t под перестановкой-вектором g (точки вне вектора неподвижны)
(define (gal-act g t sorted)
  (let ((r (map (lambda (i) (if (< i (vlength g)) (vref g i) i)) t)))
    (if sorted (sort r <) r)))

; размеры орбит группы с образующими gens на наборах pts (по возрастанию)
(define (gal-orbit-sizes gens pts sorted)
  (let ((seen (make-hash)) (sizes '()))
    (for-each
     (lambda (p)
       (cond ((hash-has? seen p) #f)
             (else
              (let loop ((queue (list p)) (cnt 0))
                (cond ((null? queue) (set! sizes (cons cnt sizes)))
                      ((hash-has? seen (car queue)) (loop (cdr queue) cnt))
                      (else
                       (hash-set! seen (car queue) #t)
                       (loop (append (cdr queue)
                                     (map (lambda (g) (gal-act g (car queue) sorted)) gens))
                             (+ cnt 1))))))))
     pts)
    (sort sizes <)))

; (gal-row-orbit-data row n) → (P2 P3 O2): орбиты на парах, тройках, упорядоченных парах
(define (gal-row-orbit-data row n)
  (let ((gens (car (gal-row->group row n)))
        (pts (gal-upto 0 (- n 1))))
    (list (gal-orbit-sizes gens (gal-subsets 2 pts) #t)
          (gal-orbit-sizes gens (gal-subsets 3 pts) #t)
          (gal-orbit-sizes gens (gal-ordered-pairs n) #f))))

; данные строки *gal-row-data* совпадают с вычисленными по группе (имена — набор строк n)
(define (gal-row-data-ok? n names)
  (gal-all?
   (lambda (name)
     (let* ((row (gal-group-lookup n name))
            (d (assoc name *gal-row-data*)))
       (and row d
            (gal-same-set? (car (cdr d)) (gal-cycle-types-of (gal-row->group row n)))
            (equal? (cdr (cdr d)) (gal-row-orbit-data row n)))))
   names))

; значение инварианта kind строки name: P2/P3/O2 — размеры орбит группы на
; парах / тройках / упорядоченных парах; CAY — лежит ли группа в F20 (C5, D5, F20)
(define (gal-row-inv-value name kind)
  (cond ((equal? kind 'CAY) (if (member? name '(C5 D5 F20)) #t #f))
        (else (let ((d (assoc name *gal-row-data*)))
                (cond ((equal? kind 'P2) (nth d 2))
                      ((equal? kind 'P3) (nth d 3))
                      (else (nth d 4)))))))

; значение инварианта по результату резольвенты inv = (kind tr степени)
(define (gal-inv-value inv)
  (if (equal? (car inv) 'CAY)
      (if (member? 1 (nth inv 2)) #t #f)
      (nth inv 2)))

; наблюдённые типы + флаг A_n + результаты резольвент → кандидаты: строки
; таблицы, содержащие все наблюдённые типы, согласованные с дискриминантом
; (∈A_n = disc-квадрат) и с каждой резольвентой
(define (gal-candidates n types disc-square invs)
  (let loop ((rows (gal-transitive-groups n)) (acc '()))
    (cond ((null? rows) (reverse acc))
          (else
           (let* ((row (car rows))
                  (an-flag (car (cdr (cdr (cdr row))))))
             (cond ((not (equal? an-flag disc-square)) (loop (cdr rows) acc))
                   ((not (gal-all? (lambda (ct) (gal-row-has-type? row n ct)) types))
                    (loop (cdr rows) acc))
                   ((not (gal-all? (lambda (iv)
                                     (equal? (gal-row-inv-value (car row) (car iv))
                                             (gal-inv-value iv)))
                                   invs))
                    (loop (cdr rows) acc))
                   (else (loop (cdr rows) (cons (car row) acc)))))))))

; лемма о простой степени: транзитивная подгруппа S_p, p ≥ 5 простое,
; содержащая транспозицию — это S_p (Джордан)
(define (gal-lemma-prime n types)
  (cond ((not (prime? n)) #f)
        ((not (member? '(2 1 1 1 1 1) types)) #f)
        (else 'Sp)))

; ---------- кубическая резольвента квартики (Kappe–Warren) ----------

; депрессивная квартика: f = x⁴ + a x³ + b x² + c x + d → (p q r) для
; y⁴ + p y² + q y + r после x = y − a/4 (рациональные коэффициенты)
(define (gal-quartic-depress f x)
  (let* ((a (coeff f x 3)) (b (coeff f x 2)) (c (coeff f x 1)) (d0 (coeff f x 0)))
    (list (simplify (list '- b (list '/ (list '* 3 (list '^ a 2)) 8)))
          (simplify (list '+ c
                          (list '/ (list '* a b) 2)
                          (list '/ (list '* -1 (list '^ a 3)) 8)))
          (simplify (list '- d0 (list '/ (list '* a c) 4)
                          (list '/ (list '* (list '^ a 2) b) 16)
                          (list '/ (list '* 3 (list '^ a 4)) 256))))))

; кубическая резольвента в z = u²: z³ + 2p z² + (p² − 4r) z − q²; рациональные
; корни z₀ дают разложения f = (x² + ux + v)(x² − ux + w)
(define (gal-quartic-resolvent f x)
  (let* ((d (gal-quartic-depress f x))
         (p (car d)) (q (car (cdr d))) (r (car (cdr (cdr d)))))
    (list '+ (list '^ 'z 3)
          (list '* 2 p (list '^ 'z 2))
          (list '* (simplify (list '- (list '^ p 2) (list '* 4 r))) 'z)
          (list '* -1 (simplify (list '^ q 2))))))

; рациональные корни кубической резольвенты (с повторами по кратности)
(define (gal-quartic-resolvent-roots f x)
  (let* ((R (gal-quartic-resolvent f x))
         (fs (gal-factor-list R)))
    (apply append
           (map (lambda (e)
                  (let* ((g (car e)) (k (car (cdr e)))
                         (dg (galois-poly-degree g 'z)))
                    (cond ((= dg 1) (gal-replicate k
                                     (simplify (list '/ (list '* -1 (coeff g 'z 0))
                                                        (coeff g 'z 1)))))
                          (else '()))))
                fs))))

; квартика: различение кандидатов кубической резольвентой (Kappe–Warren):
; R без рациональных корней → S4 (disc не квадрат) / A4 (квадрат);
; R с 3 корнями → V4; R с 1 корнем z₀: D' = (p+z₀)² − 4r, D'·disc — квадрат
; в ℚ → C4, иначе D4. #f — не решает
(define (gal-quartic-distinguish f x disc)
  (let* ((dpr (gal-quartic-depress f x))
         (p (car dpr))
         (r (car (cdr (cdr dpr))))
         (roots (gal-quartic-resolvent-roots f x)))
    (cond ((null? roots) (if disc 'A4 'S4))
          ((= (length roots) 3) 'V4)
          ((and (not disc) (= (length roots) 1))
           (let* ((z0 (car roots))
                  (dp (simplify (list '- (list '^ (simplify (list '+ p z0)) 2)
                                          (list '* 4 r)))))
             (if (gal-rat-square? (simplify (list '* dp (galois-disc f x)))) 'C4 'D4)))
          (else #f))))

; ---------- GAL.2b: резольвенты (точно, по степенным суммам) ----------
; Резольвента по подмножествам — многочлен с корнями s_T = сумма (взвешенная)
; по набору T корней u_i = x_i + c·x_i²; степенные суммы s_T выражаются через
; степенные суммы корней (производящая функция E(t) = Σ p_m t^m/m!, включения-
; исключения по разбиениям), затем Ньютон → коэффициенты. Если все s_T различны
; (резольвента без кратных множителей), неприводимые множители ⇔ орбиты G на
; наборах T: степени множителей = размеры орбит.

; b^n для рационального b (^ рационального основания не вычисляется)
(define (gal-pow b n) (if (<= n 0) 1 (* b (gal-pow b (- n 1)))))

; (gal-binom m j) — биномиальный коэффициент
(define (gal-binom m j)
  (let loop ((i 1) (acc 1))
    (if (> i j) acc (loop (+ i 1) (/ (* acc (- (+ m 1) i)) i)))))

; коэффициенты f по возрастанию, приведённые к старшему 1
(define (gal-monic-coeffs f x)
  (let* ((cs (gal-coeffs f x)) (lc (car (reverse cs))))
    (map (lambda (c) (/ c lc)) cs)))

; сдвиг: коэффициенты g(y) = f(y + h) (синтетическое деление), список по возрастанию
(define (gal-taylor-shift cs h)
  (let* ((v (list->vector cs)) (n (- (vlength v) 1)))
    (let outer ((i 0))
      (cond ((< i n)
             (let inner ((j (- n 1)))
               (cond ((>= j i)
                      (vset! v j (+ (vref v j) (* h (vref v (+ j 1)))))
                      (inner (- j 1)))))
             (outer (+ i 1)))))
    (vector->list v)))

; степенные суммы p_0..p_M корней унитарного многочлена (тождества Ньютона)
(define (gal-power-sums cs M)
  (let* ((n (- (length cs) 1)) (c (list->vector cs)) (p (make-vector (+ M 1) 0)))
    (vset! p 0 n)
    (let loop ((m 1))
      (cond ((<= m M)
             (let ((s (if (<= m n) (* m (vref c (- n m))) 0)))
               (let inner ((i 1))
                 (cond ((<= i (min (- m 1) n))
                        (set! s (+ s (* (vref c (- n i)) (vref p (- m i)))))
                        (inner (+ i 1)))))
               (vset! p m (- s)))
             (loop (+ m 1)))))
    p))

; степенные суммы корней u_i = x_i + c·x_i^k (tr = (c . k), c = 0 — тождественно):
; Σ (x + c x^k)^m = Σ_j C(m,j) c^j p_{m+(k−1)j}
(define (gal-power-sums-u cs tr M)
  (let* ((c (car tr)) (k (cdr tr))
         (p (gal-power-sums cs (if (= c 0) M (* k M)))))
    (if (= c 0)
        p
        (let ((q (make-vector (+ M 1) 0)))
          (let loop ((m 0))
            (cond ((<= m M)
                   (vset! q m
                          (let inner ((j 0) (s 0))
                            (if (> j m) s
                                (inner (+ j 1)
                                       (+ s (* (gal-binom m j) (gal-pow c j)
                                               (vref p (+ m (* (- k 1) j)))))))))
                   (loop (+ m 1)))))
          q))))

; ряды — векторы коэффициентов t^0..t^N
(define (gal-fact m) (if (<= m 1) 1 (* m (gal-fact (- m 1)))))

; E(a t): e_m a^m, E_m = p_m/m!
(define (gal-ser-e pu a N)
  (let ((v (make-vector (+ N 1) 0)))
    (let loop ((m 0))
      (cond ((<= m N)
             (vset! v m (/ (* (vref pu m) (gal-pow a m)) (gal-fact m)))
             (loop (+ m 1)))))
    v))

(define (gal-ser-mul a b N)
  (let ((v (make-vector (+ N 1) 0)))
    (let loop ((i 0))
      (cond ((<= i N)
             (let ((ai (vref a i)))
               (cond ((not (= ai 0))
                      (let inner ((j 0))
                        (cond ((<= (+ i j) N)
                               (vset! v (+ i j) (+ (vref v (+ i j)) (* ai (vref b j))))
                               (inner (+ j 1))))))))
             (loop (+ i 1)))))
    v))

(define (gal-ser-lin terms N)   ; Σ коэф·ряд
  (let ((v (make-vector (+ N 1) 0)))
    (for-each (lambda (tm)
                (let loop ((m 0))
                  (cond ((<= m N)
                         (vset! v m (+ (vref v m) (* (car tm) (vref (car (cdr tm)) m))))
                         (loop (+ m 1))))))
              terms)
    v))

; число корней резольвенты
(define (gal-resolvent-degree kind n)
  (cond ((equal? kind 'P2) (/ (* n (- n 1)) 2))
        ((equal? kind 'P3) (/ (* n (- n 1) (- n 2)) 6))
        ((equal? kind 'O2) (* n (- n 1)))
        (else #f)))

; степенные суммы P_1..P_N корней резольвенты (вектор P_0..P_N)
(define (gal-resolvent-sums kind pu N)
  (let* ((E1 (gal-ser-e pu 1 N))
         (S (cond ((equal? kind 'P2)
                   (gal-ser-lin (list (list 1/2 (gal-ser-mul E1 E1 N))
                                      (list -1/2 (gal-ser-e pu 2 N))) N))
                  ((equal? kind 'P3)
                   (gal-ser-lin (list (list 1/6 (gal-ser-mul E1 (gal-ser-mul E1 E1 N) N))
                                      (list -1/2 (gal-ser-mul (gal-ser-e pu 2 N) E1 N))
                                      (list 1/3 (gal-ser-e pu 3 N))) N))
                  ((equal? kind 'O2)
                   (gal-ser-lin (list (list 1 (gal-ser-mul E1 (gal-ser-e pu 2 N) N))
                                      (list -1 (gal-ser-e pu 3 N))) N))
                  (else (error "gal-resolvent-sums: вид" kind))))
         (P (make-vector (+ N 1) 0)))
    (let loop ((m 0))
      (cond ((<= m N)
             (vset! P m (* (vref S m) (gal-fact m)))
             (loop (+ m 1)))))
    P))

; Ньютон: монический многочлен с суммами P_0..P_N → коэффициенты по возрастанию
(define (gal-newton-coeffs P N)
  (let ((e (make-vector (+ N 1) 0)))
    (vset! e 0 1)
    (let loop ((k 1))
      (cond ((<= k N)
             (vset! e k
                    (/ (let inner ((i 1) (s 0))
                         (if (> i k) s
                             (inner (+ i 1)
                                    (+ s (* (if (gal-odd? i) 1 -1) (vref e (- k i)) (vref P i))))))
                       k))
             (loop (+ k 1)))))
    ; коэффициент при y^(N-k) = (-1)^k e_k; по возрастанию — k от N до 0
    (map (lambda (j) (* (if (gal-odd? (- N j)) -1 1) (vref e (- N j))))
         (gal-upto 0 N))))

(define (gal-odd? i) (= (mod i 2) 1))

; многочлен из коэффициентов (по возрастанию) → выражение с целыми коэффициентами
(define (gal-coeffs->expr cs var)
  (let* ((den (apply lcm (map denom cs)))
         (ics (map (lambda (c) (* c den)) cs)))
    (cons '+ (map (lambda (i) (list '* (nth ics i) (list '^ var i)))
                  (gal-upto 0 (- (length ics) 1))))))

; разложение многочлена (коэффициенты по возрастанию) над ℚ → список (степень . кратность)
(define (gal-factor-degs cs var)
  (map (lambda (e) (cons (galois-poly-degree (car e) var) (car (cdr e))))
       (gal-factor-list (gal-coeffs->expr cs var))))


; ---------- резольвента Кэли (степень 5) ----------
; θ = Σ_{g∈F20} g·(x₀² x₁ x₄) — F20-инвариант (стабилизатор — F20, орбита под S5
; из 6 значений); R(y) = ∏_{6 смежных классов}(y − θ) — симметрична по корням и
; выражена через (a b c d) — коэффициенты депрессивного x⁵ + a x³ + b x² + c x + d
; (формулы получены интерполяцией по многочленам с целыми корнями и проверены
; на 260 примерах; тест «GAL: резольвента Кэли» сверяет их с корнями θ).
; Если R без кратных корней: рациональный корень ⇔ G ⊆ F20 (разрешима).

; коэффициенты R по возрастанию (7 штук, старший = 1)
(define (gal-cayley-coeffs a b c d)
  (list (+ (* -600000 c (gal-pow d 4)) (* 16384 (gal-pow c 6)) (* -102400 b (gal-pow c 4) d) (* 208000 (gal-pow b 2) (gal-pow c 2) (gal-pow d 2)) (* 1088 (gal-pow b 4) (gal-pow c 3)) (* -7936 (gal-pow b 5) c d) (* 64 (gal-pow b 8)) (* -128000 a (gal-pow c 3) (gal-pow d 2)) (* -80000 a b c (gal-pow d 3)) (* -1024 a (gal-pow b 2) (gal-pow c 4)) (* 37760 a (gal-pow b 3) (gal-pow c 2) d) (* -8000 a (gal-pow b 4) (gal-pow d 2)) (* -832 a (gal-pow b 6) c) (* 200000 (gal-pow a 2) (gal-pow d 4)) (* -12288 (gal-pow a 2) (gal-pow c 5)) (* -10240 (gal-pow a 2) b (gal-pow c 3) d) (* -46400 (gal-pow a 2) (gal-pow b 2) c (gal-pow d 2)) (* 4160 (gal-pow a 2) (gal-pow b 4) (gal-pow c 2)) (* -768 (gal-pow a 2) (gal-pow b 5) d) (* 76800 (gal-pow a 3) (gal-pow c 2) (gal-pow d 2)) (* -8192 (gal-pow a 3) (gal-pow b 2) (gal-pow c 3)) (* 768 (gal-pow a 3) (gal-pow b 3) c d) (* 3072 (gal-pow a 4) (gal-pow c 4)) (* 12544 (gal-pow a 4) b (gal-pow c 2) d) (* -9600 (gal-pow a 4) (gal-pow b 2) (gal-pow d 2)) (* -6336 (gal-pow a 5) c (gal-pow d 2)) (* 64 (gal-pow a 5) (gal-pow b 2) (gal-pow c 2)) (* -256 (gal-pow a 5) (gal-pow b 3) d) (* -256 (gal-pow a 6) (gal-pow c 3)) (* 1152 (gal-pow a 6) b c d) (* -1728 (gal-pow a 7) (gal-pow d 2)))
        (+ (* -100000 (gal-pow d 4)) (* 16384 (gal-pow c 5)) (* -76800 b (gal-pow c 3) d) (* 88000 (gal-pow b 2) c (gal-pow d 2)) (* 96 (gal-pow b 4) (gal-pow c 2)) (* -1856 (gal-pow b 5) d) (* -16000 a (gal-pow c 2) (gal-pow d 2)) (* 20000 a b (gal-pow d 3)) (* 2432 a (gal-pow b 2) (gal-pow c 3)) (* 3360 a (gal-pow b 3) c d) (* -64 a (gal-pow b 6)) (* -8192 (gal-pow a 2) (gal-pow c 4)) (* 8320 (gal-pow a 2) b (gal-pow c 2) d) (* -10400 (gal-pow a 2) (gal-pow b 2) (gal-pow d 2)) (* 608 (gal-pow a 2) (gal-pow b 4) c) (* 16800 (gal-pow a 3) c (gal-pow d 2)) (* -1632 (gal-pow a 3) (gal-pow b 2) (gal-pow c 2)) (* -992 (gal-pow a 3) (gal-pow b 3) d) (* 1024 (gal-pow a 4) (gal-pow c 3)) (* 3744 (gal-pow a 4) b c d) (* -3456 (gal-pow a 5) (gal-pow d 2)))
        (+ (* 6400 (gal-pow c 4)) (* -22400 b (gal-pow c 2) d) (* 10000 (gal-pow b 2) (gal-pow d 2)) (* -128 (gal-pow b 4) c) (* 8000 a c (gal-pow d 2)) (* 1216 a (gal-pow b 2) (gal-pow c 2)) (* -800 a (gal-pow b 3) d) (* -2176 (gal-pow a 2) (gal-pow c 3)) (* 1440 (gal-pow a 2) b c d) (* 16 (gal-pow a 2) (gal-pow b 4)) (* -96 (gal-pow a 3) (gal-pow b 2) c) (* 144 (gal-pow a 4) (gal-pow c 2)))
        (+ (* 1280 (gal-pow c 3)) (* -3200 b c d) (* -16 (gal-pow b 4)) (* 1000 a (gal-pow d 2)) (* 168 a (gal-pow b 2) c) (* -320 (gal-pow a 2) (gal-pow c 2)) (* -120 (gal-pow a 2) b d))
        (+ (* 160 (gal-pow c 2)) (* -200 b d) (* 8 a (gal-pow b 2)) (* -24 (gal-pow a 2) c))
        (+ (* 16 c))
        1))

; (a b c d) депрессивного многочлена по унитарным коэффициентам cs (по возрастанию)
(define (gal-depress5 cs)
  (let ((sh (gal-taylor-shift cs (- (/ (nth cs 4) 5)))))
    (list (nth sh 3) (nth sh 2) (nth sh 1) (nth sh 0))))

; ---------- результат резольвенты ----------

; степени неприводимых множителей резольвенты (по возрастанию) или #f, если есть
; кратный множитель (суммы по набору не все различны — вывод об орбитах невозможен)
(define (gal-squarefree-degrees cs)
  (let ((degs (gal-factor-degs cs 'y)))
    (if (gal-all? (lambda (d) (= (cdr d) 1)) degs)
        (sort (map car degs) <)
        #f)))

; (gal-compute-inv-with f x kind tr) → (kind tr степени) | #f
; kind: CAY (n = 5), P2 / P3 / O2 — по подмножествам корней u = x + c·x^k, tr = (c . k)
(define (gal-compute-inv-with f x kind tr)
  (let* ((cs (gal-monic-coeffs f x)) (n (- (length cs) 1)))
    (cond ((equal? kind 'CAY)
           (if (not (= n 5))
               #f
               (let* ((abcd (gal-depress5 cs))
                      (degs (gal-squarefree-degrees
                             (gal-cayley-coeffs (nth abcd 0) (nth abcd 1)
                                                (nth abcd 2) (nth abcd 3)))))
                 (if degs (list 'CAY '(0 . 1) degs) #f))))
          (else
           (let* ((N (gal-resolvent-degree kind n))
                  (pu (gal-power-sums-u cs tr N))
                  (P (gal-resolvent-sums kind pu N))
                  (degs (gal-squarefree-degrees (gal-newton-coeffs P N))))
             (if degs (list kind tr degs) #f))))))

; перебор подстановок u = x + c·x^k, пока резольвента не станет без кратных корней
(define *gal-transforms*
  '((0 . 1) (1 . 2) (-1 . 2) (1 . 3) (2 . 2) (-1 . 3) (1 . 4) (2 . 3)))

(define (gal-compute-inv f x kind)
  (if (equal? kind 'CAY)
      (gal-compute-inv-with f x kind '(0 . 1))
      (let trynext ((trs *gal-transforms*))
        (cond ((null? trs) #f)
              (else (let ((r (gal-compute-inv-with f x kind (car trs))))
                      (if r r (trynext (cdr trs)))))))))

; виды резольвент по степени (порядок попыток)
(define *gal-inv-kinds*
  '((5 CAY O2 P2) (6 O2 P3 P2) (7 P3 O2 P2)))

; инвариант kind различает хоть двух кандидатов?
(define (gal-informative? cands kind)
  (let ((vs (map (lambda (nm) (gal-row-inv-value nm kind)) cands)))
    (not (gal-all? (lambda (v) (equal? v (car vs))) vs))))

; добавить резольвенты, пока кандидатов > 1 и есть различающие инварианты;
; failed — виды, для которых все подстановки дали кратные корни
; → (invs failed)
(define (gal-add-resolvents f x n types sq invs failed)
  (let ((m (assoc n *gal-inv-kinds*)))
    (let loop ((ks (if m (cdr m) '())) (invs invs) (failed failed))
      (cond ((null? ks) (list invs failed))
            (else
             (let ((cands (gal-candidates n types sq invs))
                   (k (car ks)))
               (cond ((<= (length cands) 1) (list invs failed))
                     ((or (assoc k invs) (member? k failed)
                          (not (gal-informative? cands k)))
                      (loop (cdr ks) invs failed))
                     (else
                      (let ((r (gal-compute-inv f x k)))
                        (if r
                            (loop (cdr ks) (append invs (list r)) failed)
                            (loop (cdr ks) invs (cons k failed))))))))))))

; ---------- простые: накопление типов Дедекинда ----------

; добавить в хеш h (тип → частота) типы разложения f mod p для простых из primes
(define (gal-scan-primes! h f x disc lc primes)
  (define cs (gal-coeffs f x))
  (for-each
   (lambda (p)
     (cond ((or (= (mod disc p) 0) (= (mod lc p) 0)) #f)
           (else
            (let ((t (gal-modp-type-cs cs p)))
              (cond ((equal? t #f) #f)
                    (else
                     (let ((ct (sort t >)))
                       (hash-set! h ct (+ 1 (hash-ref h ct 0))))))))))
   primes))

; порции простых: после каждой — резольвенты (если ещё > 1 кандидата)
(define *gal-batches* '(100 250))

; ---------- шаги (ST.3г-1) ----------
(define (gal-mp e) (try (math-print e) (lambda (err) (to-string e))))

(define (gal-make-group f x n name types ps d sq invs extra)
  (let* ((row (gal-group-lookup n name))
        (lem (gal-lemma-prime n types))
        (res (list :group name (car (cdr row))
                   :certificate
                   (append (list :types types :primes ps :disc d :disc-square sq
                                 :irreducible #t :lemmas (if lem (list lem) '())
                                 :resolvents invs)
                           extra))))
    (if (step-log-enabled?)
        (begin
          (record-step 'gal-irreducible "Неприводимость над Q"
                       "factor-list: ровно один множитель степени n"
                       (list 'galois-group f x) (list 'deg n) 'main)
          (record-step 'gal-discriminant "Дискриминант"
                       (string-append "D = " (gal-mp d)
                                      (if sq " — точный квадрат ⇒ G ⊆ A_n"
                                          " — не квадрат ⇒ G ⊄ A_n"))
                       d sq 'main)
          (record-step 'gal-cycles "Типы циклов по простым (Дедекинд)"
                       (string-append "типы: " (gal-mp types)
                                      "; f mod p раскладывается на множители этих степеней")
                       ps types 'main)
          (if (pair? invs)
              (record-step 'gal-resolvents "Резольвенты"
                           "степени неприводимых множителей после точной факторизации"
                           (map car invs) invs 'main))
          (record-step 'gal-candidates "Отсев кандидатов"
                       (string-append "типы Дедекинда + A_n + резольвенты ("
                                      (to-string (length invs)) ") оставляют одну группу")
                       (list 'кандидаты 'до 'отсева) name 'main)
          (record-step 'gal-conclusion "Группа Галуа"
                       (string-append "единственная согласованная группа: " (to-string name))
                       (list 'galois-group f x) name 'main)
          (record-step 'gal-check "Проверка сертификата"
                       (if (galois-group-check f x res)
                           "пересчёт типов, резольвент и кандидатов: сертификат принят"
                           "сертификат не принят")
                       res (galois-group-check f x res) 'detail)))
    res))

; (galois-group f x) → (:group имя порядок :certificate c) | (:candidates …) | unknown
; c = (:types наблюдённые :primes ps :disc d :disc-square b :irreducible b
;       :lemmas (…) :resolvents ((вид (c . k) степени-множителей) …) [:quartic-resolvent имя])
; Простые набираются порциями (100, 250); после каждой порции — резольвенты
; (Кэли для n = 5; суммы по парам/тройкам/упорядоченным парам для n = 6, 7), только
; различающие оставшихся кандидатов. Как только остаётся один кандидат — стоп.
(define (galois-group f x)
  (let ((n (galois-poly-degree f x)))
    (cond ((or (< n 2) (> n 7)) 'unknown)
          ((not (galois-irreducible? f x)) 'unknown)
          (else
           (let* ((d (galois-disc f x))
                  (sq (gal-rat-square? d))
                  (lc (gal-lc f x))
                  (h (make-hash)))
             (let scan ((bs *gal-batches*) (prev 1) (ps '()) (invs '()) (failed '()))
               (cond
                 ((null? bs)
                  (let ((cands (gal-candidates n (hash-keys h) sq invs)))
                    (cond ((null? cands) 'unknown)
                          (else (list :candidates cands)))))
                 (else
                  (let* ((new (filter (lambda (p) (> p prev)) (primes-up-to (car bs))))
                         (ps2 (append ps new)))
                    (gal-scan-primes! h f x d lc new)
                    (let* ((types (hash-keys h))
                           (r (gal-add-resolvents f x n types sq invs failed))
                           (invs2 (car r))
                           (failed2 (car (cdr r)))
                           (cands (gal-candidates n types sq invs2)))
                      (cond ((null? cands) 'unknown)
                            ((= (length cands) 1)
                             (gal-make-group f x n (car cands) types ps2 d sq invs2 '()))
                            ((= n 4)
                             (let ((q (gal-quartic-distinguish f x sq)))
                               (cond ((and (symbol? q) (member? q cands))
                                      (gal-make-group f x n q types ps2 d sq invs2
                                                      (list :quartic-resolvent q)))
                                     (else (scan (cdr bs) (car bs) ps2 invs2 failed2)))))
                            (else (scan (cdr bs) (car bs) ps2 invs2 failed2)))))))))))))

; значение по ключу в плоском списке (:k1 v1 :k2 v2 …)
(define (gal-cert-get cert key)
  (let loop ((l cert))
    (cond ((null? l) #f)
          ((null? (cdr l)) #f)
          ((equal? (car l) key) (car (cdr l)))
          (else (loop (cdr (cdr l)))))))

; два списка — одно и то же множество (по equal?)
(define (gal-same-set? a b)
  (and (= (length a) (length b))
       (gal-all? (lambda (e) (member? e b)) a)
       (gal-all? (lambda (e) (member? e a)) b)))

; (galois-group-check f x res) — независимая проверка результата:
; пересчёт дискриминанта/неприводимости; для :group — заявленная группа
; содержит все наблюдённые типы (порция простых из сертификата), порядок
; совпадает, типы и каждая резольвента сертификата пересчитываются заново
; (резольвента — точная факторизация без кратных множителей), и ни одна другая
; строка таблицы не согласована с пересчитанным (типы, A_n-флаг, резольвенты,
; для квартики — резольвента Kappe–Warren); для :candidates — пересчёт даёт тот же список
(define (galois-group-check f x res)
  (try (if (gal-group-check-core f x res) #t #f)
       (lambda (e) #f)))      ; искажённый сертификат — не принят, а не ошибка

(define (gal-group-check-core f x res)
  (and (list? res)
       (let ((n (galois-poly-degree f x)))
         (cond ((equal? (car res) :group)
                (let* ((name (car (cdr res)))
                       (cert (car (cdr (cdr (cdr (cdr res))))))
                       (types (gal-cert-get cert :types))
                       (ps (gal-cert-get cert :primes))
                       (invs (let ((v (gal-cert-get cert :resolvents))) (if v v '())))
                       (row (gal-group-lookup n name)))
                  (and row
                       (galois-irreducible? f x)
                       (equal? (car (cdr (cdr res))) (car (cdr row)))
                       (gal-all? (lambda (ct) (gal-row-has-type? row n ct)) types)
                       ; пересчёт: по тем же простым ровно эти типы
                       (gal-same-set? types (map car (galois-cycle-types f x ps)))
                       ; пересчёт резольвент: точно те же степени множителей
                       (gal-all? (lambda (iv)
                                   (and (list? iv) (= (length iv) 3)
                                        (equal? (gal-compute-inv-with f x (car iv) (nth iv 1))
                                                iv)))
                                 invs)
                       (let* ((sq (gal-rat-square? (galois-disc f x)))
                              (cands (gal-candidates n types sq invs)))
                         (cond ((= (length cands) 1) (equal? (car cands) name))
                               ((= n 4)
                                (let ((r (gal-quartic-distinguish f x sq)))
                                  (and (symbol? r) (equal? r name)
                                       (member? name cands))))
                               (else #f))))))
               ((equal? (car res) :candidates)
                (let ((fresh (galois-group f x)))
                  (and (list? fresh) (equal? (car fresh) :candidates)
                       (equal? (car (cdr res)) (car (cdr fresh))))))
               (else #f)))))

; ---------- GAL.3: разрешимость в радикалах ----------

; группа таблицы разрешима? (флаг строки)
(define (gal-row-solvable name n)
  (car (cdr (cdr (cdr (cdr (gal-group-lookup n name)))))))

; вердикт по результату galois-group для неприводимого f степени n:
; (вердикт :group имя) | (вердикт :candidates (имена)) | (unknown); вердикт — #t/#f только
; когда доказан: единственная группа (с пройденной проверкой сертификата) или все
; оставшиеся кандидаты одного рода — истинная группа среди них (каждый отброшенный
; исключён точным сертификатом: типы Дедекинда, дискриминант, резольвенты)
(define (gal-verdict-of f x n r)
  (cond ((and (list? r) (equal? (car r) :group))
         (if (galois-group-check f x r)
             (list (gal-row-solvable (nth r 1) n) :group (nth r 1))
             (list 'unknown)))
        ((and (list? r) (equal? (car r) :candidates))
         (let ((fl (map (lambda (nm) (gal-row-solvable nm n)) (nth r 1))))
           (cond ((gal-all? (lambda (v) (equal? v #t)) fl) (list #t :candidates (nth r 1)))
                 ((gal-all? (lambda (v) (equal? v #f)) fl) (list #f :candidates (nth r 1)))
                 (else (list 'unknown)))))
        (else (list 'unknown))))

; (galois-solvability f x) — для неприводимого над ℚ многочлена f степени 2…7:
; (#t :group имя) | (#f :group имя) | (#t :candidates (…)) | (#f :candidates (…)) | (unknown);
; степень ≤ 4 — разрешим всегда (формулы Кардано/Феррари; группа не вычисляется): (#t :degree n)
(define (galois-solvability f x)
  (try
   (let ((n (galois-poly-degree f x)))
     (let ((res (cond ((< n 1) (list 'unknown))
                      ((not (galois-irreducible? f x)) (list 'unknown))
                      ((<= n 4) (list #t :degree n))
                      ((> n 7) (list 'unknown))
                      (else (gal-verdict-of f x n (galois-group f x))))))
       (if (step-log-enabled?)
           (record-step 'gal-solvability "Разрешимость в радикалах"
                        (cond ((and (list? res) (equal? (car res) #t) (>= (length res) 2)
                                    (equal? (nth res 1) :degree))
                               "степень ≤ 4: формулы Кардано/Феррари — разрешимо")
                              ((and (list? res) (equal? (car res) #t))
                               "группа разрешима (ряд композиции; A₅ не содержится) ⇒ корни в радикалах")
                              ((and (list? res) (equal? (car res) #f))
                               "группа не разрешима (содержит A₅) ⇒ корни не в радикалах")
                              (else "разрешимость не доказана: кандидаты разных родов"))
                        f res 'main))
       res))
   (lambda (e) (list 'unknown))))

; (solvable-by-radicals? f x) → #t / #f / unknown: корни многочлена f выражаются в радикалах
; над ℚ ⇔ группа Галуа каждого неприводимого множителя разрешима. #f — только при доказанно
; неразрешимой группе (сертификат galois-group); степень множителя > 7 или нечисловые
; коэффициенты — unknown (если нет множителя с #f)
(define (solvable-by-radicals? f x)
  (try
   (let* ((fl (cdr (factor-list f)))
          (vs (map (lambda (pe) (car (galois-solvability (car pe) x)))
                   (filter (lambda (pe) (>= (galois-poly-degree (car pe) x) 1)) fl))))
     (let ((res (cond ((any? (lambda (v) (equal? v #f)) vs) #f)
                      ((gal-all? (lambda (v) (equal? v #t)) vs) #t)
                      (else 'unknown))))
       (if (step-log-enabled?)
           (record-step 'gal-radicals "Выражение корней радикалами"
                        (cond ((equal? res #t) "все неприводимые множители имеют разрешимую группу")
                              ((equal? res #f) "есть множитель с неразрешимой группой")
                              (else "есть множитель с недоказанной разрешимостью"))
                        (list 'solvable-by-radicals? f x) res 'main))
       res))
   (lambda (e) 'unknown)))
