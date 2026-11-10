
; curves.lisp — плоские алгебраические кривые: особые точки, род (21m A3.1)
;
; Особые точки (аффинные и бесконечно удалённые) системы F = F_x = F_y = 0:
; lex-базис Грёбнера (y ≻ x) → полином от x → факторизация → сопряжённые группы
; (нормальная позиция: y = s(x) mod g). Бесконечность: однородизация F_h(X,Y,Z),
; патч X = 1 (точки [1 : b : 0]).
;
; δ_P — по ветвям Пюизё в точке после сдвига (задание A3.1):
;   δ_P = Σ_ветвям δ_ветви + Σ_{i<j} I(φ_i, φ_j);
;   δ_ветви = (1/2)Σ (h_i − 1)(v_i − 1) по характеристическим парам шагов Ньютона
;   (Walker гл. IV; каспида ⟨2,3⟩: 1, y³−x⁵: 4);
;   I(φ_i, φ_j) = ord_x(φ_i − φ_j) для ветвей-графиков.
; Цикл Ньютона — собственный (cv-walk): термы (коэф-элемент поля, i, j), перебор ВСЕХ
; рёбер нижней ломаной, раскрытие сопряжённых корней характеристических многочленов:
;   ℚ — все вложения (px-all-embeddings); ℚ(α) — deg 1 в поле, deg 2 через alg-primitive
;   (оба корня: β и −p−β); deg ≥ 3 над ℚ(α) — ошибка (группа помечается unknown).
; Род: g = (d−1)(d−2)/2 − Σ_P δ_P·[число точек в группе] (Нётер).
; Абсолютная неприводимость — factor-list над ℚ + поля особых точек (эвристика).
;
; Все внутренние имена — с префиксом cv-.

(module curves
  (export singular-points curve-genus curve-singular? parametrize-curve parametrization-check
          parametrize-curve-inverse parametrization-inverse-check))
; ---------- термы: список (c i j), c — элемент поля K (#f — рациональное число) ----------

; элементные операции — обёртки над puiseux::px-el-* (K = #f — ℚ);
; рациональные числа автоматически конвертируются в элементы K.
; Башня полей: K = (tw base p q) — расширение base присоединением β с β²+pβ+q = 0
; (p, q ∈ base); элементы — (tw a b) = a + b·β, a, b ∈ base (тег — однозначность
; представления). Алгебра deg ≤ 2: поле, если T²+pT+q неприводим над base.
(define (cv-tower? K) (and (pair? K) (equal? (car K) (quote tw))))
(define (cv-tw-base K) (nth K 1))

(define (cv-el-of K a)
  (cond ((not K) a)
        ((cv-tower? K)
         (cond ((and (number? a) (rational-number? a))
                (list 'tw (puiseux::px-el-from-rat (cv-tw-base K) a)
                      (puiseux::px-el-zero (cv-tw-base K))))
               ((and (pair? a) (equal? (car a) (quote tw))) a)
               ; элемент базового поля → погружение в башню
               (else (list 'tw a (puiseux::px-el-zero (cv-tw-base K))))))
        ((and (number? a) (rational-number? a)) (puiseux::px-el-from-rat K a))
        (else a)))

(define (cv-el-zero? K a)
  (if (cv-tower? K)
      (let ((e (cv-el-of K a)))
        (and (puiseux::px-el-zero? (cv-tw-base K) (nth e 1))
             (puiseux::px-el-zero? (cv-tw-base K) (nth e 2))))
      (puiseux::px-el-zero? K (cv-el-of K a))))
(define (cv-el-add K a b)
  (if (cv-tower? K)
      (let ((x (cv-el-of K a)) (y (cv-el-of K b)) (B (cv-tw-base K)))
        (list 'tw (puiseux::px-el-add B (nth x 1) (nth y 1))
              (puiseux::px-el-add B (nth x 2) (nth y 2))))
      (puiseux::px-el-add K (cv-el-of K a) (cv-el-of K b))))
(define (cv-el-neg K a)
  (if (cv-tower? K)
      (let ((x (cv-el-of K a)) (B (cv-tw-base K)))
        (list 'tw (puiseux::px-el-neg B (nth x 1)) (puiseux::px-el-neg B (nth x 2))))
      (puiseux::px-el-neg K (cv-el-of K a))))
(define (cv-el-sub K a b)
  (if (cv-tower? K)
      (let ((x (cv-el-of K a)) (y (cv-el-of K b)) (B (cv-tw-base K)))
        (list 'tw (puiseux::px-el-sub B (nth x 1) (nth y 1))
              (puiseux::px-el-sub B (nth x 2) (nth y 2))))
      (puiseux::px-el-sub K (cv-el-of K a) (cv-el-of K b))))
; (a1+b1β)(a2+b2β) = a1a2 − q·b1b2 + (a1b2+a2b1 − p·b1b2)β  (β² = −pβ−q)
(define (cv-el-mul K a b)
  (if (cv-tower? K)
      (let* ((x (cv-el-of K a)) (y (cv-el-of K b)) (B (cv-tw-base K))
             (p (nth K 2)) (q (nth K 3))
             (a1 (nth x 1)) (b1 (nth x 2)) (a2 (nth y 1)) (b2 (nth y 2)))
        (list 'tw
              (puiseux::px-el-sub B (puiseux::px-el-mul B a1 a2)
                                  (puiseux::px-el-mul B q (puiseux::px-el-mul B b1 b2)))
              (puiseux::px-el-sub B (puiseux::px-el-add B (puiseux::px-el-mul B a1 b2)
                                                        (puiseux::px-el-mul B a2 b1))
                                  (puiseux::px-el-mul B p (puiseux::px-el-mul B b1 b2)))))
      (puiseux::px-el-mul K (cv-el-of K a) (cv-el-of K b))))
; 1/(c+dβ) = ((c−pd)/N + (−d/N)·β), N = c² − pcd + qd² ∈ base (норма);
; деление — покомпонентное на N (без рекурсии)
(define (cv-el-div K a b)
  (if (cv-tower? K)
      (let* ((x (cv-el-of K a)) (y (cv-el-of K b)) (B (cv-tw-base K))
             (p (nth K 2)) (q (nth K 3))
             (c (nth y 1)) (d (nth y 2))
             (N (puiseux::px-el-add B (puiseux::px-el-sub B (puiseux::px-el-mul B c c)
                                                          (puiseux::px-el-mul B p (puiseux::px-el-mul B c d)))
                                    (puiseux::px-el-mul B q (puiseux::px-el-mul B d d))))
             (oneB (puiseux::px-el-one B))
             (invN (puiseux::px-el-div B oneB N)))
        (cv-el-mul K x (list 'tw (puiseux::px-el-mul B (puiseux::px-el-sub B c (puiseux::px-el-mul B p d)) invN)
                             (puiseux::px-el-mul B (puiseux::px-el-neg B d) invN))))
      (puiseux::px-el-div K (cv-el-of K a) (cv-el-of K b))))
(define (cv-el-pow K a n)
  (if (= n 0) (cv-el-one K)
      (let loop ((k 1) (r (cv-el-of K a)))
        (if (= k n) r (loop (+ k 1) (cv-el-mul K r a))))))
(define (cv-el-zero K)
  (if (cv-tower? K)
      (list 'tw (puiseux::px-el-zero (cv-tw-base K)) (puiseux::px-el-zero (cv-tw-base K)))
      (puiseux::px-el-zero K)))
(define (cv-el-one K)
  (if (cv-tower? K)
      (list 'tw (puiseux::px-el-one (cv-tw-base K)) (puiseux::px-el-zero (cv-tw-base K)))
      (puiseux::px-el-one K)))
; выражение элемента: base — px-el->expr (точно/приближённо по вложению), β —
; через корень T²+pT+q при вложении base (приближённо; ветви различаются)
(define (cv-el->expr K a)
  (if (cv-tower? K)
      (let* ((B (cv-tw-base K)) (x (cv-el-of K a))
             (p (nth K 2)) (q (nth K 3))
             (pe (puiseux::px-el->expr B p)) (qe (puiseux::px-el->expr B q)))
        (simplify (list '+ (puiseux::px-el->expr B (nth x 1))
                        (list '* (puiseux::px-el->expr B (nth x 2))
                              (list '/ (list '+ (list '* -1 pe)
                                             (list '^ (list '- (list '* pe pe) (list '* 4 qe)) 1/2))
                                   2)))))
      (puiseux::px-el->expr K a)))

; выражение ℚ[x,y] → термы (c i j), c ∈ ℚ
(define (cv-terms F x y)
  (let loop ((rows (coefficients F y)) (j 0) (acc '()))
    (if (null? rows) acc
        (loop (cdr rows) (+ j 1)
              (let iloop ((cs (coefficients (car rows) x)) (i 0) (acc2 acc))
                (if (null? cs) acc2
                    (iloop (cdr cs) (+ i 1)
                           (if (equal? (simplify (car cs)) 0) acc2
                               (cons (list (simplify (car cs)) i j) acc2)))))))))

; просуммировать термы с одинаковыми (i j)
(define (cv-agg terms K)
  (let loop ((l terms) (acc '()))
    (if (null? l) (filter (lambda (t) (not (cv-el-zero? K (car t)))) acc)
        (let* ((t (car l))
               (hit (let seek ((u acc))
                      (cond ((null? u) #f)
                            ((and (= (nth (car u) 1) (nth t 1))
                                  (= (nth (car u) 2) (nth t 2))) (car u))
                            (else (seek (cdr u)))))))
          (loop (cdr l)
                (if hit
                    (map (lambda (u) (if (equal? u hit)
                                         (list (cv-el-add K (car u) (car t)) (nth u 1) (nth u 2))
                                         u)) acc)
                    (cons t acc)))))))

; сдвиг кривой в точку (a, b): x := a + u, y := b + v; a, b — элементы K (#f — ℚ)
(define (cv-shift terms a b K)
  (cv-shift-y
   (cv-agg
    (apply append
           (map (lambda (t)
                  (map (lambda (p)      ; c·binom(i,p)·a^{i−p}·u^p
                         (list (cv-el-mul K (cv-el-mul K (car t) (cv-binom (nth t 1) p))
                                          (cv-el-pow K a (- (nth t 1) p)))
                               p (nth t 2)))
                       (cv-range (+ (nth t 1) 1))))
                terms))
    K)
   b K))

; сдвиг по y на термах от (u, y)
(define (cv-shift-y terms b K)
  (cv-agg
   (apply append
          (map (lambda (t)
                 (map (lambda (r)      ; c·binom(j,r)·b^{j−r}·v^r
                       (list (cv-el-mul K (cv-el-mul K (car t) (cv-binom (nth t 2) r))
                                        (cv-el-pow K b (- (nth t 2) r)))
                             (nth t 1) r))
                     (cv-range (+ (nth t 2) 1))))
               terms))
   K))

(define (cv-range n) (let loop ((k 0) (acc '())) (if (= k n) (reverse acc) (loop (+ k 1) (cons k acc)))))

(define (cv-binom n k)
  (if (or (< k 0) (> k n)) 0
      (simplify (list '/ (cv-fact n) (* (cv-fact k) (cv-fact (- n k)))))))

(define (cv-fact n) (if (<= n 1) 1 (* n (cv-fact (- n 1)))))

; кратность точки: min(i+j) по термам
(define (cv-terms-mult terms)
  (foldl (lambda (m t) (min m (+ (nth t 1) (nth t 2)))) 1000000 terms))
; ---------- многоугольник Ньютона и характеристические многочлены ----------

; нижняя ломаная термов → список рёбер (h v m): примитивные (h > 0),
; m = h·vx + v·vy — баланс ребра (константа на ребре)
(define (cv-edges terms)
  (let* ((pts (cv-uniq-points (map (lambda (t) (list (nth t 1) (nth t 2))) terms)))
         (hull (reverse (puiseux::px-lower-hull pts))))
    (if (< (length hull) 2) '()
        (let loop ((l hull) (acc '()))
          (if (null? (cdr l)) (reverse acc)
              (let* ((p0 (car l)) (p1 (cadr l))
                     (dvx (- (nth p1 0) (nth p0 0))) (dvy (- (nth p1 1) (nth p0 1))))
                (if (= dvy 0)
                    (loop (cdr l) acc)
                    (let* ((g (gcd dvx (abs dvy)))
                           (hh (quotient (abs dvy) g))
                           (vv0 (quotient dvx g))
                           (vv (if (< dvy 0) vv0 (- vv0)))
                           (mm (+ (* hh (nth p0 0)) (* vv (nth p0 1)))))
                      (loop (cdr l) (cons (list hh vv mm) acc))))))))))

; уникальные опорные точки: по каждому x — только минимальный y (как px-lower-hull;
; вертикальные цепочки схлопываются — вертикальное «ребро» не даёт ветвей,
; ряд заканчивается константой)
(define (cv-uniq-points pts)
  (let* ((sorted (sort pts (lambda (a b)
                             (if (= (nth a 0) (nth b 0))
                                 (< (nth a 1) (nth b 1))
                                 (< (nth a 0) (nth b 0))))))
         (uniq (let loop ((l sorted) (acc '()))
                 (cond ((null? l) (reverse acc))
                       ((and (not (null? acc)) (= (nth (car l) 0) (nth (car acc) 0)))
                        (loop (cdr l) acc))
                       (else (loop (cdr l) (cons (car l) acc)))))))
    (if (= (length uniq) 1) (list (car uniq))
        (let loop ((rest (cdr uniq)) (h (list (car uniq))))
          (if (null? rest) h
              (let push ((p (car rest)) (stk h))
                (if (and (>= (length stk) 2)
                         (<= (cv-cross (nth stk 1) (nth stk 0) p) 0))
                    (push p (cdr stk))
                    (loop (cdr rest) (cons p stk)))))))))

; векторное произведение (a→b)×(a→c)
(define (cv-cross a b c)
  (- (* (- (nth b 0) (nth a 0)) (- (nth c 1) (nth a 1)))
     (* (- (nth b 1) (nth a 1)) (- (nth c 0) (nth a 0)))))

; характеристический многочлен ребра (h v m): Σ c·T^vy по мономам на ребре
(define (cv-charpoly terms edge K)
  (let* ((hh (nth edge 0)) (vh (nth edge 1)) (m (nth edge 2))
         (on (filter (lambda (t) (= (+ (* hh (nth t 1)) (* vh (nth t 2))) m)) terms))
         (deg (foldl (lambda (acc t) (max acc (nth t 2))) 0 on))
         (cs0 (puiseux::px-make-list (+ deg 1) (cv-el-zero K))))
    (cv-poly-trim
     (let loop ((l on) (cs cs0))
       (if (null? l) cs
           (let ((vy (nth (car l) 2)))
             (loop (cdr l)
                   (puiseux::px-list-set cs vy
                                         (cv-el-add K (nth cs vy) (car (car l))))))))
     K)))

; все корни многочлена (коэффициенты-элементы K) с полным раскрытием сопряжённых:
; → список (K' корень); deg 1 — в K; deg 2 над K≠ℚ — башня (tw K p q) (β и −p−β);
; K = ℚ — все вложения; deg ≥ 3 над K≠ℚ — ошибка cv: unknown-roots.
; Ведущие нулевые коэффициенты → корень 0 в исходном поле K
(define (cv-roots K cs)
  (let loop ((cs cs))
    (cond ((null? cs) '())
          ((cv-el-zero? K (car cs))
           (cons (list K (cv-el-zero K)) (loop (cdr cs))))
          (else (cv-roots-nonzero K cs)))))

; обрезка ведущих нулей полинома над K (в т.ч. башней)
(define (cv-poly-trim p K)
  (let loop ((l (reverse p)))
    (if (and (pair? l) (cv-el-zero? K (car l))) (loop (cdr l)) (reverse l))))

; монизация полинома над K (в т.ч. башней) — делим на старший коэффициент
(define (cv-monicize K cs)
  (let* ((t (let loop ((l (reverse cs)))
              (if (cv-el-zero? K (car l)) (loop (cdr l)) (reverse l))))
         (lc (last t))
         (inv (cv-el-div K (cv-el-one K) lc)))
    (map (lambda (a) (cv-el-mul K a inv)) t)))

(define (cv-roots-nonzero K cs)
  (let* ((mono (cv-monicize K cs))
         ; deg ≤ 2 над K≠ℚ — без факторизации (башня); deg ≥ 3 — факторизация:
         ; над alg-полем — alg-factor, над башней — не поддерживается
         (facs (cond ((not K) (puiseux::px-factor-pairs #f mono))
                     ((<= (- (length mono) 1) 2) (list (list mono 1)))
                     ((cv-tower? K) (error "cv: unknown-roots (deg ≥ 3 над башней полей)"))
                     (else (nth (alg-factor K mono 'T) 1)))))
    (apply append
           (map (lambda (fk) (cv-roots-factor K fk)) facs))))

; корни одного фактора (g k): deg 1 — в K; deg 2 над K≠ℚ — расширение-башня
; (tw K p q): β² + pβ + q = 0, β и −p−β (второй корень); K = ℚ — все вложения
(define (cv-roots-factor K fk)
  (let* ((g (car fk)) (d (- (length g) 1)))
    (cond ((= d 0) '())
          ((= d 1) (list (list K (cv-el-div K (cv-el-neg K (nth g 0)) (nth g 1)))))
          ((not K)
           (let* ((res (puiseux::px-int-scale g))
                  (m (puiseux::px-nums->expr (nth res 0) 't))
                  (M (nth res 1))
                  (embs (puiseux::px-all-embeddings m 't)))
             (map (lambda (e)
                    (let ((L (alg-field (simplify m) 't e)))
                      (list L (alg-elt L (list 0 (simplify (list '/ 1 M)))))))
                  embs)))
          (else
           ; g = T² + pT + q (монический): D = p²−4q; D = 0 в K — вырожденный случай
           ; (кратный корень β = −p/2 ∈ K, башня необратима — норма N = 0)
           (let* ((p (nth g 1)) (q (nth g 0))
                  (D (cv-el-sub K (cv-el-mul K p p)
                                 (cv-el-mul K (cv-el-of K 4) q))))
             (if (cv-el-zero? K D)
                 (list (list K (cv-el-div K (cv-el-neg K p) (cv-el-of K 2))))
                 (let* ((L (list 'tw K p q))
                        (beta (list 'tw (cv-el-zero K) (cv-el-one K)))
                        (beta2 (list 'tw (cv-el-neg K p) (cv-el-neg K (cv-el-one K)))))
                   (list (list L beta) (list L beta2)))))))))
; подстановка шага: x = ξ^h, z = ξ^v·(c + w) на термах от (x, z);
; затем выносим общий множитель ξ^val (минимальный ξ-порядок) — иначе показатели
; не убывают и рекурсия зацикливается (как px-shift-laurent в puiseux)
(define (cv-step-subst terms h v c K2)
  (cv-strip-val
   (cv-agg
    (apply append
           (map (lambda (t)
                  (cv-binom-expand (car t) (+ (* h (nth t 1)) (* v (nth t 2)))
                                   (nth t 2) v c K2))
               terms))
    K2)
   K2))

; вынести ξ^val: минимальный ξ-порядок термов (w-степени учитываются как есть)
(define (cv-strip-val terms K)
  (let ((val (foldl (lambda (acc t) (min acc (nth t 1))) 1000000 terms)))
    (if (>= val 1000000) terms
        (map (lambda (t) (list (car t) (- (nth t 1) val) (nth t 2))) terms))))

; c·ξ^m·(c₀ + w)^j → термы (коэф, ξ-показатель m, w-степень r):
; (c₀ + w)^j = Σ binom(j,r)·c₀^{j−r}·w^r (без ξ-степеней у w!)
(define (cv-binom-expand c m j v c0 K2)
  (map (lambda (r)
         (list (cv-el-mul K2 (cv-el-mul K2 c (cv-binom j r)) (cv-el-pow K2 c0 (- j r)))
               m r))
       (cv-range (+ j 1))))

; регулярность: G(0, w) = a·w + O(w²), a ≠ 0 — есть терм (0 1) с ненулевым коэф.
; и нет терма (0 0) (тогда по теореме о неявной функции z = ряд по x; как
; px-regular-at-zero? в puiseux — высшие w-степени не мешают Тейлору).
; Раньше требовался ровно один терм на грани — walk дрейфовал по рёбрам (1 1),
; биномиальный взрыв коэффициентов, десятки шагов (астроид ~40 с на группу)
(define (cv-regular? terms K)
  (let loop ((l terms))
    (cond ((null? l) #f)
          ((and (= (nth (car l) 1) 0) (= (nth (car l) 2) 0)) #f)
          ((and (= (nth (car l) 1) 0) (= (nth (car l) 2) 1)
                (not (cv-el-zero? K (car (car l))))) #t)
          (else (loop (cdr l))))))
(define (cv-diff-terms terms K)
  (filter (lambda (t) (not (cv-el-zero? K (car t))))
          (map (lambda (t) (list (cv-el-mul K (car t) (nth t 2))
                                 (nth t 1) (- (nth t 2) 1)))
               terms)))

; терм с минимальным ξ-порядком среди w-степени 0; #f — все нули
(define (cv-minord terms K)
  (let loop ((l (sort (filter (lambda (t) (= (nth t 2) 0)) terms)
                      (lambda (u w) (< (nth u 1) (nth w 1))))))
    (cond ((null? l) #f)
          ((cv-el-zero? K (car (car l))) (loop (cdr l)))
          (else (car l)))))

; регулярный случай: ряд Тейлора z(ξ) = Σ d_k ξ^k неопределёнными коэффициентами
(define (cv-taylor terms K n)
  (let loop ((F terms) (shift 0) (acc '()))
    (if (>= (length acc) n) acc
        (let* ((A (cv-minord F K))
               (B (cv-minord (cv-diff-terms F K) K)))
          (if (or (not A) (not B)) acc
              (let* ((va (nth A 1)) (vb (nth B 1))
                     (k (- va vb))
                     (pos (+ shift k))
                     (d (cv-el-div K (cv-el-neg K (car A)) (car B))))
                (if (or (< k 1) (> pos n) (< pos (+ 1 (length acc)))) acc
                    (let* ((acc2 (append acc (puiseux::px-make-list (- pos 1 (length acc))
                                                                    (cv-el-zero K)) (list d)))
                           (Fnext (cv-agg (apply append (map (lambda (t) (cv-tsub t d k K)) F)) K)))
                      (loop Fnext (+ shift k) acc2)))))))))

; подстановка z := d·ξ^k + ξ^k·w в терм (c i j): c·binom(j,r)·d^{j−r}·ξ^{i+k·j}·w^r
(define (cv-tsub t d k K)
  (map (lambda (r)
         (list (cv-el-mul K (cv-el-mul K (car t) (cv-binom (nth t 2) r))
                          (cv-el-pow K d (- (nth t 2) r)))
               (+ (nth t 1) (* k (nth t 2))) r))
       (cv-range (+ (nth t 2) 1))))

; все ветви: (1) сдвиг-нормализация по w: пока G(0, w) ≠ 0 — корень d = −A/B,
; подстановка w := d + w₁ (k = 0; как px-taylor при регулярном/нерегулярном случае);
; (2) G(0, w) ≡ 0 → многоугольник (перебор всех рёбер); (3) регулярность → ряд Тейлора
(define (cv-walk terms K n depth)
  (if (> depth 30)
      '()
      (cond ((cv-regular? terms K)
             (let ((ds (cv-taylor terms K (+ n 1))))
               (list (list 1 (cv-pack-taylor ds K) '()))))
            ((cv-terms-have-w0? terms K)
             ; G(0,w) ≠ 0, но не регулярна: корни d полинома G(0, w) (по w) —
             ; сдвиг w := d + w₁ (терм (d, 0)), как «ребро» (h=1, v=0)
             (let* ((pw (cv-poly-w0 terms K))
                    (ds (cv-roots K pw)))
               (apply append
                     (map (lambda (rc)
                            (cv-walk-root terms K n depth '(1 0 0) 1 0 rc pw))
                          ds))))
            (else
             ; страховка: общий множитель w^k у термов с ξ-порядком 0 после подстановок
             ; мешает Ньютоновской нижней грани (шаги не уменьшают кратность — дрейф)
             (let ((terms (cv-normalize-w terms K)))
             (let loop ((edges (cv-edges terms)) (acc '()))
               (if (null? edges)
                   (if (null? acc)
                       (list (list 1 '() '()))
                       (reverse acc))
                   (loop (cdr edges)
                         (append (cv-walk-edge terms K n depth (car edges)) acc)))))))))

(define (cv-poly-w0 terms K)
  (let* ((cs0 (filter (lambda (t) (= (nth t 1) 0)) terms))
         (deg (foldl (lambda (acc t) (max acc (nth t 2))) 0 cs0))
         (cs (puiseux::px-make-list (+ deg 1) (cv-el-zero K))))
    (cv-poly-trim
     (let loop ((l cs0) (cs cs))
       (if (null? l) cs
           (let ((j (nth (car l) 2)))
             (loop (cdr l)
                   (puiseux::px-list-set cs j
                                         (cv-el-add K (nth cs j) (car (car l))))))))
     K)))

; есть терм с w-степенью 0 и ξ-порядком 0 (свободный член G(0, w) ≠ 0)?
(define (cv-terms-have-w0? terms K)
  (let loop ((l terms))
    (cond ((null? l) #f)
          ((and (= (nth (car l) 1) 0) (= (nth (car l) 2) 0)
                (not (cv-el-zero? K (car (car l))))) #t)
          (else (loop (cdr l))))))

; нормализация по w: вынесение общего множителя w^k (если G ≡ 0 по w при ξ=0... 
; нормализация по w: вынесение общего множителя w^k — законно, только если w-степень ≥ k
; у ВСЕХ термов (вычитание лишь у ξ=0-термов даёт отрицательные w-степени
; у остальных и ломает нижнюю ломаную). Страховка от дрейфа (шаги по ребру
; не уменьшают кратность)
(define (cv-normalize-w terms K)
  (let ((vw (foldl (lambda (acc t) (min acc (nth t 2))) 1000000 terms)))
    (if (or (>= vw 1000000) (<= vw 0)) terms
        (map (lambda (t) (list (car t) (nth t 1) (- (nth t 2) vw))) terms))))
; упаковка ряда Тейлора: ((элемент-выражение k)), нулевые пропускаем
(define (cv-pack-taylor ds K)
  (let loop ((l ds) (k 1) (acc '()))
    (if (null? l) (reverse acc)
        (loop (cdr l) (+ k 1)
              (if (cv-el-zero? K (car l)) acc
                  (cons (list (cv-el->expr K (car l)) k) acc))))))

; шаг по ребру (h v m): корни φ(T) → подстановка → рекурсия
; шаг по ребру (h v m): корни φ(T) → подстановка → рекурсия
(define (cv-walk-edge terms K n depth edge)
  (let* ((phi (cv-charpoly terms edge K))
         ; только ненулевые корни: c = 0 не лежит на ребре (ветвь покрывается другим ребром)
         (rcs (filter (lambda (rc) (not (cv-el-zero? (nth rc 0) (nth rc 1)))) (cv-roots K phi)))
         (h (nth edge 0)) (v (nth edge 1)))
    (apply append
           (map (lambda (rc) (cv-walk-root terms K n depth edge h v rc phi)) rcs))))

; один корень c ребра: x = ξ^h, z = ξ^v(c + w); терм (c, v/h), хвост: e ↦ v/h + e/h
(define (cv-walk-root terms K n depth edge h v rc phi)
  (let* ((K2 (nth rc 0)) (c (nth rc 1))
         (mu (simplify (list '/ v h))))
    (if (and (integer? mu)
             (cv-el-poly-multiple-root? phi K2 c))
        (cv-walk-root-shift terms K n depth h v c K2 mu)
        (let* ((G (cv-step-subst terms h v c K2))
         (sub (cv-walk G K2 (* n h) (+ depth 1))))
    (map (lambda (br)
           (list (* h (nth br 0))
                 (append (if (cv-el-zero? K2 c) '()
                            (list (list (cv-el->expr K2 c) mu)))
                         (filter (lambda (tm) (<= (nth tm 1) n))
                                 (map (lambda (tm)
                                        (list (nth tm 0)
                                              (simplify (list '+ mu (list '/ (nth tm 1) h)))))
                                      (nth br 1))))
                 (cons (list h v) (nth br 2))))
         sub)))))


; сдвиг-ветка walk-root: y := c·x^μ + v (аналитическая замена, μ = v/h целое,
; корень c кратный — шаг A3.1d): сохраняет характеристические пары и δ.
; Ряды: y = c·x^μ + ряды по v; q и пары — из рекурсии напрямую (не домножаем).
(define (cv-walk-root-shift terms K n depth h v c K2 mu)
  (let* ((G (cv-shift-terms-y terms mu c K2))
         (sub (cv-walk G K2 n (+ depth 1))))
    (map (lambda (br)
           (list (nth br 0)
                 (append (if (cv-el-zero? K2 c) '()
                            (list (list (cv-el->expr K2 c) mu)))
                         (filter (lambda (tm) (<= (nth tm 1) n)) (nth br 1)))
                 (nth br 2)))
         sub)))

; корень c кратный в phi (список коэффициентов-элементов K)? phi(c) = 0 и phi'(c) = 0
(define (cv-el-poly-multiple-root? cs K c)
  (and (cv-el-zero? K (cv-el-poly-val cs K c))
       (cv-el-zero? K (cv-el-poly-val (cv-el-poly-deriv cs K) K c))))

; значение полинома (список коэффициентов-элементов, cs[j] при T^j) в элементе a
(define (cv-el-poly-val cs K a)
  (let loop ((l (reverse cs)) (acc (cv-el-zero K)))
    (if (null? l) acc
        (loop (cdr l) (cv-el-add K (cv-el-mul K acc a) (car l))))))

; производная полинома-списка: cs'[j] = (j+1)*cs[j+1]
(define (cv-el-poly-deriv cs K)
  (let loop ((l (cdr cs)) (k 1) (acc '()))
    (if (null? l) (reverse acc)
        (loop (cdr l) (+ k 1)
              (cons (cv-el-mul K (car l) (cv-el-of K k)) acc)))))

; аналитический сдвиг y := c*x^mu + v на термах (coef i j):
; coef*x^i*(c*x^mu + v)^j -> sum_k binom(j,k)*coef*c^k*x^(i+k*mu)*v^(j-k)
(define (cv-shift-terms-y terms mu c K)
  (cv-agg
   (apply append
          (map (lambda (t)
                 (map (lambda (k)
                        (list (cv-el-mul K (cv-el-mul K (car t) (cv-el-pow K c k))
                                          (cv-el-of K (cv-binom (nth t 2) k)))
                              (+ (nth t 1) (* k mu))
                              (- (nth t 2) k)))
                      (cv-range (+ (nth t 2) 1))))
               terms))
   K))
; ---------- δ и пересечения ----------

; δ_ветви по характеристическим парам: (1/2)Σ (h−1)(v−1)
(define (cv-branch-delta pairs)
  (simplify (list '/ (foldl (lambda (acc p) (+ acc (* (- (nth p 0) 1) (- (nth p 1) 1)))) 0 pairs) 2)))


; I(B1, B2) = q1·Σ_{ψ ∈ орбита B2} ord_x(φ1 − ψ) — пересечение геометрических ветвей:
; сумма ord_x по всем сопряжённым рядам ψ = σ^j·φ2 орбиты B2 (σ: x^{1/q} ↦ ζ_q·x^{1/q},
; коэффициент при x^e умножается на ζ_q^{j·q·e}). ord_x разности двух рядов — наименьший
; показатель e (в единицах x), где коэффициенты различаются: приводим к общему знаменателю
; Q = q1·q2 (показатели e ↦ e·Q/q_i, целые), первый различный показатель e' в единицах t
; (x = t^Q) даёт ord_x = e'/Q. Сравнение коэффициентов ТОЧНОЕ (simplify разности,
; px-coef-zero?; радикальные ζ — каноническая форма). ζ_q — радикалы для q ≤ 6
; (px-root-of-unity); q > 6 — ошибка (группа unknown).
(define (cv-ord-diff-x b1 b2)
  (let* ((q1 (nth b1 0)) (q2 (nth b2 0))
         ; Q — общий знаменатель: lcm(q1, q2); показатели e (в единицах x, дробные m/q)
         ; дают t-показатели e·Q — целые (q_i | Q)
         (Q (quotient (* q1 q2) (gcd q1 q2)))
         (t1 (map (lambda (tm) (list (nth tm 0) (* Q (nth tm 1)))) (nth b1 1)))
         (t2 (map (lambda (tm) (list (nth tm 0) (* Q (nth tm 1)))) (nth b2 1))))
    (let loop ((a t1) (b t2))
      (cond ((and (null? a) (null? b)) #f)
            ((null? a) (list 'ord (nth (car b) 1) Q))
            ((null? b) (list 'ord (nth (car a) 1) Q))
            (else
             (let ((e1 (nth (car a) 1)) (e2 (nth (car b) 1)))
               (cond ((< e1 e2) (list 'ord e1 Q))
                     ((> e1 e2) (list 'ord e2 Q))
                     (else (let ((dc (simplify (expand (list '- (nth (car a) 0) (nth (car b) 0))))))
                             (if (puiseux::px-coef-zero? dc)
                                 (loop (cdr a) (cdr b))
                                 (list 'ord e1 Q)))))))))))

; ζ_q^k-сдвиг ряда b = (q термы): коэффициент при x^e ↦ ζ_q^{k·q·e}·c.
; ζ_q — выражение-радикал (px-root-of-unity); m = q·e обязан быть целым.
; Возвращает сдвинутый ряд (q термы') или #f (нецелая ζ-степень / q > 6)
(define (cv-zeta-shift b k)
  (let* ((q (nth b 0))
         (zeta (puiseux::px-root-of-unity q)))
    (if (not zeta) #f
        (let ((zk (if (= k 0) 1 (puiseux::px-zeta-k zeta k))))
          (let loop ((ts (nth b 1)) (acc '()))
            (if (null? ts) (list q (reverse acc))
                (let* ((tm (car ts))
                       (m (* q (nth tm 1)))
                       (c (nth tm 0))
                       ; c ↦ ζ^{k·m}·c (при m = 0 или k = 0 — без изменения)
                       (f (if (or (= k 0) (= m 0)) c
                              (simplify (expand (list '* (list '^ zk m) c)))))
                       (z (puiseux::px-coef-zero? f)))
                  (if (not (integer? m)) #f
                      (loop (cdr ts) (if (or (equal? f 0) z) acc (cons (list f (nth tm 1)) acc)))))))))))

; группировка рядов в ζ-орбиты (геометрические ветви): сопряжённые ряды
; (b' = ζ^k·b, действие на коэффициенты при x^{e_j}: c_j ↦ ζ^{k·q·e_j}·c_j) —
; одна ветвь (px-conjugate-branches? из A2.2 — та же проверка); ζ выражается
; радикалами только для q ∈ {1,2,3,4,6} — прочие q не склеиваются (риск: выдача
; групп = рядов завышена; для целей δ тестовых кривых достаточно)
; q=1: ζ-орбита тривиальна — склеиваются только ТОЖДЕСТВЕННЫЕ ряды (τ-склейка
; px-conj-terms при k=0 объединяет ±β-ветви одного поля — это разные ветви);
; q>1 — px-conjugate-branches? как в A2.2; при его ошибке на комплексных
; выражениях — численная ζ-проверка (приближённая, 1e-6)
(define (cv-same-branch? b1 b2)
  (if (= (nth b1 0) 1)
      (and (equal? (map (lambda (tm) (nth tm 1)) (nth b1 1))
                   (map (lambda (tm) (nth tm 1)) (nth b2 1)))
           (equal? (map car (nth b1 1)) (map car (nth b2 1))))
      (or (try (puiseux::px-conjugate-branches? b1 b2) (lambda (err) #f))
          (cv-approx-conjugate? b1 b2))))

; численная ζ-проверка: ∃k: все j: c2_j ≈ ζ^{k·m_j}·c1_j (m_j = q·e_j — ζ-степени)
(define (cv-approx-conjugate? b1 b2)
  (let* ((q (nth b1 0))
         (ok-cols (equal? (map (lambda (tm) (nth tm 1)) (nth b1 1))
                          (map (lambda (tm) (nth tm 1)) (nth b2 1)))))
    (and ok-cols
         (let k-loop ((k 0))
           (cond ((= k q) #f)
                 ((cv-approx-conj-k q k (nth b1 1) (nth b2 1)) #t)
                 (else (k-loop (+ k 1))))))))

; комплексное численное значение expr (рекурсивный разбор: числа, %i, +, *,
; ^ с рациональными показателями — комплексный корень; прочее — eval-num, real)
(define (cv-cnum e)
  (cond ((and (number? e) (or (integer? e) (equal? (type-of e) 'rational) (equal? (type-of e) 'double))) (list e 0))
        ((and (number? e) (equal? (type-of e) 'algebraic))
         ; алгебраическое число → double (вещественное значение по вложению)
         (let ((v (try (eval-num e) (lambda (err) #f))))
           (if (number? v) (list v 0) (list 0 0))))
        ((equal? e '%i) (list 0 1))
        ((and (list? e) (equal? (car e) '+))
         (let loop ((ts (cdr e)) (acc (list 0 0)))
           (if (null? ts) acc
               (let ((c (cv-cnum (car ts))))
                 (loop (cdr ts) (list (+ (nth acc 0) (nth c 0)) (+ (nth acc 1) (nth c 1))))))))
        ((and (list? e) (equal? (car e) '*))
         (let loop ((ts (cdr e)) (acc (list 1 0)))
           (if (null? ts) acc
               (let ((c (cv-cnum (car ts))))
                 (loop (cdr ts)
                       (list (- (* (nth acc 0) (nth c 0)) (* (nth acc 1) (nth c 1)))
                             (+ (* (nth acc 0) (nth c 1)) (* (nth acc 1) (nth c 0)))))))))
        ((and (list? e) (equal? (car e) '^) (= (length e) 3))
         (let* ((b (cv-cnum (nth e 1))) (p (nth e 2)))
           (cond ((and (number? p) (= p 2)) (cv-cmul b b))
                 ((and (number? p) (= p 3)) (cv-cmul b (cv-cmul b b)))
                 ((and (number? p) (equal? p 1/2)) (cv-csqrt b))
                 (else (let ((bv (try (eval-num e) (lambda (err) #f))))
                         (if (number? bv) (list bv 0) (list 0 0)))))))
        (else (let ((bv (try (eval-num e) (lambda (err) #f))))
                (if (number? bv) (list bv 0) (list 0 0))))))

(define (cv-cmul a b)
  (list (- (* (nth a 0) (nth b 0)) (* (nth a 1) (nth b 1)))
        (+ (* (nth a 0) (nth b 1)) (* (nth a 1) (nth b 0)))))

; главный корень (неотрицательная вещественная часть); принудительно double
; (sqrt рационального создаёт algebraic — здесь нужна численная оценка)
(define (cv-csqrt a)
  (let* ((x0 (* 1.0 (nth a 0)))
         (y0 (* 1.0 (nth a 1)))
         (r (sqrt (+ (* x0 x0) (* y0 y0))))
         (re (sqrt (/ (+ r x0) 2.0))))
    (if (= re 0)
        (list 0.0 (sqrt (/ (+ r (- x0)) 2.0)))
        (list re (/ y0 (* 2.0 re))))))

; один терм-пар численной ζ-проверки: c2 = e^{i*ang*m}*c1, m = q*e
(define (cv-approx-conj-pair q ang a b)
  (let* ((e (nth a 1))
         (m (floor (* q e 1.0)))
         (rot (list (cos (* ang m)) (sin (* ang m))))
         (c1 (try (cv-cnum (car a)) (lambda (err) #f)))
         (c2 (try (cv-cnum (car b)) (lambda (err) #f))))
    (and c1 c2
         (let* ((xr (- (* (nth c1 0) (nth rot 0)) (* (nth c1 1) (nth rot 1))))
                (yr (+ (* (nth c1 0) (nth rot 1)) (* (nth c1 1) (nth rot 0))))
                (dx (- xr (nth c2 0)))
                (dy (- yr (nth c2 1)))
                (dd (sqrt (+ (* dx dx) (* dy dy)))))
           (<= dd 1e-6)))))

(define (cv-approx-conj-k q k t1 t2)
  (let ((ang (* 2 3.141592653589793 k (/ 1 q))))
    (let loop ((a t1) (b t2))
      (cond ((null? a) (null? b))
            ((null? b) #f)
            ((cv-approx-conj-pair q ang (car a) (car b)) (loop (cdr a) (cdr b)))
            (else #f)))))


; группа: (представитель ряды-орбиты) — ряды-члены нужны для суммы пересечений
; по ζ-сдвигам; cv-delta берёт число ветвей из длины орбиты
(define (cv-group-branches brs)
  (let loop ((rest brs) (acc '()))
    (if (null? rest) (reverse acc)
        (let* ((b (car rest))
               (mates (filter (lambda (b2) (cv-same-branch? b b2)) (cdr rest)))
               (others (filter (lambda (b2) (not (cv-same-branch? b b2))) (cdr rest))))
          (loop others (cons (list b (cons b mates)) acc))))))

; δ точки: (Σ_ветвям δ_ветви, Σ_{i<j} I(φ_i, φ_j)) — по ГРУППАМ (ветвям),
; не по отдельным рядам: внутри ζ-орбиты пересечения не считаются
(define (cv-delta branches)
  (let* ((groups (cv-group-branches branches))
         (reps (map car groups)))
    (list (foldl (lambda (acc b) (+ acc (cv-branch-delta (nth b 2)))) 0 reps)
          ; пересечение групп (геометрических ветвей) = Σ по ВСЕМ парам рядов-членов ord_x(φ − ψ) (показатели в x).
          ; Замечание ревью: прежний cv-intersect масштабировал показатели дважды (y⁴ − x⁶: δ = 14 вместо 8,
          ; y² = x⁶ + 1 давал род −4) и сравнивал ряды с разными q в разных единицах.
          (let outer ((l groups) (acc 0))
            (if (null? l) acc
                (outer (cdr l)
                       (+ acc (foldl (lambda (a g2) (+ a (cv-group-intersect (car l) g2)))
                                     0 (cdr l)))))))))

; пересечение геометрических ветвей (ζ-орбит): I(B1, B2) = q1·Σ_{j=0..q2−1} ord_x(φ1 − σʲφ2)
; (σʲ — ζ_q2-сдвиг представителя B2; сумма по всем сопряжённым рядам орбиты B2 —
; формула задания, равносильна сумме по парам рядов). Сдвиги — точные (cv-zeta-shift,
; ζ-радикалы q ≤ 6); q > 6 или сбой сдвига — ошибка → группа unknown (не неверный δ).
(define (cv-group-intersect g1 g2)
  (let* ((b1 (car g1)) (b2 (car g2)))
    (cv-branch-intersect b1 b2)))

; I(B1, B2) = q1·Σ_j ord_x(φ1 − σʲφ2): сдвигаем φ2 на все ζ_q2^j и суммируем
(define (cv-branch-intersect b1 b2)
  (let* ((q1 (nth b1 0)) (q2 (nth b2 0)))
    (let j-loop ((j 0) (acc 0))
      (if (>= j q2) acc
          (let* ((sh (cv-zeta-shift b2 j))
                 (o (if sh (cv-ord-diff-x b1 sh)
                        (error "cv-delta: ζ-сдвиг не удался (q > 6 или нецелые ζ-степени)"))))
            (if (not o) acc
                (j-loop (+ j 1) (+ acc (* q1 (/ (nth o 1) (nth o 2)))))))))))

; ord_x(φ − ψ) для двух рядов (q (c e) …): первый показатель (в x), где коэффициенты различаются
(define (cv-ord-diff b1 b2)
  (let loop ((a (nth b1 1)) (b (nth b2 1)))
    (cond ((and (null? a) (null? b)) #f)
          ((null? a) (nth (car b) 1))
          ((null? b) (nth (car a) 1))
          (else
           (let ((e1 (nth (car a) 1)) (e2 (nth (car b) 1)))
             (cond ((< e1 e2) e1)
                   ((> e1 e2) e2)
                   (else (let ((dc (simplify (expand (list '- (nth (car a) 0) (nth (car b) 0))))))
                           (if (puiseux::px-coef-zero? dc) (loop (cdr a) (cdr b)) e1)))))))))

; ---------- аффинные особые точки ----------

; полиномы базиса, зависящие только от x
(define (cv-xpoly basis x y)
  (let ((ps (filter (lambda (p) (and (not (contains-sym? p y)) (contains-sym? p x))) basis)))
    (if (null? ps) #f
        (foldl (lambda (a p) (if (> (degree p x) (degree a x)) p a)) (car ps) ps))))

; полином из базиса, линейный по y; #f если нет
(define (cv-linear-y basis y)
  (let ((ps (filter (lambda (p) (= (degree p y) 1)) basis)))
    (if (null? ps) #f (car ps))))

; аффинные особые группы: список (g s e): точки (корни g, s(корень)), e = deg g.
; Идеал J = (F, Fx, Fy) содержит точки с кратностями (μ) — лекс-базис содержит
; степени (x³, y²); для нормальной позиции подмешиваем бесквадратные части
; полиномов исключения (аннулируются во всех точках — безопасно):
; J₃ = J + (sqfree Xp) + (sqfree Yp), затем факторизация Xp₃ и группы
(define (cv-affine-groups F x y)
  (let* ((J (list F (diff x F) (diff y F)))
         (G (groebner-lex J (list y x))))
    (if (and (list? G) (not (null? G)) (equal? (car G) 1)) '()
        (let ((Xp (cv-xpoly G x y)))
          (if (not Xp) '()
              (let* ((Xsf (cv-poly-sqfree Xp x))
                     (Yp (try (car (eliminate J (list x) (list y))) (lambda (err) #f)))
                     (Ysf (if (and Yp (> (degree Yp y) 0)) (cv-poly-sqfree Yp y) #f))
                     (J3 (append J (list Xsf) (if Ysf (list Ysf) '())))
                     (G3 (groebner-lex J3 (list y x)))
                     (X3 (cv-xpoly G3 x y)))
                (if (not X3) '()
                    (let loop ((facs (cdr (factor-list X3))) (acc '()))
                      (if (null? facs) (reverse acc)
                          (let* ((g (nth (car facs) 0)))
                            (loop (cdr facs)
                                  (append (if (> (degree g x) 0)
                                              (cv-groups-for-x J3 g x y)
                                              '())
                                          acc))))))))))))

; группы для x-фактора g: базис (J + g); если нет линейного по y полинома
; (несколько y-орбит на один x-фактор) — факторизуем y-полином базиса и
; углубляемся рекурсивно; depth — защита от зависания (степени y-факторов падают,
; но гарантия слабая)
(define (cv-groups-for-x Jg g x y) (cv-groups-for-x-d Jg g x y 4))

(define (cv-groups-for-x-d Jg g x y depth)
  (if (<= depth 0) '()
      (let* ((Gi (groebner-lex (append Jg (list g)) (list y x)))
             (lin (cv-linear-y Gi y)))
        (cond ((not (list? Gi)) '())
              ((and (not (null? Gi)) (equal? (car Gi) 1)) '())
              (lin (let ((s (cv-solve-y lin g x y)))
                     (if s (list (list g s (degree g x))) '())))
              (else
               ; ищем полином только от y в базисе, факторизуем НАД полем ℚ[x]/(g)
               ; (yp может быть неприводим над ℚ, но разложим над расширением)
               (let ((yp (cv-ypoly Gi x y)))
                 (if (or (not yp) (= (degree yp y) 0)) '()
                     (let loop ((facs (cv-factors-over-y yp g x y)) (acc '()))
                       (if (null? facs) acc
                           (let* ((h (simplify (expand (car facs)))))
                             (loop (cdr facs)
                                   (append (if (> (degree h y) 0)
                                               (cv-groups-for-x-d (append Jg (list h)) g x y (- depth 1))
                                               '())
                                            acc))))))))))))


; факторизация yp (полином от y над ℚ[x], фактически от ℚ[x]/(g)) над полем ℚ[x]/(g);
; возвращает список множителей как ℚ[x,y]-полиномов (коэффициенты: элемент ℚ[x]/(g)
; = c0+c1·x+… ↦ выражение от x mod g). Гарантия: h(α, y) — неприводимый фактор yp(α, y)
(define (cv-factors-over-y yp g x y)
  (let* ((t 'tt)
         (K (try (alg-field (simplify (subst (list x t) g)) t) (lambda (err) #f))))
    (if (not K) '()
        (let* ((deg (degree g x))
               ; yp — полином от y с ℚ-коэффициентами (без x); переводим в ap по y над K
               (f (try (let loop ((cs (coefficients yp y)) (acc '()))
                         (if (null? cs) (reverse acc)
                             (loop (cdr cs) (cons (alg-elt K (list (car cs))) acc))))
                       (lambda (err) #f)))
               (r (if f (try (alg-factor K f 'y) (lambda (err) #f)) #f)))
          (if (not r) '()
              (map (lambda (pr)
                     (cv-ap-to-qxy K (car pr) x y))
                   (nth r 1)))))))

; ap-многочлен по y над полем K=ℚ(α), α↔x mod g → ℚ[x,y]-выражение
; (коэффициент (c0 c1 …) ↦ c0+c1·x+…)
(define (cv-ap-to-qxy K ap x y)
  (simplify
   (expand
    (cons '+
          (let loop ((cs (reverse ap)) (k (- (length ap) 1)) (acc '()))
            (if (null? cs) acc
                (loop (cdr cs) (- k 1)
                      (append acc
                              (list (list '* (cv-el-to-qxy (car cs) x)
                                          (list '^ y k)))))))))))

; элемент K (список rational по возрастанию) → ℚ[x]-выражение c0+c1·x+…; () → 0
(define (cv-el-to-qxy cs x)
  (if (null? cs) 0
      (cons '+ (let loop ((l cs) (k 0) (acc '()))
                 (if (null? l) acc
                     (loop (cdr l) (+ k 1)
                           (append acc (list (list '* (car l) (list '^ x k))))))))))

(define (cv-ypoly basis x y)
  (let ((ps (filter (lambda (p) (not (contains-sym? p x))) basis)))
    (if (null? ps) #f (car ps))))

; бесквадратная часть полинома ℚ[x] (через factor-list)
(define (cv-poly-sqfree p x)
  (let ((fl (cdr (factor-list p))))
    (if (null? fl) p
        (simplify (expand (cons '* (map (lambda (fk) (nth fk 0)) fl)))))))

; y = −b/a mod g для p = a(x)·y + b(x)
(define (cv-solve-y p g x y)
  (let* ((a (simplify (expand (coeff p y 1))))
         (b (simplify (expand (subst (list y 0) p))))
         (u (cv-poly-inv a g x)))
    (and u (simplify (expand (list '* -1 (list '* b u)))))))

; обратный к a в ℚ[x]/(g) (расширенный Евклид); #f если gcd(a, g) ≠ 1
(define (cv-poly-inv a g x)
  (let ev ((r0 g) (r1 a) (s0 0) (s1 1))
    (cond ((cv-poly-zero? r1 x)
           (if (cv-poly-const? r0 x) (if (equal? (simplify r0) 0) #f 1) #f))
          (else
           (let* ((qr (cv-poly-divmod r0 r1 x))
                  (q (nth qr 0)) (r2 (nth qr 1)))
             (if (cv-poly-zero? r2 x)
                 (if (cv-poly-const? r1 x)
                     (simplify (list '/ s1 r1))
                     #f)
                 (ev r1 r2 s1 (simplify (expand (list '- s0 (list '* q s1)))))))))))

(define (cv-poly-zero? p x) (equal? (simplify p) 0))
(define (cv-poly-const? p x) (or (not (contains-sym? p x)) (= (degree p x) 0)))

; деление с остатком ℚ[x]: (частное остаток)
(define (cv-poly-divmod a b x)
  (let loop ((r (simplify (expand a))) (q 0))
    (if (cv-poly-zero? r x)
        (list q r)
        (let ((dr (degree r x)) (db (degree b x)))
          (if (< dr db)
              (list q r)
              (let* ((lc-r (coeff r x dr))
                     (lc-b (coeff b x db))
                     (c (/ lc-r lc-b))
                     (tt (simplify (expand (* c (^ x (- dr db))))))
                     (r2 (simplify (expand (- r (* tt b)))))
                     (q2 (simplify (expand (+ q tt)))))
                (loop r2 q2)))))))

; ---------- бесконечность ----------

; F(x, y) → F_h(X, Y, Z) (однородный)
(define (cv-homogenize F x y)
  (let* ((ts (cv-terms F x y))
         (d (foldl (lambda (acc t) (max acc (+ (nth t 1) (nth t 2)))) 0 ts)))
    (simplify (expand
               (cons '+ (map (lambda (t)
                               (list '* (car t)
                                     (list '^ 'X (nth t 1)) (list '^ 'Y (nth t 2))
                                     (list '^ 'Z (- d (+ (nth t 1) (nth t 2))))))
                             ts))))))

; особые точки на бесконечности, патч X = 1: [1 : b : 0], b — общий корень
; g(Y) = Fh(1, Y, 0), Fh_Y(1, Y, 0), Fh_Z(1, Y, 0) (по Эйлеру Fh_X = 0 автоматически)
; → группы (g 0 e): g — минмногочлен b (координата Y/X)
(define (cv-inf-groups F x y)
  (let* ((Fh (cv-homogenize F x y))
         (g1 (simplify (expand (subst (list 'Z 0) (subst (list 'X 1) Fh)))))
         (dy (simplify (expand (subst (list 'Z 0) (subst (list 'X 1) (diff 'Y Fh))))))
         (dz (simplify (expand (subst (list 'X 1) (subst (list 'Z 0) (diff 'Z Fh))))))
         (c (cv-poly-gcd (cv-poly-gcd g1 dy 'Y) dz 'Y)))
    (if (or (not (contains-sym? c 'Y)) (= (degree c 'Y) 0)) '()
        (let loop ((facs (cdr (factor-list c))) (acc '()))
          (if (null? facs) (reverse acc)
              (let ((g (nth (car facs) 0)))
                (loop (cdr facs)
                      (if (> (degree g 'Y) 0) (cons (list g 0 (degree g 'Y)) acc) acc))))))))

; НОД полиномов ℚ[v] (Евклид)
(define (cv-poly-gcd a b v)
  (let ev ((r0 (simplify (expand a))) (r1 (simplify (expand b))))
    (cond ((cv-poly-zero? r1 v) (cv-poly-normalize r0 v))
          (else (ev r1 (nth (cv-poly-divmod r0 r1 v) 1))))))

(define (cv-poly-normalize p v)
  (if (cv-poly-zero? p v) p
      (let ((lc (coeff p v (degree p v))))
        (simplify (expand (list '* (list '/ 1 lc) p))))))

; (c i j) → (c p q r) однородные (степени X, Y, Z; r = d−i−j)
(define (cv-hom-terms ts)
  (let ((d (foldl (lambda (acc t) (max acc (+ (nth t 1) (nth t 2)))) 0 ts)))
    (map (lambda (t) (list (car t) (nth t 1) (nth t 2) (- d (+ (nth t 1) (nth t 2))))) ts)))

; сдвиг в бесконечную точку [1 : b : 0]: локальные координаты u = Z/X, w = (Y−bX)/X:
; X = 1, Y = b + w, Z = u → термы (коэф, u-степень, w-степень)
(define (cv-inf-shift ts K b)
  (cv-agg
   (apply append
          (map (lambda (ht)
                 (map (lambda (s)
                        (list (cv-el-mul K (cv-el-mul K (car ht) (cv-binom (nth ht 2) s))
                                         (cv-el-pow K b (- (nth ht 2) s)))
                              (nth ht 3) s))
                      (cv-range (+ (nth ht 2) 1))))
               (cv-hom-terms ts)))
   K))

; главная переменная полинома-выражения (первый символ из переменных)
(define (cv-main-var p)
  (let ((vs (try (variables p) (lambda (err) '()))))
    (if (null? vs) 'x (car vs))))

; s(a) для s ∈ ℚ[t], a — элемент K (горнер по убыванию)
; элемент поля → выражение; нулевой элемент () → число 0 (px-nums->expr не понимает ())
(define (cv-el-norm0 K a)
  (if (null? a) 0 (cv-el->expr K a)))

(define (cv-eval-poly-in-field K s t a)
  (let loop ((l (reverse (coefficients s t))) (acc (cv-el-zero K)))
    (if (null? l) acc
        (loop (cdr l) (cv-el-add K (cv-el-mul K acc a)
                                 (cv-el-of K (car l)))))))
; ---------- анализ группы и публичный API ----------

; (g s e kind) → данные группы: поле-представитель, сдвиг кривой, ветви, δ
(define (cv-analyze-group F x y grp)
  (let* ((g0 (nth grp 0)) (s (nth grp 1)) (kind (nth grp 3))
         ; переменная поля — из типичных имён px-field-var (t u w s z), не входящая в g/s
         (t (let loop ((cands (list 't 'u 'w 's 'z)))
              (if (null? cands) (gensym "cvt")
                  (if (or (contains-sym? g0 (car cands)) (contains-sym? s (car cands)))
                      (loop (cdr cands)) (car cands)))))
         (g (simplify (subst (list (cv-main-var g0) t) g0)))
         ; deg g = 1 — рациональная точка: поле ℚ (K = #f) — все расширения раскрываются
         ; px-all-embeddings'ом (включая точные квадратичные комплексные)
         (rat? (= (degree g t) 1))
         (K (if rat? #f (alg-field g t (car (puiseux::px-all-embeddings g t)))))
         (ar (if rat? (simplify (list '- 0 (coeff g t 0))) 0))
         (a (if rat? ar (alg-elt K '(0 1))))
         (b (if rat?
                (simplify (subst (list (cv-main-var g0) ar) s))
                (cv-eval-poly-in-field K s (cv-main-var g0) a)))
         (ts (cv-terms F x y))
         (d (foldl (lambda (acc tt) (max acc (+ (nth tt 1) (nth tt 2)))) 0 ts))
         (shifted (if (equal? kind 'affine)
                      (cv-shift ts a b K)
                      (cv-inf-shift ts K a)))
         (mult (cv-terms-mult shifted))
         (brs0 (cv-walk shifted K (+ d 2) 0))
         ; вертикальная касательная: ряды по x не различают ветвей (сопряжённые
         ; x = ±c·y^{j} при q с плохой ζ-склейкой идут как разные ветви — дефект A3.1c).
         ; Пересчёт по y (обмен ролей переменных в сдвинутом полиноме): ряды x по y
         ; дают ζ-орбиты с чётными q — склейка cv-same-branch? точна; пересечения — тем же методом.
         (vert? (let ((gr (cv-group-branches brs0)))
                  (and (pair? gr)
                       (all? (lambda (br)
                               (let ((tms (nth (car br) 1)))
                                 (and (pair? tms) (< (nth (car tms) 1) 1))))
                             gr))))
         (brs (if (and vert? (equal? kind 'affine))
                  (cv-walk-swap shifted K (+ d 2))
                  brs0))
         (dl (cv-delta brs))
         (delta (+ (nth dl 0) (nth dl 1)))
         (r (length (cv-group-branches brs)))
         ; касательные: при вертикальной касательной после swap — r вертикальных;
         ; иначе — по исходным рядам (роли переменных не менялись)
         (tang (if (and vert? (equal? kind 'affine))
                   (map (lambda (u) 'vert) (cv-group-branches brs))
                   (cv-tangents (map car (cv-group-branches brs0))))))
    (list 'ok grp K a b mult r delta tang (nth grp 2))))

; все элементы списка истинны
(define (all? p xs)
  (cond ((null? xs) #t)
        ((not (p (car xs))) #f)
        (else (all? p (cdr xs)))))

; ветви при вертикальной касательной: обменять роли переменных (термы (c i j) → (c j i)),
; walk по новым терсам; орбиты (q ζ-склейка) корректны для чётных q
(define (cv-walk-swap shifted K n)
  (let ((sw (map (lambda (tm) (list (nth tm 0) (nth tm 2) (nth tm 1))) shifted)))
    (cv-walk sw K n 0)))

; касательные ветвей: первый терм (c e): e < 1 → вертикаль; e = 1 → наклон c;
; e > 1 или пусто → горизонталь
(define (cv-tangents brs)
  (map (lambda (br)
         (let ((ts (nth br 1)))
           (cond ((null? ts) 'horiz)
                 ((< (nth (car ts) 1) 1) 'vert)
                 ((= (nth (car ts) 1) 1) (list 'slope (nth (car ts) 0)))
                 (else 'horiz))))
       brs))

; самопроверка инвариантов точки: кратность m, ветвей r, δ — 1 ≤ r ≤ m, δ ≥ m(m−1)/2
; обыкновенная ⇒ r = m и δ = m(m−1)/2 (обратное неверно: каспида m = 2, r = 1, δ = 1); нарушение —
; δ/ветви посчитаны неверно → (unknown запись причина).
; Пример: (y − x²)² = x⁵ в (0, 0) давал m = 2, r = 1, δ = 0 → род 2 вместо 0 (ложное not-rational).
(define (cv-sane-group g)
  (if (or (not (list? g)) (null? g) (equal? (car g) 'unknown))
      g
      (let ((m (cv-pluck g 'multiplicity))
            (r (cv-pluck g 'branches))
            (dl (cv-pluck g 'delta))
            (o (cv-pluck g 'ordinary)))
        (if (and (integer? m) (integer? r) (number? dl)
                 (or (< r 1) (> r m)
                     (< dl (* 1/2 m (- m 1)))
                     (and (equal? o #t) (not (and (= r m) (= dl (* 1/2 m (- m 1))))))))
            (list 'unknown g "несогласованные инварианты: нужно 1 ≤ r ≤ m, δ ≥ m(m−1)/2, обыкновенная ⇒ r = m, δ = m(m−1)/2")
            g))))

; (singular-points F x y) → список групп особых точек (аффинные и бесконечные).
; Группа: ((point a b) (multiplicity m) (branches r) (delta δ) (ordinary #t/#f)
;         (tangents …) (conjugates e) (at affine|infinity)); δ — инвариант одной
; точки группы; нераскрывшиеся группы → (unknown g kind)
(define (singular-points F x y)
  (let* ((F (simplify F))
         (sqf (puiseux::px-sqfree-y F))
         (aff (map (lambda (g) (append g (list 'affine))) (cv-affine-groups sqf x y)))
         (inf (map (lambda (g) (append g (list 'inf))) (cv-inf-groups sqf x y))))
    (cv-list-or-empty (append
     (map (lambda (grp)
            (let ((res (try (cv-analyze-group sqf x y grp)
                            (lambda (err) (list 'unknown grp)))))
              (cv-sane-group (cv-format-group res))))
          (append aff inf))
     (cv-point-010 sqf x y)))))

; (append '() '()) даёт nil, не равный '() по equal? — нормализуем пустой ответ
(define (cv-list-or-empty r) (if (null? r) '() r))

; точка [0 : 1 : 0] (направление оси y): патч X = 1 её не видит. Замечание ревью: y² = x⁴ + 1 давал род 3
; вместо 1 — пропущен такнод на бесконечности. Если точка особая — анализ как аффинной точки (0, 0) кривой
; G(x, y) = Fh(x, 1, y) (локальные координаты X/Y, Z/Y).
(define (cv-point-010 F x y)
  (let* ((Fh (cv-homogenize F x y))
         (at0 (lambda (e) (simplify (subst (list 'Z 0) (subst (list 'Y 1) (subst (list 'X 0) e))))))
         (sing (and (equal? (at0 Fh) 0) (equal? (at0 (diff 'X Fh)) 0) (equal? (at0 (diff 'Z Fh)) 0))))
    (if (not sing) '()
        (let* ((G (simplify (expand (subst (list 'Z y) (subst (list 'Y 1) (subst (list 'X x) Fh))))))
               (res (try (cv-analyze-group G x y (list x 0 1 'affine))
                         (lambda (err) (list 'unknown (list x 0 1 'inf)))))
               (g (cv-format-group res)))
          (list (if (equal? (car g) 'unknown) g
                    (map (lambda (kv)
                           (cond ((equal? (car kv) 'point) (list 'point 'inf-y 0))
                                 ((equal? (car kv) 'at) (list 'at 'inf))
                                 (else kv)))
                         g)))))))

; выдача группы
(define (cv-format-group res)
  (if (equal? (nth res 0) 'unknown)
      (list 'unknown (nth (nth res 1) 0) (nth (nth res 1) 3))
      (let* ((grp (nth res 1)) (K (nth res 2)) (a (nth res 3)) (b (nth res 4))
             (mult (nth res 5)) (r (nth res 6)) (delta (nth res 7))
             (tang (nth res 8)) (e (nth res 9))
             (ord (and (number? delta) (= delta (* 1/2 r (- r 1)))
                       (= (length (cv-dedupe tang)) r))))
        (list (list 'point (cv-el->expr K a) (cv-el->expr K b))
              (list 'multiplicity mult) (list 'branches r) (list 'delta delta)
              (list 'ordinary (if ord #t #f)) (list 'tangents tang)
              (list 'conjugates e) (list 'at (nth grp 3))))))

(define (cv-dedupe l)
  (let loop ((rest l) (acc '()))
    (if (null? rest) (reverse acc)
        (if (member? (car rest) acc) (loop (cdr rest) acc) (loop (cdr rest) (cons (car rest) acc))))))

; (curve-genus F x y) → (genus g) | (reducible (F₁ …)) | unknown
; неприводимость над ℚ̄: factor-list над ℚ + поля особых точек (эвристика из задания;
; приводимость над ℚ̄, невидимая этими полями, — риск)
(define (curve-genus F x y)
  (let* ((F (simplify F))
         (fl (cdr (factor-list F))))
    (if (> (length fl) 1)
        (list 'reducible (map (lambda (fk) (nth fk 0)) fl))
        (let* ((sqf (puiseux::px-sqfree-y F))
               (ts (cv-terms sqf x y))
               (d (foldl (lambda (acc t) (max acc (+ (nth t 1) (nth t 2)))) 0 ts))
               (groups (singular-points F x y)))
          (if (any? (lambda (g) (and (list? g) (equal? (car g) 'unknown))) groups)
              'unknown
              (let ((dd (foldl (lambda (acc g)
                                 (+ acc (* (cv-pluck g 'delta) (cv-pluck g 'conjugates))))
                               0 groups)))
                (if (not (number? dd)) 'unknown
                    (let ((g (simplify (- (* 1/2 (- d 1) (- d 2)) dd))))
                      ; род отрицательным быть не может — значит, δ посчитан неверно: unknown, не ответ
                      (if (and (number? g) (>= g 0)) (list 'genus g) 'unknown)))))))))

; значение ключа из ((key val) …)
(define (cv-pluck pairs key)
  (let loop ((l (cdr pairs)))
    (cond ((null? l) #f)
          ((equal? (car (car l)) key) (cadr (car l)))
          (else (loop (cdr l))))))

; точка особая на кривой? (сертификат: F = F_x = F_y = 0 в точке)
(define (curve-singular? F x y px py)
  (and (equal? (simplify (subst (list y py) (subst (list x px) F))) 0)
       (equal? (simplify (subst (list y py) (subst (list x px) (diff x F)))) 0)
       (equal? (simplify (subst (list y py) (subst (list x px) (diff y F)))) 0)))

; ---------- A3.2: рациональная параметризация кривых рода 0 ----------
;
; Метод — пучок прямых через особую точку кратности d−1 (Sendra–Winkler–Pérez-Díaz гл. 4):
; сумма кратностей в одной точке достигает d−1 → каждая прямая пучка y−b = t·(x−a) пересекает
; кривую ещё ровно в одной точке → параметризация степени 1. Сдвиг (a,b)→(0,0), y = t·x,
; R = F(x, tx) = x^{d−1}·Q(x, t); t-независимый множитель Q (прямая x = 0 — компонента
; пучка, проходящая через особую точку «лишний» раз) выносится НОД коэффициентов по t;
; Qn линеен по x → x(t) = −c0/c1, y(t) = t·x(t), обратный сдвиг. Коники d ≤ 2: роль точки
; кратности d−1 = 1 играет любая рациональная точка кривой (перебор малых высот).
; Сертификат: F(x(t), y(t)) ≡ 0 и степень отображения 1 (parametrization-check).

; степень кривой (максимальная полная степень термов)
(define (cv-par-degree F x y)
  (foldl (lambda (a tt) (max a (+ (nth tt 1) (nth tt 2)))) 0 (cv-terms F x y)))

; рациональная точка кривой малой высоты (для коник): перебор |a|,|b| ≤ H
(define (cv-par-rat-point F x y H)
  (let outer ((a (- H)))
    (if (> a H) #f
        (let inner ((b (- H)))
          (if (> b H)
              (outer (+ a 1))
              (if (equal? (simplify (subst (list y b) (subst (list x a) F))) 0)
                  (list a b)
                  (inner (+ b 1))))))))

; НОД списка полиномов от t (константы по t — НОД 1; ошибка — 1: вынос не делаем)
(define (cv-par-gcd-list cs)
  (try (let ((g (foldl (lambda (a b) (cv-poly-gcd a b 't)) (car cs) (cdr cs))))
         (if (equal? (simplify g) 1) 1 g))
       (lambda (e) 1)))

; (cv-par-ratfun e t) → (num den) — e = num/den, оба многочлены от t (после together);
; не рациональная функция от t (cos t, √t …) → #f
(define (cv-par-ratfun e t)
  (let* ((r (together e))
         (n (simplify (expand (numer r))))
         (d (simplify (expand (denom r)))))
    (if (and (polynomial? n t) (polynomial? d t) (not (equal? d 0)))
        (list n d)
        #f)))

; F(x(t), y(t)) ≡ 0 — точная полиномиальная проверка: x = nx/dx, y = ny/dy;
; терм c·x^i·y^j, умноженный на dx^d·dy^d, — c·nx^i·ny^j·dx^{d−i}·dy^{d−j} (d — степень F);
; сумма ≡ 0 (expand, точно). Не рациональные x(t), y(t) → #f.
(define (cv-par-on-curve? F x y xt yt t)
  (let ((nxd (cv-par-ratfun xt t))
        (nyd (cv-par-ratfun yt t)))
    (and nxd nyd
         (cv-par-on-curve-nd? F x y nxd nyd))))

(define (cv-par-on-curve-nd? F x y nxd nyd)
  (let* ((d (cv-par-degree F x y))
         (nx (nth nxd 0)) (dx (nth nxd 1))
         (ny (nth nyd 0)) (dy (nth nyd 1))
         (ts (cv-terms F x y)))
    (equal? 0 (simplify (expand
      (foldl (lambda (acc tt)
               (list '+ acc
                     (list '* (nth tt 0)
                           (list '^ nx (nth tt 1)) (list '^ ny (nth tt 2))
                           (list '^ dx (- d (nth tt 1)))
                           (list '^ dy (- d (nth tt 2))))))
             0 ts))))))

(define (cv-par-pencil F x y t a b)
  (let* ((shift-x (if (equal? a 0) x (list (quote +) x a)))
         (shift-y (if (equal? b 0) y (list (quote +) y b)))
         (Fs (simplify (expand (subst (list (list y shift-y)) (subst (list (list x shift-x)) F)))))
         (d (cv-par-degree F x y))
         (R (simplify (expand (subst (list (list y (list (quote *) t x))) Fs))))
         (Q (simplify (expand (list '/ R (list '^ x (- d 1))))))
         (nQ (degree Q t))
         (cs (filter (lambda (c) (not (equal? c 0)))
                     (map (lambda (i) (simplify (coeff Q t i))) (range (+ nQ 1)))))
         (g (if (null? cs) #f (cv-par-gcd-list cs)))
         (Qn (if (or (not g) (equal? g 1)) Q (simplify (expand (list '/ Q g)))))
         (c0 (simplify (coeff Qn x 0)))
         (c1 (simplify (coeff Qn x 1))))
    (if (or (not g) (equal? c1 0) (contains-sym? c1 x))
        #f
         (let* ((xt (simplify (expand (list (quote /) (list (quote *) -1 c0) c1))))
                (yt (simplify (expand (list (quote *) t xt))))
                (xa (if (equal? a 0) xt (simplify (expand (list (quote +) a xt)))))
                (ya (if (equal? b 0) yt (simplify (expand (list (quote +) b yt))))))
          (if (cv-par-on-curve? F x y xa ya t)
              (list xa ya)
              #f)))))
; ---------- A3.2b: адъюнкты (кратности в разных точках) ----------
;
; Метод (Sendra–Winkler–Pérez-Díaz гл. 4): адъюнкт — кривая степени d−2, проходящая через каждую
; особую точку P кратности r_P с кратностью ≥ r_P (обнуление коэф локального разложения до порядка
; r_P−2). Линейная система на коэффициенты → fm-nullspace; добавляем простые точки, пока dim > 2;
; пучок G_t = b1 + t·b2; вторые точки пересечения с F — из линейных множителей результантов
; res(F, G_t, y) по x и res(F, G_t, x) по y. Особые точки допускаются над ℚ(%i) (лемниската,
; астроида): формы расщепляются подстановкой %i→0/1 на рациональные строки; координаты вне
; ℚ(%i) или нечисловые строки → честный unknown (#f). Ответ всегда проходит
; parametrization-check — не прошёл → unknown.

; мономы (i j), i+j ≤ e
(define (cv-adj-monos e)
  (apply append
    (map (lambda (i) (map (lambda (j) (list i j)) (range (+ (- e i) 1))))
         (range (+ e 1)))))

; interned символы-коэффициенты (префикс «cva|» — имя не читается из файла, конфликтов нет)
(define (cv-adj-csym k) (string->symbol (string-append "cva|" (number->string k))))
(define cv-adj-X (string->symbol "cva|X"))
(define cv-adj-Y (string->symbol "cva|Y"))
(define cv-adj-Z (string->symbol "cva|Z"))

; аффинная точка (p,q) кратности r шаблона T (в x,y): сдвиг, коэф xi^a eta^b, a+b ≤ r−2
(define (cv-adj-aff-conds T x y p q r)
  (let ((E (simplify (expand (subst (list y (list '+ q 'eta)) (subst (list x (list '+ p 'xi)) T))))))
    (apply append
      (map (lambda (a)
        (apply append
          (map (lambda (b)
            (let ((Tc (simplify (expand (coeff (coeff E 'xi a) 'eta b)))))
              (if (and (<= (+ a b) (- r 2)) (not (equal? Tc 0))) (list Tc) '())))
            (range r))))
        (range r)))))

; бесконечная точка [1:b:0] кратности r однородного Gh: X=1, Y=b+w, Z=u; коэф w^a u^c, a+c ≤ r−2
(define (cv-adj-inf-conds Gh b r)
  (let ((E (simplify (expand (subst (list cv-adj-Z 'u) (subst (list cv-adj-Y (list '+ b 'w)) (subst (list cv-adj-X 1) Gh)))))))
    (apply append
      (map (lambda (a)
        (apply append
          (map (lambda (c)
            (let ((Tc (simplify (expand (coeff (coeff E 'w a) 'u c)))))
              (if (and (<= (+ a c) (- r 2)) (not (equal? Tc 0))) (list Tc) '())))
            (range r))))
        (range r)))))

; расщепление ℚ(%i)-формы на рациональные: re = T|%i=0, im = T|%i=1 − re
(define (cv-adj-split-row Tc)
  (let* ((re (simplify (expand (subst (list '%i 0) Tc))))
         (tot (simplify (expand (subst (list '%i 1) Tc))))
         (im (simplify (expand (list '- tot re)))))
    (append (if (equal? re 0) '() (list re))
            (if (equal? im 0) '() (list im)))))

; форма → числовая строка по csym k
(define (cv-adj-form->row Tc NC)
  (map (lambda (k) (simplify (coeff Tc (cv-adj-csym k) 1))) (range NC)))

; условия из записей singular-points; #f — точка вне охвата (координаты не ℚ / не ℚ(%i))
(define (cv-adj-conds Gh Gaff x y sps)
  (let loop ((rest sps) (acc '()))
    (if (null? rest)
        (apply append acc)
        (let* ((sp (car rest))
               (pt (nth (nth sp 0) 1))
               (r (nth (nth sp 1) 1))
               (at (nth (nth sp 7) 1))
               (cj (nth (nth sp 6) 1)))
           (cond
             ((not (and (number? r) (> r 1))) (loop (cdr rest) acc))
            ; [0:1:0] — патч Y=1: локальные координаты (X/Y, Z/Y), точка (0,0)
             ((and (equal? at (quote inf)) (equal? pt (quote inf-y)))
             (loop (cdr rest)
                   (cons (cv-adj-aff-conds
                           (simplify (expand (subst (list cv-adj-Z y) (subst (list cv-adj-Y 1) (subst (list cv-adj-X x) Gh)))))
                           x y 0 0 r)
                         acc)))
            ; [1:b:0], b ∈ ℚ(%i); при cj=2 — ещё сопряжённая [1:b̄:0]
            ((equal? at 'inf)
             (if (> cj 2)
                 #f
                  (let ((E1 (cv-adj-inf-conds Gh pt r))
                        (E2 (if (and (= cj 2) (contains-sym? pt (quote %i)))
                                (cv-adj-inf-conds Gh (simplify (expand (list (quote *) -1 pt))) r)
                               '())))
                   (loop (cdr rest) (cons (append E1 E2) acc)))))
            ; аффинная точка (p,q) ∈ ℚ(%i)² — одна запись = одна точка
            (else
             (loop (cdr rest) (cons (cv-adj-aff-conds Gaff x y (nth (nth sp 0) 1) (nth (nth sp 0) 2) r) acc))))))))

; рациональная ли ℚ(%i)-координата после simplify: только числа и %i линейно
(define (cv-adj-row-numeric? row)
  (every? (lambda (c) (number? c)) row))

; простые рациональные точки: (а) перебор x = p/q (q ≤ 6, |p| ≤ 6), факторизация F(p/q, y),
; линейные факторы → рациональный корень по y; (б) прямые через рациональные особые точки
; с целыми наклонами k ∈ [−12, 12] (+ вертикаль): линейные факторы по x → рациональные точки.
; поле записи singular-points: (nth (nth sp k) 1)
(define (cv-sp-field sp k) (nth (nth sp k) 1))

(define (cv-adj-simple-points F x y sps)
  (let* ((F (simplify F))
          (spts (filter (lambda (sp)
                          (and (equal? (cv-sp-field sp 7) (quote affine))
                               (number? (nth (nth sp 0) 1))
                               (number? (nth (nth sp 0) 2))))
                       sps))
         (on-curve? (lambda (p q) (equal? (simplify (subst (list y q) (subst (list x p) F))) 0)))
         (push (lambda (p q acc)
                 (if (and (number? p) (number? q) (on-curve? p q)
                          (not (try (curve-singular? F x y p q) (lambda (e) #t)))
                          (not (member? (list p q) acc)))
                     (cons (list p q) acc) acc)))
         (lin-root (lambda (f0 v)
                     (let ((a1 (simplify (coeff f0 v 1)))
                           (b1 (simplify (coeff f0 v 0))))
                       (if (equal? a1 0) #f
                           (simplify (expand (list (quote /) (list (quote *) -1 b1) a1))))))))
     (let scanx ((qs (cdr (range 7))) (acc (quote ())))
      (if (null? qs)
          (let ((ks (append (range 13) (map (lambda (k) (* -1 k)) (cdr (range 13))))))
            (let scanline ((S spts) (K (append ks (list 'inf))) (acc acc))
               (if (or (null? S) (> (length acc) 20))
                  acc
                  (if (null? K)
                      (scanline (cdr S) (append ks (list 'inf)) acc)
                       (let* ((P (nth (car S) 0))
                              (px (nth P 1)) (py (nth P 2))
                              (k (car K))
                              (Gs (simplify (expand
                                 (if (equal? k (quote inf))
                                     (subst (list x px) F)
                                     (subst (list y (list (quote +) py (list (quote *) k (list (quote -) x px)))) F)))))
                              (fs (try (cdr (factor-list Gs)) (lambda (e) (quote ()))))
                              (var (if (equal? k (quote inf)) y x)))
                         (scanline S (cdr K)
                           (foldl (lambda (a f)
                                    (if (= (try (degree (nth f 0) var) (lambda (e) -1)) 1)
                                        (let ((rt (lin-root (nth f 0) var)))
                                          (if rt
                                              (if (equal? k (quote inf))
                                                  (push px rt a)
                                                  (push rt (simplify (expand (list (quote +) py (list (quote *) k (list (quote -) rt px))))) a))
                                              a))
                                        a))
                                   acc fs)))))))
           (let* ((q (car qs))
                  (acc2 (let scanp ((ps (append (map (lambda (p) (* -1 p)) (cdr (range 7))) (range 7))) (a acc))
                          (if (null? ps) a
                             (let* ((p (car ps))
                                    (P (simplify (expand (subst (list x (list '/ p q)) F))))
                                    (fs (try (cdr (factor-list P)) (lambda (e) '()))))
                               (scanp (cdr ps)
                                 (foldl (lambda (a f)
                                          (if (= (try (degree (nth f 0) y) (lambda (e) -1)) 1)
                                              (let ((rt (lin-root (nth f 0) y)))
                                                (if rt (push (list '/ p q) rt a) a))
                                              a))
                                         a fs)))))))
             (scanx (cdr qs) acc2))))))

; пучок из базиса (2 вектора) → параметризация через результанты; #f если не вышло
(define (cv-adj-pencil-param F x y t Ms Gaff basis)
  (let* ((b1 (nth basis 0)) (b2 (nth basis 1))
         (cs12 (map2 (lambda (u v) (list '+ u (list '* t v))) b1 b2))
         (Gt (simplify (expand (cons '+ (map2 (lambda (kc m)
                     (list '* kc (list '^ x (nth m 0)) (list '^ y (nth m 1))))
                   cs12 Ms)))))
         (Ry (simplify (expand (resultant F Gt y))))
         (Rx (simplify (expand (resultant F Gt x))))
         (lin (lambda (R v)
                (let ((fs (filter (lambda (f)
                                    (and (= (try (degree (nth f 0) v) (lambda (e2) -1)) 1)
                                         (contains-sym? (nth f 0) t)))
                                  (cdr (factor-list R)))))
                  (if (null? fs) #f
                      (let* ((f0 (nth (car fs) 0))
                             (a1 (simplify (coeff f0 v 1)))
                             (b1c (simplify (coeff f0 v 0))))
                        (if (equal? a1 0) #f
                            (simplify (expand (list '/ (list '* -1 b1c) a1))))))))))
    (let ((xt (lin Ry x)) (yt (lin Rx y)))
      (if (and xt yt (parametrization-check F x y (list xt yt) t))
          (list xt yt) #f))))

; (cv-par-adjoint F x y t sps) → (x(t) y(t)) | #f. Базис условий особых точек; простые точки
; добавляем по одной, пока dim > 2; пучок → результанты → линейные множители → x(t), y(t).
(define (cv-par-adjoint F x y t sps)
  (let* ((d (cv-par-degree F x y))
         (e (- d 2))
         (Ms (cv-adj-monos e))
         (NC (length Ms))
         (Gh (cons '+ (map2 (lambda (m k)
                     (list '* (cv-adj-csym k) (list '^ cv-adj-X (nth m 0))
                           (list '^ cv-adj-Y (nth m 1))
                           (list '^ cv-adj-Z (- e (+ (nth m 0) (nth m 1))))))
                   Ms (range NC))))
         (Gaff (simplify (expand (subst (list cv-adj-Z 1) (subst (list cv-adj-Y y) (subst (list cv-adj-X x) Gh))))))
         (conds (cv-adj-conds Gh Gaff x y sps)))
    (if (not conds) #f
        (let* ((rows0 (map (lambda (Tc) (cv-adj-form->row Tc NC))
                           (apply append (map cv-adj-split-row conds)))))
          (if (not (every? cv-adj-row-numeric? rows0)) #f
              (let ((b0 (fm-nullspace (field-Q) rows0)))
                (if (or (not b0) (< (length b0) 2)) #f
                    (let loop ((extra (cv-adj-simple-points F x y sps)) (rows rows0))
                      (let ((basis (fm-nullspace (field-Q) rows)))
                        (cond ((= (length basis) 2)
                               (cv-adj-pencil-param F x y t Ms Gaff basis))
                              ((<= (length basis) 1) #f)
                              ((null? extra) #f)
                              (else
                               (let* ((Q (car extra))
                                      (Gq (simplify (expand (subst (list y (nth Q 1)) (subst (list x (nth Q 0)) Gaff)))))
                                      (rq (map (lambda (k) (simplify (coeff Gq (cv-adj-csym k) 1))) (range NC))))
                                 (loop (cdr extra) (append rows (list rq)))))))))))))))


; Род 0: особая точка кратности d−1 (рациональная аффинная) → пучок; коники — рациональная
; точка перебором малых высот; иначе — базис адъюнктов (cv-par-adjoint); не вышло → unknown
; коника a·(x²+y²) − c (после нормировки a=1): точка над ℚ(√c), если c не сумма двух квадратов;
; целое c = a²+b² (sum-of-two-squares) → рациональная точка (a b) большой высоты.
; Ответ — символьное (^ c 1/2) = √c; параметризация над ℚ(√c), check принимает (^ c 1/2).
(define (cv-par-conic-sqrt F x y t)
  (let* ((cxx (simplify (coeff F x 2)))
         (cyy (simplify (coeff F y 2)))
         (cx (simplify (coeff F x 1)))
         (cy (simplify (coeff F y 1)))
         (c0 (simplify (subst (list y 0) (subst (list x 0) F)))))
    (if (not (and (number? cxx) (number? cyy) (number? cx) (number? cy) (number? c0)
                 (equal? cxx cyy) (equal? cx 0) (equal? cy 0) (not (equal? cxx 0))))
        #f
        (let ((c (simplify (expand (list (quote /) (list (quote *) -1 c0) cxx)))))
         (let ((c (simplify (expand (list (quote /) (list (quote *) -1 c0) cxx)))))
           (cond ((and (number? c) (> c 0) (not (integer? (sqrt c))))
                  (let ((ab (if (and (integer? c) (>= c 0)) (sum-of-two-squares c) #f)))
                    (cond (ab (cv-par-pencil F x y t (nth ab 0) (nth ab 1)))
                          ; нет рациональной точки: (√c, 0) над ℚ(√c)
                          (else (cv-par-pencil F x y t (list (quote ^) c 1/2) 0)))))
                 ; c < 0: точка (0, i·√|c|) над ℚ(i·√|c|); корректно для c = -1 (ℚ(i))
                 ((and (number? c) (< c 0) (= c -1)) (cv-par-pencil F x y t 0 (sqrt -1)))
                 (else #f)))))))
 
(define (parametrize-curve F x y t)
  (let* ((F (simplify F))
         (fl (cdr (factor-list F)))
         (sp (singular-points F x y))
         (ts (cv-terms F x y))
         (dg (foldl (lambda (acc tt) (max acc (+ (nth tt 1) (nth tt 2)))) 0 ts))
         (gen (cond ((> (length fl) 1) (list (quote reducible) (map (lambda (fk) (nth fk 0)) fl)))
                    ((any? (lambda (g) (and (list? g) (equal? (car g) (quote unknown)))) sp) (quote unknown))
                    (else (let ((dd (foldl (lambda (acc g) (+ acc (* (cv-pluck g (quote delta)) (cv-pluck g (quote conjugates))))) 0 sp)))
                            (if (not (number? dd)) (quote unknown)
                                (let ((g (simplify (- (* 1/2 (- dg 1) (- dg 2)) dd))))
                                  (if (and (number? g) (>= g 0)) (list (quote genus) g) (quote unknown))))))))
         (gen0 (cond ((not (list? gen)) (quote unknown))
                     ((equal? (car gen) (quote reducible)) gen)
                     ((not (equal? (car gen) (quote genus))) gen)
                     ((> (nth gen 1) 0) (list (quote not-rational) (nth gen 1)))
                     (else #f))))
    (if gen0 gen0
        (let* ((d dg)
               (cands (filter (lambda (p)
                                  (and (list? (car p)) (equal? (car (car p)) 'point)
                                       (equal? (nth p 7) (list 'at 'affine))
                                       (number? (nth (car p) 1)) (number? (nth (car p) 2))
                                       (= (nth (nth p 1) 1) (- d 1))))
                                sp))
                        (pt (if (null? cands)
                                (cv-par-rat-point F x y 6)
                                (list (nth (car (car cands)) 1) (nth (car (car cands)) 2)))))
                   (cond ((= d 1)
                          ; прямая: F = αx + βy + γ; точка P₀ + t·(β, −α)
                          (let* ((a1 (simplify (coeff F x 1)))
                                 (b1 (simplify (coeff F y 1)))
                                 (p0 (or pt (list 0 0))))
                            (if (equal? (simplify (subst (list y (nth p0 1)) (subst (list x (nth p0 0)) F))) 0)
                                (list (list '+ (nth p0 0) (list '* t b1))
                                      (list '- (nth p0 1) (list '* t a1)))
                                'unknown)))
                         ((not pt)
                          ; коника a·(x²+y²)=c без рациональной точки малой высоты — над ℚ(√c);
                          ; d ≥ 3 — базис адъюнктов (особые точки над ℚ(%i) допустимы)
                          (let ((par (if (= d 2)
                                           (try (cv-par-conic-sqrt F x y t) (lambda (e) #f))
                                           (try (cv-par-adjoint F x y t sp) (lambda (e) #f)))))
                            (if par par (quote unknown))))
                         (else
                           ; сперва пучок через точку кратности d-1; не вышло - адъюнкты
                           ; (найденная точка малой высоты может быть особой кратности < d-1)
                           (let ((par (try (cv-par-pencil F x y t (nth pt 0) (nth pt 1)) (lambda (e) #f))))
                             (if par par
                                 (let ((par2 (try (cv-par-adjoint F x y t sp) (lambda (e) #f))))
                                      (if par2 par2 (quote unknown)))))))))))
 
; ny(s)·dy(t0) − ny(t0)·dy(s) — их общие корни s дают ту же точку кривой, что t0. При степени
; отображения k ≥ 2 НОД имеет степень ≥ k для всех t0, кроме конечного числа (часть слоя в
; полюсе или на бесконечности). t0 — полюс → #f (проба не годится).
(define (cv-par-fiber-deg nxd nyd t t0)
  (let ((v (lambda (e) (simplify (subst (list (list t t0)) e))))
        (sv (lambda (e) (simplify (subst (list (list t 'cv-s)) e)))))
    (let ((dx0 (v (nth nxd 1))) (dy0 (v (nth nyd 1))))
      (if (or (equal? dx0 0) (equal? dy0 0))
          #f
          (let* ((px (simplify (expand (list '- (list '* (sv (nth nxd 0)) dx0)
                                             (list '* (v (nth nxd 0)) (sv (nth nxd 1)))))))
                 (py (simplify (expand (list '- (list '* (sv (nth nyd 0)) dy0)
                                             (list '* (v (nth nyd 0)) (sv (nth nyd 1)))))))
                 (g (poly-gcd px py)))
            (if (equal? g 0) #f (degree g 'cv-s)))))))

; (parametrization-check F x y par t) → #t/#f — независимая проверка сертификата:
; 1) x(t), y(t) — рациональные функции от t и F(x(t), y(t)) ≡ 0 (полиномиально, точно);
; 2) степень отображения 1: слой из одной точки во всех годных пробах t0 (не меньше двух).
;    Ложное #t при k ≥ 2 — только если все пробы попали в конечное исключительное множество.
(define (parametrization-check F x y par t)
  (and (list? par) (= (length par) 2)
       (let ((nxd (cv-par-ratfun (nth par 0) t))
             (nyd (cv-par-ratfun (nth par 1) t)))
         (and nxd nyd
              (cv-par-on-curve-nd? F x y nxd nyd)
              (let ((ks (filter number? (map (lambda (t0) (cv-par-fiber-deg nxd nyd t t0))
                                             (list 2 3 -5 7 1/2 -11/3)))))
                (and (>= (length ks) 2) (every? (lambda (k) (= k 1)) ks)))))))

; ---------- A3′.2: обратное отображение параметризации ----------

; рациональные аффинные точки (особые и малые целые на кривой) — кандидаты в базу пучка
(define (cv-inv-rational-points F x y)
  (let* ((sps (try (singular-points F x y) (lambda (e) '())))
         (sing (filter (lambda (p)
                         (and (list? p) (list? (car p))
                              (equal? (car (car p)) 'point)
                              (number? (nth (car p) 1)) (number? (nth (car p) 2))))
                       sps))
         (ks (map (lambda (k) (- k 6)) (range 13)))
         (small (filter (lambda (p)
                          (equal? (simplify (subst (list y (cadr p))
                                                   (subst (list x (car p)) F))) 0))
                        (append-map (lambda (a) (map (lambda (b) (list a b)) ks)) ks))))
    (append (map (lambda (p) (list (nth (car p) 1) (nth (car p) 2))) sing) small)))

; (parametrize-curve-inverse F x y t par) → t(x,y) для пучка t=(y−b)/(x−a), иначе unknown
(define (parametrize-curve-inverse F x y t par)
  (if (not (and (list? par) (= (length par) 2)))
      'unknown
      (let* ((xt (nth par 0)) (yt (nth par 1))
             (pts (append (list (list 0 0)) (cv-inv-rational-points F x y))))
        (let loop ((ps pts))
          (if (null? ps)
              (or (cv-par-inv-interp F x y t par 2) 'unknown)
              (let* ((a (car (car ps))) (b (cadr (car ps)))
                     (d (simplify (together
                                   (list '- (list '/ (list '- yt b) (list '- xt a)) t)))))
                (if (equal? d 0)
                    (list '/ (list '- y b) (list '- x a))
                    (loop (cdr ps)))))))))

; (parametrization-inverse-check F x y par inv t) → #t/#f: независимая проверка inv(par(t)) = t
(define (parametrization-inverse-check F x y par inv t)
  (and (list? par) (= (length par) 2)
       (not (equal? inv 'unknown))
       (not (contains-sym? inv t))
       (let ((sub (subst (list y (nth par 1)) (subst (list x (nth par 0)) inv))))
         (and (equal? (simplify (together (list '- sub t))) 0)
              (parametrization-check F x y par t)))))

; ---------- A3′.2: общий inverse интерполяцией t = P(x,y)/Q(x,y) ----------

(define (cv-inv-mons d x y)
  (append-map (lambda (i)
                (map (lambda (j) (simplify (list '* (list '^ x i) (list '^ y j))))
                     (range (+ (- d i) 1))))
              (range (+ d 1))))

(define (cv-inv-eval-rat r t ti)
  (let ((n (simplify (subst (list t ti) (car r))))
        (d (simplify (subst (list t ti) (cadr r)))))
    (and (number? n) (number? d) (not (equal? d 0)) (/ n d))))

(define (cv-inv-mons-at mons x y xi yi)
  (map (lambda (m) (simplify (subst (list y yi) (subst (list x xi) m)))) mons))

(define (cv-inv-rows r1 r2 t mons need x y)
  (let loop ((ts (list 2 3 5 1/2 7 1/3 3/2 5/2 4/3 9 2/7 11/5 -3 -5/2 7/3 13/4 -7 5/7
                       11/3 9/5 13/3 17/4 -4/3 3/7 8/5 15/7 -11/4 7/5 10/3 -13/5
                       17/5 19/4 -9/5 14/3 5/8 12/7 -15/4 9/8 16/5 7/9))
             (rows '()))
    (if (or (null? ts) (>= (length rows) need))
        (reverse rows)
        (let ((x0 (cv-inv-eval-rat r1 t (car ts)))
              (y0 (cv-inv-eval-rat r2 t (car ts))))
          (if (and x0 y0)
              (let* ((ms (cv-inv-mons-at mons x y x0 y0))
                     (ti (car ts))
                     (row (append ms (map (lambda (v) (* (- ti) v)) ms))))
                (loop (cdr ts) (cons row rows)))
              (loop (cdr ts) rows))))))

(define (cv-inv-vec-expr v mons)
  (let ((n (length mons)))
    (simplify (foldl (lambda (acc i)
                       (list '+ acc (list '* (nth v i) (nth mons i))))
                     0 (range n)))))

(define (cv-par-inv-interp F x y t par d)
  (if (> d 4)
      #f
      (let ((r1 (cv-par-ratfun (nth par 0) t))
            (r2 (cv-par-ratfun (nth par 1) t)))
        (if (not (and r1 r2))
            #f
            (let* ((mons (cv-inv-mons d x y))
                   (n (length mons))
                   (rows (cv-inv-rows r1 r2 t mons (+ (* 2 n) 2) x y)))
              (if (< (length rows) (* 2 n))
                  (cv-par-inv-interp F x y t par (+ d 1))
                  (let ((vecs (try (nullspace (tensor rows)) (lambda (e) '()))))
                    (let loop ((vs vecs))
                      (if (null? vs)
                          (cv-par-inv-interp F x y t par (+ d 1))
                          (let* ((v (car vs))
                                 (P (cv-inv-vec-expr (map (lambda (i) (nth v i)) (range n)) mons))
                                 (Q (cv-inv-vec-expr (map (lambda (i) (nth v (+ n i))) (range n)) mons))
                                 (inv (if (equal? (simplify Q) 0)
                                          #f
                                          (simplify (list '/ P Q)))))
                            (if (and inv
                                     (try (parametrization-inverse-check F x y par inv t)
                                          (lambda (e) #f)))
                                inv
                                (loop (cdr vs)))))))))))))
