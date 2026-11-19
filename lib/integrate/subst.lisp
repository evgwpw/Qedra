; integrate/subst.lisp — «скрытая подстановка» (шаг INT.SUBST, И4)
;
; Подынтегральное f(x) такое, что для некоторой u(x) отношение g = f/u′ — рациональная функция R(u). Тогда ∫f dx = ∫R(u) du.
; Почти все находки — u = xᵏ·(радикал из f) (подстановки Чебышёва, x·√(x⁴+1)), x ± 1/x, вложенные √(x+√(x²+1)).
; Кандидаты u — из «кирпичиков» f: xᵏ·b (k = −3…3, b — радикал, exp), основания радикалов, x ± 1/x, x² ± 1/x², xᵏ.
; Отсев — численный: g и u в 16 точках (параметры — пробные значения), подбор R = P(u)/Q(u) степеней ≤ 4 как одномерного
; ядра линейной системы (метод исключения с полным выбором, double), коэффициенты — рационализация цепной дробью; найденная R
; проверяется на всех точках и (если есть параметры) на втором наборе значений параметров — коэффициенты должны от них не зависеть.
; Затем — символьно: R(u) → (integrate R u) по новой переменной, обратная подстановка u(x), int-check по ИСХОДНОМУ f и численная
; проверка самой F (int-check-F-status = 'ok). Численная часть только предлагает кандидата; принимает ответ дифференцирование.
; Внутренние имена: su-.
(module integrate
  (export int-hidden-subst int-subst-stats without-subst without-subst-extra))

(define int-subst-enabled #t)
(define int-subst-time-limit 3)
(define su-why #f)
(define su-info '())
(define su-depth 0)
(define su-rank 0)
(define su-var 'su-u)

(define (int-subst-stats) (list su-why su-info))
(define int-subst-extra #t)   ; INT.HEUR.1: добавочные кандидаты (#f — прежний набор, замеры «до/после»)
(define (without-subst-extra thunk)
  (let ((old int-subst-extra))
    (set! int-subst-extra #f)
    (unwind-protect (thunk) (set! int-subst-extra old))))
(define (without-subst thunk)
  (let ((old int-subst-enabled))
    (set! int-subst-enabled #f)
    (unwind-protect (thunk) (set! int-subst-enabled old))))

; причины отказа по возрастанию «глубины»: no-u < r-not-rational < int-fails < check-fails
(define (su-reach! n why) (if (>= n su-rank) (begin (set! su-rank n) (set! su-why why))))

; точки и значения параметров — числа с плавающей точкой (eval-num по ним в разы быстрее, чем по рациональным: нет точной алгебры)
(define su-pts '(0.31 0.47 0.62 0.83 1.13 1.37 1.71 2.09 2.53 2.97 0.55 0.77 1.29 1.88 2.3 0.4 0.35 0.51 0.69 0.93 1.21 1.53 1.81 2.17
                   -0.31 -0.62 -1.13 -1.71 -2.09 -0.83 3.4 4.1 5.3 7.7))
; точки по всей оси (x < 0, x > 3): R, найденная только на куске оси, даёт ответ, верный лишь там (√(x−3)-ветви: u′ меняет знак)
(define su-pv-a '(1.7 2.3 1.9 3.1 1.3 2.9 1.1 2.7))
(define su-pv-b '(1.4 1.6666666666666667 1.857142857142857 2.25 1.8333333333333333 1.6 0.7142857142857143 2.111111111111111))

; ---------- кирпичики и кандидаты ----------
(define (su-bricks e x)
  (cond ((not (pair? e)) '())
        ((and (equal? (car e) '^) (= (length e) 3) (number? (caddr e)) (not (integer? (caddr e))) (contains-sym? (cadr e) x))
         (cons e (su-bricks (cadr e) x)))
        ((and (equal? (car e) 'sqrt) (contains-sym? (cadr e) x)) (cons (list '^ (cadr e) 1/2) (su-bricks (cadr e) x)))
        ((and (equal? (car e) 'exp) (contains-sym? (cadr e) x)) (cons e (su-bricks (cadr e) x)))
        (else (foldl append '() (map (lambda (a) (su-bricks a x)) (cdr e))))))

(define (su-dedup l)
  (let loop ((l l) (acc '()))
    (cond ((null? l) (reverse acc))
          ((member? (car l) acc) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

(define (su-candidates f x)
  (let* ((bs (su-dedup (su-bricks f x)))
         (ks '(0 1 -1 2 -2 3 -3))
         (rad (foldl append '() (map (lambda (b) (map (lambda (k) (if (= k 0) b (list '* (list '^ x k) b))) ks)) bs)))
         (base (foldl append '() (map (lambda (b) (if (equal? (car b) '^) (list (cadr b)) '())) bs)))
         (laur (list (list '+ x (list '^ x -1)) (list '- x (list '^ x -1))
                     (list '+ (list '^ x 2) (list '^ x -2)) (list '- (list '^ x 2) (list '^ x -2))
                     (list '^ x 2) (list '^ x 3) (list '^ x 4) (list '^ x 6))))
    (filter (lambda (u) (not (equal? u x)))
            (su-dedup (append rad base laur (if int-subst-extra (su-extra-candidates f x bs) '()))))))

; INT.HEUR.1: добавочные кандидаты (после прежних, порядок прежних находок не меняется):
;  b^(m·r)·xᵏ при m ∈ {−1, 2, −2} (b = P^r — радикал; для √P: xᵏ/√P, xᵏ·P, xᵏ/P), k = −2…2;
;  отношения множителей подкоренного P = P₁·P₂ (factor-list): P₁/P₂ и x^(±1)·P₁/P₂ (в каждой паре — вариант с первым множителем);
;  внутренние аргументы функций (u = аргумент log/exp/trig/обратной) и узлы ln, tg, th, sin, cos, atan от x и от аргумента.
(define (su-pow-brick b m)
  (let ((r (* (caddr b) m)))
    (if (equal? r 1) (cadr b) (list '^ (cadr b) r))))
(define (su-extra-radical bs x)
  (foldl append '()
         (map (lambda (b)
                (if (equal? (car b) '^)
                    (foldl append '()
                           (map (lambda (m)
                                  (let ((bm (su-pow-brick b m)))
                                    (map (lambda (k) (if (= k 0) bm (list '* (list '^ x k) bm))) '(0 1 -1 2 -2))))
                                '(-1 2 -2)))
                    '()))
              bs)))
(define (su-subsets-with-first fs)   ; все разбиения множителей на две группы, первая содержит fs[0]; обе непусты
  (let loop ((rest (cdr fs)) (a (list (car fs))) (b '()))
    (if (null? rest)
        (if (null? b) '() (list (list (reverse a) (reverse b))))
        (append (loop (cdr rest) (cons (car rest) a) b)
                (loop (cdr rest) a (cons (car rest) b))))))
(define (su-prod fs)
  (cons '* (map (lambda (p) (if (= (cadr p) 1) (car p) (list '^ (car p) (cadr p)))) fs)))
(define (su-ratio-candidates bs x)
  (foldl append '()
         (map (lambda (b)
                (let* ((P (if (equal? (car b) '^) (cadr b) #f))
                       (fl (and P (polynomial? P x) (try (factor-list P) (lambda (e) #f)))))
                  (if (and fl (pair? fl))
                      (let ((fs (filter (lambda (p) (contains-sym? (car p) x)) (cdr fl))))
                        (if (and (>= (length fs) 2) (<= (length fs) 4))
                            (foldl append '()
                                   (map (lambda (sp)
                                          (let ((q (list '/ (su-prod (car sp)) (su-prod (cadr sp)))))
                                            (list q (list '* x q) (list '* (list '^ x -1) q))))
                                        (su-subsets-with-first fs)))
                            '()))
                      '())))
              bs)))
(define su-inner-heads '(log exp sin cos tan cot sec csc sinh cosh tanh coth asin acos atan acot asinh acosh atanh acoth))
(define su-node-heads '(log tan tanh atan sin cos sinh cosh))
(define (su-inner-nodes e x)
  (cond ((not (op-expr? e)) '())
        ((and (= (length e) 2) (member? (car e) su-inner-heads) (contains-sym? (cadr e) x))
         (cons e (su-inner-nodes (cadr e) x)))
        (else (foldl append '() (map (lambda (a) (su-inner-nodes a x)) (cdr e))))))
(define (su-inner-candidates f x)
  (foldl append '()
         (map (lambda (n)
                ; линейный аргумент (c + d·x) как u бесполезен: R(u) = f(x(u))/d — это сам f
                (append (if (or (equal? (cadr n) x) (and (polynomial? (cadr n) x) (= (degree (cadr n) x) 1))) '() (list (cadr n)))
                        (if (member? (car n) su-node-heads) (list n) '())))
              (su-dedup (su-inner-nodes f x)))))
(define (su-extra-candidates f x bs)
  (append (su-inner-candidates f x) (su-ratio-candidates bs x) (su-extra-radical bs x)))

; ---------- значения ----------
(define (su-num e) (try (let ((v (eval-num e))) (if (real-numeric? v) v #f)) (lambda (err) #f)))

(define (su-sub e x xv vals)
  (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr))) (replace-expr e x xv) vals))

; строки (u g), g = f/u′, в точках su-pts; u′ — численно, симметричной разностью по пяти точкам (ошибка ≈ h⁴·u⁽⁵⁾ ≈ 1e-13):
; символьный diff громоздкого u (вложенные радикалы) стоил ≈ 50 мс на кандидата
(define su-h 0.001)
(define su-tol 0.000000001)   ; допуск совпадения R(u) и g (относительный)
(define su-maxk 1000)         ; наибольший знаменатель коэффициента R
; значения кэшируются (выражение, точка, набор параметров): f и радикалы xᵏ·b у многих кандидатов общие
(define su-memo (make-hash))
(define (su-ev e x t tag vals)
  (let* ((key (list tag t e)) (v (hash-ref su-memo key 'miss)))
    (if (equal? v 'miss)
        (let ((r (su-num (su-sub e x t vals)))) (hash-set! su-memo key r) r)
        v)))
(define (su-ipow t k) (if (>= k 0) (su-pow t k) (/ 1 (su-pow t (- 0 k)))))
(define (su-ev-u u x t tag vals)
  (if (and (op-expr? u) (equal? (car u) '*) (= (length u) 3)
           (op-expr? (cadr u)) (equal? (car (cadr u)) '^) (equal? (cadr (cadr u)) x) (integer? (caddr (cadr u))))
      (let ((bv (su-ev (caddr u) x t tag vals)))
        (and bv (* (su-ipow t (caddr (cadr u))) bv)))
      (su-ev u x t tag vals)))
(define su-pts2 '(0.36 0.71 0.97 1.51 1.99 2.71 -0.36 -0.97 -1.99 3.7 5.9))   ; свежие точки для проверки найденной R
(define (su-rows f u x vals tag) (su-rows-at f u x vals tag su-pts))
(define (su-rows-at f u x vals tag pts)
  (filter (lambda (r) r)
          (map (lambda (xv)
                 (let* ((ev (lambda (e t) (su-ev-u e x t tag vals)))
                        (a (ev u xv)) (fv (su-ev f x xv tag vals))
                        (um2 (ev u (- xv (* 2 su-h)))) (um1 (ev u (- xv su-h)))
                        (up1 (ev u (+ xv su-h))) (up2 (ev u (+ xv (* 2 su-h))))
                        (vm2 (ev u (- xv (* 4 su-h)))) (vp2 (ev u (+ xv (* 4 su-h)))))
                   (and a fv um2 um1 up1 up2 vm2 vp2
                        (let ((d (/ (+ (- um2 (* 8 um1)) (- (* 8 up1) up2)) (* 12 su-h)))
                              (d2 (/ (+ (- vm2 (* 8 um2)) (- (* 8 up2) vp2)) (* 24 su-h))))
                          ; шаги h и 2h должны давать одно значение: иначе точка близка к особенности u (ошибка ≈ h⁴·u⁽⁵⁾ велика)
                          (and (> (su-abs d) 0.000000001)
                               (<= (su-abs (- d d2)) (* 0.000000001 (su-abs d)))
                               (list a (/ fv d)))))))
               pts)))

; ---------- ядро линейной системы (double) ----------
(define (su-maxabs l) (foldl (lambda (m v) (let ((a (if (< v 0) (- 0 v) v))) (if (> a m) a m))) 0 l))
(define (su-pow u i) (if (= i 0) 1 (* u (su-pow u (- i 1)))))
(define (su-abs v) (if (< v 0) (- 0 v) v))

(define (su-matrix rows dp dq)
  (map (lambda (r)
         (let ((u (car r)) (g (cadr r)))
           (append (map (lambda (i) (su-pow u i)) (range (+ dp 1)))
                   (map (lambda (j) (* -1 g (su-pow u j))) (range (+ dq 1))))))
       rows))

(define (su-nth-max-col mat j) (su-maxabs (map (lambda (r) (nth r j)) mat)))

; mat — список строк длины m; одномерное ядро (вектор) или #f
(define (su-null mat m)
  (let* ((cs (map (lambda (j) (let ((c (su-nth-max-col mat j))) (if (= c 0) 1 c))) (range m)))
         (m1 (map (lambda (r) (map2 (lambda (v c) (/ v c)) r cs)) mat))
         (m2 (map (lambda (r) (let ((s (su-maxabs r))) (if (= s 0) r (map (lambda (v) (/ v s)) r)))) m1)))
    (let loop ((rest m2) (piv '()))
      ; наибольший элемент среди оставшихся строк в столбцах без опоры
      (let ((best (foldl (lambda (b r)
                           (foldl (lambda (b2 j)
                                    (if (any? (lambda (p) (= (car p) j)) piv) b2
                                        (let ((a (su-abs (nth r j)))) (if (> a (car b2)) (list a r j) b2))))
                                  b (range m)))
                         (list 0.00000001 #f #f) rest)))
        (if (cadr best)
            (let* ((r (cadr best)) (c (caddr best)) (pr (map (lambda (v) (/ v (nth r c))) r))
                   (elim (lambda (row) (let ((f (nth row c))) (map2 (lambda (a b) (- a (* f b))) row pr)))))
              (loop (map elim (filter (lambda (row) (not (equal? row r))) rest))
                    (cons (cons c pr) (map (lambda (p) (cons (car p) (elim (cdr p)))) piv))))
            (if (not (= (- m (length piv)) 1))
                (cons (- m (length piv)) #f)
                (let* ((c0 (car (filter (lambda (j) (not (any? (lambda (p) (= (car p) j)) piv))) (range m))))
                       (v (map (lambda (j) (cond ((= j c0) 1)
                                                 (else (let ((p (car (filter (lambda (p) (= (car p) j)) piv))))
                                                         (- 0 (nth (cdr p) c0))))))
                               (range m))))
                  (cons 1 (map2 (lambda (a c) (/ a c)) v cs)))))))))

; ---------- рационализация (цепная дробь) ----------
(define (su-ratz c)
  (let loop ((y c) (h1 1) (k1 0) (h0 0) (k0 1) (n 0))
    (let* ((a (floor y)) (h (+ (* a h1) h0)) (k (+ (* a k1) k0)))
      (cond ((= k 0) #f)
            ((<= (su-abs (- c (/ h k))) (* 0.00000005 (+ 1 (su-abs c)))) (/ h k))
            ((or (> n 14) (> (su-abs k) su-maxk)) #f)
            (else (let ((fr (- y a)))
                    (if (< (su-abs fr) 0.000000000001) #f
                        (loop (/ 1 fr) h k h1 k1 (+ n 1)))))))))

(define (su-ratz-all v)
  (let ((m (su-maxabs v)))
    (and (> m 0)
         (let* ((i (car (filter (lambda (j) (= (su-abs (nth v j)) m)) (range (length v)))))
                (s (nth v i))
                (rs (map (lambda (c) (if (< (su-abs c) 0.00000001) 0 (su-ratz (/ c s)))) v)))
           (and (every? (lambda (r) r) rs) rs)))))

; значение R = P/Q (списки коэффициентов) в точке u; #f при Q = 0
(define (su-r-at pc qc u)
  (let ((p (foldl (lambda (acc c) (+ (* acc u) c)) 0 (reverse pc)))
        (q (foldl (lambda (acc c) (+ (* acc u) c)) 0 (reverse qc))))
    (if (< (su-abs q) 0.000000001) #f (/ p q))))

(define (su-r-fits? pc qc rows)
  (every? (lambda (r)
            (let ((v (su-r-at pc qc (car r))))
              (and v (<= (su-abs (- v (cadr r))) (* su-tol (+ 1 (su-abs (cadr r))))))))
          rows))

(define su-degs '((0 0) (1 0) (2 0) (0 1) (1 1) (0 2) (2 1) (1 2) (2 2) (3 1) (1 3) (0 4) (3 3) (4 4) (2 4) (4 2)))

; rows → (pc qc) с рациональными коэффициентами или #f; rows2 — проверочные (другие параметры) или '()
; u переводится в t = (u − c)/s (c, s — рациональные, середина и полуразмах значений u): иначе степени u плохо обусловлены;
; R(u) рациональна ⇔ рациональна по t, коэффициенты подбираются по t. Результат — (pc qc c s), R(u) = P(t)/Q(t), t = (u − c)/s.
; полуразмах h > 0, округлённый до одной значащей цифры (точное рациональное число; ≥ 1 — до целого)
(define (su-round1 h)
  (let loop ((k 1) (d 1))
    (if (and (< (* h d) 1) (< k 12))
        (loop (+ k 1) (* d 10))
        (let ((n (floor (+ (* h d) 0.5))))
          (/ (if (< n 1) 1 n) d)))))

; многочлен Σ p_i·t^i, t = (u − c)/s, → коэффициенты по u (схема Горнера по спискам, double)
(define (su-padd a b)
  (cond ((null? a) b) ((null? b) a) (else (cons (+ (car a) (car b)) (su-padd (cdr a) (cdr b))))))
(define (su-pmul a b)
  (if (null? a) '() (su-padd (map (lambda (v) (* (car a) v)) b) (cons 0 (su-pmul (cdr a) b)))))
(define (su-to-u pt c s)
  (let ((lin (list (* -1.0 (/ c s)) (/ 1.0 s))))
    (foldl (lambda (acc p) (su-padd (su-pmul acc lin) (list p))) '() (reverse pt))))

(define (su-fit rows0 rows20)
  (let* ((us (map car rows0)) (lo (foldl min (car us) us)) (hi (foldl max (car us) us))
         (s (su-round1 (/ (- hi lo) 2)))
         (c (* s (floor (+ (/ (/ (+ lo hi) 2) s) 0.5))))
         (tf (lambda (rs) (map (lambda (r) (list (/ (- (car r) c) s) (cadr r))) rs)))
         (rows (tf rows0)) (rows2 (tf rows20)))
    (and (>= (length rows) 12)
         (> (- hi lo) 0.000001)
         (let ((tr (take rows 12)))
          ; быстрый отсев: при R степеней ≤ (4, 4) система (4, 4) (10 неизвестных, 12 уравнений) вырождена
          (and (>= (car (su-null (su-matrix tr 4 4) 10)) 1)
           (let loop ((ds su-degs))
             (if (null? ds) #f
                 (let* ((dp (car (car ds))) (dq (cadr (car ds))) (m (+ dp dq 2)))
                   (or (and (<= m 10)
                            (let* ((v (cdr (su-null (su-matrix tr dp dq) m)))
                                   ; из базиса t — обратно в базис u (в double), там коэффициенты R «маленькие» рациональные
                                   (vu (and v (append (su-to-u (take v (+ dp 1)) c s) (su-to-u (drop v (+ dp 1)) c s))))
                                   (rs (and vu (su-ratz-all vu))))
                              (and rs
                                   (let ((pc (take rs (+ dp 1))) (qc (drop rs (+ dp 1))))
                                     (and (su-r-fits? pc qc rows0) (su-r-fits? pc qc rows20)
                                          (list pc qc))))))
                       (loop (cdr ds)))))))))))

; ---------- символьная часть ----------
(define (su-poly cs tv)   ; Σ cs[i]·tv^i (схема Горнера, без упрощения)
  (foldl (lambda (acc c) (list '+ (list '* acc tv) c)) 0 (reverse cs)))

(define (su-recurse R)
  (set! su-depth (+ su-depth 1))
  (unwind-protect
    (let ((v (integrate R su-var)))
      (and v (not (equal? v 'unknown)) (not (int-has-integrate? v)) v))
    (set! su-depth (- su-depth 1))))

(define (su-num-ok? F f x)
  (let ((old *check-numeric-F*))
    (set! *check-numeric-F* #t)
    (let ((st (unwind-protect (try (int-check-F-status F f x) (lambda (err) 'skip))
                              (set! *check-numeric-F* old))))
      (equal? st 'ok))))

; точки быстрого отсева: 13 положительных и 3 отрицательные (R, найденная по x > 0, должна совпасть с g и при x < 0, где она годна)
(define su-sieve-pts (append (take su-pts 13) '(-0.31 -0.62 -1.13)))
; быстрый отсев (INT.HEUR.1): сначала 16 точек — если по ним (≥ 12 годных) R не подбирается, остальные 18 точек не считаются
(define (su-try f x u ps)
  (let* ((va (map2 list ps su-pv-a))
         (r16 (su-rows-at f u x va 'a su-sieve-pts)))
    (and (or (< (length r16) 12) (su-fit r16 '()))
         (su-try-full f x u ps va))))

(define (su-try-full f x u ps va)
  (let* ((rows (su-rows f u x va 'a)))
    (and (>= (length rows) 12)
         (let* ((rows2 (if (null? ps) '() (su-rows f u x (map2 list ps su-pv-b) 'b)))
                (fit (su-fit rows rows2)))
           (cond ((not fit) #f)
                 ; свежие точки (6 шт.): рациональная R должна совпасть с g и там (отсекает приближение гладкой функции)
                 ((not (let ((r3 (su-rows-at f u x va 'a su-pts2)))
                         (and (>= (length r3) 4) (su-r-fits? (car fit) (cadr fit) r3))))
                  (su-reach! 1 'r-not-rational) #f)
                 (else
                  (let* ((pc (car fit)) (qc (cadr fit))
                         (R (try (together (list '/ (su-poly pc su-var) (su-poly qc su-var))) (lambda (e) #f)))
                         (iu (and R (try (su-recurse R) (lambda (e) #f)))))
                    (set! su-info (list u R))
                    (cond ((not R) (su-reach! 1 'r-not-rational) #f)
                          ((not iu) (su-reach! 2 'u-integral-fails) #f)
                          (else
                           (let* ((F0 (replace-expr iu su-var u))
                                  (F (try (simplify F0) (lambda (e) F0))))
                             (cond ((and (not (contains-sym? F su-var)) (int-check F f x) (su-num-ok? F f x)) F)
                                   (else (su-reach! 3 'check-fails) #f))))))))))))

(define (su-run f x)
  (let ((ps (int-symbols f x)))
    (set! su-memo (make-hash))
    (let loop ((cs (su-candidates f x)))
      (if (null? cs) #f
          (or (su-try f x (car cs) ps) (loop (cdr cs)))))))

; (int-hidden-subst f x) → F (F′ = f, int-check) или #f; причина — (int-subst-stats)
(define (int-hidden-subst f x)
  (set! su-why 'no-u) (set! su-rank 0) (set! su-info '())
  (if (> su-depth 0)
      (begin (set! su-why 'nested) #f)
      (let ((r (call-with-time-limit int-subst-time-limit
                                     (lambda () (try (su-run f x) (lambda (e) (set! su-why 'error) #f))))))
        (cond ((and (pair? r) (equal? (car r) 'ok))
               (if (cadr r) (begin (set! su-why #f) (cadr r)) #f))
              (else (set! su-why 'timeout) #f)))))

; дёшево: есть радикал/exp — иначе кандидатов мало и ступень бесполезна
(define (su-applicable? f x)
  (and (= su-depth 0) (or (pair? (su-bricks f x)) (and int-subst-extra (pair? (su-inner-candidates f x))))))
