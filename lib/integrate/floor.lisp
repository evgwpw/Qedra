; floor.lisp — определённые интегралы с floor / ceiling (шаг INT.FLOOR)
;
; Идея: на отрезке [a, b] найти точки скачков и разбить на куски, где каждый узел (floor u) / (ceiling u) постоянен;
; на куске узел заменяется целым, остаток — обычная подынтегральная без floor, интеграл по куску — обычным integrate
; (многочлен и константа — быстрой формулой); ответ — сумма по кускам.
;   1. «листовые» узлы — floor/ceiling, у которых в аргументе нет других floor/ceiling; аргумент без x — просто число;
;   2. аргумент с x: u монотонна на отрезке (проверка по 30 точкам; линейная — всегда), целые k строго между значениями
;      u на концах дают точки скачков x_k = u⁻¹(k): обращение цепочки + − * ^ sqrt log exp (точно), затем сверка
;      u(x_k) = k численно; ветвь вне отрезка или немонотонность — отказ (#f), а не догадка;
;   3. на каждом куске значение узла = floor(u) в трёх внутренних точках (должны совпасть, не у целого); внешние узлы
;      (floor от выражения с уже подставленными целыми) обрабатываются следующим кругом по тому же куску;
;   4. проверка: на ≤ 10 кусках (первом, последнем и равномерно) точное значение сравнивается с квадратурой
;      Гаусса — Лежандра ИСХОДНОЙ подынтегральной (со своими floor) по 32 внутренним узлам.
; Отказ (#f) — бесконечно много кусков (floor(√(1+1/x)) у 0), немонотонное u (floor(sin x)), больше ifl-max-pieces кусков:
; тогда определённый интеграл остаётся невычисленной формой — классический путь НЕ зовётся (diff floor = 0 дал бы ложную
; первообразную x·floor(x)). Внутренние имена: ifl-.

(module integrate
  (export))

(define ifl-max-pieces 5000)
(define ifl-max-slow 2500)       ; кусков, интегрируемых общим integrate (не константа и не многочлен)
(define ifl-eps 0.000000001)

(define (ifl-node? t) (and (pair? t) (member? (car t) '(floor ceiling)) (= (length t) 2)))
(define (ifl-has? e) (and (pair? e) (or (ifl-node? e) (any? ifl-has? (cdr e)))))
(define (ifl-uniq l) (foldl (lambda (acc t) (if (member? t acc) acc (append acc (list t)))) '() l))
(define (ifl-leaf-nodes e)
  (cond ((not (pair? e)) '())
        ((and (ifl-node? e) (not (ifl-has? (cadr e)))) (list e))
        (else (ifl-uniq (append-map ifl-leaf-nodes (cdr e))))))
(define (ifl-subst e node v)
  (cond ((equal? e node) v)
        ((pair? e) (cons (car e) (map (lambda (t) (ifl-subst t node v)) (cdr e))))
        (else e)))
(define (ifl-subst-all e nodes vals)
  (if (null? nodes) e (ifl-subst-all (ifl-subst e (car nodes) (car vals)) (cdr nodes) (cdr vals))))

; ---------- численное значение ----------
(define (ifl-num e)
  (let ((v (try (eval-num e) (lambda (er) #f))))
    (and v (number? v) (equal? (type-of v) 'float) (= v v) (< (abs v) 1000000000000000.0) v)))
(define (ifl-at u x s) (ifl-num (replace-expr u x s)))
(define (ifl-exact? v) (and (number? v) (member? (type-of v) '(integer rational))))
(define (ifl-big? p) (or (equal? p 'inf) (equal? p '-inf)))
; числовая позиция конца: ±1e12 для бесконечности
(define (ifl-pos p)
  (cond ((equal? p 'inf) 1000000000000.0) ((equal? p '-inf) -1000000000000.0)
        (else (ifl-num p))))
(define (ifl-round head v) (if (equal? head 'floor) (floor v) (ceiling v)))

; значение узла от постоянного аргумента: целое или #f
(define (ifl-const-val node)
  (let ((s (try (simplify (cadr node)) (lambda (er) #f))))
    (cond ((not s) #f)
          ((ifl-exact? s) (ifl-round (car node) s))
          (else (let ((n (ifl-num s)))
                  (and n (> (min (- n (floor n)) (- (ceiling n) n)) ifl-eps) (ifl-round (car node) n)))))))

; ---------- обращение цепочки ----------
; exp(t) с t = log b или n·log b (n — число): b или b^n (exp(6·log 2) сам упрощатель не сворачивает)
(define (ifl-exp-of t)
  (cond ((and (pair? t) (equal? (car t) 'log) (= (length t) 2)) (cadr t))
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3) (ifl-exact? (cadr t))
              (pair? (caddr t)) (equal? (car (caddr t)) 'log) (= (length (caddr t)) 2))
         (simplify (list '^ (cadr (caddr t)) (cadr t))))
        (else (simplify (list 'exp t)))))

(define (ifl-invert u x t)
  (cond ((equal? u x) t)
        ((not (pair? u)) #f)
        ((equal? (car u) '+)
         (let ((vs (filter (lambda (s) (not (x-free? s x))) (cdr u))) (cs (filter (lambda (s) (x-free? s x)) (cdr u))))
           (and (= (length vs) 1)
                (ifl-invert (car vs) x (simplify (if (null? cs) t (- t (apply + cs))))))))
        ((equal? (car u) '*)
         (let ((vs (filter (lambda (s) (not (x-free? s x))) (cdr u))) (cs (filter (lambda (s) (x-free? s x)) (cdr u))))
           (and (= (length vs) 1)
                (ifl-invert (car vs) x (simplify (if (null? cs) t (/ t (apply * cs))))))))
        ((equal? (car u) '^)
         (let ((b (cadr u)) (r (caddr u)))
           (cond ((and (not (x-free? b x)) (x-free? r x) (not (equal? r 0)))
                  (ifl-invert b x (simplify (list '^ t (/ 1 r)))))
                 ((and (x-free? b x) (not (x-free? r x)))
                  (ifl-invert r x (simplify (list '/ (list 'log t) (list 'log b)))))
                 (else #f))))
        ((and (equal? (car u) 'sqrt) (= (length u) 2)) (ifl-invert (cadr u) x (simplify (list '^ t 2))))
        ((and (equal? (car u) 'log) (= (length u) 2)) (ifl-invert (cadr u) x (ifl-exp-of t)))
        ((and (equal? (car u) 'exp) (= (length u) 2)) (ifl-invert (cadr u) x (simplify (list 'log t))))
        (else #f)))

; ---------- значения u на концах, монотонность ----------
(define (ifl-lim-inf u x s)
  (let ((a (ifl-at u x (* s 100000000.0))) (b (ifl-at u x (* s 1000000000000.0))))
    (and a b (<= (abs (- a b)) (* 0.000001 (+ 1 (abs a)))) b)))
(define (ifl-end-near u x p pother)     ; p — конечный конец; значение вблизи p внутри отрезка
  (let* ((pn (ifl-pos p)) (on (ifl-pos pother)))
    (and pn on
         (let* ((w (if (> (abs on) 100000000000.0) 1.0 (abs (- on pn)))) (dir (if (< pn on) 1.0 -1.0)) (h (* w 0.000000001))
                (a (ifl-at u x (+ pn (* dir h)))) (b (ifl-at u x (+ pn (* dir 10.0 h)))))
           (and a b (<= (abs (- a b)) (* 0.000001 (+ 1 (abs a)))) a)))))
(define (ifl-end-val u x p pother)
  (cond ((equal? p 'inf) (ifl-lim-inf u x 1.0))
        ((equal? p '-inf) (ifl-lim-inf u x -1.0))
        (else (let ((v (try (simplify (replace-expr u x p)) (lambda (er) #f))))
                (cond ((and v (ifl-exact? v)) v)
                      ((and v (ifl-num v)) (ifl-num v))
                      (else (ifl-end-near u x p pother)))))))

; точки внутри (pa, pb) по возрастанию (n штук); бесконечные концы — по степеням десяти от конечного
(define ifl-pw (let loop ((i 0) (v 0.1) (acc '())) (if (= i 30) (reverse acc) (loop (+ i 1) (* v 3.1622776601683795) (cons v acc)))))
(define (ifl-samples pa pb n)
  (let ((ia (< pa -100000000000.0)) (ib (> pb 100000000000.0)))
    (cond ((and (not ia) (not ib)) (map (lambda (i) (+ pa (* (- pb pa) (/ (+ i 1.0) (+ n 1.0))))) (range n)))
          ((and (not ia) ib) (map (lambda (d) (+ pa d)) (take ifl-pw n)))
          ((and ia (not ib)) (reverse (map (lambda (d) (- pb d)) (take ifl-pw n))))
          (else (append (reverse (map (lambda (d) (- 0.0 d)) (take ifl-pw (quotient n 2))))
                        (list 0.3)
                        (take ifl-pw (quotient n 2)))))))

(define (ifl-linear? u x) (and (polynomial? u x) (= (degree u x) 1)))
(define (ifl-monotone? u x pa pb)
  (or (ifl-linear? u x)
      (let ((vs (map (lambda (s) (ifl-at u x s)) (ifl-samples pa pb 30))))
        (and (every? (lambda (v) v) vs)
             (let ((ds (map2 - (cdr vs) (take vs (- (length vs) 1)))))
               (or (every? (lambda (d) (> d 0)) ds) (every? (lambda (d) (< d 0)) ds)))))))

; ---------- точки скачков узла ----------
; → список (позиция . точное x_k) по возрастанию позиции (внутри (p, q)); #f — отказ
(define (ifl-breaks u x p q)
  (let ((pa (ifl-pos p)) (pb (ifl-pos q)))
    (and pa pb
         (ifl-monotone? u x pa pb)
         (let ((vp (ifl-end-val u x p q)) (vq (ifl-end-val u x q p)))
           (and vp vq
                (let* ((lo (if (< vp vq) vp vq)) (hi (if (< vp vq) vq vp))
                       (eps (if (and (ifl-exact? lo) (ifl-exact? hi)) 0 ifl-eps))
                       (kmin (+ (floor (- lo eps)) 1)) (kmax (- (ceiling (+ hi eps)) 1)))
                  (cond ((> kmin kmax) '())
                        ((> (+ (- kmax kmin) 1) ifl-max-pieces) #f)
                        (else (ifl-break-list u x pa pb (map (lambda (i) (+ kmin i)) (range (+ (- kmax kmin) 1))))))))))))

(define (ifl-break-list u x pa pb ks)
  (let loop ((ks ks) (acc '()))
    (if (null? ks)
        (sort acc (lambda (s t) (< (car s) (car t))))
        (let* ((xk (try (ifl-invert u x (car ks)) (lambda (er) #f)))
               (xn (and xk (ifl-num xk)))
               (tol (and xn (* ifl-eps (+ 1 (abs xn))))))
          (cond ((not xn) #f)
                ((or (<= (abs (- xn pa)) tol) (<= (abs (- xn pb)) tol)) (loop (cdr ks) acc))
                ((or (< xn pa) (> xn pb)) #f)
                (else (let ((back (ifl-at u x xn)))
                        (and back (<= (abs (- back (car ks))) (* 0.0000001 (+ 1 (abs (car ks)))))
                             (loop (cdr ks) (cons (cons xn xk) acc))))))))))

; ---------- разбиение ----------
; точки (позиция . x): объединение по узлам, одинаковые позиции склеены
(define (ifl-merge-points pts)
  (let ((s (sort pts (lambda (a b) (< (car a) (car b))))))
    (let loop ((s s) (acc '()))
      (cond ((null? s) (reverse acc))
            ((and (pair? acc) (<= (abs (- (car (car s)) (car (car acc)))) (* ifl-eps (+ 1 (abs (car (car s)))))))
             (loop (cdr s) acc))
            (else (loop (cdr s) (cons (car s) acc)))))))

; значение узла на куске (pl, pr): целое или #f (три точки должны дать одно значение, не вблизи целого)
(define (ifl-node-val node x pl pr)
  (let* ((pa (ifl-pos pl)) (pb (ifl-pos pr)) (u (cadr node)))
    (and pa pb
         (let* ((ss (cond ((and (< pb 100000000000.0) (> pa -100000000000.0))
                           (map (lambda (t) (+ pa (* (- pb pa) t))) '(0.25 0.5 0.75)))
                          ((< pb 100000000000.0) (map (lambda (d) (- pb d)) '(10.0 1000.0 100000.0)))
                          ((> pa -100000000000.0) (map (lambda (d) (+ pa d)) '(10.0 1000.0 100000.0)))
                          (else '(-100.0 0.3 100.0))))
                (vs (map (lambda (s) (ifl-at u x s)) ss)))
           (and (every? (lambda (v) v) vs)
                (every? (lambda (v) (> (min (- v (floor v)) (- (ceiling v) v)) 0.0000001)) vs)
                (let ((ns (map (lambda (v) (ifl-round (car node) v)) vs)))
                  (and (= (car ns) (cadr ns)) (= (car ns) (caddr ns)) (car ns))))))))

; → список кусков (p q e') без floor/ceiling | #f
(define (ifl-pieces e x p q)
  (let ((nodes (ifl-leaf-nodes e)))
    (if (null? nodes)
        (list (list p q e))
        (let ((free (filter (lambda (n) (x-free? (cadr n) x)) nodes)))
          (if (pair? free)
              (let ((vals (map ifl-const-val free)))
                (and (every? (lambda (v) v) vals)
                     (ifl-pieces (simplify (ifl-subst-all e free vals)) x p q)))
              (let ((bs (map (lambda (n) (ifl-breaks (cadr n) x p q)) nodes)))
                (and (every? (lambda (b) b) bs)
                     (let* ((pts (ifl-merge-points (apply append bs)))
                            (cuts (append (list (cons (ifl-pos p) p)) pts (list (cons (ifl-pos q) q)))))
                       (and (<= (length cuts) (+ ifl-max-pieces 2))
                            (ifl-pieces-on cuts nodes e x))))))))))

(define (ifl-pieces-on cuts nodes e x)
  (let loop ((cs cuts) (acc '()))
    (if (null? (cdr cs))
        (and (<= (length acc) ifl-max-pieces) (reverse acc))
        (let* ((pl (cdr (car cs))) (pr (cdr (cadr cs)))
               (vals (map (lambda (n) (ifl-node-val n x pl pr)) nodes)))
          (and (every? (lambda (v) v) vals)
               (let* ((e1 (simplify (ifl-subst-all e nodes vals))) (sub (ifl-pieces e1 x pl pr)))
                 ; кусок без дальнейшего разбиения помнит шаблон (e, узлы, значения): параметрический интеграл — один на все
                 (and sub (loop (cdr cs)
                                (append (reverse (if (and (null? (cdr sub)) (equal? (caddr (car sub)) e1))
                                                     (list (list pl pr e1 (list e nodes vals)))
                                                     sub))
                                        acc)))))))))

; ---------- интеграл по куску ----------
(define (ifl-ipow r n) (if (= n 0) 1 (* r (ifl-ipow r (- n 1)))))
(define (ifl-poly-int e x pl pr)
  (let ((d (degree e x)))
    (foldl (lambda (acc j)
             (+ acc (* (/ (coeff e x j) (+ j 1)) (- (ifl-ipow pr (+ j 1)) (ifl-ipow pl (+ j 1))))))
           0 (range (+ d 1)))))
(define ifl-slow-count 0)
(define ifl-templates '())      ; ((e . (F . символы-параметры) | #f) …) — первообразные шаблонов с параметрами вместо floor

; первообразная шаблона e, где узлы заменены символами ifl_pN: (F . символы) | #f
(define (ifl-template-F meta x)
  (let ((hit (assoc (car meta) ifl-templates)))
    (if hit
        (cdr hit)
        (let* ((syms (map (lambda (i) (string->symbol (string-append "ifl_p" (to-string i)))) (range (length (cadr meta)))))
               (ep (simplify (ifl-subst-all (car meta) (cadr meta) syms)))
               (F (int-guard (lambda () (integrate ep x))))
               (r (and F (not (int-has-integrate? F)) (cons F syms))))
          (begin (set! ifl-templates (cons (cons (car meta) r) ifl-templates)) r)))))

; значение куска по шаблону; проверено квадратурой по самому куску (e1 без floor) — иначе #f
(define (ifl-param-int e1 meta x pl pr)
  (let ((tf (ifl-template-F meta x)))
    (and tf
         (let* ((rules (map2 list (cdr tf) (caddr meta)))
                (v (try (simplify (- (subst (cons (list x pr) rules) (car tf)) (subst (cons (list x pl) rules) (car tf))))
                        (lambda (er) #f)))
                (vn (and v (ifl-num v)))
                (g (and vn (try (ifl-gl e1 x (ifl-pos pl) (ifl-pos pr)) (lambda (er) #f)))))
           (and g (number? g) (<= (abs (- g vn)) (* 0.0002 (+ 1 (abs vn)))) v)))))

(define (ifl-piece-int e x pl pr meta)
  (cond ((equal? e 0) 0)
        ((and (ifl-big? pl) (ifl-big? pr) (equal? pl pr)) 0)
        ((x-free? e x) (if (or (ifl-big? pl) (ifl-big? pr)) #f (simplify (* e (- pr pl)))))
        ((and (not (ifl-big? pl)) (not (ifl-big? pr)) (polynomial? e x)) (simplify (ifl-poly-int e x pl pr)))
        (else (or (and meta (not (ifl-big? pl)) (not (ifl-big? pr)) (> ifl-slow-count 20) (ifl-param-int e meta x pl pr))
                  (begin
                    (set! ifl-slow-count (+ ifl-slow-count 1))
                    (and (<= ifl-slow-count ifl-max-slow)
                         (let ((v (integrate e x pl pr)))
                           (and (not (int-unevaluated? v)) v))))))))

; ---------- проверка квадратурой Гаусса — Лежандра (8 узлов × 4 панели) ----------
(define ifl-gl-nodes '((0.1834346424956498 . 0.3626837833783620) (0.5255324099163290 . 0.3137066458778873)
                       (0.7966664774136267 . 0.2223810344533745) (0.9602898564975363 . 0.1012285362903763)))
(define (ifl-gl e x a b)       ; ∫_a^b e dx численно (a, b — числа), e — с floor
  (let ((h (/ (- b a) 4.0)))
    (foldl (lambda (acc k)
             (let* ((c (+ a (* h (+ k 0.5)))) (r (/ h 2.0)))
               (+ acc (foldl (lambda (s nw)
                               (let ((v1 (ifl-at e x (+ c (* r (car nw))))) (v2 (ifl-at e x (- c (* r (car nw))))))
                                 (and s v1 v2 (+ s (* r (cdr nw) (+ v1 v2))))))
                             0.0 ifl-gl-nodes))))
           0.0 (range 4))))

(define (ifl-check-indices n)
  (if (<= n 10)
      (range n)
      (ifl-uniq (append (list 0 (- n 1)) (map (lambda (i) (quotient (* i (- n 1)) 8)) (range 9))))))

(define (ifl-verify e x pieces vals)
  (every? (lambda (i)
            (let* ((pc (nth pieces i)) (pa (ifl-pos (car pc))) (pb (ifl-pos (cadr pc))) (v (ifl-num (nth vals i))))
              (cond ((or (not pa) (not pb)) #f)
                    ((or (< pa -100000000000.0) (> pb 100000000000.0)) #t)      ; бесконечный кусок — только значение
                    ((not v) #f)
                    (else (let ((g (try (ifl-gl e x pa pb) (lambda (er) #f))))
                            (and g (number? g) (<= (abs (- g v)) (* 0.0002 (+ 1 (abs v))))))))))
          (ifl-check-indices (length pieces))))

; ---------- итог ----------
; суммы логарифмов целых (floor(eˣ): Σ k·(log(k+1) − log k)) — через логарифмы простых: 14 − 4·log 2 − 2·log 3 − log 5 − log 7
(define (ifl-prime-logs e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'log) (= (length e) 2) (integer? (cadr e)) (> (cadr e) 1) (< (cadr e) 10000000))
         (apply + (map (lambda (p) (list 'log p)) (numtheory::nt-prime-factors (cadr e)))))
        (else (cons (car e) (map ifl-prime-logs (cdr e))))))
(define (ifl-final v)
  (if (contains-sym? v 'log) (simplify (expand (ifl-prime-logs (expand v)))) v))

; сумма кусков: линейная комбинация по нечисловым множителям (хеш), чтобы тысячи слагаемых с логарифмами не складывались
; попарно (квадратично); логарифмы целых раскладываются на простые
(define (ifl-term-split t)       ; → (ключ . коэффициент); ключ 'const для числа
  (cond ((number? t) (cons 'const t))
        ((and (pair? t) (equal? (car t) '*) (number? (cadr t)))
         (cons (if (null? (cdr (cddr t))) (caddr t) (cons '* (cddr t))) (cadr t)))
        (else (cons t 1))))
(define (ifl-sum vals)
  (if (every? ifl-exact? vals)
      (foldl (lambda (acc v) (+ acc v)) 0 vals)
      (let ((h (make-hash)))
        (begin
          (for-each (lambda (v)
                      (let* ((w (expand v)) (w2 (if (contains-sym? w 'log) (expand (ifl-prime-logs w)) w))
                             (ts (if (and (pair? w2) (equal? (car w2) '+)) (cdr w2) (list w2))))
                        (for-each (lambda (t)
                                    (let ((kc (ifl-term-split t)))
                                      (hash-set! h (car kc) (+ (hash-ref h (car kc) 0) (cdr kc)))))
                                  ts)))
                    vals)
          (simplify (apply + (map (lambda (k) (if (equal? k 'const) (hash-ref h k 0) (* (hash-ref h k 0) k))) (hash-keys h))))))))

; ---------- вход ----------
(define (ifl-compute e x a b)
  (set! ifl-slow-count 0)
  (set! ifl-templates '())
  (let ((pieces (ifl-pieces (simplify e) x a b)))
    (and pieces (pair? pieces)
         (let ((vals (map (lambda (pc) (ifl-piece-int (caddr pc) x (car pc) (cadr pc) (and (pair? (cdddr pc)) (cadddr pc)))) pieces)))
           (and (every? (lambda (v) v) vals)
                (let ((total (ifl-final (ifl-sum vals))))
                  (and (ifl-verify e x pieces vals) total)))))))

; определённый интеграл: значение или невычисленная форма (integrate e x a b)
(define (ifl-definite e x a b)
  (let ((na (ifl-pos a)) (nb (ifl-pos b)))
    (cond ((not (and na nb)) (list 'integrate e x a b))
          ((< nb na) (let ((r (ifl-definite e x b a))) (if (int-unevaluated? r) (list 'integrate e x a b) (simplify (- r)))))
          ((= na nb) 0)
          (else (or (int-guard (lambda () (ifl-compute e x a b))) (list 'integrate e x a b))))))
