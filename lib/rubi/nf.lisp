; rubi/nf.lisp — RUBI.NF: одна нормальная форма выражения для обеих сторон сопоставления Rubi.
;
; Rubi написан под автовычисление Mathematica: образец правила и интегранд в Mathematica уже «посчитаны»
; (Flat/Orderless у Plus и Times, свёрнуты числа, склеены одинаковые основания степеней, целая степень
; произведения разложена, `Times[-1, …]` для минуса), но НЕ упрощены: tan/cot/sec/csc остаются своими
; головами, тригонометрических тождеств автовычисление не делает.
;
; Здесь ровно это и только это — без общего `simplify`: он переписывает tan → sin/cos, раскрывает и
; сворачивает степени по-своему, из-за чего правила перестают узнавать выражения (карточка RUBI.NF,
; research/rubi/nf-map.md). Форма одна на всём пути Rubi: вход задачи, каждая подзадача, правая часть
; после подстановки и образцы правил при загрузке.
;
; Что НЕ входит (сознательно): тригонометрические и логарифмические тождества, раскрытие скобок,
; сборка подобных с символьными коэффициентами (Mathematica их тоже не собирает: a x + b x остаётся),
; численное вычисление дробных степеней сверх точных (2^(1/2) остаётся степенью).
(module rubi
  (export rubi-nf *rubi-nf*))

; Единая форма: форма автовычисления Mathematica на всём пути Rubi (вход, подзадачи, правые части,
; образцы правил при загрузке). Шаг NF.4 исправил главный дефект, из-за которого форма не работала
; (имена Mathematica Pi/I в образцах и условиях — правила главы 4 были мёртвыми,
; tools/rubi/generate.mjs, PAT_CONST).
; RUBI.SYM.1 (сверка с symbolica-integrate): под #t считаются cos^n, sec^n, tan, cot, csc, 1/(a+b cos),
; sqrt(a+b sec^2), cos*exp(sin) и т. д. — на полном наборе приёмочных тестов 15 падений из ~1560:
; четыре потери ответа по бюджету (4.5.1.2 sec^2/(a sec+a), 8.8 x²·Li₃(a x²), 1.1.3.6 (x+1+√3)/√(−x³−1),
; шаг integrate-rubi для 1/(x^(4/3)(a+bx))), потеря в 1.4.1 (x·√(a+bx)/√(−a−bx)) и в INT.FIX2.e,
; а также тесты, записанные под старую форму утилит (rubi-ch4/4, /10, /11, /13, rubi-hyp/2, rubi-c,
; rubi/S7, rubi-ch8/5, цепочка шагов 9.3 #24) — список и разбор в REPORT-RUBI-SYM.md.
; Поэтому значение по умолчанию — #f; #t остаётся целью RUBI.SYM.2 (там же план: кэш DeactivateTrig,
; защита от повторного входа шлюза, переписывание тестов формы).
; Значение #f — аварийный выключатель: вход идёт через simplify + ручной инертный порт (utils.lisp),
; как до NF; нужен, чтобы изолировать дефект формы от дефекта правил.
(define *rubi-nf* #t)



; ---------- мелочи ----------
(define (nf-neg x)
  (if (number? x) (- 0 x) (nf-times (list -1 x))))

; коэффициент и «остаток» слагаемого: (* 2 x^2) -> (2 . x^2); x -> (1 . x); 5 -> (5 . 1)
(define (nf-term-split t)
  (cond ((number? t) (cons t 1))
        ((and (pair? t) (equal? (car t) '*))
         (let ((c (foldl * 1 (filter number? (cdr t))))
               (r (filter (lambda (f) (not (number? f))) (cdr t))))
           (cond ((null? r) (cons c 1))
                 ((null? (cdr r)) (cons c (car r)))
                 (else (cons c (cons '* r))))))
        (else (cons 1 t))))

; c·r с раскрытием произведения: Times в Mathematica — Flat, поэтому множитель не остаётся вложенным
; произведением: -1 · (a x^2) = (* -1 a x^2), а не (* -1 (* a x^2)). Вложенное произведение не
; совпадает с образцами правил Rubi вида (* ?c (^ ?x 2)) — из-за него под единой формой не брался,
; например, ∫1/(1-a x^2) (REPORT-RUBI-SYM4.md).
(define (nf-scale r c)
  (cond ((equal? c 1) r)
        ((equal? r 1) c)
        ((and (pair? r) (equal? (car r) '*)) (cons '* (cons c (cdr r))))
        (else (list '* c r))))

; ---------- сборка сумм и произведений ----------
(define (nf-flatten-in op ts acc)
  (cond ((null? ts) (reverse acc))
        ((and (pair? (car ts)) (equal? (car (car ts)) op))
         (nf-flatten-in op (append (cdr (car ts)) (cdr ts)) acc))
        (else (nf-flatten-in op (cdr ts) (cons (car ts) acc)))))

(define (nf-group-add r c acc)
  (cond ((null? acc) (list (cons c r)))
        ((equal? (cdr (car acc)) r) (cons (cons (+ (car (car acc)) c) r) (cdr acc)))
        (else (cons (car acc) (nf-group-add r c (cdr acc))))))

; подобные слагаемые: x + x -> 2 x, 2 x^2 + 3 x^2 -> 5 x^2, x + (-1) x -> 0 (группы с нулём выпадают).
; Порядок слагаемых — по первому появлению (сортировки нет: сопоставитель ac-match коммутативный,
; а сравнения ответов идут через simplify).
(define (nf-groups ts acc)
  (cond ((null? ts) acc)
        (else (nf-groups (cdr ts) (nf-group-add (cdr (car ts)) (car (car ts)) acc)))))

(define (nf-plus ts)
  (let* ((ts (nf-flatten-in '+ ts '()))
         (num (foldl + 0 (filter number? ts)))
         (gs0 (map (lambda (t) (let ((sp (nf-term-split t))) (cons (car sp) (cdr sp))))
                   (filter (lambda (t) (not (number? t))) ts)))
         (gs (filter (lambda (g) (not (equal? (car g) 0))) (nf-groups gs0 '())))
         (out (map (lambda (g) (nf-scale (cdr g) (car g))) gs)))
    (cond ((and (equal? num 0) (null? out)) 0)
          ((equal? num 0) (if (null? (cdr out)) (car out) (cons '+ out)))
          ((null? out) num)
          (else (cons '+ (cons num out))))))

; основание и показатель множителя: x -> (x . 1); (^ u -2) -> (u . -2)
(define (nf-mb-split f)
  (cond ((and (pair? f) (equal? (car f) '^) (= (length f) 3)) (cons (cadr f) (caddr f)))
        (else (cons f 1))))

; RUBI.NF.CONF: Plus — Orderless, поэтому основания, различающиеся лишь порядком слагаемых/множителей, одинаковы
; ((a+b)^-1 (b+a) = 1); сравнение с сортировкой — только если обычное equal? не сработало и голова/длина совпали.
(define (nf-acsort e)
  (cond ((not (pair? e)) e)
        ((equal? (car e) 'quote) e)
        ((member? (car e) '(+ *))
         (cons (car e) (sort (map nf-acsort (cdr e)) (lambda (a b) (string<? (to-string a) (to-string b))))))
        (else (cons (car e) (map nf-acsort (cdr e))))))

(define (nf-same-base? a b)
  (or (equal? a b)
      (and (pair? a) (pair? b) (member? (car a) '(+ *)) (equal? (car a) (car b)) (= (length a) (length b))
           (equal? (nf-acsort a) (nf-acsort b)))))

; показатели: числа складываются, остальное — через nf-plus (та же форма суммы)
(define (nf-add-exp a b)
  (if (and (number? a) (number? b)) (+ a b) (nf-plus (list a b))))

(define (nf-mb-add b e acc)
  (cond ((null? acc) (list (list b e)))
        ((nf-same-base? (car (car acc)) b) (cons (list (car (car acc)) (nf-add-exp (cadr (car acc)) e)) (cdr acc)))
        (else (cons (car acc) (nf-mb-add b e (cdr acc))))))

; u^a u^b -> u^(a+b): в Mathematica Times склеивает одинаковые основания; нулевой показатель множитель убирает
; (раньше оставался литерал 1: x^-1 · x давало (* 1 …)); числовое основание считается (2^(1/2) 2^(1/2) = 2)
(define (nf-merge-bases fs)
  (filter (lambda (f) (not (equal? f 1)))
          (map (lambda (g)
                 (let ((b (car g)) (e (cadr g)))
                   (cond ((equal? e 0) 1)
                         ((equal? e 1) b)
                         ((and (number? b) (integer? e)) (nf-pow b e))
                         ((and (equal? b '%i) (integer? e)) (nf-i-pow e))
                         ; 2^(1/2) · 2^(3/2) = 2^2; 2^(1/2) · 2^(2/3) = 2^(7/6) -> 2 · 2^(1/6) (целая часть — в коэффициент)
                         ((and (nf-exact? b) (integer? b) (> b 1) (nf-exact? e) (or (> e 1) (< e -1)))
                          (let ((ir (nf-int-radical b e)))
                            (if (cdr ir) (list '* (car ir) (cdr ir)) (car ir))))
                         (else (list '^ b e)))))
               (foldl (lambda (acc f) (let ((sp (nf-mb-split f))) (nf-mb-add (car sp) (cdr sp) acc))) '() fs))))

; ---------- числа-радикалы (автовычисление Mathematica) ----------
; 2 Sqrt[2] = 2^(3/2) -> 2 Sqrt[2]; 2 · 2^(-1/2) -> Sqrt[2]; 8^(1/3) -> 2; 4^(1/3) -> 2^(2/3); (1/2)^(1/2) -> 2^(-1/2)
(define (nf-exact? x) (member? (type-of x) '(integer rational)))

(define (nf-rat-ipow b k) (if (< k 0) (/ 1 (^ b (- 0 k))) (^ b k)))

; точный целый корень q-й степени из целого n > 0 или #f (двоичный поиск)
(define (nf-iroot n q)
  (let loop ((lo 1) (hi n))
    (if (> lo hi)
        #f
        (let* ((mid (quotient (+ lo hi) 2)) (p (^ mid q)))
          (cond ((= p n) mid) ((< p n) (loop (+ mid 1) hi)) (else (loop lo (- mid 1))))))))

; n^e для целого n > 1 и нецелого рационального e: (коэффициент . радикал или #f); множители m^q вынимаются
; из n (12^(1/2) = 2 · 3^(1/2)), целая часть показателя уходит в коэффициент (2^(3/2) = 2 · 2^(1/2))
(define (nf-strip-powers n q)                ; (fac . cur): n = fac^q · cur (для n < 10^8; иначе fac = 1)
  (if (>= n 100000000)
      (cons 1 n)
      (let loop ((m 2) (cur n) (fac 1))
        (cond ((> (^ m q) cur) (cons fac cur))
              ((= (modulo cur (^ m q)) 0) (loop m (quotient cur (^ m q)) (* fac m)))
              (else (loop (+ m 1) cur fac))))))

(define (nf-int-radical n e)
  (if (equal? n 1)
      (cons 1 #f)
      (let* ((q (denom e)) (p (numer e))
             (sp (nf-strip-powers n q))
             (root (nf-iroot (cdr sp) q)))
        (cond (root (cons (nf-rat-ipow (* (car sp) root) p) #f))
              (else
               (let ((t (quotient p q)))
                 (cons (* (nf-rat-ipow (car sp) p) (nf-rat-ipow (cdr sp) t)) (list '^ (cdr sp) (- e t)))))))))

(define (nf-rat-radical b e)
  (let ((nb (nf-int-radical (numer b) e)) (db (nf-int-radical (denom b) (- 0 e))))
    (nf-times (append (list (car nb) (car db)) (if (cdr nb) (list (cdr nb)) '()) (if (cdr db) (list (cdr db)) '())))))

(define (nf-count-div n b) (let loop ((n n) (k 0)) (if (and (> n 0) (= (modulo n b) 0)) (loop (quotient n b) (+ k 1)) k)))
(define (nf-mult-of b c)
  (let ((nn (nf-count-div (abs (numer c)) b)) (dd (nf-count-div (denom c) b)))
    (cond ((> nn 0) nn) ((> dd 0) (- 0 dd)) (else 0))))

; коэффициент c поглощает кратные B: 2 · 2^(-1/2) -> 2^(1/2); 4 · 2^(-1/2) -> 2 · 2^(1/2); (1/2) · 2^(1/2) -> 2^(-1/2)
(define (nf-absorb-one c f)
  (if (and (pair? f) (equal? (car f) '^) (= (length f) 3) (integer? (cadr f)) (> (cadr f) 1)
           (nf-exact? (caddr f)) (not (integer? (caddr f))) (nf-exact? c) (not (equal? c 0)))
      (let* ((b (cadr f)) (j (nf-mult-of b c)))
        (if (equal? j 0)
            (cons c f)
            (let* ((tot (+ (caddr f) j)) (t (quotient (numer tot) (denom tot))))
              (cons (* c (nf-rat-ipow b (- t j))) (list '^ b (- tot t))))))
      (cons c f)))

(define (nf-radical-absorb c rs)
  (let loop ((rs rs) (c c) (acc '()))
    (if (null? rs)
        (cons c (reverse acc))
        (let ((r (nf-absorb-one c (car rs))))
          (loop (cdr rs) (car r) (cons (cdr r) acc))))))

(define (nf-times-fin coef merged)
  (let* ((c (foldl * coef (filter number? merged)))
         (ab (nf-radical-absorb c (filter (lambda (f) (not (number? f))) merged)))
         (c2 (car ab)) (rs (cdr ab)))
    (cond ((equal? c2 0) 0)
          ((null? rs) c2)
          ((equal? c2 1) (if (null? (cdr rs)) (car rs) (cons '* rs)))
          (else (cons '* (cons c2 rs))))))

(define (nf-times fs)
  (let* ((fs (nf-flatten-in '* fs '()))
         (coef (foldl * 1 (filter number? fs)))
         (rest (filter (lambda (f) (not (number? f))) fs)))
    (if (equal? coef 0)
        0
        (let* ((merged (if (null? rest) '() (nf-merge-bases rest)))
               (flat (nf-flatten-in '* merged '())))
          (if (equal? flat merged)
              (nf-times-fin coef merged)
              (nf-times (cons coef flat)))))))

; ---------- степени ----------
(define (nf-rep b n) (if (< n 1) '() (cons b (nf-rep b (- n 1)))))

(define (nf-num-pow b e)
  ; точные степени числа: 2^3 = 8, 2^-1 = 1/2; положительное рациональное число в нецелой рациональной степени —
  ; радикал в форме Mathematica (nf-rat-radical: 4^(1/2) = 2, 8^(1/2) = 2 Sqrt[2], 2^(3/2) = 2 Sqrt[2], (1/2)^(1/2) = 2^(-1/2))
  (cond ((equal? e 0) 1)
        ((equal? e 1) b)
        ((and (integer? e) (> e 0)) (foldl * 1 (nf-rep b e)))
        ((and (integer? e) (< e 0) (not (equal? b 0))) (nf-num-pow (/ 1 b) (- 0 e)))
        ((and (nf-exact? e) (nf-exact? b) (> b 0)) (nf-rat-radical b e))
        ; (-c)^(p/2) = I^p c^(p/2): Sqrt[-4] = 2 I, (-1)^(-3/2) = I (автовычисление Mathematica)
        ((and (nf-exact? e) (nf-exact? b) (< b 0) (equal? (denom e) 2))
         (nf-times (list (nf-i-pow (numer e)) (nf-num-pow (- 0 b) e))))
        (else (list '^ b e))))

; I^k: 1, I, -1, -I
(define (nf-i-pow k)
  (let ((r (modulo (+ (modulo k 4) 4) 4)))
    (cond ((= r 0) 1) ((= r 1) '%i) ((= r 2) -1) (else (list '* -1 '%i)))))

(define (nf-pow b e)
  (cond ((equal? e 0) 1)
        ((equal? e 1) b)
        ((and (number? b) (number? e)) (nf-num-pow b e))
        ((and (equal? b '%i) (integer? e)) (nf-i-pow e))
        ; (c·u)^r = c^r · u^r при c > 0 рациональном и нецелом рациональном r (автовычисление Mathematica:
        ; Sqrt[4 x] -> 2 Sqrt[x], Sqrt[2 x] -> Sqrt[2] Sqrt[x], (2 x)^(1/3) -> 2^(1/3) x^(1/3)); символьный показатель не трогаем
        ((and (number? e) (nf-exact? e) (not (integer? e)) (pair? b) (equal? (car b) '*) (>= (length b) 3)
              (number? (cadr b)) (nf-exact? (cadr b)) (> (cadr b) 0) (not (equal? (cadr b) 1)))
         (nf-times (list (nf-num-pow (cadr b) e)
                         (nf-pow (if (null? (cdddr b)) (caddr b) (cons '* (cddr b))) e))))
        ; (u^a)^n = u^(a n) при целом n (верно на любой ветви и при символьном a); результат — снова степень (u^(a n))
        ((and (pair? b) (equal? (car b) '^) (= (length b) 3) (integer? e))
         (nf-pow (cadr b) (nf-times (list (caddr b) e))))
        ; (u v)^n = u^n v^n при целом n (в т.ч. n = -1: 1/(u v) = u^-1 v^-1)
        ((and (pair? b) (equal? (car b) '*) (integer? e))
         (nf-times (map (lambda (f) (nf-pow f e)) (cdr b))))
        (else (list '^ b e))))

; ---------- вход ----------
(define (nf-ex e)
  (cond ((number? e) e)
        ((symbol? e) (if (equal? e 'I) '%i e))
        ((not (pair? e)) e)
        (else
         (let ((h (car e)))
           (cond ((equal? h 'sqrt) (nf-pow (nf-ex (cadr e)) 1/2))
                 ((equal? h 'exp) (nf-pow 'E (nf-ex (cadr e))))
                 ((equal? h 'quote) e)
                 ((equal? h '-)
                  (if (null? (cddr e))
                      (nf-times (list -1 (nf-ex (cadr e))))
                      (nf-plus (cons (nf-ex (cadr e)) (map (lambda (a) (nf-neg (nf-ex a))) (cddr e))))))
                 ((equal? h '/)
                  (if (null? (cddr e))
                      (nf-pow (nf-ex (cadr e)) -1)
                      (nf-times (cons (nf-ex (cadr e)) (map (lambda (a) (nf-pow (nf-ex a) -1)) (cddr e))))))
                 ((equal? h '+) (nf-plus (map nf-ex (cdr e))))
                 ((equal? h '*) (nf-times (map nf-ex (cdr e))))
                 ((and (equal? h '^) (= (length e) 3)) (nf-pow (nf-ex (cadr e)) (nf-ex (caddr e))))
                 (else (cons h (map nf-ex (cdr e)))))))))

; Нормальная форма выражения: автовычисление Mathematica без тождеств и без общего simplify.
; Форма одна на обе стороны сопоставления: ею нормализуются вход, подзадачи, правые части и образцы правил.
(define (rubi-nf e) (nf-ex e))

