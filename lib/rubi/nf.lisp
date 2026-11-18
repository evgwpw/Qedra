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

; Единая форма: флаг для сравнения «вкл/выкл» одной и той же сборкой. По умолчанию ВЫКЛЮЧЕН:
; включение меняет форму на всём пути Rubi и требует шагов 2–3 карточки RUBI.NF (инертные головы по IUF.m,
; утилиты под новой формой) — см. REPORT-RUBI-NF.md. Замер шага 1 при #t: +11 живых правил на сэмпле
; глав 1.1–8 (гл. 4.1 +65, 4.3 +11, 4.7 +28, 4.5 −15), но 29 тестов красные до шага 2.
(define *rubi-nf* #f)

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

(define (nf-scale r c)
  (cond ((equal? c 1) r)
        ((equal? r 1) c)
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

(define (nf-mb-add b e acc)
  (cond ((null? acc) (list (list b e)))
        ((equal? (car (car acc)) b) (cons (list b (+ (cadr (car acc)) e)) (cdr acc)))
        (else (cons (car acc) (nf-mb-add b e (cdr acc))))))

; u^a u^b -> u^(a+b): в Mathematica Times склеивает одинаковые основания (показатели — числа)
(define (nf-merge-bases fs)
  (map (lambda (g)
         (let ((b (car g)) (e (cadr g)))
           (cond ((equal? e 0) 1)
                 ((equal? e 1) b)
                 (else (list '^ b e)))))
       (foldl (lambda (acc f) (let ((sp (nf-mb-split f))) (nf-mb-add (car sp) (cdr sp) acc))) '() fs)))

(define (nf-times fs)
  (let* ((fs (nf-flatten-in '* fs '()))
         (coef (foldl * 1 (filter number? fs)))
         (rest (filter (lambda (f) (not (number? f))) fs))
         (merged (if (null? rest) '() (nf-merge-bases rest))))
    (cond ((equal? coef 0) 0)
          ((null? merged) coef)
          ((equal? coef 1) (if (null? (cdr merged)) (car merged) (cons '* merged)))
          (else (cons '* (cons coef merged))))))

; ---------- степени ----------
(define (nf-rep b n) (if (< n 1) '() (cons b (nf-rep b (- n 1)))))

(define (nf-num-pow b e)
  ; точные степени числа: 2^3 = 8, 2^-1 = 1/2; дробные — только точный корень (4^(1/2) = 2, 2^(1/2) — степень)
  (cond ((equal? e 0) 1)
        ((equal? e 1) b)
        ((and (integer? e) (> e 0)) (foldl * 1 (nf-rep b e)))
        ((and (integer? e) (< e 0)) (nf-num-pow (/ 1 b) (- 0 e)))
        ((equal? e 1/2)
         (let ((r (sqrt b))) (if (and (number? r) (equal? (* r r) b)) r (list '^ b e))))
        (else (list '^ b e))))

(define (nf-pow b e)
  (cond ((equal? e 0) 1)
        ((equal? e 1) b)
        ((and (number? b) (number? e)) (nf-num-pow b e))
        ; Sqrt[c·u] = Sqrt[c]·Sqrt[u] при точном целом корне c (автовычисление Mathematica: Sqrt[4 x] -> 2 Sqrt[x])
        ((and (equal? e 1/2) (pair? b) (equal? (car b) '*) (= (length b) 3) (number? (cadr b)))
         (let ((r (sqrt (cadr b))))
           (if (and (number? r) (equal? (* r r) (cadr b)))
               (nf-times (list r (nf-pow (caddr b) 1/2)))
               (list '^ b e))))
        ; (u^a)^n = u^(a n) при целом n (верно на любой ветви)
        ((and (pair? b) (equal? (car b) '^) (= (length b) 3) (number? (caddr b)) (integer? e))
         (let ((x (* (caddr b) e))) (if (equal? x 1) (cadr b) (list '^ (cadr b) x))))
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

