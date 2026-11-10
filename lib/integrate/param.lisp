; integrate/param.lisp — параметры в неопределённых интегралах: разбор случаев по знаку и нулю выражения от параметров.
; Загружается после check.lisp, до api.lisp. integrate (api.lisp) сначала зовёт int-param-integrate: если подынтегральное —
; одно из семейств (ниже) с символьным коэффициентом и знак/нуль решающего выражения не следует из деклараций, ответ —
; (piecewise ((условие ответ) ...)); если решают декларации — один ответ и record-condition; иначе #f (прежний каскад).
; Параметры без деклараций считаются вещественными. Семейства (ветвей ≤ 3):
;   c/(A x² + B x + C), A — рациональное ≠ 0: по знаку q = C/A − (B/A)²/4 (при B ≠ 0 — по дискриминанту);
;   x^a (a ≠ −1 / a = −1); exp(αx+β), sin(αx+β), cos(αx+β), 1/(αx+β), x·exp(αx+β) (α ≠ 0 / α = 0).
; Условия — (> E k) (< E k) (= E k) (!= E k) (>= E k) (<= E k) и (and ...). Сертификат int-piecewise-check:
; покрытие всех знаков решающих выражений + проверка каждой ветви дифференцированием в 1–3 допустимых рациональных
; точках параметров (ответ без %i — вещественный).
(module integrate
  (export int-piecewise-check))

; ---------- условия ----------

(define (int-pc-rel? h) (member? h '(> < = != >= <=)))

; условие → список атомов: #t — пусто, (and ...) — их список, иначе одно отношение
(define (int-pc-atoms c)
  (cond ((equal? c #t) '())
        ((and (op-expr? c) (equal? (car c) 'and)) (append-map int-pc-atoms (cdr c)))
        ((and (op-expr? c) (int-pc-rel? (car c)) (= (length c) 3)) (list c))
        (else (error "piecewise: неизвестное условие" c))))

(define (int-pc-cond-expr atoms)
  (cond ((null? atoms) #t) ((null? (cdr atoms)) (car atoms)) (else (cons 'and atoms))))

; выражение «левая часть − правая» атома — его знак решает атом
(define (int-pc-S a) (simplify (list '+ (cadr a) (list '* -1 (caddr a)))))

(define (int-pc-sign-ok? h s)
  (cond ((equal? h '>) (equal? s 'p)) ((equal? h '<) (equal? s 'n)) ((equal? h '=) (equal? s 'z))
        ((equal? h '!=) (not (equal? s 'z))) ((equal? h '>=) (not (equal? s 'n))) (else (not (equal? s 'p)))))

; E = c·R² (c рациональное) → (c R)
(define (int-pc-sqform E)
  (cond ((and (op-expr? E) (equal? (car E) '^) (= (length E) 3) (equal? (caddr E) 2) (not (number? (cadr E))))
         (list 1 (cadr E)))
        ((and (op-expr? E) (equal? (car E) '*) (= (length E) 3) (rational-number? (cadr E))
              (op-expr? (caddr E)) (equal? (car (caddr E)) '^) (equal? (caddr (caddr E)) 2))
         (list (cadr E) (cadr (caddr E))))
        (else #f)))

; (+ n rest...) с числом n → (rest −n): «a + 1 = 0» читается как «a = −1»
(define (int-pc-split-const E)
  (if (and (op-expr? E) (equal? (car E) '+) (= (length E) 3) (number? (cadr E)))
      (list (caddr E) (- 0 (cadr E)))
      (list E 0)))

; множество знаков as ⊆ (p n z) выражения E → список атомов (пусто — условие всегда истинно)
(define (int-pc-cond E as)
  (let ((hp (member? 'p as)) (hn (member? 'n as)) (hz (member? 'z as)) (sq (int-pc-sqform E)))
    (cond ((and hp hn hz) '())
          (sq (let* ((nzs (if (> (car sq) 0) 'p 'n)) (R (cadr sq)) (hnz (member? nzs as)))
                (cond ((and hnz hz) '())
                      (hnz (list (list '!= R 0)))
                      (hz (list (list '= R 0)))
                      (else (int-pc-cond-generic E as)))))
          (else (int-pc-cond-generic E as)))))

(define (int-pc-cond-generic E as)
  (if (and (op-expr? E) (equal? (car E) '*) (= (length E) 3) (rational-number? (cadr E)) (not (= (cadr E) 0))
           (not (number? (caddr E))))
      ; c·R: положительный множитель отбрасываем, отрицательный меняет знаки
      (int-pc-cond-generic (caddr E) (if (< (cadr E) 0) (int-pc-flip as) as))
      (let* ((hp (member? 'p as)) (hn (member? 'n as)) (ek (int-pc-split-const E)))
        (list (list (cond ((and hp hn) '!=) (hp (if (member? 'z as) '>= '>)) (hn (if (member? 'z as) '<= '<)) (else '=))
                    (car ek) (cadr ek))))))

; ---------- покрытие ----------

; branches — список списков атомов (конъюнкций): каждый вектор знаков решающих выражений (допустимых по sign-of с декларациями)
; удовлетворяет какой-нибудь ветви
(define (int-pc-covers? branches)
  (let* ((Ss (int-dedupe (map int-pc-S (append-map (lambda (b) b) branches))))
         (feas (map (lambda (s) (domain::sign-atoms s)) Ss)))
    (every? (lambda (vec)
              (any? (lambda (b)
                      (every? (lambda (a) (int-pc-sign-ok? (car a) (nth vec (int-pc-index (int-pc-S a) Ss)))) b))
                    branches))
            (int-cartesian feas))))

(define (int-pc-index s l)
  (let loop ((i 0) (r l)) (if (equal? (car r) s) i (loop (+ i 1) (cdr r)))))

; ---------- допустимые значения параметров ----------

(define int-pc-grid '(1 4 2 -1 -4 -2 3 -3 1/2 -1/2 5 -5 0 1/4 -1/4 7/3))
(define int-pc-fill '(2 3 5 7))

(define (int-pc-assignments ps)
  (if (null? ps)
      (list '())
      (let ((rest (int-pc-assignments (cdr ps))))
        (append-map (lambda (v) (map (lambda (r) (cons (list (car ps) v) r)) rest)) int-pc-grid))))

(define (int-pc-atom-true? a vals)
  (let ((v (try (simplify (subst vals (cadr a))) (lambda (er) #f))))
    (and v (real-numeric? v)
         (let ((k (caddr a)) (h (car a)))
           (cond ((equal? h '>) (> v k)) ((equal? h '<) (< v k)) ((equal? h '=) (= v k))
                 ((equal? h '!=) (not (= v k))) ((equal? h '>=) (>= v k)) (else (<= v k)))))))

(define (int-pc-take-ok l n)
  (let loop ((r l) (out '()) (k 0))
    (cond ((or (null? r) (>= k n)) (reverse out))
          (else (loop (cdr r) (if (car r) (cons (car r) out) out) (if (car r) (+ k 1) k))))))

; до 3 допустимых присваиваний параметров ps (первое, среднее, последнее из найденных)
(define (int-pc-samples atoms ps)
  (let* ((cps (filter (lambda (p) (any? (lambda (a) (contains-sym? (cadr a) p)) atoms)) ps))
         (others (filter (lambda (p) (not (member? p cps))) ps))
         (fillv (map2 list others int-pc-fill))
         (ok (let loop ((as (int-pc-assignments cps)) (out '()) (k 0))
               (cond ((or (null? as) (>= k 12)) (reverse out))
                     ((every? (lambda (a) (int-pc-atom-true? a (car as))) atoms) (loop (cdr as) (cons (car as) out) (+ k 1)))
                     (else (loop (cdr as) out k))))))
    (if (null? ok)
        '()
        (map (lambda (v) (append v fillv))
             (int-dedupe (list (car ok) (nth ok (quotient (length ok) 2)) (last ok)))))))

(define (int-pc-sample-ok? ans e x vals)
  (let ((Fs (try (simplify (subst vals ans)) (lambda (er) #f)))
        (es (try (simplify (subst vals e)) (lambda (er) #f))))
    (and Fs es (not (contains-sym? Fs '%i)) (not (contains-sym? Fs 'undefined))
         (try (int-check Fs es x) (lambda (er) #f)))))

; параметры выражения вещественны, если не объявлено иное (на время thunk)
(define (int-pc-with-reals ps thunk)
  (assuming-call (map (lambda (s) (list s reals)) (filter (lambda (s) (null? (declarations s))) ps)) thunk))

; bs — список (атомы ответ); результат: ok или (bad причина)
(define (int-pc-verify bs e x ps)
  (if (not (int-pc-covers? (map car bs)))
      (list 'bad "условия ветвей не покрывают все значения параметров")
      (let loop ((r bs))
        (if (null? r)
            'ok
            (let ((smp (int-pc-samples (car (car r)) ps)))
              (cond ((null? smp) (list 'bad (string-append "нет допустимых значений параметров для условия "
                                                           (to-string (int-pc-cond-expr (car (car r)))))))
                    ((every? (lambda (v) (int-pc-sample-ok? (cadr (car r)) e x v)) smp) (loop (cdr r)))
                    (else (list 'bad (string-append "ветвь неверна при условии "
                                                    (to-string (int-pc-cond-expr (car (car r)))))))))))))

; (int-piecewise-check pw e x) — pw = (piecewise ((условие ответ) ...)): ok или (bad причина)
(define (int-piecewise-check pw e x)
  (let* ((bs (map (lambda (b) (list (int-pc-atoms (car b)) (cadr b))) (cadr pw)))
         (ps (int-dedupe (append (int-symbols e x)
                                 (append-map (lambda (b)
                                               (append (int-symbols (cadr b) x)
                                                       (append-map (lambda (a) (int-symbols a x)) (car b))))
                                             bs)))))
    (int-pc-with-reals ps (lambda () (int-pc-verify bs e x ps)))))

; ---------- семейства ----------
; семейство → (E классы), класс — (знаки thunk-ответа); знаки E ⊆ (p n z)

(define (int-pc-root E)
  (let ((E (simplify E)))
    (cond ((and (rational-number? E) (> E 0)) (simplify (list '^ E 1/2)))
          ((and (op-expr? E) (equal? (car E) '^) (= (length E) 3) (integer? (caddr E)) (> (caddr E) 0) (= (mod (caddr E) 2) 0))
           (simplify (list '^ (cadr E) (/ (caddr E) 2))))
          ((and (op-expr? E) (equal? (car E) '*) (= (length E) 3) (rational-number? (cadr E)) (> (cadr E) 0))
           (simplify (list '* (int-pc-root (cadr E)) (int-pc-root (caddr E)))))
          (else (list '^ E 1/2)))))

(define (int-pc-flip as)
  (map (lambda (a) (cond ((equal? a 'p) 'n) ((equal? a 'n) 'p) (else a))) as))

(define (int-pc-fam-quad Q x)
  (let ((A (simplify (coeff Q x 2))) (B (simplify (coeff Q x 1))) (C (simplify (coeff Q x 0))))
    (and (rational-number? A) (not (= A 0))
         (let* ((b (simplify (list '* B (/ 1 A)))) (c (simplify (list '* C (/ 1 A))))
                (lin (equal? b 0))
                (q (simplify (expand (list '+ c (list '* -1/4 (list '^ b 2))))))
                (D (if lin q (simplify (expand (list '* -4 q)))))
                (w (if lin x (simplify (list '+ x (list '* 1/2 b)))))
                (k (/ 1 A)))
           (list D
                 (list (list (if lin '(p) '(n))
                             (lambda () (let ((s (int-pc-root q)))
                                          (list '* k (list '^ s -1) (list 'atan (list '* w (list '^ s -1)))))))
                       (list (if lin '(n) '(p))
                             (lambda () (let ((s (int-pc-root (list '* -1 q))))
                                          (list '* k 1/2 (list '^ s -1)
                                                (list 'log (list '* (list '+ w (list '* -1 s)) (list '^ (list '+ w s) -1)))))))
                       (list '(z) (lambda () (list '* (- 0 k) (list '^ w -1))))))))))

(define (int-pc-head? t h n) (and (op-expr? t) (equal? (car t) h) (= (length t) n)))

; α·x + β: α нечисловой
(define (int-pc-lin U x)
  (let ((a (int-slope U x)))
    (and a (not (number? a)) (x-free? a x)
         (list a (simplify (list '+ U (list '* -1 a x)))))))

(define (int-pc-fam-lin E x U mk-nz mk-z)
  (let ((ab (int-pc-lin U x)))
    (and ab (list (car ab)
                  (list (list '(p n) (lambda () (mk-nz (car ab) (cadr ab))))
                        (list '(z) (lambda () (mk-z (car ab) (cadr ab)))))))))

(define (int-pc-family core x)
  (cond
    ((= (length core) 1)
     (let ((t (car core)))
       (cond
         ((and (int-pc-head? t '^ 3) (equal? (caddr t) -1) (polynomial? (cadr t) x) (equal? (degree (cadr t) x) 2))
          (int-pc-fam-quad (cadr t) x))
         ((and (int-pc-head? t '^ 3) (equal? (caddr t) -1) (polynomial? (cadr t) x) (equal? (degree (cadr t) x) 1))
          (let ((L (cadr t)))
            (int-pc-fam-lin #f x L
                            (lambda (a b) (list '* (list '^ a -1) (list 'log L)))
                            (lambda (a b) (list '* x (list '^ b -1))))))
         ((and (int-pc-head? t '^ 3) (equal? (cadr t) x) (x-free? (caddr t) x) (not (number? (caddr t))))
          (let ((E (simplify (list '+ (caddr t) 1))))
            (list E (list (list '(p n) (lambda () (list '* (list '^ E -1) (list '^ x E))))
                          (list '(z) (lambda () (list 'log x)))))))
         ((int-pc-head? t 'exp 2)
          (int-pc-fam-lin #f x (cadr t)
                          (lambda (a b) (list '* (list '^ a -1) t))
                          (lambda (a b) (list '* x (list 'exp b)))))
         ((int-pc-head? t 'sin 2)
          (int-pc-fam-lin #f x (cadr t)
                          (lambda (a b) (list '* -1 (list '^ a -1) (list 'cos (cadr t))))
                          (lambda (a b) (list '* x (list 'sin b)))))
         ((int-pc-head? t 'cos 2)
          (int-pc-fam-lin #f x (cadr t)
                          (lambda (a b) (list '* (list '^ a -1) (list 'sin (cadr t))))
                          (lambda (a b) (list '* x (list 'cos b)))))
         (else #f))))
    ((= (length core) 2)
     (let ((ex (filter (lambda (t) (int-pc-head? t 'exp 2)) core)) (xs (filter (lambda (t) (equal? t x)) core)))
       (and (= (length ex) 1) (= (length xs) 1)
            (let ((U (cadr (car ex))))
              (int-pc-fam-lin #f x U
                              (lambda (a b) (list '* (list '^ a -2) (car ex) (list '+ (list '* a x) -1)))
                              (lambda (a b) (list '* 1/2 (list 'exp b) (list '^ x 2))))))))
    (else #f)))

; ---------- сборка ответа ----------

; n — подынтегральное после приведения: (c0 факторы без x) и список факторов с x
(define (int-pc-split n x)
  (let* ((fs (if (and (op-expr? n) (equal? (car n) '*)) (cdr n) (list n)))
         (free (filter (lambda (t) (x-free? t x)) fs)))
    (list (if (null? free) 1 (simplify (cons '* free)))
          (filter (lambda (t) (not (x-free? t x))) fs))))

; E, классы → ответ: один (декларации решили) либо (piecewise ...); #f, если сертификат не прошёл
(define (int-pc-assemble E classes c1 f x ps decl)
  (let* ((feas (domain::sign-atoms E))
         (brs (filter (lambda (b) b)
                      (map (lambda (cl)
                             (let ((as (filter (lambda (a) (member? a feas)) (car cl))))
                               (if (null? as) #f (list as (cadr cl)))))
                           classes)))
         (n (length brs)))
    (and (>= n 1) (<= n 4)
         (let* ((bs (map (lambda (b)
                           (list (int-pc-cond E (car b))
                                 (simplify (list '* c1 ((cadr b))))))
                         brs))
                (ver (int-pc-verify bs f x ps)))
           (and (equal? ver 'ok)
                (begin
                  (map (lambda (b)
                         (alg-step 'pc-branch "Случай по знаку или нулю параметра"
                                   "первообразная при выполнении условия"
                                   (int-pc-cond-expr (car b)) (cadr b)))
                       bs)
                  (alg-step 'pc-certificate "Сертификат ветвей"
                            "условия ветвей покрывают все значения параметров; каждая ветвь проверена дифференцированием в 1–3 допустимых рациональных точках"
                            '() 'ok)
                  #t)
                (if (= n 1)
                    (begin
                      (if (and (pair? (car (car bs))) (any? (lambda (s) (member? s decl)) (int-symbols E x)))
                          (record-condition (car (car (car bs)))
                                            "integrate: ответ по объявленному знаку параметра"))
                      (cadr (car bs)))
                    (list 'piecewise
                          (map (lambda (b) (list (int-pc-cond-expr (car b)) (cadr b))) bs))))))))

; (int-param-integrate f x) → ответ или #f (не наше семейство / решают декларации без параметров / сертификат не прошёл)
(define (int-param-integrate f x)
  (let ((ps (int-symbols f x)))
    (and (pair? ps) (<= (length ps) 3)
         (int-guard
          (lambda ()
            ; Шаги: рамка pc-integration (ключевые шаги — решающее выражение, ветви, сертификат; расчёт тихий)
            (with-step ('pc-integration "Интеграл с параметрами: разбор случаев" (int-form f x)
                        :comment "вид первообразной зависит от знака или нуля выражения от параметров: ответ — piecewise по ветвям"
                        :after int-p)
              (alg-run
               (lambda ()
                 (let ((decl (filter (lambda (s) (pair? (declarations s))) ps)))
                   (int-pc-with-reals
                    ps
                    (lambda ()
                      (let* ((n (int-norm f)) (sp (int-pc-split n x)) (fam (int-pc-family (cadr sp) x)))
                        (if fam
                            (alg-step 'pc-family "Решающее выражение"
                                      (string-append "знак или нуль выражения E = " (alg-mp (car fam))
                                                     " определяет вид первообразной; без деклараций параметры вещественны")
                                      (int-form f x) (car fam)))
                        (and fam (int-pc-assemble (car fam) (cadr fam) (car sp) f x ps decl))))))))))))))
