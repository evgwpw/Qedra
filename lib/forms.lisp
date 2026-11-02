; forms.lisp — Шаг DF.1: внешнее исчисление (дифференциальные формы) в ℝⁿ и векторный анализ через формы.
;
; k-форма в переменных (x1 … xn) — вектор #(form vars k terms); terms — список (коэффициент индексы), индексы —
; возрастающий список номеров переменных (с 0), нулевые коэффициенты отброшены, коэффициенты упрощены (simplify),
; термы отсортированы лексикографически. Нулевая форма — terms = (). Формы однородны по степени.
; Выражения: dx, dy … — символы "d" + имя переменной; (form '(+ (* P dx) (* Q dy)) '(x y)); печать — form->expr,
; произведение — (wedge dx dy). Скаляр в wedge/form-add — 0-форма.
;
; Операции: wedge, form-d (внешний дифференциал), form-pullback (прообраз по отображению x = φ(u)), form-interior (ι_v),
; form-hodge (Ходж в евклидовом ℝⁿ, стандартная ориентация), form-closed?, form-exact?, form-potential.
;
; form-potential — оператор гомотопии Пуанкаре от базовой точки p (по умолчанию 0): K ω = ∫₀¹ tᵏ⁻¹ ι_{x−p} ω(p + t(x−p)) dt;
; верен на области, звёздной относительно p. Ответ принимается только после сертификата d(F) = ω. Не замкнутая форма → #f;
; особенность в базовой точке (знаменатель коэффициента обращается в 0) → #f с record-condition (область не звёздная относительно
; p: глобального потенциала нет, например dθ на ℝ²∖{0}); явная базовая точка p ≠ особой даёт ЛОКАЛЬНЫЙ потенциал
; (условие `(star-shaped-domain p)` записывается в канал условий).
;
; Векторный анализ (ℝ², ℝ³ и ℝⁿ там, где определено): vf-grad, vf-div, vf-curl (ℝ³ — список, ℝ² — скаляр), vf-laplacian — через формы
; (♭ и ∗); vf-potential (градиентное поле), vf-vector-potential (div F = 0 в ℝ³, гомотопия 2-формы ι_F vol) — с проверками.

(module forms
  (export make-form form form? form-vars form-degree form-terms form->expr form-zero? form-equal?
          form-add form-sub form-neg form-scale wedge form-d form-pullback form-interior form-hodge
          form-closed? form-exact? form-potential form-potential-check
          vf-grad vf-div vf-curl vf-laplacian vf-potential vf-potential-check vf-vector-potential vf-vector-potential-check
          make-chain chain? chain-phi chain-ranges integrate-form integrate-form-numeric chain-rect-boundary stokes-check
          vf-form1 vf-form2))

; ---------- вспомогательное ----------

(define (frm-zero-expr? e)
  (let ((s (simplify e)))
    (if (number? s)
        (= s 0)
        (or (let ((s1 (simplify (expand s)))) (and (number? s1) (= s1 0)))
            (let ((s2 (simplify (together s)))) (and (number? s2) (= s2 0)))))))

; канонический коэффициент: simplify; для не-атомов — наименьший по размеру из simplify, simplify∘together, simplify∘factor
(define (frm-simp c)
  (let ((s (simplify c)))
    (if (not (pair? s))
        s
        (let ((cands (list s
                           (try (simplify (together s)) (lambda (e) s))
                           (try (simplify (factor s)) (lambda (e) s)))))
          (foldl (lambda (best x) (if (< (trigsimp-size x) (trigsimp-size best)) x best)) s (cdr cands))))))

(define (frm-mk vars k terms) (vector 'form vars k terms))

(define (form? x) (and (vector? x) (= (vlength x) 4) (equal? (vref x 0) 'form)))
(define (form-vars f) (vref f 1))
(define (form-degree f) (vref f 2))
(define (form-terms f) (vref f 3))
(define (form-zero? f) (null? (vref f 3)))

(define (frm-inversions l)
  (if (null? l)
      0
      (+ (length (filter (lambda (y) (< y (car l))) (cdr l))) (frm-inversions (cdr l)))))
(define (frm-has-dup? l)
  (cond ((null? l) #f) ((member? (car l) (cdr l)) #t) (else (frm-has-dup? (cdr l)))))
(define (frm-sign-of l) (if (= (modulo (frm-inversions l) 2) 0) 1 -1))

(define (frm-idx<? a b)
  (cond ((null? a) (not (null? b)))
        ((null? b) #f)
        ((< (car a) (car b)) #t)
        ((> (car a) (car b)) #f)
        (else (frm-idx<? (cdr a) (cdr b)))))

; raw — список (коэффициент индексы) с возрастающими индексами, возможны повторы индексов и нули
(define (frm-normalize vars k raw)
  (let ((h (make-hash)))
    (for-each (lambda (t) (hash-set! h (cadr t) (+ (hash-ref h (cadr t) 0) (car t)))) raw)
    (let ((terms (filter (lambda (t) (not (frm-zero-expr? (car t))))
                         (map (lambda (i) (list (frm-simp (hash-ref h i 0)) i)) (hash-keys h)))))
      (frm-mk vars k (sort terms (lambda (a b) (frm-idx<? (cadr a) (cadr b))))))))

(define (frm-var-index vars v)
  (let loop ((l vars) (i 0))
    (cond ((null? l) (error "form: неизвестная переменная" v))
          ((equal? (car l) v) i)
          (else (loop (cdr l) (+ i 1))))))

(define (frm-lift x vars)
  (if (form? x)
      x
      (frm-mk vars 0 (if (frm-zero-expr? x) '() (list (list (frm-simp x) '()))))))

(define (frm-check-same a b)
  (if (not (equal? (vref a 1) (vref b 1))) (error "form: разные переменные" (vref a 1) (vref b 1)) #t))

; ---------- конструкторы ----------

; (make-form vars k terms): terms — ((coef (i j …)) …), индексы — номера с 0 или имена переменных, любой порядок
(define (make-form vars k terms)
  (frm-normalize
    vars k
    (append-map
      (lambda (t)
        (let ((idx (map (lambda (i) (if (integer? i) i (frm-var-index vars i))) (cadr t))))
          (if (not (= (length idx) k)) (error "make-form: число индексов не равно k" t) #t)
          (if (frm-has-dup? idx)
              '()
              (list (list (* (frm-sign-of idx) (car t)) (sort idx <))))))
      terms)))

(define (frm-dname v) (string->symbol (string-append "d" (symbol->string v))))

(define (frm-has-d? e dnames)
  (any? (lambda (d) (contains-sym? e d)) dnames))

(define (form e vars)
  (let ((dnames (map frm-dname vars)))
    (let parse ((e e))
      (cond ((form? e) e)
            ((and (symbol? e) (member? e dnames))
             (frm-mk vars 1 (list (list 1 (list (frm-var-index dnames e))))))
            ((not (frm-has-d? e dnames)) (frm-lift e vars))
            ((and (pair? e) (equal? (car e) '+))
             (foldl (lambda (acc x) (form-add acc (parse x))) (frm-lift 0 vars) (cdr e)))
            ((and (pair? e) (or (equal? (car e) '*) (equal? (car e) 'wedge)))
             (foldl (lambda (acc x) (frm-wedge2 acc (parse x))) (frm-lift 1 vars) (cdr e)))
            ((and (pair? e) (equal? (car e) '-))
             (if (null? (cddr e))
                 (form-neg (parse (cadr e)))
                 (foldl (lambda (acc x) (form-sub acc (parse x))) (parse (cadr e)) (cddr e))))
            ((and (pair? e) (equal? (car e) '/) (= (length e) 3) (not (frm-has-d? (caddr e) dnames)))
             (form-scale (list '/ 1 (caddr e)) (parse (cadr e))))
            (else (error "form: не разобрано выражение" e))))))

(define (frm-term->expr t vars)
  (let ((c (car t)) (idx (cadr t)))
    (if (null? idx)
        c
        (let ((w (if (null? (cdr idx))
                     (frm-dname (nth vars (car idx)))
                     (cons 'wedge (map (lambda (i) (frm-dname (nth vars i))) idx)))))
          (cond ((equal? c 1) w)
                ((and (pair? c) (equal? (car c) '*)) (append c (list w)))
                (else (list '* c w)))))))

(define (form->expr f)
  (let ((ts (map (lambda (t) (frm-term->expr t (vref f 1))) (vref f 3))))
    (cond ((null? ts) 0)
          ((null? (cdr ts)) (car ts))
          (else (cons '+ ts)))))

; ---------- линейные операции ----------

(define (form-add a b)
  (let ((a (frm-lift a (if (form? b) (vref b 1) '()))) (b (frm-lift b (if (form? a) (vref a 1) '()))))
    (frm-check-same a b)
    (cond ((form-zero? a) b)
          ((form-zero? b) a)
          ((not (= (vref a 2) (vref b 2))) (error "form-add: разные степени" (vref a 2) (vref b 2)))
          (else (frm-normalize (vref a 1) (vref a 2) (append (vref a 3) (vref b 3)))))))

(define (form-scale c f)
  (frm-normalize (vref f 1) (vref f 2) (map (lambda (t) (list (* c (car t)) (cadr t))) (vref f 3))))
(define (form-neg f) (form-scale -1 f))
(define (form-sub a b) (form-add a (form-neg b)))

(define (form-equal? a b)
  (and (equal? (vref a 1) (vref b 1))
       (or (= (vref a 2) (vref b 2)) (and (form-zero? a) (form-zero? b)))
       (form-zero? (form-sub a b))))

; ---------- внешнее произведение ----------

(define (frm-wedge2 a b)
  (let ((a (frm-lift a (if (form? b) (vref b 1) '()))) (b (frm-lift b (if (form? a) (vref a 1) '()))))
    (frm-check-same a b)
    (frm-normalize
      (vref a 1) (+ (vref a 2) (vref b 2))
      (append-map
        (lambda (ta)
          (append-map
            (lambda (tb)
              (let ((idx (append (cadr ta) (cadr tb))))
                (if (frm-has-dup? idx)
                    '()
                    (list (list (* (frm-sign-of idx) (car ta) (car tb)) (sort idx <))))))
            (vref b 3)))
        (vref a 3)))))

(define (wedge a &rest more)
  (foldl (lambda (acc x) (frm-wedge2 acc x)) a more))

; ---------- внешний дифференциал ----------

(define (form-d f)
  (let ((vars (vref f 1)) (k (vref f 2)))
    (frm-normalize
      vars (+ k 1)
      (append-map
        (lambda (t)
          (let ((c (car t)) (idx (cadr t)))
            (append-map
              (lambda (m)
                (if (member? m idx)
                    '()
                    (let ((dc (diff (nth vars m) c))
                          (s (if (= (modulo (length (filter (lambda (i) (< i m)) idx)) 2) 0) 1 -1)))
                      (if (frm-zero-expr? dc)
                          '()
                          (list (list (* s dc) (sort (cons m idx) <)))))))
              (range (length vars)))))
        (vref f 3)))))

(define (form-closed? f) (form-zero? (form-d f)))

; ---------- прообраз ----------

; (form-pullback ω phi uvars): phi — список из n выражений от uvars (xᵢ = φᵢ(u)); результат — форма в uvars
(define (form-pullback f phi uvars)
  (let* ((vars (vref f 1))
         (rules (map2 (lambda (x p) (list x p)) vars phi))
         (dphi (map (lambda (p)
                      (frm-normalize uvars 1
                        (map2 (lambda (u j) (list (diff u p) (list j))) uvars (range (length uvars)))))
                    phi)))
    (if (not (= (length phi) (length vars))) (error "form-pullback: длина phi не равна числу переменных") #t)
    (foldl
      (lambda (acc t)
        (form-add acc
                  (foldl (lambda (w i) (frm-wedge2 w (nth dphi i)))
                         (frm-lift (subst rules (car t)) uvars)
                         (cadr t))))
      (frm-mk uvars (vref f 2) '())
      (vref f 3))))

; ---------- внутреннее произведение и Ходж ----------

(define (form-interior v f)
  (let ((vars (vref f 1)) (k (vref f 2)))
    (if (= k 0) (error "form-interior: у 0-формы нет внутреннего произведения") #t)
    (frm-normalize
      vars (- k 1)
      (append-map
        (lambda (t)
          (let ((c (car t)) (idx (cadr t)))
            (map (lambda (j)
                   (list (* (if (= (modulo j 2) 0) 1 -1) (nth v (nth idx j)) c)
                         (append (take idx j) (drop idx (+ j 1)))))
                 (range k))))
        (vref f 3)))))

(define (form-hodge f)
  (let* ((vars (vref f 1)) (n (length vars)))
    (frm-normalize
      vars (- n (vref f 2))
      (map (lambda (t)
             (let ((comp (filter (lambda (i) (not (member? i (cadr t)))) (range n))))
               (list (* (frm-sign-of (append (cadr t) comp)) (car t)) comp)))
           (vref f 3)))))

; ---------- потенциал (гомотопия Пуанкаре) ----------

(define frm-tvar 'frm_t)

(define (frm-subst-base-zero? c vars p)
  (let ((den (denom (together c))))
    (frm-zero-expr? (subst (map2 (lambda (x a) (list x a)) vars p) den))))

(define (form-potential-check omega pot)
  ; потенциал 1-формы можно передать выражением (0-форма) — замечание ревью: раньше выражение молча давало #f
  (let ((P (if (and (not (form? pot)) (= (vref omega 2) 1)) (form pot (vref omega 1)) pot)))
    (and (form? P) (form-equal? (form-d P) omega))))

; (form-potential ω [p]) → (k−1)-форма F с dF = ω либо #f
(define (form-potential omega &rest opt)
  (let* ((vars (vref omega 1)) (k (vref omega 2)) (n (length vars))
         (p (if (null? opt) (map (lambda (x) 0) vars) (car opt))))
    (cond
      ((= k 0) #f)
      ((form-zero? omega) (frm-mk vars (- k 1) '()))
      ((not (form-closed? omega))
       (record-condition (list 'form-not-closed (form->expr omega)) "form-potential: форма не замкнута, потенциала нет")
       #f)
      ((any? (lambda (t) (frm-subst-base-zero? (car t) vars p)) (vref omega 3))
       (record-condition (list 'form-singular-at-base p)
                         "form-potential: особенность в базовой точке — область не звёздная; глобального потенциала нет (укажите другую базовую точку для локального)")
       #f)
      (else
       (let* ((tv frm-tvar)
              (rules (map2 (lambda (x a) (list x (list '+ a (list '* tv (list '- x a))))) vars p))
              (v (map2 (lambda (x a) (simplify (list '+ x (list '* -1 a)))) vars p))
              (raw
               (append-map
                 (lambda (t)
                   (let ((ct (simplify (subst rules (car t)))) (idx (cadr t)))
                     (map (lambda (j)
                            (list (integrate (simplify (list '* (if (= (modulo j 2) 0) 1 -1) (nth v (nth idx j)) ct
                                                             (list '^ tv (- k 1))))
                                             tv 0 1)
                                  (append (take idx j) (drop idx (+ j 1)))))
                          (range k))))
                 (vref omega 3))))
         (if (any? (lambda (r) (contains-sym? (car r) 'integrate)) raw)
             (begin
               (record-condition '(form-potential-integral-failed) "form-potential: интеграл гомотопии не вычислен")
               #f)
             (let ((pot (frm-normalize vars (- k 1) raw)))
               (if (form-potential-check omega pot)
                   (begin
                     (record-condition (list 'star-shaped-domain p)
                                       "form-potential: гомотопия Пуанкаре от базовой точки — потенциал верен на области, звёздной относительно неё и без особенностей")
                     pot)
                   (begin
                     (record-condition '(form-potential-certificate-failed)
                                       "form-potential: сертификат dF = ω не подтверждён символьно — потенциал не возвращается")
                     #f)))))))))

(define (form-exact? omega)
  (if (= (vref omega 2) 0)
      (form-zero? omega)
      (if (form-potential omega) #t #f)))

; ---------- векторный анализ ----------

(define (vf-vol vars) (frm-mk vars (length vars) (list (list 1 (range (length vars))))))

(define (vf->form1 F vars) (make-form vars 1 (map2 (lambda (c i) (list c (list i))) F (range (length vars)))))

; коэффициенты 1-формы как список из n компонент
(define (frm-components1 f)
  (map (lambda (i)
         (let ((t (assoc (list i) (map (lambda (t) (cons (cadr t) (car t))) (vref f 3)))))
           (if t (cdr t) 0)))
       (range (length (vref f 1)))))

(define (frm-scalar f)
  (if (null? (vref f 3)) 0 (car (car (vref f 3)))))

(define (vf-grad f vars) (frm-components1 (form-d (frm-lift f vars))))

(define (vf-div F vars)
  (frm-scalar (form-hodge (form-d (form-hodge (vf->form1 F vars))))))

(define (vf-curl F vars)
  (let ((r (form-hodge (form-d (vf->form1 F vars)))))
    (case (length vars)
      ((2) (frm-scalar r))
      ((3) (frm-components1 r))
      (else (error "vf-curl: только ℝ² и ℝ³")))))

(define (vf-laplacian f vars)
  (frm-scalar (form-hodge (form-d (form-hodge (form-d (frm-lift f vars)))))))

(define (frm-list-equal? a b)
  (every? (lambda (p) (frm-zero-expr? (list '+ (car p) (list '* -1 (cadr p))))) (map2 list a b)))

(define (vf-potential-check F vars pot) (frm-list-equal? (vf-grad pot vars) F))

(define (vf-potential F vars &rest opt)
  (let ((r (apply form-potential (cons (vf->form1 F vars) opt))))
    (if (and r (vf-potential-check F vars (frm-scalar r))) (frm-scalar r) #f)))

(define (vf-vector-potential-check F vars A) (frm-list-equal? (vf-curl A vars) F))

(define (vf-vector-potential F vars &rest opt)
  (if (not (= (length vars) 3))
      (error "vf-vector-potential: только ℝ³")
      (let* ((omega (form-interior F (vf-vol vars)))
             (r (apply form-potential (cons omega opt))))
        (if r
            (let ((A (frm-components1 r)))
              (if (vf-vector-potential-check F vars A) A #f))
            #f))))

; ---------- шаг DF.2: интегрирование форм по параметризованным цепям ----------
;
; Цепь — вектор #(chain phi ranges): phi — n выражений от параметров, ranges — ((u a b) …) (k параметров = степень формы).
; Сумма цепей с коэффициентами — список ((коэффициент цепь) …). ∫_c ω = ∫ по параметрам от коэффициента при du₁∧…∧du_k
; формы φ*ω (ориентация — порядок параметров). Точное значение (integrate с пределами); если интеграл не берётся —
; численный Симпсон (eval-num), ответ — float и условие `(integrate-form-numeric)`.

(define (make-chain phi ranges) (vector 'chain phi ranges))
(define (chain? c) (and (vector? c) (= (vlength c) 3) (equal? (vref c 0) 'chain)))
(define (chain-phi c) (vref c 1))
(define (chain-ranges c) (vref c 2))

(define (frm-top-coef f)
  (let ((t (assoc (range (length (vref f 1))) (map (lambda (t) (cons (cadr t) (car t))) (vref f 3)))))
    (if t (cdr t) 0)))

; pullback формы на цепь → коэффициент при du₁∧…∧du_k
(define (frm-chain-integrand omega c)
  (let ((us (map car (chain-ranges c))))
    (if (not (= (vref omega 2) (length us)))
        (error "integrate-form: степень формы не равна размерности цепи" (vref omega 2) (length us))
        (frm-top-coef (form-pullback omega (chain-phi c) us)))))

(define (frm-integrate-ranges e ranges)
  (foldl (lambda (acc r) (integrate acc (car r) (cadr r) (caddr r))) e (reverse ranges)))

; Симпсон, n — чётное число интервалов на параметр
(define (frm-simpson-ranges e ranges rules n)
  (if (null? ranges)
      (eval-num (subst rules e))
      (let* ((r (car ranges)) (a (eval-num (cadr r))) (b (eval-num (caddr r))) (h (/ (- b a) n)))
        (* (/ h 3)
           (foldl (lambda (acc i)
                    (let ((w (cond ((or (= i 0) (= i n)) 1) ((= (modulo i 2) 1) 4) (else 2))))
                      (+ acc (* w (frm-simpson-ranges e (cdr ranges) (cons (list (car r) (+ a (* i h))) rules) n)))))
                  0 (range (+ n 1)))))))

(define (integrate-form-numeric omega c &rest opt)
  (let ((n (if (null? opt) (if (= (length (chain-ranges c)) 1) 400 40) (car opt))))
    (frm-simpson-ranges (frm-chain-integrand omega c) (chain-ranges c) '() n)))

(define (frm-integrate-chain omega c)
  (let* ((e (frm-chain-integrand omega c))
         (v (try (frm-integrate-ranges e (chain-ranges c)) (lambda (err) #f))))
    (if (and v (not (contains-sym? v 'integrate)))
        (simplify v)
        (begin
          (record-condition '(integrate-form-numeric) "integrate-form: символьный интеграл не взят — численный Симпсон")
          (integrate-form-numeric omega c)))))

; (integrate-form ω цепь) или (integrate-form ω ((коэф цепь) …))
(define (integrate-form omega chain)
  (if (chain? chain)
      (frm-integrate-chain omega chain)
      (simplify (foldl (lambda (acc t) (+ acc (* (car t) (frm-integrate-chain omega (cadr t))))) 0 chain))))

; граница прямоугольника параметров (u a b) × (v c d) для цепи phi(u,v): четыре ребра против часовой стрелки
(define (chain-rect-boundary phi ru rv)
  (let* ((u (car ru)) (a (cadr ru)) (b (caddr ru))
         (v (car rv)) (c (cadr rv)) (d (caddr rv))
         (at (lambda (var val) (map (lambda (e) (simplify (subst (list (list var val)) e))) phi))))
    (list (list 1 (make-chain (at v c) (list ru)))
          (list 1 (make-chain (at u b) (list rv)))
          (list -1 (make-chain (at v d) (list ru)))
          (list -1 (make-chain (at u a) (list rv))))))

; (stokes-check ω phi ru rv) → (∮_{∂M} ω, ∫_M dω, статус): exact / numeric (|разность| < 1e-6) / mismatch
(define (stokes-check omega phi ru rv)
  (let* ((lhs (integrate-form omega (chain-rect-boundary phi ru rv)))
         (rhs (integrate-form (form-d omega) (make-chain phi (list ru rv))))
         (diff-e (simplify (list '+ lhs (list '* -1 rhs)))))
    (list lhs rhs
          (cond ((frm-zero-expr? diff-e) 'exact)
                ((< (abs (eval-num diff-e)) 1e-6) 'numeric)
                (else 'mismatch)))))

; формы поля: работа (1-форма F♭) и поток (2-форма ι_F vol в ℝ³)
(define (vf-form1 F vars) (vf->form1 F vars))
(define (vf-form2 F vars) (form-interior F (vf-vol vars)))
