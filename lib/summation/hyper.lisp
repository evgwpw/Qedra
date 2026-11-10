; summation/hyper.lisp — Шаг 21l.2: классификатор гипергеометрических термов и целые корни результанта.
; (hyper-ratio t k) → (p . q) — числитель/знаменатель отношения t(k+1)/t(k), многочлены по k над ℚ(парам.),
;   либо #f — терм не гипергеометрический по k (kᵏ, H_k, sin k, Γ(k/2), сумма разных классов и т. п.).
;   Единственное место, где «видны» Γ/!/C/rf/ff (принцип «двух стадий»: дальше — только алгебра многочленов).
; (poly-shift p k h) — сдвиг p(k+h); (poly-int-roots q k) — целые корни ≥ 0 результанта q(k), q(k+h) (дисперсия).
; Источник рецепта: Koepf, Hypergeometric Summation (hypersimp; нормальная форма Γ, x^α, (−1)^k).

(module summation
  (export sum-symbolic sum-strategies sum-add-strategy sum-guard sum-check sum-check-how
          sum-unevaluated sum-faulhaber sum-form
          hyper-ratio hyper-termp poly-shift poly-int-roots poly-int-roots-param poly-dispersion
          hyper-lin hyper-frac-mul hyper-poly-mul))

; ---------- вспомогательное ----------

; ошибка = отказ (не гипергеометрический): дискриминируем через исключение с маркером
(define (hyper-fail msg) (raise (list 'hyper-not-hypergeometric msg)))
(define (hyper-catch thunk)
  (try (thunk) (lambda (err)
                 (let ((data (error-data err)))
                   (if (and (pair? data) (equal? (car data) 'hyper-not-hypergeometric))
                       #f
                       (raise err))))))

; линейная форма a·e+b по k: → (a . b) или #f (a, b — не зависят от k; a ≠ 0 проверяет вызывающий)
; поддерживает n-арные + и -, унарный минус, умножение на k-свободный множитель
; (вход упрощается: (- (+ m j) j) синтаксически содержит j, хотя равен m)
(define (hyper-lin e k) (hyper-lin-raw (simplify e) k))
(define (hyper-lin-raw e k)
  (cond ((equal? e k) (cons 1 0))
        ((sum-k-free? e k) (cons 0 e))     ; константа/параметр (не обязательно число)
        ((and (op-expr? e) (equal? (car e) '+)) (hyper-lin-add (cdr e) k))
        ((and (op-expr? e) (equal? (car e) '-))
         (if (= (length e) 2)
             (let ((l (hyper-lin (cadr e) k)))
               (and l (cons (- (car l)) (sum-hyper-sub 0 (cdr l)))))
             (let ((l1 (hyper-lin (cadr e) k)) (lr (hyper-lin-add (cddr e) k)))
               (and l1 lr (cons (- (car l1) (car lr))
                                (sum-hyper-sub (cdr l1) (cdr lr)))))))
        ((and (op-expr? e) (equal? (car e) '*) (>= (length e) 3)
              (sum-k-free? (cadr e) k))
         (let ((l2 (hyper-lin (cons '* (cddr e)) k)))
           (and l2 (cons (* (cadr e) (car l2)) (* (cadr e) (cdr l2))))))
        ((and (op-expr? e) (equal? (car e) '*) (= (length e) 3)
              (sum-k-free? (caddr e) k))
         (let ((l1 (hyper-lin (cadr e) k)))
           (and l1 (cons (* (caddr e) (car l1)) (* (caddr e) (cdr l1))))))
        (else #f)))

; сумма линейных форм списка аргументов
(define (hyper-lin-add args k)
  (if (null? args)
      (cons 0 0)
      (let ((l1 (hyper-lin (car args) k)) (lr (hyper-lin-add (cdr args) k)))
        (and l1 lr (cons (+ (car l1) (car lr)) (sum-hyper-add (cdr l1) (cdr lr)))))))

; сложение/вычитание «свободных» частей (могут быть выражениями с параметрами)
(define (sum-hyper-add a b) (simplify (list '+ a b)))
(define (sum-hyper-sub a b) (simplify (list '- a b)))

; ---- p/q-действия: рациональная функция как пара многочленов (упрощённых выражений по k) ----

(define (hyper-poly-mul p q) (expand (simplify (list '* p q))))
(define (hyper-make-frac p q) (cons p q))
(define (hyper-frac-mul f g) (cons (hyper-poly-mul (car f) (car g))
                                   (hyper-poly-mul (cdr f) (cdr g))))
(define (hyper-frac-recip f) (cons (cdr f) (car f)))

; произведение отношений списка аргументов
(define (hyper-frac-prod-list args k)
  (if (null? args)
      (hyper-make-frac 1 1)
      (hyper-frac-mul (hyper-ratio-core (car args) k)
                      (hyper-frac-prod-list (cdr args) k))))

; f^e (e — целое со знаком): повторное умножение/обращение
(define (hyper-frac-pow f e)
  (if (= e 0)
      (hyper-make-frac 1 1)
      (if (> e 0)
          (hyper-frac-mul f (hyper-frac-pow f (- e 1)))
          (hyper-frac-recip (hyper-frac-pow f (- e))))))


; ---- Γ-факторы ----

; Γ(a·k+b): a — целое ≠ 0, b свободно от k. Отношение Γ(a(k+1)+b)/Γ(ak+b):
;   a > 0: ∏_{j=0}^{a-1} (ak+b+j);  a < 0: 1/∏_{j=1}^{-a} (ak+b-j).
(define (hyper-gamma-prod b a k j)          ; ∏_{i=0}^{j-1} (ak+b+i)
  (if (<= j 0) 1
      (hyper-poly-mul (hyper-gamma-prod b a k (- j 1))
                      (list '+ b (list '* a k) (- j 1)))))
(define (hyper-gamma-prod-neg b a k j)      ; ∏_{i=1}^{j} (ak+b-i)
  (if (= j 0) 1
      (hyper-poly-mul (hyper-gamma-prod-neg b a k (- j 1))
                      (list '+ b (list '* a k) (list '- j)))))
(define (hyper-gamma-ratio arg k)
  (let ((l (hyper-lin arg k)))
    (cond ((not l) (hyper-fail "gamma: аргумент не линеен по k"))
          ((= (car l) 0) (hyper-make-frac 1 1))          ; Γ от k-свободного → константа
          ((not (sum-int? (car l))) (hyper-fail "gamma: коэффициент при k не целое число"))
          (else
           (let ((a (car l)) (b (cdr l)))
             (if (> a 0)
                 (hyper-make-frac (hyper-gamma-prod b a k a) 1)
                 (hyper-make-frac 1 (hyper-gamma-prod-neg b a k (- a)))))))))

; ---- главная функция: отношение t(k+1)/t(k) как пара многочленов (p . q) ----

; t — терм; возвращает (p . q) либо бросает hyper-fail (отказ).
; Суммы, функции от k (sin k, H_k, Γ(k/2)), k^k, нецелые α при x^k — отказ.
(define (hyper-ratio-core t k)
  (cond ((sum-k-free? t k) (hyper-make-frac 1 1))       ; константа (в т.ч. параметры)
        ((equal? t k) (hyper-make-frac (list '+ k 1) k))
        ((and (op-expr? t) (or (equal? (car t) '+) (equal? (car t) '-)) (polynomial? t k))
         ; сумма/разность, являющаяся многочленом по k (напр. 4k+1): R(k+1)/R(k)
         (hyper-make-frac (simplify (subst (list '= k (list '+ k 1)) t)) t))
        ((and (op-expr? t) (equal? (car t) '+)) (hyper-fail "сумма слагаемых не многочлен"))
        ((and (op-expr? t) (equal? (car t) '-) (= (length t) 2))
         (hyper-ratio-core (cadr t) k))                 ; (−A): отношение то же
        ((and (op-expr? t) (equal? (car t) '-)) (hyper-fail "разность слагаемых не многочлен"))
        ((and (op-expr? t) (equal? (car t) '*))
         (hyper-frac-prod-list (cdr t) k))
        ((and (op-expr? t) (equal? (car t) '/) (= (length t) 3))
         (hyper-frac-mul (hyper-ratio-core (cadr t) k)
                         (hyper-frac-recip (hyper-ratio-core (caddr t) k))))
        ((and (op-expr? t) (equal? (car t) '^) (= (length t) 3) (sum-k-free? (cadr t) k))
         (let ((l (hyper-lin (caddr t) k)))
           (cond ((not l) (hyper-fail "экспонента не линейна по k"))
                 ((= (car l) 0) (hyper-make-frac 1 1))  ; x^β, β без k
                 ((sum-int? (car l))
                  (hyper-make-frac (simplify (list '^ (cadr t) (car l))) 1))
                 ((number? (cadr t))                     ; 4^(k/2): числовая база — константа-степень
                  (hyper-make-frac (simplify (list '^ (cadr t) (car l))) 1))
                 (else (hyper-fail "нецелая степень при k")))))
        ((and (op-expr? t) (equal? (car t) '^) (= (length t) 3) (sum-k-free? (caddr t) k)
              (sum-int? (caddr t)) (not (= (caddr t) 0)))
         ; (u(k))^e при целом e: (u(k+1)/u(k))^e
         (hyper-frac-pow (hyper-ratio-core (cadr t) k) (caddr t)))
        ((and (op-expr? t) (equal? (car t) 'gamma) (= (length t) 2))
         (hyper-gamma-ratio (cadr t) k))
        ((and (op-expr? t) (equal? (car t) 'factorial) (= (length t) 2))
         (hyper-gamma-ratio (list '+ (cadr t) 1) k))
        ((and (op-expr? t) (equal? (car t) 'binomial) (= (length t) 3))
         ; C(N,M) → Γ(N+1)/(Γ(M+1)·Γ(N−M+1)), дальше обычный путь
         (hyper-ratio-core (list '/ (list 'gamma (list '+ (cadr t) 1))
                                 (list '* (list 'gamma (list '+ (caddr t) 1))
                                       (list 'gamma (list '+ (list '- (cadr t) (caddr t)) 1)))) k))
        ((and (op-expr? t) (equal? (car t) 'rf) (= (length t) 3))    ; (a)_k = Γ(a+k)/Γ(a)
         (hyper-ratio-core (list '/ (list 'gamma (list '+ (cadr t) (caddr t)))
                                 (list 'gamma (cadr t))) k))
        ((and (op-expr? t) (equal? (car t) 'ff) (= (length t) 3))    ; ff(a,k)=Γ(a+1)/Γ(a−k+1)
         (hyper-ratio-core (list '/ (list 'gamma (list '+ (cadr t) 1))
                                 (list 'gamma (list '+ (list '- (cadr t) (caddr t)) 1))) k))
        ((polynomial? t k)                                        ; рациональная часть R(k): R(k+1)/R(k)
         (hyper-make-frac (simplify (subst (list '= k (list '+ k 1)) t)) t))
        (else (hyper-fail "не гипергеометрический терм"))))

; обёртка: #f — отказ («не гипергеометрический»)
(define (hyper-ratio t k) (hyper-catch (lambda () (hyper-ratio-core t k))))
(define (hyper-termp t k) (if (hyper-ratio t k) #t #f))

; ---- сдвиг и целые корни результанта (для 21l.3 Госпера) ----

; p(k+h): h — целое число (обычно > 0) или выражение; подстановка + раскрытие
(define (poly-shift p k h)
  (expand (simplify (subst (list '= k (list '+ k h)) p))))

; целые корни ≥ 0 многочлена r по h. Результант может содержать параметры (q = (k+a)(k+b) →
; множитель h+a−b): раскладываем на множители (factor-list), берём только линейные множители
; c1·h + c0 с числовыми c1 ≠ 0, c0 (корень −c0/c1, целый ≥ 0); множители с параметрами —
; генерические (целого корня нет). poly-int-roots-param возвращает также список
; параметрических множителей — вызывающий (gosper-normal) пишет по ним record-condition.
(define (poly-int-roots r h)
  (car (poly-int-roots-param r h)))
(define (poly-int-roots-param r h)
  (let ((fl (factor-list r)))
    (if (or (not (list? fl)) (< (length fl) 2))
        (cons '() '())
        (gosper-roots-loop (cdr fl) h '() '()))))
(define (gosper-roots-loop fs h roots params)
  (if (null? fs)
      (cons roots params)
      (let* ((f (car (car fs)))
             (c1 (coeff f h 1))
             (c0 (coeff f h 0)))
        (cond ((and (= (degree f h) 1) (number? c1) (not (= c1 0)) (number? c0))
               (let ((root (/ (- c0) c1)))
                 (if (and (sum-int? root) (>= root 0))
                     (gosper-roots-loop (cdr fs) h (cons root roots) params)
                     (gosper-roots-loop (cdr fs) h roots params))))
              ((and (= (degree f h) 0) (number? f) (not (= f 0)))
               (gosper-roots-loop (cdr fs) h roots params))
              (else (gosper-roots-loop (cdr fs) h roots (cons f params)))))))

; дисперсия знаменателя q: максимальный целый корень >= 1 результанта res_h(q(k), q(k+h)) по k
(define (poly-dispersion q k)
  (let ((pos (filter (lambda (x) (> x 0))
                     (poly-int-roots (resultant q (poly-shift q k 'h) k) 'h))))
    (if (null? pos) #f (apply max pos))))
