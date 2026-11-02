; series.lisp — усечённые степенные ряды Лорана как объект `series` (Шаг 20)
;
; Представление: (make-object 'series var pt val cs n)
;   var — переменная ряда (символ), pt — точка разложения a (число, символ или выражение без var),
;   val — valuation: показатель первого члена (может быть отрицательным),
;   cs  — список коэффициентов при (var − pt)^val, (var − pt)^(val+1), ... (коэффициенты — любые выражения);
;         хвост, которого нет в списке, — точные нули; cs пуст только у нулевого ряда,
;   n   — порядок усечения N: всё, что ≥ N, — O((var − pt)^N); n ≥ ser-big означает «точно» (многочлен/константа).
; Инвариант (ser-make): первый коэффициент ненулевой, val ≥ n у нулевого ряда (val = n).
;
; Коэффициент может содержать log(var − pt) как «медленную» величину — так получаются ряды вида x·log x
; (log(x − a) считается константой при арифметике ряда; производная/интеграл такого ряда не берутся).
;
; Арифметика: методы + * ^ (а также - и / — через них, упроститель сводит их к + * ^). Скаляры, зависящие от var,
; раскладываются в ряд того же порядка, прочие — константы.
; Публичный интерфейс: (series e x a n), (taylor e x a n), (series->expr s), (series-coeff s k), (series-order s).
; Все внутренние имена — с префиксом ser-.

; Шаг 21h': модуль series. Экспорт — публичный интерфейс и то, чем пользуется limit (ser-bad? ser-lg ser-var ser-val ser-cs
; ser-compute ser-precision-err?); остальные ser-... приватны (тесты обращаются к ним как series::ser-...)
(module series
  (export series series? taylor series->expr series-coeff series-order
          ser-bad? ser-lg ser-var ser-val ser-cs ser-compute ser-precision-err? ser-with-logx))

(deftype 'series 'any)
(put 'series 'commutative #t)

(define ser-big 1000000)
(define (ser-exact? n) (>= n 500000))

; рабочий порядок (абсолютный показатель, до которого разворачиваются бесконечные разложения);
; его задаёт драйвер series, вне драйвера — значение по умолчанию
(define *ser-w* 12)
(define (ser-with-w w thunk)
  (let ((old *ser-w*))
    (set! *ser-w* w)
    (unwind-protect (thunk) (set! *ser-w* old))))

; ---------- представление ----------

(define (series? x) (and (object? x) (equal? (object-type x) 'series)))
(define (ser-var s) (object-ref s 0))
(define (ser-pt s) (object-ref s 1))
(define (ser-val s) (object-ref s 2))
(define (ser-cs s) (object-ref s 3))
(define (ser-n s) (object-ref s 4))

; сообщение об ошибке «ряд оказался нулевым при данной точности» (лечится повышением порядка);
; все остальные ошибки series — «не умею», повтор с большей точностью бесполезен
(define ser-msg-prec "series: недостаточно членов ряда (нулевой ряд) — повысьте порядок")
(define (ser-precision-err? err) (equal? (error-message err) ser-msg-prec))

(define (ser-zero-c? c) (and (number? c) (= c 0)))

; (cs . val) без нулевых коэффициентов в начале
(define (ser-strip-lead cs v)
  (if (and (not (null? cs)) (ser-zero-c? (car cs)))
      (ser-strip-lead (cdr cs) (+ v 1))
      (list cs v)))
(define (ser-strip-trail cs) (reverse (car (ser-strip-lead (reverse cs) 0))))

; нормализующий конструктор: усечение до n, снятие нулей в начале и в конце
(define (ser-make var pt val cs n0)
  (let* ((n (if (ser-exact? n0) ser-big n0))
         (cs1 (if (ser-exact? n) cs (take cs (max 0 (- n val)))))
         (lead (ser-strip-lead cs1 val))
         (cs2 (ser-strip-trail (car lead))))
    (if (null? cs2)
        (make-object 'series var pt n '() n)
        (make-object 'series var pt (cadr lead) cs2 n))))

(define (ser-const var pt c) (ser-make var pt 0 (list c) ser-big))

(define (ser-range lo hi) (if (< lo hi) (map (lambda (i) (+ lo i)) (range (- hi lo))) '()))

(define (ser-coef-at s e)
  (let ((i (- e (ser-val s))))
    (if (or (< i 0) (not (< i (length (ser-cs s))))) 0 (nth (ser-cs s) i))))

; ---------- арифметика коэффициентов ----------

(define (ser-c+ a b)
  (cond ((equal? a 0) b)
        ((equal? b 0) a)
        ((and (number? a) (number? b)) (+ a b))
        (else (simplify (list '+ a b)))))
(define (ser-c* a b)
  (cond ((or (equal? a 0) (equal? b 0)) 0)
        ((equal? a 1) b)
        ((equal? b 1) a)
        ((and (number? a) (number? b)) (* a b))
        (else (simplify (list '* a b)))))
(define (ser-c-neg a) (ser-c* -1 a))
(define (ser-c-inv a)
  (if (number? a) (/ 1 a) (simplify (list '^ a -1))))

(define (ser-fact k) (if (< k 2) 1 (* k (ser-fact (- k 1)))))
(define (ser-sgn j) (if (= (mod j 2) 0) 1 -1))

; ---------- арифметика рядов ----------

; верхняя граница показателей хранимых коэффициентов (нулевой ряд — «минус бесконечность»)
(define (ser-top s) (if (null? (ser-cs s)) (- 0 ser-big) (+ (ser-val s) (length (ser-cs s)))))

(define (ser-add a b)
  (let* ((n (min (ser-n a) (ser-n b)))
         (v (min (ser-val a) (ser-val b)))
         (hi (min n (max (ser-top a) (ser-top b)))))
    (ser-make (ser-var a) (ser-pt a) v
              (map (lambda (e) (ser-c+ (ser-coef-at a e) (ser-coef-at b e))) (ser-range v hi))
              n)))

; умножение на константу c (не зависящую от переменной); 0·(O(...)) = 0 точно
(define (ser-scale s c)
  (if (ser-zero-c? c)
      (ser-make (ser-var s) (ser-pt s) 0 '() ser-big)
      (ser-make (ser-var s) (ser-pt s) (ser-val s) (map (lambda (k) (ser-c* c k)) (ser-cs s)) (ser-n s))))

(define (ser-neg s) (ser-scale s -1))
(define (ser-sub a b) (ser-add a (ser-neg b)))

; умножение на t^d
(define (ser-shift s d)
  (ser-make (ser-var s) (ser-pt s) (+ (ser-val s) d) (ser-cs s)
            (if (ser-exact? (ser-n s)) ser-big (+ (ser-n s) d))))

; усечение до порядка n (если ряд известен точнее)
(define (ser-trunc s n)
  (if (>= (ser-n s) n)
      (ser-make (ser-var s) (ser-pt s) (ser-val s) (ser-cs s) n)
      s))

; свёртка коэффициентов: k-й коэффициент произведения
(define (ser-conv-loop ca cb k i hi acc)
  (if (> i hi)
      acc
      (ser-conv-loop ca cb k (+ i 1) hi (ser-c+ acc (ser-c* (vref ca i) (vref cb (- k i)))))))
(define (ser-conv ca cb la lb k)
  (ser-conv-loop ca cb k (max 0 (- k (- lb 1))) (min k (- la 1)) 0))

(define (ser-mul a b)
  (let* ((va (ser-val a)) (vb (ser-val b))
         (n (min (+ va (ser-n b)) (+ vb (ser-n a))))
         (ca (list->vector (ser-cs a))) (cb (list->vector (ser-cs b)))
         (la (vlength ca)) (lb (vlength cb))
         (v (+ va vb))
         (len0 (if (or (= la 0) (= lb 0)) 0 (- (+ la lb) 1)))
         (len (if (ser-exact? n) len0 (min len0 (max 0 (- n v))))))
    (ser-make (ser-var a) (ser-pt a) v
              (map (lambda (k) (ser-conv ca cb la lb k)) (range len))
              n)))

; обратный ряд: b0 = 1/c0, b_k = −b0·Σ_{j=1..k} c_j·b_{k−j}; потеря точности — 2·val
(define (ser-rsum cv m b k j hi acc)
  (if (> j hi)
      acc
      (ser-rsum cv m b k (+ j 1) hi (ser-c+ acc (ser-c* (vref cv j) (vref b (- k j)))))))
(define (ser-recip-fill cv m b b0 k rel)
  (if (< k rel)
      (begin (vset! b k (ser-c* (ser-c-neg b0) (ser-rsum cv m b k 1 (min k (- m 1)) 0)))
             (ser-recip-fill cv m b b0 (+ k 1) rel))
      b))

(define (ser-recip s)
  (if (null? (ser-cs s))
      (error ser-msg-prec)
      (let* ((v (ser-val s)) (cs (ser-cs s)) (n (ser-n s)) (b0 (ser-c-inv (car cs))))
        (if (and (= (length cs) 1) (ser-exact? n))
            (ser-make (ser-var s) (ser-pt s) (- v) (list b0) ser-big)
            (let* ((rel (min (- n v) (max 1 (+ *ser-w* v))))
                   (b (make-vector rel 0)))
              (vset! b 0 b0)
              (ser-recip-fill (list->vector cs) (length cs) b b0 1 rel)
              (ser-make (ser-var s) (ser-pt s) (- v) (vector->list b) (+ (- v) rel)))))))

(define (ser-pow-pos s k)
  (cond ((= k 1) s)
        ((= (mod k 2) 0) (let ((h (ser-pow-pos s (/ k 2)))) (ser-mul h h)))
        (else (ser-mul s (ser-pow-pos s (- k 1))))))

(define (ser-pow-int s k)
  (cond ((= k 0) (ser-const (ser-var s) (ser-pt s) 1))
        ((< k 0) (ser-pow-pos (ser-recip s) (- k)))
        (else (ser-pow-pos s k))))

; ---------- производная и интеграл по (var − pt) ----------

(define (ser-slow? s) (any? (lambda (c) (contains-sym? c (ser-var s))) (ser-cs s)))

(define (ser-deriv s)
  (if (ser-slow? s)
      (error "series: производная ряда с коэффициентом log(x − a) не поддерживается")
      (let ((v (ser-val s)))
        (ser-make (ser-var s) (ser-pt s) (- v 1)
                  (map2 (lambda (c i) (ser-c* (+ v i) c)) (ser-cs s) (range (length (ser-cs s))))
                  (if (ser-exact? (ser-n s)) ser-big (- (ser-n s) 1))))))

(define (ser-integ s)
  (let ((v (ser-val s)))
    (if (not (ser-zero-c? (ser-coef-at s -1)))
        (error "series: интеграл ряда с членом 1/x даёт логарифм — не поддерживается")
        (ser-make (ser-var s) (ser-pt s) (+ v 1)
                  (map2 (lambda (c i) (if (= (+ v i 1) 0) 0 (ser-c* (/ 1 (+ v i 1)) c))) (ser-cs s) (range (length (ser-cs s))))
                  (if (ser-exact? (ser-n s)) ser-big (+ (ser-n s) 1))))))

; ---------- суммы степеней: Σ f(k)·u^k, val(u) ≥ 1 ----------

(define (ser-powsum-loop u fk k kmax p acc)
  (if (> k kmax)
      acc
      (let ((f (fk k)))
        (ser-powsum-loop u fk (+ k 1) kmax (if (< k kmax) (ser-mul p u) p)
                         (if (ser-zero-c? f) acc (ser-add acc (ser-scale p f)))))))

; cap — абсолютный порядок, до которого нужен результат
(define (ser-powsum u fk cap)
  (let ((var (ser-var u)) (pt (ser-pt u)) (nn (min (ser-n u) cap)))
    (if (null? (ser-cs u))
        (ser-make var pt 0 (list (fk 0)) (ser-n u))
        (let ((kmax (if (>= (ser-val u) nn) 0 (floor (/ (- nn 1) (ser-val u))))))
          (ser-trunc (ser-powsum-loop u fk 0 kmax (ser-const var pt 1) (ser-const var pt 0)) nn)))))

; g = c + u: свободный член и остаток с val ≥ 1
(define (ser-split g)
  (cond ((< (ser-val g) 0) (error "series: аргумент функции имеет полюс в точке разложения"))
        ((< (ser-n g) 1) (error ser-msg-prec))
        ((> (ser-val g) 0) (list 0 g))
        (else (list (car (ser-cs g))
                    (ser-make (ser-var g) (ser-pt g) 1 (cdr (ser-cs g)) (ser-n g))))))

; ---------- значения функций в точке (константе) ----------

; (Шаг 21c: точные значения — tan 0, acot 0, sin(π/2), ... — считает simplify)
(define (ser-fval h c)
  (if (equal? (type-of c) 'float)
      (eval-num (list h c))
      (simplify (list h c))))

; ---------- элементарные функции от ряда ----------

(define (ser-exp g)
  (let* ((cu (ser-split g)))
    (ser-scale (ser-powsum (cadr cu) (lambda (k) (/ 1 (ser-fact k))) *ser-w*) (ser-fval 'exp (car cu)))))

; (sin g . cos g) через сложение: sin(c+u) = sin c·cos u + cos c·sin u
(define (ser-sincos g)
  (let* ((cu (ser-split g)) (c (car cu)) (u (cadr cu))
         (S (ser-powsum u (lambda (k) (if (= (mod k 2) 1) (/ (ser-sgn (/ (- k 1) 2)) (ser-fact k)) 0)) *ser-w*))
         (C (ser-powsum u (lambda (k) (if (= (mod k 2) 0) (/ (ser-sgn (/ k 2)) (ser-fact k)) 0)) *ser-w*))
         (sc (ser-fval 'sin c)) (cc (ser-fval 'cos c)))
    (list (ser-add (ser-scale C sc) (ser-scale S cc))
          (ser-sub (ser-scale C cc) (ser-scale S sc)))))

(define (ser-sinhcosh g)
  (let* ((cu (ser-split g)) (c (car cu)) (u (cadr cu))
         (S (ser-powsum u (lambda (k) (if (= (mod k 2) 1) (/ 1 (ser-fact k)) 0)) *ser-w*))
         (C (ser-powsum u (lambda (k) (if (= (mod k 2) 0) (/ 1 (ser-fact k)) 0)) *ser-w*))
         (sc (ser-fval 'sinh c)) (cc (ser-fval 'cosh c)))
    (list (ser-add (ser-scale C sc) (ser-scale S cc))
          (ser-add (ser-scale C cc) (ser-scale S sc)))))

; g/(c·t^k) − 1: ряд с val ≥ 1 (g ненулевой)
(define (ser-unit-part g)
  (let* ((k (ser-val g)) (cs (ser-cs g)) (ic (ser-c-inv (car cs))))
    (ser-make (ser-var g) (ser-pt g) 1 (map (lambda (z) (ser-c* z ic)) (cdr cs))
              (if (ser-exact? (ser-n g)) ser-big (- (ser-n g) k)))))

; log(var − pt) — «медленная» константа
; Шаг 21j.1: *ser-logx* = (var . L) — log var в точке 0 заменяется выражением L без var (Грунц: log ω = logw,
; как logx в эталонной реализации); задаётся только через ser-with-logx, по умолчанию #f — прежнее поведение
(define *ser-logx* #f)
(define (ser-with-logx var lx thunk)
  (let ((old *ser-logx*))
    (set! *ser-logx* (cons var lx))
    (unwind-protect (thunk) (set! *ser-logx* old))))

(define (ser-lg g)
  (let ((x (ser-var g)) (a (ser-pt g)))
    (if (and *ser-logx* (equal? (car *ser-logx*) x) (equal? a 0))
        (cdr *ser-logx*)
        (simplify (list 'log (if (equal? a 0) x (simplify (list '+ x (list '* -1 a)))))))))

(define (ser-log-const c) (if (equal? c 1) 0 (simplify (list 'log c))))

; log(c·t^k·(1+u)) = log c + k·log t + log(1+u)
(define (ser-log g)
  (if (null? (ser-cs g))
      (error ser-msg-prec)
      (let* ((k (ser-val g)) (c (car (ser-cs g))) (u (ser-unit-part g))
             (const (ser-c+ (ser-log-const c) (if (= k 0) 0 (ser-c* k (ser-lg g))))))
        (ser-add (ser-powsum u (lambda (j) (cond ((= j 0) 0) ((= (mod j 2) 1) (/ 1 j)) (else (/ -1 j)))) *ser-w*)
                 (ser-const (ser-var g) (ser-pt g) const)))))

(define (ser-binom-loop r j i acc)
  (if (= i j)
      acc
      (ser-binom-loop r j (+ i 1) (ser-c* acc (ser-c* (ser-c+ r (- 0 i)) (/ 1 (+ i 1)))))))
(define (ser-binom r j) (ser-binom-loop r j 0 1))

(define (ser-cpow c r) (if (equal? c 1) 1 (simplify (list '^ c r))))

; степень с нецелым (рациональным или символьным) показателем: c^r · t^(k·r) · (1+u)^r
(define (ser-pow-rat g r)
  (cond ((null? (ser-cs g)) (error ser-msg-prec))
        ((integer? r) (ser-pow-int g r))
        (else
         (let* ((k (ser-val g)) (c (car (ser-cs g))) (kr (* k r)))
           (if (not (or (= k 0) (and (rational-number? r) (integer? kr))))
               (error "series: показатель не даёт ряда Лорана (нужен ряд Пюизё)")
               (ser-shift (ser-scale (ser-powsum (ser-unit-part g) (lambda (j) (ser-binom r j))
                                                 (max 1 (- *ser-w* kr)))
                                     (ser-cpow c r))
                          kr))))))

; общая степень: показатель без переменной — через ser-pow-int/ser-pow-rat, иначе exp(e·log g)
(define (ser-power g e)
  (if (and (not (series? e)) (x-free? e (ser-var g)))
      (if (integer? e) (ser-pow-int g e) (ser-pow-rat g e))
      (ser-exp (ser-mul (ser-lift g e) (ser-log g)))))

; ---------- обратные функции: F(c) + ∫ g'·F'(g) dt ----------

(define (ser-need-regular g)
  (if (< (ser-val g) 0) (error "series: аргумент функции имеет полюс в точке разложения") #t))

(define (ser-inverse h g dser sgn)
  (ser-need-regular g)
  (ser-add (ser-const (ser-var g) (ser-pt g) (ser-fval h (ser-coef-at g 0)))
           (ser-scale (ser-integ (ser-mul (ser-deriv g) dser)) sgn)))

(define (ser-one+g2 g sgn)   ; 1 + sgn·g²
  (ser-add (ser-const (ser-var g) (ser-pt g) 1) (ser-scale (ser-mul g g) sgn)))

; ---------- вычисление выражения ----------

(define (ser-fn h g)
  (cond ((equal? h 'exp) (ser-exp g))
        ((member? h '(log ln)) (ser-log g))
        ((equal? h 'sqrt) (ser-pow-rat g 1/2))
        ((equal? h 'sin) (car (ser-sincos g)))
        ((equal? h 'cos) (cadr (ser-sincos g)))
        ((equal? h 'tan) (let ((sc (ser-sincos g))) (ser-mul (car sc) (ser-recip (cadr sc)))))
        ((equal? h 'cot) (let ((sc (ser-sincos g))) (ser-mul (cadr sc) (ser-recip (car sc)))))
        ((equal? h 'sec) (ser-recip (cadr (ser-sincos g))))
        ((equal? h 'csc) (ser-recip (car (ser-sincos g))))
        ((equal? h 'sinh) (car (ser-sinhcosh g)))
        ((equal? h 'cosh) (cadr (ser-sinhcosh g)))
        ((equal? h 'tanh) (let ((sc (ser-sinhcosh g))) (ser-mul (car sc) (ser-recip (cadr sc)))))
        ((equal? h 'coth) (let ((sc (ser-sinhcosh g))) (ser-mul (cadr sc) (ser-recip (car sc)))))
        ((equal? h 'sech) (ser-recip (cadr (ser-sinhcosh g))))
        ((equal? h 'csch) (ser-recip (car (ser-sinhcosh g))))
        ((equal? h 'atan) (ser-inverse 'atan g (ser-recip (ser-one+g2 g 1)) 1))
        ((equal? h 'acot) (ser-inverse 'acot g (ser-recip (ser-one+g2 g 1)) -1))
        ((equal? h 'atanh) (ser-inverse 'atanh g (ser-recip (ser-one+g2 g -1)) 1))
        ((equal? h 'asin) (ser-inverse 'asin g (ser-pow-rat (ser-one+g2 g -1) -1/2) 1))
        ((equal? h 'acos) (ser-inverse 'acos g (ser-pow-rat (ser-one+g2 g -1) -1/2) -1))
        ((equal? h 'asinh) (ser-inverse 'asinh g (ser-pow-rat (ser-one+g2 g 1) -1/2) 1))
        (else #f)))

(define ser-fn-names '(exp log ln sqrt sin cos tan cot sec csc sinh cosh tanh coth sech csch atan acot atanh asin acos asinh))

; операции, которые умеет дифференцировать F#-diff (остальное diff превращает в 0 — молча неверно)
(define ser-diff-heads '(+ - * / ^ sin cos tan cot sec csc sinh cosh tanh coth sech csch asin acos atan acot asec acsc
                          asinh acosh atanh acoth asech acsch exp log ln sqrt))

(define (ser-diffable? e x)
  (cond ((x-free? e x) #t)
        ((op-expr? e) (and (member? (car e) ser-diff-heads) (every? (lambda (a) (ser-diffable? a x)) (cdr e))))
        (else #t)))

; значение расходится: 0^p при p ≤ 0, log 0
(define (ser-bad? v)
  (cond ((op-expr? v)
         (or (and (equal? (car v) '^) (equal? (cadr v) 0) (or (not (number? (caddr v))) (<= (caddr v) 0)))
             (and (member? (car v) '(log ln)) (equal? (cadr v) 0))
             (any? ser-bad? (cdr v))))
        (else #f)))

; запасной путь: ряд Тейлора через производные: c_k = f^(k)(a)/k! (значения в точке должны быть конечны)
(define (ser-taylor-loop e x a k acc)
  (if (>= k *ser-w*)
      (ser-make x a 0 (reverse acc) *ser-w*)
      (let ((v (simplify (subst (list '= x a) e))))
        (if (ser-bad? v)
            (error "series: функция или её производная не определена в точке разложения")
            (let ((acc2 (cons (ser-c* v (/ 1 (ser-fact k))) acc))
                  (d (simplify (diff x e))))
              (if (equal? d 0)
                  (ser-make x a 0 (reverse acc2) ser-big)
                  (ser-taylor-loop d x a (+ k 1) acc2)))))))

; пользовательская функция: тело, вычисленное на выражениях-аргументах, раскладывается дальше
(define (ser-user-body e)
  (try (let ((r (apply (eval (car e)) (cdr e)))) (if (equal? r e) #f r))
       (lambda (err) #f)))

(define (ser-ex-other e x a)
  (let ((body (ser-user-body e)))
    (cond (body (ser-ex (simplify body) x a))
          ((ser-diffable? e x)
           (with-step ('series-derivatives "Ряд Тейлора через производные" e
                       :comment "коэффициенты c_k = f⁽ᵏ⁾(a)/k! вычисляются последовательным дифференцированием" :after ser->form)
             (ser-taylor-loop e x a 0 '())))
          (else (error "series: не умею раскладывать" (math-print e))))))

(define (ser-ex-all args x a) (map (lambda (z) (ser-ex z x a)) args))

; ---------- шаги (шаг S.4) ----------
; Рамки with-step работают только при включённом журнале (при выключенном — прямые вызовы, без замыканий):
;   series            — верхняя рамка «Разложение в ряд Тейлора (Лорана) в точке a до порядка n»; ряд считается тихо
;                       (с повышением точности), затем один раз повторяется с журналом (рабочий порядок — последний);
;   series-known      — стандартное разложение функции (exp, sin, log(1+u), бином, …);
;   series-compose    — подстановка ряда аргумента в стандартное разложение;
;   series-arith      — сумма, произведение, частное, целая степень рядов;
;   series-derivatives — запасной путь: коэффициенты через производные.
; «После» шагов — форма (+ члены… (O (^ t n))) — печатается как x − x^3/6 + O(x^5); checkSteps такие шаги пропускает.

(define *ser-show* 1000000)      ; до какого абсолютного порядка показывать ряд в шагах (в драйвере — запрошенный n)
(define *ser-last-w* 0)          ; рабочий порядок последней попытки драйвера

; t = x − a в виде для печати: x, x - 1, x + 2 (без перестановки слагаемых)
(define (ser-base s)
  (let ((a (ser-pt s)) (x (ser-var s)))
    (cond ((equal? a 0) x)
          ((and (real-numeric? a) (< a 0)) (list '+ x (- 0 a)))
          (else (list '- x a)))))

; член c·t^e без упрощения (порядок множителей и вид t сохраняются)
(define (ser-term c base e)
  (let ((p (cond ((= e 0) 1) ((= e 1) base) (else (list '^ base e)))))
    (cond ((equal? p 1) c)
          ((equal? c 1) p)
          (else (list '* c p)))))

; ряд как выражение с остатком (O (^ t n)); члены показываются до порядка cap
(define (ser-form s cap0)
  (let* ((v (ser-val s)) (n (ser-n s)) (exact (ser-exact? n))
         (cap (if exact cap0 (min n cap0)))
         (base (ser-base s))
         (cs (ser-cs s))
         (terms (filter (lambda (z) z)
                        (map2 (lambda (c i)
                                (if (or (ser-zero-c? c) (>= (+ v i) cap))
                                    #f
                                    (ser-term c base (+ v i))))
                              cs (range (length cs)))))
         (o-needed (or (not exact) (> (ser-top s) cap)))
         (o (list 'O (if (= cap 1) base (list '^ base cap)))))
    (cond ((and (null? terms) (not o-needed)) 0)
          ((null? terms) o)
          (o-needed (cons '+ (append terms (list o))))
          ((null? (cdr terms)) (car terms))
          (else (cons '+ terms)))))

(define (ser->form s) (ser-form s *ser-show*))

(define (ser-known-comment h)
  (cond ((equal? h 'exp) "exp(u) = 1 + u + u²/2! + u³/3! + …")
        ((equal? h 'sin) "sin(u) = u − u³/3! + u⁵/5! − …")
        ((equal? h 'cos) "cos(u) = 1 − u²/2! + u⁴/4! − …")
        ((equal? h 'tan) "tan(u) = sin(u)/cos(u): ряд синуса делится на ряд косинуса")
        ((equal? h 'cot) "cot(u) = cos(u)/sin(u): ряд косинуса делится на ряд синуса")
        ((member? h '(log ln)) "log(1 + u) = u − u²/2 + u³/3 − …; log(c·tᵏ·(1 + u)) = log c + k·log t + log(1 + u)")
        ((equal? h 'sqrt) "(1 + u)^(1/2) = 1 + u/2 − u²/8 + … (биномиальный ряд)")
        ((equal? h 'sinh) "sinh(u) = u + u³/3! + u⁵/5! + …")
        ((equal? h 'cosh) "cosh(u) = 1 + u²/2! + u⁴/4! + …")
        ((equal? h 'atan) "atan(u) = u − u³/3 + u⁵/5 − …")
        ((equal? h 'asin) "asin(u) = u + u³/6 + 3u⁵/40 + …")
        (else "стандартное разложение функции по степеням аргумента")))

; x и c·x — тривиальные «ряды», кадр для них был бы шумом
(define (ser-linear-arg? z x)
  (or (equal? z x)
      (and (op-expr? z) (equal? (car z) '*) (= (length z) 3) (x-free? (cadr z) x) (equal? (caddr z) x))
      (and (op-expr? z) (equal? (car z) '+) (every? (lambda (u) (or (x-free? u x) (ser-linear-arg? u x))) (cdr z)))))

(define (ser-nontrivial? args x)
  (any? (lambda (z) (and (not (x-free? z x)) (not (ser-linear-arg? z x)))) args))

(define (ser-arith-title h args)
  (cond ((equal? h '+) "Сумма рядов")
        ((equal? h '-) "Разность рядов")
        ((equal? h '*) "Произведение рядов")
        ((equal? h '/) "Частное рядов")
        ((and (equal? h '^) (integer? (simplify (cadr args))) (< (simplify (cadr args)) 0)) "Отрицательная степень ряда")
        (else "Степень ряда")))

(define (ser-arith-comment h)
  (cond ((member? h '(+ -)) "ряды слагаемых складываются почленно")
        ((equal? h '*) "ряды перемножаются (свёртка коэффициентов), результат усекается до нужного порядка")
        ((equal? h '/) "ряд делителя заменяется обратным рядом и умножается на ряд делимого")
        (else "степень — повторное умножение ряда на себя; отрицательная — через обратный ряд")))

; функция одного аргумента: стандартное разложение (аргумент x) или композиция (подстановка ряда аргумента)
(define (ser-ex-fn h arg x a e)
  (cond ((not (step-log-enabled?)) (ser-fn h (ser-ex arg x a)))
        ((ser-linear-arg? arg x)
         (with-step ('series-known "Стандартное разложение" e :comment (ser-known-comment h) :after ser->form)
           (ser-fn h (ser-ex arg x a))))
        (else
         (with-step ('series-compose "Подстановка ряда аргумента" e
                     :comment (string-append "ряд аргумента " (math-print arg) " подставляется в разложение функции " (to-string h))
                     :after ser->form)
           (let ((g (ser-ex arg x a)))
             (with-step ('series-known "Стандартное разложение" (list h 'u)
                         :comment (string-append (ser-known-comment h) "; здесь u = " (math-show (ser->form g)))
                         :after ser->form)
               (ser-fn h g)))))))

(define (ser-ex-op h args x a e)
  (cond ((not (step-log-enabled?)) (ser-ex-op-core h args x a e))
        ((and (member? h '(+ - * / ^))
              (if (equal? h '^)
                  (and (= (length args) 2) (not (equal? (car args) x)) (x-free? (cadr args) x) (integer? (simplify (cadr args))))
                  (ser-nontrivial? args x)))
         (with-step ('series-arith (ser-arith-title h args) e :comment (ser-arith-comment h) :after ser->form)
           (ser-ex-op-core h args x a e)))
        ((and (equal? h '^) (= (length args) 2) (not (x-free? (simplify (cadr args)) x)))
         (with-step ('series-compose "Степень с переменным показателем" e
                     :comment "f^g = exp(g·log f): ряд g·log f подставляется в разложение экспоненты" :after ser->form)
           (ser-ex-op-core h args x a e)))
        ((and (equal? h '^) (= (length args) 2) (not (equal? (car args) x)) (not (x-free? (car args) x)))
         (with-step ('series-known "Биномиальный ряд" e
                     :comment "(1 + u)^r = 1 + r·u + r(r−1)/2!·u² + …; c·tᵏ·(1 + u) выносится за степень" :after ser->form)
           (ser-ex-op-core h args x a e)))
        (else (ser-ex-op-core h args x a e))))

(define (ser-ex-op-core h args x a e)
  (cond ((equal? h '+) (let ((ss (ser-ex-all args x a))) (foldl ser-add (car ss) (cdr ss))))
        ((equal? h '*) (let ((ss (ser-ex-all args x a))) (foldl ser-mul (car ss) (cdr ss))))
        ((equal? h '-)
         (let ((ss (ser-ex-all args x a)))
           (if (null? (cdr ss)) (ser-neg (car ss)) (ser-sub (car ss) (foldl ser-add (cadr ss) (cdr (cdr ss)))))))
        ((equal? h '/)
         (let ((ss (ser-ex-all args x a)))
           (if (null? (cdr ss))
               (ser-recip (car ss))
               (ser-mul (car ss) (ser-recip (foldl ser-mul (cadr ss) (cdr (cdr ss))))))))
        ((and (equal? h '^) (= (length args) 2))
         (let ((b (simplify (car args))) (ex (simplify (cadr args))))
           (if (x-free? ex x)
               (ser-power (ser-ex b x a) ex)
               (ser-exp (ser-mul (ser-ex ex x a) (ser-log (ser-ex b x a)))))))
        ((and (member? h ser-fn-names) (= (length args) 1))
         (ser-ex-fn h (car args) x a e))
        (else (ser-ex-other e x a))))

(define (ser-ex e x a)
  (cond ((x-free? e x) (ser-const x a (simplify e)))
        ((equal? e x) (ser-make x a 0 (list a 1) ser-big))
        ((op-expr? e) (ser-ex-op (car e) (cdr e) x a e))
        (else (error "series: не умею раскладывать" e))))

; скаляр v как ряд (в точке/переменной ряда s): константа или разложение выражения
(define (ser-lift s v)
  (cond ((series? v) v)
        ((x-free? v (ser-var s)) (ser-const (ser-var s) (ser-pt s) (simplify v)))
        (else (ser-with-w (if (ser-exact? (ser-n s)) *ser-w* (ser-n s))
                          (lambda () (ser-ex (simplify v) (ser-var s) (ser-pt s)))))))

; ---------- методы ----------

(defmethod + (series series) (a b) (ser-add a b))
(defmethod + (series scalar) (a b) (ser-add a (ser-lift a b)))
(defmethod + (scalar series) (a b) (ser-add (ser-lift b a) b))
(defmethod * (series series) (a b) (ser-mul a b))
(defmethod * (series scalar) (a b) (ser-mul a (ser-lift a b)))
(defmethod * (scalar series) (a b) (ser-mul (ser-lift b a) b))
(defmethod ^ (series series) (a b) (ser-power a b))
(defmethod ^ (series scalar) (a b) (ser-power a b))
(defmethod ^ (scalar series) (a b) (ser-exp (ser-mul b (ser-log (ser-lift b a)))))

(defmethod simplify (series) (s) s)
(defmethod diff (series) (s x)
  (if (equal? x (ser-var s))
      (ser-deriv s)
      (ser-make (ser-var s) (ser-pt s) (ser-val s) (map (lambda (c) (diff x c)) (ser-cs s)) (ser-n s))))

; ---------- печать: 1 + x + 1/2*x^2 + O(x^3) ----------

(define (ser-paren? e) (and (op-expr? e) (member? (car e) '(+ -))))

(define (ser-tstr s)
  (let ((x (to-string (ser-var s))) (a (ser-pt s)))
    (cond ((equal? a 0) x)
          ((ser-paren? a) (string-append "(" x " - (" (math-print a) "))"))
          ((and (real-numeric? a) (< a 0)) (string-append "(" x " + " (math-print (- 0 a)) ")"))
          (else (string-append "(" x " - " (math-print a) ")")))))

(define (ser-neg-c? c)
  (or (and (real-numeric? c) (< c 0))
      (and (op-expr? c) (equal? (car c) '*) (real-numeric? (cadr c)) (< (cadr c) 0))))

(define (ser-term-body s c e)
  (if (= e 0)
      (math-print c)
      (let ((p (if (= e 1) (ser-tstr s) (string-append (ser-tstr s) "^" (to-string e)))))
        (if (equal? c 1)
            p
            (string-append (if (ser-paren? c) (string-append "(" (math-print c) ")") (math-print c)) "*" p)))))

; список (отрицателен? . текст) по возрастанию показателя
(define (ser-terms s)
  (let ((v (ser-val s)))
    (filter (lambda (z) z)
            (map2 (lambda (c i)
                    (if (ser-zero-c? c)
                        #f
                        (let ((neg (ser-neg-c? c)))
                          (list neg (ser-term-body s (if neg (ser-c-neg c) c) (+ v i))))))
                  (ser-cs s) (range (length (ser-cs s)))))))

(define (ser-ostr s)
  (let ((n (ser-n s)))
    (string-append "O(" (cond ((= n 0) "1") ((= n 1) (ser-tstr s)) (else (string-append (ser-tstr s) "^" (to-string n)))) ")")))

(define (ser-join terms first?)
  (if (null? terms)
      ""
      (string-append (if first?
                         (if (car (car terms)) "-" "")
                         (if (car (car terms)) " - " " + "))
                     (cadr (car terms))
                     (ser-join (cdr terms) #f))))

(define (ser-string s)
  (let ((body (ser-join (ser-terms s) #t)))
    (cond ((ser-exact? (ser-n s)) (if (equal? body "") "0" body))
          ((equal? body "") (ser-ostr s))
          (else (string-append body " + " (ser-ostr s))))))

(defmethod print (series) (s) (ser-string s))
(defmethod math-print (series) (s) (ser-string s))

; ---------- публичный интерфейс ----------

(define (ser-compute e x a w)
  (ser-with-w w (lambda () (ser-ex (simplify e) x a))))

; растущий запас точности: пока порядок результата меньше запрошенного n — повтор с большим рабочим порядком
(define ser-slacks '(4 10 22 46))
(define (ser-attempt e x a n slacks)
  (set! *ser-last-w* (+ n (car slacks)))
  (let ((r (try (ser-compute e x a (+ n (car slacks))) (lambda (err) err))))
    (cond ((series? r)
           (cond ((>= (ser-n r) n) (ser-trunc r n))
                 ((null? (cdr slacks)) r)
                 (else (ser-attempt e x a n (cdr slacks)))))
          ((or (null? (cdr slacks)) (not (ser-precision-err? r))) (error (error-message r)))
          (else (ser-attempt e x a n (cdr slacks))))))

; (series e x a n) — ряд Лорана выражения e по степеням (x − a) с точностью O((x − a)^n)
(define (series e x a0 n)
  (let ((a (simplify a0)))
    (cond ((not (symbol? x)) (error "series: переменная — символ"))
          ((not (and (integer? n) (>= n 0))) (error "series: порядок n — неотрицательное целое"))
          ((not (x-free? a x)) (error "series: точка разложения не должна содержать переменную"))
          ((member? a '(inf -inf)) (error "series: точка разложения должна быть конечной (для бесконечности — limit)"))
          (else (series-run e x a n)))))

; шаг S.4: верхняя рамка series; журнал выключен — прямой вызов драйвера
(define (series-top-comment s)
  (string-append (if (< (ser-val s) 0) "ряд Лорана: есть члены с отрицательными степенями" "ряд Тейлора")
                 "; внутри — использованные стандартные разложения и операции над рядами"))

(define (series-run e x a n)
  (if (not (step-log-enabled?))
      (ser-attempt e x a n ser-slacks)
      (with-step ('series (string-append "Разложение в ряд Тейлора (Лорана) в точке " (math-print a) " до порядка " (to-string n))
                  (list 'series e x a n)
                  :comment series-top-comment
                  :after (lambda (s) (ser-form s n)))
        (let ((r (call-quietly (lambda () (ser-attempt e x a n ser-slacks)))))
          (let ((old *ser-show*) (w *ser-last-w*))
            (set! *ser-show* n)
            (try (unwind-protect (ser-compute e x a w) (set! *ser-show* old)) (lambda (err) #f)))
          r))))

(define (series->expr s)
  (let ((base (if (equal? (ser-pt s) 0)
                  (ser-var s)
                  (simplify (list '+ (ser-var s) (list '* -1 (ser-pt s))))))
        (v (ser-val s)))
    (let ((terms (filter (lambda (z) z)
                         (map2 (lambda (c i) (if (ser-zero-c? c) #f (list '* c (list '^ base (+ v i)))))
                               (ser-cs s) (range (length (ser-cs s)))))))
      (if (null? terms) 0 (simplify (cons '+ terms))))))

; (taylor e x a n) — многочлен (без O) по (x − a): члены степени < n
(define (taylor e x a n) (series->expr (series e x a n)))

(define (series-coeff s k)
  (if (and (not (ser-exact? (ser-n s))) (>= k (ser-n s)))
      (error "series-coeff: показатель не меньше порядка усечения" k)
      (ser-coef-at s k)))

(define (series-order s) (if (ser-exact? (ser-n s)) 'inf (ser-n s)))
