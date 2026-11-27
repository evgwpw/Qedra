; dual.lisp — значение и производная выражения в точке через дуальные числа (шаг CHECK.DUAL).
;
; F(x₀ + ε), ε² = 0, даёт F(x₀) + F′(x₀)·ε: производная в точке БЕЗ шага h и без символьного diff от самого F
; (независимая сверка ответа интегрирования; конечные разности давали «неубедительно» между порогами 1e-6 и 1e-3).
; Обход дерева: + * - / ^ — правила дуальной арифметики; абсолютное значение — отдельно; прочая голова h(u₁…uₙ) —
; значение eval-num, производная Σ ∂h/∂uₖ · u′ₖ, где ∂h/∂uₖ — результат diff для головы от свежих символов %d1…%dn
; (считается eval-num в точке). Голова, у которой diff не даёт производной (остаток diff/deriv, либо 0 там, где он
; означает «не реализовано»), — отказ #f, а не догадка и не молчаливый 0. Числа — double: вещественные и комплексные
; (внутри — float или пара (re . im)); катастрофическое сокращение больших слагаемых в double остаётся (его закрывает
; только точная проверка — zero-test).
;
; (dual-eval e x x0 env)       → (v . d) | #f; v, d — как у eval-num: число или (+ re (* im %i))
; (dual-eval-parts e x x0 env) → ((re . im) . (re . im)) | #f (вещественные части — car, мнимые — cdr)
; env — список (символ значение) параметров (как правила subst); x0 и значения — рациональные, float или (+ re (* im %i)).
(module dual
  (export dual-eval dual-eval-parts))

; ---------- числа: float или (re . im) ----------
(define (dn-re a) (if (pair? a) (car a) a))
(define (dn-im a) (if (pair? a) (cdr a) 0.0))
; мнимая (вещественная) часть порядка 1e-13 от другой — шум округления double (√(−a)² = −a + 3e-16·i): сбрасывается,
; иначе знак шума переключает ветвь следующего √/log (главное значение на разрезе)
(define (dn-norm re im)
  (cond ((not (and (equal? re re) (equal? im im))) (cons re im))
        ((<= (abs im) (* 1e-13 (abs re))) re)
        ((<= (abs re) (* 1e-13 (abs im))) (cons 0.0 im))
        (else (cons re im))))
(define (dn-zero? a) (and (not (pair? a)) (= a 0)))
(define (dn+ a b)
  (if (or (pair? a) (pair? b))
      (dn-norm (+ (dn-re a) (dn-re b)) (+ (dn-im a) (dn-im b)))
      (+ a b)))
(define (dn* a b)
  (if (or (pair? a) (pair? b))
      (let ((ar (dn-re a)) (ai (dn-im a)) (br (dn-re b)) (bi (dn-im b)))
        (dn-norm (- (* ar br) (* ai bi)) (+ (* ar bi) (* ai br))))
      (* a b)))
(define (dn-neg a) (dn* -1.0 a))
(define (dn/ a b)
  (if (dn-zero? b)
      (dl-fail)
      (if (or (pair? a) (pair? b))
          (let* ((ar (dn-re a)) (ai (dn-im a)) (br (dn-re b)) (bi (dn-im b))
                 (den (+ (* br br) (* bi bi))))
            (dn-norm (/ (+ (* ar br) (* ai bi)) den) (/ (- (* ai br) (* ar bi)) den)))
          (/ a b))))
; NaN в диалекте: (< nan b) и (= nan nan) — #t, только (equal? nan nan) — #f
(define (dn-finite-1? x) (and (equal? x x) (< (abs x) 1e300)))
(define (dn-finite? a) (and (dn-finite-1? (dn-re a)) (dn-finite-1? (dn-im a))))
(define (dl-fail) (error "dual: нет значения или производной"))

; число → выражение для eval-num
(define (dn->expr a) (if (pair? a) (list '+ (car a) (list '* (cdr a) '%i)) a))
; результат eval-num (число или (+ re (* im %i))) → внутреннее число; не число — #f
(define (dn-parse v)
  (cond ((real-numeric? v) (* 1.0 v))
        ((equal? v '%i) (cons 0.0 1.0))
        ((and (op-expr? v) (equal? (car v) '+))
         (foldl (lambda (acc t) (let ((p (and acc (dn-parse t)))) (and p (dn+ acc p)))) 0.0 (cdr v)))
        ((and (op-expr? v) (equal? (car v) '*))
         (foldl (lambda (acc t) (let ((p (and acc (dn-parse t)))) (and p (dn* acc p)))) 1.0 (cdr v)))
        (else #f)))
; голова, значения которой считает polylog-evalf (eval-num их не знает)
(define dl-pl-heads '(polylog lambert_w))
(define (dl-num h e)
  (let ((r (if (member? h dl-pl-heads) (try (polylog-evalf e) (lambda (err) #f)) #f)))
    (dn-parse (or r (eval-num e)))))
(define (dl-num! h e) (let ((r (dl-num h e))) (if (and r (dn-finite? r)) r (dl-fail))))

; ---------- производные голов: diff от свежих символов, кэш ----------
(define dl-dcache (make-hash))
(define (dl-sym k) (string->symbol (string-append "%d" (to-string k))))
(define (dl-has-residue? e)
  (cond ((not (pair? e)) #f)
        ((member? (car e) '(diff deriv integrate)) #t)
        (else (any? dl-has-residue? (cdr e)))))
; (diff s s) — недоработка diff у polylog: это 1
(define (dl-fixdiff e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'diff) (= (length e) 3) (equal? (nth e 1) (nth e 2))) 1)
        (else (map dl-fixdiff e))))
(define dl-zero-ok '(sign floor ceiling round))
(define (dl-build-dexpr h n k)
  (let* ((syms (map (lambda (i) (dl-sym (+ i 1))) (range n)))
         ; diff пишет шаг «differentiation diff» в журнал шагов — проверка не должна попадать в шаги интегрирования
         (d (try (if (step-log-enabled?)
                     (call-quietly (lambda () (diff (dl-sym (+ k 1)) (cons h syms))))
                     (diff (dl-sym (+ k 1)) (cons h syms)))
                 (lambda (err) #f)))
         (d (and d (dl-fixdiff d))))
    (cond ((not d) #f)
          ((dl-has-residue? d) #f)
          ((and (equal? d 0) (not (member? h dl-zero-ok))) #f)     ; diff молчит: «0» может значить «не реализовано»
          (else d))))
(define (dl-dexpr h n k)
  (let* ((key (list h n k)) (c (hash-ref dl-dcache key 'none)))
    (if (equal? c 'none)
        (let ((r (dl-build-dexpr h n k))) (hash-set! dl-dcache key r) r)
        c)))
(define (dl-partial h vs k)
  (let ((d (dl-dexpr h (length vs) k)))
    (if (not d)
        (dl-fail)
        (dl-num! h (subst (map2 (lambda (i v) (list (dl-sym (+ i 1)) (dn->expr v))) (range (length vs)) vs) d)))))

; ---------- дуальные числа (v . d) ----------
(define (dd+ a b) (cons (dn+ (car a) (car b)) (dn+ (cdr a) (cdr b))))
(define (dd* a b) (cons (dn* (car a) (car b)) (dn+ (dn* (cdr a) (car b)) (dn* (car a) (cdr b)))))
(define (dd-neg a) (dd* (cons -1.0 0.0) a))

; целая степень вещественного: возведением в квадрат (^ от float в диалекте не вычисляется)
(define (dl-ipow a n)
  (let* ((m (abs (floor n)))
         (r (let loop ((b a) (m m) (acc 1.0))
              (cond ((= m 0) acc)
                    ((odd? m) (loop (* b b) (quotient m 2) (* acc b)))
                    (else (loop (* b b) (quotient m 2) acc))))))
    (cond ((>= n 0) r)
          ((= r 0) (dl-fail))
          (else (/ 1.0 r)))))
; a^b для вещественных a, b без комплексной ветви: целый b, либо a > 0; иначе #f (считает eval-num)
(define (dl-pow-real a b)
  (cond ((= b (floor b)) (dl-ipow a b))
        ((> a 0) (exp (* b (log a))))
        (else #f)))
(define (dl-pow-val h a b)
  (or (and (not (pair? a)) (not (pair? b)) (dl-pow-real a b))
      (dl-num! h (list '^ (dn->expr a) (dn->expr b)))))
(define (dl-pow a b)
  (let ((av (car a)) (ad (cdr a)) (bv (car b)) (bd (cdr b)))
    (cond ((and (dn-zero? ad) (dn-zero? bd)) (cons (dl-pow-val '^ av bv) 0.0))
          ((dn-zero? bd)
           ; постоянный показатель: d = b·a^(b−1)·a′
           (let ((p1 (dl-pow-val '^ av (dn+ bv -1.0))))
             (cons (if (dn-zero? av) (dl-pow-val '^ av bv) (dn* av p1))
                   (dn* (dn* bv p1) ad))))
          (else
           ; u^v = e^(v·log u): d = u^v·(v′·log u + v·u′/u)
           (let* ((w (dl-pow-val '^ av bv))
                  (lg (dl-num! 'log (list 'log (dn->expr av)))))
             (cons w (dn* w (dn+ (dn* bd lg) (dn* bv (dn/ ad av))))))))))

(define (dl-abs a)
  (let* ((v (dl-num! 'abs (list 'abs (dn->expr (car a))))))
    (if (= v 0)
        (dl-fail)
        ; d|u|/dx = Re(conj(u)·u′)/|u|
        (cons v (/ (+ (* (dn-re (car a)) (dn-re (cdr a))) (* (dn-im (car a)) (dn-im (cdr a)))) v)))))

; быстрый путь для вещественного аргумента одноместной головы: (значение . h′(v)) | #f (вне области — считает общий путь)
(define (dl-fast h v)
  (cond ((equal? h 'exp) (let ((w (exp v))) (cons w w)))
        ((equal? h 'log) (and (> v 0) (cons (log v) (/ 1.0 v))))
        ((equal? h 'sin) (cons (sin v) (cos v)))
        ((equal? h 'cos) (cons (cos v) (- 0.0 (sin v))))
        ((equal? h 'tan) (let ((c (cos v))) (and (not (= c 0)) (cons (tan v) (/ 1.0 (* c c))))))
        ((equal? h 'atan) (cons (atan v) (/ 1.0 (+ 1.0 (* v v)))))
        ((equal? h 'sqrt) (and (> v 0) (let ((s (sqrt v))) (cons s (/ 0.5 s)))))
        ((equal? h 'sinh) (cons (sinh v) (cosh v)))
        ((equal? h 'cosh) (cons (cosh v) (sinh v)))
        ((equal? h 'tanh) (let ((c (cosh v))) (cons (tanh v) (/ 1.0 (* c c)))))
        (else #f)))

(define (dl-head h es x x0 env)
  (let* ((ds (map (lambda (a) (dl a x x0 env)) es))
         (vs (map car ds))
         (fast (and (= (length vs) 1) (not (pair? (car vs))) (dl-fast h (car vs)))))
    (if fast
        (cons (car fast) (if (dn-zero? (cdr (car ds))) 0.0 (dn* (cdr fast) (cdr (car ds)))))
        (let ((val (dl-num! h (cons h (map dn->expr vs)))))
          (cons val
                (let loop ((k 0) (ds ds) (acc 0.0))
                  (cond ((null? ds) acc)
                        ((dn-zero? (cdr (car ds))) (loop (+ k 1) (cdr ds) acc))
                        (else (loop (+ k 1) (cdr ds) (dn+ acc (dn* (dl-partial h vs k) (cdr (car ds)))))))))))))

(define (dl e x x0 env)
  (cond ((real-numeric? e) (cons (* 1.0 e) 0.0))
        ((symbol? e)
         (cond ((equal? e x) (cons x0 1.0))
               ((equal? e 'pi) (cons 3.141592653589793 0.0))
               ((equal? e '%i) (cons (cons 0.0 1.0) 0.0))
               (else (let ((p (assoc e env))) (if p (cons (cadr p) 0.0) (dl-fail))))))
        ((not (op-expr? e)) (dl-fail))
        (else
         (let ((h (car e)) (as (cdr e)))
           (cond ((equal? h '+) (foldl (lambda (acc a) (dd+ acc (dl a x x0 env))) (cons 0.0 0.0) as))
                 ((equal? h '*) (foldl (lambda (acc a) (dd* acc (dl a x x0 env))) (cons 1.0 0.0) as))
                 ((and (equal? h '-) (= (length as) 1)) (dd-neg (dl (car as) x x0 env)))
                 ((and (equal? h '-) (> (length as) 1))
                  (foldl (lambda (acc a) (dd+ acc (dd-neg (dl a x x0 env)))) (dl (car as) x x0 env) (cdr as)))
                 ((and (equal? h '/) (= (length as) 2)) (dl (list '* (car as) (list '^ (cadr as) -1)) x x0 env))
                 ((and (equal? h '^) (= (length as) 2)) (dl-pow (dl (car as) x x0 env) (dl (cadr as) x x0 env)))
                 ((and (equal? h 'abs) (= (length as) 1)) (dl-abs (dl (car as) x x0 env)))
                 ((and (equal? h 'sec) (= (length as) 1)) (dl (list '^ (list 'cos (car as)) -1) x x0 env))
                 ((and (equal? h 'csc) (= (length as) 1)) (dl (list '^ (list 'sin (car as)) -1) x x0 env))
                 ((and (equal? h 'cot) (= (length as) 1))
                  (dl (list '* (list 'cos (car as)) (list '^ (list 'sin (car as)) -1)) x x0 env))
                 ((member? h '(root-sum lambda let integrate diff sum product)) (dl-fail))
                 (else (dl-head h as x x0 env)))))))

; число из пользовательской записи (рациональное, float, (+ re (* im %i))) во внутреннее
(define (dl-input v) (let ((p (dn-parse v))) (if p p (dl-fail))))

(define (dual-eval-parts e x x0 env)
  (try (let* ((env2 (map (lambda (p) (list (car p) (dl-input (cadr p)))) env))
              (r (dl e x (dl-input x0) env2)))
         (and (dn-finite? (car r)) (dn-finite? (cdr r))
              (cons (cons (dn-re (car r)) (dn-im (car r))) (cons (dn-re (cdr r)) (dn-im (cdr r))))))
       (lambda (err) #f)))

(define (dual-eval e x x0 env)
  (let ((r (dual-eval-parts e x x0 env)))
    (and r
         (let ((cx (lambda (c) (if (= (cdr c) 0) (car c) (list '+ (car c) (list '* (cdr c) '%i))))))
           (cons (cx (car r)) (cx (cdr r)))))))
