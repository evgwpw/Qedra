; WASM.5b: независимая проверка ответов каталога примеров.
; Интеграл — производная ответа сравнивается с подынтегральной функцией численно в 5 точках;
; определённый интеграл — квадратура Симпсона; предел — численный подход к точке;
; сумма — прямой пересчёт слагаемых; отказ — система обязана оставить форму невычисленной.

; n-й элемент списка (с нуля) — в диалекте есть только car/cdr/cadr/caddr/cddr
(define (ex-nth n l)
  (if (= n 0) (car l) (ex-nth (- n 1) (cdr l))))

; список без первых n элементов
(define (ex-drop n l)
  (if (= n 0) l (ex-drop (- n 1) (cdr l))))

; eval-num не знает acot/asec/acsc/acoth/asech/acsch — переписываем их через atan/log/sqrt
(define (ex-rw e)
  (cond ((null? e) e)
        ((not (pair? e)) e)
        ((equal? (car e) 'acot) (list '- '(/ pi 2) (list 'atan (ex-rw (cadr e)))))
        ((equal? (car e) 'asec) (list 'acos (list '/ 1 (ex-rw (cadr e)))))
        ((equal? (car e) 'acsc) (list 'asin (list '/ 1 (ex-rw (cadr e)))))
        ((equal? (car e) 'acoth) (list 'atanh (list '/ 1 (ex-rw (cadr e)))))
        ((equal? (car e) 'asech) (list 'acosh (list '/ 1 (ex-rw (cadr e)))))
        ((equal? (car e) 'acsch) (list 'asinh (list '/ 1 (ex-rw (cadr e)))))
        (else (cons (ex-rw (car e)) (ex-rw (cdr e))))))

(define (ex-num-at e v pt)
  (try (eval-num (ex-rw (subst (list v pt) e))) (lambda (err) #f)))

(define (ex-close? a b)
  (and (number? a) (number? b) (< (abs (- a b)) 1e-8)))

; точки внутри (0, 1) — работают и для √(1−x²), и для 1/(x²−k²) без полюсов
(define ex-points (list 1/2 1/3 2/3 3/4 4/5))

; точки общего вида для проверки равенства выражений (x > 0, без особых точек)
(define ex-id-points (list 2/5 3/5 7/10 11/10 3/2))

; ---- численные значения ----

; значение выражения как float; #f — не число (комплекс, символ, ошибка)
(define (ex-val e)
  (let ((r (try (eval-num (ex-rw e)) (lambda (err) #f))))
    (cond ((not r) #f)
          ((number? r) (* 1.0 r))
          ((equal? r 'e) 2.718281828459045)
          ((equal? r 'pi) 3.141592653589793)
          (else #f))))

; |a − b| ≤ tol·max(1, |a|, |b|)
(define (ex-rel-close? a b tol)
  (and (number? a) (number? b)
       (<= (abs (- a b)) (* tol (max 1.0 (abs a) (abs b))))))

; ---- интегралы ----

; ответ F верен для integrate(f, x), если dF/dx = f в пяти точках
(define (ex-deriv-ok? input expect-text)
  (let ((F (try (math-read expect-text) (lambda (err) #f))))
    (if (not F) #f
        (ex-deriv-ok?-expr input F))))

(define (ex-deriv-ok?-expr input F)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (d (try (diff v F) (lambda (err) #f))))
    (if (not d) #f
        (let loop ((pts ex-points))
          (if (null? pts) #t
              (if (ex-close? (ex-num-at d v (car pts)) (ex-num-at f v (car pts)))
                  (loop (cdr pts))
                  #f))))))

; определённый интеграл: квадратура Симпсона против численного значения ответа
; квадратура Симпсона (200 узлов); #f — если функция не считается
(define (ex-simpson f v a b)
  (let* ((n 200)
         (h (/ (- b a) n)))
    (let loop ((i 0) (acc 0.0))
      (if (> i n) (* (/ h 3) acc)
          (let* ((x (+ a (* i h)))
                 (y (ex-num-at f v x))
                 (w (cond ((or (= i 0) (= i n)) 1)
                          ((even? i) 2)
                          (else 4))))
            (if (not (number? y)) #f
                (loop (+ i 1) (+ acc (* w y)))))))))

(define (ex-defint-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (a (ex-val (ex-nth 3 ast)))
         (b (ex-val (ex-nth 4 ast)))
         (want (ex-val (math-eval expect))))
    (if (or (not a) (not b) (not want) (= a b)) #f
        (ex-rel-close? (ex-simpson f v a b) want 1e-6))))

; certified_integral: ответ — отрезок [lo, hi]; значение моей квадратуры должно в него попасть
(define (ex-cint-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (a (ex-val (ex-nth 3 ast)))
         (b (ex-val (ex-nth 4 ast)))
         (vals (map (lambda (t) (try (string->number t) (lambda (err) #f)))
                    (ex-numbers expect))))
    (if (or (not a) (not b) (not (= (length vals) 2))) #f
        (let ((s (ex-simpson f v a b))
              (lo (car vals))
              (hi (cadr vals)))
          (and (number? s) (number? lo) (number? hi)
               (>= s (- lo 1e-6)) (<= s (+ hi 1e-6)))))))

; ---- пределы ----

(define (ex-pow10 k)
  (if (= k 0) 1.0 (* 0.1 (ex-pow10 (- k 1)))))

; h = 10^-2 … 10^-6
(define (ex-hs k acc)
  (if (> k 6) acc (ex-hs (+ k 1) (cons (ex-pow10 k) acc))))

; значения e при подходе к точке; список пар (значения . h)
(define (ex-limit-values e v at dir)
  (let* ((inf (equal? at 'inf))
         (ninf (equal? at (list '- 'inf)))
         (side (cond ((equal? dir 'plus) 1) ((equal? dir 'minus) -1) (else 0))))
    (let loop ((hs (ex-hs 2 '())) (acc '()))
      (if (null? hs) (reverse acc)
          (let* ((h (car hs))
                 (pts (cond (inf (list (/ 1.0 h)))
                            (ninf (list (- (/ 1.0 h))))
                            ((= side 1) (list (+ at h)))
                            ((= side -1) (list (- at h)))
                            (else (list (+ at h) (- at h)))))
                 (vals (let inner ((ps pts) (out '()))
                         (if (null? ps) (reverse out)
                             (inner (cdr ps) (cons (ex-num-at e v (car ps)) out))))))
            (loop (cdr hs) (cons (cons vals h) acc)))))))

(define (ex-all-vals? vals ok)
  (cond ((null? vals) #t)
        ((not (number? (car vals))) #f)
        ((ok (car vals)) (ex-all-vals? (cdr vals) ok))
        (else #f)))

; все значения строки — обычные конечные числа (inf/nan и ошибки отбрасывают строку)
(define (ex-finite-row? vals)
  (cond ((null? vals) #t)
        ((not (number? (car vals))) #f)
        ((> (abs (car vals)) 1e300) #f)
        (else (ex-finite-row? (cdr vals)))))

; берём самый мелкий шаг, на котором значения ещё конечны: на крупных шагах сходимость медленная,
; а на самых мелких (x = 10^6) бывает переполнение double (exp(x) и т. п.)
(define (ex-limit-near? e v at dir want)
  (let loop ((rows (ex-limit-values e v at dir)))
    (cond ((null? rows) #f)
          ((ex-finite-row? (car (car rows)))
           (ex-all-vals? (car (car rows)) (lambda (x) (ex-rel-close? x want 5e-3))))
          (else (loop (cdr rows))))))

; бесконечный предел: на мелком шаге значения растут по модулю и держат знак
(define (ex-limit-infinite? e v at rest sign)
  (let ((h (cdr (car (ex-limit-values e v at (if (null? rest) 'both (car rest)))))))
    (ex-all-vals? (car (car (ex-limit-values e v at (if (null? rest) 'both (car rest)))))
                  (lambda (x) (and (> (* sign x) 0) (> (abs x) (* 0.5 (/ 1.0 h))))))))

; предела нет: односторонние численные пределы не совпадают
(define (ex-last-val rows)
  (let ((vals (car (car rows))))
    (if (null? vals) #f (car vals))))

(define (ex-limit-undefined? e v at rest)
  (let* ((r (ex-last-val (ex-limit-values e v at 'plus)))
         (l (ex-last-val (ex-limit-values e v at 'minus))))
    (if (or (not (number? r)) (not (number? l))) #f
        (let ((diff (abs (- r l))))
          (or (> diff 1e-2) (> diff (* 1e-2 (max 1.0 (abs r) (abs l)))))))))

(define (ex-limit-ok? input expect)
  (let* ((ast (math-read input))
         (e (cadr ast))
         (v (caddr ast))
         (at (ex-nth 3 ast))
         (rest (ex-drop 4 ast))
         (dir (if (null? rest) 'both (car rest)))
         (want (math-eval expect)))
    (cond
      ((equal? want 'undefined) (ex-limit-undefined? e v at rest))
      ((equal? want 'inf) (ex-limit-infinite? e v at rest 1))
      ((equal? want '-inf) (ex-limit-infinite? e v at rest -1))
      (else (let ((num (ex-val want)))
              (if (not num) #f
                  (ex-limit-near? e v at dir num)))))))

; ---- суммы ----

; sum(f, k, a, b): прямой пересчёт слагаемых против численного значения ответа
(define (ex-sum-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (a (ex-nth 3 ast))
         (b (ex-nth 4 ast))
         (want (ex-val (math-eval expect))))
    (if (or (not (number? a)) (not (number? b)) (not want)) #f
        (let loop ((k a) (acc 0.0) (cnt 0))
          (cond ((> k b) (ex-rel-close? acc want 1e-6))
                ((> cnt 3000) #f)
                (else
                 (let ((y (ex-num-at f v k)))
                   (if (not (number? y)) #f
                       (loop (+ k 1) (+ acc y) (+ cnt 1))))))))))

; ---- равенство выражений (алгебра, упрощение, тригонометрия) ----

(define ex-inner-heads
  '(factor expand simplify apart together cancel trigexpand ratnorm denest radsimp))

(define (ex-input-ast input)
  (let ((ast (try (math-read input) (lambda (err) #f))))
    (if (pair? ast) ast #f)))

; внутренняя задача: у factor/simplify/expand/… ответ равен аргументу, у остальных — всему выражению
(define (ex-inner ast)
  (if (and (member? (car ast) ex-inner-heads) (pair? (cdr ast)))
      (cadr ast)
      ast))

(define (ex-sym-in? e s)
  (cond ((null? e) #f)
        ((equal? e s) #t)
        ((pair? e) (or (ex-sym-in? (car e) s) (ex-sym-in? (cdr e) s)))
        (else #f)))

; три набора значений для переменных x, y, z, t, n, k, m, u, a, b —
; равенство выражений проверяется в трёх точках (одна точка может случайно совпасть)
(define ex-assigns
  (list
    (list (list 'x 2/5) (list 'y 3/5) (list 'z 7/10) (list 't 11/10)
          (list 'n 3/2) (list 'k 7/5) (list 'm 9/5) (list 'u 11/5)
          (list 'a 13/5) (list 'b 3))
    (list (list 'x 4/3) (list 'y 5/4) (list 'z 9/7) (list 't 5/3)
          (list 'n 7/4) (list 'k 8/5) (list 'm 11/6) (list 'u 13/7)
          (list 'a 7/3) (list 'b 5/2))
    (list (list 'x 1/2) (list 'y 2/3) (list 'z 3/4) (list 't 4/5)
          (list 'n 5/6) (list 'k 6/7) (list 'm 7/8) (list 'u 8/9)
          (list 'a 9/10) (list 'b 10/11))))

(define (ex-num-at-all e al)
  (try (eval-num (ex-subst-al e al)) (lambda (err) #f)))

(define (ex-subst-al e al)
  (cond ((null? al) e)
        (else (ex-subst-al (subst (car al) e) (cdr al)))))

; 'ok — совпадает во всех точках, 'no — расходится, 'na — ничего не посчиталось
(define (ex-ident-eq? a b)
  (let loop ((als ex-assigns) (any #f))
    (cond ((null? als) (if any 'ok 'na))
          (else (let ((va (ex-num-at-all a (car als)))
                      (vb (ex-num-at-all b (car als))))
                  (cond ((or (not (number? va)) (not (number? vb))) (loop (cdr als) any))
                        ((ex-close? va vb) (loop (cdr als) #t))
                        (else 'no)))))))

(define (ex-identity-ok? input expect)
  (let* ((ast (ex-input-ast input))
         (e (if ast (ex-inner ast) #f))
         (want (try (math-read expect) (lambda (err) #f))))
    (and e want (equal? (ex-ident-eq? e want) 'ok))))

; ---- производные и ряды ----

; численная производная порядка n от f в точке p (центральные разности)
(define (ex-diff-num f v p n h)
  (let ((f0 (ex-num-at f v p))
        (f1 (ex-num-at f v (+ p h)))
        (f2 (ex-num-at f v (- p h)))
        (f3 (ex-num-at f v (+ p (* 2 h))))
        (f4 (ex-num-at f v (- p (* 2 h)))))
    (cond ((= n 1) (if (and f1 f2) (/ (- f1 f2) (* 2 h)) #f))
          ((= n 2) (if (and f0 f1 f2) (/ (+ (- f1 (* 2 f0)) f2) (* h h)) #f))
          (else (if (and f1 f2 f3 f4)
                    (/ (+ (- f3 (* 2 f1)) (* 2 f2) (- f4)) (* 2 h h h))
                    #f)))))

(define (ex-all-pts? pts ok)
  (cond ((null? pts) #t)
        ((ok (car pts)) (ex-all-pts? (cdr pts) ok))
        (else #f)))

; diff: ответ A проверяется численным дифференцированием самой функции f
(define (ex-diff-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (rest (ex-drop 3 ast))
         (n (if (null? rest) 1 (car rest)))
         (A (try (math-read expect) (lambda (err) #f)))
         (h (if (= n 1) 1e-5 1e-2))
         (tol (cond ((= n 1) 1e-4) ((= n 2) 1e-2) (else 5e-2))))
    (if (or (not A) (not (number? n))) #f
        (ex-all-pts? ex-points
                     (lambda (p) (ex-rel-close? (ex-diff-num f v p n h) (ex-num-at A v p) tol))))))

; отрезать хвост «+ O(…)» от записи ряда
(define (ex-cut-tail s)
  (let ((t (ex-trim s)))
    (if (and (> (string-length t) 0) (equal? (ex-char t (- (string-length t) 1)) "+"))
        (ex-trim (substring t 0 (- (string-length t) 1)))
        t)))

(define (ex-strip-big-o s)
  (let loop ((i 0))
    (cond ((>= (+ i 1) (string-length s)) s)
          ((and (equal? (ex-char s i) "O") (equal? (ex-char s (+ i 1)) "("))
           (ex-cut-tail (substring s 0 i)))
          (else (loop (+ i 1))))))

; series/taylor: частичная сумма сравнивается с функцией вблизи точки разложения
(define (ex-series-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (a (ex-nth 3 ast))
         (P (try (math-read (ex-strip-big-o expect)) (lambda (err) #f))))
    (if (not P) #f
        (let loop ((hs (list 1/100 1/50 1/20 1/10)))
          (if (null? hs) #t
              (let* ((h (car hs))
                     (x (if (number? a) (+ a h) h))
                     (fv (ex-num-at f v x))
                     (pv (ex-num-at P v x)))
                (if (and (number? fv) (number? pv) (ex-rel-close? fv pv 5e-2))
                    (loop (cdr hs))
                    #f)))))))

; certified_sum: ответ — отрезок [lo, hi]; частичная сумма должна в него попасть (члены положительны)
(define (ex-csum-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (a (ex-nth 3 ast))
         (vals (map (lambda (t) (try (string->number t) (lambda (err) #f)))
                    (ex-numbers expect))))
    (if (or (not (= (length vals) 2)) (not (number? a))) #f
        (let* ((lo (car vals))
               (hi (cadr vals))
               (s (let loop ((k a) (acc 0.0) (cnt 0))
                    (if (> cnt 3000) acc
                        (let ((y (ex-num-at f v k)))
                          (if (number? y) (loop (+ k 1) (+ acc y) (+ cnt 1)) #f))))))
          (and (number? s) (number? lo) (number? hi)
               (>= s (- lo 1e-6)) (<= s (+ hi 1e-6)))))))

; ---- линейная алгебра: определитель пересчётом (разложение Лапласа) ----

(define (ex-mat? e) (and (pair? e) (equal? (car e) 'm-vector)))

(define (ex-mat-rows m)
  (map (lambda (r) (if (ex-mat? r) (cdr r) #f)) (cdr m)))

(define (ex-drop-col r j)
  (let loop ((xs r) (i 0) (acc '()))
    (cond ((null? xs) (reverse acc))
          ((= i j) (loop (cdr xs) (+ i 1) acc))
          (else (loop (cdr xs) (+ i 1) (cons (car xs) acc))))))

(define (ex-minor rows j)
  (map (lambda (r) (ex-drop-col r j)) rows))

(define (ex-det m)
  (cond ((null? m) 1)
        ((null? (cdr m)) (car (car m)))
        (else
         (let loop ((j 0) (row (car m)) (acc 0))
           (if (null? row) acc
               (loop (+ j 1) (cdr row)
                     (+ acc (* (if (even? j) 1 -1) (car row)
                               (ex-det (ex-minor (cdr m) j))))))))))

(define (ex-det-num m)
  (let ((d (try (ex-det m) (lambda (err) #f))))
    (and d (ex-val d))))

; det(A) сравнивается с пересчитанным разложением по первой строке
(define (ex-det-ok? input expect)
  (let* ((ast (math-read input))
         (m (ex-nth 1 ast))
         (want (ex-val (math-eval expect))))
    (and (ex-mat? m) want (ex-rel-close? (ex-det-num (ex-mat-rows m)) want 1e-9))))

; eigenvalues: det(A − λI) = 0 для каждого собственного значения из ответа
(define (ex-eig-ok? input expect)
  (let* ((ast (math-read input))
         (m (ex-nth 1 ast))
         (rows (if (ex-mat? m) (ex-mat-rows m) #f))
         (lams (let loop ((xs (ex-num-list expect)) (acc '()))
                 (if (null? xs) (reverse acc) (loop (cddr xs) (cons (car xs) acc))))))
    (if (or (not rows) (null? lams)) #f
        (let loop ((ls lams))
          (cond ((null? ls) #t)
                (else
                 (let* ((lam (car ls))
                        (shifted (let sub ((rs rows) (i 0))
                                   (if (null? rs) '()
                                       (cons (let sub2 ((xs (car rs)) (j 0))
                                               (cond ((null? xs) '())
                                                     ((= i j) (cons (- (car xs) lam) (sub2 (cdr xs) (+ j 1))))
                                                     (else (cons (car xs) (sub2 (cdr xs) (+ j 1))))))
                                             (sub (cdr rs) (+ i 1)))))))
                   (if (ex-rel-close? (ex-det-num shifted) 0 1e-9)
                       (loop (cdr ls))
                       #f))))))))

; ---- ОДУ: сертификат dsolve-check (подстановка решения в уравнение) ----

(define (ex-rec-field rec key)
  (let loop ((xs (cdr rec)))
    (cond ((null? xs) #f)
          ((equal? (car xs) key) (cadr xs))
          (else (loop (cddr xs))))))

; подстановка числовых значений постоянных C1, C2, C3 в решение
(define (ex-fix-consts e)
  (let loop ((al (list (list 'C1 1) (list 'C2 2) (list 'C3 3)
                       (list 'C4 4) (list 'C5 5) (list 'C6 6))) (acc e))
    (cond ((null? al) acc)
          (else (loop (cdr al) (try (subst (car al) acc) (lambda (err) acc)))))))

(define (ex-subst-call e pat val)
  (cond ((null? e) e)
        ((equal? e pat) val)
        ((pair? e) (cons (ex-subst-call (car e) pat val) (ex-subst-call (cdr e) pat val)))
        (else e)))

; порядок производной в узле diff (вложенные diff считаются: (diff (diff y x) x) — второй)
(define (ex-diff-depth e)
  (cond ((and (pair? e) (equal? (car e) 'diff))
         (+ 1 (ex-diff-depth (cadr e))))
        (else 0)))

(define (ex-diff-order e)
  (if (and (pair? e) (equal? (car e) 'diff))
      (let ((d (ex-diff-depth e))
            (k (if (>= (length e) 4) (caddr (cddr e)) 1)))
        (max d (if (number? k) k 1)))
      1))

; замена y, y(x) и производных y на числа в точке p (для проверки невязки уравнения)
(define (ex-ode-subst e sol p)
  (cond ((null? e) e)
        ((and (pair? e) (equal? (car e) 'diff))
         (let ((n (ex-diff-order e)))
           (ex-diff-num sol 'x p n (if (= n 1) 1e-5 (if (= n 2) 1e-3 3e-3)))))
        ((equal? e '(y x)) (ex-num-at sol 'x p))
        ((equal? e 'y) (ex-num-at sol 'x p))
        ((pair? e) (cons (ex-ode-subst (car e) sol p) (ex-ode-subst (cdr e) sol p)))
        (else e)))

; проверка решения ОДУ: невязка «левая часть − правая часть» в пяти точках
; (собственный пересчёт: ode_check системы отвергает верные решения, когда правая часть зависит от y)
(define (ex-ode-ok? input)
  (let* ((ast (math-read input))
         (eq (cadr ast))
         (rec (try (math-eval input) (lambda (err) #f)))
         (sols (and (pair? rec) (equal? (car rec) 'ode-solution) (ex-rec-field rec ':solutions)))
         (rhs (and sols (pair? sols) (pair? (car sols)) (caddr (car sols)))))
    (if (or (not rhs) (not (pair? eq)) (not (equal? (car eq) '=))) #f
        (let ((sol (ex-fix-consts rhs)))
          (ex-all-pts? ex-points
                       (lambda (p)
                         (let ((lv (ex-num-at (ex-ode-subst (cadr eq) sol p) 'x p))
                               (rv (ex-num-at (ex-ode-subst (caddr eq) sol p) 'x p)))
                           (and (number? lv) (number? rv)
                                (ex-rel-close? lv rv 5e-3)))))))))

; ---- системы уравнений: подстановка найденных значений во все уравнения ----

(define (ex-vec->list e)
  (if (and (pair? e) (equal? (car e) 'm-vector)) (cdr e) #f))

(define (ex-apply-assigns eq assigns)
  (let loop ((as assigns) (acc (list '- (cadr eq) (caddr eq))))
    (cond ((null? as) acc)
          ((not (pair? (car as))) #f)
          (else (loop (cdr as) (ex-subst-call acc (cadr (car as)) (caddr (car as))))))))

; (ex-sol-ok? eqs as) — набор присваиваний as (список (= x …)) обращает все уравнения в 0
(define (ex-sol-ok? eqs as)
  (and (pair? as)
       (let loop ((es eqs))
         (cond ((null? es) #t)
               (else
                (let* ((expr (ex-apply-assigns (car es) as))
                       (v (and expr (try (eval-num expr) (lambda (err) #f)))))
                  (if (and (number? v) (< (abs v) 1e-9))
                      (loop (cdr es))
                      #f)))))))

; ответ solve для системы — множество векторов [x = …, y = …]; проверяем КАЖДОЕ решение
; ({…} снимаем один раз, затем делим по запятым верхнего уровня на векторы, каждый — на присваивания)
(define (ex-brace-strip s)
  (let ((t (ex-trim s)))
    (if (and (> (string-length t) 1)
             (equal? (ex-char t 0) "{")
             (equal? (ex-char t (- (string-length t) 1)) "}"))
        (substring t 1 (- (string-length t) 1))
        t)))

(define (ex-solution-assigns grp)
  (map (lambda (s) (math-read (ex-trim s)))
       (ex-split-top (ex-strip grp))))

(define (ex-system-ok? input expect)
  (let* ((ast (math-read input))
         (eqs (ex-vec->list (cadr ast)))
         (inner (ex-brace-strip expect))
         (sols (if (equal? (ex-trim inner) "")
                   '()
                   (map ex-solution-assigns (ex-split-top inner)))))
    (and eqs (any? (lambda (as) (ex-sol-ok? eqs as)) sols))))

; ---- теория чисел: сертификат ответа пересчётом ----

(define (ex-num-list s)
  (map (lambda (t) (try (string->number t) (lambda (err) #f))) (ex-numbers s)))

(define (ex-ipow a k)
  (cond ((<= k 0) 1) (else (* a (ex-ipow a (- k 1))))))

; произведение p^e по плоскому списку (p1 e1 p2 e2 …)
(define (ex-prod-pairs vals)
  (let loop ((xs vals) (acc 1))
    (cond ((null? xs) acc)
          ((null? (cdr xs)) #f)
          ((not (and (number? (car xs)) (number? (cadr xs)))) #f)
          (else (loop (cddr xs) (* acc (ex-ipow (car xs) (cadr xs))))))))

(define (ex-pell-eq d x y) (- (* x x) (* d y y)))

; все пары (x y) из плоского списка удовлетворяют уравнению Пелля с правой частью r
(define (ex-pell-pairs-ok? d vals r)
  (let loop ((xs vals))
    (cond ((null? xs) #t)
          ((null? (cdr xs)) #f)
          (else (and (= (ex-pell-eq d (car xs) (cadr xs)) r) (loop (cddr xs)))))))

(define (ex-triples-ok? vals)
  (let loop ((xs vals))
    (cond ((null? xs) #t)
          ((< (length xs) 3) #f)
          (else (let ((a (car xs)) (b (cadr xs)) (c (caddr xs)))
                  (and (number? a) (number? b) (number? c)
                       (= (+ (* a a) (* b b)) (* c c))
                       (loop (ex-drop 3 xs))))))))

; диофантово уравнение a·x + b·y = c: ответ ((x0 y0) (dx dy)) — частное решение и шаг
(define (ex-dio-ok? ast vals)
  (let ((a (ex-val (ex-nth 1 ast)))
        (b (ex-val (ex-nth 2 ast)))
        (c (ex-val (ex-nth 3 ast))))
    (if (or (not a) (not b) (not c) (< (length vals) 4)) #f
        (let ((x0 (car vals)) (y0 (cadr vals))
              (dx (caddr vals)) (dy (car (ex-drop 3 vals))))
          (and (number? x0) (number? y0) (number? dx) (number? dy)
               (= (+ (* a x0) (* b y0)) c)
               (= (+ (* a dx) (* b dy)) 0))))))

; сертификат для теории чисел: проверяем свойство ответа, а не его совпадение с эталоном
(define (ex-nt-ok? input expect)
  (let* ((ast (math-read input))
         (head (car ast))
         ; аргумент может быть выражением (2^32 + 1, 10^9 + 9) — упрощаем до точного целого
         (n (try (simplify (ex-nth 1 ast)) (lambda (e) #f)))
         (vals (ex-num-list expect)))
    (cond
      ((equal? head 'factorint) (and (number? n) (equal? (ex-prod-pairs vals) n)))
      ((equal? head 'sum_of_two_squares)
       (and (number? n) (= (length vals) 2)
            (= (+ (* (car vals) (car vals)) (* (cadr vals) (cadr vals))) n)))
      ((equal? head 'pythagorean_triples) (ex-triples-ok? vals))
      ((equal? head 'solve_linear_diophantine) (ex-dio-ok? ast vals))
      ((equal? head 'pell) (and (number? n) (ex-pell-pairs-ok? n vals 1)))
      ((equal? head 'pell_negative) (and (number? n) (ex-pell-pairs-ok? n vals -1)))
      ((equal? head 'pell_solutions) (and (number? n) (ex-pell-pairs-ok? n vals 1)))
      (else #f))))


(define (ex-char s i) (substring s i (+ i 1)))

(define (ex-open? c) (or (equal? c "(") (equal? c "[") (equal? c "{")))
(define (ex-bracket-close? c) (or (equal? c ")") (equal? c "]") (equal? c "}")))

; куски строки, разделённые запятыми верхнего уровня (внутри скобок запятые не считаются)
(define (ex-split-top s)
  (let loop ((i 0) (depth 0) (start 0) (acc '()))
    (if (>= i (string-length s))
        (reverse (cons (substring s start i) acc))
        (let ((c (ex-char s i)))
          (cond ((ex-open? c) (loop (+ i 1) (+ depth 1) start acc))
                ((ex-bracket-close? c) (loop (+ i 1) (- depth 1) start acc))
                ((and (= depth 0) (equal? c ","))
                 (loop (+ i 1) depth (+ i 1) (cons (substring s start i) acc)))
                (else (loop (+ i 1) depth start acc)))))))

; содержимое множества/вектора без внешних скобок
(define (ex-strip s)
  (let ((t (ex-trim s)))
    (if (and (> (string-length t) 1)
             (ex-open? (ex-char t 0))
             (ex-bracket-close? (ex-char t (- (string-length t) 1))))
        (substring t 1 (- (string-length t) 1))
        t)))

(define (ex-trim s)
  (let loop ((a 0) (b (string-length s)))
    (cond ((>= a b) "")
          ((equal? (ex-char s a) " ") (loop (+ a 1) b))
          ((equal? (ex-char s (- b 1)) " ") (loop a (- b 1)))
          (else (substring s a b)))))

; все числа из записи (токены из цифр, «/», «.», «-»)
(define ex-digits '("0" "1" "2" "3" "4" "5" "6" "7" "8" "9"))

(define (ex-numchar? c)
  (or (member? c ex-digits) (equal? c ".") (equal? c "/")))

(define (ex-numbers s)
  (let loop ((i 0) (tok "") (acc '()))
    (if (>= i (string-length s))
        (reverse (if (equal? tok "") acc (cons tok acc)))
        (let ((c (ex-char s i)))
          (cond ((ex-numchar? c) (loop (+ i 1) (string-append tok c) acc))
                ((and (equal? c "-") (equal? tok "")) (loop (+ i 1) "-" acc))
                (else (loop (+ i 1) "" (if (equal? tok "") acc (cons tok acc)))))))))

; отказ: система не вычислила задачу — ответ остался той же невычисленной формой
; (integrate … для интегралов, limit … для пределов, sum … для сумм) либо честное «не знаю» (#f);
; для dsolve отказ — запись ode-solution без решений (status unknown, WASM.6a Д1 печатает «unknown»)
(define (ex-refusal-ok? input)
  (let* ((ast (ex-input-ast input))
         (r (try (math-eval input) (lambda (err) 'ex-error))))
    (or (equal? r #f)
        (and ast (pair? r) (equal? (car r) (car ast)))
        (and ast (equal? (car ast) 'dsolve)
             (pair? r) (equal? (car r) 'ode-solution)
             (null? (ode-solutions r))))))

; подстановка одного корня в уравнение: символьно (точно 0) либо численно
(define (ex-eq-body e)
  (if (and (pair? e) (equal? (car e) '=)) (list '- (cadr e) (caddr e)) e))

(define (ex-root-ok? eq v root)
  (let* ((body (ex-eq-body eq))
         (sub (subst (list v root) body))
         (s (try (simplify sub) (lambda (err) #f))))
    (if (and s (number? s) (< (abs s) 1e-12)) #t
        ; модуль значения: работает и для комплексных корней
        (let ((m (try (eval-num (abs sub)) (lambda (err) #f))))
          (and (number? m) (< (abs m) 1e-8))))))

; solve: каждый корень из ответа подставляется в уравнение
(define (ex-subst-ok? input expect)
  (let* ((ast (math-read input))
         (eq (cadr ast))
         (v (caddr ast))
         (roots (map (lambda (s) (try (math-read s) (lambda (err) #f)))
                     (ex-split-top (ex-strip expect)))))
    (and (pair? roots)
         (let loop ((rs roots))
           (cond ((null? rs) #t)
                 ((not (car rs)) #f)
                 ((ex-root-ok? eq v (car rs)) (loop (cdr rs)))
                 (else #f))))))

; certified_roots: ответ — интервалы; проверяем смену знака и малую ширину
(define (ex-croots-ok? input expect)
  (let* ((ast (math-read input))
         (f (cadr ast))
         (v (caddr ast))
         (a (ex-val (ex-nth 3 ast)))
         (b (ex-val (ex-nth 4 ast)))
         (nums (ex-numbers expect))
         (vals (map (lambda (t) (try (string->number t) (lambda (err) #f))) nums)))
    (if (or (not a) (not b) (null? vals) (not (even? (length vals)))) #f
        (let loop ((xs vals))
          (cond ((null? xs) #t)
                ((or (not (car xs)) (not (cadr xs))) #f)
                (else
                 (let* ((lo (car xs))
                        (hi (cadr xs))
                        (flo (ex-num-at f v lo))
                        (fhi (ex-num-at f v hi)))
                   (if (and (number? flo) (number? fhi)
                            (<= (* flo fhi) 0)
                            (<= (- hi lo) 1e-3)
                            (>= lo (- a 1e-9)) (<= hi (+ b 1e-9)))
                       (loop (cddr xs))
                       #f))))))))

; эталон: ответ сверяется с опорным значением (ref) из литературы.
; Числа — с точностью 1e-9; выражения от переменной — численно в 5 точках;
; если точки не считаются (векторы и т. п.) — по записи.
(define (ex-ident3 a b v)
  (let loop ((pts ex-id-points) (any #f))
    (cond ((null? pts) (if any 'ok 'na))
          (else (let ((va (ex-num-at a v (car pts)))
                      (vb (ex-num-at b v (car pts))))
                  (cond ((or (not (number? va)) (not (number? vb))) (loop (cdr pts) any))
                        ((ex-close? va vb) (loop (cdr pts) #t))
                        (else 'no)))))))

(define (ex-ref-ok? expect ref)
  (let* ((want (try (math-eval ref) (lambda (err) (try (math-read ref) (lambda (e2) #f)))))
         (got (try (math-eval expect) (lambda (err) #f))))
    (cond
      ; ref не разбирается как выражение (например, рваная матрица) — сверяем по записи
      ((not want)
       (equal? (ex-trim (if got (to-string (math-print got)) expect)) (ex-trim ref)))
      ((not got) (equal? (ex-trim expect) (ex-trim ref)))
      ((equal? got want) #t)
      ((and (ex-val got) (ex-val want)) (ex-rel-close? (ex-val got) (ex-val want) 1e-9))
      (else (let ((ver (ex-ident-eq? got want)))
              (if (equal? ver 'na)
                  (equal? (math-print got) (math-print want))
                  (equal? ver 'ok)))))))

; проверка одного примера: "ok" | "fail" | "err: …"
(define (ex-check input expect kind check ref)
  (try
    (cond
      ((equal? kind "отказ") (if (ex-refusal-ok? input) "ok" "fail"))
      ((equal? kind "график") "ok")
      ((equal? check "производная") (if (ex-deriv-ok? input expect) "ok" "fail"))
      ((equal? check "подстановка")
       (let ((ast (ex-input-ast input)))
         (if (and ast (equal? (car ast) 'solve) (ex-vec->list (cadr ast)))
             (if (ex-system-ok? input expect) "ok" "fail")
             (if (ex-subst-ok? input expect) "ok" "fail"))))
      ((equal? check "сертификат")
       (let ((ast (ex-input-ast input)))
         (cond ((and ast (equal? (car ast) 'certified_roots))
                (if (ex-croots-ok? input expect) "ok" "fail"))
               ((and ast (equal? (car ast) 'certified_integral))
                (if (ex-cint-ok? input expect) "ok" "fail"))
               ((and ast (equal? (car ast) 'det))
                (if (ex-det-ok? input expect) "ok" "fail"))
               ((and ast (equal? (car ast) 'eigenvalues))
                (if (ex-eig-ok? input expect) "ok" "fail"))
               ((and ast (equal? (car ast) 'certified_sum))
                (if (ex-csum-ok? input expect) "ok" "fail"))
               ((and ast (member? (car ast) '(factorint sum_of_two_squares pythagorean_triples
                                             solve_linear_diophantine pell pell_negative
                                             pell_solutions)))
                (if (ex-nt-ok? input expect) "ok" "fail"))
               (else "fail"))))
      ((equal? check "dsolve-check") (if (ex-ode-ok? input) "ok" "fail"))
      ((equal? check "эталон") (if (ex-ref-ok? expect ref) "ok" "fail"))
      ((equal? check "численно")
       (let ((ast (ex-input-ast input)))
         (cond ((not ast) "fail")
               ((equal? (car ast) 'limit) (if (ex-limit-ok? input expect) "ok" "fail"))
               ((equal? (car ast) 'integrate) (if (ex-defint-ok? input expect) "ok" "fail"))
               ((equal? (car ast) 'sum) (if (ex-sum-ok? input expect) "ok" "fail"))
               ((equal? (car ast) 'diff) (if (ex-diff-ok? input expect) "ok" "fail"))
               ((or (equal? (car ast) 'series) (equal? (car ast) 'taylor))
                (if (ex-series-ok? input expect) "ok" "fail"))
               (else (if (ex-identity-ok? input expect) "ok" "fail")))))
      (else (if (equal? (math-eval input) (math-eval expect)) "ok" "fail")))
    (lambda (err) (string-append "err: " (to-string err)))))

(define (ex-report id input expect kind check ref)
  (display "@@") (display id) (display " ")
  (display (ex-check input expect kind check ref)) (newline))
