; laplace.lisp — преобразование Лапласа: прямое и обратное, правила, сертификат (шаг TR.1)
; Голова (heaviside u) — θ(u), (dirac u) — δ(u); неизвестная функция — (f t). Результат обратного преобразования — для t > 0.
; Внутренние имена с префиксом lt- (lp- занят линейным программированием).
(module laplace
  (export laplace inverse-laplace laplace-check convolve heaviside dirac
          laplace-dsolve laplace-dsolve-system laplace-volterra laplace-dsolve-check laplace-system-check
          transfer-function impulse-response step-response transfer-poles stable?))

; ---------- ступенька и дельта как данные ----------

; θ(x): число → 0 / 1 / 1/2 (в нуле), иначе (heaviside x)
(define (heaviside x)
  (let ((v (simplify x)))
    (cond ((number? v) (cond ((> v 0) 1) ((< v 0) 0) (else 1/2)))
          (else (list 'heaviside v)))))

; δ(x): ненулевое число → 0, иначе (dirac x)
(define (dirac x)
  (let ((v (simplify x)))
    (cond ((and (number? v) (not (= v 0))) 0)
          (else (list 'dirac v)))))

; ---------- вспомогательное ----------

(define (lt-free? e x) (not (contains-sym? e x)))
(define (lt-head? e h) (and (pair? e) (equal? (car e) h)))
(define (lt-factors e) (if (lt-head? e '*) (cdr e) (list e)))
(define (lt-try thunk) (try (thunk) (lambda (e) #f)))
(define (lt-has-int? e) (or (contains-sym? e 'integrate) (contains-sym? e 'limit)))
(define (lt-has-step? e) (or (contains-sym? e 'heaviside) (contains-sym? e 'dirac)))

(define (lt-find p l)
  (cond ((null? l) #f) ((p (car l)) (car l)) (else (lt-find p (cdr l)))))

(define (lt-remove x l)
  (cond ((null? l) '())
        ((equal? x (car l)) (cdr l))
        (else (cons (car l) (lt-remove x (cdr l))))))

; u = a·t + b (a, b без t) → (a . b), иначе #f
(define (lt-lin u t)
  (let ((v (expand u)))
    (if (polynomial? v t)
        (let ((cs (coefficients v t)))
          (cond ((null? cs) (cons 0 0))
                ((null? (cdr cs)) (cons 0 (car cs)))
                ((null? (cddr cs)) (cons (cadr cs) (car cs)))
                (else #f)))
        #f)))

(define (lt-nth-diff x e n)
  (if (<= n 0) e (lt-nth-diff x (simplify (diff x e)) (- n 1))))

; (heaviside число) → 0/1/1/2 внутри выражения
(define (lt-fix-steps e)
  (cond ((not (pair? e)) e)
        ((and (lt-head? e 'heaviside) (pair? (cdr e)) (number? (cadr e))) (heaviside (cadr e)))
        (else (cons (car e) (map lt-fix-steps (cdr e))))))

; неизвестная функция (h t)
(define lt-known-heads
  '(sin cos tan sinh cosh tanh exp log sqrt ^ * + - / heaviside dirac abs atan asin acos gamma erf
    diff integrate convolve laplace at root-sum))
(define (lt-unknown-call? f t)
  (and (pair? f) (symbol? (car f)) (not (member? (car f) lt-known-heads))
       (pair? (cdr f)) (null? (cddr f)) (equal? (cadr f) t)))

; значение функции g в нуле: (f t) → (f 0), производная — (at g (= t 0))
(define (lt-at0 g t)
  (cond ((lt-unknown-call? g t) (list (car g) 0))
        ((lt-head? g 'diff) (list 'at g (list '= t 0)))
        (else (simplify (subst (list t 0) g)))))

; sin/cos числа и выражений без плавающих хвостов ((cos 0) = 1, не 1.0)
(define (lt-neg-arg? a)
  (or (and (number? a) (< a 0))
      (and (lt-head? a '*) (number? (cadr a)) (< (cadr a) 0))))
(define (lt-sin x)
  (let ((v (simplify x)))
    (if (lt-neg-arg? v)
        (simplify (* -1 (lt-sin (simplify (* -1 v)))))
        (simplify (list 'sin v)))))
(define (lt-cos x)
  (let ((v (simplify x)))
    (if (lt-neg-arg? v)
        (lt-cos (simplify (* -1 v)))
        (simplify (list 'cos v)))))

; чётность sin/cos/sinh/cosh с отрицательным коэффициентом в аргументе
(define (lt-parity e)
  (cond ((not (pair? e)) e)
        ((and (member? (car e) '(sin sinh)) (pair? (cdr e)) (lt-neg-arg? (cadr e)))
         (simplify (* -1 (list (car e) (simplify (* -1 (lt-parity (cadr e))))))))
        ((and (member? (car e) '(cos cosh)) (pair? (cdr e)) (lt-neg-arg? (cadr e)))
         (simplify (list (car e) (simplify (* -1 (lt-parity (cadr e)))))))
        (else (simplify (cons (car e) (map lt-parity (cdr e)))))))
(define (lt-exp x) (simplify (list (quote exp) x)))

; Γ(x): целое — факториал, полуцелое — через π, иначе (gamma x)
(define (lt-gamma x)
  (cond ((and (integer? x) (> x 0)) (simplify (list 'gamma x)))
        ((and (number? x) (not (integer? x)) (= (denom x) 2))
         (lt-gamma-half x))
        (else (list 'gamma x))))

(define (lt-gamma-half x)
  (let ((half 1/2))
    (cond ((= x half) (^ 'pi 1/2))
          ((> x half) (simplify (* (- x 1) (lt-gamma-half (- x 1)))))
          (else (simplify (/ (lt-gamma-half (+ x 1)) x))))))

; ---------- произведения sin/cos → суммы ----------

(define (lt-trig? x t)
  (and (pair? x) (member? (car x) '(sin cos)) (pair? (cdr x)) (not (lt-free? x t))))

(define (lt-replicate n v) (if (<= n 0) '() (cons v (lt-replicate (- n 1) v))))

(define (lt-trig-flat fs t)
  (append-map
   (lambda (x)
     (if (and (lt-head? x '^) (lt-trig? (cadr x) t) (integer? (caddr x)) (>= (caddr x) 2) (<= (caddr x) 8))
         (lt-replicate (caddr x) (cadr x))
         (list x)))
   fs))

(define (lt-p2s a b)
  (let ((ha (car a)) (hb (car b)) (u (cadr a)) (v (cadr b)))
    (cond ((and (equal? ha 'sin) (equal? hb 'sin)) (* 1/2 (- (lt-cos (- u v)) (lt-cos (+ u v)))))
          ((and (equal? ha 'cos) (equal? hb 'cos)) (* 1/2 (+ (lt-cos (- u v)) (lt-cos (+ u v)))))
          ((and (equal? ha 'sin) (equal? hb 'cos)) (* 1/2 (+ (lt-sin (+ u v)) (lt-sin (- u v)))))
          (else (lt-p2s b a)))))

(define (lt-trig-term x t)
  (let* ((fs (lt-trig-flat (lt-factors x) t))
         (tr (filter (lambda (y) (lt-trig? y t)) fs)))
    (if (< (length tr) 2)
        x
        (let* ((a (car tr)) (b (cadr tr)) (rest (lt-remove b (lt-remove a fs))))
          (lt-trig-reduce (* (apply * rest) (lt-p2s a b)) t)))))

; expand и произведения тригонометрии → суммы кратных углов
(define (lt-trig-reduce e t)
  (let ((g (expand e)))
    (if (lt-head? g '+)
        (simplify (apply + (map (lambda (x) (lt-trig-term x t)) (cdr g))))
        (lt-trig-term g t))))

(define (lt-prep g t)
  (if (or (contains-sym? g 'sin) (contains-sym? g 'cos))
      (lt-trig-reduce g t)
      (expand g)))

; ---------- абсцисса сходимости и условия ----------

; коэффициенты a при t в множителях (exp (a t + b)) (без мнимых)
(define (lt-exps e t)
  (cond ((not (pair? e)) '())
        ((and (lt-head? e 'exp) (lt-lin (cadr e) t))
         (let ((a (car (lt-lin (cadr e) t)))) (if (contains-sym? a '%i) '() (list a))))
        (else (append-map (lambda (x) (lt-exps x t)) (cdr e)))))

(define (lt-note-cond s thr)
  (if (symbol? s)
      (record-condition (list '> s thr) "преобразование Лапласа сходится при Re s > абсциссы сходимости")
      #f))

; записать Re s > max(0, a…) и символические a
(define (lt-record-abscissa f t s)
  (let* ((as (lt-exps f t))
         (nums (filter number? as))
         (syms (filter (lambda (a) (not (number? a))) as))
         (sigma (foldl max 0 nums)))
    (lt-note-cond s sigma)
    (for-each (lambda (a) (lt-note-cond s a)) syms)
    #t))

; ---------- прямое преобразование: правила ----------

; L[f](s) или #f
(define (lt-L f t s)
  (let ((g (simplify f)))
    (cond ((lt-free? g t) (simplify (/ g s)))
          ((lt-head? g '+) (lt-L-sum (cdr g) t s))
          ((lt-has-step? g) (lt-L-term g t s))
          (else (let ((e (lt-prep g t)))
                  (if (lt-head? e '+) (lt-L-sum (cdr e) t s) (lt-L-term e t s)))))))

(define (lt-L-sum ts t s)
  (let loop ((l ts) (acc '()))
    (if (null? l)
        (let ((r (simplify (apply + acc))))
          (if (step-log-enabled?)
              (record-step 'lt-linearity "Линейность преобразования"
                           "L[f + g] = L[f] + L[g]" (apply + ts) r 'detail))
          r)
        (let ((r (lt-L (car l) t s)))
          (if r (loop (cdr l) (cons r acc)) #f)))))

(define (lt-L-term f t s)
  (let ((r (or (lt-L-rules f t s) (lt-direct f t s))))
    (if (and r (step-log-enabled?)) (lt-note-forward f t r))
    r))

; ---------- шаги (ST.3в-1) ----------
(define (lt-mp e) (try (math-print e) (lambda (err) (to-string e))))

; правило прямого преобразования по форме слагаемого (литеральные record-step —
; сканер словаря StepDict видит только их)
(define (lt-note-forward f t r)
  (let* ((fs (lt-factors f))
         (ex (lt-find (lambda (x) (and (lt-head? x 'exp) (lt-lin (cadr x) t))) fs))
         (hv (lt-find (lambda (x) (lt-head? x 'heaviside)) fs))
         (dr (lt-find (lambda (x) (lt-head? x 'dirac)) fs))
         (tp (lt-find (lambda (x) (let ((n (lt-tpow-of x t))) (and n (integer? n) (not (= n 0))))) fs)))
    (cond (ex (record-step 'lt-exp "Прямое преобразование: правило"
                           "сдвиг по частоте: L[e^{a t+b} g] = e^b G(s − a)" f r 'main))
          (hv (record-step 'lt-heaviside "Прямое преобразование: правило"
                           "запаздывание: L[θ(t−τ) g(t)] = e^{−τ s} L[g(t+τ)]" f r 'main))
          (dr (record-step 'lt-dirac "Прямое преобразование: правило"
                           "просеивание: g(t)·δ(a(t−τ)) = g(τ)·δ(t−τ)/|a|" f r 'main))
          (tp (record-step 'lt-tpow "Прямое преобразование: правило"
                           "умножение на t^n: L[t^n g] = (−1)^n d^n G/ds^n" f r 'main))
          (else (record-step 'lt-table "Прямое преобразование: правило"
                             "табличное значение (экспонента, тригонометрия, степень)" f r 'detail)))))

(define (lt-L-rules f t s)
  (let* ((fs (lt-factors f))
         (cs (filter (lambda (x) (lt-free? x t)) fs))
         (ds (filter (lambda (x) (not (lt-free? x t))) fs)))
    (if (not (null? cs))
        (let ((r (lt-L (apply * ds) t s)))
          (and r (simplify (* (apply * cs) r))))
        (lt-L-peel ds t s))))

(define (lt-L-peel ds t s)
  (let ((ex (lt-find (lambda (x) (and (lt-head? x 'exp) (lt-lin (cadr x) t))) ds))
        (hv (lt-find (lambda (x) (and (lt-head? x 'heaviside) (lt-lin (cadr x) t))) ds))
        (dr (lt-find (lambda (x) (lt-head? x 'dirac)) ds)))
    (cond (ex (lt-L-exp ex (lt-remove ex ds) t s))
          (hv (lt-L-heaviside hv (lt-remove hv ds) t s))
          (dr (lt-L-dirac dr (lt-remove dr ds) t s))
          (else (lt-L-rest ds t s)))))

; сдвиг по частоте: L[e^{at+b} g] = e^b G(s − a)
(define (lt-L-exp ex rest t s)
  (let* ((ab (lt-lin (cadr ex) t))
         (g (lt-L (apply * rest) t s)))
    (and g (simplify (* (lt-exp (cdr ab)) (subst (list s (- s (car ab))) g))))))

; запаздывание: L[θ(t−τ) g(t)] = e^{−τ s} L[g(t+τ)]
(define (lt-L-heaviside hv rest t s)
  (let* ((ab (lt-lin (cadr hv) t))
         (a (car ab))
         (tau (simplify (/ (- (cdr ab)) a))))
    (cond ((not (number? a)) #f)
          ((<= a 0) #f)
          ((and (number? tau) (<= tau 0)) (lt-L (apply * rest) t s))
          (else
           (begin
             (if (number? tau) #f (record-condition (list '>= tau 0) "запаздывание неотрицательно"))
             (let ((g (lt-L (simplify (subst (list t (+ t tau)) (apply * rest))) t s)))
               (and g (simplify (* (lt-exp (* -1 tau s)) g)))))))))

; просеивание: g(t) δ(a(t−τ)) = g(τ) δ(t−τ)/|a|
(define (lt-L-dirac dr rest t s)
  (let ((ab (lt-lin (cadr dr) t)))
    (cond ((not ab) #f)
          ((not (number? (car ab))) #f)
          ((= (car ab) 0) #f)
          (else
           (let* ((a (car ab))
                  (tau (simplify (/ (- (cdr ab)) a)))
                  (aa (if (< a 0) (- a) a)))
             (cond ((and (number? tau) (< tau 0)) 0)
                   ((contains-sym? tau t) #f)
                   (else
                    (let ((val (lt-fix-steps (simplify (subst (list t tau) (apply * rest))))))
                      (simplify (* val (lt-exp (* -1 tau s)) (/ 1 aa)))))))))))

; без exp, θ, δ: производная, интеграл, свёртка, степень t, таблица
(define (lt-L-rest ds t s)
  (cond ((null? ds) (simplify (/ 1 s)))
        ((null? (cdr ds)) (lt-L-single (car ds) t s))
        (else (lt-L-tpow ds t s))))

(define (lt-tpow-of x t)   ; показатель n, если x = t или t^n, иначе #f
  (cond ((equal? x t) 1)
        ((and (lt-head? x '^) (equal? (cadr x) t) (lt-free? (caddr x) t)) (caddr x))
        (else #f)))

; умножение на t^n: (−1)^n dⁿ/dsⁿ L[g]; деление на t: ∫_s^∞
(define (lt-L-tpow ds t s)
  (let ((tp (lt-find (lambda (x) (let ((n (lt-tpow-of x t))) (and n (integer? n) (not (= n 0))))) ds)))
    (if (not tp)
        #f
        (let* ((n (lt-tpow-of tp t))
               (g (lt-L (apply * (lt-remove tp ds)) t s)))
          (cond ((not g) #f)
                ((> n 0) (simplify (* (^ -1 n) (lt-nth-diff s g n))))
                ((= n -1) (lt-int-inf g s))
                (else #f))))))

; atan(∞) → π/2
(define (lt-fix-inf e)
  (cond ((not (pair? e)) e)
        ((and (lt-head? e 'atan) (equal? (cadr e) '∞)) (* 1/2 'pi))
        (else (simplify (cons (car e) (map lt-fix-inf (cdr e)))))))

; ∫_s^∞ G(σ) dσ
(define (lt-int-inf g s)
  (let* ((sg 'lt-sig)
         (gs (subst (list s sg) g))
         (a (lt-try (lambda () (integrate gs sg)))))
    (if (or (not a) (lt-has-int? a))
        #f
        (let ((lim (lt-try (lambda () (lt-fix-inf (limit a sg '∞))))))
          (if (or (not lim) (contains-sym? lim '∞) (lt-has-int? lim))
              #f
              (simplify (- lim (subst (list sg s) a))))))))

(define (lt-L-single x t s)
  (cond
    ((lt-unknown-call? x t) (list 'laplace x t s))
    ((lt-head? x 'diff)
     (if (and (= (length x) 3) (equal? (caddr x) t))
         (let ((g (lt-L (cadr x) t s)))
           (and g (simplify (- (* s g) (lt-at0 (cadr x) t)))))
         #f))
    ((and (lt-head? x 'integrate) (= (length x) 5) (equal? (list-ref-lt x 3) 0) (equal? (list-ref-lt x 4) t))
     (let ((g (lt-L (subst (list (caddr x) t) (cadr x)) t s)))
       (and g (simplify (/ g s)))))
    ((and (lt-head? x 'convolve) (= (length x) 4) (equal? (list-ref-lt x 3) t))
     (let ((a (lt-L (cadr x) t s)) (b (lt-L (caddr x) t s)))
       (and a b (simplify (* a b)))))
    ((lt-tpow-of x t)
     (let ((n (lt-tpow-of x t)))
       (cond ((and (number? n) (> n -1) (not (integer? n)))
              (simplify (* (lt-gamma (+ n 1)) (^ s (- (+ n 1))))))
             ((and (integer? n) (> n 0))
              (simplify (/ (lt-gamma (+ n 1)) (^ s (+ n 1)))))
             (else #f))))
    ((and (member? (car x) '(sin cos sinh cosh)) (pair? (cdr x)))
     (lt-L-trig x t s))
    (else #f)))

(define (list-ref-lt l i) (if (= i 0) (car l) (list-ref-lt (cdr l) (- i 1))))

; sin/cos(a t + b), sinh/cosh(a t) (с фазой — через экспоненты)
(define (lt-L-trig x t s)
  (let ((ab (lt-lin (cadr x) t)))
    (if (not ab)
        #f
        (let ((a (car ab)) (b (cdr ab)) (h (car x)))
          (cond
            ((equal? a 0) #f)
            ((equal? h 'sin)
             (simplify (/ (+ (* s (lt-sin b)) (* a (lt-cos b))) (+ (^ s 2) (^ a 2)))))
            ((equal? h 'cos)
             (simplify (/ (- (* s (lt-cos b)) (* a (lt-sin b))) (+ (^ s 2) (^ a 2)))))
            ((equal? b 0)
             (if (equal? h 'sinh)
                 (simplify (/ a (- (^ s 2) (^ a 2))))
                 (simplify (/ s (- (^ s 2) (^ a 2))))))
            (else
             (let* ((p (exp (+ (* a t) b))) (q (exp (- (+ (* a t) b)))))
               (lt-L (if (equal? h 'sinh) (* 1/2 (- p q)) (* 1/2 (+ p q))) t s))))))))

; ---------- прямое интегрирование (независимый путь) ----------

; знак коэффициента c в exp(c t) при больших s отрицателен?
(define (lt-neg-large? c s)
  (cond ((number? c) (< c 0))
        ((symbol? s)
         (let ((v (lt-try (lambda () (eval-num (subst (list s 1000000) c))))))
           (and v (number? v) (< v 0))))
        (else #f)))

; порог s > thr, при котором exp(c(s) t) убывает (c линейно по s)
(define (lt-threshold c s)
  (if (and (symbol? s) (polynomial? c s))
      (let ((cs (coefficients c s)))
        (if (and (= (length cs) 2) (< (cadr cs) 0))
            (simplify (/ (car cs) (- (cadr cs))))
            #f))
      #f))

; значение первообразной A при t → ∞: слагаемые с убывающим exp(c t) → 0; константы остаются; иначе #f
(define (lt-at-inf a t s)
  (let* ((e (expand a)) (ts (if (lt-head? e '+) (cdr e) (list e))))
    (let loop ((l ts) (acc 0))
      (cond ((null? l) (simplify acc))
            ((lt-free? (car l) t) (loop (cdr l) (+ acc (car l))))
            (else
             (let ((ex (lt-find (lambda (x) (and (lt-head? x 'exp) (lt-lin (cadr x) t)
                                                 (not (equal? (car (lt-lin (cadr x) t)) 0))))
                                (lt-factors (car l)))))
               (if (and ex (lt-neg-large? (car (lt-lin (cadr ex) t)) s))
                   (begin
                     (let ((thr (lt-threshold (car (lt-lin (cadr ex) t)) s)))
                       (if thr (lt-note-cond s thr) #f))
                     (loop (cdr l) acc))
                   #f)))))))

; ∫_lo^∞ g e^{−s t} dt
(define (lt-direct-int g lo t s)
  (let* ((ig (simplify (* g (lt-exp (* -1 s t)))))
         (a (integrate ig t)))
    (if (lt-has-int? a)
        #f
        (let ((inf (lt-at-inf a t s)))
          (and inf (simplify (- inf (simplify (subst (list t lo) a)))))))))

; один член: константы наружу, θ(t−τ) — нижний предел, δ — просеивание
(define (lt-direct-term f t s)
  (let* ((fs (lt-factors f))
         (cs (filter (lambda (x) (lt-free? x t)) fs))
         (ds (filter (lambda (x) (not (lt-free? x t))) fs))
         (dr (lt-find (lambda (x) (lt-head? x 'dirac)) ds))
         (hv (lt-find (lambda (x) (and (lt-head? x 'heaviside) (lt-lin (cadr x) t)
                                       (number? (car (lt-lin (cadr x) t))) (> (car (lt-lin (cadr x) t)) 0)))
                      ds)))
    (cond ((not (null? cs))
           (let ((r (lt-direct (apply * ds) t s))) (and r (simplify (* (apply * cs) r)))))
          (dr (lt-L-dirac dr (lt-remove dr ds) t s))
          (hv (let* ((ab (lt-lin (cadr hv) t)) (tau (simplify (/ (- (cdr ab)) (car ab)))))
                (if (and (number? tau) (>= tau 0))
                    (lt-direct-int (apply * (lt-remove hv ds)) tau t s)
                    #f)))
          (else (lt-direct-int (apply * ds) 0 t s)))))

(define (lt-direct1 f t s)
  (let ((g (lt-prep (simplify f) t)))
    (cond ((lt-free? g t) (simplify (/ g s)))
          ((lt-head? g '+)
           (let loop ((l (cdr g)) (acc '()))
             (if (null? l)
                 (simplify (apply + acc))
                 (let ((r (lt-direct-term (car l) t s)))
                   (if r (loop (cdr l) (cons r acc)) #f)))))
          (else (lt-direct-term g t s)))))

; ∫_0^∞ f e^{−s t} dt через integrate и хвост; #f, если не вышло
(define (lt-direct f t s)
  (lt-try (lambda () (lt-direct1 f t s))))

; ---------- обратное преобразование ----------

(define (lt-rational? f s)
  (and (polynomial? (numer f) s) (polynomial? (denom f) s)))

(define (lt-inv F s t)
  (let ((g (simplify F)))
    (cond ((lt-free? g s) (if (equal? g 0) 0 (simplify (* g (list 'dirac t)))))
          ((lt-rational? g s) (lt-inv-rat g s t))
          ((lt-head? g '+) (lt-inv-sum (cdr g) s t))
          (else (or (lt-inv-term g s t)
                    (let ((e (expand g)))
                      (and (lt-head? e '+) (lt-inv-sum (cdr e) s t))))))))

(define (lt-inv-sum ts s t)
  (let loop ((l ts) (acc '()))
    (if (null? l)
        (simplify (apply + acc))
        (let ((r (lt-inv (car l) s t)))
          (if r (loop (cdr l) (cons r acc)) #f)))))

; рациональная F: простейшие дроби над ℚ
(define (lt-inv-rat g s t)
  (let* ((a (simplify (apart g s)))
         (ts (if (lt-head? a '+) (cdr a) (list a))))
    (if (step-log-enabled?)
        (record-step 'lt-inv-partial "Разложение на простейшие дроби"
                     (string-append "знаменатель " (lt-mp (denom g)) "; полюса: "
                                    (lt-mp (try (solve (list '= (denom g) 0) s)
                                                (lambda (err) 'unknown)))
                                    "; коэффициенты — слагаемые разложения")
                     g a 'main))
    (let loop ((l ts) (acc '()))
      (if (null? l)
          (simplify (expand (apply + acc)))
          (let ((r (lt-inv-rat-term (car l) s t)))
            (if (and r (step-log-enabled?))
                (record-step 'lt-inv-term "Обратное преобразование слагаемого"
                             "табличное значение / вычет в полюсе" (car l) r 'detail))
            (if r (loop (cdr l) (cons r acc)) #f))))))

(define (lt-degree p s) (- (length (coefficients p s)) 1))

(define (lt-inv-rat-term term s t)
  (let ((n (numer term)) (d (denom term)))
    (if (lt-free? d s)
        (if (lt-free? n s) (simplify (* (/ n d) (list 'dirac t))) #f)
        (let ((fl (factor-list d)))
          (if (not (= (length fl) 2))
              #f
              (let* ((c (car fl)) (q (car (cadr fl))) (m (cadr (cadr fl))) (dg (lt-degree q s))
                     (qc (coefficients q s)))
                (cond ((= dg 1) (lt-inv-lin n c qc m s t))
                      ((= dg 2) (lt-inv-quad n c qc m s t))
                      ((and (>= dg 3) (= m 1) (< (lt-degree n s) dg))
                       (let ((e (simplify (/ n (* c (diff s q))))))
                         (list 'root-sum s q (list '* e (list 'exp (list '* s t))))))
                      (else #f))))))))

; N/(c (a s + b)^m), N без s
(define (lt-inv-lin n c qc m s t)
  (if (not (lt-free? n s))
      #f
      (let* ((b (car qc)) (a (cadr qc)) (rho (simplify (/ (- b) a))))
        (simplify (* (/ n (* c (^ a m))) (^ t (- m 1)) (/ 1 (lt-gamma m)) (lt-exp (* rho t)))))))

; (n1 s + n0)/(c a^k m^k), m = s² + p s + r
(define (lt-inv-quad n c qc m s t)
  (if (> (lt-degree n s) 1)
      #f
      (let* ((a (caddr qc)) (p (/ (cadr qc) a)) (r (/ (car qc) a))
             (h (/ p 2)) (w (- r (* h h)))
             (nc (coefficients n s))
             (n0 (if (null? nc) 0 (car nc)))
             (n1 (if (or (null? nc) (null? (cdr nc))) 0 (cadr nc)))
             (n2 (- n0 (* n1 h)))
             (ij (lt-IJ m w t)))
        (simplify (* (/ 1 (* c (^ a m))) (lt-exp (* -1 h t))
                     (+ (* n1 (cdr ij)) (* n2 (car ij))))))))

; I_k = L^-1[(u²+w)^-k], J_k = L^-1[u (u²+w)^-k] при u = s + h: (I . J)
(define (lt-IJ k w0 t)
  (let* ((w 'lt-w)
         (i1 (if (> w0 0)
                 (/ (sin (* (^ w 1/2) t)) (^ w 1/2))
                 (/ (sinh (* (^ (- w) 1/2) t)) (^ (- w) 1/2))))
         (j1 (if (> w0 0) (cos (* (^ w 1/2) t)) (cosh (* (^ (- w) 1/2) t)))))
    (let loop ((j 1) (i i1) (jj j1))
      (if (>= j k)
          (cons (simplify (expand (subst (list w w0) i))) (simplify (expand (subst (list w w0) jj))))
          (loop (+ j 1)
                (simplify (expand (* (/ -1 j) (diff w i))))
                (simplify (expand (* (/ -1 j) (diff w jj)))))))))

; нерациональная F: сдвиг по t (e^{−τ s}), константы, таблица, свёртка
(define (lt-inv-term g s t)
  (let* ((fs (lt-factors g))
         (cs (filter (lambda (x) (lt-free? x s)) fs))
         (ds (filter (lambda (x) (not (lt-free? x s))) fs))
         (ex (lt-find (lambda (x) (and (lt-head? x 'exp) (lt-lin (cadr x) s))) ds)))
    (cond
      ((not (null? cs))
       (let ((r (lt-inv (apply * ds) s t))) (and r (simplify (* (apply * cs) r)))))
      (ex
       (let* ((ab (lt-lin (cadr ex) s)) (a (car ab)))
         (if (or (and (number? a) (< a 0))
                 (let ((v (lt-try (lambda () (eval-num a))))) (and (number? v) (< v 0))))
             (let ((r (lt-inv (apply * (lt-remove ex ds)) s t)) (tau (- a)))
               (cond ((not r) #f)
                     ((contains-sym? r 'dirac)
                      (let ((c (simplify (/ r (list 'dirac t)))))
                        (and (lt-free? c t)
                             (simplify (* (lt-exp (cdr ab)) c (list 'dirac (- t tau)))))))
                     (else (simplify (* (lt-exp (cdr ab)) (list 'heaviside (- t tau))
                                        (subst (list t (- t tau)) r))))))
             #f)))
      ((null? (cdr ds)) (lt-inv-table (car ds) s t))
      (else (lt-inv-conv ds s t)))))

; степени (a s + b)^p, p < 0 нецелое; atan(a/s)
(define (lt-inv-table x s t)
  (cond
    ((and (lt-head? x '^) (lt-lin (cadr x) s) (number? (caddr x)) (< (caddr x) 0) (not (integer? (caddr x))))
     (let* ((ab (lt-lin (cadr x) s)) (al (car ab)) (h (/ (cdr ab) al)) (nu (- (caddr x))))
       (if (and (number? al) (> al 0))
           (simplify (* (^ al (- nu)) (lt-exp (* -1 h t)) (^ t (- nu 1)) (/ 1 (lt-gamma nu))))
           #f)))
    ((and (lt-head? x 'atan) (pair? (cdr x)))
     (let* ((u (simplify (cadr x)))
            (a (cond ((equal? u (^ s -1)) 1)
                     ((and (lt-head? u '*) (= (length u) 3) (equal? (caddr u) (^ s -1)) (lt-free? (cadr u) s)) (cadr u))
                     (else #f))))
       (and a (simplify (/ (sin (* a t)) t)))))
    (else #f)))

; произведение: F = F1 · F2 ↔ свёртка f1 * f2
(define (lt-inv-conv ds s t)
  (let* ((f1 (lt-inv (car ds) s t)))
    (and f1
         (let ((f2 (lt-inv (apply * (cdr ds)) s t)))
           (and f2 (convolve f1 f2 t))))))

; ---------- свёртка ----------

; подынтегральное выражение безопасно для integrate: степени u только целые неотрицательные
(define (lt-conv-safe? e u)
  (cond ((not (pair? e)) #t)
        ((and (lt-head? e '^) (contains-sym? (cadr e) u))
         (and (integer? (caddr e)) (>= (caddr e) 0) (lt-conv-safe? (cadr e) u)))
        (else (every? (lambda (x) (lt-conv-safe? x u)) (cdr e)))))

; (convolve f g t) = ∫_0^t f(τ) g(t−τ) dτ; не взялся интеграл — невычисленная форма
(define (convolve f g t)
  (let ((u 'lt-tau))
    (if (or (lt-has-step? f) (lt-has-step? g))
        (list 'convolve f g t)
        (let* ((e (simplify (* (subst (list t u) f) (subst (list t (- t u)) g))))
               (r (and (lt-conv-safe? e u) (lt-try (lambda () (integrate e u 0 t))))))
          (if (and r (not (lt-has-int? r)))
              (lt-parity (simplify r))
              (list 'convolve f g t))))))

; ---------- входные точки ----------

(define (laplace f t s)
  (let ((r (with-step ('lt-forward "Прямое преобразование Лапласа" (list 'laplace f t s))
              (lt-L f t s))))
    (if r
        (begin (lt-record-abscissa f t s) r)
        (list 'laplace f t s))))

(define (inverse-laplace F s t)
  (let ((r (with-step ('lt-inverse "Обратное преобразование Лапласа" (list 'inverse-laplace F s t))
              (lt-inv F s t))))
    (if r
        (begin
          (record-condition (list '> t 0) "обратное преобразование Лапласа: ответ для t > 0")
          ; проверка: прямое преобразование ответа равно F(s) (для рациональных F)
          (if (and (step-log-enabled?) (lt-rational? (simplify F) s))
              (let* ((chk (call-quietly (lambda () (lt-L r t s))))
                     (ok (and chk (lt-equal? chk F))))
                (record-step 'lt-inv-check "Проверка обратного преобразования"
                             (if ok "прямое преобразование ответа равно F(s): проверено"
                                 "прямое преобразование ответа не совпало: не проверено")
                             F r 'main)))
          r)
        (list 'inverse-laplace F s t))))

; ---------- сертификат ----------

(define (lt-equal? a b)
  (let ((d (lt-try (lambda () (simplify (together (- a b)))))))
    (and d (equal? d 0))))

; узлы и веса Гаусса–Лежандра, 5 точек на [−1, 1]
(define lt-gl-nodes '(-0.906179845938664 -0.5384693101056831 0.0 0.5384693101056831 0.906179845938664))
(define lt-gl-weights '(0.2369268850561891 0.4786286704993665 0.5688888888888889 0.4786286704993665 0.2369268850561891))

; значение f в точке t0 (ступеньки считаются)
(define (lt-ev f t t0)
  (eval-num (lt-fix-steps (subst (list t t0) f))))

; ∫_a^b h(t) dt составной формулой Гаусса–Лежандра (узлы внутри отрезка)
(define (lt-quad h a b)
  (let* ((n (max 1 (ceiling (/ (- b a) 0.25))))
         (w (/ (* 1.0 (- b a)) n)) (half (/ w 2)))
    (let loop ((i 0) (acc 0.0))
      (if (>= i n)
          acc
          (let ((mid (+ a (* w (+ i 0.5)))))
            (loop (+ i 1)
                  (+ acc (* half (foldl (lambda (sum p) (+ sum (* (car p) (h (+ mid (* half (cdr p)))))))
                                        0.0 (map2 cons lt-gl-weights lt-gl-nodes))))))))))

; точки разрыва θ(t − τ) в f
(define (lt-breaks f t)
  (cond ((not (pair? f)) '())
        ((and (lt-head? f 'heaviside) (lt-lin (cadr f) t))
         (let ((ab (lt-lin (cadr f) t)))
           (if (and (number? (car ab)) (not (= (car ab) 0)) (number? (cdr ab)))
               (list (/ (- (cdr ab)) (car ab)))
               '())))
        (else (append-map (lambda (x) (lt-breaks x t)) (cdr f)))))

; разбиение f на гладкую часть и члены с δ
(define (lt-split-dirac f t)
  (let* ((e (expand (simplify f))) (ts (if (lt-head? e '+) (cdr e) (list e))))
    (cons (filter (lambda (x) (not (contains-sym? x 'dirac))) ts)
          (filter (lambda (x) (contains-sym? x 'dirac)) ts))))

(define (lt-sort-nums l) (sort l <))

; численное значение L[f](s0): квадратура до T с хвостом e^{−(s0−σ)T} < e^{−40}; #f, если не вышло
(define (lt-num-L f t s0)
  (lt-try
   (lambda ()
     (let* ((sp (lt-split-dirac f t))
            (smooth (simplify (apply + (car sp))))
            (sigma (foldl max 0 (filter number? (lt-exps f t))))
            (tt (* 1.0 (/ 40 (- s0 sigma))))
            (bs (lt-sort-nums (filter (lambda (b) (and (> b 0) (< b tt))) (lt-breaks smooth t))))
            (pts (append (list 0) bs (list tt)))
            (h (lambda (x) (* (lt-ev smooth t x) (exp-num (* -1 s0 x)))))
            (q (let loop ((p pts) (acc 0.0))
                 (if (null? (cdr p)) acc (loop (cdr p) (+ acc (lt-quad h (car p) (cadr p)))))))
            (dsum (if (null? (cdr sp)) 0.0
                      (let ((v (lt-L-sum (cdr sp) t 's0-lt)))
                        (and v (eval-num (subst (list 's0-lt s0) v)))))))
       (and (number? q) dsum (+ q dsum))))))

(define (exp-num x) (eval-num (list 'exp x)))

(define (lt-close? a b) (<= (abs (- a b)) (* 0.000001 (+ 1.0 (abs b)))))

; (laplace-check f F t s) → #t (точно), numeric (в точках), #f (не равно), unknown (не удалось)
; (а) прямой интеграл ∫₀^∞ f e^{−st} dt через integrate и хвост; (в) правила прямого преобразования; (б) квадратура
(define (laplace-check f F t s)
  (let ((direct (lt-direct f t s)))
    (cond
      ((and direct (lt-equal? direct F)) #t)
      ((and (not direct) (let ((r (lt-L f t s))) (and r (not (lt-head? r 'laplace)) (lt-equal? r F)))) #t)
      (else (lt-check-numeric f F t s)))))

(define (lt-check-numeric f F t s)
  (let* ((sigma (foldl max 0 (filter number? (lt-exps f t))))
         (pts (list (+ sigma 2) (+ sigma 3) (+ sigma 5)))
         (res (map (lambda (s0)
                     (let ((q (lt-num-L f t s0))
                           (v (lt-try (lambda () (eval-num (subst (list s s0) F))))))
                       (if (and q v (number? q) (number? v)) (lt-close? q v) 'unknown)))
                   pts)))
    (cond ((member? #f res) #f)
          ((member? 'unknown res) 'unknown)
          (else 'numeric))))

; =====================================================================================
; Шаг TR.2: ОДУ, системы и интегральные уравнения методом Лапласа (префикс ld-)
; Постоянные коэффициенты: Σ a_k y⁽ᵏ⁾ = g(t). Недостающие условия — константы C1, C2, … :
; C1 = y(0), C2 = y′(0), …; у системы нумерация сквозная по (функция, производная).
; =====================================================================================

(define (ld-depth e y t)
  (cond ((equal? e (list y t)) 0)
        ((and (lt-head? e 'diff) (= (length e) 3) (equal? (caddr e) t))
         (let ((k (ld-depth (cadr e) y t))) (if k (+ k 1) #f)))
        (else #f)))

; узел неизвестной функции или её производной → (индекс . порядок)
(define (ld-hit e names t)
  (let loop ((ns names) (i 0))
    (if (null? ns)
        #f
        (let ((k (ld-depth e (car ns) t)))
          (if k (cons i k) (loop (cdr ns) (+ i 1)))))))

(define (ld-hits e names t)
  (let ((h (ld-hit e names t)))
    (cond (h (list h))
          ((pair? e) (append-map (lambda (z) (ld-hits z names t)) e))
          (else '()))))

(define (ld-dsym i k) (string->symbol (string-append "ld-D" (to-string i) "-" (to-string k))))

(define (ld-abstract e names t)
  (let ((h (ld-hit e names t)))
    (cond (h (ld-dsym (car h) (cdr h)))
          ((pair? e) (map (lambda (z) (ld-abstract z names t)) e))
          (else e))))

(define (ld-subst-nodes e names sols t)
  (let ((h (ld-hit e names t)))
    (cond (h (lt-nth-diff t (nth sols (car h)) (cdr h)))
          ((pair? e) (map (lambda (z) (ld-subst-nodes z names sols t)) e))
          (else e))))

(define (ld-norm-eq eq)
  (if (lt-head? eq '=) (simplify (list '- (cadr eq) (caddr eq))) (simplify eq)))

(define (ld-C n) (string->symbol (string-append "C" (to-string n))))

(define (ld-ord-of hits i)
  (foldl (lambda (acc h) (if (= (car h) i) (max acc (cdr h)) acc)) 0 hits))

(define (ld-sum l) (if (null? l) 0 (apply + l)))

; ---------- матрицы многочленов ----------

(define (ld-remove-nth l n)
  (if (= n 0) (cdr l) (cons (car l) (ld-remove-nth (cdr l) (- n 1)))))
(define (ld-minor M i j) (map (lambda (row) (ld-remove-nth row j)) (ld-remove-nth M i)))
(define (ld-sgn k) (if (= (modulo k 2) 0) 1 -1))

(define (ld-det M)
  (if (null? (cdr M))
      (expand (car (car M)))
      (expand (ld-sum (map (lambda (j) (* (ld-sgn j) (nth (car M) j) (ld-det (ld-minor M 0 j))))
                           (range (length M)))))))

; присоединённая матрица: adj[i][j] = (−1)^(i+j) det(минор j,i)
(define (ld-adj M)
  (let ((n (length M)))
    (if (= n 1)
        (list (list 1))
        (map (lambda (i)
               (map (lambda (j) (* (ld-sgn (+ i j)) (ld-det (ld-minor M j i)))) (range n)))
             (range n)))))

; ---------- разбор условий ----------

; (= (y 0) v) или (= (at (diff (y t) t) (= t 0)) v) → (i k v) или #f
(define (ld-parse-cond c names t)
  (if (not (and (lt-head? c '=) (= (length c) 3)))
      #f
      (let* ((lhs (cadr c)) (v (caddr c)))
        (cond ((and (pair? lhs) (= (length lhs) 2) (symbol? (car lhs)) (member? (car lhs) names)
                    (equal? (cadr lhs) 0))
               (list (ld-index (car lhs) names) 0 v))
              ((and (lt-head? lhs 'at) (= (length lhs) 3)
                    (lt-head? (caddr lhs) '=) (equal? (cadr (caddr lhs)) t) (equal? (caddr (caddr lhs)) 0))
               (let ((h (ld-hit (cadr lhs) names t)))
                 (if h (list (car h) (cdr h) v) #f)))
              (else #f)))))

(define (ld-index x l)
  (let loop ((l l) (i 0)) (if (equal? (car l) x) i (loop (cdr l) (+ i 1)))))

; ---------- разбор системы: порядки, коэффициенты, линейность ----------

; → (s Es ords coefs gs); coefs[j][i] = список a_k (k = 0 … ord_i) при y_i⁽ᵏ⁾ в j-м уравнении; gs[j] = −(член без y)
(define (ld-prep eqs names t)
  (let* ((m (length names))
         (s (if (any? (lambda (e) (contains-sym? e 's)) eqs) 'ld-s 's))
         (Es (map ld-norm-eq eqs))
         (hits (append-map (lambda (e) (ld-hits e names t)) Es))
         (ords (map (lambda (i) (ld-ord-of hits i)) (range m)))
         (all-d (append-map (lambda (i) (map (lambda (k) (cons i k)) (range (+ (nth ords i) 1)))) (range m)))
         (zero-rule (map (lambda (p) (list (ld-dsym (car p) (cdr p)) 0)) all-d)))
    (if (not (= (length eqs) m)) (error "число уравнений не равно числу неизвестных"))
    (if (every? (lambda (o) (= o 0)) ords) (error "в уравнении нет производных"))
    (let* ((abs-eqs (map (lambda (e) (ld-abstract e names t)) Es))
           (fs (map (lambda (e) (simplify (subst zero-rule e))) abs-eqs))
           (coefs (map2 (lambda (e f)
                          (map (lambda (i)
                                 (map (lambda (k)
                                        (let ((rule (map (lambda (p) (list (ld-dsym (car p) (cdr p))
                                                                           (if (equal? p (cons i k)) 1 0)))
                                                         all-d)))
                                          (simplify (- (subst rule e) f))))
                                      (range (+ (nth ords i) 1))))
                               (range m)))
                        abs-eqs fs)))
      ; линейность: E = f + Σ a·D
      (for-each (lambda (j)
                  (let ((recon (+ (nth fs j)
                                  (ld-sum (append-map
                                           (lambda (i) (map2 (lambda (a k) (* a (ld-dsym i k)))
                                                             (nth (nth coefs j) i) (range (+ (nth ords i) 1))))
                                           (range m))))))
                    (if (not (equal? (simplify (expand (- (nth abs-eqs j) recon))) 0))
                        (error "уравнение нелинейно по неизвестным"))))
                (range m))
      (if (any? (lambda (row) (any? (lambda (as) (any? (lambda (a) (contains-sym? a t)) as)) row)) coefs)
          (error "коэффициенты зависят от t (не постоянные)"))
      (if (any? (lambda (f) (any? (lambda (n) (contains-sym? f n)) names)) fs)
          (error "неизвестная функция вне производных (в точке, не в t)"))
      (list s Es ords coefs (map (lambda (f) (simplify (* -1 f))) fs)))))

; условия → ((i k v) …)
(define (ld-parse-conds conds names t ords)
  (let ((parsed (map (lambda (c) (ld-parse-cond c names t)) conds)))
    (if (any? (lambda (p) (not p)) parsed)
        (error "не распознано условие (нужно (= (y 0) v) или (= (at (diff (y t) t) (= t 0)) v))"))
    (for-each (lambda (p)
                (if (>= (cadr p) (nth ords (car p)))
                    (error "условие на производную не ниже порядка уравнения")))
              parsed)
    parsed))

(define (ld-given parsed key)
  (let ((hit (lt-find (lambda (p) (and (= (car p) (car key)) (= (cadr p) (cdr key)))) (reverse parsed))))
    (if hit (caddr hit) #f)))

(define (ld-init-keys ords)
  (append-map (lambda (i) (map (lambda (k) (cons i k)) (range (nth ords i)))) (range (length ords))))

; ---------- ядро: преобразование, алгебра по s, обратное преобразование ----------

; → (ok sols consts expected ords coefs gs Es) или ошибка с причиной
(define (ld-engine eqs names t conds)
  (let* ((m (length names))
         (pr (ld-prep eqs names t))
         (s (nth pr 0)) (Es (nth pr 1)) (ords (nth pr 2)) (coefs (nth pr 3)) (gs (nth pr 4))
         (parsed (ld-parse-conds conds names t ords))
         (M (map (lambda (j)
                   (map (lambda (i)
                          (expand (ld-sum (map2 (lambda (a k) (* a (^ s k)))
                                                (nth (nth coefs j) i) (range (+ (nth ords i) 1))))))
                        (range m)))
                 (range m)))
         (det (ld-det M)))
    (if (equal? det 0) (error "вырожденная система (определитель по s равен нулю)"))
    (let* ((adj (ld-adj M))
           (Lgs (map (lambda (g) (if (equal? g 0) 0 (laplace g t s))) gs)))
      (if (any? (lambda (L) (contains-sym? L 'laplace)) Lgs)
          (error "правая часть не имеет известного образа Лапласа"))
      (let* ((inv (lambda (F)
                    (let ((r (inverse-laplace (simplify F) s t)))
                      (if (contains-sym? r 'inverse-laplace)
                          (error "обратное преобразование не вычислено")
                          r))))
             (terms-of (lambda (L) (cond ((equal? L 0) '()) ((lt-head? L '+) (cdr L)) (else (list L)))))
             ; вынужденная часть
             (xp (map (lambda (i)
                        (ld-sum
                         (map (lambda (j)
                                (let ((a (nth (nth adj i) j)))
                                  (if (equal? a 0) 0
                                      (ld-sum (map (lambda (term) (inv (list '/ (* a term) det)))
                                                   (terms-of (nth Lgs j)))))))
                              (range m))))
                      (range m)))
             (init-keys (ld-init-keys ords))
             (cnum (let loop ((ks init-keys) (n 1) (acc '()))
                     (if (null? ks) (reverse acc) (loop (cdr ks) (+ n 1) (cons (cons (car ks) n) acc)))))
             (value (lambda (key)
                      (let ((v (ld-given parsed key)))
                        (if v v (ld-C (cdr (assoc key cnum)))))))
             ; вклад константы y_{i',k'}: Σ_j adj_ij q_{j,i',k'} / det
             (homog (lambda (i key)
                      (let* ((ip (car key)) (kp (cdr key))
                             (num (expand (ld-sum
                                           (map (lambda (j)
                                                  (* (nth (nth adj i) j)
                                                     (ld-sum (map (lambda (k) (* (nth (nth (nth coefs j) ip) k)
                                                                                 (^ s (- k 1 kp))))
                                                                  (filter (lambda (k) (> k kp)) (range (+ (nth ords ip) 1)))))))
                                                (range m))))))
                        (if (equal? num 0) 0 (inv (list '/ num det))))))
             (sols (map (lambda (i)
                          (simplify
                           (+ (nth xp i)
                              (ld-sum (map (lambda (key) (* (value key) (homog i key))) init-keys)))))
                        (range m)))
             (consts (filter (lambda (c) (any? (lambda (x) (contains-sym? x c)) sols))
                             (map (lambda (p) (ld-C (cdr p))) cnum)))
             (expected (map (lambda (i) (map (lambda (k) (value (cons i k))) (range (nth ords i)))) (range m))))
        (list 'ok sols consts expected ords coefs gs Es)))))

; проверка готового решения без вывода: (ok sols consts expected ords coefs gs Es); недостающее условие — 'none
(define (ld-engine-check eqs names t sols conds)
  (let* ((pr (ld-prep eqs names t))
         (ords (nth pr 2))
         (parsed (ld-parse-conds conds names t ords))
         (expected (map (lambda (i)
                          (map (lambda (k) (let ((v (ld-given parsed (cons i k)))) (if v v 'none)))
                               (range (nth ords i))))
                        (range (length names)))))
    (list 'ok sols '() expected ords (nth pr 3) (nth pr 4) (nth pr 1))))

; ---------- сертификат: по интервалам между точками переключения θ/δ ----------

; заморозить ступеньки в точке p: θ → 0/1, δ → 0
(define (ld-freeze e t p)
  (cond ((not (pair? e)) e)
        ((and (lt-head? e 'heaviside) (pair? (cdr e)))
         (if (> (eval-num (subst (list t p) (cadr e))) 0) 1 0))
        ((lt-head? e 'dirac) 0)
        (else (map (lambda (z) (ld-freeze z t p)) e))))

(define (ld-step-nodes e)
  (cond ((not (pair? e)) '())
        ((or (lt-head? e 'heaviside) (lt-head? e 'dirac)) (list e))
        (else (append-map ld-step-nodes e))))

; точки переключения t > 0: ((точное . число) …) по возрастанию, и признак «всё разобрано»
(define (ld-breaks Es t)
  (let loop ((nodes (append-map ld-step-nodes Es)) (acc '()) (ok #t))
    (if (null? nodes)
        (cons (sort acc (lambda (x y) (< (cdr x) (cdr y)))) ok)
        (let* ((nd (car nodes)) (ab (lt-lin (cadr nd) t)))
          (cond ((not ab) (loop (cdr nodes) acc #f))
                ((equal? (car ab) 0) (loop (cdr nodes) acc ok))
                ((not (number? (car ab))) (loop (cdr nodes) acc #f))
                (else
                 (let* ((pt (simplify (/ (* -1 (cdr ab)) (car ab))))
                        (num (lt-try (lambda () (eval-num pt)))))
                   (cond ((not (number? num)) (loop (cdr nodes) acc #f))
                         ((> num 0)
                          (loop (cdr nodes)
                                (if (any? (lambda (b) (equal? (car b) pt)) acc) acc (cons (cons pt num) acc))
                                ok))
                         ((lt-head? nd 'dirac) (loop (cdr nodes) acc #f))
                         (else (loop (cdr nodes) acc ok))))))))))

(define (ld-samples nums)
  (if (null? nums)
      (list 1.0)
      (cons (/ (car nums) 2.0)
            (let loop ((l nums))
              (if (null? (cdr l))
                  (list (+ (car l) 1.0))
                  (cons (/ (+ (car l) (cadr l)) 2.0) (loop (cdr l))))))))

(define (ld-combine rs)
  (cond ((member? #f rs) #f) ((member? 'unknown rs) 'unknown) ((member? 'numeric rs) 'numeric) (else #t)))

; остаток res (выражение от t) — ноль? #t | numeric | #f | unknown
(define (ld-zero-check res t)
  (let ((z (lt-try (lambda () (simplify (together res))))))
    (cond ((not z) 'unknown)
          ((or (equal? z 0) (equal? z 0.0)) #t)
          ((ode::ode-surely-nonzero? z) #f)
          ((ode::ode-numeric-zero? res t) 'numeric)
          (else #f))))

(define (ld-eq-check ef names sols t)
  (if (null? (cdr names))
      (let ((r (lt-try (lambda () (dsolve-check ef (list '= (list (car names) t) (car sols)) (list (car names) t))))))
        (if (equal? r 'numeric) 'numeric (if (equal? r #t) #t (if r 'unknown #f))))
      (ld-zero-check (simplify (ld-subst-nodes ef names sols t)) t)))

; сравнение точное, иначе численное
(define (ld-same a b)
  (cond ((lt-equal? a b) #t)
        (else (let ((x (lt-try (lambda () (eval-num a)))) (y (lt-try (lambda () (eval-num b)))))
                (if (and (number? x) (number? y) (lt-close? x y)) 'numeric #f)))))

; сила δ(t − b) в g: Σ g_k(b)/|α|
(define (ld-dirac-strength g t b)
  (let* ((e (expand (simplify g))) (ts (if (lt-head? e '+) (cdr e) (list e))))
    (simplify
     (ld-sum
      (map (lambda (term)
             (if (not (contains-sym? term 'dirac))
                 0
                 (let* ((fs (lt-factors term))
                        (dr (lt-find (lambda (f) (lt-head? f 'dirac)) fs)))
                   (if (not dr) (error "δ не множитель"))
                   (let* ((rest (apply * (lt-remove dr fs))) (ab (lt-lin (cadr dr) t)))
                     (if (or (not ab) (not (number? (car ab))) (equal? (car ab) 0)) (error "δ не линейна по t"))
                     (if (equal? (simplify (/ (* -1 (cdr ab)) (car ab))) b)
                         (/ (subst (list t b) rest) (if (< (car ab) 0) (- (car ab)) (car ab)))
                         0)))))
           ts)))))

(define (ld-certify Es names t sols ords expected coefs gs)
  (let* ((br (ld-breaks Es t)) (bs (car br)) (m (length names)))
    (if (not (cdr br))
        'unknown
        (let* ((samples (ld-samples (map cdr bs)))
               (fsols (map (lambda (p) (map (lambda (x) (ld-freeze x t p)) sols)) samples))
               (eq-res (append-map
                        (lambda (r)
                          (map (lambda (e) (ld-eq-check (ld-freeze e t (nth samples r)) names (nth fsols r) t)) Es))
                        (range (length samples))))
               (init-res
                (append-map
                 (lambda (i)
                   (map (lambda (k)
                          (if (equal? (nth (nth expected i) k) 'none)
                              #t
                              (ld-same (simplify (subst (list t 0) (lt-nth-diff t (nth (car fsols) i) k)))
                                       (nth (nth expected i) k))))
                        (range (nth ords i))))
                 (range m)))
               (jump-res
                (append-map
                 (lambda (r)
                   (let* ((b (car (nth bs (- r 1))))
                          (cs (map (lambda (g) (ld-dirac-strength g t b)) gs))
                          (left (nth fsols (- r 1))) (right (nth fsols r))
                          (A (map (lambda (j) (map (lambda (i) (last (nth (nth coefs j) i))) (range m))) (range m)))
                          (jumps
                           (if (every? (lambda (c) (equal? c 0)) cs)
                               (map (lambda (i) 0) (range m))
                               (let ((d (ld-det A)))
                                 (if (equal? d 0)
                                     (error "δ-сила: вырожденная старшая матрица")
                                     (let ((adj (ld-adj A)))
                                       (map (lambda (i)
                                              (simplify (/ (ld-sum (map (lambda (j) (* (nth (nth adj i) j) (nth cs j))) (range m))) d)))
                                            (range m))))))))
                     (append-map
                      (lambda (i)
                        (map (lambda (k)
                               (ld-same (simplify (- (subst (list t b) (lt-nth-diff t (nth right i) k))
                                                     (subst (list t b) (lt-nth-diff t (nth left i) k))))
                                        (if (= k (- (nth ords i) 1)) (nth jumps i) 0)))
                             (range (nth ords i))))
                      (range m))))
                 (map (lambda (r) (+ r 1)) (range (length bs))))))
          (ld-combine (append eq-res init-res jump-res))))))

; ---------- входные точки ----------

(define (ld-run eqs names t conds)
  (let* ((cs (if (lt-head? conds '=) (list conds) conds))
         ; внутренние шаги laplace/inverse-laplace не дублируются (как alg-run): в журнал идут ld-*
         (r (try (if (step-log-enabled?)
                     (call-quietly (lambda () (ld-engine eqs names t cs)))
                     (ld-engine eqs names t cs))
                 (lambda (e) (list 'fail (if (error? e) (error-message e) "ошибка"))))))
    (if (equal? (car r) 'fail)
        (ode-solution 'general '() '() (string-append "laplace: " (to-string (cadr r))) 'unknown 'laplace 'none)
        (let* ((sols (nth r 1)) (consts (nth r 2))
               (chk (try (ld-certify (nth r 7) names t sols (nth r 4) (nth r 3) (nth r 5) (nth r 6))
                         (lambda (e) 'unknown)))
               (eqs-out (map2 (lambda (n s) (list '= (list n t) s)) names sols)))
          (if (step-log-enabled?)
              (let* ((sv (if (any? (lambda (e) (contains-sym? e 's)) eqs) 'ld-s 's))
                     (ys (map (lambda (sol)
                                (let ((v (call-quietly (lambda () (lt-L sol t sv)))))
                                  (if v v 'unknown)))
                              sols)))
                (record-step 'ld-transform "Преобразованное уравнение"
                             "L переводит дифференциальное уравнение в алгебраическое по s"
                             eqs (nth r 7) 'main)
                (record-step 'ld-initial "Начальные условия"
                             "значения y и её производных в нуле подставлены в изображение"
                             cs (nth r 4) 'main)
                (record-step 'ld-ys "Изображение Y(s)"
                             (string-append "решение алгебраической системы относительно Y(" (to-string sv) ")")
                             (nth r 7) ys 'main)
                (record-step 'ld-inverse "Обратное преобразование"
                             "Y(s) → y(t): таблица и простейшие дроби"
                             ys eqs-out 'main)
                (record-step 'ld-check "Проверка подстановкой"
                             (cond ((equal? chk #t) "решение подставлено в уравнение: тождество проверено")
                                   ((equal? chk 'numeric) "решение проверено численно в точках")
                                   (else "проверка не выполнена: остаток не свёлся"))
                             eqs eqs-out 'main)))
          (cond ((or (equal? chk #t) (equal? chk 'numeric))
                 (ode-solution (if (null? consts) 'particular 'general) eqs-out consts '() 'ok 'laplace chk))
                ((equal? chk #f)
                 (ode-solution 'general '() '() "решение не прошло проверку" 'unknown 'laplace #f))
                (else
                 (ode-solution (if (null? consts) 'particular 'general) eqs-out consts '() 'unchecked 'laplace 'unknown)))))))

(define (ld-rhs s) (if (and (pair? s) (equal? (car s) '=)) (caddr s) s))

; сертификат готового решения: #t | numeric | #f | unknown; условия без значения в проверке пропускаются
(define (ld-check-run eqs names t sols conds)
  (let* ((cs (if (lt-head? conds '=) (list conds) conds))
         (r (try (ld-engine-check eqs names t (map ld-rhs sols) cs) (lambda (e) #f))))
    (if (not r)
        'unknown
        (try (ld-certify (nth r 7) names t (nth r 1) (nth r 4) (nth r 3) (nth r 5) (nth r 6))
             (lambda (e) 'unknown)))))

; (laplace-dsolve-check eq (y t) sol conds) — sol: (= (y t) выражение) или выражение
(define (laplace-dsolve-check eq yt sol conds)
  (ld-check-run (list eq) (list (car yt)) (cadr yt) (list sol) conds))

; (laplace-system-check eqs funcs t sols conds)
(define (laplace-system-check eqs funcs t sols conds)
  (ld-check-run eqs (map (lambda (f) (if (pair? f) (car f) f)) funcs) t sols conds))

; (laplace-dsolve eq (y t) conds) — линейное ОДУ с постоянными коэффициентами; conds — список условий в t = 0
(define (laplace-dsolve eq yt conds)
  (with-step ('ld-solve "Решение ОДУ преобразованием Лапласа" eq
                        :after (lambda (r) (try (ode-solutions r) (lambda (e) r))))
    (ld-run (list eq) (list (car yt)) (cadr yt) conds)))

; (laplace-dsolve-system eqs funcs t conds) — funcs: имена (x y) или вызовы ((x t) (y t))
(define (laplace-dsolve-system eqs funcs t conds)
  (ld-run eqs (map (lambda (f) (if (pair? f) (car f) f)) funcs) t conds))

; ---------- интегральные уравнения типа свёртки (Вольтерра) ----------
; a·y(t) + Σ λᵢ ∫₀ᵗ kᵢ(t−τ) y(τ) dτ = f(t) (второго рода a ≠ 0, первого a = 0). Интеграл — (integrate h tau 0 t)
; или (convolve k (y t) t). Образ: (a + Σ λᵢ Kᵢ(s)) Y = F(s).

; разбор: список элементов (y c) | (int c ядро-от-lt-u) | (free выражение)
(define (ld-vflat e c y t)
  (cond
    ((lt-head? e '+) (append-map (lambda (z) (ld-vflat z c y t)) (cdr e)))
    ((and (lt-head? e '-) (= (length e) 2)) (ld-vflat (cadr e) (* -1 c) y t))
    ((lt-head? e '-)
     (append (ld-vflat (cadr e) c y t)
             (append-map (lambda (z) (ld-vflat z (* -1 c) y t)) (cddr e))))
    ((lt-head? e '*)
     (let ((act (filter (lambda (z) (contains-sym? z y)) (cdr e)))
           (rest (filter (lambda (z) (not (contains-sym? z y))) (cdr e))))
       (cond ((null? act) (list (list 'free (* c (apply * rest)))))
             ((null? (cdr act)) (ld-vflat (car act) (* c (apply * rest)) y t))
             (else (error "уравнение нелинейно по y")))))
    ((and (lt-head? e '/) (= (length e) 3) (not (contains-sym? (caddr e) y)))
     (ld-vflat (cadr e) (/ c (caddr e)) y t))
    ((equal? e (list y t)) (list (list 'y c)))
    ((lt-head? e 'integrate) (list (list 'int c (ld-vkernel e y t))))
    ((lt-head? e 'convolve)
     (cond ((equal? (caddr e) (list y t)) (list (list 'int c (subst (list t 'lt-u) (cadr e)))))
           ((equal? (cadr e) (list y t)) (list (list 'int c (subst (list t 'lt-u) (caddr e)))))
           (else (error "convolve без y"))))
    ((contains-sym? e y) (error "y в неподдерживаемой форме"))
    (else (list (list 'free (* c e))))))

; (integrate h tau 0 t) → ядро как функция lt-u = t − τ
(define (ld-vkernel e y t)
  (if (not (and (= (length e) 5) (equal? (nth e 3) 0) (equal? (nth e 4) t)))
      (error "интеграл не от 0 до t"))
  (let* ((h (cadr e)) (tau (caddr e)) (fs (lt-factors h))
         (direct (lt-find (lambda (f) (equal? f (list y tau))) fs))
         (shifted (lt-find (lambda (f) (equal? f (list y (simplify (list '- t tau))))) fs)))
    (cond
      (direct
       (let ((k (simplify (subst (list t (list '+ 'lt-u tau)) (apply * (lt-remove direct fs))))))
         (if (contains-sym? k tau) (error "ядро не зависит от t − τ") k)))
      (shifted
       (let ((k (simplify (subst (list tau 'lt-u) (apply * (lt-remove shifted fs))))))
         (if (contains-sym? k t) (error "ядро не зависит от t − τ") k)))
      (else (error "не вижу y(τ) под интегралом")))))

; численная проверка в точках: a·y + Σ λ ∫ k(t−τ)y(τ)dτ + f = 0
(define (ld-vcheck-num items sol t)
  (ld-combine
   (map (lambda (t0)
          (let* ((vals (map (lambda (it)
                              (cond ((equal? (car it) 'y) (* (eval-num (cadr it)) (lt-ev sol t t0)))
                                    ((equal? (car it) 'free) (lt-ev (cadr it) t t0))
                                    (else (* (eval-num (cadr it))
                                             (lt-quad (lambda (x) (* (lt-ev (caddr it) 'lt-u (- t0 x)) (lt-ev sol t x)))
                                                      0 t0)))))
                            items))
                 (v (apply + vals))
                 (scale (+ 1.0 (apply + (map abs vals)))))
            (if (< (abs v) (* 0.000001 scale)) 'numeric #f)))
        '(1/2 1 3/2 2))))

(define (ld-vcheck items sol t)
  (let* ((steps? (or (lt-has-step? sol) (any? (lambda (it) (lt-has-step? (cdr it))) items)))
         (exact
          (lt-try
           (lambda ()
             (simplify
              (ld-sum
               (map (lambda (it)
                      (cond ((equal? (car it) 'y) (* (cadr it) sol))
                            ((equal? (car it) 'free) (cadr it))
                            (else (* (cadr it) (convolve (subst (list 'lt-u t) (caddr it)) sol t)))))
                    items))))))
         (ex (if (and exact (not (contains-sym? exact 'convolve)) (not (lt-has-int? exact)))
                 (ld-zero-check exact t)
                 'unknown)))
    (cond ((not (equal? ex 'unknown)) ex)
          (steps? 'unknown)
          (else (ld-vcheck-num items sol t)))))

(define (ld-volterra eq y t)
  (let* ((s (if (contains-sym? eq 's) 'ld-s 's))
         (items (if (lt-head? eq '=)
                    (append (ld-vflat (cadr eq) 1 y t) (ld-vflat (caddr eq) -1 y t))
                    (ld-vflat eq 1 y t)))
         (ay (ld-sum (map cadr (filter (lambda (it) (equal? (car it) 'y)) items))))
         (ints (filter (lambda (it) (equal? (car it) 'int)) items))
         (frees (ld-sum (map cadr (filter (lambda (it) (equal? (car it) 'free)) items))))
         (forcing (simplify (* -1 frees)))
         (Ks (map (lambda (it)
                    (let ((K (laplace (caddr it) 'lt-u s)))
                      (if (contains-sym? K 'laplace) (error "ядро не имеет образа Лапласа") (* (cadr it) K))))
                  ints))
         (dn (simplify (together (+ ay (ld-sum Ks)))))
         (F (if (equal? forcing 0) 0 (laplace forcing t s))))
    (if (contains-sym? F 'laplace) (error "правая часть не имеет образа Лапласа"))
    (if (equal? dn 0) (error "вырожденное уравнение (a + λK = 0)"))
    (let ((sol (if (equal? F 0) 0
                   (let ((r (inverse-laplace (simplify (list '/ F dn)) s t)))
                     (if (contains-sym? r 'inverse-laplace) (error "обратное преобразование не вычислено") r)))))
      (list (simplify sol) items))))

; (laplace-volterra eq (y t)) — уравнение Вольтерра типа свёртки; результат — ode-solution (check: #t | numeric | unknown)
(define (laplace-volterra eq yt)
  (let* ((y (car yt)) (t (cadr yt))
         (r (try (ld-volterra eq y t)
                 (lambda (e) (list 'fail (if (error? e) (error-message e) "ошибка"))))))
    (if (equal? (car r) 'fail)
        (ode-solution 'particular '() '() (string-append "laplace-volterra: " (to-string (cadr r))) 'unknown 'laplace 'none)
        (let* ((sol (car r))
               (chk (try (ld-vcheck (cadr r) sol t) (lambda (e) 'unknown)))
               (out (list (list '= (list y t) sol))))
          (cond ((or (equal? chk #t) (equal? chk 'numeric))
                 (ode-solution 'particular out '() '() 'ok 'laplace chk))
                ((equal? chk #f)
                 (ode-solution 'particular '() '() "решение не прошло проверку" 'unknown 'laplace #f))
                (else (ode-solution 'particular out '() '() 'unchecked 'laplace 'unknown)))))))

; ---------- передаточная функция, импульсная и переходная характеристики, полюса, устойчивость ----------

; разложение линейного E = f + Σ a·D по парам (i . k)
(define (ld-lin-split ab pairs)
  (let* ((f (simplify (subst (map (lambda (p) (list (ld-dsym (car p) (cdr p)) 0)) pairs) ab)))
         (as (map (lambda (p)
                    (simplify (- (subst (map (lambda (q) (list (ld-dsym (car q) (cdr q)) (if (equal? p q) 1 0))) pairs) ab) f)))
                  pairs)))
    (if (not (equal? (simplify (expand (- ab (+ f (ld-sum (map2 (lambda (a p) (* a (ld-dsym (car p) (cdr p)))) as pairs)))))) 0))
        (error "уравнение нелинейно"))
    (cons f as)))

; (transfer-function eq (y t) (u t)) → W(s) = Y/U при нулевых начальных условиях; не вышло — невычисленная форма
(define (transfer-function eq yt ut)
  (let ((r (try (ld-transfer eq yt ut) (lambda (e) #f))))
    (if r r (list 'transfer-function eq yt ut))))

(define (ld-transfer eq yt ut)
  (let* ((y (car yt)) (u (car ut)) (t (cadr yt)) (names (list y u))
         (E (ld-norm-eq eq))
         (hits (ld-hits E names t))
         (o0 (ld-ord-of hits 0)) (o1 (ld-ord-of hits 1))
         (pairs (append (map (lambda (k) (cons 0 k)) (range (+ o0 1))) (map (lambda (k) (cons 1 k)) (range (+ o1 1)))))
         (sp (ld-lin-split (ld-abstract E names t) pairs))
         (as (cdr sp))
         (pa (filter (lambda (x) (= (car (car x)) 0)) (map2 cons pairs as)))
         (pb (filter (lambda (x) (= (car (car x)) 1)) (map2 cons pairs as)))
         (poly (lambda (l sg) (expand (* sg (ld-sum (map (lambda (x) (* (cdr x) (^ 's (cdr (car x))))) l))))))
         (P (poly pa 1)) (Q (poly pb -1)))
    (if (not (equal? (car sp) 0)) (error "есть слагаемое без y и u"))
    (if (equal? P 0) (error "нет y"))
    (simplify (together (/ Q P)))))

(define (impulse-response eq yt ut)
  (let ((W (transfer-function eq yt ut)))
    (if (lt-head? W 'transfer-function)
        (list 'impulse-response eq yt ut)
        (inverse-laplace W 's (cadr yt)))))

(define (step-response eq yt ut)
  (let ((W (transfer-function eq yt ut)))
    (if (lt-head? W 'transfer-function)
        (list 'step-response eq yt ut)
        (inverse-laplace (simplify (list '/ W 's)) 's (cadr yt)))))

; полюса W (список различных корней: рациональные, квадратные радикалы, root-of); без полюсов — ()
(define (transfer-poles W s)
  (let ((d (denom (together W))))
    (if (not (contains-sym? d s))
        '()
        (let ((r (solve d s)))
          (if (equal? (type-of r) 'set) (set->list r) (list r))))))

; первый столбец таблицы Рауса
(define (ld-routh-ok? r0 r1 n)
  (let loop ((a r0) (b r1) (k 1))
    (cond ((<= (car b) 0) #f)
          ((>= k n) #t)
          (else
           (let* ((p (car b)) (q (car a))
                  (next (append (map2 (lambda (x y) (/ (- (* p x) (* q y)) p)) (cdr a) (cdr b)) (list 0))))
             (loop b next (+ k 1)))))))

; все полюса W в Re s < 0? #t | #f | unknown (нерациональные коэффициенты): Раус–Гурвиц над ℚ
(define (stable? W s)
  (let* ((d (lt-try (lambda () (expand (denom (together W)))))))
    (cond ((not d) 'unknown)
          ((not (contains-sym? d s)) #t)
          ((not (polynomial? d s)) 'unknown)
          (else
           (let* ((cs (reverse (coefficients d s))))
             (if (not (every? (lambda (c) (and (number? c) (not (equal? (type-of c) 'float)))) cs))
                 'unknown
                 (let* ((cs (if (< (car cs) 0) (map (lambda (c) (* -1 c)) cs) cs))
                        (n (- (length cs) 1)))
                   (cond ((any? (lambda (c) (<= c 0)) cs) #f)
                         ((= n 1) #t)
                         (else
                          (let* ((ev (let loop ((l cs) (i 0)) (cond ((null? l) '()) ((= (modulo i 2) 0) (cons (car l) (loop (cdr l) (+ i 1)))) (else (loop (cdr l) (+ i 1))))))
                                 (od (let loop ((l cs) (i 0)) (cond ((null? l) '()) ((= (modulo i 2) 1) (cons (car l) (loop (cdr l) (+ i 1)))) (else (loop (cdr l) (+ i 1))))))
                                 (w (length ev))
                                 (pad (lambda (l) (append l (map (lambda (i) 0) (range (- w (length l))))))))
                            (ld-routh-ok? (pad ev) (pad od) n)))))))))))
