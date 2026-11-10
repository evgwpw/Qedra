; definite.lisp — несобственные определённые интегралы (шаг DI.1)
; (definite-integral f x a b) → значение | (divergent "причина") | unknown; концы — числа, inf, -inf, константы (pi).
; Пути: сходимость → вычеты рациональных функций (прямая, полупрямая через log z) → R(x)·cos/sin(ωx) (лемма Жордана)
; → таблицы (Гаусс, Γ, B, Дирихле, Френель, e^{-ax}cos bx) → ∫₀^{2π} R(cos, sin) → Ньютон–Лейбниц (integrate + пределы).
; (definite-check f x a b v) — сертификат: интервалы certified-integral + строгий хвост (#t | numeric | #f | unknown).
; Вычеты точно: поле ℚ[t]/(t²+pt+q) (степень ≤ 2); неприводимые степени ≥ 3 — точные суммы по корням (биквадрат, нормальное
; поле → радикалы, иначе root-sum с heaviside); DI.2: замочная скважина x^s·R, log x·R, параметры, Фейнман, окружность.
; Внутренние имена: di-.
(module definite
  (export definite-integral definite-check definite-convergence definite-feynman definite-interior))

; ---------- общее ----------

(define (di-free? e x) (not (contains-sym? e x)))
(define (di-head? e h) (and (pair? e) (equal? (car e) h)))
(define (di-inf? v) (or (equal? v 'inf) (equal? v '-inf)))
(define (di-q? c) (or (integer? c) (equal? (type-of c) 'rational)))
(define (di-all-q? l) (every? di-q? l))
(define (di-fl v) (let ((r (try (eval-num v) (lambda (e) #f)))) (if (number? r) r #f)))
(define (di-nth-or l i z) (if (< i (length l)) (nth l i) z))

; комплексная пара (re . im) → список (re im) для печати в шагах
(define (di-cpair p) (if (pair? p) (list (car p) (cdr p)) (list p)))

; комплексная пара (re . im) → выражение a + b·i (полюс/вычет в шаге)
(define (di-cx p)
  (let* ((re (simplify (car p))) (im (simplify (cdr p))))
    (cond ((and (equal? re 0) (equal? im 1)) '%i)
          ((equal? re 0) (simplify (list '* im '%i)))
          ((equal? im 0) re)
          ((equal? im 1) (simplify (list '+ re '%i)))
          ((equal? im -1) (simplify (list '- re '%i)))
          (else (simplify (list '+ re (list '* im '%i)))))))
(define (di-sqrt q) (simplify (list '^ q 1/2)))
(define (di-pi) (di-fl 'pi))

; числовое значение границы: число | +-1e30 для inf | #f
(define (di-bnum v)
  (cond ((equal? v 'inf) 1e30) ((equal? v '-inf) -1e30) (else (di-fl v))))

(define (di-factors e)
  (if (di-head? e '*) (append-map di-factors (cdr e)) (list e)))
(define (di-terms e)
  (if (di-head? e '+) (cdr e) (list e)))
(define (di-prod l) (if (null? l) 1 (if (null? (cdr l)) (car l) (apply * l))))
(define (di-sum l) (if (null? l) 0 (if (null? (cdr l)) (car l) (apply + l))))

; ---------- комплексные пары (re . im) с символьными/числовыми компонентами ----------

(define (c+ a b) (cons (+ (car a) (car b)) (+ (cdr a) (cdr b))))
(define (c* a b)
  (cons (- (* (car a) (car b)) (* (cdr a) (cdr b)))
        (+ (* (car a) (cdr b)) (* (cdr a) (car b)))))

; ---------- поля: линейный корень (ℚ) и корень x² + p x + q (ℚ[t]/(t²+pt+q), элемент (u . v) = u + v t) ----------
; ops = (add mul inv ofq gen)

(define (di-ops-lin r) (list + * (lambda (z) (/ 1 z)) (lambda (q) q) r))
(define (di-ops-quad p q)
  (let* ((add (lambda (a b) (cons (+ (car a) (car b)) (+ (cdr a) (cdr b)))))
         (mul (lambda (a b)
                (let ((u1 (car a)) (v1 (cdr a)) (u2 (car b)) (v2 (cdr b)))
                  (cons (- (* u1 u2) (* q v1 v2))
                        (- (+ (* u1 v2) (* u2 v1)) (* p v1 v2))))))
         (inv (lambda (z)
                (let* ((zb (cons (- (car z) (* p (cdr z))) (- 0 (cdr z))))
                       (n (car (mul z zb))))
                  (cons (/ (car zb) n) (/ (cdr zb) n))))))
    (list add mul inv (lambda (c) (cons c 0)) (cons 0 1))))
(define (ops-add o) (car o))
(define (ops-mul o) (cadr o))
(define (ops-inv o) (caddr o))
(define (ops-q o) (nth o 3))
(define (ops-gen o) (nth o 4))
(define (di-neg o z) ((ops-mul o) ((ops-q o) -1) z))
(define (di-sub o a b) ((ops-add o) a (di-neg o b)))
(define (di-zero o) ((ops-q o) 0))

(define (di-synth o cs-desc a)
  (let loop ((l (cdr cs-desc)) (acc (car cs-desc)) (out '()))
    (if (null? l)
        (cons (reverse out) acc)
        (loop (cdr l) ((ops-add o) (car l) ((ops-mul o) a acc)) (cons acc out)))))

; коэффициенты Тейлора многочлена (элементы поля по возрастанию) в точке a
(define (di-taylor o cs-asc a)
  (let loop ((cur (reverse cs-asc)) (acc '()))
    (if (null? cur)
        (reverse acc)
        (let ((r (di-synth o cur a))) (loop (car r) (cons (cdr r) acc))))))

; первые n коэффициентов ps/rs (r0 обратим)
(define (di-series-div o ps rs n)
  (let ((z (di-zero o)) (ri0 ((ops-inv o) (car rs))))
    (let loop ((k 0) (s '()))
      (if (= k n)
          (reverse s)
          (let ((acc (di-nth-or ps k z)))
            (let inner ((j 1) (acc acc))
              (if (> j k)
                  (loop (+ k 1) (cons ((ops-mul o) acc ri0) s))
                  (inner (+ j 1)
                         (di-sub o acc ((ops-mul o) (di-nth-or rs j z)
                                                    (nth s (- j 1))))))))))))

; ряд f(a+t)·g: s = ps/rest до порядка m − 1; возвращает список s_0..s_{m-1}
(define (di-pole-series o pcs qcs a m)
  (let* ((pt (di-taylor o (map (ops-q o) pcs) a))
         (qt (di-taylor o (map (ops-q o) qcs) a)))
    (di-series-div o pt (drop qt m) m)))

; ---------- рациональная функция ----------

(define (di-rat f x)
  (let* ((g (together f)) (n (numer g)) (d (denom g)))
    (if (and (polynomial? n x) (polynomial? d x))
        (let ((pc (coefficients n x)) (qc (coefficients d x)))
          (if (and (pair? qc) (di-all-q? pc) (di-all-q? qc)) (cons pc qc) #f))
        #f)))

(define (di-poly cs x) (coefficients->poly cs x))
(define (di-deg cs) (- (length cs) 1))

; разложение знаменателя: список (вид кратность данные...)
;   (lin k r) (quad k p q D) (quadreal k p q D) (high k cs)
(define (di-classify qc x)
  (let* ((fl (factor-list (di-poly qc x))))
    (map (lambda (fk)
           (let* ((cs (coefficients (car fk) x)) (k (cadr fk)))
             (cond ((= (length cs) 2) (list 'lin k (/ (- 0 (car cs)) (cadr cs))))
                   ((= (length cs) 3)
                    (let* ((a (caddr cs)) (p (/ (cadr cs) a)) (q (/ (car cs) a)) (D (- (* 4 q) (* p p))))
                      (if (> D 0) (list 'quad k p q D) (list 'quadreal k p q D))))
                   (else (list 'high k cs)))))
         (cdr fl))))

(define (di-kind r) (car r))
(define (di-mult r) (cadr r))

; вещественные полюса: есть ли корень на множестве? pred: вещественное число-приближение → #t
(define (di-real-poles-in facs x pred)
  (any? (lambda (r)
          (cond ((equal? (di-kind r) 'lin) (pred (caddr r)))
                ((equal? (di-kind r) 'quadreal)
                 (let* ((p (caddr r)) (q (nth r 3)) (D (- (* p p) (* 4 q))) (sq (di-fl (di-sqrt D))))
                   (or (pred (/ (+ (- 0 p) sq) 2)) (pred (/ (- (- 0 p) sq) 2)))))
                ((equal? (di-kind r) 'high)
                 (any? (lambda (rt) (pred (di-fl rt))) (try (real-roots (di-poly (caddr r) x) x) (lambda (e) '()))))
                (else #f)))
        facs))

; ---------- вычеты рациональной функции ----------

(define (di-ops-of r)
  (if (equal? (di-kind r) 'lin) (di-ops-lin (caddr r)) (di-ops-quad (caddr r) (nth r 3))))

; корень квадратичного множителя: (re . im), im = ±√D/2 (sigma = 1 — верхний)
(define (di-root-parts r sigma)
  (cons (/ (- 0 (caddr r)) 2) (* sigma (/ (di-sqrt (nth r 4)) 2))))

(define (di-elt->c r e sigma)
  (if (equal? (di-kind r) 'lin)
      (cons e 0)
      (let ((parts (di-root-parts r sigma)))
        (cons (+ (car e) (* (cdr e) (car parts))) (* (cdr e) (cdr parts))))))

; ряд s_0..s_{m-1} = коэффициенты (z−α)^m·P/Q в α
(define (di-res-series r pc qc)
  (let ((o (di-ops-of r)))
    (di-pole-series o pc qc (ops-gen o) (di-mult r))))

(define (di-res r pc qc sigma)
  (let ((s (di-res-series r pc qc)))
    (di-elt->c r (nth s (- (di-mult r) 1)) sigma)))

; ---------- точные суммы вычетов по корням неприводимого множителя степени ≥ 3 (DI.2) ----------
; Вычет в корне α простого множителя g: P(α)/Q′(α) = R(α), R ∈ ℚ[t] (элемент поля ℚ(α) = ℚ[t]/g).
; 'upper — b = Σ_{Im α>0} Im R(α) (∫ по прямой = −2π·Σb), 'disc — Σ_{|α|<1} R(α) (окружность = 2π·Σ).
; Нормальное поле (все корни g лежат в ℚ(α); алгоритм alg-factor): сумма — элемент поля, затем замкнутая форма
; через минимальный многочлен степени ≤ 2 (радикалы). Иначе (или степень выше 2) — root-sum по корням g с
; отбором heaviside; плавающих догадок нет: числа служат только выбору вложения и самопроверке.

(define (di-monic-cs gcs) (let ((lc (last gcs))) (map (lambda (c) (/ c lc)) gcs)))

(define (di-high-field gcs)
  (try (alg-field (coefficients->poly (di-monic-cs gcs) 't) 't) (lambda (e) #f)))

; корни g как элементы F, если g полностью разлагается над F (иначе #f)
(define (di-normal-roots F gcs)
  (let* ((f (map (lambda (c) (alg-elt F (list c))) (di-monic-cs gcs)))
         (r (try (alg-factor F f 'x) (lambda (e) #f))))
    (and r
         (every? (lambda (pr) (and (= (length (car pr)) 2) (= (cadr pr) 1))) (cadr r))
         (map (lambda (pr) (alg-negate F (car (car pr)))) (cadr r)))))

; численное вложение (re . im)
(define (di-emb-c F)
  (let ((emb (alg-field-embed F)))
    (cond ((alg? emb) (cons (di-fl emb) 0.0))
          ((number? emb) (cons (* 1.0 emb) 0.0))
          (else (transforms::tr-cplx emb)))))

(define (fc* a b) (cons (- (* (car a) (car b)) (* (cdr a) (cdr b))) (+ (* (car a) (cdr b)) (* (cdr a) (car b)))))
(define (fc-horner cs z)
  (foldl (lambda (acc c) (let ((m (fc* acc z))) (cons (+ (car m) c) (cdr m)))) (cons 0.0 0.0) (reverse cs)))
(define (di-elt-num e z0) (fc-horner (map (lambda (c) (* 1.0 c)) e) z0))

(define (di-dpoly cs)
  (let loop ((l (cdr cs)) (i 1) (out '()))
    (if (null? l) (reverse out) (loop (cdr l) (+ i 1) (cons (* i (car l)) out)))))

; элемент R(r): подстановка элемента r в многочлен-элемент R (схема Горнера)
(define (di-compose F R r)
  (let loop ((cs (reverse R)) (acc '()))
    (if (null? cs)
        acc
        (loop (cdr cs) (alg-add F (alg-mul F acc r) (alg-elt F (list (car cs))))))))

(define (di-sum-elts F l) (foldl (lambda (acc e) (alg-add F acc e)) '() l))

; неприводимый множитель характеристического многочлена элемента z, обнуляющийся в znum (и точно: z — его корень)
(define (di-minpoly F z znum)
  (let* ((p (algnum::ag-poly-expr F z))
         (res (resultant (alg-field-minpoly F) (list '+ 'y (list '* -1 p)) 't))
         (cands (map (lambda (fk) (nth fk 0)) (cdr (factor-list res))))
         (sc (map (lambda (c) (cons (let ((v (di-fl (simplify (subst (list 'y znum) c))))) (if v (abs v) 1e30)) c)) cands))
         (best (foldl (lambda (b c) (if (< (car c) (car b)) c b)) (car sc) (cdr sc))))
    (and (< (car best) 1e-6) (algnum::ag-vanishes? F z (cdr best) 'y) (cdr best))))

; вещественный корень минимального многочлена степени ≤ 2 → выражение | #f
(define (di-solve-minpoly mp znum)
  (let ((cs (coefficients mp 'y)))
    (cond ((= (length cs) 2) (/ (- 0 (car cs)) (cadr cs)))
          ((= (length cs) 3)
           (let* ((a (caddr cs)) (b (cadr cs)) (c (car cs))
                  (sq (di-sqrt (- (* b b) (* 4 a c))))
                  (r1 (simplify (/ (+ (- 0 b) sq) (* 2 a))))
                  (r2 (simplify (/ (- (- 0 b) sq) (* 2 a)))))
             (if (< (abs (- (di-fl r1) znum)) (abs (- (di-fl r2) znum))) r1 r2)))
          (else #f))))

; вещественный элемент e ∈ F → выражение | #f
(define (di-real-elt-expr F e enum)
  (if (null? e)
      0
      (let ((mp (di-minpoly F e enum))) (and mp (di-solve-minpoly mp enum)))))

; замкнутая сумма по корням нормального поля: выражение | #f
(define (di-high-closed F rts R sel)
  (let* ((z0 (di-emb-c F))
         (vals (map (lambda (r) (di-elt-num r z0)) rts))
         (key (if (equal? sel 'upper) (lambda (v) (cdr v)) (lambda (v) (- 1.0 (sqrt (+ (* (car v) (car v)) (* (cdr v) (cdr v))))))))
         (ok (every? (lambda (v) (> (abs (key v)) 1e-9)) vals))
         (ins (filter (lambda (p) (> (key (car p)) 0)) (map2 cons vals rts)))
         (outs (filter (lambda (p) (< (key (car p)) 0)) (map2 cons vals rts)))
         (ein (di-sum-elts F (map (lambda (p) (di-compose F R (cdr p))) ins)))
         (eout (di-sum-elts F (map (lambda (p) (di-compose F R (cdr p))) outs))))
    (and ok
         (if (equal? sel 'upper)
             (let* ((d (alg-sub F ein eout))
                    (z (alg-mul F (alg-elt F '(-1/4)) (alg-mul F d d)))
                    (bnum (cdr (di-elt-num ein z0)))
                    (zexpr (di-real-elt-expr F z (car (di-elt-num z z0)))))
               (and zexpr
                    (let* ((s (if (< bnum 0) -1 1)) (b (simplify (list '* s (list '^ zexpr 1/2))))
                           (bv (di-fl b)))
                      (and bv (< (abs (- bv bnum)) 1e-8) b))))
             (let* ((enum (car (di-elt-num ein z0))) (e (di-real-elt-expr F ein enum)) (ev (and e (di-fl e))))
               (and ev (< (abs (- ev enum)) 1e-8) e))))))

; root-sum по корням g с отбором heaviside — точное выражение без замкнутой формы
(define (di-high-rootsum F R sel)
  (let* ((gm (alg-field-minpoly F)) (Rx (di-poly R 't)))
    (if (equal? sel 'upper)
        (list 'im (list 'root-sum 't gm (list '* Rx (list 'heaviside (list 'im 't)))))
        (list 'root-sum 't gm (list '* Rx (list 'heaviside (list '+ 1 (list '* -1 (list 'abs 't)))))))))

; сумма по выбору sel для множителя gcs (кратность 1): выражение (вещественное)
(define (di-high-sum gcs pc qc sel)
  (let ((F (di-high-field gcs)))
    (and F
         (let* ((R (expr->alg F (/ (di-poly pc 't) (di-poly (di-dpoly qc) 't))))
                (rts (di-normal-roots F gcs))
                (cl (and rts (di-high-closed F rts R sel))))
           (or cl (di-high-rootsum F R sel))))))

; биквадрат Q = k(x⁴ + p x² + q), P = c0 + c2 x²: ∫ dx/(x⁴+px²+q) = π/(√q √(p+2√q)), ∫ x²… = π/√(p+2√q)
(define (di-biquad pc qc)
  (and (= (length qc) 5) (equal? (nth qc 1) 0) (equal? (nth qc 3) 0)
       (<= (length pc) 3) (or (< (length pc) 2) (equal? (nth pc 1) 0))
       (let* ((k (nth qc 4)) (p (/ (nth qc 2) k)) (q (/ (nth qc 0) k)))
         (and (> q 0)
              (let* ((s (di-sqrt q)) (w (di-sqrt (+ p (* 2 s))))
                     (c0 (di-nth-or pc 0 0)) (c2 (di-nth-or pc 2 0)))
                (simplify (/ (* 'pi (+ (/ c0 s) c2)) (* k w))))))))

; ∫ P/Q по прямой при простых неприводимых множителях степени ≥ 3: вещественное значение | #f
(define (di-line-high facs pc qc x tot)
  (let ((hs (filter (lambda (r) (equal? (di-kind r) 'high)) facs)))
    (or (and (= (length facs) 1) (di-biquad pc qc))
        (let loop ((l hs) (acc (cdr tot)))
          (if (null? l)
              (simplify (* -2 'pi acc))
              (let ((b (di-high-sum (caddr (car l)) pc qc 'upper)))
                (and b (loop (cdr l) (+ acc b)))))))))

(define (di-high? facs) (any? (lambda (r) (equal? (di-kind r) 'high)) facs))
(define (di-high-simple? facs)
  (every? (lambda (r) (or (not (equal? (di-kind r) 'high)) (= (di-mult r) 1))) facs))
(define (di-simple? facs) (every? (lambda (r) (= (di-mult r) 1)) facs))

; прямая: (divergent …) | значение | #f
(define (di-line-rat pc qc x)
  (let ((facs (di-classify qc x)))
    (cond ((di-real-poles-in facs x (lambda (r) #t)) (list 'divergent "вещественный полюс на прямой"))
          ((< (- (di-deg qc) (di-deg pc)) 2) (list 'divergent "подынтегральная функция убывает не быстрее 1/x"))
          ((not (di-high-simple? facs)) #f)
          (else
           (let ((tot (foldl (lambda (acc r)
                               (if (equal? (di-kind r) 'quad)
                                   (c+ acc (di-res r pc qc 1))
                                   acc))
                             (cons 0 0) facs)))
             (if (step-log-enabled?)
                 (let* ((qs (filter (lambda (r) (equal? (di-kind r) 'quad)) facs))
                        (poles (map (lambda (r) (di-cx (di-root-parts r 1))) qs))
                        (ress (map (lambda (r) (di-cx (di-res r pc qc 1))) qs)))
                   (record-step 'di-residues "Полюса в верхней полуплоскости и вычеты"
                                (string-append "deg Q − deg P = " (to-string (- (di-deg qc) (di-deg pc)))
                                               " ≥ 2: на дуге |z| = R подынтегральная убывает (лемма Жордана);"
                                               " сумма вычетов · 2πi")
                                (di-one poles) (di-one ress) 'main)))
             (if (di-high? facs)
                 (di-line-high facs pc qc x tot)
                 (simplify (* -2 (cdr tot) 'pi))))))))

(define (di-even? f x)
  (equal? (simplify (together (- f (subst (list x (list '* -1 x)) f)))) 0))

; наименьшее v ≤ 120, при котором α^v вещественно (ТОЧНО, в ℚ[t]/(t²+pt+q)): тогда arg α — кратное π/v
(define (di-arg-denom r)
  (let* ((o (di-ops-of r)) (g (ops-gen o)))
    (let loop ((v 1) (pw g))
      (cond ((equal? (cdr pw) 0) v)
            ((>= v 120) #f)
            (else (loop (+ v 1) ((ops-mul o) pw g)))))))

; угол корня в (0, 2π) как рациональное кратное π | #f (знаменатель доказан точно; числитель — из float-угла,
; кандидаты отстоят на π/v ≥ π/120 ≫ погрешности)
(define (di-arg-pi r sigma)
  (let* ((v (di-arg-denom r)))
    (and v
         (let* ((ap (di-root-parts r 1)) (a (car ap)) (s (di-fl (cdr ap)))
                (pi (di-pi))
                (th (cond ((> a 0) (di-fl (list 'atan (/ s (di-fl a)))))
                          ((< a 0) (+ pi (di-fl (list 'atan (/ s (di-fl a))))))
                          (else (/ pi 2))))
                (k (/ (floor (+ (* v (/ th pi)) 0.5)) v)))
           (if (> sigma 0) k (- 2 k))))))

; вклад полюса в Res(R log z): (re . im) или #f
(define (di-res-log r pc qc sigma)
  (let* ((o (di-ops-of r)) (m (di-mult r))
         (s (di-res-series r pc qc))
         (kth (if (equal? (di-kind r) 'lin) (if (< (caddr r) 0) 1 #f) (di-arg-pi r sigma))))
    (and kth
         (let* ((lnr (if (equal? (di-kind r) 'lin)
                         (simplify (list 'log (- 0 (caddr r))))
                         (simplify (list '* 1/2 (list 'log (nth r 3))))))
                (L (cons lnr (simplify (list '* kth 'pi))))
                (ia ((ops-inv o) (ops-gen o)))
                (B (let loop ((k 1) (pw ia) (acc (di-zero o)))
                     (if (>= k m)
                         acc
                         (loop (+ k 1) ((ops-mul o) pw ia)
                               ((ops-add o) acc
                                ((ops-mul o) (nth s (- m 1 k))
                                             ((ops-mul o) ((ops-q o) (/ (if (even-int? (+ k 1)) 1 -1) k)) pw))))))))
           (c+ (c* (di-elt->c r (nth s (- m 1)) sigma) L) (di-elt->c r B sigma))))))

(define (even-int? n) (= (remainder n 2) 0))

; (0, ∞): (divergent …) | значение | #f
(define (di-half-rat pc qc x f)
  (let ((facs (di-classify qc x)))
    (cond ((di-real-poles-in facs x (lambda (r) (>= r 0))) (list 'divergent "полюс на [0, ∞)"))
          ((< (- (di-deg qc) (di-deg pc)) 2) (list 'divergent "подынтегральная функция убывает не быстрее 1/x"))
          ((di-even? f x)
           (let ((v (di-line-rat pc qc x)))
             (if (and v (not (di-head? v 'divergent))) (simplify (* 1/2 v)) v)))
          ((some-bad-half? facs) #f)
          (else
           (let loop ((l facs) (tot (cons 0 0)))
             (if (null? l)
                 (let ((im (di-fl (cdr tot))))
                   (and im (< (abs im) 1e-9) (simplify (- 0 (car tot)))))
                 (let ((r (car l)))
                   (cond ((equal? (di-kind r) 'lin)
                          (let ((v (di-res-log r pc qc 1))) (and v (loop (cdr l) (c+ tot v)))))
                         (else
                          (let ((v1 (di-res-log r pc qc 1)) (v2 (di-res-log r pc qc -1)))
                            (and v1 v2 (loop (cdr l) (c+ (c+ tot v1) v2)))))))))))))

(define (some-bad-half? facs)
  (any? (lambda (r) (or (equal? (di-kind r) 'high) (equal? (di-kind r) 'quadreal))) facs))

; ---------- рациональные функции на полупрямых и прямой ----------

; подстановка x → u(x) с упрощением
(define (di-subst x u f) (simplify (subst (list x u) f)))

; (a, b) — a конечный/−inf, b конечный/inf; результат (divergent …) | значение | #f
(define (di-rational-route f x a b)
  (let ((rf (di-rat f x)))
    (cond
      ((not rf) #f)
      ((and (equal? a '-inf) (equal? b 'inf)) (di-line-rat (car rf) (cdr rf) x))
      ((and (equal? b 'inf) (di-q? a))
       (let ((g (if (= a 0) f (di-subst x (list '+ x a) f))))
         (let ((rg (di-rat g x))) (and rg (di-half-rat (car rg) (cdr rg) x g)))))
      ((and (equal? a '-inf) (di-q? b))
       (let* ((g (di-subst x (list '+ b (list '* -1 x)) f)) (rg (di-rat g x)))
         (and rg (di-half-rat (car rg) (cdr rg) x g))))
      ((and (di-q? a) (di-q? b))
       (let ((facs (di-classify (cdr rf) x)))
         (if (di-real-poles-in facs x (lambda (r) (and (>= r a) (<= r b))))
             (list 'divergent "полюс подынтегральной функции на отрезке")
             #f)))
      (else #f))))


; ---------- Γ и Β ----------

(define (di-fact n) (if (<= n 1) 1 (* n (di-fact (- n 1)))))
(define (di-dfact2 n) (if (<= n 0) 1 (* n (di-dfact2 (- n 2)))))   ; n!!

; Γ(s): целое > 0 → факториал; полуцелое → r·√π; иначе (gamma s)
(define (di-gamma s)
  (cond ((and (integer? s) (> s 0)) (di-fact (- s 1)))
        ((and (di-q? s) (integer? (- s 1/2)))
         (let ((n (- s 1/2)))
           (if (>= n 0)
               (simplify (list '* (/ (di-dfact2 (- (* 2 n) 1)) (^ 2 n)) (list '^ 'pi 1/2)))
               (let ((m (- 0 n)))
                 (simplify (list '* (/ (* (^ -4 m) (di-fact m)) (di-fact (* 2 m))) (list '^ 'pi 1/2)))))))
        (else (list 'gamma s))))

(define (di-pow a e) (simplify (list '^ a e)))
(define (di-odd? n) (= (remainder n 2) 1))
(define (di-sign-of w) (let ((n (di-fl w))) (cond ((not n) #f) ((> n 0) 1) ((< n 0) -1) (else 0))))

; положительность параметра: числовая — по значению, символьная — условие в канал
(define (di-positive? v why)
  (let ((n (di-fl v)))
    (if n
        (> n 0)
        (begin (record-condition (list '> v 0) why) #t))))

; (основание . показатель): (^ b p), (sqrt b), иначе (u . 1)
(define (di-pow-form u)
  (cond ((and (di-head? u '^) (= (length u) 3))
         (let ((inner (di-pow-form (cadr u))) (p (caddr u)))
           (if (and (di-q? p) (di-q? (cdr inner)) (not (equal? (cdr inner) 1)))
               (cons (car inner) (* p (cdr inner)))
               (cons (cadr u) p))))
        ((and (di-head? u 'sqrt) (= (length u) 2))
         (let ((inner (di-pow-form (cadr u))))
           (if (di-q? (cdr inner)) (cons (car inner) (/ (cdr inner) 2)) (cons (cadr u) 1/2))))
        (else (cons u 1))))

; ---------- R(x)·cos/sin(ωx): лемма Жордана ----------

(define (di-trig-head? u) (or (di-head? u 'sin) (di-head? u 'cos)))

; вычет R(z) e^{iωz} в корне r (ω > 0): (re . im)
(define (di-res-fourier r pc qc w)
  (let* ((s (di-res-series r pc qc)) (m (di-mult r))
         (tot (let loop ((k 0) (acc (cons 0 0)))
                (if (>= k m)
                    acc
                    (loop (+ k 1)
                          (c+ acc (c* (di-elt->c r (nth s (- m 1 k)) 1)
                                      (let ((mag (/ (^ w k) (di-fact k))))
                                        (case (remainder k 4)
                                          ((0) (cons mag 0)) ((1) (cons 0 mag))
                                          ((2) (cons (- 0 mag) 0)) (else (cons 0 (- 0 mag)))))))))))
         (parts (di-root-parts r 1))
         (E (simplify (list 'exp (list '* -1 w (cdr parts)))))
         (ph (if (equal? (car parts) 0)
                 (cons E 0)
                 (let ((ang (list '* w (car parts))))
                   (cons (* E (simplify (list 'cos ang))) (* E (simplify (list 'sin ang))))))))
    (c* tot ph)))

; ∫_{−∞}^{∞} R cos ωx, R sin ωx (ω > 0) → (cos . sin) | #f
(define (di-fourier-line pc qc x w)
  (let ((facs (di-classify qc x)))
    (and (not (di-real-poles-in facs x (lambda (r) #t)))
         (>= (- (di-deg qc) (di-deg pc)) 1)
         (not (di-high? facs))
         (let ((tot (foldl (lambda (acc r)
                             (if (equal? (di-kind r) 'quad) (c+ acc (di-res-fourier r pc qc w)) acc))
                           (cons 0 0) facs)))
           (if (step-log-enabled?)
               (let* ((qs (filter (lambda (r) (equal? (di-kind r) 'quad)) facs))
                      (poles (map (lambda (r) (di-cx (di-root-parts r 1))) qs))
                      (ress (map (lambda (r) (di-cx (di-res-fourier r pc qc w))) qs)))
                 (record-step 'di-residues "Полюса в верхней полуплоскости и вычеты"
                              (string-append "deg Q − deg P = " (to-string (- (di-deg qc) (di-deg pc)))
                                             " ≥ 1: на дуге |z| = R подынтегральная убывает (лемма Жордана);"
                                             " сумма вычетов · 2πi")
                              (di-one poles) (di-one ress) 'main)))
           (cons (simplify (* -2 'pi (cdr tot))) (simplify (* 2 'pi (car tot))))))))

(define (di-parity R x)
  (let ((m (simplify (subst (list x (list '* -1 x)) R))))
    (cond ((equal? (simplify (together (- R m))) 0) 'even)
          ((equal? (simplify (together (+ R m))) 0) 'odd)
          (else #f))))

(define (di-fourier-term t x rng)
  (let* ((fs (di-factors t))
         (cs (filter (lambda (u) (di-free? u x)) fs))
         (rest (filter (lambda (u) (not (di-free? u x))) fs))
         (tr (filter di-trig-head? rest)))
    (and (= (length tr) 1)
         (let ((lin (transforms::tr-lin (cadr (car tr)) x)))
           (and lin (equal? (cdr lin) 0)
                (let* ((R (simplify (di-prod (filter (lambda (u) (not (equal? u (car tr)))) rest))))
                       (rf (di-rat R x)) (w (car lin)) (sg (di-sign-of w)))
                  (and rf (not (equal? sg 0))
                       (let* ((wp (if (equal? sg -1) (- 0 w) w))
                              (_ (if sg #t (record-condition (list '> w 0) "ω > 0 в e^{iωx}")))
                              (v (di-fourier-line (car rf) (cdr rf) x wp)))
                         (and v
                              (let* ((cosv (car v)) (sinv (if (equal? sg -1) (- 0 (cdr v)) (cdr v)))
                                     (kind (car (car tr))) (full (if (equal? kind 'cos) cosv sinv)))
                                (cond ((equal? rng 'line) (* (di-prod cs) full))
                                      ((equal? (di-parity R x) (if (equal? kind 'cos) 'even 'odd))
                                       (* (di-prod cs) 1/2 full))
                                      (else #f))))))))))))

(define (di-fourier-route f x a b)
  (let ((rng (di-range a b)))
    (and (or (equal? rng 'line) (equal? rng 'pos))
         (let loop ((l (di-terms (expand f))) (acc 0))
           (if (null? l)
               (simplify acc)
               (let ((v (di-fourier-term (car l) x rng)))
                 (and v (loop (cdr l) (+ acc v)))))))))

(define (di-range a b)
  (cond ((and (equal? a '-inf) (equal? b 'inf)) 'line)
        ((and (equal? a 0) (equal? b 'inf)) 'pos)
        ((and (equal? a '-inf) (equal? b 0)) 'neg)
        (else #f)))

; ---------- таблицы ----------

(define (di-xpow u x)
  (let ((pf (di-pow-form u)))
    (and (equal? (car pf) x) (di-free? (cdr pf) x) (cdr pf))))

; показатель p > −1: #t | #f (расходится) ; символьный — условие
(define (di-p-ok p)
  (let ((n (di-fl p)))
    (if n
        (> n -1)
        (begin (record-condition (list '> p -1) "p > −1: интегрируемость в нуле") #t))))

(define (di-diverges why) (list 'divergent why))

; ∫ x^p e^{c2 x² + c1 x + c0}
(define (di-gauss p c0 c1 c2 rng)
  (let ((a (simplify (- 0 c2))) (e0 (simplify (list 'exp c0))))
    (and (di-positive? a "a > 0: сходимость гауссова интеграла")
         (cond
           ((equal? rng 'line)
            (cond ((and (equal? c1 0) (integer? p) (>= p 0))
                   (if (di-odd? p)
                       0
                       (simplify (* e0 (di-gamma (/ (+ p 1) 2)) (di-pow a (- 0 (/ (+ p 1) 2)))))))
                  ((and (equal? p 0) (not (equal? c1 0)))
                   (simplify (* e0 (di-pow (/ 'pi a) 1/2) (list 'exp (/ (* c1 c1) (* 4 a))))))
                  (else #f)))
           ((and (equal? c1 0) (or (equal? rng 'pos) (and (equal? rng 'neg) (integer? p) (>= p 0))))
            (if (di-p-ok p)
                (let ((v (simplify (* 1/2 e0 (di-gamma (/ (+ p 1) 2)) (di-pow a (- 0 (/ (+ p 1) 2)))))))
                  (if (and (equal? rng 'neg) (di-odd? p)) (- 0 v) v))
                (di-diverges "x^p, p ≤ −1: расходится в нуле")))
           (else #f)))))

; ∫ x^p e^{c1 x + c0}
(define (di-expl p c0 c1 rng)
  (let ((e0 (simplify (list 'exp c0))))
    (cond ((equal? rng 'pos)
           (let ((a (simplify (- 0 c1))))
             (and (di-positive? a "a > 0: ∫₀^∞ e^{−ax}")
                  (if (di-p-ok p)
                      (simplify (* e0 (di-gamma (+ p 1)) (di-pow a (- 0 (+ p 1)))))
                      (di-diverges "x^p, p ≤ −1: расходится в нуле")))))
          ((and (equal? rng 'neg) (integer? p) (>= p 0))
           (and (di-positive? c1 "a > 0: ∫_{−∞}^0 e^{ax}")
                (simplify (* e0 (if (di-odd? p) -1 1) (di-fact p) (di-pow c1 (- 0 (+ p 1)))))))
          (else #f))))

; ∫₀^∞ x^n e^{−a x} (cos|sin)(ω x) через Re/Im n!/(a − iω)^{n+1}
(define (di-exp-trig n c0 c1 kind w rng)
  (let ((a (simplify (- 0 c1))) (e0 (simplify (list 'exp c0))))
    (and (equal? rng 'pos) (integer? n) (>= n 0)
         (di-positive? a "a > 0: ∫₀^∞ e^{−ax} cos/sin bx")
         (let* ((z (let loop ((k 0) (acc (cons 1 0)))
                     (if (> k n) acc (loop (+ k 1) (c* acc (cons a w))))))
                (N (di-pow (+ (* a a) (* w w)) (+ n 1)))
                (part (if (equal? kind 'cos) (car z) (cdr z))))
           (simplify (/ (* e0 (di-fact n) part) N))))))

(define (di-dirichlet w rng)
  (let ((sg (di-sign-of w)))
    (cond ((equal? rng 'line) (if sg (* sg 'pi) (simplify (list '* 'pi (list 'sign w)))))
          ((equal? rng 'pos) (if sg (* sg 1/2 'pi) (simplify (list '* 1/2 'pi (list 'sign w)))))
          (else #f))))

; ∫ sin|cos(c x²)
(define (di-fresnel kind c rng)
  (let ((sg (di-sign-of c)))
    (and (or (equal? rng 'pos) (equal? rng 'line))
         (if (equal? sg 0)
             #f
             (let* ((a (if (equal? sg -1) (- 0 c) c))
                    (_ (if sg #t (record-condition (list '> c 0) "a > 0: интеграл Френеля")))
                    (h (simplify (* 1/2 (di-pow (/ 'pi (* 2 a)) 1/2))))
                    (h2 (if (and (equal? kind 'sin) (equal? sg -1)) (- 0 h) h)))
               (if (equal? rng 'line) (simplify (* 2 h2)) h2))))))

; линейные степени: список (s t p) для факторов (s x + t)^p с числовым p; #f если не получается
(define (di-lin-pows fs x)
  (let loop ((l fs) (out '()))
    (if (null? l)
        out
        (let* ((pf (di-pow-form (car l))) (b (car pf)) (p (cdr pf)))
          (cond ((not (di-q? p)) #f)
                ((and (di-head? b '*) (> (length b) 2))
                 (loop (append (map (lambda (u) (list '^ u p)) (cdr b)) (cdr l)) out))
                (else
                 (let ((lin (transforms::tr-lin b x)))
                   (and lin (not (equal? (car lin) 0))
                        (di-q? (car lin)) (di-q? (cdr lin))
                        (loop (cdr l) (cons (list (car lin) (cdr lin) p) out))))))))))

; ∫_a^b ∏ (x−a)^α (b−x)^β: Бета-функция
(define (di-beta lp a b)
  (let loop ((l lp) (al 0) (be 0) (c 1))
    (if (null? l)
        (and (> al -1) (> be -1)
             (simplify (* c (di-gamma (+ al 1)) (di-gamma (+ be 1)) (di-pow (di-gamma (+ al be 2)) -1)
                          (di-pow (- b a) (+ al be 1)))))
        (let* ((s (car (car l))) (t0 (cadr (car l))) (p (caddr (car l))) (r (/ (- 0 t0) s)))
          (cond ((and (= r a) (or (> s 0) (integer? p)))
                 (loop (cdr l) (+ al p) be (* c (di-pow s p))))
                ((and (= r b) (or (< s 0) (integer? p)))
                 (loop (cdr l) al (+ be p) (* c (di-pow (- 0 s) p))))
                (else #f))))))

; ∫₀^∞ x^p (x + c)^{−τ}: c^{p+1−τ} B(p+1, τ−p−1)
(define (di-beta-prime lp)
  (let loop ((l lp) (p 0) (tau #f) (cc #f) (c 1))
    (if (null? l)
        (and tau (> p -1)
             (cond ((<= tau (+ p 1)) (di-diverges "степенное убывание на ∞ не быстрее 1/x"))
                   ((= tau 1)
                    (simplify (* c (di-pow cc p)
                                 (if (integer? (* 2 (+ p 1)))
                                     (* (di-gamma (+ p 1)) (di-gamma (- 0 p)))
                                     (/ 'pi (list 'sin (* 'pi (+ p 1))))))))
                   (else
                    (simplify (* c (di-pow cc (- (+ p 1) tau)) (di-gamma (+ p 1)) (di-gamma (- tau p 1))
                                 (di-pow (di-gamma tau) -1))))))
        (let* ((s (car (car l))) (t0 (cadr (car l))) (e (caddr (car l))))
          (cond ((= t0 0) (loop (cdr l) (+ p e) tau cc (* c (di-pow s e))))
                ((and (not tau) (> s 0) (> (/ t0 s) 0) (< e 0))
                 (loop (cdr l) p (- 0 e) (/ t0 s) (* c (di-pow s e))))
                (else #f))))))

; ∫ f по таблице: один член; fs — множители, зависящие от x
(define (di-table-term fs x rng a b)
  (let* ((xs (filter (lambda (u) (di-xpow u x)) fs))
         (rest1 (filter (lambda (u) (not (di-xpow u x))) fs))
         (es (filter (lambda (u) (di-head? u 'exp)) rest1))
         (ts (filter di-trig-head? rest1))
         (ls (filter (lambda (u) (not (or (di-head? u 'exp) (di-trig-head? u)))) rest1))
         (p (di-sum (map (lambda (u) (di-xpow u x)) xs)))
         (u (if (null? es) 0 (di-sum (map cadr es)))))
    (cond
      ((and (null? ts) (null? ls) (pair? es))
       (and (polynomial? u x)
            (let* ((cs (coefficients u x)) (c0 (di-nth-or cs 0 0)) (c1 (di-nth-or cs 1 0)) (c2 (di-nth-or cs 2 0)))
              (cond ((> (length cs) 3) #f)
                    ((not (equal? c2 0)) (di-gauss p c0 c1 c2 rng))
                    ((not (equal? c1 0)) (di-expl p c0 c1 rng))
                    (else #f)))))
      ((and (= (length ts) 1) (null? ls) (pair? es))
       (let ((lin (transforms::tr-lin (cadr (car ts)) x)) (cs (and (polynomial? u x) (coefficients u x))))
         (and lin (equal? (cdr lin) 0) cs (<= (length cs) 2)
              (di-exp-trig p (di-nth-or cs 0 0) (di-nth-or cs 1 0) (car (car ts)) (car lin) rng))))
      ((and (= (length ts) 1) (null? ls) (null? es))
       (let ((arg (cadr (car ts))) (kind (car (car ts))))
         (let ((lin (transforms::tr-lin arg x)))
           (cond ((and lin (equal? (cdr lin) 0) (equal? kind 'sin) (equal? p -1)) (di-dirichlet (car lin) rng))
                 ((and (equal? p 0) (polynomial? arg x))
                  (let ((cs (coefficients arg x)))
                    (and (= (length cs) 3) (equal? (car cs) 0) (equal? (cadr cs) 0)
                         (di-fresnel kind (caddr cs) rng))))
                 (else #f)))))
      ((and (null? ts) (null? es))
       (let ((lp (di-lin-pows fs x)))
         (and lp (pair? lp)
              (cond ((and (equal? rng 'pos) (di-q? a)) (di-beta-prime lp))
                    ((and (di-q? a) (di-q? b)) (di-beta lp a b))
                    (else #f)))))
      (else #f))))

(define (di-table-route f x a b)
  (or (di-table-run f x a b) (di-table-run (expand f) x a b)))

(define (di-table-run f x a b)
  (let ((rng (di-range a b)))
    (let loop ((l (di-terms f)) (acc 0))
      (if (null? l)
          (simplify acc)
          (let* ((fs (di-factors (car l)))
                 (cs (filter (lambda (u) (di-free? u x)) fs))
                 (rest (filter (lambda (u) (not (di-free? u x))) fs))
                 (v (and (pair? rest) (di-table-term rest x rng a b))))
            (cond ((not v) #f)
                  ((di-head? v 'divergent) v)
                  (else (loop (cdr l) (+ acc (* (di-prod cs) v))))))))))

; ---------- ∫₀^{2π} R(cos θ, sin θ) dθ ----------

(define (di-circ-range? a b)
  (let ((na (di-fl a)) (nb (di-fl b)) (pi (di-pi)))
    (and na nb (not (di-inf? a)) (not (di-inf? b))
         (or (and (< (abs na) 1e-12) (< (abs (- nb (* 2 pi))) 1e-12))
             (and (< (abs (+ na pi)) 1e-12) (< (abs (- nb pi)) 1e-12))))))

; значение корня 'real' r вида (kind k …) внутри единичного круга: -1 вне, 1 внутри, 0 на окружности
(define (di-in-disc r)
  (let ((k (di-kind r)))
    (cond ((equal? k 'lin) (let ((m (abs (caddr r)))) (cond ((< m 1) 1) ((= m 1) 0) (else -1))))
          ((equal? k 'quad) (let ((q (nth r 3))) (cond ((< q 1) 1) ((= q 1) 0) (else -1))))
          (else 2))))

; корень неприводимого множителя g на единичной окружности ⇔ g пропорционален обратному g*(z) = zⁿg(1/z) (точно:
; на окружности корень α даёт и корень 1/α = ᾱ, значит g | g*, а степени равны)
; g неприводим: корень на окружности возможен только у возвратного g = zᵐ h(z + 1/z); тогда он есть ⇔ у h
; вещественный корень строго между −2 и 2 (±2 невозможны — z = ±1 сделали бы g приводимым)
(define (di-high-on-circle? r)
  (and (equal? (di-kind r) 'high)
       (let* ((cs (caddr r)) (rc (reverse cs)) (k (/ (car rc) (car cs))))
         (and (equal? rc (map (lambda (c) (* k c)) cs))
              (even-int? (- (length cs) 1))
              (let* ((m (quotient (- (length cs) 1) 2))
                     (w 'ww)
                     (ss (let loop ((j 1) (prev 2) (cur w) (acc (list w)))
                           (if (>= j m)
                               (reverse acc)
                               (let ((nx (simplify (list '+ (list '* w cur) (list '* -1 prev)))))
                                 (loop (+ j 1) cur nx (cons nx acc))))))
                     (h (simplify (di-sum (cons (nth cs m)
                                                (map2 (lambda (c s) (list '* c s)) (drop cs (+ m 1)) ss)))))
                     (rr (try (real-roots h w) (lambda (e) '()))))
                (any? (lambda (v) (and (< v 2) (> v -2))) rr))))))

; 2π Σ_{|α|<1} Res h, h = P/Q
(define (di-circle-sum pc qc z)
  (let* ((facs (di-classify qc z)) (st (map di-in-disc facs)))
    (cond ((member? 0 st) (di-diverges "полюс подынтегральной функции на окружности |z| = 1"))
          ((not (di-high-simple? facs)) #f)
          ((any? di-high-on-circle? facs) (di-diverges "полюс подынтегральной функции на окружности |z| = 1"))
          (else
           (let loop ((l facs) (tot 0))
             (if (null? l)
                 (simplify (expand (* 2 'pi tot)))
                 (let* ((r (car l)) (k (di-kind r)) (m (di-mult r)))
                   (cond
                     ((equal? k 'high)
                      (let ((v (di-high-sum (caddr r) pc qc 'disc))) (and v (loop (cdr l) (+ tot v)))))
                     ((equal? k 'lin)
                      (loop (cdr l) (if (= (di-in-disc r) 1) (+ tot (nth (di-res-series r pc qc) (- m 1))) tot)))
                     ((equal? k 'quad)
                      (loop (cdr l) (if (= (di-in-disc r) 1) (+ tot (* 2 (car (di-res r pc qc 1)))) tot)))
                     (else
                      (let* ((s (nth (di-res-series r pc qc) (- m 1)))
                             (p (caddr r)) (q (nth r 3)) (sq (di-sqrt (- (* p p) (* 4 q))))
                             (al1 (simplify (/ (+ (- 0 p) sq) 2))) (al2 (simplify (/ (- (- 0 p) sq) 2))))
                        (loop (cdr l)
                              (+ tot
                                 (if (< (abs (di-fl al1)) 1) (+ (car s) (* (cdr s) al1)) 0)
                                 (if (< (abs (di-fl al2)) 1) (+ (car s) (* (cdr s) al2)) 0)))))))))))))

; f = Φ(cc, ss), cc = cos x, ss = sin x (рациональная функция), иначе #f
(define (di-trig-rational f x)
  (let ((g (replace-expr (replace-expr f (list 'sin x) 'ss) (list 'cos x) 'cc)))
    (and (not (contains-sym? g x)) g)))

; нечётная по sin часть интегрируется в 0 (θ → −θ на симметричном периоде): чётная часть
; ½(Φ(cc, ss) + Φ(cc, −ss)) — рациональная в cc после ss² → 1 − cc²; #f, если не получается
(define (di-ss-even-part phi)
  (let* ((ev (simplify (together (* 1/2 (+ phi (subst (list 'ss (list '* -1 'ss)) phi))))))
         (red (lambda (p)
                (and (polynomial? p 'ss)
                     (let* ((cs (coefficients p 'ss)) (idx (range (length cs))))
                       (and (every? (lambda (k) (or (even-int? k) (equal? (nth cs k) 0))) idx)
                            (simplify (di-sum (map (lambda (k) (list '* (nth cs k) (list '^ (list '+ 1 (list '* -1 (list '^ 'cc 2))) (/ k 2))))
                                                   (filter even-int? idx))))))))))
    (if (equal? ev 0)
        0
        (let ((n (red (numer ev))) (d (red (denom ev))))
          (and n d (together (/ n d)))))))

(define (di-circle-route f x a b)
  (and (di-circ-range? a b)
       (let* ((phi (di-trig-rational f x)) (g (and phi (di-ss-even-part phi))))
         (and g
              (if (equal? g 0)
                  (and (equal? (definite-convergence f x a b) 'convergent) 0)
                  (let* ((w (list '* 1/2 (list '+ 'zz (list '^ 'zz -1))))
                         (h (together (/ (replace-expr g 'cc w) 'zz)))
                         (rh (di-rat h 'zz)))
                    (and rh (di-circle-sum (car rh) (cdr rh) 'zz))))))))

; ---------- замочная скважина: ∫₀^∞ x^s R(x) dx и ∫₀^∞ log x · R(x) dx (DI.2) ----------
; Разрез по [0, ∞), arg z ∈ (0, 2π). x^s: (1 − e^{2πis})·I = 2πi·ΣRes(z^s R), т.е.
; I = −π/sin(πs) · Re Σ c·|α|^s·e^{is(θ−π)} (c — коэффициент с биномами C(s,k)). log: ∫ log x·R = −½·Re ΣRes(R log² z).
; Полюса — линейные отрицательные и квадратичные неприводимые без вещественных корней (аргумент — кратное π,
; знаменатель доказывается точно: di-arg-denom); иначе #f.

(define (di-strip0 cs)
  (let loop ((l cs) (k 0))
    (if (and (pair? l) (pair? (cdr l)) (equal? (car l) 0)) (loop (cdr l) (+ k 1)) (cons k l))))

; f = x^s · R(x): (s . R) | #f
(define (di-split-xpow f x)
  (let* ((fs (di-factors f))
         (xs (filter (lambda (u) (di-xpow u x)) fs))
         (rest (filter (lambda (u) (not (di-xpow u x))) fs)))
    (and (pair? xs)
         (let ((s (di-sum (map (lambda (u) (di-xpow u x)) xs))))
           (and (di-q? s) (cons s (simplify (di-prod rest))))))))

; f = log x · R(x): R | #f
(define (di-split-log f x)
  (let* ((fs (di-factors f))
         (ls (filter (lambda (u) (equal? u (list 'log x))) fs))
         (rest (filter (lambda (u) (not (equal? u (list 'log x)))) fs)))
    (and (= (length ls) 1) (simplify (di-prod rest)))))

(define (di-lin? r) (equal? (di-kind r) 'lin))

; W = Σ_{k<m} s_{m−1−k}·C(sx,k)·α^{−k} (элемент поля)
(define (di-w-power r s sx)
  (let* ((o (di-ops-of r)) (m (di-mult r)) (ia ((ops-inv o) (ops-gen o))))
    (let loop ((k 0) (pw ((ops-q o) 1)) (cb 1) (acc (di-zero o)))
      (if (>= k m)
          acc
          (loop (+ k 1) ((ops-mul o) pw ia) (* cb (/ (- sx k) (+ k 1)))
                ((ops-add o) acc ((ops-mul o) (nth s (- m 1 k)) ((ops-mul o) ((ops-q o) cb) pw))))))))

; полюса пригодны? (линейные с r < 0, квадратичные неприводимые без вещественных корней)
(define (di-key-poles-ok? facs)
  (every? (lambda (r) (or (and (di-lin? r) (< (caddr r) 0)) (equal? (di-kind r) 'quad))) facs))

(define (di-keyhole-sum facs pc qc sx)
  (let loop ((l facs) (T 0))
    (if (null? l)
        T
        (let* ((r (car l)) (lin (di-lin? r)) (s (di-res-series r pc qc)) (W (di-w-power r s sx)))
          (let inner ((ss (if lin '(1) '(1 -1))) (T T))
            (if (null? ss)
                (loop (cdr l) T)
                (let ((kk (if lin 1 (di-arg-pi r (car ss)))))
                  (and kk
                       (let* ((c (di-elt->c r W (car ss)))
                              (mag (if lin (di-pow (- 0 (caddr r)) sx) (di-pow (nth r 3) (/ sx 2))))
                              (ang (list '* (* sx (- kk 1)) 'pi))
                              (cs (simplify (list 'cos ang))) (sn (simplify (list 'sin ang))))
                         (inner (cdr ss) (+ T (* mag (- (* (car c) cs) (* (cdr c) sn))))))))))))))

; один элемент списка — сам элемент (для компактной печати шага)
(define (di-one l) (if (and (pair? l) (null? (cdr l))) (car l) l))

; шаг замочной скважины: полюс, вычет R(z)·z^s, Σ и формула с подставленными числами
(define (di-note-keyhole f x facs pc qc sx T r)
  (if (step-log-enabled?)
      (let* ((ls (filter di-lin? facs))
             (qs (filter (lambda (u) (equal? (di-kind u) 'quad)) facs))
             (pis (append (map (lambda (u) (caddr u)) ls)
                          (map (lambda (u) (di-cx (di-root-parts u 1))) qs)))
             (ress (map (lambda (u)
                          (let* ((s (di-res-series u pc qc))
                                 (W (di-w-power u s sx))
                                 (c (di-elt->c u W 1))
                                 (mag (di-pow (- 0 (caddr u)) sx)))
                            (simplify (* mag (di-cx c)))))
                        ls)))
        (record-step 'di-keyhole "Замочная скважина"
                     (string-append "s = " (to-string sx)
                                    "; полюс z = " (di-mp (car pis))
                                    "; вычет R(z)·z^s = " (di-mp (di-one ress))
                                    "; Σ = " (di-mp T)
                                    "; −π/sin(πs)·Σ при s = " (to-string sx) ": " (di-mp r))
                     (list 'integral f x 0 'inf) r 'main)))
  #t)

; ∫₀^∞ x^s R, s нецелое рациональное: значение | (divergent …) | #f
(define (di-keyhole-xpow f x)
  (let ((sp (di-split-xpow f x)))
    (and sp
         (let ((rf (di-rat (cdr sp) x)))
           (and rf
                (let* ((z1 (di-strip0 (car rf))) (z2 (di-strip0 (cdr rf)))
                       (pc (cdr z1)) (qc (cdr z2))
                       (sx (+ (car sp) (car z1) (- 0 (car z2)))))
                  (and (not (integer? sx))
                       (let ((facs (di-classify qc x)))
                         (cond ((<= sx -1) (di-diverges "x^s: s ≤ −1 — расходится в нуле"))
                               ((>= (+ sx (di-deg pc) (- 0 (di-deg qc))) -1)
                                (di-diverges "подынтегральная функция убывает не быстрее 1/x"))
                               ((di-real-poles-in facs x (lambda (r) (>= r 0))) (di-diverges "полюс на [0, ∞)"))
                               ((not (di-key-poles-ok? facs)) #f)
                               (else
                                (let ((T (di-keyhole-sum facs pc qc sx)))
                                  (and T
                                       (begin
                                         (di-note-keyhole f x facs pc qc sx T
                                                          (simplify (* -1 'pi T (di-pow (list 'sin (list '* 'pi sx)) -1))))
                                         (simplify (* -1 'pi T (di-pow (list 'sin (list '* 'pi sx)) -1))))))))))))))))

; Σ Res(R log² z) → (re . im) | #f
(define (di-logkey-sum facs pc qc)
  (let loop ((l facs) (S (cons 0 0)))
    (if (null? l)
        S
        (let* ((r (car l)) (lin (di-lin? r)) (m (di-mult r)) (s (di-res-series r pc qc))
               (o (di-ops-of r)) (ia ((ops-inv o) (ops-gen o))))
          (let inner ((ss (if lin '(1) '(1 -1))) (S S))
            (if (null? ss)
                (loop (cdr l) S)
                (let ((kk (if lin 1 (di-arg-pi r (car ss)))))
                  (and kk
                       (let* ((lnr (if lin (simplify (list 'log (- 0 (caddr r)))) (simplify (list '* 1/2 (list 'log (nth r 3))))))
                              (L (cons lnr (simplify (list '* kk 'pi))))
                              (t0 (c* (di-elt->c r (nth s (- m 1)) (car ss)) (c* L L))))
                         (let kl ((k 1) (pw ia) (H 0) (acc t0))
                           (if (>= k m)
                               (inner (cdr ss) (c+ S acc))
                               (let* ((e ((ops-mul o) (nth s (- m 1 k))
                                                      ((ops-mul o) ((ops-q o) (/ (if (even-int? k) -1 1) k)) pw)))
                                      (ck (di-elt->c r e (car ss)))
                                      (fac (c+ (c* (cons 2 0) L) (cons (* -2 H) 0))))
                                 (kl (+ k 1) ((ops-mul o) pw ia) (+ H (/ 1 k)) (c+ acc (c* ck fac)))))))))))))))

; ∫₀^∞ log x · R(x) dx: значение | (divergent …) | #f
(define (di-keyhole-log f x)
  (let ((R (di-split-log f x)))
    (and R
         (let ((rf (di-rat R x)))
           (and rf
                (let* ((pc (car rf)) (qc (cdr rf)) (facs (di-classify qc x)))
                  (cond ((equal? (car qc) 0) (di-diverges "log x / x в нуле — расходится"))
                        ((< (- (di-deg qc) (di-deg pc)) 2) (di-diverges "подынтегральная функция убывает не быстрее log x / x"))
                        ((di-real-poles-in facs x (lambda (r) (>= r 0))) (di-diverges "полюс на [0, ∞)"))
                        ((not (di-key-poles-ok? facs)) #f)
                        (else
                         (let ((S (di-logkey-sum facs pc qc)))
                           (and S (simplify (* -1/2 (car S)))))))))))))

(define (di-keyhole-route f x a b)
  (and (equal? a 0) (equal? b 'inf)
       (or (di-keyhole-xpow f x) (di-keyhole-log f x))))

; ---------- рациональные функции с параметрами (DI.2) ----------
; Параметры (символы, кроме x, pi, e) предполагаются положительными на время вычисления (declare … reals positive,
; потом снимается); условия «параметр > 0» для входящих в знаменатель — в канал record-condition.
; Поддержаны неприводимые квадратичные множители с доказуемо положительным D = 4q − p² (x² + a², x² + 2bx + b² + c²);
; прямая и чётные подынтегральные на (0, ∞). Остальное — #f.

(define (di-rat-params f x)
  (let* ((g (together f)) (n (numer g)) (d (denom g)) (vs (variables g)))
    (and (polynomial? n x) (polynomial? d x) (not (di-free? d x))
         (every? symbol? vs)
         (let ((ps (filter (lambda (s) (not (or (equal? s x) (member? s '(pi e %i))))) vs)))
           (and (pair? ps)
                (list (coefficients n x) (coefficients d x) ps))))))

; квадратичные множители знаменателя с доказуемо D > 0 (иначе #f)
(define (di-classify-sym qc x)
  (let loop ((l (cdr (factor-list (di-poly qc x)))) (out '()))
    (if (null? l)
        (reverse out)
        (let ((cs (coefficients (car (car l)) x)))
          (and (= (length cs) 3)
               (let* ((a (caddr cs)) (p (simplify (/ (cadr cs) a))) (q (simplify (/ (car cs) a)))
                      (D (simplify (expand (- (* 4 q) (* p p))))))
                 (and (true? (positive? D))
                      (loop (cdr l) (cons (list 'quad (cadr (car l)) p q D) out)))))))))

(define (di-param-line pc qc x)
  (let ((facs (di-classify-sym qc x)))
    (and facs (pair? facs) (>= (- (di-deg qc) (di-deg pc)) 2)
         (let ((tot (foldl (lambda (acc r) (c+ acc (di-res r pc qc 1))) (cons 0 0) facs)))
           (simplify (together (* -2 (cdr tot) 'pi)))))))

; declare на время thunk только тех параметров, у которых деклараций ещё нет
(define (di-with-positive ps thunk)
  (let ((mine (filter (lambda (s) (null? (declarations s))) ps)))
    (unwind-protect
     (begin (for-each (lambda (s) (declare s reals positive)) mine) (thunk))
     (for-each (lambda (s) (undeclare s)) mine))))

(define (di-param-route f x a b)
  (let* ((rng (di-range a b))
         (rp (and (or (equal? rng 'line) (equal? rng 'pos)) (di-rat-params f x))))
    (and rp
         (let* ((ps (caddr rp)) (qc (cadr rp))
                (v (di-with-positive
                    ps
                    (lambda ()
                      (cond ((equal? rng 'line) (di-param-line (car rp) qc x))
                            ((di-even? f x) (let ((w (di-param-line (car rp) qc x))) (and w (simplify (* 1/2 w)))))
                            (else #f))))))
           (and v
                (begin
                  (for-each (lambda (p)
                              (if (contains-sym? (di-poly qc x) p)
                                  (record-condition (list '> p 0) "параметр > 0 (в знаменателе)")
                                  #t))
                            ps)
                  v))))))

; ---------- дифференцирование по параметру (Фейнман) (DI.2) ----------
; ∫ x^p log x · h = ∂/∂c ∫ x^c · h при c = p: интеграл с символьным показателем (таблица), производная по c.

; ψ(q) для натурального и полуцелого q > 0 в замкнутом виде
(define (di-psi-val q)
  (cond ((and (integer? q) (> q 0))
         (simplify (list '+ (let loop ((k 1) (h 0)) (if (>= k q) h (loop (+ k 1) (+ h (/ 1 k))))) (list '* -1 'euler-gamma))))
        ((and (di-q? q) (> q 0) (integer? (- q 1/2)))
         (let ((n (- q 1/2)))
           (simplify (list '+ (let loop ((k 1) (h 0)) (if (> k n) (* 2 h) (loop (+ k 1) (+ h (/ 1 (- (* 2 k) 1))))))
                           (list '* -1 'euler-gamma) (list '* -2 (list 'log 2))))))
        (else #f)))

(define (di-psi-eval e)
  (cond ((not (pair? e)) e)
        ((and (di-head? e 'psi) (= (length e) 2) (di-psi-val (cadr e))) (di-psi-val (cadr e)))
        (else (map di-psi-eval e))))

; (gamma n), n ≤ 0 целое — полюс (производная в вырожденной точке)
(define (di-gamma-pole? e)
  (and (pair? e)
       (or (and (di-head? e 'gamma) (= (length e) 2) (integer? (cadr e)) (<= (cadr e) 0))
           (any? di-gamma-pole? e))))

(define (di-feynman-log f x a b)
  (let* ((fs (di-factors f))
         (lg (filter (lambda (u) (equal? u (list 'log x))) fs)))
    (and (= (length lg) 1)
         (let* ((rest (filter (lambda (u) (not (equal? u (list 'log x)))) fs))
                (xs (filter (lambda (u) (di-xpow u x)) rest))
                (others (filter (lambda (u) (not (di-xpow u x))) rest))
                (p (if (null? xs) 0 (di-sum (map (lambda (u) (di-xpow u x)) xs))))
                (cc 'feynman-c))
           (and (di-q? p) (di-free? (di-prod others) cc)
                (let* ((g (simplify (* (list '^ x (list '+ cc -1)) (di-prod others))))
                       (cap (capture-conditions (lambda () (di-table-route g x a b))))
                       (F (car cap)))
                  (and F (not (di-head? F 'divergent)) (not (contains-sym? F 'integrate))
                       (not (contains-sym? F x))
                       (let ((v (di-psi-eval (simplify (subst (list cc (+ p 1)) (diff cc F))))))
                         (and (> p -1) (not (di-gamma-pole? v))
                              (begin
                                (for-each (lambda (c) (if (contains-sym? (car c) cc) #t (record-condition (car c) (cadr c))))
                                          (cadr cap))
                                (record-condition (list '> p -1) "p > −1: интегрируемость в нуле")
                                v))))))))))

; (definite-feynman f x c a b) — ∂/∂c ∫_a^b f dx как производная замкнутого параметрического ответа | unknown
(define (definite-feynman f x c a b)
  (let ((v (definite-integral f x a b)))
    (if (or (equal? v 'unknown) (di-head? v 'divergent))
        'unknown
        (simplify (diff c v)))))

; ---------- сходимость ----------

(define (di-lim e x p side)
  (let ((r (try (if side (limit e x p side) (limit e x p)) (lambda (er) #f))))
    (cond ((not r) #f)
          ((di-inf? r) r)
          ((di-fl r) r)
          (else #f))))
(define (di-fin? l) (and l (not (di-inf? l))))
(define (di-nonzero? l) (and l (or (di-inf? l) (not (= (di-fl l) 0)))))

; конец конечной точки c (side: plus — справа от c, minus — слева): ok | div | unknown
(define (di-end-finite f x c side)
  (let ((l0 (di-lim f x c side)))
    (if (di-fin? l0)
        'ok
        (let* ((d (if (equal? side 'plus) (list '+ x (list '* -1 c)) (list '+ c (list '* -1 x))))
               (lh (di-lim (simplify (list '* (list '^ d 1/2) f)) x c side)))
          (if (di-fin? lh)
              'ok
              (let ((l1 (di-lim (simplify (list '* d f)) x c side)))
                (if (di-nonzero? l1) 'div 'unknown)))))))

(define (di-osc f x)
  (let* ((fs (di-factors f))
         (tr (filter (lambda (u) (and (di-trig-head? u)
                                      (let ((lin (transforms::tr-lin (cadr u) x))) (and lin (not (equal? (car lin) 0))))))
                     fs)))
    (if (= (length tr) 1)
        (let* ((h (simplify (di-prod (filter (lambda (u) (not (equal? u (car tr)))) fs))))
               (lh (di-lim h x 'inf #f)))
          (cond ((not lh) 'unknown)
                ((di-nonzero? lh) (di-diverges "подынтегральная функция колеблется и не стремится к 0 на бесконечности"))
                (else
                 (let ((m (di-lim (simplify (/ (* x (diff x h)) h)) x 'inf #f)))
                   (if (and (di-fin? m) (< (di-fl m) 0)) 'conditional 'unknown)))))
        'unknown)))

; поведение f на +∞: ok | conditional | divergent | unknown
(define (di-end-inf f x)
  (let ((l2 (di-lim (simplify (list '* (list '^ x 2) f)) x 'inf #f)))
    (if (di-fin? l2)
        'ok
        (let ((l32 (di-lim (simplify (list '* (list '^ x 3/2) f)) x 'inf #f)))
          (if (di-fin? l32)
              'ok
              (let ((l1 (di-lim (simplify (list '* x f)) x 'inf #f)))
                (if (di-nonzero? l1)
                    (di-diverges "подынтегральная функция убывает не быстрее 1/x")
                    (di-osc f x))))))))

(define (di-comb st1 st2)
  (cond ((di-head? st1 'divergent) st1)
        ((di-head? st2 'divergent) st2)
        ((equal? st1 'div) (di-diverges "особенность не интегрируема"))
        ((equal? st2 'div) (di-diverges "особенность не интегрируема"))
        ((or (equal? st1 'unknown) (equal? st2 'unknown)) 'unknown)
        ((or (equal? st1 'conditional) (equal? st2 'conditional)) 'conditional)
        (else 'ok)))

; внутренние вещественные полюса знаменателя (многочлена) на (a, b)
(define (di-interior-poles f x a b)
  (let ((d (denom (together f))))
    (if (and (polynomial? d x) (not (di-free? d x)))
        (let ((rs (try (real-roots d x) (lambda (e) '()))) (na (di-bnum a)) (nb (di-bnum b)))
          (filter (lambda (r) (let ((v (di-fl r))) (and v (< na v) (< v nb)))) rs))
        '())))

(define (di-rat-conv pc qc x a b)
  (let ((facs (di-classify qc x)))
    (cond ((di-real-poles-in facs x (lambda (r) (and (or (equal? a '-inf) (>= r (di-bnum a)))
                                                    (or (equal? b 'inf) (<= r (di-bnum b))))))
           (di-diverges "полюс подынтегральной функции на промежутке интегрирования"))
          ((and (or (di-inf? a) (di-inf? b)) (< (- (di-deg qc) (di-deg pc)) 2))
           (di-diverges "подынтегральная функция убывает не быстрее 1/x"))
          (else 'ok))))

; сходимость: convergent | conditional | (divergent "…") | unknown
(define (definite-convergence f x a b)
  (let* ((g (simplify f)) (rf (di-rat g x)))
    (if rf
        (let ((r (di-rat-conv (car rf) (cdr rf) x a b))) (if (equal? r 'ok) 'convergent r))
        (let* ((s1 (cond ((equal? a '-inf) (di-end-inf (di-subst x (list '* -1 x) g) x))
                         (else (di-end-finite g x a 'plus))))
               (s2 (cond ((equal? b 'inf) (di-end-inf g x))
                         (else (di-end-finite g x b 'minus))))
               (s3 (let loop ((ps (di-interior-poles g x a b)) (st 'ok))
                     (if (null? ps)
                         st
                         (loop (cdr ps)
                               (di-comb st (di-comb (di-end-finite g x (car ps) 'plus)
                                                    (di-end-finite g x (car ps) 'minus)))))))
               (st (di-comb (di-comb s1 s2) s3)))
          (if (equal? st 'ok) 'convergent st)))))

; ---------- Ньютон–Лейбниц ----------

(define (di-oscillatory? f)
  (any? (lambda (h) (contains-sym? f h)) '(sin cos tan cot sec csc sinh cosh tanh)))

(define (di-fallback f x a b)
  (and (not (di-oscillatory? f))
       (let ((r (try (integrate f x a b 'classic) (lambda (e) #f))))
         (and r
              (not (any? (lambda (h) (contains-sym? r h)) '(integrate limit inf undefined nan)))
              r))))

; ---------- главная функция ----------

(define (di-negate v)
  (if (or (di-head? v 'divergent) (equal? v 'unknown)) v (simplify (- 0 v))))

; ---------- шаги (ST.3в-2) ----------
(define (di-mp e) (try (math-print e) (lambda (err) (to-string e))))

; метод выбран: имя маршрута в пояснении, «до ⇒ после»
(define (di-note-method f x a b name r)
  (if (step-log-enabled?)
      (record-step 'di-method "Выбор метода" name (list 'integral f x a b) r 'main))
  #t)

(define (di-note-divergent f x a b cv)
  (if (step-log-enabled?)
      (record-step 'di-divergent "Интеграл расходится"
                   (if (and (pair? cv) (pair? (cdr cv)) (string? (cadr cv)))
                       (cadr cv)
                       "особенность на промежутке интегрирования")
                   (list 'integral f x a b) 'divergent 'main))
  #t)

; Ньютон — Лейбниц: проверка непрерывности и F(b) − F(a) (первообразная — для шага)
(define (di-note-newton f x a b r)
  (let* ((cont (try (definite-continuous? f x a b) (lambda (e) #f)))
         (F (try (integrate f x) (lambda (e) #f))))
    (if (step-log-enabled?)
        (begin
          (record-step 'di-method "Выбор метода"
                       "Ньютон — Лейбниц: особенностей на [a, b] нет, F(b) − F(a)"
                       (list 'integral f x a b) r 'main)
          (if (and F (not (any? (lambda (h) (contains-sym? F h)) '(integrate limit inf undefined nan))))
              (record-step 'di-newton "Формула Ньютона — Лейбница"
                           (string-append "F(x) = " (di-mp F) "; непрерывность на [a, b]: "
                                          (cond ((equal? cont 'closed) "замкнута (нет полюсов и ветвей)")
                                                ((equal? cont 'open) "внутри непрерывна, на конце — односторонний предел")
                                                (else "не подтверждена"))
                                          "; F(b) − F(a)")
                           F r 'main))))
    #t))

; особые точки внутри: найденные точки, вывод (расходится / сумма частей)
(define (di-dedup ps)
  (if (null? ps)
      '()
      (cons (car ps)
            (di-dedup (filter (lambda (q) (not (equal? (simplify (- q (car ps))) 0))) (cdr ps))))))

(define (di-note-singular f x a b pts r)
  (if (step-log-enabled?)
      (let ((ps (di-dedup (or pts (caddr (di-sing-points f x a b (di-fl a) (di-fl b)))))))
        (record-step 'di-singular "Особые точки внутри отрезка"
                     (string-append "найдены точки " (di-mp ps)
                                    "; в каждой — односторонние пределы и порядок полюса"
                                    (if (di-head? r 'divergent) "; интеграл расходится" "; отрезок разбит"))
                     (list 'integral f x a b) r 'main)))
  #t)

(define (di-solve f x a b)
  (let* ((finite (and (not (di-inf? a)) (not (di-inf? b))))
         ; Ньютон — Лейбниц первым на конечном отрезке без особенностей: первообразная и F(b) − F(a)
         (cont (and finite (try (definite-continuous? f x a b) (lambda (e) #f))))
         (newton (and (equal? cont 'closed) (di-fallback f x a b))))
    (if newton
        (begin (di-note-newton f x a b newton) newton)
        (di-solve-routes f x a b))))

(define (di-routes f x a b)
  (list (cons "рациональная функция: первообразная или вычеты"
              (lambda () (di-rational-route f x a b)))
        (cons "параметрический интеграл (вычеты)"
              (lambda () (di-param-route f x a b)))
        (cons "тригонометрическая замена z = e^{ix}: вычеты в круге"
              (lambda () (di-circle-route f x a b)))
        (cons "вычеты в верхней полуплоскости (лемма Жордана)"
              (lambda () (di-fourier-route f x a b)))
        (cons "замочная скважина"
              (lambda () (di-keyhole-route f x a b)))
        (cons "табличный интеграл"
              (lambda () (di-table-route f x a b)))
        (cons "приём Фейнмана (дифференцирование по параметру)"
              (lambda () (di-feynman-log f x a b)))))

; тихий перебор маршрутов: (имя результат thunk) первого сработавшего
(define (di-pick-route f x a b)
  (let loop ((rs (di-routes f x a b)))
    (if (null? rs)
        #f
        (let ((r (call-quietly (lambda () ((cdr (car rs)))))))
          (if r
              (list (car (car rs)) r (cdr (car rs)))
              (loop (cdr rs)))))))

(define (di-solve-routes f x a b)
  (let ((pick (di-pick-route f x a b)))
    (if pick
        (let ((name (car pick)) (r (cadr pick)) (thunk (caddr pick)))
          (cond ((di-head? r 'divergent)
                 (di-note-divergent f x a b r) r)
                ((step-log-enabled?)
                 ; выбор и причина — до шагов самого метода
                 (record-step 'di-method "Выбор метода" name (list 'integral f x a b) r 'main)
                 (thunk))
                (else r)))
        (let ((cv (definite-convergence f x a b)))
          (cond ((di-head? cv 'divergent) (di-note-divergent f x a b cv) cv)
                ((equal? cv 'convergent)
                 ; особые точки внутри проверяются до первообразной (∫ dx/sin²x и т. п.)
                 (let ((iv (try (definite-interior f x a b) (lambda (e) #f))))
                   (cond ((di-head? iv 'divergent)
                          (di-note-singular f x a b #f iv)
                          iv)
                         (iv (di-note-singular f x a b #f iv)
                             iv)
                         (else
                          (let ((nl (di-fallback f x a b)))
                            (if nl (begin (di-note-newton f x a b nl) nl) 'unknown))))))
                (else 'unknown))))))

(define (definite-integral f x a b)
  (let* ((na (di-bnum a)) (nb (di-bnum b)) (g (simplify f)))
    (cond ((and na nb (= na nb)) 0)
          ((equal? g 0) 0)
          ((and na nb (> na nb))
           (with-step ('di-definite "Определённый интеграл" (list 'integral f x a b))
             (di-negate (di-solve g x b a))))
          (else
           (with-step ('di-definite "Определённый интеграл" (list 'integral f x a b))
             (di-solve g x a b))))))

; ---------- сертификат ----------

(define (di-tol) 1/1000)

; iv^ не знает, что квадрат неотрицателен на интервале через 0 — делим в нуле
(define (di-enc g x a b)
  (let ((na (di-fl a)) (nb (di-fl b)))
    (if (and na nb (< na 0) (> nb 0))
        (di-iv-sum (list (di-enc1 g x a 0) (di-enc1 g x 0 b)))
        (di-enc1 g x a b))))

(define (di-enc1 g x a b)
  (try (certified-integral g x a b (di-tol)) (lambda (e) #f)))

(define (di-iv-sum ivs)
  (if (any? (lambda (v) (not v)) ivs) #f (apply iv+ ivs)))

; хвост ∫_T^∞ g dx (sgn = 1) или ∫_{−∞}^{−T} g dx (sgn = −1) подстановкой x = sgn/u: ∫_0^{1/T} g(sgn/u)/u² du
(define (di-tail-rat g x T sgn)
  (let ((gt (try (simplify (together (/ (subst (list x (list '/ sgn 'u)) g) (list '^ 'u 2)))) (lambda (e) #f))))
    (and gt (di-enc gt 'u 0 (/ 1 T)))))

(define (di-rig-rat g x a b)
  (cond ((and (equal? a '-inf) (equal? b 'inf))
         (di-iv-sum (list (di-enc g x -1 1) (di-tail-rat g x 1 1) (di-tail-rat g x 1 -1))))
        ((and (equal? b 'inf) (di-q? a))
         (let ((T (max (+ a 1) 1)))
           (di-iv-sum (list (di-enc g x a T) (di-tail-rat g x T 1)))))
        ((and (equal? a '-inf) (di-q? b))
         (let ((T (max (- 1 b) 1)))
           (di-iv-sum (list (di-enc g x (- 0 T) b) (di-tail-rat g x T -1)))))
        (else #f)))

; g = c · r(x) · e^{u(x)} · (тригонометрия, |·| ≤ 1): (c r-коэффициенты u-коэффициенты) или #f
(define (di-exp-structure g x)
  (let* ((fs (di-factors g))
         (cs (filter (lambda (u) (di-free? u x)) fs))
         (rest (filter (lambda (u) (not (di-free? u x))) fs))
         (es (filter (lambda (u) (di-head? u 'exp)) rest))
         (others (filter (lambda (u) (not (or (di-head? u 'exp) (di-trig-head? u)))) rest))
         (c (di-prod cs)) (u (if (null? es) 0 (di-sum (map cadr es))))
         (r (expand (di-prod others))))
    (and (pair? es) (di-q? c) (polynomial? u x) (polynomial? r x)
         (let ((uc (coefficients u x)) (rc (coefficients r x)))
           (and (<= (length uc) 3) (di-all-q? uc) (di-all-q? rc)
                (let ((c1 (di-nth-or uc 1 0)) (c2 (di-nth-or uc 2 0)))
                  (and (or (< c2 0) (and (= c2 0) (< c1 0)))
                       (list (abs c) rc uc))))))))

; граница ∫_{T0}^∞ |r| e^u ≤ e^{u(T0)} Σ |r_j| j!/λ^{j+1} (u вогнута, λ = −u′(T0) > 0): (T0 . iv) с верхом ≤ 1e-7
(define (di-exp-tail c rc uc)
  (let loop ((T0 1) (n 0))
    (if (> n 40)
        #f
        (let* ((c1 (di-nth-or uc 1 0)) (c2 (di-nth-or uc 2 0)) (c0 (di-nth-or uc 0 0))
               (lam (- 0 (+ c1 (* 2 c2 T0)))))
          (if (<= lam 0)
              (loop (+ T0 1) (+ n 1))
              (let* ((sh (di-taylor (di-ops-lin 0) rc T0))
                     (S (let sl ((l sh) (j 0) (acc 0))
                          (if (null? l) acc (sl (cdr l) (+ j 1) (+ acc (* (abs (car l)) (di-fact j) (^ (/ 1 lam) (+ j 1))))))))
                     (uT (+ c0 (* c1 T0) (* c2 T0 T0)))
                     (B (iv* (iv-exp (iv uT uT)) (iv (* c S) (* c S)))))
                (if (<= (iv-hi B) 1/1000) (cons T0 B) (loop (+ T0 1) (+ n 1)))))))))

(define (di-rig-exp g x a b)
  (let ((st (di-exp-structure g x)))
    (and st
         (let* ((c (car st)) (rc (cadr st)) (uc (caddr st))
                (tr (if (equal? b 'inf) (di-exp-tail c rc uc) (cons b 0)))
                (g2 (simplify (subst (list x (list '* -1 x)) g)))
                (st2 (di-exp-structure g2 x))
                (tl (if (equal? a '-inf) (and st2 (di-exp-tail (car st2) (cadr st2) (caddr st2))) (cons a 0))))
           (and tr tl
                (let* ((hi (if (equal? b 'inf) (car tr) b)) (lo (if (equal? a '-inf) (- 0 (car tl)) a))
                       (head (di-enc g x lo hi))
                       (eb (+ (if (equal? b 'inf) (iv-hi (cdr tr)) 0) (if (equal? a '-inf) (iv-hi (cdr tl)) 0))))
                  (and head (iv+ head (iv (- 0 eb) eb)))))))))

(define (di-rigorous g x a b)
  (cond ((and (not (di-inf? a)) (not (di-inf? b))) (di-enc g x a b))
        ((and (equal? a '-inf) (equal? b 'inf) (equal? (di-parity g x) 'even))
         (let ((E (di-rigorous g x 0 'inf))) (and E (iv* (iv 2 2) E))))
        ((di-rat g x) (di-rig-rat g x a b))
        (else (di-rig-exp g x a b))))

; ---------- численная проверка (не строгая) ----------

(define (di-fun g x) (lambda (t) (let ((r (di-fl (subst (list x t) g)))) (if r r 0.0))))

(define (di-omega g x)
  (let* ((tr (filter di-trig-head? (di-factors g))))
    (if (null? tr)
        #f
        (let ((lin (transforms::tr-lin (cadr (car tr)) x))) (and lin (di-fl (car lin)))))))

(define (di-numeric-check g x a b vf)
  (let* ((L 40.0)
         (lo (if (equal? a '-inf) (- 0.0 L) (di-fl a)))
         (hi (if (equal? b 'inf) L (di-fl b)))
         (h (di-fun g x))
         (ok-end (lambda (c side) (or (di-inf? c) (equal? (di-end-finite g x c side) 'ok))))
         (probe (di-fl (subst (list x (/ (+ lo hi) 2)) g))))
    (cond ((or (not lo) (not hi) (not probe)) 'unknown)
          ((not (and (ok-end a 'plus) (ok-end b 'minus))) 'unknown)
          (else
           (let* ((q1 (di-quad h lo hi 0.25)) (q (di-quad h lo hi 0.125))
                  (qerr (* 3.0 (abs (- q1 q))))
                  (om (di-omega g x))
                  (ends (append (if (equal? a '-inf) (list (- 0.0 L)) '()) (if (equal? b 'inf) (list L) '())))
                  ; хвост на конце e: (оценка . неопределённость); степенной спад C|x|^{-p}: ∫ ≈ h(e)·L/(p−1)
                  (tl (map (lambda (e)
                             (let* ((m (foldl (lambda (mx k) (max mx (abs (h (- e (* (if (> e 0) 1 -1) (* 0.3 k)))))))
                                              0.0 (range 22)))
                                    (he (h e)) (hh (h (/ e 2.0)))
                                    (p (if (and (not (= he 0.0)) (not (= hh 0.0)) (> (* he hh) 0.0))
                                           (/ (log (/ hh he)) (log 2.0))
                                           #f)))
                               (cond (om (cons 0.0 (/ (* 2.0 m) (max (abs om) 0.1))))
                                     ((= he 0.0) (cons 0.0 0.0))
                                     ((and p (> p 1.1)) (cons (/ (* he L) (- p 1.0)) (+ 1e-6 (* 0.25 (abs (/ (* he L) (- p 1.0)))))))
                                     (else (cons 0.0 (* L m))))))
                           ends))
                  (corr (foldl (lambda (acc t) (+ acc (car t))) 0.0 tl))
                  (tail (foldl (lambda (acc t) (+ acc (cdr t))) 0.0 tl))
                  (q (+ q corr)))
             (if (<= (abs (- q vf)) (+ 1e-5 qerr tail)) 'numeric #f))))))

; составная формула Гаусса–Лежандра с шириной панели не больше w
(define (di-quad h lo hi w)
  (let* ((n (max 1 (ceiling (/ (- hi lo) w))))
         (pw (/ (* 1.0 (- hi lo)) n)) (half (/ pw 2))
         (wn (map2 cons laplace::lt-gl-weights laplace::lt-gl-nodes)))
    (let loop ((i 0) (acc 0.0))
      (if (>= i n)
          acc
          (let ((mid (+ lo (* pw (+ i 0.5)))))
            (loop (+ i 1)
                  (+ acc (* half (foldl (lambda (sum p) (+ sum (* (car p) (h (+ mid (* half (cdr p)))))))
                                        0.0 wn)))))))))

(define (di-check1 f x a b v)
  (let* ((g (simplify f)) (vf (di-fl v)))
    (cond ((not vf) 'unknown)
          ((and (di-circ-range? a b) (di-oscillatory? g)) (di-circle-numeric g x a b vf))
          (else
           (let ((cv (definite-convergence g x a b)))
             (if (di-head? cv 'divergent)
                 #f
                 (let ((rig (di-rigorous g x a b)) (V (try (interval::iv-bound (di-prep-v v)) (lambda (e) #f))))
                   (cond ((and rig V)
                          (cond ((iv-subset? V rig) #t)
                                ((or (< (iv-hi V) (iv-lo rig)) (> (iv-lo V) (iv-hi rig))) #f)
                                (else 'numeric)))
                         (else (di-numeric-check g x a b vf))))))))))

; период 2π: правило средних точек экспоненциально точно для аналитической функции; N и 2N должны совпасть
(define (di-circle-numeric g x a b vf)
  (let* ((h (di-fun g x)) (lo (di-fl a)) (hi (di-fl b))
         (mid (lambda (n)
                (let ((st (/ (- hi lo) n)))
                  (let loop ((k 0) (acc 0.0))
                    (if (>= k n) (* acc st) (loop (+ k 1) (+ acc (h (+ lo (* st (+ k 0.5))))))))))))
    (let ((q1 (mid 200)) (q2 (mid 400)))
      (cond ((> (abs (- q1 q2)) 1e-6) 'unknown)
            ((< (abs (- q2 vf)) 1e-6) 'numeric)
            (else #f)))))

; значение для iv-eval: дробные степени → exp(p·log b), (sqrt b) → b^(1/2)
(define (di-prep-v e)
  (cond ((not (pair? e)) e)
        ((and (di-head? e '^) (= (length e) 3) (di-q? (caddr e)) (not (integer? (caddr e))))
         (if (= (denom (caddr e)) 2)
             (list '^ (list 'sqrt (di-prep-v (cadr e))) (* 2 (caddr e)))
             (list 'exp (list '* (caddr e) (list 'log (di-prep-v (cadr e)))))))
        ((and (di-head? e 'sqrt) (= (length e) 2))
         (list 'sqrt (di-prep-v (cadr e))))
        (else (map di-prep-v e))))

; ---------- root-sum с heaviside: численное значение для проверки ----------

(define (di-has-rs? e)
  (and (pair? e) (or (equal? (car e) 'root-sum) (any? di-has-rs? e))))

; (root-sum t Q (* R… (heaviside S))) → (re . im): сумма R(корень) по корням с S > 0 (S: (im t) или 1 − |t|)
; (root-sum t Q (* R… (heaviside S))) → (re . im): сумма R(корень) по корням с S > 0 (S: (im t) или 1 − |t|).
; heaviside нет (свободная сумма по корням, например разность F(b) − F(a) в definite-check) — берутся все корни
(define (di-rs-value rs)
  (let* ((Q (nth rs 2)) (E (nth rs 3))
         (fs (di-factors E))
         (hv (filter (lambda (u) (di-head? u 'heaviside)) fs))
         (rest (filter (lambda (u) (not (di-head? u 'heaviside))) fs))
         (Rc (coefficients (simplify (di-prod rest)) 't))
         (upper? (and (pair? hv) (not (contains-sym? (car hv) 'abs))))
         (rts (map transforms::tr-cplx (nroots Q 't))))
    (foldl (lambda (acc z)
             (let ((m (sqrt (+ (* (car z) (car z)) (* (cdr z) (cdr z))))))
               (if (or (null? hv) (if upper? (> (cdr z) 0) (< m 1)))
                   (let ((v (fc-horner (map (lambda (c) (* 1.0 c)) Rc) z)))
                     (cons (+ (car acc) (car v)) (+ (cdr acc) (cdr v))))
                   acc)))
           (cons 0.0 0.0) rts)))

(define (di-rs-subst e)
  (cond ((not (pair? e)) e)
        ((and (di-head? e 'im) (di-head? (cadr e) 'root-sum)) (cdr (di-rs-value (cadr e))))
        ((di-head? e 'root-sum) (car (di-rs-value e)))
        (else (map di-rs-subst e))))

; (definite-check f x a b v) — сертификат; значение с root-sum проверяется только численно ('numeric)
(define (definite-check f x a b v0)
  (let* ((rs (di-has-rs? v0))
         (r (di-check1 f x a b (if rs (di-rs-subst v0) v0))))
    (if (and rs (equal? r #t)) 'numeric r)))

; ---------- DI.4: особые точки внутри конечного отрезка (тригонометрия, ветви) ----------
; (definite-interior f x a b): #f — внутренних особенностей нет (можно Ньютон–Лейбниц); unknown; (divergent …); либо значение
; (сумма частей по точкам разбиения, каждая часть — классика с пределами на особом конце). Концы — числа/константы.

(define (di-trig-rewrite e)
  (cond ((not (pair? e)) e)
        ((and (di-head? e 'tan) (= (length e) 2)) (let ((u (di-trig-rewrite (cadr e)))) (list '/ (list 'sin u) (list 'cos u))))
        ((and (di-head? e 'cot) (= (length e) 2)) (let ((u (di-trig-rewrite (cadr e)))) (list '/ (list 'cos u) (list 'sin u))))
        ((and (di-head? e 'sec) (= (length e) 2)) (list '/ 1 (list 'cos (di-trig-rewrite (cadr e)))))
        ((and (di-head? e 'csc) (= (length e) 2)) (list '/ 1 (list 'sin (di-trig-rewrite (cadr e)))))
        (else (cons (car e) (map di-trig-rewrite (cdr e))))))

(define (di-ev g x v)
  (let ((r (try (eval-num (subst (list x v) g)) (lambda (er) #f)))) (if (number? r) r #f)))

; числовые нули h на (na, nb): знакопеременные интервалы (бисекция) и точные нули сетки
(define (di-scan-zeros h x na nb)
  (let* ((n 400) (step (/ (- nb na) n)))
    (let loop ((j 1) (prev (di-ev h x (+ na step))) (pp (+ na step)) (acc '()))
      (if (>= j n)
          (reverse acc)
          (let* ((p (+ na (* (+ j 1) step))) (v (if (< (+ j 1) n) (di-ev h x p) #f)))
            (cond ((and prev v (<= (* prev v) 0.0) (not (= v 0.0)) (< (abs prev) 1e30) (< (abs v) 1e30))
                   (loop (+ j 1) v p (cons (di-bisect h x pp p) acc)))
                  ((and prev v (= v 0.0)) (loop (+ j 1) v p (cons p acc)))
                  (else (loop (+ j 1) v p acc))))))))

; нули касания: локальные минимумы |h| на сетке, уточнённые тернарным поиском; нуль, если |h| < 1e-10
(define (di-scan-touch h x na nb)
  (let* ((n 400) (step (/ (- nb na) n))
         (vals (map (lambda (j) (let ((v (di-ev h x (+ na (* j step))))) (if v (abs v) #f))) (range (+ n 1)))))
    (let loop ((j 1) (acc '()))
      (if (>= j n)
          (reverse acc)
          (let ((a0 (nth vals (- j 1))) (a1 (nth vals j)) (a2 (nth vals (+ j 1))))
            (if (and a0 a1 a2 (<= a1 a0) (<= a1 a2) (< a1 1e-2))
                (let ((c (di-ternary h x (+ na (* (- j 1) step)) (+ na (* (+ j 1) step)))))
                  (let ((vc (di-ev h x c)))
                    (loop (+ j 1) (if (and vc (< (abs vc) 1e-10)) (cons c acc) acc))))
                (loop (+ j 1) acc)))))))

(define (di-ternary h x lo hi)
  (let loop ((l lo) (r hi) (i 0))
    (if (> i 100)
        (/ (+ l r) 2.0)
        (let* ((m1 (+ l (/ (- r l) 3.0))) (m2 (- r (/ (- r l) 3.0)))
               (f1 (di-ev h x m1)) (f2 (di-ev h x m2)))
          (if (and f1 f2 (<= (abs f1) (abs f2))) (loop l m2 (+ i 1)) (loop m1 r (+ i 1)))))))

(define (di-bisect h x lo hi)
  (let loop ((l lo) (r hi) (i 0))
    (if (> i 60)
        (/ (+ l r) 2.0)
        (let* ((m (/ (+ l r) 2.0)) (fl (di-ev h x l)) (fm (di-ev h x m)))
          (if (and fl fm (<= (* fl fm) 0.0)) (loop l m (+ i 1)) (loop m r (+ i 1)))))))

; точка → точное k/q·π или рациональное число, если совпало с точностью 1e-9; иначе число
(define (di-snap c)
  (let* ((pi0 (di-pi)))
    (let loop ((qs (map (lambda (k) (+ k 1)) (range 12))))
      (cond ((null? qs) c)
            (else
             (let* ((q (car qs)) (kp (round (* c q (/ 1.0 pi0)))) (kr (round (* c q))))
               (cond ((< (abs (- c (* kp (/ pi0 q)))) 1e-9) (simplify (list '* (/ kp q) 'pi)))
                     ((< (abs (- c (/ kr q))) 1e-9) (/ kr q))
                     (else (loop (cdr qs))))))))))

; аргументы log и степеней с нецелым показателем и чётным знаменателем (ветви, не определённые при u < 0)
(define (di-branch-args e)
  (cond ((not (pair? e)) '())
        ((and (di-head? e 'log) (= (length e) 2)) (cons (cadr e) (di-branch-args (cadr e))))
        ((and (di-head? e '^) (= (length e) 3) (equal? (type-of (caddr e)) 'rational) (even? (denom (caddr e))))
         (cons (cadr e) (di-branch-args (cadr e))))
        (else (append-map di-branch-args (cdr e)))))

(define (di-not-real? g x na nb)
  (let ((n 200))
    (any? (lambda (u)
            (and (not (di-free? u x))
                 (any? (lambda (j) (let ((v (di-ev u x (+ na (* (- nb na) (/ j 1.0 n)))))) (and v (< v -1e-12))))
                       (map (lambda (k) (+ k 1)) (range (- n 1))))))
          (di-branch-args g))))

(define (di-split-sum g x pts a b)
  (let loop ((ps (append (list a) pts (list b))) (acc 0))
    (if (null? (cdr ps))
        (simplify acc)
        (let ((v (try (integrate g x (car ps) (cadr ps) 'classic) (lambda (er) #f))))
          (if (or (not v) (any? (lambda (h) (contains-sym? v h)) '(integrate limit inf -inf undefined nan %i)) (contains-sym? (try (eval-num v) (lambda (er) 0)) '%i))
              'unknown
              (loop (cdr ps) (+ acc v)))))))

; кандидаты в особые точки на (na, nb): (gr facs pts) — подынтегральная после trig-переписывания, множители знаменателя, точки
(define (di-sing-points g x a b na nb)
  (let* ((gr (di-trig-rewrite g))
         (d (try (denom (together gr)) (lambda (er) 1)))
         (rat (di-interior-poles g x a b))
         (facs (di-factors (try (factor d) (lambda (er) d))))
         ; замечание ревью: множитель-степень (sin x)² — нули основания; касание без смены знака (1 − cos x) — локальные
         ; минимумы |h| (di-scan-touch); раньше ∫₁⁴ dx/sin²x давал cot 1 − cot 4 (полюс π внутри пропускался)
         (facs (map (lambda (h) (if (and (pair? h) (di-head? h '^) (= (length h) 3) (integer? (caddr h)) (> (caddr h) 0)) (cadr h) h)) facs))
         (nums (append-map (lambda (h) (if (or (di-free? h x) (polynomial? h x)) '()
                                           (append (di-scan-zeros h x na nb) (di-scan-touch h x na nb)))) facs))
         (nums (filter (lambda (c) (not (any? (lambda (r) (< (abs (- c (di-fl r))) 1e-7)) rat))) nums)))
    (list gr facs (append rat (map di-snap nums)))))

; аргументы функций (atan, log, sin, …) внутри e, рекурсивно, плюс сам e: знаменатели прячутся и в них (atan(cot(x/2)·√3))
(define (di-sources e)
  (if (not (pair? e))
      '()
      (let ((args (append-map di-sources (cdr e))))
        (if (member? (car e) '(+ * / ^ -)) args (append (cdr e) args)))))

; Ньютон — Лейбниц: 'closed — f непрерывна и конечна на замкнутом [a, b] (нет нулей знаменателей внутри и на концах, ветвей
; при u < 0); 'open — то же внутри, но на конце знаменатель обращается в нуль (нужен односторонний предел); #f — иначе
(define (definite-continuous? f x a b)
  (let ((na (di-fl a)) (nb (di-fl b)))
    (and na nb (< na nb) (not (di-inf? a)) (not (di-inf? b))
         (let* ((g (simplify f))
                (rs (map (lambda (u) (di-sing-points u x a b na nb))
                         (filter (lambda (u) (and (pair? u) (not (di-free? u x)))) (cons g (di-sources g))))))
           (and (every? (lambda (r) (and (not (di-not-real? (car r) x na nb)) (null? (caddr r)))) rs)
                (if (every? (lambda (r)
                              (every? (lambda (h) (or (di-free? h x)
                                                      (let ((ha (di-ev h x na)) (hb (di-ev h x nb)))
                                                        (and ha hb (> (abs ha) 1e-9) (> (abs hb) 1e-9)))))
                                      (cadr r)))
                            rs)
                    'closed
                    'open))))))

(define (definite-interior f x a b)
  (let ((na (di-fl a)) (nb (di-fl b)))
    (if (not (and na nb (< na nb) (not (di-inf? a)) (not (di-inf? b))))
        #f
        (let* ((g (simplify f)) (r (di-sing-points g x a b na nb)) (gr (car r)) (pts (caddr r)))
          (cond ((di-not-real? gr x na nb) 'unknown)
                ((null? pts) #f)
                (else
                 (let* ((pts (sort pts (lambda (p q) (< (di-fl p) (di-fl q)))))
                        (st (foldl (lambda (acc c)
                                     (di-comb acc (if (di-fl c)
                                                      (di-comb (di-end-finite g x c 'plus) (di-end-finite g x c 'minus))
                                                      'unknown)))
                                   'ok pts)))
                   (cond ((di-head? st 'divergent) st)
                         ((equal? st 'ok) (di-split-sum g x pts a b))
                         (else 'unknown)))))))))
