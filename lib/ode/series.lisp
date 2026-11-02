; series.lisp — решения линейных ОДУ степенными рядами (шаги ODE.7a/7b)
; Обыкновенная точка: y = Σ a_k (x − x0)^k, свободны a_0…a_{n−1}.
; Регулярная особая точка: y = u^r Σ a_k u^k, u = x − x0; корни определяющего уравнения → показатели.
; Единая лестница коэффициентов: коэффициент при u^{r+J} в L[y] равен
;   Σ_{k≤J} a_k·S(k, J) = 0,   S(k, J) = Σ_m P_{m, μ+m+J−k}·fall(r+k, m),
; где P_m — коэффициент при y⁽ᵐ⁾ (в переменной u), μ = min_m (ord P_m − m), а S(J, J) = I(r+J) —
; определяющий многочлен I(r) = Σ_m P_{m, μ+m}·fall(r, m). Свободные a_J — те, где I(r+J) = 0.
; Замкнутый вид: если отношения a_{J+L}/a_J (L = порядок) рациональны по J — подпоследовательности
; по J mod L дают ₚFq (hyperexpand); принимается только после dsolve-check.
; Сертификат: подстановка усечённого ряда в уравнение → остаток O(u^N) (точно, через series;
; при дробном показателе — замена u = v^q).
(module ode
  (export dsolve-series ode-series-check))

; ---------- доступ к разбору уравнения ----------

(define (se-get pi k)
  (let loop ((xs pi))
    (cond ((null? xs) #f)
          ((equal? (car xs) k) (cadr xs))
          (else (loop (cddr xs))))))

; порядок нуля (или полюса) p в u = 0: целое (может быть < 0) или 'inf
(define (se-ord p u)
  (cond ((ode-zero? p) 'inf)
        (else
         (let ((s (try (series (simplify p) u 0 14) (lambda (e) #f))))
           (if (not s)
               #f
               (let loop ((k -6))
                 (cond ((> k 12) 'inf)
                       ((not (ode-zero? (series-coeff s k))) k)
                       (else (loop (+ k 1))))))))))

; разбор уравнения: линейное однородное, коэффициенты в u = x − x0
; → (:n :u :x0 :p (P_0 … P_n) :mu μ :ss (ряды P_m)) либо #f
(define (se-apply-min xs f)
  (if (null? xs) #f (foldl (lambda (a b) (if (< b a) b a)) (car xs) (cdr xs))))

(define (se-prep eq y x x0)
  (if (not (and (symbol? y) (symbol? x) (number? x0)))
      #f
      (let* ((n (ode-order eq y x))
             (e (ode-normalize eq))
             (ds (map (lambda (k) (if (= k 0) (list y x) (ode-nth-deriv y x k)))
                      (range (+ n 1))))
             (rs (map (lambda (d) (ode-coeff-of d e y x)) ds)))
        (if (or (< n 1) (> n 4) (any? (lambda (r) (not r)) rs))
            #f
            (let* ((as (map car rs))
                   (g (simplify (foldl (lambda (acc p) (list '- acc (list '* (car p) (cadr p))))
                                       e (map2 list as ds)))))
              (if (or (ode-y-node-any? g y x) (not (ode-zero? g)))
                  #f
                  (se-prep-coeffs n x x0 as)))))))

; коэффициенты P_m в u = x − x0, порядки, μ = min_m (ord P_m − m)
(define (se-prep-coeffs n x x0 as)
  (let* ((u (if (= x0 0) x (gensym "u")))
         (ps (map (lambda (a)
                    (simplify (if (equal? u x)
                                  a
                                  (subst (list (list x (list '+ x0 u))) a))))
                  as))
         (ss (map (lambda (pm) (try (series pm u 0 14) (lambda (err) #f))) ps))
         (ords (map (lambda (pm) (se-ord pm u)) ps)))
    (if (any? (lambda (s) (not s)) ss)
        #f
        (let ((mu (se-apply-min
                   (filter (lambda (z) (number? z))
                           (map (lambda (k)
                                  (if (number? (nth ords k))
                                      (- (nth ords k) k)
                                      #f))
                                (range (+ n 1))))
                   #f)))

          (if (or (not mu) (not (number? mu)))
              #f
              (list :n n :x x :u u :x0 x0 :p ps :ords ords :mu mu :ss ss))))))


; коэффициент при u^k в P_m (0 вне диапазона разложения)
(define (se-pcoef pi m k)
  (if (< k 0)
      0
      (let ((s (nth (se-get pi :ss) m)))
        (try (series-coeff s k) (lambda (e) 0)))))

; падающий факториал r(r−1)…(r−m+1)
(define (se-fall r m)
  (let loop ((j 0) (acc 1))
    (if (>= j m) acc (loop (+ j 1) (list '* acc (list '- r j))))))

; определяющий многочлен I(r) = Σ_m P_{m, μ+m}·fall(r, m)
(define (se-ind pi r)
  (let* ((n (se-get pi :n)) (mu (se-get pi :mu)))
    (simplify (foldl (lambda (acc m)
                       (let ((c (se-pcoef pi m (+ mu m))))
                         (if (ode-zero? c)
                             acc
                             (list '+ acc (list '* c (se-fall r m))))))
                     0 (range (+ n 1))))))

; S(k,K) = Σ_m P_{m, μ+K+m−k}·fall(rho+k, m) — множитель при a_k в уравнении степени u^{rho+K}
; S(K,K) = I(rho+K)
(define (se-sval pi rho k K)
  (let* ((n (se-get pi :n)) (mu (se-get pi :mu)))
    (simplify (foldl (lambda (acc m)
                       (let ((c (se-pcoef pi m (+ mu K m (- k)))))
                         (if (ode-zero? c)
                             acc
                             (list '+ acc (list '* c (se-fall (list '+ rho k) m))))))
                     0 (range (+ n 1))))))

; ---------- лестница коэффициентов ----------

; свободные индексы J: I(r+J) = 0 (для обыкновенной точки — 0…n−1)
(define (se-free-indices pi rho limit)
  (let loop ((j 0) (acc '()))
    (if (> j limit)
        (reverse acc)
        (if (ode-zero? (se-ind pi (list '+ rho j)))
            (loop (+ j 1) (cons j acc))
            (loop (+ j 1) acc)))))

; множители при a_j в уравнении степени u^{r+J}: список (j . S(j,J)); excludes свободные
(define (se-eq-terms pi rho j)
  (let loop ((k 0) (acc '()))
    (if (>= k j)
        (reverse acc)
        (let ((s (se-sval pi rho k j)))
          (if (ode-zero? s)
              (loop (+ k 1) acc)
              (loop (+ k 1) (cons (list k s) acc)))))))

; рекуррентность: a_J = −Σ_{j<J} a_j·S(j,J)/I(r+J); #f — I(r+J) = 0 (свободный индекс)
(define (se-cmk pi rho j)
  (let* ((ij (simplify (se-ind pi (list '+ rho j)))))
    (if (ode-zero? ij)
        #f
        (map (lambda (p) (list (car p) (simplify (list '/ (list '- 0 (cadr p)) ij))))
             (se-eq-terms pi rho j)))))

; значения assoc (index . expr); отсутствующий — 0
(define (se-at acc j)
  (let ((p (assoc j acc))) (if p (cdr p) 0)))

; рекуррентность по индексам 0…upto; free — свободные индексы, init — ((j . value) …)
; → assoc (j . expr), упорядоченный по возрастанию j
(define (se-ladder pi rho free upto init)
  (let loop ((j 0) (acc init))
    (cond ((> j upto) (reverse acc))
          ((or (assoc j acc) (member? j free)) (loop (+ j 1) acc))
          (else
           (let ((cs (se-cmk pi rho j)))
             (if (not cs)
                 (reverse acc)
                 (let ((v (simplify (foldl (lambda (s p)
                                             (list '+ s (list '* (cadr p) (se-at acc (car p)))))
                                           0 cs))))
                   (loop (+ j 1) (cons (cons j v) acc)))))))))

; многочлен Σ a_j·u^j по assoc (только ненулевые вклады)
(define (se-poly acc u)
  (simplify (foldl (lambda (s p)
                     (if (ode-zero? (cdr p))
                         s
                         (list '+ s (list '* (cdr p) (list '^ u (car p))))))
                   0 acc)))

; u^rho·(log u)^logpow·Σ — решение Фробениуса
(define (se-ser pi rho acc logpow)
  (let* ((u (se-get pi :u))
         (body (se-poly acc u)))
    (simplify (list '* (list '^ u rho)
                    (if (and logpow (> logpow 0))
                        (list '* (list '^ (list 'log u) logpow) body)
                        body)))))

; ---------- символическая рекуррентность шага L ----------

; S(k, k+L) = Σ_m P_{m, μ+L+m}·fall(rho+k, m) — при K = k+L индекс коэффициента
; μ+L+m не зависит от k, поэтому k может быть символом
(define (se-svalstep pi rho k L)
  (let* ((n (se-get pi :n)) (mu (se-get pi :mu)))
    (simplify (foldl (lambda (acc m)
                       (let ((c (se-pcoef pi m (+ mu L m))))
                         (if (ode-zero? c)
                             acc
                             (list '+ acc (list '* c (se-fall (list '+ rho k) m))))))
                    0 (range (+ n 1))))))

; отношение a_{k+L}/a_k = −S(k,k+L)/I(rho+k+L) как функция символа kk
(define (se-ratio pi rho L)
  (simplify (list '/ (list '- 0 (se-svalstep pi rho 'kk L))
                  (se-ind pi (list '+ rho 'kk L)))))

; рекуррентность двухчленная (только a_{K−L} входит в уравнение степени rho+K)?
(define (se-twostep? pi rho L upto)
  (let loop ((K L))
    (cond ((> K upto) #t)
          ((>= K 24) #t)
          (else
           (let ((ts (se-eq-terms pi rho K)))
             (if (and (= (length ts) 1) (= (car (car ts)) (- K L)))
                 (loop (+ K 1))
                 #f))))))

; линейный множитель poly по m → (lead . α), poly = lead·(m+α); #f если не линейный
(define (se-lin-root poly m)
  (let ((dd (try (degree poly m) (lambda (e) #f))))
    (if (not (= dd 1))
        #f
        (let ((lead (try (coeff poly m 1) (lambda (e) #f)))
              (cst (try (coeff poly m 0) (lambda (e) #f))))
          (if (and lead (not (ode-zero? lead)))
              (cons (simplify lead) (simplify (list '/ cst lead)))
              #f)))))

; разбор factor-list: → (leads . ((α . кратность) …)); #f — есть нелинейный множитель
(define (se-mults fs m)
  (let loop ((xs fs) (acc '()) (ld 1))
    (cond ((null? xs) (cons (simplify ld) (reverse acc)))
          (else
           (let* ((fm (car xs))
                  (lr (se-lin-root (car fm) m)))
             (and lr (loop (cdr xs)
                           (cons (cons (cdr lr) (cadr fm)) acc)
                           (list '* ld (list '^ (car lr) (cadr fm))))))))))

; разложение многочлена p(m) на линейные множители: (c . ((α . кратность) …)), p = c·∏(m+α)^k
; #f — не многочлен по m, степень > 4 или не раскладывается на линейные
(define (se-lin-facts p m)
  (let* ((q (try (expand p) (lambda (e) p)))
         (d (try (degree q m) (lambda (e) #f))))
    (cond ((not d) #f)
          ((= d 0) (cons (simplify q) '()))
          ((> d 4) #f)
          (else
           (let* ((fl (try (factor-list q) (lambda (e) #f)))
                  (ms (and fl (se-mults (cdr fl) m))))
             (and ms (cons (simplify (list '* (car fl) (car ms))) (cdr ms))))))))




; убрать один элемент x из списка
(define (se-del-one x l)
  (cond ((null? l) '())
        ((equal? x (car l)) (cdr l))
        (else (cons (car l) (se-del-one x (cdr l))))))

; развернуть ((α . кратность) …) в список с повторами
(define (se-expand-mult xs)
  (append-map (lambda (p)
                (let loop ((k 0) (acc '()))
                  (if (>= k (cdr p)) acc (loop (+ k 1) (cons (car p) acc)))))
              xs))

; гипергеометрическая форма подпоследовательности b_m = a_{j0+L·m}:
; → (A B z) для hyper A B (z·u^L), либо #f
(define (se-hyper-parts pi rho j0 L)
  (let* ((m (gensym "m"))
         (r (simplify (subst (list (list 'kk (list '+ j0 (list '* L m))))
                             (se-ratio pi rho L))))
         (q (try (together r) (lambda (e) r)))
         (num (try (numer (simplify q)) (lambda (e) #f)))
         (den (try (denom (simplify q)) (lambda (e) #f))))
    (if (or (not num) (not den))
        #f
        (let ((nf (se-lin-facts num m)) (df (se-lin-facts den m)))
          (if (or (not nf) (not df))
              #f
              (let* ((A0 (se-expand-mult (cdr nf)))
                     (B0 (se-expand-mult (cdr df)))
                     ; в определении pFq отношение содержит множитель (m+1) (это k!).
                     ; Обычно он виден как единица в знаменателе: снимаем её. Если её нет —
                     ; k! сократилась с единицей числителя, и эту единицу надо вернуть в A
                     ; (₂F₁(1,1;2;x): r = (m+1)/(m+2) при num = m+1, den = m+2).
                     (has-one (member? 1 B0))
                     (A (if has-one A0 (append A0 (list 1))))
                     (B (if has-one (se-del-one 1 B0) B0)))
                (if (any? (lambda (a) (and (number? a) (<= a 0) (= a (floor a)))) A)
                    #f
                    (list (map simplify A)
                          (map simplify B)
                          (simplify (list '/ (car nf) (car df)))))))))))


; убрать дубликаты из списка (сохраняя порядок)
(define (se-uniq l)
  (let loop ((xs l) (acc '()))
    (cond ((null? xs) (reverse acc))
          ((member? (car xs) acc) (loop (cdr xs) acc))
          (else (loop (cdr xs) (cons (car xs) acc))))))

; ---------- вторая ветвь: y₂ = c·y₁·log u + u^{r2}·Σbₖuᵏ ----------
; y₁ = u^{r1}Σaₖuᵏ (a — готовая лестница при r1). L[c·y₁·log u] = c·u^{r1}·Σ_J R(J)u^J,
; R(J) = Σ_{k≤J} aₖ·∂S(k,J)/∂ρ|_{ρ=r1} (см. тождество L[u^ρΣa] = u^ρ I(ρ)a₀ → ∂/∂ρ).
; Приравнивая коэффициенты при u^{r2+J} (r1 = r2 + N):
;   J = 0    : b₀ свободен (1)
;   0<J<N    : b_J = −m_J/I(r2+J)
;   J = N    : c = −m_N/I'(r1)          (N > 0; c = 0 — лога нет)
;   J > N    : b_J = −(m_J + c·R(J−N))/I(r2+J)
;   N = 0 (равные корни): c = 1, b₀ = 0, b_J = −(m_J + R(J))/I(r+J)
; где m_J = Σ_{k<J} bₖ·S(k,J)|_{ρ=r2}.

; ∂S(k,J)/∂ρ при ρ = rho
(define (se-dsval pi rho k j)
  (simplify (subst (list (list 'rr rho)) (diff 'rr (se-sval pi 'rr k j)))))

; R(J) = Σ_{k≤J} aₖ·∂S(k,J)/∂ρ (a — assoc (k . value))
(define (se-rval pi rho a j)
  (simplify (foldl (lambda (acc k)
                     (let ((d (se-dsval pi rho k j)))
                       (if (ode-zero? d)
                           acc
                           (list '+ acc (list '* (se-at a k) d)))))
                   0 (range (+ j 1)))))

; I'(rho)
(define (se-ind-deriv pi rho)
  (simplify (subst (list (list 'rr rho)) (diff 'rr (se-ind pi 'rr)))))

; m_J для assoc b (k . value) при показателе r2
(define (se-msum pi r2 b j)
  (simplify (foldl (lambda (acc p)
                     (if (>= (car p) j)
                         acc
                         (let ((s (se-sval pi r2 (car p) j)))
                           (if (ode-zero? s)
                               acc
                               (list '+ acc (list '* (cdr p) s))))))
                   0 b)))

; (se-log2 pi r1 r2 N a K) → (c . b-assoc) | #f
(define (se-log2 pi r1 r2 N a K)
  (define (step j b c)
    (let* ((iv (simplify (se-ind pi (list '+ r2 j))))
           (free? (ode-zero? iv))
           (m (se-msum pi r2 b j))
           (rlog (if (>= (- j N) 0) (se-rval pi r1 a (- j N)) 0)))
      (cond ((= j 0) (cons b c))
            ((and free? (= N 0))
             ; равные корни: c = 1 уже задан, b₀ = 0
             (cons (cons (cons j (simplify (list '/ (list '- 0 (simplify (list '+ m rlog)))
                                             iv)))
                         b)
                   c))
            ((and free? (= j N))
             (let ((c2 (simplify (list '/ (list '- 0 m) (se-ind-deriv pi r1)))))
               (cons b c2)))
            (free? #f)
            (else
             (cons (cons (cons j (simplify (list '/ (list '- 0 (simplify (list '+ m
                                                                             (if c
                                                                                 (list '* c rlog)
                                                                                 0))))
                                             iv)))
                         b)
                   c)))))
  (let loop ((j 0) (b (if (= N 0) (list (cons 0 0)) (list (cons 0 1)))) (c (if (= N 0) 1 #f)))
    (if (> j K)
        (if c (cons c b) #f)
        (let ((st (step j b c)))
          (if (not st)
              #f
              (loop (+ j 1) (car st) (cdr st)))))))

; ---------- оператор и сертификат ----------

; n-я производная expr по var
(define (se-diff-n expr var m)
  (let loop ((k 0) (e expr))
    (if (>= k m) e (loop (+ k 1) (simplify (diff var e))))))

; L[expr] = Σ_m P_m·expr⁽ᵐ⁾ в переменной u
(define (se-lop pi expr)
  (let ((n (se-get pi :n)) (u (se-get pi :u)) (ps (se-get pi :p)))
    (simplify (foldl (lambda (acc m)
                       (list '+ acc (list '* (nth ps m) (se-diff-n expr u m))))
                     0 (range (+ n 1))))))

; знаменатели рациональных показателей степеней (^ base e) в e
(define (se-dens e)
  (cond ((pair? e)
         (if (and (equal? (car e) '^) (= (length e) 3))
             (let ((q (caddr e)))
               (append (if (and (number? q) (not (integer? q))) (list (denom q)) '())
                       (se-dens q)))
             (append-map se-dens e)))
        (else '())))

; q — общий знаменатель всех дробных степеней выражения (1 — если нет)
(define (se-q e)
  (let loop ((ds (se-dens e)) (q 1))
    (if (null? ds)
        q
        (let ((d (car ds)))
          (if (equal? (type-of d) 'float) q (loop (cdr ds) (quotient (* q d) (gcd q d))))))))

; разложение L[expr] в u = 0; при дробном показателе — замена u = v^q (после оператора)
; → (ряд . v) либо #f
(define (se-res-series pi expr ord)
  (let* ((u (se-get pi :u))
         (q (se-q expr)))
    (if (= q 1)
        (let ((s (try (series (se-lop pi expr) u 0 ord) (lambda (e) #f))))
          (and s (cons s u)))
        (let* ((v (gensym "v"))
               (res (se-lop pi expr))
               (sub (subst (list (list u (list '^ v q))) res))
               (s (try (series sub v 0 ord) (lambda (e) #f))))
          (and s (cons s v))))))


; точный ноль с раскрытием вложенных сумм (simplify сам не собирает (+ c·(+ a b)) …)
(define (se-zero? z)
  (ode-zero? (simplify (try (expand z) (lambda (e) z)))))

; сертификат: L[expr] = O(u^K) (все коэффициенты до K равны 0)
(define (se-cert pi expr K)
  (let ((rs (se-res-series pi expr (+ K 14))))
    (and rs
         (let ((s (car rs)))
           (let loop ((k 0))
             (cond ((> k K) #t)
                   ((>= k (series-order s)) #t)
                   ((se-zero? (series-coeff s k)) (loop (+ k 1)))
                   (else #f)))))))

; вторая ветвь: u^{r2}Σbₖuᵏ + c·u^{r1}Σaₖuᵏ·log u; #f — не удалось
(define (se-y2 pi r1 r2 N a K)
  (let ((lr (se-log2 pi r1 r2 N a K)))
    (and lr
         (simplify (list '+
                         (se-ser pi r2 (cdr lr) 0)
                         (list '* (car lr) (se-ser pi r1 a 1)))))))

; ---------- определяющее уравнение, корни, случаи ----------

(define (se-roots pi)
  (let* ((ind (se-ind pi 'rr))
         (rs (try (set->list (solve (list '= ind 0) 'rr)) (lambda (e) #f)))
         (d (try (degree (expand ind) 'rr) (lambda (e) #f))))
    (cond ((not rs) #f)
          ; solve вернул один корень, а многочлен второй степени → корень кратности 2
          ((and (= (length rs) 1) (equal? d 2)) (list (car rs) (car rs)))
          ((pair? rs) rs)
          (else #f))))


; обыкновенная точка: P_n не обращается в нуль и все P_m аналитичны
(define (se-ord-point? pi)
  (let* ((n (se-get pi :n))
         (ords (se-get pi :ords)))
    (and (equal? (nth ords n) 0)
         (every? (lambda (o) (or (equal? o 'inf) (and (number? o) (>= o 0)))) ords))))

; регулярная особая точка: ord P_m − m ≥ ord P_n − n при всех m (критерий Фукса)
(define (se-regular? pi)
  (let* ((n (se-get pi :n)) (ords (se-get pi :ords)) (on (nth ords n)))
    (and (number? on) (equal? (se-get pi :mu) (- on n)))))




; шаг рекуррентности L: уравнение степени J содержит только a_{J−L} (или ничего)
; (проверяется до J = upto); #f — рекуррентность не двухчленная
(define (se-step pi rho upto nmax)
  (let loop ((L 1))
    (cond ((> L nmax) #f)
          ((se-twostep? pi rho L upto) L)
          (else (loop (+ L 1))))))

; замкнутый вид подпоследовательности a_{j0+L·m}: u^{rho+j0}·hyper(A;B;z·u^L)
(define (se-closed pi rho j0 L)
  (let ((hp (se-hyper-parts pi rho j0 L)))
    (and hp
         (let* ((u (se-get pi :u))
                (A (car hp)) (B (cadr hp)) (z (caddr hp))
                (arg (simplify (list '* z (list '^ u L)))))
           (simplify (list '* (list '^ u (simplify (list '+ rho j0)))
                           (list 'hyper A B arg)))))))

; ---------- рекуррентность в читаемом виде ----------

; (a_J = Σ c_k·a_k) в виде (J (k c) …) — только ненулевые
(define (se-rec-list pi rho K)
  (let loop ((j 0) (acc '()))
    (if (> j K)
        (reverse acc)
        (let ((cs (if (ode-zero? (se-ind pi (list '+ rho j))) '() (se-cmk pi rho j))))
          (loop (+ j 1) (cons (list j (or cs '())) acc))))))

; ---------- проверка замкнутого вида ----------

; наибольший индекс лестницы acc (порядок элементов не предполагается)
(define (se-maxidx acc)
  (foldl (lambda (a p) (if (> (car p) a) (car p) a)) 0 acc))

; многочлен по подпоследовательности j0, j0+L, … из acc
(define (se-sub-poly acc j0 L u)
  (let ((M (se-maxidx acc)))
    (let loop ((j j0) (s 0))
      (if (> j M)
          (simplify s)
          (loop (+ j L)
                (if (ode-zero? (se-at acc j))
                    s
                    (list '+ s (list '* (se-at acc j) (list '^ u j)))))))))

; проверка: hyper-форма (A B z, шаг L, сдвиг j0) с коэффициентом c совпадает с acc
; (сравниваются коэффициенты подпоследовательности до старшего индекса лестницы)
(define (se-cl-match pi j0 L A B z acc c)
  (let* ((u (se-get pi :u))
         (M (se-maxidx acc))
         (nterm (+ 2 (quotient (- M j0) L)))
         (poly (try (hyper-series (list 'hyper A B (list '* z (list '^ u L))) nterm)
                    (lambda (e) #f)))
         (diff (and poly
                    (try (series (simplify (expand
                                            (list '- (se-sub-poly acc j0 L u)
                                                  (list '* c (list '^ u j0) poly))))
                                 u 0 (+ M 2))
                         (lambda (e) #f)))))
    (and diff
         (let loop ((j j0))
           (cond ((> j M) #t)
                 ((ode-zero? (series-coeff diff j)) (loop (+ j L)))
                 (else #f))))))







; ---------- вещественность, порядок корней, регулярность ----------

; |z| числом (точное значение или приближение); #f — не удалось
(define (se-mod z)
  (let ((s (try (simplify (list 'abs z)) (lambda (e) #f))))
    (if (and s (number? s))
        s
        (let ((v (try (eval-num (list 'abs z)) (lambda (e) #f))))
          (if (and v (number? v) (real? v)) v #f)))))

; радиус сходимости: расстояние от x0 до ближайшей ДРУГОЙ особой точки (корни
; старшего коэффициента, кроме u = 0 — сама точка разложения); нет других → inf
; → число | 'inf | 'unknown
(define (se-radius pi)
  (let* ((n (se-get pi :n)) (u (se-get pi :u))
         (lead (nth (se-get pi :p) n))
         (rs (try (set->list (solve (list '= lead 0) u)) (lambda (e) #f))))
    (if (or (not rs) (null? rs) (not (number? (se-ord lead u))))
        'inf
        (let ((ds (filter (lambda (d) (and d (> d 1e-12))) (map se-mod rs))))
          (cond ((any? (lambda (d) (not d)) (map se-mod rs)) 'unknown)
                ((null? ds) 'inf)
                (else (foldl (lambda (a b) (if (< b a) b a)) (car ds) (cdr ds))))))))

; целая неотрицательная разность r1 − r2; #f иначе
(define (se-int-diff r1 r2)
  (let ((d (try (simplify (list '- r1 r2)) (lambda (e) #f))))
    (and d (integer? d) (>= d 0) d)))

; r1 больше r2 (по численному значению); иначе #f
(define (se-bigger? a b)
  (let ((va (try (eval-num a) (lambda (e) #f)))
        (vb (try (eval-num b) (lambda (e) #f))))
    (and (number? va) (number? vb) (real? va) (real? vb) (> va vb))))

; упорядочить корни: больший первым, если сравнимы
(define (se-order-roots rs)
  (if (and (= (length rs) 2) (se-bigger? (cadr rs) (car rs)))
      (list (cadr rs) (car rs))
      rs))

(define (se-consts k)
  (map (lambda (i) (string->symbol (string-append "C" (to-string (+ i 1))))) (range k)))

; вернуть выражение из переменной u в исходную x (u = x − x0)
(define (se-back-subst pi e)
  (let ((u (se-get pi :u)) (x (se-get pi :x)) (x0 (se-get pi :x0)))
    (if (equal? u x)
        (simplify e)
        (simplify (subst (list (list u (list '- x x0))) e)))))

; hyper → элементарное, если hyperexpand умеет; иначе исходное
(define (se-he e)
  (let ((r (try (hyperexpand e) (lambda (err) e))))
    (try (simplify r) (lambda (err) r))))
; ---------- замкнутый вид ветви ----------

; все коэффициенты подпоследовательности j0, j0+L, j0+2L, … нулевые?
(define (se-sub-zero? acc j0 L)
  (let ((M (se-maxidx acc)))
    (let loop ((j j0))
      (cond ((> j M) #t)
            ((ode-zero? (se-at acc j)) (loop (+ j L)))
            (else #f)))))

; hyper-часть подпоследовательности j0, если она сверена с лестницей; иначе #f
; (нулевая подпоследовательность — это честный 0, а не провал)
(define (se-part pi rho acc j0 L)
  (if (se-sub-zero? acc j0 L)
      0
      (let ((hp (se-hyper-parts pi rho j0 L))
            (c (se-at acc j0)))
        (and hp (not (ode-zero? c))
             (let* ((u (se-get pi :u))
                    (A (car hp)) (B (cadr hp)) (z (caddr hp))
                    (arg (simplify (list '* z (list '^ u L))))
                    (e (simplify (list '* c (list '^ u (simplify (list '+ rho j0)))
                                        (list 'hyper A B arg)))))
               (and (se-cl-match pi j0 L A B z acc c) e))))))


; шаг рекуррентности для готовой лестницы: наименьший L, при котором уравнение
; степени K содержит только a_{K−L}
(define (se-step-of pi rho acc)
  (let ((M (se-maxidx acc)))
    (let loop ((L 1))
      (cond ((> L 4) #f)
            ((se-twostep? pi rho L (+ M 2)) L)
            (else (loop (+ L 1)))))))

; замкнутый вид всей лестницы acc при показателе rho → выражение или #f
(define (se-closed-branch pi rho acc)
  (let ((L (se-step-of pi rho acc)))
    (and L
         (let loop ((j0 0) (parts '()))
           (cond ((>= j0 L)
                  (and (pair? parts)
                       (simplify (foldl (lambda (s p) (list '+ s p)) 0 (reverse parts)))))
                 (else
                  (let ((p (se-part pi rho acc j0 L)))
                    (if p (loop (+ j0 1) (cons p parts)) #f))))))))

; замкнутый вид ветви, прошедший сертификат: hyperexpand → элементарное (численно),
; иначе hyper-форма (остаток усечённого ряда); #f — не распознано или не сертифицируется
(define (se-branch-closed pi rho acc K)
  (let* ((c (se-closed-branch pi rho acc))
         (h (and c (se-he c))))
    (cond ((not c) #f)
          ((and h (not (contains-sym? h 'hyper))
                (or (se-num-cert pi h) (se-cert-best pi (se-hy-sub h 40) K)))
           h)
          ((or (se-num-cert pi c) (se-cert-best pi (se-hy-sub c 40) K)) c)
          (else #f))))

; ---------- численный сертификат (hyper раскрывается в ряд) ----------

; заменить узлы (hyper A B z) на первые n членов ряда
(define (se-hy-sub e n)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'hyper) (= (length e) 4))
         (try (hyper-series e n) (lambda (err) e)))
        (else (map (lambda (z) (se-hy-sub z n)) e))))

; свободные символы выражения, кроме исключённых
(define (se-syms e skip)
  (let loop ((es (list e)) (acc '()))
    (cond ((null? es) (reverse acc))
          ((not (pair? (car es)))
           (if (and (symbol? (car es)) (not (member? (car es) skip))
                    (not (member? (car es) acc)))
               (loop (cdr es) (cons (car es) acc))
               (loop (cdr es) acc)))
          (else (loop (append (cdr (car es)) (cdr es)) acc)))))

; подставить мелкие числа вместо свободных символов (констант) — для численной проверки
(define (se-numify e skip)
  (let ((ss (se-syms e skip)))
    (let loop ((ss ss) (vs (list 1/3 2/5 7/11 5/4)) (binds '()))
      (cond ((null? ss)
             (if (null? binds) e (subst binds e)))
            ((null? vs) (subst binds e))
            (else (loop (cdr ss) (cdr vs) (cons (list (car ss) (car vs)) binds)))))))

; |L[expr]| < 1e-8 в нескольких МАЛЫХ точках (hyper раскрывается усечённо: вдали от нуля
; ошибка усечения ряда велика, поэтому точки порядка 1/50…1/1000)
(define (se-num-cert pi expr)
  (let* ((u (se-get pi :u))
         (res (simplify (se-lop pi (se-numify (se-hy-sub expr 24) (list u))))))
    (let loop ((ts (list 1/50 1/100 1/200 1/500 1/1000)))
      (cond ((null? ts) #t)
            (else
             (let ((v (try (eval-num (subst (list (list u (car ts))) res)) (lambda (e) #f))))
               (if (and (number? v) (real? v) (< (abs v) 1e-8))
                   (loop (cdr ts))
                   #f)))))))




; ---------- сборка объекта результата ----------

(define (se-mk-result sols consts method extra)
  (append (ode-solution 'series sols consts '() 'ok method 'cert-series) extra))

; частное решение (условия Коши заданы) — тип particular
(define (se-mk-particular sols method extra)
  (append (ode-solution 'particular sols '() '() 'ok method 'cert-series) extra))

; сборка ответа: без условий — общее решение; с условиями — подставить значения a₀…a_{n−1}
(define (se-finish sols consts method conds yx extra)
  (if (null? conds)
      (se-mk-result sols consts method extra)
      (se-mk-particular sols method extra)))



(define (se-unknown reason)
  (ode-solution 'unknown '() '() '() reason 'series 'none))

; ---------- начальные данные: константы или условия Коши ----------

; k!
(define (se-fact k)
  (let loop ((i 1) (acc 1))
    (if (> i k) acc (loop (+ i 1) (* acc i)))))

; ((k . значение) …) для индексов 0…n−1: из условий Коши или C1…Cn;
; #f — условия не сводятся к значениям производных в x0
(define (se-init pi n conds yx)
  (let ((x0 (se-get pi :x0)) (y (car yx)) (x (cadr yx)))
    (if (null? conds)
        (map (lambda (k) (cons k (nth (se-consts n) k))) (range n))
        (let ((parsed (map (lambda (c)
                             (if (and (pair? c) (equal? (car c) '=)
                                      *ode-cauchy-loaded* (ca-condition c y x))
                                 (ca-condition c y x)
                                 c))
                           conds)))
          (if (or (any? (lambda (c) (not c)) parsed)
                  (any? (lambda (c) (or (not (number? (cadr c)))
                                        (>= (car c) n)))
                        parsed)
                  (any? (lambda (c) (not (ode-zero? (simplify (list '- (cadr c) x0)))))
                        parsed))
              #f
              ; y⁽ᵏ⁾(x0) = k!·a_k
              (map (lambda (c)
                     (cons (car c) (simplify (list '/ (caddr c) (se-fact (car c))))))
                   parsed))))))

; наибольший K ≤ K0, до которого L[expr] = O(u^K) точно (усечение съедает верхние члены)
(define (se-cert-best pi expr K0)
  (let ((rs (se-res-series pi expr (+ K0 6))))
    (and rs
         (let ((s (car rs)))
           (let loop ((k 0) (best #f))
             (cond ((> k K0) (or best K0))
                   ((>= k (series-order s)) (or best K0))
                   ((se-zero? (series-coeff s k)) (loop (+ k 1) k))
                   (else (or best #f))))))))

(define (se-certK pi U)
  (let ((k (+ U (se-get pi :mu)))) (and (>= k 1) k)))

; ---------- обыкновенная точка ----------

; первые N членов, замкнутый вид при распознавании; сертификат остатка
(define (se-ordinary pi N conds yx)
  (let* ((n (se-get pi :n))
         (u (se-get pi :u))
         (ini (se-init pi n conds yx))
         (U (- N 1))
         (K (and ini (se-certK pi U))))
    (cond ((not ini) (se-unknown "условия Коши не сводятся к значениям производных в точке"))
          ((not K) (se-unknown "слишком мало членов для сертификата остатка"))
          (else
           (let* ((acc (se-ladder pi 0 (range n) U ini))
                  (ser (se-poly acc u))
                  (exact (se-cert-best pi ser K))
                  (closed (se-closed-branch pi 0 acc))
                  (hec (and closed (se-he closed)))
                  (closed2 (and hec (not (contains-sym? hec 'hyper)) hec))
                  (use-closed (and closed (se-num-cert pi (or closed2 closed))))
                  (rhs0 (if use-closed (or closed2 closed) ser)))
             (if (not (or exact use-closed))
                 (se-unknown "ряд не прошёл сертификат остатка")
                 (let ((rec (se-rec-list pi 0 K))
                       (rad (se-radius pi)))
                   (if (step-log-enabled?)
                       (begin
                         (record-step 'ode-se-recurrence "Рекуррентность коэффициентов"
                                      "a_J выражены через предыдущие коэффициенты"
                                      (list 'N U) rec 'detail)
                         (record-step 'ode-se-series "Ряд Тейлора"
                                      (string-append "L[ряд] = O(u^" (to-string exact) ")"
                                                     "; радиус сходимости " (to-string rad)
                                                     (if use-closed "; замкнутый вид распознан" ""))
                                      (list '= 'x (se-get pi :x0)) (se-back-subst pi rhs0) 'main)))
                   (se-finish (list (list '= yx (se-back-subst pi rhs0)))
                              (if (null? conds) (se-consts n) '())
                              'series conds yx
                              (list :radius rad
                                    :recurrence rec
                                    :series (se-back-subst pi ser)
                                    :cert-order exact
                                    :closed-form (if use-closed #t #f))))))))))






; ---------- регулярная особая точка: Фробениус ----------

; ветвь по показателю rho: лестница, первые члены, замкнутый вид (если распознан и сертифицирован)
; → (ladder . closed|#f)
(define (se-branch pi rho K nmax)
  (let ((l (se-ladder pi rho '(0) nmax '((0 . 1)))))
    (and l (cons l (se-branch-closed pi rho l K)))))

; ветвь 1 всегда; вторая — по разности корней (целая → log/вторая ветвь)
(define (se-frobenius pi N conds yx)
  (if (pair? conds)
      (se-unknown "условия Коши в особой точке не поддерживаются: нужен общий ряд")
      (let* ((ind (simplify (se-ind pi 'rr)))
             (raw (se-roots pi)))
        (if (or (not raw) (not (= (length raw) 2)))
            (se-unknown "определяющее уравнение: два корня не найдены")
            (let* ((rs (se-order-roots raw))
                   (r1 (car rs)) (r2 (cadr rs))
                   (K (se-certK pi (- N 1)))
                   (nm (- N 1))
                   (l1 (se-ladder pi r1 '(0) nm '((0 . 1))))
                   (s1 (se-ser pi r1 l1 0))
                   (d (se-int-diff r1 r2))
                   (sep (not d))                    ; корни не отличаются на целое
                   (b2 (and sep (se-branch pi r2 K nm)))
                   (lr (and d (se-log2 pi r1 r2 d l1 nm)))
                   (c2 (and lr (car lr)))
                   (lb (and lr (cdr lr)))
                   (y2 (cond (lr (simplify (list '+
                                                (se-ser pi r2 lb 0)
                                                (list '* c2 (se-ser pi r1 l1 1)))))
                             (d #f)
                             (b2 (se-ser pi r2 (car b2) 0))))
                   (e1 (and K (se-cert-best pi s1 K)))
                   (e2 (and K y2 (se-cert-best pi y2 K)))
                   (exact (and e1 e2))
                   (g1 (and exact (se-branch-closed pi r1 l1 K)))
                   ; вторая ветвь в замкнутом виде: отдельный ряд при r2 (d не целое
                   ; или лог-члена нет: c2 = 0)
                   (g2 (and exact
                            (cond (b2 (cdr b2))
                                  ((and lb (ode-zero? c2))
                                   (se-branch-closed pi r2 lb K))
                                  (else #f))))
                   (v1 (or g1 s1))
                   (v2 (or g2 y2))
                   (rad (se-radius pi))
                   (rec (and K (se-rec-list pi r1 K)))
                   (rhs (and exact (simplify (list '+
                                                  (list '* 'C1 v1)
                                                  (list '* 'C2 v2))))))
              (cond ((not rhs) (se-unknown "ряд не прошёл сертификат остатка"))
                    (else
                     (if (step-log-enabled?)
                         (begin
                           (record-step 'ode-se-indicial "Определяющее уравнение"
                                        (string-append "I(r) = " (ode-mp (expand ind))
                                                       "; корни r₁ = " (ode-mp r1)
                                                       ", r₂ = " (ode-mp r2)
                                                       (if d "; разность целая — вторая ветвь с log u" ""))
                                        (subst (ode-mp-binds) (expand ind))
                                        (list 'list (list '= 'r r1) (list '= 'r r2)) 'main)
                           (record-step 'ode-se-recurrence "Рекуррентность коэффициентов"
                                        "коэффициенты ветви r₁ выражены через предыдущие"
                                        (list 'N nm) rec 'detail)
                           (record-step 'ode-se-series "Ряд Фробениуса"
                                        (string-append "L[ряд] = O(u^" (to-string exact) ")"
                                                       "; радиус сходимости " (to-string rad)
                                                       (if g1 "; замкнутый вид распознан" ""))
                                        (list '= 'x (se-get pi :x0))
                                        (se-back-subst pi (simplify (list '+ (list '* 'C1 s1) (list '* 'C2 y2))))
                                        'main)))
                     (se-finish (list (list '= yx (se-back-subst pi rhs)))
                                (if (null? conds) '(C1 C2) '()) 'frobenius conds yx
                                (list :indicial ind
                                      :exponents (list r1 r2)
                                      :radius rad
                                      :recurrence rec
                                      :series (se-back-subst pi (simplify (list '+ (list '* 'C1 s1) (list '* 'C2 y2))))
                                      :cert-order exact
                                      :closed-form (if g1 #t #f)
                                      :regular #t)))))))))




; ---------- шаги результата (ряд считается тихо, шаги — по полям объекта) ----------

(define (se-record-result r)
  (if (and (pair? r) (equal? (ode-field r :status) 'ok) (step-log-enabled?))
      (begin
        (if (equal? (ode-field r :method) 'frobenius)
            (record-step 'ode-se-indicial "Определяющее уравнение"
                         (string-append "I(r) = " (ode-mp (expand (ode-field r :indicial)))
                                        "; корни: " (ode-mp-list (ode-field r :exponents))
                                        "; вторая ветвь может содержать log u")
                         (subst (ode-mp-binds) (expand (ode-field r :indicial)))
                         (list 'list (list '= 'r (car (ode-field r :exponents)))
                               (list '= 'r (cadr (ode-field r :exponents)))) 'main))
        (record-step 'ode-se-recurrence "Рекуррентность коэффициентов"
                     "коэффициенты ряда выражены через предыдущие"
                     'N (ode-field r :recurrence) 'detail)
        (record-step 'ode-se-series (if (equal? (ode-field r :method) 'frobenius)
                                        "Ряд Фробениуса"
                                        "Ряд Тейлора")
                     (string-append "сертификат остатка L[ряд] = O(u^"
                                    (to-string (ode-field r :cert-order))
                                    ") — проверено по коэффициентам"
                                    "; радиус сходимости " (to-string (ode-field r :radius))
                                    (if (equal? (ode-field r :closed-form) #t)
                                        "; замкнутый вид распознан" ""))
                     '() (ode-field r :series) 'main)))
  r)

; ---------- точка входа ----------

; (dsolve-series eq (y x) [x0] [N] [условия]): N членов ряда в точке x0 (по умолчанию 0 и 8).
; #f — не линейное уравнение охватываемого вида; иначе ode-solution :type series.
(define (dsolve-series eq yx &rest rest)
  (let ((x0 (if (pair? rest) (car rest) 0))
        (N (if (pair? rest) (cadr rest) 8))
        (conds (if (pair? rest) (cddr rest) '())))
    (if (not (and (pair? yx) (= (length yx) 2) (symbol? (car yx)) (symbol? (cadr yx))
                  (number? x0) (number? N) (> N 1)))
        #f
        (let* ((y (car yx)) (x (cadr yx))
               (eq (ode-bare-y->call eq y x))
               (pi (ode-quiet (lambda () (try (se-prep eq y x x0) (lambda (e) #f))))))
          (cond
            ((not pi) #f)
            (else
             (if (step-log-enabled?)
                 (record-step 'ode-se-point "Точка разложения"
                              (string-append "x₀ = " (to-string x0)
                                             "; порядки P_m: "
                                             (ode-mp-join (map (lambda (m) (to-string m))
                                                               (se-get pi :ords)))
                                             "; μ = min(ord P_m − m) = " (to-string (se-get pi :mu))
                                             (cond ((se-ord-point? pi) " ⇒ обыкновенная")
                                                   ((se-regular? pi) " ⇒ регулярная особая (критерий Фукса)")
                                                   (else " ⇒ иррегулярная особая")))
                              (list '= 'x x0) (list '= 'μ (se-get pi :mu)) 'main))
             (cond ((se-ord-point? pi)
                    (se-record-result (ode-quiet (lambda () (se-ordinary pi N conds yx)))))
                   ((se-regular? pi)
                    (se-record-result (ode-quiet (lambda () (se-frobenius pi N conds yx)))))
                   (else (se-unknown "иррегулярная особая точка: метод Фробениуса неприменим")))))))))

; крючок для dsolve: ряд в точке 0; условия Коши применяются сразу (se-init)
(define (se-dsolve-hook eq yx conds)
  (try (let ((r (apply dsolve-series (cons eq (cons yx (cons 0 (cons 10 conds)))))))
         (if (and r (equal? (ode-status r) 'ok)) r #f))
       (lambda (e) #f)))


(define *ode-series-loaded* #t)

; старшая степень по u многочленой части ответа (трансцендентные множители — степени 0):
; #f — есть голое u вне многочлена (напр. в показателе) или отрицательная/дробная степень u
(define (se-pdeg e u)
  (cond ((number? e) 0)
        ((symbol? e) (if (equal? e u) 1 0))
        ((and (pair? e) (equal? (car e) '^) (= (length e) 3)
              (equal? (cadr e) u) (integer? (caddr e)) (>= (caddr e) 0))
         (caddr e))
        ((and (pair? e) (member? (car e) '(+ -)))
         (let loop ((ts (cdr e)) (d #f))
           (cond ((null? ts) d)
                 (else (let ((t (se-pdeg (car ts) u)))
                         (and t (loop (cdr ts) (if (and d (> d t)) d t))))))))
        ((and (pair? e) (equal? (car e) '*))
         (let loop ((ts (cdr e)) (d 0))
           (cond ((null? ts) d)
                 (else (let ((t (se-pdeg (car ts) u)))
                         (and t (loop (cdr ts) (+ d t))))))))
        ; log, hyper, sin, exp, … — функция: трансцендентный множитель степени 0
        ((pair? e) 0)
        (else 0)))

; ---------- сертификат ответа ----------
; Ответ-ряд усечён: печатаются члены до некоторой степени, поэтому L[y] не нуль, а O(u^N).
; Остаток раскладывается по степеням log (узел (log z) → символ t): у log-ветви
; L[y] = A(u) + B(u)·log u + …, и каждая часть проверяется ОТДЕЛЬНО — иначе ошибка
; в одной части маскируется другой (B — это L[y₁] для коэффициента при log, A — остальное).
; Для части k ответа (коэффициент при t^k) с многочленой степенью d_k (hyper/функции —
; степень 0, μ = min_m(ord P_m − m)) усечение даёт остаток O(u^{μ+d_k+1}), поэтому
; требуется нулевой префикс длины ≥ max(μ + d_k + 1, 1). Равенство — норма (усечение
; ровно на границе): подделка со сдвинутым коэффициентом даёт префикс короче (d_k, d_k−1, …).
; Замкнутый вид (в ответе есть hyper): кроме префиксного критерия нужен численный —
; усечённый hyper сам по себе не доказывает тождество (подделка «y₁·log x» проходит префикс).

; замена всех узлов (log z) на символ t
(define (se-log->sym e t)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'log) (= (length e) 2)) t)
        (else (map (lambda (z) (se-log->sym z t)) e))))

; разложение e по степеням t: список коэффициентов от t^0; #f — не разложить
(define (se-parts e t)
  (let ((rt (se-log->sym e t)))
    (cond ((not (contains-sym? rt t)) (list rt))
          (else
           (let ((s (try (series rt t 0 6) (lambda (err) #f))))
             (and s (> (series-order s) 0)
                  (map (lambda (k) (series-coeff s k)) (range (series-order s)))))))))

; нулевой префикс длины ≥ need у ряда expr по u
(define (se-zeroprefix? expr u need)
  (let ((s (try (series expr u 0 (+ need 6)) (lambda (e) #f))))
    (and s
         (let loop ((k 0))
           (cond ((>= k need) #t)
                 ((>= k (series-order s)) #t)
                 ((se-zero? (series-coeff s k)) (loop (+ k 1)))
                 (else #f))))))

; нужная длина нулевого префикса остатка для части ответа степени d (μ — из уравнения)
(define (se-need pi d)
  (let ((k (+ (+ (se-get pi :mu) (or d 0)) 1)))
    (if (< k 1) 1 k)))

; части ответа (rhs) и остатка L[expr] сверяются по степеням log, каждая отдельно
(define (se-cert-parts pi rhs expr u)
  (let* ((t (gensym "lg"))
         (ap (se-parts rhs t))
         (rp (se-parts (se-lop pi expr) t)))
    (and ap rp
         (let loop ((k 0) (ps rp))
           (cond ((null? ps) #t)
                 ((se-zeroprefix? (car ps) u
                                  (se-need pi (and (< k (length ap)) (se-pdeg (nth ap k) u))))
                  (loop (+ k 1) (cdr ps)))
                 (else #f))))))

(define (ode-series-check eq sol yx)
  (let ((chk (try (dsolve-check eq sol yx) (lambda (e) #f))))
    (cond ((equal? chk #t) #t)
          ((not (and (pair? sol) (equal? (car sol) '=) (pair? yx) (= (length yx) 2))) #f)
          (else
           (let* ((y (car yx)) (x (cadr yx))
                  (pi (try (se-prep (ode-bare-y->call eq y x) y x 0) (lambda (e) #f))))
             (and pi
                  (let* ((rhs (caddr sol))
                         (u (se-get pi :u))
                         ; hyper раскрывается на столько членов, чтобы покрыть проверяемый
                         ; префикс; согласованное усечение обеих ветвей
                         (e (se-numify (se-hy-sub rhs 24) (list u))))
                    (cond
                      ; замкнутый вид с головами Бесселя/Эйри/Лежандра — численный сертификат остатка
                      ((se-num-cert pi e) 'numeric)
                      ((and (se-pdeg rhs u)
                            (se-cert-parts pi rhs e u))
                       (if (contains-sym? rhs 'hyper)
                           (and (se-num-cert pi e) 'numeric)
                           'numeric))
                      (else #f)))))))))






