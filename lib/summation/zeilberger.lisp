; summation/zeilberger.lisp — Шаг 21l.5: алгоритм Цайльбергера (creative telescoping).
; Для F(n,k), гипергеометрического по k и по n: многочлены a_0(n)..a_J(n) (не все 0) и
; рациональный R(n,k) с
;   Σ_{j=0}^{J} a_j(n) F(n+j,k) = G(n,k+1) − G(n,k),  G(n,k) = R(n,k)·F(n,k).
; Суммирование по k (естественные границы) ⇒ рекуррентность Σ_j a_j(n) S(n+j) = 0.
; Форма ответа: (recurrence S n (a0 … aJ) rhs ((n0 v0) …)) — diff/subst/eval-num не трогают.
; 21l.5a: форма + проверки (тождество рекуррентности численным оракулом, WZ на ручных
;   сертификатах). Ядро поиска (параметризованный Госпер) — 21l.5b.
; Источники: Петковшек–Вильф–Цейльбергер, A = B, гл. 6–7.

(module summation
  (export recurrence-check recurrence-order wz-prove-identity wz-certificate zeilberger zeilberger-full
          zeilberger-cert-check zb-par-gosper zb-shift-ratio zb-shift-ratios zb-par-numer))



; ---------- проверка рекуррентности численным оракулом ----------

; порядок рекуррентности J = длина коэффициентов − 1
(define (recurrence-order r) (- (length (car (cdr (cdr (cdr r))))) 1))

; (recurrence-check r direct-sum) — r = (recurrence S n (a0 … aJ) rhs ((n0 v0) …)),
; direct-sum = функция n → S(n) (прямым суммированием). Проверяем тождество
; Σ_j a_j(n)·S(n+j) = rhs(n) при n = n0 … n0+J+2 и согласованность начальных значений.
; → #t / #f (ложных «доказано» не даём).
(define (recurrence-check r direct-sum)
  (sum-guard
   (lambda ()
     (let ((init (car (cdr (cdr (cdr (cdr (cdr r))))))))
       (if (null? init)
           (recurrence-check-points r direct-sum (recurrence-start r) (+ (recurrence-order r) 3))
           (and (recurrence-check-init init direct-sum)
                (recurrence-check-points r direct-sum
                                          (car (car init))
                                           (+ (recurrence-order r) 3))))))))

; n0 — старт: первое неотрицательное целое после целых корней старшего коэффициента a_J
(define (recurrence-start r)
  (let* ((coeffs (car (cdr (cdr (cdr r)))))
         (n (car (cdr r)))
         (aJ (recurrence-last coeffs)))
    (if (or (equal? (simplify aJ) 0) (<= (degree aJ n) 0))
        0
        (let ((roots (sum-guard (lambda () (poly-int-roots aJ n)))))
          (if (not roots)
              0
              (recurrence-max-int roots -1))))))

(define (recurrence-last xs) (if (null? (cdr xs)) (car xs) (recurrence-last (cdr xs))))

(define (recurrence-max-int xs cur)
  (if (null? xs)
      cur
      (let ((x (car xs)))
        (recurrence-max-int (cdr xs)
                            (if (and (number? x) (>= x 0) (> x cur)) x cur)))))

; начальные значения: S(n0+i) = v_i должны совпадать с direct-sum
(define (recurrence-check-init init direct-sum)
  (if (null? init)
      #t
      (let* ((pair (car init))
             (v (direct-sum (car pair))))
        (and (number? v)
             (equal? (simplify (list '- v (car (cdr pair)))) 0)
             (recurrence-check-init (cdr init) direct-sum)))))

; тождество в точках n = n0 … n1: Σ a_j(n)·S(n+j) − rhs(n) = 0
(define (recurrence-check-points r direct-sum n0 n1)
  (if (> n0 n1)
      #t
      (let ((v (recurrence-check-point r direct-sum n0)))
        (and v (recurrence-check-points r direct-sum (+ n0 1) n1)))))

(define (recurrence-check-point r direct-sum pt)
  (sum-guard
   (lambda ()
     (let* ((nn (car (cdr (cdr r))))
            (coeffs (car (cdr (cdr (cdr r)))))
            (rhs (car (cdr (cdr (cdr (cdr r))))))
            (lhs (recurrence-lhs coeffs nn pt direct-sum)))
       (and lhs
            (equal? (simplify (list '- lhs (subst (list '= nn pt) rhs))) 0))))))

; Σ_j a_j(n)·S(n+j) при числовом n (все S(n+j) — числа через direct-sum)
(define (recurrence-lhs coeffs n pt direct-sum)
  (recurrence-lhs-loop coeffs n pt 0 0 direct-sum))

(define (recurrence-lhs-loop coeffs n pt j acc direct-sum)
  (if (null? coeffs)
      acc
      (let ((v (direct-sum (+ pt j))))
        (if (not (number? v))
            #f
            ; коэффициент a_j(n0) — число; eval-контекст считает (^ q -1) в рациональное
            (let ((cj (eval-num (eval (zb-subst-sym (car coeffs) n pt)))))
              (if (not (number? cj))
                  #f
                  (recurrence-lhs-loop (cdr coeffs) n pt (+ j 1)
                                       (+ acc (* cj v)) direct-sum)))))))


; ---------- WZ: проверка тождества по ручному сертификату ----------

; ---------- WZ: автоматический сертификат (21l.5, часть 3) ----------

; (wz-certificate F f n k [n0]) → R(n,k) — рациональный сертификат WZ-пары
; (F, f): Σ_k F(n,k) = f(n), G = R·F:
;   F(n+1,k) − F(n,k) = G(n,k+1) − G(n,k)
; Тогда ΣF(n+1) − ΣF(n) = f(n+1) − f(n) суммируется телескопически, и
; тождество сводится к базе n = n0. Путь: Цайльбергер J=1 на нормированном
; терме F̃ = F/f(n); если рекуррентность вырождается в a0·F̃ + a1·F̃(n+1)
; с a0 = −a1 (т.е. S̃(n+1) = S̃(n)), R̃ = R/a1 — искомый сертификат.
; Сертификат проверяется рационально (wz-check-identity); n0 не задан —
; проверяются все базы 0..2, пока сумма сходится (wz-check-base).
; #f — пара не доказана (нет WZ-пары порядка 1 или проверка не прошла).
; базы 0,1,2 подряд (когда n0 не задан) — пока какая-нибудь не сойдётся
(define (wz-check-base-any F f n k)
  (or (wz-check-base F f n k 0)
      (wz-check-base F f n k 1)
      (wz-check-base F f n k 2)))

; ядро wz-certificate: сертификат найден и проверен рационально; базы отдельно
(define (wz-cert-core Ft F f n k)
  (let* ((res (zb-par-gosper Ft n k 1)))
    (if (not (and (pair? res) (pair? (cdr res))))
        #f
        (wz-cert-check Ft F f n k res))))

(define (wz-cert-check Ft F f n k res)
  (let ((a (car res)) (R (cdr res)))
    (if (not (and (list? a) (= (length a) 2)))
        #f
        (wz-cert-try Ft F f n k (car a) (car (cdr a)) R))))

; a0·F̃ + a1·F̃(n+1) = ΔG; при a0 = −a1 → F̃(n+1) − F̃(n) = Δ(R/a1·F̃)
(define (wz-cert-try Ft F f n k a0 a1 R)
  (let ((sum-aa (simplify (together (list '+ a0 a1)))))
    (if (not (equal? sum-aa 0))
        #f
        (let ((Rtilde (simplify (together (list '/ R a1)))))
          (if (wz-check-identity Ft n k Rtilde #f)
              Rtilde
              #f)))))

(define (wz-certificate F f n k &rest n0)
  (sum-guard
   (lambda ()
     (let* ((Ft (list '/ F f))
            (Rtilde (wz-cert-core Ft F f n k)))
       (if (not Rtilde)
           #f
           (if (null? n0)
               (if (wz-check-base-any F f n k) Rtilde #f)
               (if (wz-check-base F f n k (car n0)) Rtilde #f)))))))

; ---------- драйвер zeilberger (21l.5c): перебор J, init, форма ответа ----------

; (zeilberger F n k [max-order]) → форма (recurrence S n (a0…aJ) 0 init) с init =
; ((n0 v0) … (n0+J−1 v_{J−1})) — прямыми суммами; #f/'unsolvable — не найдено.
; Перебор J от 1 до max-order (умолчание 4): первый успешный кандидат
; (полный порядок — все a_j ≠ 0 — предпочитается вырожденному; вырожденный
; принимается только если полный не найден на этом J).
; rhs = 0: естественные границы (терм нулей вне конечного диапазона — сдвиги
; по n не меняют носитель суммы с точностью до нулевых членов).
(define (zeilberger F n k &rest max-order)
  (let ((full (zeilberger-full F n k (if (null? max-order) 4 (car max-order)))))
    (if full (car full) #f)))

; (zeilberger-full F n k [max-order]) → (рекуррентность . R(n,k)) — сертификат
; G(n,k) = R(n,k)·F(n,k), Σ_j a_j(n)·F(n+j,k) = G(n,k+1) − G(n,k); #f — не найдено
(define (zeilberger-full F n k &rest max-order)
  (sum-guard
   (lambda ()
     (zb-driver F n k (if (null? max-order) 4 (car max-order)) 1))))

; (zeilberger-cert-check F n k a R) — независимая проверка сертификата:
; Σ_j a_j(n)·F(n+j,k)/F(n,k) = R(n,k+1)·F(n,k+1)/F(n,k) − R(n,k)
; приводится к рациональной функции и сравнивается с 0; #t/#f (подделка — #f).
(define (zeilberger-cert-check F n k a R)
  (and (list? a) (>= (length a) 2)
       ; замечание ревью ST.3б-3): a ≡ 0, R = 0 — тривиальное тождество 0 = 0, не сертификат
       (not (every? (lambda (c) (equal? (simplify c) 0)) a))
       (sum-guard (lambda () (zb-rec-verified F n k (cons a R))))))

(define (zb-driver F n k Jmax j)
  (if (> j Jmax)
      #f
      (let ((cand (zb-par-gosper F n k j)))
        (if (and (pair? cand) (pair? (cdr cand)))
            (let ((rec (zb-make-recurrence F n k cand)))
              (if rec (cons rec (cdr cand)) (zb-driver F n k Jmax (+ j 1))))
            (zb-driver F n k Jmax (+ j 1))))))

; форма ответа: коэффициенты a_j, init прямыми суммами; #f если init не вычислился
; или численная проверка (прямые суммы, rhs = 0) не прошла — тогда драйвер
; попробует больший J (краевые члены при сдвиге носителя дают неоднородность,
; которую однородная рекуррентность этого J не ловит)
(define (zb-make-recurrence F n k cand)
  (let* ((a (car cand))
         (J (- (length a) 1))
         (n0 (zb-start-of a n))
         (init (zb-initial-values F n k n0 J)))
    (if (not init)
        #f
        (let ((rec (list 'recurrence 'S n a 0 init)))
          (if (and (zb-rec-verified F n k cand)
                   (recurrence-check rec (zb-dsum F n k)))
              rec
              #f)))))

; прямая сумма S(m) по естественным границам (для recurrence-check)
(define (zb-dsum F n k)
  (lambda (m)
    (let ((lo (wz-nat-bound F n k m -1))
          (hi (wz-nat-bound F n k m 1)))
      (if (and lo hi (<= lo hi))
          (wz-direct-sum F n k m lo hi)
          #f))))

; стартовое n0: после целых корней всех a_j (чтобы рекуррентность была корректна
; с первой же точки; консервативно — максимум по всем коэффициентам)
(define (zb-start-of a n)
  (zb-start-loop a n -1))

(define (zb-start-loop a n cur)
  (if (null? a)
      (if (< cur 0) 0 cur)
      (zb-start-loop (cdr a) n
                     (zb-start-max a n cur))))

; нормализация ^-1-форм в /-формы для together ((^ q -1) → (/ 1 q))
(define (zb-inv-to-div e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) (quote ^)) (= (length e) 3)
              (equal? (car (cdr (cdr e))) -1))
         (list '/ 1 (zb-inv-to-div (car (cdr e)))))
        (else (cons (zb-inv-to-div (car e)) (zb-inv-to-div (cdr e))))))

(define (zb-start-max a n cur)
  (let* ((c (car a))
         ; рациональный коэффициент: запрещены и корни числителя (обнуляют a_j),
         ; и полюса знаменателя (не определён); n0 = max(корни ≥ 0, полюса ≥ 0)
         (nd (zb-split (together (zb-inv-to-div c))))
         (num (car nd)) (den (cdr nd)))
    (zb-start-shift num den n cur)))

; корень r запрещает точку r (рекуррентность не нужна в r, но a_j(r)=0 —
; вырожденный шаг; стартуем после всех запретов); полюс p — тем более.
; n0 = max(запрещённая точка + 1 …) с нижней границей 0.
(define (zb-start-shift num den n cur)
  (let ((r1 (zb-int-roots-or num n))
        (r2 (if (number? den) #f (zb-int-roots-or den n))))
    (zb-max-root (if r1 r1 '())
                 (zb-pole-shift (if r2 r2 '()) cur))))

; полюс p запрещает точки ≤ p (a_j не определён): сдвиг на +1 от каждого
(define (zb-pole-shift poles cur)
  (if (null? poles)
      cur
      (let ((p (car poles)))
        (zb-pole-shift (cdr poles)
                       (if (and (number? p) (>= p 0) (> (+ p 1) cur)) (+ p 1) cur)))))

(define (zb-int-roots-or p n)
  (if (or (number? p) (equal? (simplify p) 0))
      #f
      (sum-guard (lambda () (poly-int-roots p n)))))

(define (zb-max-root roots cur)
  (if (null? roots)
      cur
      (let ((x (car roots)))
        (zb-max-root (cdr roots)
                     (if (and (number? x) (>= x 0) (> x cur)) x cur)))))

; начальные значения S(n0..n0+J−1) прямыми суммами по естественным границам
(define (zb-initial-values F n k n0 J)
  (zb-init-loop F n k n0 J 0 '()))

(define (zb-init-loop F n k n0 J i acc)
  (if (= i J)
      (zb-reverse acc)
      (let* ((m (+ n0 i))
             (lo (wz-nat-bound F n k m -1))
             (hi (wz-nat-bound F n k m 1)))
        (if (not (and lo hi))
            #f
            (let ((v (wz-direct-sum F n k m lo hi)))
              (if (not (number? v))
                  #f
                  (zb-init-loop F n k n0 J (+ i 1)
                                (cons (list m v) acc))))))))

; рациональная проверка тождества телескопирования — на отношениях (без
; binomial-правил simplify): делим Σ_j a_j·F(n+j) = G(k+1) − G(k), G = R·F,
; на F(n,k): Σ_j a_j·s_j − (R(k+1)·r_k − R) = 0, s_j = F(n+j)/F(n),
; r_k = F(n,k+1)/F(n,k) — рациональные функции (hyper-ratio/zb-shift-ratios)
(define (zb-rec-verified F n k cand)
  (let* ((a (car cand)) (R (cdr cand))
         (J (- (length a) 1))
         (ratios (zb-shift-ratios F n J))
         (rk (hyper-ratio F k))
         (rk-e (list '/ (car rk) (cdr rk)))
         (R1 (zb-subst-sym R k (list '+ k 1)))
         (lhs (zb-rec-rat-lhs a ratios))
         (diff (simplify (together
                          (list '- lhs
                                (list '- (list '* R1 rk-e) R))))))
    (equal? diff 0)))

; Σ_j a_j·s_j в выражениях (num/den парами ratios)
(define (zb-rec-rat-lhs a ratios)
  (zb-rec-rat-lhs-loop a ratios 0 0))

(define (zb-rec-rat-lhs-loop a ratios j acc)
  (if (null? a)
      acc
      (zb-rec-rat-lhs-loop (cdr a) (cdr ratios) (+ j 1)
                           (expand (simplify
                                    (list '+ acc
                                          (list '* (car a)
                                                (list '/ (car (car ratios))
                                                      (cdr (car ratios))))))))))

; Сертификат R(n,k): F(n+1,k) − F(n,k) = G(n,k+1) − G(n,k), G = R·F.
; Проверка тождества — рациональная (together/simplify = 0), базы — прямая сумма.
; (wz-prove-identity F f n k R n0) → #t (доказано) / #f (сертификат неверен).
; Стиль: hipergeo (Maxima, MIT): wz проверяет F(n+1)−F(n)−G(n,k+1)+G(n,k) = 0.
(define (wz-prove-identity F f n k R n0)
  (sum-guard
   (lambda ()
     (let ((id-ok (wz-check-identity F n k R f)))
       (and id-ok
            (wz-check-base F f n k n0))))))

; рациональная проверка тождества телескопирования: сертификат даётся для
; нормированной пары F̃ = F/f(n) (как эталонная схема wz_certificate): тождество
;   F̃(n+1,k) − F̃(n,k) = G(n,k+1) − G(n,k),  G = R·F̃
; делим на F̃(n,k): r_n − 1 = R(n,k+1)·r_k − R(n,k), где r_n = F̃(n+1,k)/F̃(n,k)
; и r_k = F̃(n,k+1)/F̃(n,k) — рациональные по k (hyper-ratio, Γ-нормализация).
; f = #f — F уже нормирован (F сам есть WZ-пара с f = 1).
(define (wz-check-identity F n k R f)
  (sum-guard
   (lambda ()
     (let* ((Ftilde (if f (list '/ F f) F))
            (rn (hyper-ratio Ftilde n))
            (rk (hyper-ratio Ftilde k))
            (rn-e (list '/ (car rn) (cdr rn)))
            (rk-e (list '/ (car rk) (cdr rk)))
            (R1 (subst (list '= k (list '+ k 1)) R))
            (diff (simplify (together
                             (list '- (list '- rn-e 1)
                                   (list '- (list '* R1 rk-e) R))))))
       (equal? diff 0)))))

; база: Σ_k F(n0,k) по естественным границам = f(n0) (прямым суммированием)
(define (wz-check-base F f n k n0)
  (sum-guard
   (lambda ()
     (let ((rhs (subst (list '= n n0) f)))
       (if (not (number? rhs))
           #f
           (let ((lo (wz-nat-bound F n k n0 -1))
                 (hi (wz-nat-bound F n k n0 1)))
             (and lo hi (<= lo hi)
                  (equal? (simplify
                           (list '- (wz-direct-sum F n k n0 lo hi) rhs))
                          0))))))))

; прямая сумма числовых значений
(define (wz-direct-sum F n k n0 lo hi)
  (wz-direct-loop F n k n0 lo hi 0))

(define (wz-direct-loop F n k n0 lo hi acc)
  (if (> lo hi)
      acc
      (let ((v (wz-num F n k n0 lo)))
        (wz-direct-loop F n k n0 (+ lo 1) hi
                        (if (number? v) (+ acc v) acc)))))

; численное значение F(n0, k0): подстановка чисел и eval (точный путь:
; встроенный binomial для целых аргументов даёт точные целые, в отличие от eval-num)
(define (wz-num F n k n0 k0)
  (sum-guard
   (lambda ()
     (let ((v (eval (subst (list '= k k0) (subst (list '= n n0) F)))))
       (if (number? v) v #f)))))

; естественные границы носителя F(n0, ·): lo — первая ненулевая точка от 0
; вправо, hi — последняя ненулевая (гипергеометрический терм нулей вне конечного
; диапазона; ведущие нули пропускаются — терм вида k·C(n,k); cap 30)
(define (wz-nat-bound F n k n0 step)
  (if (< step 0)
      (wz-nat-lo F n k n0 0 30)
      (wz-nat-hi F n k n0 0 30)))

; первая ненулевая точка от 0 вправо (0, если F(0) ≠ 0)
(define (wz-nat-lo F n k n0 k0 cap)
  (if (= cap 0)
      #f
      (let ((v (wz-num F n k n0 k0)))
        (if (and (number? v) (not (equal? v 0)))
            k0
            (wz-nat-lo F n k n0 (+ k0 1) (- cap 1))))))

; последняя ненулевая точка: пропуск ведущих нулей, затем до первого нуля
(define (wz-nat-hi F n k n0 k0 cap)
  (wz-nat-hi-skip F n k n0 k0 cap 0))

(define (wz-nat-hi-skip F n k n0 k0 cap zeros)
  (if (= cap 0)
      #f
      (let ((v (wz-num F n k n0 k0)))
        (if (and (number? v) (not (equal? v 0)))
            (wz-nat-hi-run F n k n0 k0 cap)
            ; ноль: ведущий — идём дальше; после ненулевых — граница левее
            (if (= zeros 0)
                (wz-nat-hi-skip F n k n0 (+ k0 1) (- cap 1) (+ zeros 1))
                (- k0 1))))))

(define (wz-nat-hi-run F n k n0 k0 cap)
  (if (= cap 0)
      #f
      (let ((v (wz-num F n k n0 k0)))
        (if (and (number? v) (not (equal? v 0)))
            (wz-nat-hi-run F n k n0 (+ k0 1) (- cap 1))
            (- k0 1)))))

; ---------- 21l.5b: ядро Цайльбергера — параметризованный Госпер ----------

; s_j(k) = F(n+j,k)/F(n,k) — рациональная функция от (n,k), пара (num . den).
; s_j = ∏_{i=0}^{j-1} r_n(n+i), где r_n(n+i) = F(n+i+1,k)/F(n+i,k)
; (hyper-ratio по n терма с подставленным n+i; сам hyper-ratio делает сдвиг +1).
(define (zb-shift-ratio F n j)
  (zb-shift-ratio-loop F n j 0 1 1))

(define (zb-shift-ratio-loop F n j i num den)
  (if (= i j)
      (cons (expand (simplify num)) (expand (simplify den)))
      (let* ((Fi (subst (list '= n (list '+ n i)) F))
             (ri (hyper-ratio Fi n)))
        (zb-shift-ratio-loop F n j (+ i 1)
                             (list '* (car ri) num)
                             (list '* (cdr ri) den)))))

; список s_0..s_J (в порядке j)
(define (zb-shift-ratios F n J)
  (zb-shift-ratios-loop F n J J '()))

; разложение выражения в несократимую пару (num . den) — многочлены по k
; (together + разбор /- и ^-форм; числитель — частное без знаменателя)


; факторы пропорциональны с точностью до константы?
(define (zb-prop-factors? f1 f2)
  (let ((q (simplify (together (list (quote /) f1 f2)))))
    (number? q)))

; кратность фактора f в facs (с точностью до константы)
(define (zb-fmult facs f acc)
  (cond ((null? facs) acc)
        ((zb-prop-factors? (car (car facs)) f)
         (zb-fmult (cdr facs) f (+ acc (car (cdr (car facs))))))
        (else (zb-fmult (cdr facs) f acc))))

; сокращение num/den через factor-list; → (num . den)
; общие факторы (с точностью до константы) делятся каждый в своей форме
(define (zb-cancel num den)
  (if (or (number? num) (number? den))
      (cons num den)
      (let* ((fsn (cdr (factor-list num))) (fsd (cdr (factor-list den))))
        (zb-cancel-loop num den fsn fsd))))

(define (zb-cancel-loop num den fsn fsd)
  (cond ((null? fsn) (cons num den))
        (else
         (let* ((f (car (car fsn))) (mn (car (cdr (car fsn))))
                (md (zb-fmult fsd f 0)))
           (if (= md 0)
               (zb-cancel-loop num den (cdr fsn) fsd)
               (let* ((m (min mn md))
                      (gp (zb-find-prop fsd f))
                      (gd (zb-factors-prod (list (cons (car gp) m))))
                      (num2 (zb-poly-exact-div num gd))
                      (den2 (simplify (together (list (quote /) den gd)))))
                 (zb-cancel-loop num2 den2
                                 (zb-drop-prop (cdr fsn) f (- mn m))
                                 fsd)))))))

; найти в facs фактор, пропорциональный f
(define (zb-find-prop facs f)
  (cond ((null? facs) #f)
        ((zb-prop-factors? (car (car facs)) f) (car facs))
        (else (zb-find-prop (cdr facs) f))))

; удалить из facs кратность m у фактора, пропорционального f
(define (zb-drop-prop facs f m)
  (cond ((null? facs) (quote ()))
        ((zb-prop-factors? (car (car facs)) f)
         (let ((mm (- (car (cdr (car facs))) m)))
           (if (<= mm 0)
               (cdr facs)
               (cons (cons (car (car facs)) (list mm)) (cdr facs)))))
        (else (cons (car facs) (zb-drop-prop (cdr facs) f m)))))


; точное деление многочленов через simplify; #f если не делится
(define (zb-poly-exact-div p q)
  (let ((qres (simplify (together (list (quote /) p q)))))
    (let ((t (together qres)))
      (if (and (op-expr? t) (equal? (car t) (quote /)) (= (length t) 3))
          (if (equal? (simplify (car (cdr (cdr t)))) 1)
              (car (cdr t))
              #f)
          qres))))
; произведение факторов с кратностями
(define (zb-factors-prod fs)
  (if (null? fs)
      1
      (expand (simplify (list (quote *) (list (quote ^) (car (car fs)) (cdr (car fs))) (zb-factors-prod (cdr fs)))))))
(define (zb-split x)
  (let ((t (simplify (together x))))
    (cond ((and (op-expr? t) (equal? (car t) (quote /)) (= (length t) 3))
           (cons (car (cdr t)) (car (cdr (cdr t)))))
          ; (* (^ q -1) rest) → num=rest, den=q
          ((and (zb-prod-inv? t) (zb-inv-factor? (car (cdr t))))
           (cons (car (cdr (cdr t))) (car (cdr (car (cdr t))))))
          ; (* rest (^ q -1)) → num=rest, den=q
          ((zb-prod-inv? t)
           (cons (car (cdr t)) (car (cdr (car (cdr (cdr t)))))))
          (else (cons t 1)))))

; список s_0..s_J (в порядке j)
(define (zb-shift-ratios-loop F n J j acc)
  (if (< j 0)
      acc
      (zb-shift-ratios-loop F n J (- j 1) (cons (zb-shift-ratio F n j) acc))))

(define (zb-reverse xs)
  (if (null? xs) '() (zb-append (zb-reverse (cdr xs)) (list (car xs)))))
(define (zb-append xs ys)
  (if (null? xs) ys (cons (car xs) (zb-append (cdr xs) ys))))

; lcm списка многочленов по k: через poly-gcd (lcm(p,q) = p·q/gcd; poly-lcm — builtin
; с другой сигнатурой — lcm(poly, var), не подходит)

; произведение знаменателей (точно кратно каждому; lcm-сокращение отложено до simplify)
(define (zb-prod-dens dens)
  (if (null? dens)
      1
      (expand (simplify (list (quote *) (car dens) (zb-prod-dens (cdr dens)))))))
(define (zb-lcm-list polys k)
  (if (null? polys)
      1
      (zb-lcm-loop (cdr polys) (car polys) k)))

(define (zb-lcm-loop polys acc k)
  (if (null? polys)
      acc
      (zb-lcm-loop (cdr polys) (zb-poly-lcm2 acc (car polys) k) k)))

(define (zb-poly-lcm2 p q k)
  (let ((g (sum-guard (lambda () (poly-gcd p q)))))
    (if (or (not g) (and (number? g) (= g 0)))
        (expand (simplify (list '* p q)))
        (expand (simplify (list '/ (list '* p q) g))))))

; P(k) = Σ_j a_j·num_j·D/den_j — линеен по символьным a_j (имена za0..zaJ)
(define (zb-par-numer ratios D k)
  (zb-par-numer-loop ratios D k 0 0))

; выражение без (^ q -m) — «полиномиальное»
(define (zb-rat-poly? e) (not (zb-has-negpow e)))
(define (zb-has-negpow e)
  (cond ((not (pair? e)) #f)
        ((and (equal? (car e) (quote ^)) (number? (car (cdr (cdr e))))
              (< (car (cdr (cdr e))) 0)) #t)
        (else (or (zb-has-negpow (car e)) (zb-has-negpow (cdr e))))))

(define (zb-par-numer-loop ratios D k j acc)
  (if (null? ratios)
      acc
      (let* ((s (car ratios))
             (aj (string->symbol (string-append "za" (to-string j))))
             ; точный полиномиальный терм: a_j·num_j·(D/den_j); D/den_j — нацело,
             ; но полиномиальное деление чувствительно к форме, поэтому проверяем
             ; результат упрощением: q = simplify(D/den), если полином — берём его
             (q (let ((qq (simplify (together (list (quote /) D (cdr s))))))
                  (if (zb-rat-poly? qq) qq
                      (zb-poly-exact-div D (cdr s)))))
             (term (expand (simplify (list '* aj (car s) q)))))
        (zb-par-numer-loop (cdr ratios) D k (+ j 1)
                           (expand (simplify (list '+ acc term)))))))

; ---------------------------------------------------------------
; (zb-par-gosper F n k J): ищет a_j(n) и сертификат R(k):
;   Σ_j a_j F(n+j,k) = G(k+1) − G(k),  G = R·F.
; Возврат: ((a_0 … a_J) . R) | 'unsolvable | 'unknown | 'no-hyper.
; Алгоритм — эталонная схема telescope: D = lcm знаменателей s_j;
; P(k) = Σ a_j·num_j·D/den_j; ρ = r·D(k)/D(k+1) (r = F(k+1)/F(k));
; gosper-normal(ρ) → A, B, C (не зависят от a_j);
; d = граница степени f (deg C + deg P); f = Σ f_i k^i;
; A·f(k+1) − B(k−1)·f(k) = C·P(k) — однородная линейная система по (f_i, a_j);
; solve; свободная a-переменная фиксируется = 1; ненулевые a_j → ответ.
; Сертификат R = B(k−1)·f/(C·D).
(define (zb-par-gosper F n k J)
  (sum-guard
   (lambda ()
     (let ((r (hyper-ratio F k)))
       (if (not r)
           'no-hyper
           (zb-par-gosper-core F n k J r))))))


; rho = r*D(k)/D(k+1) -> para (num . den)
(define (zb-rho-split r D k)
  (zb-cancel (zb-rho-raw-num r D k) (zb-rho-raw-den r D k)))

(define (zb-rho-raw-num r D k)
  (car (zb-split (simplify (together (zb-rho-frac r D k))))))

(define (zb-rho-raw-den r D k)
  (cdr (zb-split (simplify (together (zb-rho-frac r D k))))))

(define (zb-rho-frac r D k)
  (list (quote /) (list (quote *) (car r) D)
        (list (quote *) (cdr r) (poly-shift D k 1))))

(define (zb-par-gosper-core F n k J r)
  (let* ((ratios (zb-shift-ratios F n J))
         (dens (map cdr ratios))
         (D (zb-lcm-list dens k))
         (P (zb-par-numer ratios D k))
         (rho-split (zb-rho-split r D k))
         (rho-num (car rho-split))
         (rho-den (cdr rho-split)))
    (if (not (and (number? (degree P k)) (>= (degree P k) 0)))
        (quote unknown)
        (let ((nbc (gosper-normal rho-num rho-den k)))
          (if (and (pair? nbc) (pair? (car nbc)) (equal? (car (car nbc)) (quote param-lc)))
              (quote unknown)
              (zb-par-gosper-solve (car (car nbc)) (cdr (car nbc)) (cdr nbc)
                                   P D k J n F))))))
(define (zb-par-gosper-solve A B C P D k J n F)
  (let* ((Bm1 (poly-shift B k -1))
         (degP (degree P k))
         (K (degree C k))
         (N (degree A k))
         (M (degree Bm1 k))
         (d (gosper-degree-bound A Bm1 C N M (+ K degP) k)))
    (if (or (not d) (< d 0))
        'unsolvable
         (zb-par-gosper-ansatz A Bm1 C P D k J n d F))))

; максимум трёх чисел (или #f)
(define (zb-max3 a b c)
  (max (max (if (number? a) a -1) (if (number? b) b -1)) (if (number? c) c -1)))

; анзац и система: E = A·f(k+1) − B(k−1)·f(k) − C·P(k); coeff по k → уравнения
(define (zb-par-gosper-ansatz A Bm1 C P D k J n d F)
  (let* ((fnames (zb-coef-names "zf" d))
         (anames (zb-coef-names "za" J))
         (f (zb-ansatz fnames k))
         (f1 (expand (simplify (subst (list (quote =) k (list (quote +) k 1)) f))))
         (t1 (expand (simplify (list (quote *) A f1))))
         (t2 (expand (simplify (list (quote *) Bm1 f))))
         (t3 (expand (simplify (list (quote *) C P))))
         (E (expand (simplify (list (quote -) (list (quote -) t1 t2) t3))))
         (degE (zb-max3 (degree t1 k) (degree t2 k) (degree t3 k)))
         (eqs (zb-eqs E degE k))
         (unknowns (zb-append fnames anames))
         (sols (sum-guard (lambda () (solve eqs unknowns)))))
    (cond ((not sols) (quote unknown))
          ((null? sols) (quote unsolvable))
          (else (zb-par-gosper-extract sols fnames anames Bm1 C D k J n F)))))

; имена prefix+i
(define (zb-coef-names prefix d)
  (if (< d 0)
      '()
      (zb-append (zb-coef-names prefix (- d 1))
                 (list (string->symbol (string-append prefix (to-string d)))))))

(define (zb-ansatz names k)
  (zb-ansatz-loop names 0 0 k))
(define (zb-ansatz-loop ns i acc k)
  (if (null? ns)
      acc
      (zb-ansatz-loop (cdr ns) (+ i 1)
                       (expand (simplify (list '+ acc
                                        (list '* (car ns) (list '^ k i))))) k)))
; уравнения coeff(E, k, i) = 0 (i = D..0, ненулевые)
(define (zb-eqs E D k)
  (if (< D 0)
      '()
      (let ((ci (coeff E k D)))
        (if (equal? ci 0)
            (zb-eqs E (- D 1) k)
            (cons (list '= ci 0) (zb-eqs E (- D 1) k))))))

; извлечение решения: alist (= sym val); свободная переменная — та, чьё значение
; равно ей самой (solve оставляет её символом). Фиксируем свободную a_j = 1,
; подставляем во все значения, собираем a_j и f; если все a_j = 0 — 'unsolvable.
; кандидаты: для каждой свободной a (fix=1, прочие свободные 0) → (avals . fvals)
(define (zb-candidates alist fnames anames)
  (let ((free (zb-free-vars alist anames)))
    (if (null? free)
        (quote ())
        (zb-cand-loop alist fnames anames free))))

(define (zb-cand-loop alist fnames anames free)
  (zb-cand-loop2 alist fnames anames free free))

(define (zb-cand-loop2 alist fnames anames free all)
  (if (null? free)
      (quote ())
      (let* ((al (zb-fix-free alist (car free) (zb-remove-first (car free) all)))
              (av (zb-lookup-list anames al))
              (fv (zb-lookup-list fnames al)))
        (if (zb-all-zero? av)
            (zb-cand-loop2 alist fnames anames (cdr free) all)
            (cons (cons av fv) (zb-cand-loop2 alist fnames anames (cdr free) all))))))

(define (zb-remove-first x xs)
  (cond ((null? xs) (quote ()))
        ((equal? (car xs) x) (cdr xs))
        (else (cons (car xs) (zb-remove-first x (cdr xs))))))

; extract: берёт кандидатов, выбирает первый, прошедший численную проверку
(define (zb-par-gosper-extract sols fnames anames Bm1 C D k J n F)
  (let* ((alist (zb-sols-alist sols))
         (cands (zb-candidates alist fnames anames)))
    (if (null? cands)
        (quote unsolvable)
        (zb-try-candidates cands Bm1 C D k n F))))

(define (zb-try-candidates cands Bm1 C D k n F)
  (if (null? cands)
      (quote unsolvable)
      (let ((r (zb-normalized (car (car cands)) (cdr (car cands)) Bm1 C D k n)))
        (if (or (not (pair? r)) (equal? r (quote unsolvable)))
            (zb-try-candidates (cdr cands) Bm1 C D k n F)
            (if (zb-check-solution r F Bm1 C D k n)
                r
                (zb-try-candidates (cdr cands) Bm1 C D k n F))))))

; численная проверка рекуррентности сумм: Σ_j a_j(n)·S(n+j) ≈ 0,
; S(m) = Σ_k F(m,k) — прямая конечная сумма (гипергео-члены обнуляются)
(define (zb-check-solution r F Bm1 C D k n)
  (let ((a (car r)))
    (and (pair? a)
         (zb-check-recur a F n 5))))

(define (zb-check-recur a F n nv)
  (let ((J (length a)))
    (zb-check-recur-at a F n nv (+ nv J 3))))

; сумма k=0..K F(n+j,k) численно
(define (zb-num-sum F n m K)
  (zb-num-sum-loop F n m 0 K 0))

(define (zb-num-sum-loop F n m k K acc)
  (if (> k K)
      acc
      (zb-num-sum-loop F n m (+ k 1) K
        (+ acc (eval-num (eval (zb-subst-sym (zb-subst-sym F n m) 'k k)))))))

; Σ_j a_j(n)·S(n+j) — численно; допуск для double
(define (zb-check-recur-at a F n nv K)
  (let ((s (zb-recur-sum a F n nv K)))
    (and (number? s)
         (zb-near-zero? s (zb-recur-scale a F n nv K)))))

(define (zb-recur-scale a F n nv K)
  (if (null? a)
      1
      (+ (abs (eval-num (eval (zb-subst-sym (car a) n nv))))
         (zb-recur-scale (cdr a) F n nv K))))

(define (zb-near-zero? s scale)
  (< (abs s) (+ 1e-6 (* 1e-9 scale))))

(define (zb-recur-sum a F n nv K)
  (zb-recur-sum2 a F n nv K 0))

(define (zb-recur-sum2 a F n nv K j)
  (if (null? a)
      0
      (+ (* (eval-num (eval (zb-subst-sym (car a) n nv)))
            (zb-num-sum F n (+ nv j) K))
         (zb-recur-sum2 (cdr a) F n nv K (+ j 1)))))

(define (zb-check-at r F Bm1 C D k n nv kv)
  (let* ((a (car r)) (R (cdr r))
         (J (length a))
         (t (zb-eval-at (zb-sum-shifts a F n k J) n nv kv k))
         (G1 (zb-check-g1 R F n k J nv kv))
         (g0 (zb-eval-at (list (quote *) R F) n nv kv k)))
    (and (number? t) (number? G1) (number? g0)
         (equal? (- (eval-num t) (- (eval-num G1) (eval-num g0))) 0))))

(define (zb-check-g1 R F n k J nv kv)
  (zb-g1val (zb-subst-sym (zb-subst-sym R n nv) k (list (quote +) k 1))
            (zb-subst-sym (zb-shift-F F n k J) n nv) k kv))

(define (zb-g1val R1 F1 k kv)
  (eval (zb-subst-sym (list (quote *) R1 F1) k (+ kv 1))))
; Σ_j a_j(n) F(n+j, k) — символьная форма
(define (zb-sum-shifts a F n k J)
  (zb-sum-shifts-loop a F n k 0 (quote 0)))

(define (zb-sum-shifts-loop a F n k j acc)
  (if (null? a)
      acc
      (zb-sum-shifts-loop (cdr a) F n k (+ j 1)
        (list (quote +) acc (list (quote *) (car a) (zb-shift-F F n k j))))))

; F(n+j, k)
(define (zb-shift-F F n k j)
  (if (= j 0)
      F
      (zb-subst-sym F n (list (quote +) n j))))

; подстановка чисел n=nv, k=kv и eval
(define (zb-eval-at x n nv kv k)
  (eval (zb-subst-sym (zb-subst-sym x n nv) k kv)))

; все свободные a-переменные (значение = сам символ)
(define (zb-free-vars alist anames)
  (cond ((null? anames) (quote ()))
        ((zb-is-free? alist (car anames))
         (cons (car anames) (zb-free-vars alist (cdr anames))))
        (else (zb-free-vars alist (cdr anames)))))

; фиксация: fst = 1, прочие свободные = 0
(define (zb-fix-free alist fst others)
  (zb-subst-many alist (cons (cons fst 1)
                             (zb-pairs-zero others))))

(define (zb-pairs-zero xs)
  (if (null? xs)
      (quote ())
      (cons (cons (car xs) 0) (zb-pairs-zero (cdr xs)))))


; рекурсивная замена символа sym → val в AST (не зависит от math-упрощения)
(define (zb-subst-sym x sym val)
  (cond ((equal? x sym) val)
        ((pair? x) (cons (zb-subst-sym (car x) sym val)
                         (zb-subst-sym (cdr x) sym val)))
        (else x)))
; подстановка многих (= sym val) в значения всех пар
(define (zb-subst-many alist eqs)
  (if (null? alist)
      (quote ())
      (let ((pair (car alist)))
        (cons (zb-subst-one-pair pair eqs)
              (zb-subst-many (cdr alist) eqs)))))

(define (zb-subst-one-pair pair eqs)
  (list (car pair) (car (cdr pair)) (zb-subst-eqs (car (cdr (cdr pair))) eqs)))

(define (zb-subst-eqs x eqs)
  (if (null? eqs)
      x
      (zb-subst-eqs (zb-subst-sym x (car (car eqs)) (cdr (car eqs))) (cdr eqs))))

; solve-результат → alist пар (= sym val) (берём первое решение множества)
(define (zb-sols-alist sols)
  (let ((lst (zb-sols-list sols)))
    (if (and (pair? lst) (pair? (car lst)) (pair? (car (car lst))))
        (car lst)
        lst)))

(define (zb-sols-list sols)
  (cond ((set? sols) (set->list sols))
        ((list? sols) sols)
        (else (quote ()))))

; свободная переменная среди a-имён: значение = сама себе
(define (zb-free-var alist anames)
  (cond ((null? anames) #f)
        ((zb-is-free? alist (car anames)) (car anames))
        (else (zb-free-var alist (cdr anames)))))

(define (zb-is-free? alist nm)
  (cond ((null? alist) #f)
        ((and (pair? (car alist)) (pair? (cdr (car alist))) (equal? (car (cdr (car alist))) nm))
         (equal? (car (cdr (cdr (car alist)))) nm))
        (else (zb-is-free? (cdr alist) nm))))

; фиксация free = 1 в значениях всех пар
(define (zb-subst-free alist free)
  (if (null? alist)
      '()
      (let ((pair (car alist)))
        (cons (list (car pair) (car (cdr pair)) (subst (list '= free 1) (car (cdr (cdr pair)))))
              (zb-subst-free (cdr alist) free)))))

; значения имён из alist (нет — 0)
(define (zb-lookup-list names alist)
  (if (null? names)
      '()
      (cons (zb-lookup-one (car names) alist)
            (zb-lookup-list (cdr names) alist))))

(define (zb-lookup-one nm alist)
  (cond ((null? alist) 0)
        ((and (pair? (car alist)) (pair? (cdr (car alist))) (equal? (car (cdr (car alist))) nm))
         (simplify (car (cdr (cdr (car alist))))))
        (else (zb-lookup-one nm (cdr alist)))))

(define (zb-all-zero? vals)
  (or (null? vals)
      (and (equal? (simplify (car vals)) 0) (zb-all-zero? (cdr vals)))))

; f = Σ f_i k^i
(define (zb-build-poly vals k)
  (zb-build-poly-loop vals 0 0 k))
(define (zb-build-poly-loop vals i acc k)
  (if (null? vals)
      acc
      (zb-build-poly-loop (cdr vals) (+ i 1)
                          (expand (simplify (list '+ acc
                                                   (list '* (car vals) (list '^ k i))))) k)))

; нормировка (эталонная нормировка): умножить все a_j на НОК знаменателей a_j,
; сократить НОД числителей; R умножается на тот же множитель
(define (zb-normalized avals fvals Bm1 C D k n)
  (let* ((lcmd (zb-lcm-dens (zb-append avals fvals) n))
         (as (map (lambda (a) (expand (simplify (list '* lcmd a)))) avals))
         (fs (map (lambda (v) (expand (simplify (list '* lcmd v)))) fvals))
         (g (zb-gcd-list (zb-append as fs))))
    (if (and (number? g) (= g 0))
        'unsolvable
        (let* ((an (map (lambda (a) (expand (simplify (list '/ a g)))) as))
               (fn (map (lambda (v) (expand (simplify (list '/ v g)))) fs))
               (f (zb-build-poly fn k))
               (R (expand (simplify (list '/ (list '* Bm1 f) (list '* C D))))))
          (cons an R)))))
; НОК знаменателей рациональных функций a_j(n)
(define (zb-lcm-dens avals n)
  (zb-lcm-loop-expr avals 1 n))

(define (zb-lcm-loop-expr xs acc n)
  (if (null? xs)
      acc
      (let ((den (zb-den-of (car xs))))
        (if (or (not den) (number? den))
            (zb-lcm-loop-expr (cdr xs) acc n)
            (zb-lcm-loop-expr (cdr xs) (zb-poly-lcm2 acc den n) n)))))

; знаменатель рациональной функции (многочлен по n); число, если нет
(define (zb-den-of x)
  (zb-den-of-t (together x)))

; (* c (^ q -1))-форма?
(define (zb-inv-factor? e)
  (and (op-expr? e) (equal? (car e) (quote ^)) (equal? (car (cdr (cdr e))) -1)))

; рациональная дробь в ^-форме: (* (^ q -1) rest) или (* rest (^ q -1))
(define (zb-prod-inv? t)
  (and (op-expr? t) (equal? (car t) (quote *)) (= (length t) 3)
       (or (and (zb-inv-factor? (car (cdr t))) (not (zb-inv-factor? (car (cdr (cdr t))))) (op-expr? (car (cdr (cdr t)))))
           (and (zb-inv-factor? (car (cdr (cdr t)))) (not (zb-inv-factor? (car (cdr t)))) (op-expr? (car (cdr t)))))))
; ^-формы: (^ q -1) → q; (* c (^ q -1)) → q; (/ a q) → q; иначе 1
(define (zb-den-of-t t)
  (cond ((and (op-expr? t) (equal? (car t) (quote /)) (= (length t) 3))
         (car (cdr (cdr t))))
        ((and (op-expr? t) (equal? (car t) (quote ^)) (= (length t) 3) (equal? (car (cdr (cdr t))) -1))
         (car (cdr t)))
        ((zb-prod-inv? t)
         (car (cdr (car (cdr (cdr t))))))
        (else 1)))
; НОД списка (через poly-gcd; для не-многочленов — 1)
(define (zb-gcd-list xs)
  (zb-gcd-loop xs 0))
(define (zb-gcd-loop xs acc)
  (if (null? xs)
      (if (= acc 0) 1 acc)
      (let ((g (sum-guard (lambda () (poly-gcd acc (car xs))))))
        (zb-gcd-loop (cdr xs) (if (and g (number? g)) g (if g g acc))))))



