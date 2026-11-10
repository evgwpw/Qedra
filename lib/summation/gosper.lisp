; summation/gosper.lisp — Шаг 21l.3: алгоритм Госпера (гл. 5 «A = B»; эталонная схема как ориентир).
; (gosper-normal p q k) → ((A . B) . C): p/q = A(k)·C(k+1)/(B(k)·C(k)), gcd(A(k), B(k+h)) = 1
;   для целых h ≥ 0 (генерически; параметрические множители результанта — record-condition),
;   Z = lc(p)/lc(q) включена в A. Старший коэффициент с параметром → маркер (param-lc ...).
; (gosper-term t k) → множитель g(k) (z_k = g(k)·t_k, z_{k+1} − z_k = t_k), либо
;   'no-hyper / 'unsolvable (доказано: нет гипергеометрической первообразной) / 'unknown.
; (gosper-sum t k lo hi) → замкнутая форма Σ_{k=lo}^{hi} t_k либо #f (невычисленная форма).
;   Каждый ответ проверяется тождеством g(k+1)·r − g − 1 = 0; не прошла — #f (не ложный ответ).
;   «Доказано: нет первообразной» — только при чисто числовых данных; иначе #f («не знаю»).

(module summation
  (export gosper-degree-bound
        sum-symbolic sum-strategies sum-add-strategy sum-guard sum-check sum-check-how
          sum-unevaluated sum-faulhaber sum-form
          hyper-ratio hyper-termp poly-shift poly-int-roots poly-int-roots-param poly-dispersion
          hyper-lin hyper-frac-mul hyper-poly-mul
          gosper-normal gosper-term gosper-sum gosper-check-identity))

; ---------- gosper-normal: p/q = A·C(k+1)/(B·C(k)) ----------

(define (gosper-monic p k)
  (let ((lc (coeff p k (degree p k))))
    (if (or (not (number? lc)) (= lc 0) (= lc 1))
        p
        (expand (simplify (list '/ p lc))))))

; p/q → ((A . B) . C): p, q — несократимые (по k) многочлены. Работаем в целочисленных
; примитивных формах (poly-gcd над ℤ): A, B накапливают содержимое (Z полностью в A в конце).
(define (gosper-normal p q k)
  (let* ((ip (gosper-integerize p k))
         (iq (gosper-integerize q k))
         (plc (coeff p k (degree p k)))
         (qlc (coeff q k (degree q k)))
         (A0 (cdr ip)) (B0 (cdr iq))
         (rp (poly-int-roots-param (resultant A0 (poly-shift B0 k 'h) k) 'h)))
    (if (not (and (number? plc) (number? qlc)))
        (cons (cons 'param-lc (list plc qlc)) '())
        (let* ((roots (car rp))
               (params (cdr rp)))
          (if (not (null? params))
              (record-condition "res(A, B(k+h)) без целых корней (генерические параметры)"
                                "gosper-normal"))
          ; Z = lc(p)/lc(q): инвариант p/q = Z·A·C(k+1)/(B·C(k)) при A=A0, B=B0
          (gosper-normal-loop roots A0 B0 1 plc qlc k)))))

; A, B — целочисленные; C накапливает сдвинутые НОД (целочисленные).
; Инвариант: p/q = (m_q/m_p)·A·C(k+1)/(B·C(k)) — множитель Z = m_q/m_p собирается в A.
; целочисленные A, B, C; в финале — нормировка к эталонной форме: A = A2/lc(B2), B = B2/lc(B2),
; C = C2/lc(C2) (проверено: p/q = A·C(k+1)/(B·C(k)) при стартовом инварианте p/q = A0/B0, C=1)
(define (gosper-normal-loop roots A B C plcf qlcf k)
  (if (null? roots)
      (let* ((b (coeff B k (degree B k)))
             (c (coeff C k (degree C k))))
        (if (not (and (number? b) (not (= b 0)) (number? c) (not (= c 0))))
            (cons (cons 'param-lc (list b c)) '())
            (cons (cons (expand (simplify (list '/ A b)))
                        (expand (simplify (list '/ B b))))
                  (expand (simplify (list '/ C c))))))
      (let* ((h (apply min roots))
             (rest (filter (lambda (x) (> x h)) roots))
             (Bh (poly-shift B k h))
             (g (sum-guard (lambda () (poly-gcd A Bh)))))
        (if (or (not g) (and (number? g) (= g 1)))
            (gosper-normal-loop rest A B C plcf qlcf k) ; НОД-константа — корень ложный, пропускаем
            (let* ((A2 (poly-quotient A g k))
                   (g-sh (poly-shift g k (- h)))
                   (B2 (poly-quotient B g-sh k))
                   (C2 (gosper-normal-cprod g h C k)))
              (gosper-normal-loop rest A2 B2 C2 plcf qlcf k))))))


; C ← C·∏_{j=1}^{h} g(k−j)
(define (gosper-normal-cprod g h C k)
  (if (= h 0)
      C
      (gosper-normal-cprod g (- h 1) (hyper-poly-mul C (poly-shift g k (- h))) k)))


; ---------- шаги (ST.3б-1) ----------
; отказ с причиной (доказательство неразрешимости в гипергеометрических термах);
; литеральный record-step нужен сканеру словаря StepDict. «Неопределённая» важно:
; для определённой суммы её может взять Цайльбергер (Σ C(n,k)²)
(define (gosper-refuse why form)
  (if (step-log-enabled?)
      (record-step 'gosper-refuse "Неопределённая сумма не гипергеометрическая (Госпер)"
                   why form 'refused 'main))
  #f)

; ---------- gosper-term: границы степени x(k), линейная система ----------

; список имён неизвестных анзаца степени d: gs0, gs1, ...

; ---------- домножение до целых коэффициентов (poly-gcd работает над ℤ) ----------

; НОК знаменателей коэффициентов p по k
(define (gosper-denoms-lcm p k)
  (let ((d (degree p k)))
    (if (not (number? d))
        1
        (gosper-denoms-loop p k d 1))))
(define (gosper-denoms-loop p k d acc)
  (if (< d 0)
      acc
      (let* ((c (coeff p k d))
             (den (if (and (number? c) (not (= c 0))) (denom c) 1)))
        (gosper-denoms-loop p k (- d 1) (lcm acc den)))))

; p → m·p' с целыми коэффициентами p' (m — числовой множитель); возврат (m . p')
(define (gosper-integerize p k)
  (let* ((m (gosper-denoms-lcm p k))
         (pi (expand (simplify (list '* p m)))))
    (cons m pi)))

(define (gosper-coef-names d)
  (if (< d 0)
      '()
      (append (gosper-coef-names (- d 1))
              (list (string->symbol (string-append "gs" (to-string d)))))))

; анзац-многочлен: i-е имя — коэффициент при k^i
(define (gosper-ansatz names k)
  (gosper-ansatz-loop names 0 0 k))
(define (gosper-ansatz-loop ns i acc k)
  (if (null? ns)
      acc
      (gosper-ansatz-loop (cdr ns) (+ i 1)
                          (expand (simplify (list '+ acc
                                                   (list '* (car ns) (list '^ k i))))) k)))

; подстановка решения в анзац; свободные/отсутствующие неизвестные → 0
(define (gosper-subst-ansatz x names sols)
  (if (null? names)
      x
      (let ((val (gosper-sols-lookup sols (car names))))
        (gosper-subst-ansatz (expand (simplify (subst (list '= (car names) val) x)))
                             (cdr names) sols))))

; решение solve — множество alist'ов уравнений (= sym val); возврат значения sym или 0.
; Вход: {(= s1 v1) ...} как множество → m-items/set->list; каждый элемент — alist пар.
(define (gosper-sols-lookup sols nm)
  (let ((lst (cond ((set? sols) (set->list sols))
                   ((list? sols) sols)
                   (else '()))))
    (gosper-lookup-loop (if (and (pair? lst) (pair? (car lst)) (pair? (car (car lst)))
                                 (equal? (car (car (car lst))) '=))
                          (car lst)      ; множество решений — берём первое
                          lst)
                        nm)))
(define (gosper-lookup-loop pairs nm)
  (cond ((null? pairs) 0)
        ((and (pair? (car pairs)) (equal? (car (car pairs)) (quote =)) (equal? (cadr (car pairs)) nm))
         (let ((v (caddr (car pairs)))) (if (equal? v nm) 0 v)))
        (else (gosper-lookup-loop (cdr pairs) nm))))

; границы степени x(k): N = deg A, M = deg B(k−1), K = deg C (эталонная gosper_term)
(define (gosper-degree-bound A Bm1 C N M K k)
  (let ((lcA (coeff A k N)) (lcB (coeff Bm1 k M)))
    (cond ((not (and (number? lcA) (number? lcB))) #f)
          ((or (not (= N M)) (not (= lcA lcB))) (- K (max N M)))
          ((= N 0) (+ K 1))
          (else (let* ((d1 (+ (- K N) 1))
                       (d2raw (/ (- (coeff Bm1 k (- N 1)) (coeff A k (- N 1))) lcA))
                       (d2 (if (and (number? d2raw) (sum-int? d2raw)) d2raw -1)))
                  (max d1 d2))))))

; уравнения: coeff(E, k, i) = 0 для i = D..0 (ненулевые)
(define (gosper-eqs E D k)
  (if (< D 0)
      '()
      (let ((ci (coeff E k D)))
        (if (equal? ci 0)
            (gosper-eqs E (- D 1) k)
            (cons (list '= ci 0) (gosper-eqs E (- D 1) k))))))

; анзац степени d: E = A·x(k+1) − B(k−1)·x(k) − C; solve; x ≡ 0 → 'unsolvable
(define (gosper-solve-ansatz A Bm1 C d k)
  (let* ((names (gosper-coef-names d))
         (x (gosper-ansatz names k))
         (x1 (expand (simplify (subst (list '= k (list '+ k 1)) x))))
         (t1 (expand (simplify (list '* A x1))))
         (t2 (expand (simplify (list '* Bm1 x))))
         (E (expand (simplify (list '- (expand (simplify (list '- t1 t2))) C))))
         (D (degree E k))
         (eqs (gosper-eqs E (if (and (number? D) (> D 0)) D 0) k))
         (sols (sum-guard (lambda () (solve eqs names)))))
    (if (not sols)
        'unknown
        (let ((xs (gosper-subst-ansatz x names sols)))
          (if (equal? xs 0)
              (begin
                (gosper-refuse "система дала x ≡ 0 ⇒ многочлена нет (доказано: сумма не гипергеометрическая)" E)
                'unsolvable)
              (let ((g (expand (simplify (list '/ (list '* Bm1 xs) C)))))
                (if (step-log-enabled?)
                    (record-step 'gosper-ansatz "Уравнение a·x(k+1) − b(k−1)·x(k) = c(k)"
                                 (string-append "a(k) = " (sum-p A) ", b(k) = " (sum-p Bm1)
                                                ", c(k) = " (sum-p C) "; степень x ≤ "
                                                (to-string d) "; решение линейной системы над рациональными")
                                 (list A Bm1 C) xs 'main))
                (if (step-log-enabled?)
                    (record-step 'gosper-cert "Сертификат R(k)"
                                 "T(k) = R(k)·t(k), R(k) = B(k−1)·x(k)/C(k)" xs g 'detail))
                g))))))

; главный вход: t, k → g(k) | 'no-hyper | 'unsolvable | 'unknown
(define (gosper-term t k)
  (let ((r (hyper-ratio t k)))
    (if (not r)
        (begin
          (gosper-refuse "t(k+1)/t(k) не рационально: терм не гипергеометрический" t)
          'no-hyper)
        (begin
          (if (step-log-enabled?)
              (record-step 'gosper-ratio "Отношение соседних членов"
                           "r(k) = t(k+1)/t(k) = p(k)/q(k)" t r 'detail))
          (let* ((p (car r))
                 (q (cdr r))
                 (ip (gosper-integerize p k))
                 (iq (gosper-integerize q k))
                 (pi (cdr ip)) (qi (cdr iq))
                 (g0 (sum-guard (lambda () (poly-gcd pi qi))))  ; сокращение p/q (hyper-ratio не сокращает)
                 (p2 (if (or (not g0) (and (number? g0) (= g0 1)))
                         p (expand (simplify (list '/ p g0)))))
                 (q2 (if (or (not g0) (and (number? g0) (= g0 1)))
                         q (expand (simplify (list '/ q g0)))))
                 (nbc (gosper-normal p2 q2 k)))
            (if (and (pair? nbc) (pair? (car nbc)) (equal? (car (car nbc)) 'param-lc))
                'unknown
                (let* ((A (car (car nbc)))
                       (B (cdr (car nbc)))
                       (C (cdr nbc))
                       (Bm1 (poly-shift B k -1))
                       (N (degree A k)) (M (degree Bm1 k)) (K (degree C k))
                       (d (gosper-degree-bound A Bm1 C N M K k)))
                  (if (or (not d) (< d 0))
                      (begin
                        (gosper-refuse "граница степени x(k) < 0 ⇒ многочлена нет (доказано)" (list '/ A B))
                        'unsolvable)
                      (begin
                        (if (step-log-enabled?)
                            (record-step 'gosper-normal "Разложение Госпера–Петковшека"
                                         (string-append "r = (A/B)·(C(k+1)/C(k)); A = " (to-string A)
                                                        ", B = " (to-string B) ", C = " (to-string C))
                                         r (list '/ A B) 'detail))
                        (if (step-log-enabled?)
                            (record-step 'gosper-degree "Граница степени x(k)"
                                         (string-append "N = " (to-string N) ", M = " (to-string M)
                                                        ", K = " (to-string K) " ⇒ d = " (to-string d))
                                         (list '/ A B) d 'main))
                        (gosper-solve-ansatz A Bm1 C d k))))))))))

; ---------- gosper-sum и проверка ----------

; проверка тождества z_{k+1} − z_k = t_k ⇔ g(k+1)·r(k) − g(k) − 1 = 0 (r = t(k+1)/t(k))
(define (gosper-check-identity t g k)
  (let ((r (hyper-ratio t k)))
    (and r
         (let* ((g1 (simplify (subst (list (quote =) k (list (quote +) k 1)) g)))
                (lhs (list (quote /) (list (quote *) g1 (car r)) (cdr r)))
                (rhs (list (quote +) g 1))
                (diff (simplify (together (list (quote -) lhs rhs)))))
           (equal? (simplify diff) 0)))));
; Σ_{k=lo}^{hi} t_k через Госпера: ответ или #f (отказ). Числовые lo с нулями/полюсами t_k —
; сдвиг нижней границы + прямой хвост. hi = inf → #f (limit — 21l.8).
(define (gosper-sum t k lo hi)
  (sum-guard
   (lambda ()
     (let ((g (gosper-term t k)))
       (if (or (equal? g 'no-hyper) (equal? g 'unknown) (equal? g 'unsolvable))
           #f
           (if (not (gosper-check-identity t g k))
               #f ; проверка не прошла — не знаю (не ложный ответ)
               (begin
                 (if (step-log-enabled?)
                     (record-step 'gosper-check "Проверка телескопирования"
                                  (string-append "T(k+1) − T(k) = t(k): тождество g(k+1)·r(k) − g(k) − 1 = 0 проверено; g(k) = "
                                                 (sum-p g))
                                  t (list 'list g (simplify (list '* g t))) 'main))
                 (let ((shift (gosper-pole-shift t k lo)))
                   (gosper-sum-from g t k shift lo hi)))))))))

; сколько первых точек пропустить (t(lo+j) = 0 или полюс) — только для числовых lo
(define (gosper-pole-shift t k lo)
  (if (not (and (number? lo) (sum-int? lo)))
      0
      (gosper-pole-loop t k lo 0)))
(define (gosper-pole-loop t k lo j)
  (if (> j 32)
      0
      (let ((v (sum-guard (lambda () (simplify (subst (list '= k (+ lo j)) t))))))
        (if (or (not v) (equal? v 0))
            (gosper-pole-loop t k lo (+ j 1))
            j))))

; Σ = t(hi)·(g(hi)+1) − t(lo2)·g(lo2) + хвост; lo2 = lo + shift.
; Если числовые границы и hi < lo2 — диапазон [lo2, hi] пуст: только хвост.
(define (gosper-sum-from g t k shift lo hi)
  (let* ((lo2 (if (and (number? lo) (sum-int? lo)) (+ lo shift) lo))
         (tail (gosper-tail t k lo shift))
         (zhi (if (equal? hi 'inf)
                  #f
                  (sum-eval-const (simplify (together (subst (list '= k hi) (list '* t (list '+ g 1))))))))
         (zlo (sum-eval-const (simplify (together (subst (list (quote =) k lo2) (list (quote *) t g)))))))
    (cond ((not zhi) #f)
          ((and (number? lo2) (number? hi) (> lo2 hi)) (simplify tail))
          (else (simplify (list '+ (list '- zhi zlo) tail))))))

; числовая константа: выражение без свободных символов вычисляется (1! → 1), иначе остаётся
(define (sum-eval-const e)
  (if (pair? e)
      (let ((v (sum-guard (lambda () (eval e)))))
        (if (number? v) v e))
      e))

; прямые слагаемые хвоста: сумма t(lo+j) для j < shift
(define (gosper-tail t k lo shift)
  (if (or (= shift 0) (not (number? lo)))
      0
      (gosper-tail-loop t k lo shift 0 0)))
(define (gosper-tail-loop t k lo shift j acc)
  (if (>= j shift)
      acc
      (gosper-tail-loop t k lo shift (+ j 1)
                        (expand (simplify (list (quote +) acc
                                                 (simplify (subst (list (quote =) k (+ lo j)) t))))))))

; ---------- подключение к каскаду sum-strategies ----------

; регистрация стратегии внутри модуля summation (общая ячейка sum-strategies с core.lisp)
(sum-add-strategy
 (lambda (body k lo hi)
   (let ((res (gosper-sum body k lo hi)))
     (if res
         (begin
           (record-step 'gosper "Символьное суммирование: алгоритм Госпера"
                        "терм гипергеометрический; z_k = g(k)*t_k, ответ z(hi+1) - z(lo)"
                        (sum-form body k lo hi) res)
           res)
         #f))))


