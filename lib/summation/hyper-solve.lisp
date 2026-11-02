(module summation
  (export rsolve rsolve-first-order rsolve-const-coeffs recurrence-check-sum rs-try-central))

; ---------- rsolve (21l.6): решение рекуррентностей в замкнутых формах ----------

; (rsolve rec) — rec = (recurrence S n (a0…aJ) rhs init), однородная (rhs = 0):
; → замкнутая форма S(n) (Γ-произведение при порядке 1; сумма экспонент при
; постоянных коэффициентах) либо #f (нет гипергеометрических решений —
; напр. Апери; вызывающий вернёт саму рекуррентность).
; Порядок ≥ 2 с рациональными коэффициентами: Hyper/Poly (Петковшек) —
; не реализовано (остаток), #f.

; запись рекуррентности: доступ к полям
(define (rs-sym r) (car (cdr r)))
(define (rs-var r) (car (cdr (cdr r))))
(define (rs-coeffs r) (car (cdr (cdr (cdr r)))))
(define (rs-rhs r) (car (cdr (cdr (cdr (cdr r))))))
(define (rs-init r) (car (cdr (cdr (cdr (cdr (cdr r)))))))

(define (rsolve r)
  (sum-guard
   (lambda ()
     (if (not (equal? (simplify (rs-rhs r)) 0))
         #f
         (let* ((a (rs-coeffs r))
                (res (cond ((= (length a) 2) (rsolve-first-order r))
                           ((rs-const-coeffs? a) (rsolve-const-coeffs r))
                           (else #f))))
           (if (and res (step-log-enabled?))
               (record-step 'rsolve-solution "Решение рекуррентности"
                            (if (= (length a) 2)
                                "тип: порядок 1, отношение S(n+1)/S(n) — рациональное"
                                "тип: постоянные коэффициенты (C-конечная)")
                            r res 'main))
           res)))))

; порядок 1: a0(n)·S(n) + a1(n)·S(n+1) = 0 → S(n+1)/S(n) = −a0/a1 = r(n).
; Решение: S(n) = S(n0)·∏_{j=n0}^{n−1} r(j); r = c·∏ (j+β_i)^{m_i} →
; Γ-форма: ∏ (j+β) = Γ(n+β)/Γ(n0+β), c-часть: c^(n−n0).
(define (rsolve-first-order r)
  (let* ((n (rs-var r))
         (a (rs-coeffs r))
         (init (rs-init r))
         (a0 (car a)) (a1 (car (cdr a)))
         (rat (simplify (together (list '/ (list '* -1 a0) a1))))
         (parts (rs-rat-parts rat n)))
    (if (not parts)
        #f
        (let* ((c (car parts)) (lin (cdr parts))
               (S0 (rs-init-value init))
               (n0 (rs-init-point init)))
          (if (not (and S0 n0 (number? n0)))
              #f
              (rs-polish (rs-build-gamma c lin S0 n0 n) n))))))

; разложение r(n) на c·∏ (n+β_i)^{m_i}: → (c . ((β_1 m_1) …)) либо #f
(define (rs-rat-parts rat n)
  (let* ((nd (summation::zb-split (together (summation::zb-inv-to-div rat))))
         (num (car nd)) (den (cdr nd)))
    (if (or (rs-nonlin? num n) (rs-nonlin? den n))
        #f
        (let* ((nf (rs-lin-factors num n))
               (df (rs-lin-factors den n)))
          (if (or (not nf) (not df))
              #f
              (let ((all (rs-merge-factors (cdr nf) (cdr df))))
                (cons (/ (car nf) (car df)) all)))))))

; есть нелинейные факторы (степень по n ≥ 2)?
(define (rs-nonlin? p n)
  (let ((d (sum-guard (lambda () (degree p n)))))
    (and d (> d 1))))

; факторизация на линейные факторы: → (c . ((β_1 m_1) …)), фактор (n + β);
; #f — если есть неприводимый нелинейный фактор
(define (rs-lin-factors p n)
  (sum-guard
   (lambda ()
     (let ((fl (factor-list p)))
       (rs-lin-loop (cdr fl) (car fl) '())))))

(define (rs-lin-loop fl c acc)
  (if (null? fl)
      (cons c acc)
      (let* ((f (car (car fl)))
             (m (car (cdr (car fl))))
             (ab (rs-lin-root f)))
        (if (not ab)
            #f
            (rs-lin-loop (cdr fl)
                         (* c (rs-ipow (car ab) m))
                         (rs-add-fact acc (cdr ab) m))))))

; целочисленная степень числа (expt нет в диалекте)
(define (rs-ipow b m)
  (if (= m 0)
      1
      (if (< m 0)
          (/ 1 (rs-ipow b (- m)))
          (if (= m 1) b (* b (rs-ipow b (- m 1)))))))

; факторы f = a·n + b: → (a . β) с β = b/a (f = a·(n+β)); #f если не линейный
; или корень не рационален
(define (rs-lin-root f)
  (let* ((cs (sum-guard (lambda () (coefficients f 'n))))
         (d (sum-guard (lambda () (degree f 'n)))))
    (if (or (not cs) (not d) (not (= d 1)))
        #f
        (let ((b (car cs)) (a (car (cdr cs))))
          (if (and (number? a) (number? b) (not (= a 0)))
              (cons a (/ b a))
              #f)))))

; добавить (β, m) в счётчик факторов
(define (rs-add-fact acc b m)
  (if (null? acc)
      (list (list b m))
      (if (equal? (car (car acc)) b)
          (cons (list b (+ (car (cdr (car acc))) m)) (cdr acc))
          (cons (car acc) (rs-add-fact (cdr acc) b m)))))

; слить факторы num (+m) и den (−m): счётчики складываются
(define (rs-merge-factors nf df)
  (rs-fact-add-all nf (rs-negate-facts df)))

(define (rs-fact-add-all xs out)
  (if (null? xs)
      out
      (rs-fact-add-all (cdr xs)
                       (rs-add-fact out (car (car xs)) (car (cdr (car xs)))))))

(define (rs-negate-facts df)
  (if (null? df)
      '()
      (cons (list (car (car df)) (- (car (cdr (car df))))) (rs-negate-facts (cdr df)))))

; S(n) = S0 · c^(n−n0) · ∏ Γ(n+β_i)^{m_i} / ∏ Γ(n0+β_i)^{m_i}
(define (rs-build-gamma c lin S0 n0 n)
  (let ((base (rs-gamma-product lin n0 n)))
    (if (not base)
        #f
        (simplify (together
                   (list '* S0
                         (list '^ c (list '- n n0))
                         base))))))

; ∏ Γ(n+β_i)^{m_i} / ∏ Γ(n0+β_i)^{m_i}
(define (rs-gamma-product lin n0 n)
  (rs-gamma-loop lin n0 n 1 1))

(define (rs-gamma-loop lin n0 n accn acc0)
  (if (null? lin)
      (simplify (together (list '/ accn acc0)))
      (let* ((b (car (car lin)))
             (m (car (cdr (car lin))))
             (gn (list 'gamma (list '+ n b)))
             (g0 (list 'gamma (list '+ n0 b))))
        (rs-gamma-loop (cdr lin) n0 n
                       (expand (simplify (list '* accn (list '^ gn m))))
                       (expand (simplify (list '* acc0 (list '^ g0 m))))))))

; постоянные коэффициенты?
(define (rs-const-coeffs? a)
  (rs-const-loop a))

(define (rs-const-loop a)
  (if (null? a)
      #t
      (and (number? (car a)) (rs-const-loop (cdr a)))))

; начальное значение: первое (n0 v0) из init
(define (rs-init-point init)
  (if (and (pair? init) (pair? (car init)))
      (car (car init))
      #f))

(define (rs-init-value init)
  (if (and (pair? init) (pair? (car init)))
      (car (cdr (car init)))
      #f))

; постоянные коэффициенты (порядок ≥ 2): характеристический многочлен
; χ(z) = Σ a_j z^j; корни через solve/factor; решение Σ C_i·λ_i^n (простые
; корни); C_i из начальных значений (линейная система, solve). Кратные корни —
; остаток (Poly); #f если корни не найдены.
(define (rsolve-const-coeffs r)
  (sum-guard
   (lambda ()
     (let* ((n (rs-var r))
            (a (rs-coeffs r))
            (init (rs-init r))
            (chi (rs-char-poly a))
            (lam (rs-roots chi)))
       (if (not lam)
           #f
           (begin
             (if (step-log-enabled?)
                 (record-step 'cf-charpoly "Характеристический многочлен"
                              "χ(z) = Σ a_j·z^j; его корни — базы экспонент" a chi 'main))
             (if (step-log-enabled?)
                 (record-step 'cf-roots "Корни характеристического многочлена"
                              "λ_i — собственные значения" chi lam 'main))
             (let ((ans (rs-const-solve lam init n)))
               (if (not ans)
                   #f
                   (begin
                     (if (step-log-enabled?)
                         (record-step 'cf-general "Общий вид решения"
                                      "Σ C_i·λ_i^n; C_i — из начальных значений" lam
                                      (rs-lam-sum lam (rs-cvars lam) n) 'main))
                     (if (step-log-enabled?)
                         (record-step 'cf-constants "Константы из начальных значений"
                                      "линейная система по C_i решена" init ans 'main))
                     (if (step-log-enabled?)
                         (record-step 'cf-check "Проверка первых членов"
                                      "значения в точках init совпали с ответом (rs-const-answer)"
                                      ans ans 'main))
                     ans)))))))))

; χ(z) = Σ_j a_j z^j (a_J — старший, при S(n+J))
(define (rs-char-poly a)
  (rs-char-loop a 0 0))

(define (rs-char-loop a j acc)
  (if (null? a)
      acc
      (rs-char-loop (cdr a) (+ j 1)
                    (expand (simplify (list '+ acc
                                             (list '* (car a) (list '^ 'z j))))))))

; корни χ (все числовые или root-of); внутренние шаги solve в журнал не пишутся
; (они дублируют cf-roots/cf-constants и шумят в brief)
(define (rs-roots chi)
  (rs-quiet
   (lambda ()
     (let ((sol (solve (list '= chi 0) 'z)))
       (if (or (not sol) (equal? sol 'unknown))
           #f
           (let ((lst (if (set? sol) (set->list sol) sol)))
             (if (and (pair? lst) (rs-all-nums lst)) lst #f)))))))

; тихий вызов при включённом журнале (как call-quietly/alg-run в интеграторе)
(define (rs-quiet thunk)
  (if (step-log-enabled?) (call-quietly thunk) (thunk)))

(define (rs-all-nums xs)
  (or (null? xs)
      (and (rs-numexpr? (car xs)) (rs-all-nums (cdr xs)))))

; числовое выражение (eval-num считает): числа, sqrt-формы, root-of
(define (rs-numexpr? v)
  (let ((x (sum-guard (lambda () (eval-num (eval v))))))
    (number? x)))

; алгебраическое число (root-of …)
(define (rs-alg? v)
  (and (pair? v) (equal? (car v) 'root-of)))

; Σ C_i·λ_i^n с C_i из init: точки init → линейная система по C, solve
(define (rs-const-solve lam init n)
  (if (not (and (pair? lam) (pair? init)))
      #f
      (let* ((vars (rs-cvars lam))
             (eqs (rs-init-eqs lam init vars)))
        (if (not eqs)
            #f
            (let ((sol (rs-quiet (lambda () (solve eqs vars)))))
              (if (or (not sol) (equal? sol 'unknown))
                  #f
                  (rs-const-answer lam vars sol init n)))))))

; имена rsC0, rsC1, …
(define (rs-cvars lam)
  (rs-cvars-loop (length lam) 0 '()))

(define (rs-cvars-loop N i acc)
  (if (= i N)
      acc
      (rs-cvars-loop N (+ i 1)
                     (append acc (list (string->symbol (string-append "rsC" (to-string i))))))))

; уравнения из init: для (n0 v0): Σ C_i·λ_i^{n0} = v0
(define (rs-init-eqs lam init vars)
  (rs-init-eqs-loop lam init vars '()))

(define (rs-init-eqs-loop lam init vars eqs)
  (if (null? init)
      eqs
      (let* ((pair (car init))
             (m (car pair)) (v (car (cdr pair)))
             (lhs (rs-lam-sum lam vars m))
             (eq (list '= lhs v)))
        (rs-init-eqs-loop lam (cdr init) vars (append eqs (list eq))))))

(define (rs-lam-sum lam vars m)
  (rs-lam-loop lam vars m 0))

(define (rs-lam-loop lam vars m acc)
  (if (null? lam)
      acc
      (rs-lam-loop (cdr lam) (cdr vars) m
                   (expand (simplify (list '+ acc
                                            (list '* (car vars)
                                                  (list '^ (car lam) m))))))))

; ответ: подставить C_i в Σ C_i·λ_i^n; проверка по начальным значениям —
; точная (simplify), иначе численная (float ≈ 1e-9); явно неверный ответ не выдаётся
(define (rs-const-answer lam vars sol init n)
  (let ((alist (rs-sol-alist sol)))
    (if (not alist)
        #f
        (let ((ans (simplify (together (rs-const-sub lam vars alist n 0)))))
          (if (rs-answer-bad? ans init n) #f ans)))))

; #t — ответ противоречит начальному значению; #f — противоречий нет
(define (rs-answer-bad? ans init n)
  (if (null? init)
      #f
      (let* ((pair (car init)) (m (car pair)) (v (car (cdr pair)))
             (d (sum-guard (lambda () (simplify (list '- (subst (list '= n m) ans) v))))))
        (cond ((equal? d 0) (rs-answer-bad? ans (cdr init) n))
              ((number? d) #t)
              (else
               (let* ((va (sum-guard (lambda () (eval-num (eval (subst (list '= n m) ans))))))
                      (vv (sum-guard (lambda () (eval-num (eval v))))))
                 (if (and (number? va) (number? vv))
                     (if (and (not (= vv 0)) (< (abs (/ (- va vv) vv)) 1e-9))
                         (rs-answer-bad? ans (cdr init) n)
                         #t)
                     (rs-answer-bad? ans (cdr init) n))))))))

(define (rs-const-sub lam vars alist n acc)
  (if (null? lam)
      acc
      (let ((ci (rs-lookup (car vars) alist)))
        (rs-const-sub (cdr lam) (cdr vars) alist n
                      (expand (simplify (list '+ acc
                                               (list '* ci (list '^ (car lam) n)))))))))

; solve-ответ → alist первой группы ((= sym val) …)
(define (rs-sol-alist sol)
  (let ((lst (if (set? sol) (set->list sol) sol)))
    (if (and (pair? lst) (pair? (car lst)))
        (car lst)
        #f)))

(define (rs-lookup sym alist)
  (cond ((null? alist) 0)
        ((and (pair? (car alist)) (equal? (car (cdr (car alist))) sym))
         (car (cdr (cdr (car alist)))))
        (else (rs-lookup sym (cdr alist)))))

; ---------- подключение к каскаду sum: шаг Цайльбергера + rsolve ----------

; нормализация C(a,b) → binomial(a,b): mathlang использует binomial, но входной
; язык/bench могут писать C; zeilberger/hyper понимают только binomial (21l.8)
(define (zb-C-to-binomial e)
  (cond ((and (pair? e) (equal? (car e) 'C) (= (length e) 3))
         (cons 'binomial (map zb-C-to-binomial (cdr e))))
        ((pair? e) (cons (car e) (map zb-C-to-binomial (cdr e))))
        (else e)))

; Σ_{k=lo}^{hi} F(n,k) при символьном n в границе: zeilberger по n (n —
; символьная граница), затем rsolve. Замкнутая форма — если rsolve нашёл;
; иначе рекуррентность (Апери: честный ответ, не «не знаю»). Госпер и
; Абрамов уже пробовались раньше в каскаде.
(sum-add-strategy
 (lambda (body k lo hi)
   (if (not (or (and (symbol? lo) (number? hi))
                (and (number? lo) (symbol? hi))))
       #f
       (let* ((nv (if (symbol? hi) hi lo))
              (F (zb-C-to-binomial body))
              (full (zeilberger-full F nv k)))
         (if (not full)
             #f
             (let* ((r (car full))
                    (cert (cdr full))
                    (a (nth r 3))
                    (form (sum-form body k lo hi))
                    (ok (zeilberger-cert-check F nv k a cert)))
               (if (step-log-enabled?)
                   (record-step 'zeilb-order "Порядок рекуррентности"
                                (string-append "J = " (to-string (recurrence-order r)))
                                form (recurrence-order r) 'main))
               (if (step-log-enabled?)
                   (record-step 'zeilb-cert "Сертификат R(n,k)"
                                "G(n,k) = R(n,k)·t(n,k); Σ c_j(n)·t(n+j,k) = G(n,k+1) − G(n,k)"
                                form cert 'main))
               (if (step-log-enabled?)
                   (record-step 'zeilb-check "Проверка сертификата"
                                (if ok
                                    "Σ c_j(n)·t(n+j,k)/t(n,k) = R(n,k+1)·t(n,k+1)/t(n,k) − R(n,k): тождество проверено (разность 0)"
                                    "тождество телескопирования не проверено: сертификат не используется")
                                cert (if ok 0 'not-checked) 'main))
               (if (not ok)
                   #f
                   (begin
                     (if (step-log-enabled?)
                         (record-step 'zeilb-recurrence "Найденная рекуррентность"
                                      "Σ c_j(n)·S(n+j) = 0; коэффициенты и начальные значения — в ответе"
                                      form r 'detail))
                     (let ((closed (rsolve r)))
                       (if closed
                           (begin
                             (record-step 'sum-zeilberger
                                          "Символьное суммирование: Цайльбергер + rsolve"
                                          "рекуррентность решена в замкнутой форме"
                                          form closed)
                             closed)
                           (begin
                             (record-step 'sum-recurrence
                                          "Символьное суммирование: Цайльбергер (рекуррентность)"
                                          "гипергеометрической замкнутой формы нет; ответ — рекуррентность с начальными значениями"
                                          form r)
                             r)))))))))))

; полировка Γ-формы порядка 1: свёртка половинных Γ в биномы.
; 4^n·Γ(n+1/2)/(Γ(1/2)·Γ(n+1)) = C(2n,n); общий случай m-кратностей — 21l.8.
; Шаблон: c^n·Γ(n+β1)^m1·…/… после together; проверяем частный вид
; c = 4, один β = 1/2 с m = +1 в num, β = 0/1-факториальный хвост.
(define (rs-polish e n)
  (sum-guard (lambda () (rs-try-central e n))))

; кандидат C(2n,n): ТОЧНАЯ проверка — отношение соседних членов (hyper-ratio)
; у Γ-формы и у C(2n,n) совпадает (simplify разности = 0) и значения равны
; в одной точке; иначе Γ-форма остаётся (никаких численных свёрток)
(define (rs-try-central e n)
  (let ((cand (list 'binomial (list '* 2 n) n)))
    (if (rs-exact-eq e cand n)
        cand
        e)))

; точное равенство двух гипергеометрических термов от n: отношения соседних
; членов равны (рациональная проверка через simplify) + равенство в одной
; точке (n = 1; Γ-значения точные через eval)
(define (rs-exact-eq e cand n)
  (let* ((re (hyper-ratio e n))
         (rc (hyper-ratio cand n)))
    (if (or (not re) (not rc))
        #f
        (let ((diff (simplify (together
                               (list '- (list '/ (car re) (cdr re))
                                     (list '/ (car rc) (cdr rc)))))))
          (and (equal? diff 0)
               (rs-val-eq e cand n 1))))))

; значение в точке m: Γ-значения иррациональны — eval-num (float) с относительной
; погрешностью 1e-9 (рациональная часть уже проверена отношением соседних членов)
(define (rs-val-eq e cand n m)
  (let* ((ve (sum-guard (lambda () (eval-num (eval (subst (list (quote =) n m) e))))))
         (vc (sum-guard (lambda () (eval-num (eval (subst (list (quote =) n m) cand)))))))
    (and (number? ve) (number? vc) (not (= vc 0))
         (< (abs (/ (- ve vc) vc)) 1e-9))))
; численное равенство в точке m (eval-num; float≈ допускается относительной
; погрешностью 1e-9)
(define (rs-num-eq e cand n m)
  (let* ((ve (eval-num (eval (subst (list '= n m) e))))
         (vc (eval-num (eval (subst (list '= n m) cand)))))
    (and (number? ve) (number? vc) (not (= vc 0))
         (< (abs (/ (- ve vc) vc)) 1e-9))))

; (recurrence-check-sum rec body k n) — проверка рекуррентности-ответа суммой:
; direct-sum S(m) = тело с n→m, сумма по k по естественным границам (wz-nat-bound).
; Для MCP-сертификата инструмента sum (21l.7); #t/#f.
(define (recurrence-check-sum rec body k n)
  (sum-guard
   (lambda ()
     (recurrence-check rec (zb-dsum body n k)))))
