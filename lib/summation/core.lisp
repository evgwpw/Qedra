; summation/core.lisp — Шаг 21l.1: символьное суммирование, ядро и каскад L0–L2.
; Диспетчер sum-symbolic вызывается из m-iter-run (mathlang) при символьных границах sum;
; Lisp-интерфейс — (sum-symbolic тело k lo hi). Три исхода: ответ / невычисленная форма (sum ...).
; Слои: L0 тривиальное (константа, линейность, Карр) → L1 многочлены (Фаульхабер, Σk⁻ᵐ → harmonic)
; → L2 геометрическая (условие q ≠ 1). Госпер/Абрамов/Цайльбергер — подшаги 21l.3+ (sum-strategies).
; Проверка ответа — sum-check (аналог int-check): антиразность тождеством + оракул на целых n.

(module summation
  (export sum-symbolic sum-strategies sum-add-strategy sum-guard sum-check sum-check-how
          sum-unevaluated sum-faulhaber sum-form))

; ---------- вспомогательное ----------

; вызов thunk с перехватом ошибок (невычисленная форма при сбое стратегии — каскад продолжается)
(define *sum-catch?* #t)
(define (sum-guard thunk)
  (if *sum-catch?* (try (thunk) (lambda (err) #f)) (thunk)))

; печать для шагов журнала (math-print; ошибка печати — prettyPrint значения)
(define (sum-p e)
  (if (step-log-enabled?) (try (math-print e) (lambda (err) (to-string e))) e))

; невычисленная форма (sum тело k lo hi) — границы упрощены
(define (sum-unevaluated body k lo hi)
  (list 'sum (simplify body) k (simplify lo) (simplify hi)))

; форма для шагов «до»: sum(тело, k, lo, hi)
(define (sum-form body k lo hi)
  (list 'sum body k lo hi))

; число элементов диапазона: числовые границы; 0 — пустой (a > b); #f — символьные
(define (sum-count a b)
  (cond ((and (number? a) (number? b) (> a b)) 0)
        ((and (number? a) (number? b)) (+ (- b a) 1))
        (else #f)))

; k не входит в e
(define (sum-k-free? e k) (x-free? e k))

; ---------- шаги диспетчера (ST.3б-1) ----------

; шаг выбора пути: level main — попадает в brief (префикс sum-); r = #f — путь не сработал, шага нет
(define (sum-note-path why r form)
  (if r
      (begin
        (if (step-log-enabled?)
            (record-step 'sum-path "Выбор пути суммирования" why form r 'main))
        r)
      #f))

; отказ: ни один путь не подошёл (шаг с причиной; форма не меняется)
(define (sum-note-none form why)
  (if (step-log-enabled?)
      (record-step 'sum-no-path "Путь не найден" why form form 'main))
  #f)

; ---------- L0: тривиальное ----------

; тело не зависит от k: Σ_a^b c = c·(b−a+1); числовые границы и b < a → 0 (пустой диапазон)
(define (sum-constant body k lo hi)
  (let ((n (sum-count lo hi)))
    (and (sum-k-free? body k)
         (cond ((equal? n 0) 0)
               (n (simplify (list '* body n)))
               ; символьные границы: (b − a + 1) символьно — формула верна при любых a, b (Карр в неё встроен)
               (else (simplify (list '* body (list '+ (list '- hi lo) 1))))))))

; линейность: c·f(k) → c·Σf(k) (ровно (* c f)); f+g → Σf + Σg (рекурсивно, n-ary +)
(define (sum-linear body k lo hi)
  (cond ((and (op-expr? body) (equal? (car body) '*) (= (length body) 3)
              (sum-k-free? (cadr body) k))
         (sum-guard (lambda ()
           (simplify (list '* (cadr body) (sum-symbolic-bare (caddr body) k lo hi))))))
        ((and (op-expr? body) (equal? (car body) '+))
         (sum-guard (lambda ()
           (simplify (cons '+ (map (lambda (t) (sum-symbolic-bare t k lo hi)) (cdr body)))))))
        (else #f)))

; ---------- L1: многочлены (Фаульхабер) ----------

; Σ_{k=a}^{b} k^m = (B_{m+1}(b+1) − B_{m+1}(a))/(m+1), m ≥ 0; многочлены Бернулли — builtin (21l.0)
(define (sum-faulhaber m a b)
  (simplify (list '/ (list '- (list 'bernoulli (+ m 1) (list '+ b 1))
                              (list 'bernoulli (+ m 1) a))
                       (+ m 1))))

; полиномиальное p(k) (числовые коэффициенты): Σ по мономам c_j·Σ k^j
(define (sum-poly body k lo hi)
  (and (numeric-poly? body k)
       (let ((d (degree body k)))
         (and (>= d 1)
              (sum-guard (lambda ()
                (let ((terms (sum-poly-terms body k lo hi d)))
                  (and terms (simplify (cons '+ terms))))))))))

; список c_j·Σ_{a}^{b} k^j по коэффициентам p (коэффициенты — без k, допускаются параметры);
; #f — если коэффициент зависит от k (не бывает для numeric-poly?, защита)
(define (sum-poly-terms-from body k lo hi j d acc)
  (cond ((> j d) (reverse acc))
        (else
         (let ((c (coeff body k j)))
           (if (not (sum-k-free? c k))
               #f
               (sum-poly-terms-from body k lo hi (+ j 1) d
                 (if (and (number? c) (= c 0))
                     acc
                     (cons (simplify (list '* c (sum-faulhaber j lo hi))) acc))))))))
(define (sum-poly-terms body k lo hi d)
  (sum-poly-terms-from body k lo hi 0 d '()))

; Σ k^{−m} → harmonic(b, m) − harmonic(a−1, m), m ≥ 1 целое; тело — (^ k -m) или (/ c (^ k m)) с c без k
(define (sum-neg-power-m body k)
  (cond ((and (op-expr? body) (equal? (car body) '^) (= (length body) 3)
              (equal? (cadr body) k) (integer? (caddr body)) (<= (caddr body) -1))
         (- (caddr body)))
        ; (/ c k) = c·k^−1
        ((and (op-expr? body) (equal? (car body) '/) (= (length body) 3)
              (sum-k-free? (cadr body) k) (equal? (caddr body) k))
         1)
        ((and (op-expr? body) (equal? (car body) '/) (= (length body) 3)
              (sum-k-free? (cadr body) k)
              (op-expr? (caddr body)) (equal? (car (caddr body)) '^)
              (= (length (caddr body)) 3) (equal? (cadr (caddr body)) k)
              (integer? (caddr (caddr body))) (>= (caddr (caddr body)) 1))
         (caddr (caddr body)))
        (else #f)))
(define (sum-harmonic-term body k lo hi)
  (let ((m (sum-neg-power-m body k)))
    (and (integer? m) (>= m 1)
         (sum-guard (lambda ()
           (simplify (list '* (if (and (op-expr? body) (equal? (car body) '/)) (cadr body) 1)
                           (list '- (list 'harmonic hi m)
                                 (list 'harmonic (list '- lo 1) m)))))))))

; Σ_{k=a}^{b} q^k = (q^{b+1} − q^a)/(q − 1) при q ≠ 1; тело — ровно (^ q k), q без k.
; Числовое q = 1: каждый член 1 — сумма = число членов (символьные границы) или прямой счёт
(define (sum-geometric body k lo hi)
  (and (op-expr? body) (equal? (car body) '^) (= (length body) 3)
       (equal? (caddr body) k)
       (sum-k-free? (cadr body) k)
       (let ((q (cadr body)))
         (cond ((and (number? q) (= q 1))
                ; (^ 1 k) = 1 для всех k: Σ 1 = b − a + 1 (числовые границы уже посчитаны бы итератором)
                (simplify (list '+ (list '- hi lo) 1)))
               ((equal? (simplify (list '- q 1)) 0) #f)
               (else
                (sum-guard (lambda ()
                  (if (symbol? q)
                      (record-condition (list '/= (list '- q 1) 0)
                                        "знаменатель геометрической прогрессии не равен 1"))
                  (simplify (list '/ (list '- (list '^ q (list '+ hi 1)) (list '^ q lo))
                                   (list '- q 1))))))))))

; ---------- каскад ----------

(define sum-strategies '())
(define (sum-add-strategy f) (set! sum-strategies (append sum-strategies (list f))))

; выполнение списка стратегий: первая не-#f — ответ
(define (sum-try-strategies fs body k lo hi)
  (cond ((null? fs) #f)
        (else (or (sum-guard (lambda () ((car fs) body k lo hi)))
                  (sum-try-strategies (cdr fs) body k lo hi)))))

; ядро без рамки шага (для рекурсии линейности); каждый успешный путь отмечается шагом sum-path
(define (sum-symbolic-bare body k lo hi)
  (let ((form (sum-form body k lo hi)))
    (or (sum-note-path "тело не зависит от k ⇒ Σ c = c·(b − a + 1)"
                       (sum-constant body k lo hi) form)
        (sum-note-path "линейность: Σ(c·f + g) = c·Σf + Σg"
                       (sum-linear body k lo hi) form)
        (sum-note-path "геометрическая: Σ q^k = (q^{b+1} − q^a)/(q − 1), q ≠ 1"
                       (sum-geometric body k lo hi) form)
        (sum-note-path "Σ k^{−m}: harmonic(b, m) − harmonic(a − 1, m)"
                       (sum-harmonic-term body k lo hi) form)
        (sum-note-path "многочлен по k ⇒ формула Фаульхабера (числа Бернулли)"
                       (sum-poly body k lo hi) form)
        (sum-try-strategies sum-strategies body k lo hi))))

; ядро с рамкой шага и граничными случаями (шаг 1): пустой диапазон, каскад, невычисленная форма.
; Числовые границы с lo > hi — пустой диапазон 0 (конвенция числового итератора m-iter-run: m-range-list
; даёт пустой список; Карр Σ_a^b = −Σ_{b+1}^{a−1} здесь НЕ применяется — иначе прямой счёт и символьный
; путь противоречили бы друг другу; правило Карр останется для телескопических ответов Госпера, 21l.3)
(define (sum-symbolic-core body k lo hi)
  (let ((form (sum-form body k lo hi)))
    (with-step ('sum-symbolic "Символьное суммирование" form)
      (cond
        ((and (number? lo) (number? hi) (> lo hi))
         (with-step ('sum-empty "Пустой диапазон" form) 0))
        (else (let ((r (sum-symbolic-bare body k lo hi)))
                (cond ((not r)
                       (sum-note-none form
                                      "ни один путь не подошёл: константа, линейность, геометрическая, harmonic, Фаульхабер, Госпер/Абрамов/Цайльбергер")
                       (sum-unevaluated body k lo hi))
                      ((not (step-log-enabled?)) r)
                      (else
                       ; шаг проверки (аналог int-check): чем проверено — оракул numeric / skip
                       (let ((how (sum-check-how r body k lo hi)))
                         (record-step 'sum-check "Проверка ответа"
                                      (if (equal? how 'numeric)
                                          "прямая сумма в целых точках совпала с ответом"
                                          "проверка не выполнена (слишком много параметров)")
                                      form r 'detail)
                         r)))))))))

; бесконечная граница — невычисленная форма (сходимость и предел хвоста — 21l.3, Госпер)
(define (sum-inf? v) (or (equal? v 'inf) (equal? v '-inf)))

; публичный вход: тело — выражение (AST из m-c-partial или квотированное из Lisp);
; opts: 4-й аргумент — шаг s; числовые границы с lo > hi — пустой диапазон (0); inf — невычисленная форма
(define (sum-symbolic body k lo hi &rest more)
  (if (not (symbol? k)) (error "sum-symbolic: переменная — символ"))
  (cond ((or (sum-inf? lo) (sum-inf? hi))
         (sum-unevaluated body k lo hi))
        (else
         (let ((s (if (null? more) 1 (car more))))
    (cond ((and (number? s) (= s 0)) (error "sum-symbolic: шаг — не 0"))
          ((and (number? s) (= s 1)) (sum-symbolic-core body k lo hi))
          ((not (number? s)) (sum-unevaluated-step body k lo hi s))
          ; числовой шаг ≠ 1: замена k = a + s·j, j = 0..N, N = floor((b−a)/s); старт a = lo, конец — в
          ; направлении шага (числовой итератор: шаг вниз тоже идёт от lo; b < a при s < 0)
          (else
           (let* ((a lo)
                  (b hi)
                  (N (sum-floor-q (list '/ (list '- b a) s))))
             (cond ((not (number? N)) (sum-unevaluated-step body k lo hi s))
                   ((< N 0) 0)                            ; шаг не доходит: пустой диапазон
                   (else (sum-symbolic-core (sum-subst-shift body k a s) k 0 N))))))))))

; невычисленная форма с шагом (sum тело k lo hi s)
(define (sum-unevaluated-step body k lo hi s)
  (list 'sum (simplify body) k (simplify lo) (simplify hi) (simplify s)))

; floor значения выражения (упростить; число → floor) или #f
(define (sum-floor-q q)
  (let ((r (if (number? q) q (sum-guard (lambda () (simplify q))))))
    (if (number? r) (floor r) #f)))

; тело с заменой k → a + s·j
(define (sum-subst-shift body k a s)
  (simplify (subst (list '= k (list '+ a (list '* s k))) body)))

; ---------- проверка (аналог int-check) ----------

; чем проверено Σ_{k=a}^{b} t(k) = F(a, b, парам.): 'numeric / 'skip
; Ответ зависит от границ и параметров, а не от k — антиразность по k к определённой сумме неприменима;
; оракул: свободные символы (кроме k) заменяются целыми, границы — те же значения,
; прямая сумма (≤ 64 членов) сравнивается с eval-num(F). Перебор до первой успешной точки.
(define sum-check-values '(5 7 11 13))
; целое ли число (включая float 5.0 от eval-num)
(define (sum-int? v)
  (and (number? v) (or (integer? v) (< (abs (- v (floor v))) 1e-9))))

; свободные символы выражения (кроме k); builtin variables даёт подсписки на вложенных ^ — собираем сами
(define (sum-free-syms e k acc)
  (cond ((and (symbol? e) (not (number? e)) (not (equal? e k)) (not (member? e acc))) (cons e acc))
        ((and (list? e) (not (null? e)) (not (equal? (car e) 'quote)))
         (foldl (lambda (a t) (sum-free-syms t k a)) acc (cdr e)))
        (else acc)))

; подстановка списка пар ((имя . значение) ...) в выражение
(define (sum-subst-many e pairs)

  (cond ((null? pairs) e)
        (else (sum-subst-many (subst (list '= (car (car pairs)) (cdr (car pairs))) e) (cdr pairs)))))

; одна точка: все символы заменены значениями vals → прямая сумма против eval-num(F)
(define (sum-check-at F body k syms vals lo hi)
  (sum-guard
   (lambda ()
     (let* ((pairs (map2 (lambda (s v) (cons s v)) syms vals))
            (e-body (zb-C-to-binomial (sum-subst-many body pairs)))
            (lo2 (eval-num (sum-subst-many lo pairs)))
            (hi2 (eval-num (sum-subst-many hi pairs)))
            (e-F (product-fact-to-gamma (zb-C-to-binomial (sum-subst-many F pairs))))
            (nf (eval-num e-F)))
       (and (number? lo2) (number? hi2) (sum-int? lo2) (sum-int? hi2) (number? nf)
            (<= (abs (- hi2 lo2)) 63)
            (let ((nd (eval-num (sum-direct (product-fact-to-gamma e-body) k lo2 hi2))))
              (and (number? nd) (< (abs (- nd nf)) 1e-6))))))))

; перебор комбинаций значений символов (декартово произведение), до первой успешной точки
(define (sum-check-combos F body k syms lo hi vals)
  (cond ((= (length vals) (length syms))
         (sum-check-at F body k syms vals lo hi))
        (else (sum-check-try-vals F body k syms lo hi vals sum-check-values))))

(define (sum-check-try-vals F body k syms lo hi acc vs)
  (cond ((null? vs) #f)
        ; acc уже полный (в т.ч. пустые syms → проверка без подстановок) — не наращиваем дальше
        ((>= (length acc) (length syms)) (sum-check-at F body k syms acc lo hi))
        (else (or (sum-check-combos F body k syms lo hi (append acc (list (car vs))))
                  (sum-check-try-vals F body k syms lo hi acc (cdr vs))))))

; итог проверки: 'numeric (оракул сошёлся) / 'skip (проверить не удалось)
(define (sum-check-how F body k lo hi)
  (let ((syms (sum-free-syms F k '())))
    (cond ((not (list? syms)) 'skip)
          ((> (length syms) 3) 'skip)      ; больше 3 символов — не проверяем (комбинаторика)
          ((sum-check-try-vals F body k syms lo hi '() sum-check-values) 'numeric)
          (else 'skip))))

; (sum-check F тело k [lo hi]) — итог проверки ответа F суммы тела по k ('numeric / 'skip);
; lo/hi — границы суммы (по ним прямая сумма после подстановки значений символов)
(define (sum-check F body k &rest more)
  (sum-check-how F body k (if (null? more) 1 (car more))
                (if (or (null? more) (null? (cdr more)))
                    (if (null? more) 4 (car more))
                    (cadr more))))
(define (sum-direct-from body k kk b acc)
  (cond ((> kk b) acc)
        (else (sum-direct-from body k (+ kk 1) b (+ acc (simplify (subst (list '= k kk) body)))))))
(define (sum-direct body k a b)
  (if (> a b) 0 (sum-direct-from body k a b 0)))

