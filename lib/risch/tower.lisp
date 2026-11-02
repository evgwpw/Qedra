; risch/tower.lisp — построение башни exp-log по выражению: подшаг 21k.2
;
; Источники — Бронштейн, Symbolic Integration I, гл. 5 (башня exp-log, алгебраическая независимость, rischNormalize/expnosimp).
; Представление башни и rs-extend/rs-deriv — field.lisp.
;
; (rs-build-tower e x) → (башня выражение-в-θ таблица) или #f («не знаю», причина — в record-condition (risch-unknown …)).
;   таблица — список (θ исходное-выражение) для обратной подстановки (rs-back-subst e таблица).
;   Вход — каноническая форма (после simplify); головы + * ^ exp log, sinh/cosh/tanh (переписываются через exp).
;
; Алгоритм:
; 1. Предобработка (rs-prep): a^b с x в показателе (или с параметром в показателе) → exp(b·log a); (exp u)^c → exp(c·u);
;    sinh/cosh/tanh → через exp; корни и дробные степени от x, тригонометрия, прочие функции от x → «не знаю».
; 2. Ядра — все exp(·)/log(·), зависящие от x; порядок: глубина вложенности, затем «образующие» перегруппировки, log раньше
;    exp, затем размер. Ядра обрабатываются по порядку, аргумент переписывается через уже построенные уровни.
; 3. log u: u = c·∏pᵢ^mᵢ (factor-list числителя и знаменателя над ℚ[x, θ, параметры]); log u = log c + Σ mᵢ·log pᵢ, где
;    log pᵢ — аргумент η, если pᵢ = θ уровня exp η; θⱼ (+ константа), если pᵢ — аргумент уровня log с точностью до константы;
;    иначе новый уровень log pᵢ. Новый уровень трансцендентен: pᵢ неприводим и не специален (особый многочлен башни exp-log —
;    только сам θ экспоненты), поэтому D pᵢ/pᵢ имеет простой полюс, которого нет у производных остальных. log c (c ∈ ℚ>0) —
;    по простым множителям c (log 12 = 2 log 2 + log 3) — константы поля.
; 4. exp η: из суммы η выносятся константы (множитель exp(c)) и целые кратные log-уровней (множитель uⱼ^n); остаток r
;    проверяется структурной теоремой Риша: D r = Σ qⱼ·Dηⱼ (exp-уровни) + Σ qᵢ·Duᵢ/uᵢ (log-уровни) — линейная система над
;    константами (сравнение коэффициентов при мономах по x и θ, исключение Гаусса). Нет решения → новый уровень exp r.
;    Есть, все q рациональны: дробный q при log-уровне → алгебраическое расширение (exp(log x/2) = √x) → «не знаю»;
;    дробный q = n/d при exp-уровне ηⱼ → перезапуск с новой образующей exp(ηⱼ/d) (integer_powers, expnosimp):
;    exp(x) + exp(x/2) → θ = exp(x/2), exp x = θ². Целые q → exp η = exp(c)·∏θⱼ^qⱼ·∏uᵢ^qᵢ (exp(x+x²) = θ₁θ₂).
;    q с параметрами (exp(a·x) при уровне exp x) — параметры генерические: новый уровень + условие (risch-generic q).
; Отложено на подшаг 7: зависимости между константными ядрами (log 2 и log(1+√2)…, гипотеза Шануэля); вырождения параметров.

(module risch)

(define rs-max-restarts 6)                                           ; перегруппировок экспонент (integer_powers) на вызов
(define rs-max-levels 8)                                             ; бюджет высоты башни

(define (rs-fail why detail) (raise (list 'rs-unknown why detail)))

; ---------- общие помощники ----------
(define (rs-thetas tw) (map car (rs-levels tw)))
(define (rs-vars tw) (cons (rs-tower-x tw) (rs-thetas tw)))
(define (rs-const? e tw) (not (any? (lambda (v) (contains-sym? e v)) (rs-vars tw))))
(define (rs-size e) (if (pair? e) (foldl + 1 (map rs-size (cdr e))) 1))
(define (rs-member a l) (any? (lambda (b) (equal? a b)) l))
(define (rs-unique l)
  (cond ((null? l) l) ((rs-member (car l) (cdr l)) (rs-unique (cdr l))) (else (cons (car l) (rs-unique (cdr l))))))
(define (rs-level-of tw th) (assoc th (rs-levels tw)))               ; уровень с данным θ или #f
(define (rs-ratio a b) (rs-nf (list '* a (list '^ b -1))))

; ---------- 1. предобработка ----------
(define rs-trig-heads '(sin cos tan cot sec csc asin acos atan acot asec acsc asinh acosh atanh acoth asech acsch coth sech csch))

(define (rs-exp u) (list 'exp u))
(define (rs-prep e x)
  (if (or (not (pair? e)) (not (contains-sym? e x)))
      e
      (let ((h (car e)) (args (map (lambda (a) (rs-prep a x)) (cdr e))))
        (cond ((or (equal? h '+) (equal? h '*)) (cons h args))
              ((and (or (equal? h 'exp) (equal? h 'log)) (= (length args) 1)) (list h (car args)))
              ((equal? h 'ln) (list 'log (car args)))
              ((and (equal? h 'atan) (= (length args) 1)) (list 'atan (car args)))      ; 21k.5′: примитивный уровень atan
              ((and (equal? h 'tan) (= (length args) 1)) (list 'tan (car args)))        ; 21k″: tan появляется только из rs-trig-rewrite
              ((equal? h '^) (rs-prep-pow (car args) (cadr args) x e))
              ((equal? h 'sinh) (list '* 1/2 (list '+ (rs-exp (car args)) (list '* -1 (rs-exp (list '* -1 (car args)))))))
              ((equal? h 'cosh) (list '* 1/2 (list '+ (rs-exp (car args)) (rs-exp (list '* -1 (car args))))))
              ((equal? h 'tanh) (let ((t2 (rs-exp (list '* 2 (car args)))))
                                  (list '* (list '+ t2 -1) (list '^ (list '+ t2 1) -1))))
              ((equal? h 'sqrt) (rs-fail "алгебраическое расширение (корень) — не в первой версии" e))
              ((rs-member h rs-trig-heads) (rs-fail "тригонометрические и обратные функции — не в первой версии" e))
              (else (rs-fail "функция вне башни exp-log" e))))))

(define (rs-prep-pow b n x e)
  (cond ((and (pair? b) (equal? (car b) 'exp)) (rs-exp (list '* n (cadr b))))     ; (exp u)^n = exp(n·u)
        ((contains-sym? n x) (rs-exp (list '* n (list 'log b))))                  ; a^b → exp(b·log a)
        ((integer? n) (list '^ b n))
        ((number? n) (rs-fail "алгебраическое расширение (дробная степень) — не в первой версии" e))
        (else (rs-exp (list '* n (list 'log b))))))                               ; x^a, a — параметр: exp(a·log x)

; ---------- 2. ядра и их порядок ----------
(define (rs-kernel? e x) (and (pair? e) (member? (car e) '(exp log atan tan)) (contains-sym? e x)))
(define (rs-kernels e x)                                             ; все ядра (с повторами), внутренние тоже
  (if (not (pair? e))
      '()
      (let ((inner (apply append (map (lambda (a) (rs-kernels a x)) (cdr e)))))
        (if (rs-kernel? e x) (cons e inner) inner))))
(define (rs-kdepth k x)
  (+ 1 (foldl max 0 (map (lambda (k2) (rs-kdepth k2 x)) (rs-kernels (cadr k) x)))))

; ключ сортировки: (глубина, не-образующая, exp после log, размер)
(define (rs-kkey k gens x)
  (list (rs-kdepth k x) (if (rs-member k gens) 0 1)
        (cond ((member? (car k) '(log atan)) 0) ((equal? (car k) 'tan) 2) (else 1))      ; tan — выше exp той же глубины (21k″)
        (rs-size k)))
(define (rs-key< a b)
  (cond ((null? a) #f) ((< (car a) (car b)) #t) ((> (car a) (car b)) #f) (else (rs-key< (cdr a) (cdr b)))))
(define (rs-order-kernels ks gens x)
  (map cadr (sort (map (lambda (k) (list (rs-kkey k gens x) k)) ks) (lambda (a b) (rs-key< (car a) (car b))))))

; ---------- состояние построения: (башня отображение-ядер таблица) ----------
; отображение — ((ядро значение-в-θ) …), таблица — ((θ исходное-выражение) …)
(define (rs-st tw km tb) (list tw km tb))
(define (rs-st-map st k v) (rs-st (car st) (cons (list k v) (cadr st)) (caddr st)))

; переписать выражение через уже обработанные ядра
(define (rs-rw e km)
  (let ((hit (assoc e km)))
    (cond (hit (cadr hit)) ((pair? e) (cons (car e) (map (lambda (a) (rs-rw a km)) (cdr e)))) (else e))))

; ---------- 6. обратная подстановка ----------
(define (rs-back-subst e tb)
  (simplify (foldl (lambda (acc entry) (replace-expr acc (car entry) (cadr entry))) e tb)))

; новый уровень: свежий θ, уровень в башне, запись в таблице (исходное выражение — через обратную подстановку аргумента)
(define (rs-new-level st kind arg)
  (let* ((tw (car st)) (n (+ 1 (length (rs-levels tw)))))
    (if (> n rs-max-levels) (rs-fail "башня выше бюджета" arg))
    (let ((th (string->symbol (string-append "%t" (to-string n)))))
      (list (rs-st (rs-extend tw th kind arg) (cadr st) (cons (list th (list kind (rs-back-subst arg (caddr st)))) (caddr st)))
            th))))

; ---------- 3. логарифмы ----------
; разложение целого n ≥ 1 на простые: ((p e) …) или #f, если множитель больше предела перебора
(define (rs-int-factors n p acc)
  (cond ((= n 1) (reverse acc))
        ((> p 10000) #f)
        ((> (* p p) n) (rs-int-factors 1 p (rs-add-prime n acc)))
        ((= (remainder n p) 0) (rs-int-factors (quotient n p) p (rs-add-prime p acc)))
        (else (rs-int-factors n (+ p 1) acc))))
(define (rs-add-prime p acc)
  (if (and (pair? acc) (= (car (car acc)) p)) (cons (list p (+ 1 (cadr (car acc)))) (cdr acc)) (cons (list p 1) acc)))

; log c для константы c: рациональное c > 0 — Σ eᵢ·log pᵢ; отрицательное — log(−1) + log|c|; иное — (log c)
(define (rs-log-const c)
  (cond ((equal? c 1) 0)
        ((and (rational-number? c) (< c 0)) (list '+ (list 'log -1) (rs-log-const (- 0 c))))
        ((rational-number? c)
         (let ((fn (rs-int-factors (numer c) 2 '())) (fd (rs-int-factors (denom c) 2 '())))
           (if (and fn fd)
               (cons '+ (append (map (lambda (pe) (list '* (cadr pe) (list 'log (car pe)))) fn)
                                (map (lambda (pe) (list '* (- 0 (cadr pe)) (list 'log (car pe)))) fd)))
               (list 'log c))))
        (else (list 'log c))))

; log p для неприводимого множителя p → (состояние значение)
(define (rs-log-factor st p)
  (let* ((tw (car st)) (lv (and (symbol? p) (rs-level-of tw p))))
    (cond ((rs-const? p tw) (list st (rs-log-const p)))
          ((and lv (equal? (rs-level-kind lv) 'exp)) (list st (rs-level-arg lv)))   ; log(exp η) = η
          (else
           (let ((old (filter (lambda (l) (and (equal? (rs-level-kind l) 'log) (rs-const? (rs-ratio p (rs-level-arg l)) tw)))
                              (rs-levels tw))))
             (if (pair? old)
                 (list st (list '+ (car (car old)) (rs-log-const (rs-ratio p (rs-level-arg (car old))))))
                 (rs-new-level st 'log p)))))))

(define (rs-log-factors st fs acc)                                   ; fs — ((p m) …) → (состояние сумма)
  (if (null? fs)
      (list st (simplify (cons '+ acc)))
      (let ((r (rs-log-factor st (car (car fs)))))
        (rs-log-factors (car r) (cdr fs) (cons (list '* (cadr (car fs)) (cadr r)) acc)))))

(define (rs-log-kernel st k a)
  (let* ((fn (factor-list (numer a))) (fd (factor-list (denom a)))
         (fs (append (cdr fn) (map (lambda (pm) (list (car pm) (- 0 (cadr pm)))) (cdr fd))))
         (r (rs-log-factors st fs (list (rs-log-const (rs-ratio (car fn) (car fd)))))))
    (rs-st-map (car r) k (cadr r))))

; ---------- 4. экспоненты: структурная теорема ----------
; коэффициенты многочлена e по всем переменным vars (плоский список)
(define (rs-coeffs-all e vars)
  (if (null? vars) (list e) (apply append (map (lambda (c) (rs-coeffs-all c (cdr vars))) (coefficients e (car vars))))))

; уравнение «c = 0», c линейно по неизвестным qs → строка (a₁ … aₙ b): Σ aₖqₖ = b
(define (rs-eq-row c qs)
  (append (map (lambda (q) (rs-nf (diff q c))) qs)
          (list (rs-nf (list '* -1 (foldl (lambda (acc q) (replace-expr acc q 0)) c qs))))))

; исключение Гаусса над полем констант: частное решение (свободные неизвестные = 0) или #f
(define (rs-row-sub r s c) (map2 (lambda (a b) (rs-nf (list '+ a (list '* -1 c b)))) r s))   ; r − c·s
(define (rs-pick-row rows j seen)                                    ; (строка-с-ненулём-в-j . остальные) или #f
  (cond ((null? rows) #f)
        ((not (rs-zero? (nth (car rows) j))) (cons (car rows) (append (reverse seen) (cdr rows))))
        (else (rs-pick-row (cdr rows) j (cons (car rows) seen)))))
; (rs-gauss-elim rows '() 0 n) → (остаток опорные): приведённый ступенчатый вид; опорные — ((j строка) …), строка нормирована
; (1 в столбце j, 0 в столбцах других опорных); остаток — строки с нулями во всех n столбцах (совместность — последний элемент 0).
; Общая часть rs-gauss и rs-constant-system (prde.lisp, 21k.7a).
(define (rs-gauss-elim rows pivots j n)
  (if (= j n)
      (list rows pivots)
      (let ((pr (rs-pick-row rows j '())))
        (if (not pr)
            (rs-gauss-elim rows pivots (+ j 1) n)
            (let* ((prow (map (lambda (a) (rs-mulc a (rs-inv (nth (car pr) j)))) (car pr)))
                   (elim (lambda (r) (rs-row-sub r prow (nth r j)))))
              (rs-gauss-elim (map elim (cdr pr))
                             (cons (list j prow) (map (lambda (p) (list (car p) (elim (cadr p)))) pivots))
                             (+ j 1) n))))))
(define (rs-gauss rows n)
  (let* ((el (rs-gauss-elim rows '() 0 n)) (pivots (cadr el)))
    (and (every? (lambda (r) (rs-zero? (last r))) (car el))
         (map (lambda (k) (let ((p (assoc k pivots))) (if p (last (cadr p)) 0))) (range n)))))

; D r = Σ qⱼ·wⱼ с константами qⱼ (wⱼ = Dηⱼ для exp, Duⱼ/uⱼ для log): список q по уровням или #f
; уровни atan в структурной теореме для exp не участвуют (exp(q·atan u) через них не выражается: 21k.5′)
(define (rs-rel-levels tw) (filter (lambda (lv) (not (member? (rs-level-kind lv) '(atan tan)))) (rs-levels tw)))
(define (rs-exp-relation tw r)
  (let* ((lvs (rs-rel-levels tw)) (n (length lvs)))
    (and (> n 0)
         (let* ((qs (map (lambda (i) (string->symbol (string-append "%rsq" (to-string i)))) (range n)))
                (ws (map (lambda (lv) (if (equal? (rs-level-kind lv) 'exp) (rs-deriv tw (rs-level-arg lv)) (rs-level-dtheta lv)))
                         lvs))
                (e (rs-nf (cons '+ (cons (rs-deriv tw r) (map2 (lambda (q w) (list '* -1 q w)) qs ws)))))
                (eqs (filter (lambda (c) (not (rs-zero? c))) (rs-coeffs-all (numer e) (rs-vars tw)))))
           (rs-gauss (map (lambda (c) (rs-eq-row c qs)) eqs) n)))))

; слагаемые суммы η: константы и целые кратные log-уровней выносятся → (константа множитель остаток)
(define (rs-peel-int-log tw t)                                        ; t = n·θ(log), n ∈ ℤ → (θ n) или #f
  (let ((hit (filter (lambda (lv) (and (equal? (rs-level-kind lv) 'log) (integer? (rs-ratio t (car lv))))) (rs-levels tw))))
    (and (pair? hit) (list (car hit) (rs-ratio t (car (car hit)))))))
(define (rs-peel tw terms c fac rest)
  (if (null? terms)
      (list (rs-nf (cons '+ c)) fac (rs-nf (cons '+ rest)))
      (let* ((t (car terms)) (pl (and (not (rs-const? t tw)) (rs-peel-int-log tw t))))
        (cond ((rs-const? t tw) (rs-peel tw (cdr terms) (cons t c) fac rest))
              (pl (rs-peel tw (cdr terms) c (cons (list '^ (rs-level-arg (car pl)) (cadr pl)) fac) rest))
              (else (rs-peel tw (cdr terms) c fac (cons t rest)))))))
(define (rs-sum-terms e) (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e)))

; R4.2: exp c в нормальной форме (exp(log 2 + 1) → 2·e: слагаемые k·log p дают p^k)
(define (rs-exp-value c fac) (cons '* (if (rs-zero? c) fac (cons (const-exp-simplify c) fac))))

; R4.2: q структурной теоремы — замкнутая константа: скрытое рациональное (log 6/(log 2 + log 3) = 1) доказывается и заменяется числом;
; 'no (трансцендентное, иррациональное алгебраическое) — независимость доказана; unknown — кандидат без доказательства: ответ не выдаётся.
; Не замкнутое (параметр) — как раньше: генерическое.
(define (rs-q-normalize q)
  (if (or (rational-number? q) (not (const-closed? q)))
      q
      (let ((v (const-rational-value q)))
        (cond ((rational-number? v) v)
              ((equal? v 'unknown) (set! rs-zero-unknown #t) q)
              (else q)))))

(define (rs-exp-kernel st k a)
  (let* ((tw (car st)) (pe (rs-peel tw (rs-sum-terms (expand a)) '() '() '()))
         (c (car pe)) (fac (cadr pe)) (r (caddr pe)))
    (if (rs-zero? r)
        (rs-st-map st k (simplify (rs-exp-value c fac)))
        (let* ((qs0 (rs-exp-relation tw r)) (qs (and qs0 (map rs-q-normalize qs0))))
          (if (or (not qs) (not (every? rational-number? qs)))
              (let ((nl (rs-new-level st 'exp r)))
                (if qs (map (lambda (q) (if (and (not (rational-number? q)) (not (const-closed? q)))
                                            (record-condition (list 'risch-generic q)
                                                              "risch: параметры считаются генерическими — экспонента взята независимой")))
                            qs))
                (rs-st-map (car nl) k (simplify (rs-exp-value c (cons (cadr nl) fac)))))
              (rs-exp-dependent st k c fac r qs qs0))))))

; exp r зависим: r = Σ qⱼ·vⱼ + c₂ (vⱼ = ηⱼ для exp, θⱼ для log)
(define (rs-exp-dependent st k c fac r qs qs0)
  (let* ((tw (car st)) (lvs (rs-rel-levels tw))
         (c2 (rs-nf (cons '+ (cons r (map2 (lambda (q lv) (list '* -1 q (if (equal? (rs-level-kind lv) 'exp) (rs-level-arg lv) (car lv))))
                                          qs0 lvs)))))                    ; qs0 — решение до нормализации скрытых рациональных (q = qs доказано)
         (frac-log (filter (lambda (p) (and (equal? (rs-level-kind (cadr p)) 'log) (not (integer? (car p))))) (map2 list qs lvs)))
         (frac-exp (filter (lambda (p) (and (equal? (rs-level-kind (cadr p)) 'exp) (not (integer? (car p))))) (map2 list qs lvs))))
    (cond ((not (rs-const? c2 tw)) (rs-fail "структурная теорема: остаток не константа" k))
          ((pair? frac-log) (rs-fail "алгебраическое расширение (экспонента дробной степени логарифма) — не в первой версии" k))
          ((pair? frac-exp)                                           ; integer_powers: новые образующие exp(ηⱼ/d)
           (raise (list 'rs-restart
                        (map (lambda (p) (rs-exp (list '* (/ 1 (denom (car p))) (rs-back-subst (rs-level-arg (cadr p)) (caddr st)))))
                             frac-exp))))
          (else
           (rs-st-map st k (simplify (rs-exp-value (list '+ c c2)
                                                   (append fac (map2 (lambda (q lv) (list '^ (if (equal? (rs-level-kind lv) 'exp) (car lv) (rs-level-arg lv)) q))
                                                                     qs lvs)))))))))

; ---------- 4′. atan (21k.5′): θ = atan u, Dθ = Du/(1+u²) ∈ K — примитивный уровень ----------
; Независимость: atan u зависим от уровней atan θⱼ, если Du/(1+u²) = Σ qⱼ·Dθⱼ с константами qⱼ (линейная система, как для exp/log).
; Тогда atan u = c + Σ qⱼθⱼ, c — константа: считается численно в двух точках (должна совпасть и быть кратной π, иначе «не знаю»);
; значение действует на интервале, содержащем обе точки (atan(1/x) = π/2 − atan x при x > 0) — условие risch-atan-branch.
; Зависимости atan u − k = const с k из K (кроме сумм по уровням atan) не ищутся — отложено на подшаг 7.
(define rs-atan-pts '(11/5 3/10))
(define (rs-atan-levels tw) (filter (lambda (lv) (equal? (rs-level-kind lv) 'atan)) (rs-levels tw)))

(define (rs-atan-relation tw als w)
  (let* ((n (length als))
         (qs (map (lambda (i) (string->symbol (string-append "%raq" (to-string i)))) (range n)))
         (e (rs-nf (cons '+ (cons w (map2 (lambda (q lv) (list '* -1 q (rs-level-dtheta lv))) qs als)))))
         (eqs (filter (lambda (c) (not (rs-zero? c))) (rs-coeffs-all (numer e) (rs-vars tw)))))
    (rs-gauss (map (lambda (c) (rs-eq-row c qs)) eqs) n)))

; c (число) = n/k·π при k ≤ 12 → n/k, иначе #f
(define (rs-pi-multiple-k r k)
  (let* ((m (* r k)) (n (floor (+ m 0.5))))
    (cond ((> k 12) #f)
          ((< (abs (- m n)) 0.000000001) (/ n k))
          (else (rs-pi-multiple-k r (+ k 1))))))
(define (rs-pi-multiple c) (rs-pi-multiple-k (/ c (eval-num 'pi)) 1))

(define (rs-atan-const-at e x p) (try (eval-num (replace-expr e x p)) (lambda (err) #f)))

(define (rs-atan-dependent st k a als qs)
  (let* ((tw (car st)) (tb (caddr st)) (x (rs-tower-x tw))
         (E (cons '+ (cons (list 'atan (rs-back-subst a tb))
                           (map2 (lambda (q lv) (list '* -1 q (rs-back-subst (car lv) tb))) qs als))))
         (cs (map (lambda (p) (rs-atan-const-at E x p)) rs-atan-pts))
         (m (and (every? (lambda (c) (and c (real-numeric? c))) cs)
                 (< (abs (- (car cs) (cadr cs))) 0.000000001)
                 (rs-pi-multiple (car cs)))))
    (if (not m) (rs-fail "atan: выражается через другой уровень atan, но константа не определена" k))
    ; R4.2: кандидат m (численный) доказывается: E(p) − m·π = 0 точно в обеих точках (арктангенсы рациональных — гауссовы числа, constzero);
    ; доказанно ≠ 0 — отказ, не доказано — ответ не выдаётся (rs-zero-unknown)
    (let ((vs (map (lambda (p) (const-zero? (list '+ (replace-expr E x p) (list '* -1 m 'pi)))) rs-atan-pts)))
      (cond ((any? (lambda (v) (equal? v #f)) vs)
             (rs-fail "atan: численная константа не подтверждена точно" k))
            ((any? (lambda (v) (not (equal? v #t))) vs) (set! rs-zero-unknown #t))))
    (record-condition (list 'risch-atan-branch k)
                      "risch: atan выражен через другой уровень atan с константой, найденной в точках x = 11/5 и 3/10 (ветвь на интервале, где аргументы непрерывны)")
    (rs-st-map st k (simplify (cons '+ (cons (list '* m 'pi) (map2 (lambda (q lv) (list '* q (car lv))) qs als)))))))

(define (rs-atan-kernel st k a)
  (let* ((tw (car st)) (als (rs-atan-levels tw))
         (w (rs-mulc (rs-deriv tw a) (rs-inv (list '+ 1 (list '^ a 2)))))
         (qs (and (pair? als) (rs-atan-relation tw als w))))
    (if (and qs (every? rational-number? qs))
        (rs-atan-dependent st k a als qs)
        (let ((nl (rs-new-level st 'atan a))) (rs-st-map (car nl) k (cadr nl))))))

; ---------- 5. сборка ----------
(define (rs-process-kernel st k)
  (let* ((tw (car st)) (a (rs-nf (rs-rw (cadr k) (cadr st)))))
    (cond ((rs-const? a tw) (rs-st-map st k (list (car k) a)))
          ((equal? (car k) 'tan) (rs-tan-kernel st k a))
          ((and (equal? (car k) 'atan) (any? (lambda (lv) (equal? (rs-level-kind lv) 'tan)) (rs-levels tw)))
           (rs-fail "atan над tan: возможна зависимость atan(tan u) = u — не знаю" k))
          ((equal? (car k) 'atan) (rs-atan-kernel st k a))
          ((equal? (car k) 'log) (rs-log-kernel st k a))
          (else (rs-exp-kernel st k a)))))

; tan допустим ниже log-уровней (лог от рациональной функции θ), но не ниже exp/atan/tan:
; log u с u ∈ K(tan) — законное логарифмическое расширение, D log u = Du/u ∈ K(tan)
(define (rs-tan-placement-ok? lvs)
  (cond ((null? lvs) #t)
        ((equal? (rs-level-kind (car lvs)) 'tan)
         (every? (lambda (lv) (equal? (rs-level-kind lv) 'log)) (cdr lvs)))
        (else (rs-tan-placement-ok? (cdr lvs)))))

(define (rs-build-once e x gens)
  (let* ((p (rs-prep (rs-trig-rewrite e x) x))
         (gk (map (lambda (g) (rs-prep g x)) gens))
         (ks (rs-unique (apply append (map (lambda (z) (rs-kernels z x)) (cons p gk)))))
         (st (foldl rs-process-kernel (rs-st (rs-tower x) '() '()) (rs-order-kernels ks gk x)))
         (f (simplify (rs-rw p (cadr st))))
         (keep (rs-used-thetas (reverse (rs-levels (car st))) (list f)))
         (lvs (filter (lambda (lv) (rs-member (car lv) keep)) (rs-levels (car st)))))
    ; 21k″: tan — только верхний уровень башни, кроме log-уровней над ним: log u с u ∈ K(tan) — законное
    ; логарифмическое расширение (D log u = Du/u ∈ K), и log-случай драйвера его берёт. exp/atan над tan — нет.
    (if (not (rs-tan-placement-ok? lvs))
        (rs-fail "tan не на верхнем уровне башни (exp/log от тригонометрии) — не знаю" e))
    (list (cons x lvs)
          f
          (filter (lambda (en) (rs-member (car en) keep)) (reverse (caddr st))))))

; уровни, нужные выражению: θ входит в выражение или в аргумент нужного уровня выше (обход сверху вниз).
; Ненужные остаются от ядер, исчезнувших при переписи (log x в exp(x + log x) = x·eˣ).
(define (rs-used-thetas lvs-top-down es)
  (cond ((null? lvs-top-down) '())
        ((any? (lambda (e) (contains-sym? e (car (car lvs-top-down)))) es)
         (cons (car (car lvs-top-down)) (rs-used-thetas (cdr lvs-top-down) (cons (rs-level-arg (car lvs-top-down)) es))))
        (else (rs-used-thetas (cdr lvs-top-down) es))))

(define (rs-build-try e x gens n)
  (try (rs-build-once e x gens)
       (lambda (err)
         (let ((d (error-data err)))
           (cond ((and (pair? d) (equal? (car d) 'rs-restart) (< n rs-max-restarts))
                  (rs-build-try e x (append gens (cadr d)) (+ n 1)))
                 ((and (pair? d) (equal? (car d) 'rs-restart))
                  (rs-unknown "слишком много перегруппировок экспонент" e))
                 ((and (pair? d) (equal? (car d) 'rs-unknown)) (rs-unknown (cadr d) (caddr d)))
                 (else (error (error-message err))))))))

(define (rs-unknown why detail)
  (record-condition (list 'risch-unknown detail) (string-append "risch: " why))
  #f)

; (rs-build-tower e x) → (башня выражение-в-θ таблица) | #f
(define (rs-build-tower e x) (rs-build-try e x '() 0))
