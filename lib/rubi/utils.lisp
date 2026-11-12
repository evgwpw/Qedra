; rubi/utils.lisp — утилиты правил Rubi (RUBI.1).
; Утилиты приватны; правые части правил вызывают их как rubi::имя (eval в глобальной области).
(module rubi)

; Учёт вызовов заглушек: сколько раз правило отсеялось из-за нереализованной утилиты.
; По этой гистограмме выбираются утилиты к реализации (этап D); сбрасывается на задачу.
(define *rubi-stub-calls* (make-hash))
(define (rubi-stub name)
  (hash-set! *rubi-stub-calls* name (+ 1 (hash-ref *rubi-stub-calls* name 0)))
  #f)

; RUBI.SPEED: кэш чистых предикатов на время одного вызова rubi-integrate (ключ — equal? аргументов).
; rubi-zero? (simplify + together) и rubi-posq/negq (TogetherSimplify и числовое значение) — самые
; дорогие проверки условий: одно и то же выражение (b c - a d, дискриминант, знак параметра) спрашивают
; десятки условий подряд, а результат зависит только от аргумента. Кэшируются только составные выражения:
; на числах ответ и так мгновенный, а записи в кэш стоили бы дороже. Сбрасываются в rubi-integrate*
; (и в teстовом стенде — rubi-poly-q делает так же).
(define *rubi-zero-cache* (make-hash))
(define *rubi-posq-cache* (make-hash))
(define *rubi-pred-cache* #t)   ; диагностика: #f — кэш предикатов выключен (сравнение до/после)
(define (rubi-zero? e)
  (if (or (not *rubi-pred-cache*) (not (pair? e)))
      (or (equal? (simplify e) 0)
          (equal? (try (together e) (lambda (err) #f)) 0))
      (let ((h (hash-ref *rubi-zero-cache* e 'none)))
        (if (not (equal? h 'none))
            h
            (let ((v (or (equal? (simplify e) 0)
                         (equal? (try (together e) (lambda (err) #f)) 0))))
              (hash-set! *rubi-zero-cache* e v)
              v)))))

; FreeQ[u, x]: ни одно вхождение x (символа или любого из списка символов) нет нигде в u; u — выражение
; либо список выражений ((list a b m) в правых частях правил: вхождение в любом элементе дерева).
; Раньше проверялись только символы-элементы верхнего уровня, а аргументы шли в обратном смысле:
; FreeQ[{a, (d+e*x)^-21, 1}, x] давало #t (RUBI.S4: ложный ответ ∫x/(d+e1*x)^21 = x^2/(2(d+e1*x)^21)).
(define (rubi-freeq u x)
  (let ((xs (if (pair? x) x (list x))))
    (not (any? (lambda (v) (and (symbol? v) (contains-sym? u v))) xs))))

; EqQ[u]/NeQ[u] - сравнение с нулём (второй аргумент необязателен, RUBI.S12)
(define (rubi-eqq a &rest more)
  (rubi-zero? (if (null? more) a (list '- a (car more)))))
(define (rubi-neq a &rest more)
  (not (rubi-zero? (if (null? more) a (list '- a (car more))))))

(define (rubi-integerq x) (integer? x))
(define (rubi-igtq a b) (and (integer? a) (integer? b) (> a b)))
(define (rubi-iltq a b) (and (integer? a) (integer? b) (< a b)))
(define (rubi-igeq a b) (and (integer? a) (integer? b) (>= a b)))
(define (rubi-ileq a b) (and (integer? a) (integer? b) (<= a b)))

; знак параметра: неизвестен — ложь (как в Rubi)
; сравнения: Rubi допускает цепочки (LtQ[a,b,c] = a<b<c)
(define (rubi-gtq a b &rest more)
  (and (rubi-gtq2 a b) (or (null? more) (apply rubi-gtq (cons b more)))))
(define (rubi-ltq a b &rest more)
  (and (rubi-ltq2 a b) (or (null? more) (apply rubi-ltq (cons b more)))))
(define (rubi-geq a b &rest more)
  (and (rubi-geq2 a b) (or (null? more) (apply rubi-geq (cons b more)))))
(define (rubi-leq a b &rest more)
  (and (rubi-leq2 a b) (or (null? more) (apply rubi-leq (cons b more)))))
; RUBI.S16: GtQ/LtQ/GeQ/LeQ (IUF.m:403-471): вещественное число - как есть, иначе N[Together[u]]: константное
; выражение (pi, sqrt(2), exp(2)) сравнивается по численному значению; со свободными символами - ложь.
; Раньше любое не-число (в том числе pi, 2^(1/2)) давало ложь.
(define (rubi-const-expr? u)
  (cond ((pair? u) (every? rubi-const-expr? (cdr u)))
        ((number? u) #t)
        (else (and (symbol? u) (member? u '(pi E)) #t))))
(define (rubi-real-value u)
  (cond ((number? u) u)
        ((and (pair? u) (rubi-const-expr? u))
         (let ((v (try (eval-num (rubi-restore-e u)) (lambda (err) #f))))
           (and v (number? v) v)))
        ((member? u '(pi E)) (if (equal? u 'pi) (eval-num 'pi) (eval-num '(exp 1))))
        (else #f)))
(define (rubi-cmp2 f a b)
  (let ((x (rubi-real-value a)))
    (and x (let ((y (rubi-real-value b))) (and y (f x y))))))
(define (rubi-gtq2 a b) (rubi-cmp2 > a b))
(define (rubi-ltq2 a b) (rubi-cmp2 < a b))
(define (rubi-geq2 a b) (rubi-cmp2 >= a b))
(define (rubi-leq2 a b) (rubi-cmp2 <= a b))
; PosQ/NegQ (IntegrationUtilityFunctions.m, PosAux, RUBI.S12): число - по знаку; степень с нечётным
; целым показателем - по основанию (чётный/дробный - положительна); произведение - чётность числа
; отрицательных множителей; сумма - по первому члену; символ и прочее - положительно.
; NegQ = не нуль и не PosQ. Раньше обе были ложны для любого не-числа.
; RUBI.RULE d: PosQ[u] = PosAux[TogetherSimplify[u]] (IUF.m:605-606); числовое выражение (NumericQ)
; сравнивается по численному значению (N[u] > 0, IUF.m:615-621). Раньше TogetherSimplify не вызывался:
; для 1/(a*x^n+b*x^n) сумма не приводилась к (a+b)*x^n и PosQ[q-p] был ложен (1.1.1.7 #12).
(define (rubi-pos-aux u)
  (let ((rv (and (pair? u) (rubi-real-value u))))
    (cond (rv (try (> rv 0) (lambda (err) #t)))
        ((number? u) (try (> u 0) (lambda (err) #t)))
        ((not (pair? u)) #t)
        ((equal? (car u) '^)
         (if (and (integer? (caddr u)) (odd? (caddr u))) (rubi-pos-aux (cadr u)) #t))
        ((equal? (car u) '*)
         (even? (length (filter (lambda (f) (not (rubi-pos-aux f))) (cdr u)))))
        ((equal? (car u) '+) (rubi-pos-aux (cadr u)))
        (else #t))))
(define (rubi-pos-aux-cached u)
  (if (or (not *rubi-pred-cache*) (not (pair? u)))
      (rubi-pos-aux u)
      (let ((h (hash-ref *rubi-posq-cache* u 'none)))
        (if (not (equal? h 'none))
            h
            (let ((v (rubi-pos-aux u)))
              (hash-set! *rubi-posq-cache* u v)
              v)))))
(define (rubi-posq x) (and (not (equal? x 0)) (rubi-pos-aux-cached (rubi-together-simplify x))))
(define (rubi-negq x) (and (not (equal? x 0)) (not (rubi-pos-aux-cached (rubi-together-simplify x)))))

(define (rubi-rationalq x)
  (or (integer? x) (equal? (type-of x) 'rational)))
(define (rubi-fractionq x)
  (and (rubi-rationalq x) (not (integer? x))))

(define (rubi-sumq x) (and (pair? x) (equal? (car x) '+)))
(define (rubi-productq x) (and (pair? x) (equal? (car x) '*)))
(define (rubi-powerq x) (and (pair? x) (equal? (car x) '^)))
(define (rubi-nonsum-q x) (not (rubi-sumq x)))

; PolyQ[u, x] и PolyQ[u, x, n] (многочлен ровно степени n). Вызов с 3 аргументами раньше давал ошибку арности,
; а ошибка в условии стоила ≈ 300 мс (стек ошибки) — по 6–10 таких условий на каждое подвыражение.
; RUBI.RULE c: PolyQ[u,x] = PolynomialQ[u,x] || PolynomialQ[Together[u],x] (IUF.m:501-503);
; форма с n - то же через Together (IUF.m:505-509: Exponent и Coefficient уже по Together-форме).
; Без ветви Together дробь с сократимым НОД не считалась многочленом (23 задачи, 1.1.1.6 #7, 1.3.4-2 #9).
(define (rubi-together-safe e) (if (pair? e) (try (together e) (lambda (err) e)) e))
; IUF.m:5140-5185: Subst[u, pat, v] — «умная» подстановка. Образец — не всегда символ:
; Subst[u, x^(1/k), v] (1.1.3.2 #112) повышает/понижает степени (IUF.m:5154-5176), а не сравнивает
; структуру. Без этого в ответе оставалась разложенная степень c^(1/2) x^(-1/2) вместо (c x^q)^(1/2):
; ответ верен не при всех значениях c (потери t_1_1_3_2/28xx на полном прогоне).
(define (rubi-subst-pat u pat v)
  (cond ((symbol? pat) (subst (list (list pat v)) u))
        ((and (pair? pat) (equal? (car pat) '^) (= (length pat) 3))
         (simplify (rubi-subst-pow u (cadr pat) (caddr pat) v)))
        (else (rubi-subst-map u pat v))))
(define (rubi-subst-map u pat v)
  (cond ((equal? u pat) v)
        ((not (pair? u)) u)
        (else (cons (car u) (map (lambda (a) (rubi-subst-map a pat v)) (cdr u))))))
; Образец (a x)^n: числитель n != 1 — понижаем степень образца (IUF.m:5156-5158);
; u = (a x)^m со свободным от x m и целым m/n — v^(m/n) (IUF.m:5160-5161), иначе рекурсия по аргументам.
; Символьный образец идёт через subst: он же упрощает результат (без simplify ответ после
; подстановки x -> x^(m+1) раздувается, и 1.1.3.8 решается в 2 раза дольше мастера).
(define (rubi-subst-pow u ax n v)
  (cond ((and (rubi-rationalq n) (not (= (numer n) 1)))
         (rubi-subst-pow u ax (/ 1 (denom n))
                         (simplify (list '/ v (list '^ ax (- n (/ 1 (denom n))))))))
        ((and (pair? u) (equal? (car u) '^) (= (length u) 3)
              (equal? (cadr u) ax) (not (contains-sym? (caddr u) 'x)))
         (let ((q (simplify (list '/ (caddr u) n))))
           (if (integer? q)
               (simplify (list '^ v q))
               (list '^ (rubi-subst-pow ax ax n v) (caddr u)))))
        ((not (pair? u)) u)
        (else (cons (car u) (map (lambda (a) (rubi-subst-pow a ax n v)) (cdr u))))))
; Together в PolyQ нужен только когда в выражении есть деление: иначе (многочлен или уже
; несократимая дробь) результат тот же, а together на больших суммах стоит сотни миллисекунд.
(define (rubi-has-division? e)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) '/) #t)
        (else (any? rubi-has-division? (cdr e)))))

; RUBI.RULE c: Together в условии дорог (правила спрашивают PolyQ десятки раз про одно выражение),
; поэтому результат PolyQ кэшируется на вызов rubi-integrate вместе с ветвью Together.
(define *rubi-polyq-full-cache* (make-hash))
(define (rubi-poly-q e x &rest n)
  (let* ((key (list e x n))
         (hit (hash-ref *rubi-polyq-full-cache* key #f)))
    (if hit
        (cdr hit)
        (let ((v (rubi-poly-q1 e x n)))
          (hash-set! *rubi-polyq-full-cache* key (cons #t v))
          v))))
(define (rubi-poly-q1 e x n)
  (if (rubi-xpow-form? x)
      (rubi-poly-q-xv e (cadr x) (caddr x) n)
      (if (rubi-polynomialq e x)
          (or (null? n)
              (and (equal? (rubi-expon e x) (car n))
                   (not (rubi-zero? (rubi-coefficient e x (car n))))))
          (let ((w (if (rubi-has-division? e) (rubi-together-safe e) e)))
            (and (not (equal? w e))
                 (rubi-polynomialq w x)
                 (or (null? n)
                     (and (equal? (rubi-expon w x) (car n))
                          (not (rubi-zero? (rubi-coefficient w x (car n)))))))))))

; RUBI.S16: PolyQ[u, x^v] и PolyQ[u, x^v, n] (IUF.m:512-533): u - многочлен от x^v (v не сумма, свободно от x)
; с коэффициентами, свободными от x: все степени x в раскрытом u имеют вид v*k, k >= 0 целое; со степенью n -
; старший k равен n (Expon[u,x^v] = n и Coeff[u,x^v,n] != 0). Раньше второй аргумент (^ x v) считался
; символом: contains-sym? ложно, любое выражение объявлялось многочленом (1.3.3-2 #10 - «счастливая ошибка»).
(define (rubi-xpow-form? x)
  (and (pair? x) (equal? (car x) '^) (= (length x) 3) (symbol? (cadr x))))
; Слагаемые раскрытого u -> список (k/v . коэффициент) по степеням x^v; #f, если u не многочлен от x^v
(define (rubi-xv-terms e xs v)
  (and (not (rubi-sumq v)) (not (contains-sym? v xs))
       (let ((ts (rubi-bp-terms (rubi-expand-cached e) xs)))
         (and ts
              (let loop ((l ts) (acc '()))
                (if (null? l)
                    acc
                    (let ((q (simplify (list '/ (car (car l)) v))))
                      (and (integer? q) (>= q 0)
                           (not (contains-sym? (cdr (car l)) xs))   ; FreeQ[CoefficientList[u,x^v],x] (IUF.m:524)
                           (loop (cdr l) (cons (cons q (cdr (car l))) acc))))))))))
(define (rubi-poly-q-xv e xs v n)
  (or (rubi-poly-q-xv1 e xs v n)
      ; IUF.m:522-526: если u не многочлен по структуре, то же для Together[u].
      (let ((w (if (rubi-has-division? e) (rubi-together-safe e) e)))
        (and (not (equal? w e)) (rubi-poly-q-xv1 w xs v n)))))
(define (rubi-poly-q-xv1 e xs v n)
  (let ((ts (rubi-xv-terms e xs v)))
    (and ts
         (or (null? n)
             (let ((top (foldl (lambda (m p) (if (and (not (rubi-eqq (cdr p) 0)) (> (car p) m)) (car p) m)) 0 ts)))
               (and (equal? top (car n))
                    (let ((hit (assoc-by-equal top ts))) (and hit (not (rubi-eqq (cdr hit) 0))))))))))
; Кэш на один вызов rubi-integrate: полиномиальность одного и того же выражения спрашивают
; десятки правил.
(define *rubi-polyq-cache* (make-hash))
(define (rubi-polynomialq e x)
  (let ((hit (hash-ref *rubi-polyq-cache* (cons e x) #f)))
    (if hit
        (cdr hit)
        (let ((v (rubi-poly-q-struct e x)))
          (hash-set! *rubi-polyq-cache* (cons e x) (cons #t v))
          v))))

; Полиномиальность по структуре, без expand (он и был источником сотен миллисекунд в условиях):
; полиномиальность замкнута относительно суммы, произведения и неотрицательной целой степени.
(define (rubi-poly-q-struct e x)
  (cond ((not (contains-sym? e x)) #t)
        ((equal? e x) #t)
        ((not (pair? e)) #f)
        ((equal? (car e) '+)
         (every? (lambda (t) (rubi-poly-q-struct t x)) (cdr e)))
        ((equal? (car e) '*)
         (every? (lambda (f) (rubi-poly-q-struct f x)) (cdr e)))
        ((equal? (car e) '/)
         (and (= (length (cdr e)) 2)
              (rubi-poly-q-struct (cadr e) x)
              (not (contains-sym? (caddr e) x))))
        ((equal? (car e) '^)
         (and (= (length (cdr e)) 2)
              (integer? (nth e 2))
              (>= (nth e 2) 0)
              (rubi-poly-q-struct (cadr e) x)))
        (else #f)))
(define (rubi-linearq u x)
  (and (rubi-polynomialq u x)
       (equal? (rubi-expon u x) 1)
       (not (rubi-zero? (rubi-coefficient u x 1)))))
; MatchQ[e, pat] (RUBI.S12): образец и условие /; в правилах (rubi-matchq e (condition шаблон тест)) раньше
; вычислялись как вызов с несвязанными ?m, ?u (ошибка - условие правила ложно, ~60 правил, в том числе
; Not[MatchQ[Pq, x^m_. u_.]] в 1.1.2.x, 1.2.2.5, 1.2.3.5). Теперь макрос цитирует образец:
; (quote x) внутри шаблона - переменная интегрирования x, тест идёт в :where. Внешние ?-переменные в
; шаблоне считаются свежими (мягче исходного; ответ всё равно проходит int-check).
(define (rubi-unquote-x p)
  (cond ((and (pair? p) (equal? (car p) 'quote) (pair? (cdr p)) (null? (cddr p))) (cadr p))
        ((pair? p) (cons (rubi-unquote-x (car p)) (rubi-unquote-x (cdr p))))
        (else p)))
(define (rubi-matchq-fn e pat)
  (let* ((cp (and (pair? pat) (equal? (car pat) 'condition) (pair? (cdr pat)) (pair? (cddr pat))))
         (p (rubi-unquote-x (if cp (cadr pat) pat)))
         (w (and cp (caddr pat))))
    (try (if (if w (ac-match p e :identities #t :where w) (ac-match p e :identities #t)) #t #f)
         (lambda (err) #f))))
(defmacro (rubi-matchq e pat) (list 'rubi::rubi-matchq-fn e (list 'quote pat)))

; Sum[f, {k, lo, hi}] (RUBI.S12): слагаемые для k = lo..hi (hi может быть дробным: floor); раньше
; неизвестный символ sum (22 правила). Макрос: тело вычисляется для каждого k.
; RUBI.RULE d: генератор передаёт список в вычисленной форме (list (quote ii) 0 hi), поэтому
; переменная цикла приходит как (quote ii) — разворачиваем её; «неверный формат bindings» (1.1.3.7 #27, 1.1.3.8 #16).
(define (rubi-unquote x) (if (and (pair? x) (equal? (car x) 'quote)) (cadr x) x))
(defmacro (rubi-sum body spec)
  (let* ((items (if (and (pair? spec) (equal? (car spec) 'list)) (cdr spec) spec))
         (k (rubi-unquote (nth items 0))))
    `(let ((%hi ,(nth items 2)))
       (let %sum-loop ((,k ,(nth items 1)) (%acc '()))
         (if (> ,k %hi)
             (if (null? %acc) 0 (cons '+ (reverse %acc)))
             (%sum-loop (+ ,k 1) (cons ,body %acc)))))))
; Sign[u]: число - знак; иначе по PosAux
(define (rubi-sign u)
  (cond ((and (number? u) (equal? u 0)) 0)
        ((number? u) (if (> u 0) 1 -1))
        (else (if (rubi-pos-aux u) 1 -1))))

(define (rubi-everyq f lst) (every? (lambda (v) (apply f (list v))) lst))
(define (rubi-functionofq f u x &rest more) (rubi-stub 'rubi-functionofq))
(define (rubi-trueq x) (equal? x #t))
(define (rubi-falseq x) (equal? x #f))

; Simp[u] — упрощение; форма Simp[u,x] (упростить с учётом x) не поддержана: правила 1.1.1.2 #39
; и 1.1.1.4 #20 полагаются на полную машину Subst/Simp, и без неё их правая часть даёт unknown.
; Поэтому двухаргументная форма — ошибка (движок пробует следующего кандидата), а не тихое упрощение:
; замер на пяти задачах 1.1.1.3 — с тихим упрощением все пять отказывают, с ошибкой все пять берутся.
(define (rubi-simp u &rest rest)
  (if (and (pair? rest) (symbol? (car rest)))
      (rubi-simp-help u (car rest))
      (simplify u)))
; RUBI.C1: Simp[u,x] = NormalizeSumFactors[SimpHelp[u,x]] (IUF.m:2265-2300): x-свободные части упрощаются
; отдельно (Together), x-зависимые обходятся по структуре. Раньше Simp[u,x] = Simplify[u] целиком: коэффициенты
; b c/(b c - a d) после повторного применения правила 1.1.1.2 #39 не сокращались (b c1 - a d1 = b), форма росла
; на каждом шаге (205 попыток и 20 с на ∫(a+bx)^m (c+dx)^n), и защита «правило + выражение» не срабатывала.
; Together даёт каноническую форму (-1 b c (a d - b c)^-1) - неподвижную точку повторного шага.
(define (rubi-simp-free v)
  (if (pair? v) (try (together v) (lambda (err) v)) v))
(define (rubi-simp-help u x)
  (cond ((not (pair? u)) u)
        ((not (contains-sym? u x)) (rubi-simp-free u))
        ((equal? (car u) '*)
         (let ((free (filter (lambda (f) (not (contains-sym? f x))) (cdr u)))
               (dep (filter (lambda (f) (contains-sym? f x)) (cdr u))))
           (cons '* (append (if (null? free) '() (list (rubi-simp-free (if (null? (cdr free)) (car free) (cons '* free)))))
                            (map (lambda (f) (rubi-simp-help f x)) dep)))))
        (else (cons (car u) (map (lambda (a) (rubi-simp-help a x)) (cdr u))))))
(define (rubi-dist u v) (expand (list '* u v)))

; --- Rt[u,n]: «самый простой» корень n-й степени (Rubi/IntegrationUtilityFunctions.m, клауза Rt,
; строка 7514: Rt[u,n] = RtAux[TogetherSimplify[u],n]). Из RtAux взято существенное: корень степени
; u = v^m даёт v^(m/n), корень произведения — произведение корней, корень числа извлекается точно,
; если число — полная n-я степень; иначе остаётся выражение со степенью 1/n.
(define (rubi-rat-num-den r)
  (let ((parts (string-split (to-string r) "/")))
    (if (null? (cdr parts))
        (list (string->number (car parts)) 1)
        (list (string->number (car parts)) (string->number (cadr parts))))))

; m = k^n * rest, k наибольшее; возвращает (k . rest). Большие m и отрицательные не разбираем.
; Корень берём через exp(log m / n): ^ с вещественным показателем остаётся символьным.
(define (rubi-int-nth-split m n)
  (if (or (not (integer? m)) (< m 1) (> m 1000000000000000))
      (cons 1 m)
      (let loop ((k (floor (exp (/ (log (exact->inexact m)) (exact->inexact n))))))
        (cond ((< k 2) (cons 1 m))
              ((equal? (mod m (^ k n)) 0) (cons k (/ m (^ k n))))
              (else (loop (- k 1)))))))

(define (rubi-rt-number u n)
  (cond ((equal? u 0) 0)
        ((< u 0)
         (if (even? n)
             (list '^ u (/ 1 n))
             (let ((r (rubi-rt (- u) n)))
               (if (number? r) (- 0 r) (list '- 0 r)))))
        (else
         (let* ((nd (if (integer? u) (list u 1) (rubi-rat-num-den u)))
                (sp (rubi-int-nth-split (car nd) n))   ; числитель
                (sq (rubi-int-nth-split (cadr nd) n))  ; знаменатель
                (coef (simplify (list '/ (car sp) (car sq))))
                (rest (simplify (list '/ (cdr sp) (cdr sq)))))
           (cond ((equal? rest 1) coef)
                 ((equal? coef 1) (list '^ rest (/ 1 n)))
                 (else (list '* coef (list '^ rest (/ 1 n)))))))))

; map в диалекте одноместный — произведение корней собираем рекурсией
(define (rubi-rt-product fs n)
  (if (null? fs)
      '()
      (cons (rubi-rt (car fs) n) (rubi-rt-product (cdr fs) n))))

; RUBI.S16: Rt[u,n] = RtAux[TogetherSimplify[u],n] (IUF.m:7514, RtAux 7549-7604, предикаты 7611-7650,
; SplitProduct 7658-7668). Раньше: степень, произведение «по множителям», число - без SplitProduct/GtQ/LtQ/
; NegSumBaseQ, поэтому Rt[-b^2, 2] давал (-1)^(1/2)*b вместо (-b^2)^(1/2), а Rt[-a*(c+d x), 2] - не по Rubi.
(define (rubi-sum-base-q u)
  (or (rubi-sumq u) (and (rubi-powerq u) (rubi-odd-q (caddr u)) (rubi-sum-base-q (cadr u)))))
(define (rubi-atom-base-q u)
  (or (not (pair? u)) (and (rubi-powerq u) (rubi-odd-q (caddr u)) (rubi-atom-base-q (cadr u)))))
(define (rubi-neg-sum-base-q u)
  (or (and (rubi-sumq u) (rubi-negq (cadr u)))
      (and (rubi-powerq u) (rubi-odd-q (caddr u)) (rubi-neg-sum-base-q (cadr u)))))
(define (rubi-all-neg-term-q u)
  (cond ((and (rubi-powerq u) (rubi-odd-q (caddr u))) (rubi-all-neg-term-q (cadr u)))
        ((rubi-sumq u) (and (rubi-negq (cadr u))
                            (rubi-all-neg-term-q (if (null? (cdr (cddr u))) (caddr u) (cons '+ (cddr u))))))
        (else (rubi-negq u))))
(define (rubi-some-neg-term-q u)
  (cond ((and (rubi-powerq u) (rubi-odd-q (caddr u))) (rubi-some-neg-term-q (cadr u)))
        ((rubi-sumq u) (or (rubi-negq (cadr u))
                           (rubi-some-neg-term-q (if (null? (cdr (cddr u))) (caddr u) (cons '+ (cddr u))))))
        (else (rubi-negq u))))
(define (rubi-pred-by-name f)
  (cond ((not (symbol? f)) f)
        ((equal? f 'SumBaseQ) rubi-sum-base-q)
        ((equal? f 'AtomBaseQ) rubi-atom-base-q)
        ((equal? f 'NegSumBaseQ) rubi-neg-sum-base-q)
        ((equal? f 'AllNegTermQ) rubi-all-neg-term-q)
        ((equal? f 'SomeNegTermQ) rubi-some-neg-term-q)
        (else (lambda (v) #f))))
; Rest[u] для произведения; произведение без лишних обёрток
(define (rubi-prod-rest u) (if (null? (cdr (cddr u))) (caddr u) (cons '* (cddr u))))
(define (rubi-mul2 a b) (simplify (list '* a b)))
(define (rubi-neg-expr u) (if (number? u) (- 0 u) (simplify (list '* -1 u))))
; SplitProduct[func,u] -> (v rest) для первого множителя v с func[v]; иначе #f
(define (rubi-split-product f u)
  (let ((func (rubi-pred-by-name f)))
    (cond ((rubi-productq u)
           (if (func (cadr u))
               (list (cadr u) (rubi-prod-rest u))
               (let ((lst (rubi-split-product func (rubi-prod-rest u))))
                 (and lst (list (car lst) (rubi-mul2 (cadr u) (cadr lst)))))))
          ((func u) (list u 1))
          (else #f))))
(define (rubi-nth-root u n)
  (if (number? u) (rubi-rt-number u n) (list '^ u (/ 1 n))))
(define (rubi-rt-aux u n)
  (cond
    ((rubi-powerq u) (rubi-simp (list '^ (cadr u) (simplify (list '/ (caddr u) n)))))
    ((rubi-productq u)
     (let ((l1 (rubi-split-product (lambda (v) (rubi-gtq v 0)) u)))
       (if l1
           (rubi-mul2 (rubi-rt-aux (car l1) n) (rubi-rt-aux (cadr l1) n))
           (let ((l2 (rubi-split-product (lambda (v) (rubi-ltq v 0)) u)))
             (if l2
                 (if (equal? (car l2) -1)
                     (let ((v (cadr l2)))
                       (cond
                         ((and (rubi-powerq v) (rubi-ltq (caddr v) 0))
                          (simplify (list '/ 1 (rubi-rt-aux (rubi-neg-expr (list '^ (cadr v) (rubi-neg-expr (caddr v)))) n))))
                         ((rubi-productq v)
                          (let ((rr (lambda (l) (rubi-mul2 (rubi-rt-aux (rubi-neg-expr (car l)) n) (rubi-rt-aux (cadr l) n)))))
                            (if (rubi-split-product 'SumBaseQ v)
                                (let ((a (rubi-split-product 'AllNegTermQ v)))
                                  (if a (rr a)
                                      (let ((b (rubi-split-product 'NegSumBaseQ v)))
                                        (if b (rr b)
                                            (let ((c (rubi-split-product 'SomeNegTermQ v)))
                                              (if c (rr c) (rr (rubi-split-product 'SumBaseQ v))))))))
                                (let ((d (rubi-split-product 'AtomBaseQ v)))
                                  (if d (rr d)
                                      (rubi-mul2 (rubi-rt-aux (rubi-neg-expr (cadr v)) n)
                                                 (rubi-rt-aux (rubi-prod-rest v) n)))))))
                         ((odd? n) (rubi-neg-expr (rubi-rt-aux v n)))
                         (else (rubi-nth-root u n))))
                     (rubi-mul2 (rubi-rt-aux (rubi-neg-expr (car l2)) n) (rubi-rt-aux (rubi-neg-expr (cadr l2)) n)))
                 (let ((l3 (rubi-split-product 'AllNegTermQ u)))
                   (if (and l3 (rubi-split-product 'SumBaseQ (cadr l3)))
                       (rubi-mul2 (rubi-rt-aux (rubi-neg-expr (car l3)) n) (rubi-rt-aux (rubi-neg-expr (cadr l3)) n))
                       (let ((l4 (rubi-split-product 'NegSumBaseQ u)))
                         (if (and l4 (rubi-split-product 'NegSumBaseQ (cadr l4)))
                             (rubi-mul2 (rubi-rt-aux (rubi-neg-expr (car l4)) n) (rubi-rt-aux (rubi-neg-expr (cadr l4)) n))
                             (simplify (cons '* (map (lambda (f) (rubi-rt-aux f n)) (cdr u)))))))))))))
    ((and (odd? n) (rubi-ltq u 0)) (rubi-neg-expr (rubi-rt-aux (rubi-neg-expr u) n)))
    ((and (odd? n) (rubi-negq u) (rubi-posq (rubi-neg-expr u))) (rubi-neg-expr (rubi-rt-aux (rubi-neg-expr u) n)))
    (else (rubi-nth-root u n))))
; TogetherSimplify[u] = Together[Simplify[Together[u]]] (с защитой от ошибок; числа и символы - как есть)
; Together раскрывает произведение со скобкой (-4 (a+b x) -> -4a - 4b x), Simplify Mathematica так не делает:
; берём упрощённую форму, только если она не крупнее исходной по LeafCount.
(define (rubi-together-simplify u)
  (if (not (pair? u))
      u
      (let ((v (try (together (simplify (together u))) (lambda (err) u))))
        (if (< (rubi-leaf-count v) (rubi-leaf-count u)) v u))))
(define (rubi-rt u n)
  (if (number? u)
      (if (< u 0)
          (if (even? n) (rubi-rt-number u n) (rubi-neg-expr (rubi-rt-number (- 0 u) n)))
          (rubi-rt-number u n))
      (rubi-rt-aux (rubi-together-simplify u) n)))

(define (rubi-unintegrable u x) 'unintegrable)
(define (rubi-cannot-integrate u x) 'unintegrable)
; ExpandToSum[u,x] и ExpandToSum[u,v,x] (IUF.m:3329-3355): второй аргумент v раскладывается в сумму
; одночленов и u распределяется по ней — это expand(u*v); форма в две аргумента — expand(u).
; Раньше арность 3 была ошибкой (1.3.3-2 #15: «Функция ожидает 2 аргументов»).
(define (rubi-expand-to-sum u x &rest more)
  (if (null? more) (expand u) (expand (list '* u x))))
; IntPart/FracPart (IntegrationUtilityFunctions.m, RUBI.S12): число — целая/дробная часть с усечением к нулю
; (IntPart[-3/2] = -1, FracPart[-3/2] = -1/2); сумма — по слагаемым; иначе IntPart = 0, FracPart = u.
; Раньше был floor (IntPart[-3/2] = -2), символьные выражения давали FracPart = 0.
; RUBI.S15 (строки 2953-2979): второй необязательный аргумент n и рациональный множитель m*u -> (u, m*n);
; нерациональное неслагаемое: IntPart = 0, FracPart = n*u; рациональность - RationalQ (вещественные не в счёт).
(define (rubi-int-part u &rest nn)
  (let ((n (if (null? nn) 1 (car nn))))
    (cond ((rubi-rationalq u) (truncate (* n u)))
          ((and (rubi-productq u) (rubi-rationalq (cadr u)))
           (rubi-int-part (if (null? (cdr (cddr u))) (caddr u) (cons '* (cddr u))) (* n (cadr u))))
          ((rubi-sumq u) (simplify (cons '+ (map (lambda (t) (rubi-int-part t n)) (cdr u)))))
          (else 0))))
(define (rubi-frac-part u &rest nn)
  (let ((n (if (null? nn) 1 (car nn))))
    (cond ((rubi-rationalq u) (- (* n u) (truncate (* n u))))
          ((and (rubi-productq u) (rubi-rationalq (cadr u)))
           (rubi-frac-part (if (null? (cdr (cddr u))) (caddr u) (cons '* (cddr u))) (* n (cadr u))))
          ((rubi-sumq u) (simplify (cons '+ (map (lambda (t) (rubi-frac-part t n)) (cdr u)))))
          (else (simplify (list '* n u))))))
(define (rubi-integer-part u) (rubi-int-part u))
(define (rubi-fractional-part u) (rubi-frac-part u))
(define (rubi-int-hide u x) u)

; RUBI.S16 (IUF.m:1152-1180): v = NonfreeFactors[u,x]; целое содержание вынесено (у Mathematica - через
; Together), затем RemoveContentAux[u,x]: сумма с отрицательным первым членом (NegQ) меняет знак.
; Раньше брался весь u (свободные множители оставались) и знак не менялся.
(define (rubi-remove-content u x)
  (let* ((v (rubi-nonfree-factors u x))
         (c (rubi-content v x))
         (w (if (and (integer? c) (not (equal? c 0)) (not (equal? c 1)))
                (expand (list '* (list '/ 1 c) v))
                v)))
    (if (and (rubi-sumq w) (rubi-negq (cadr w)))
        (expand (list '* -1 w))
        w)))
; Coefficient[u,x,n] для нецелого n (правила спрашивают x^(1/2) и т. п.)
(define (rubi-coefficient e x n)
  (cond ((rubi-xpow-form? x) (rubi-coefficient-xv e (cadr x) (caddr x) n))
        ((and (integer? n) (>= n 0))
         (rubi-nth-or-0 (rubi-coefficient-list e x) n))
        ((and (pair? e) (equal? (car e) '^) (equal? (cadr e) x) (equal? (caddr e) n)) 1)
        (else 0)))
; RUBI.S16: Coefficient[u, x^v, n] - коэффициент при x^(v*n) в раскрытом u (IUF.m:1249-1253 вызывает его с x^v)
(define (rubi-coefficient-xv e xs v n)
  (let ((ts (rubi-bp-terms (rubi-expand-cached e) xs)))
    (if (not ts)
        0
        (let ((hit (filter (lambda (p) (rubi-eqq (list '- (car p) (list '* v n)) 0)) ts)))
          (cond ((null? hit) 0)
                ((null? (cdr hit)) (cdr (car hit)))
                (else (simplify (cons '+ (map cdr hit)))))))))
; Coeff[expr,form,n] (IUF.m:1249): Coefficient[expr,..] и Coefficient[Together[expr],..]; при расхождении
; (Simplify[coef1 - coef2] != 0) берётся второе. Together нужен только для не-многочлена.
(define (rubi-coeff e x n)
  (let ((c1 (rubi-coefficient e x n)))
    (if (or (rubi-xpow-form? x) (rubi-poly-q-struct e x))
        c1
        (let ((w (try (together e) (lambda (err) e))))
          (if (equal? w e)
              c1
              (let ((c2 (rubi-coefficient w x n)))
                (if (rubi-zero? (list '- c1 c2)) c1 c2)))))))
; Expon[expr,form] = Exponent[Together[expr],form] (IUF.m:1239): степень по списку коэффициентов — без
; отдельного degree на больших выражениях; для не-многочлена - после Together; x^v - степень по x^v
; RUBI.J2: Expon[expr,form,h] (IUF.m:1242) = Exponent[Together[expr],form,h] - h применяется к списку показателей ненулевых
; членов; в правилах встречается только h = Min (1.3.3-2 #17, 1.4.1 #24: Expon[Px,x,Min] - наименьшая степень x). Раньше
; арность 2 -> «Функция ожидает 2 аргументов, получено 3» и правило молча отказывало (76 случаев в журнале).
(define (rubi-expon e x &rest h)
  (if (and (pair? h) (equal? (car h) 'Min))
      (rubi-expon-min e x)
      (rubi-expon-max e x)))
(define (rubi-expon-min e x)
  (if (rubi-xpow-form? x)
      (let ((ts (rubi-xv-terms e (cadr x) (caddr x))))
        (let ((es (if ts (map car (filter (lambda (p) (not (rubi-eqq (cdr p) 0))) ts)) '())))
          (if (null? es) 0 (foldl (lambda (m v) (if (< v m) v m)) (car es) es))))
      (let* ((w (if (rubi-poly-q-struct e x) e (try (together e) (lambda (err) e))))
             (cl (try (rubi-coefficient-list w x) (lambda (err) '()))))
        (let loop ((l cl) (i 0))
          (cond ((null? l) 0)
                ((rubi-eqq (car l) 0) (loop (cdr l) (+ i 1)))
                (else i))))))
(define (rubi-expon-max e x)
  (if (rubi-xpow-form? x)
      (let ((ts (rubi-xv-terms e (cadr x) (caddr x))))
        (if ts (foldl (lambda (m p) (if (and (not (rubi-eqq (cdr p) 0)) (> (car p) m)) (car p) m)) 0 ts) 0))
      (let* ((w (if (rubi-poly-q-struct e x) e (try (together e) (lambda (err) e))))
             (cl (try (rubi-coefficient-list w x) (lambda (err) '()))))
        (if (null? cl) 0 (- (length cl) 1)))))
(define (rubi-simplify-integrand u x) (simplify u))
(define (rubi-numer e) (numer e))
(define (rubi-denom e) (denom e))
; GCD/Mod/Quotient на рациональных (RUBI.S12): Mod[3/2,1] = 1/2, Quotient = floor(a/b); раньше «целые числа» - ошибка
(define (rubi-gcd a b)
  (if (and (integer? a) (integer? b))
      (gcd a b)
      (/ (gcd (numer a) (numer b)) (lcm (denom a) (denom b)))))
(define (rubi-mod a b)
  (if (and (integer? a) (integer? b))
      (mod a b)
      (- a (* b (floor (/ a b))))))
(define (rubi-quotient a b)
  (if (and (integer? a) (integer? b))
      (quotient a b)
      (floor (/ a b))))

(define (rubi-free-factors u x)
  (if (and (pair? u) (equal? (car u) '*))
      (let ((fs (filter (lambda (f) (rubi-freeq f x)) (cdr u))))
        (cond ((null? fs) 1) ((null? (cdr fs)) (car fs)) (else (cons '* fs))))
      (if (rubi-freeq u x) u 1)))
(define (rubi-nonfree-factors u x)
  (if (and (pair? u) (equal? (car u) '*))
      (let ((fs (filter (lambda (f) (not (rubi-freeq f x))) (cdr u))))
        (cond ((null? fs) 1) ((null? (cdr fs)) (car fs)) (else (cons '* fs))))
      (if (rubi-freeq u x) 1 u)))
(define (rubi-activate-trig u) u)
(define (rubi-expand-trig-reduce u x) (expand u))
; InertTrigQ[f] — IUF.m:6160: f — одна из шести (инертных) тригонометрических голов.
; InertTrigQ[f,g] — IUF.m:6162: f и g совпадают либо взаимно обратны (InertReciprocalQ, IUF.m:6170);
; InertTrigQ[f,g,h] — IUF.m:6167: InertTrigQ[f,g] && InertTrigQ[g,h].
; В порте инертных голов нет (utils-c.lisp:8): инертная тригонометрия и обычная — одно и то же,
; поэтому f может прийти и узлом (sin x) — тогда сравниваем головы.
(define (rubi-trig-head-of f) (if (pair? f) (car f) f))
(define (rubi-inert-reciprocal-q f g)
  (let ((f (rubi-trig-head-of f)) (g (rubi-trig-head-of g)))
    (or (and (equal? f 'sin) (equal? g 'csc))
        (and (equal? f 'cos) (equal? g 'sec))
        (and (equal? f 'tan) (equal? g 'cot)))))
(define (rubi-inert-trig-q f &rest more)
  (let ((f (rubi-trig-head-of f)))
    (cond ((null? more) (member? f '(sin cos tan cot sec csc)))
          ((null? (cdr more))
           (let ((g (car more)))
             (if (equal? f (rubi-trig-head-of g))
                 (rubi-inert-trig-q f)
                 (or (rubi-inert-reciprocal-q f g) (rubi-inert-reciprocal-q g f)))))
          (else (and (rubi-inert-trig-q f (car more))
                     (rubi-inert-trig-q (car more) (cadr more)))))))

(define (rubi-linear-match-q u x)
  (and (rubi-polynomialq u x) (<= (rubi-safe-degree u x) 1)))
; RUBI.S8: poly-quotient/-remainder/-gcd бросают «ожидается многочлен», если коэффициенты не многочлены
; от параметров (c^-1 и т. п.); исключение в глубоком стеке сопоставителя стоит 40-180 мс, и правила
; звали это по 4-6 раз на задачу (2-4 с). poly? (одно выражение) в этих случаях ложь — отказ без броска,
; с тем же запасным значением, что давал перехват ошибки. Проверено: poly? = #f <=> ошибка у всех трёх.
(define (rubi-poly2? a b) (and (poly? a) (poly? b)))
; RUBI.C1: poly-quotient/poly-remainder отказывают на коэффициентах вида b/a (степень -1 свободного символа), а откат
; давал remainder = 0 и quotient = 1: PolynomialRemainder[1, 1 - b x/a, x] "= 0" - 1.1.1.5 #3 (Px (a+b x)^m (c+d x)^n,
; EqQ[remainder, 0]) срабатывало на ∫(1 - b x/a)^n/(1 + b x/a) и шагало m -> m+1 до исчерпания бюджета (14 задач из 93).
; Теперь деление с произвольными x-свободными коэффициентами - длинное деление по спискам коэффициентов (как в Mathematica).
(define (rubi-pd-sub ra rb c)    ; ra - c*rb (рб короче или равен ра; хвост ра остаётся)
  (if (null? rb)
      ra
      (cons (simplify (list '- (car ra) (list '* c (car rb)))) (rubi-pd-sub (cdr ra) (cdr rb) c))))
(define (rubi-pd-trim l) (if (and (pair? l) (rubi-eqq (car l) 0)) (rubi-pd-trim (cdr l)) l))
; список коэффициентов по убыванию степени (k - степень первого) -> многочлен от x
(define (rubi-pd-poly desc x)
  (let loop ((l desc) (k (- (length desc) 1)) (acc '()))
    (if (null? l)
        (if (null? acc) 0 (simplify (cons '+ (reverse acc))))
        (loop (cdr l) (- k 1) (if (rubi-eqq (car l) 0) acc (cons (list '* (car l) (list '^ x k)) acc))))))
(define (rubi-poly-divide-generic a b x)    ; (q . r) или #f
  (and (rubi-polynomialq a x) (rubi-polynomialq b x)
       (let ((ra (rubi-pd-trim (reverse (rubi-coefficient-list a x))))
             (rb (rubi-pd-trim (reverse (rubi-coefficient-list b x)))))
         (and (pair? rb) (< (length ra) 40)
              (let loop ((ra ra) (q '()))
                (if (< (length ra) (length rb))
                    (cons (if (null? q) 0 (simplify (cons '+ (map (lambda (p) (list '* (cdr p) (list '^ x (car p)))) q))))
                          (rubi-pd-poly ra x))
                    (let ((c (simplify (list '/ (car ra) (car rb)))))
                      (loop (cdr (rubi-pd-sub ra rb c))
                            (cons (cons (- (length ra) (length rb)) c) q)))))))))
(define (rubi-polynomial-remainder a b x)
  (let ((g (lambda () (let ((r (try (rubi-poly-divide-generic a b x) (lambda (err) #f)))) (if r (cdr r) 0)))))
    (if (rubi-poly2? a b) (try (poly-remainder a b x) (lambda (err) (g))) (g))))
(define (rubi-polynomial-quotient a b x)
  (let ((g (lambda () (let ((r (try (rubi-poly-divide-generic a b x) (lambda (err) #f)))) (if r (car r) 1)))))
    (if (rubi-poly2? a b) (try (poly-quotient a b x) (lambda (err) (g))) (g))))
; RUBI.RULE a: PolynomialDivide[u,v,x] = quo + free*monomial*rem/ExpandToSum[v,x] (IUF.m:3298-3310) —
; это СУММА (квоциент плюс остаток, делённый на v), как описано в usage (IUF.m:3296). Раньше возвращалась
; пара (quotient remainder): правило Int[PolynomialDivide[...],x] получало список и интеграл не брался
; (59 задач: x^10/(a+b*x^2), (a+b*x^2)^2/(c+d*x^2), ...). Остаток приводится к общему одночлену, как в исходнике.
(define (rubi-expon-list e x)
  (let loop ((cl (rubi-coefficient-list e x)) (k 0) (acc '()))
    (cond ((null? cl) (reverse acc))
          ((rubi-zero? (car cl)) (loop (cdr cl) (+ k 1) acc))
          (else (loop (cdr cl) (+ k 1) (cons k acc))))))
; Apply[Plus, Map[Simp[Together[Coefficient[e,x,#]*x^#/div],x]], Exponent[e,x,List]]
(define (rubi-simp-term-sum e x div)
  (let ((ts (map (lambda (k)
                   (let ((num (list '* (rubi-coefficient e x k) (list '^ x k))))
                     (rubi-simp (try (together (if (equal? div 1) num (list '/ num div)))
                                     (lambda (err) (if (equal? div 1) num (list '/ num div))))
                               x)))
                 (rubi-expon-list e x))))
    (if (null? ts) 0 (simplify (cons '+ ts)))))
(define (rubi-polynomial-divide a b x)
  (let* ((quo (rubi-polynomial-quotient a b x))
         (rem0 (rubi-polynomial-remainder a b x))
         (rem (try (together rem0) (lambda (err) rem0)))
         (quo1 (rubi-simp-term-sum quo x 1))
         (free (rubi-free-factors rem x))
         (rem2 (rubi-nonfree-factors rem x))
         (mon (list '^ x (rubi-expon-min rem2 x)))
         (mon (if (rubi-negq (try (rubi-coefficient rem x 0) (lambda (err) 1)))
                  (list '* -1 mon)
                  mon))
         (rem3 (rubi-simp-term-sum rem2 x mon))
         (div (if (rubi-binomial-q b x)
                  (rubi-expand-to-sum b x)
                  b)))
    (simplify (list '+ quo1 (list '* free mon rem3 (list '^ div -1))))))
(define (rubi-poly-divide-pair a b x)
  (list (rubi-polynomial-quotient a b x) (rubi-polynomial-remainder a b x)))
; SubstFor[u,f,x]: f с заменой x на u (правила зовут с тремя аргументами)
(define (rubi-subst-for u f x) (subst (list (list x u)) f))
(define (rubi-subst-for-inverse-function u f x) (subst (list (list x u)) f))

; FractionalPowerQ[u] — IUF.m:206: степень (^ база рациональный_нецелый)
(define (rubi-fractional-power-q u)
  (and (pair? u) (equal? (car u) '^)
       (number? (caddr u)) (not (integer? (caddr u)))))

; CalculusQ[u]: внутри вызов integrate/diff — подстановка дробной степени их не трогает (IUF.m, FractionalPowerOfLinear)
(define (rubi-calculus-q u)
  (and (pair? u) (member? (car u) (list 'integrate 'diff))))

; SubstForFractionalPowerAuxQ[u,v] — IUF.m:1824: есть ли внутри u дробная степень с базой v
(define (rubi-subst-for-fractional-power-aux-q u v)
  (cond ((not (pair? u)) #f)
        ((and (rubi-fractional-power-q u) (equal? (cadr u) v)) #t)
        (else (any? (lambda (e) (rubi-subst-for-fractional-power-aux-q e v)) u))))

; SubstForFractionalPowerQ[u,v,x] — IUF.m:1815: замена x=v^(1/n) не усложняет алгебраических частей u
(define (rubi-subst-for-fractional-power-q u v x)
  (cond ((or (not (pair? u)) (rubi-freeq u x)) #t)
        ((rubi-fractional-power-q u) (rubi-subst-for-fractional-power-aux-q u v))
        (else (every? (lambda (e) (rubi-subst-for-fractional-power-q e v x)) u))))

; FractionalPowerOfLinear[u,n,v,x] — IUF.m:6065: (n a+b*x) для первой дробной степени линейного,
; либо #f; состояние (n,v) протаскивается по дереву, как Scan+Throw в исходнике
(define (rubi-fpl-scan u n v x)
  (cond ((or (not (pair? u)) (rubi-freeq u x)) (list n v))
        ((rubi-calculus-q u) #f)
        ((and (rubi-fractional-power-q u) (rubi-linearq (cadr u) x)
              (or (equal? v #f) (equal? (cadr u) v)))
         (list (lcm (denom (caddr u)) n) (cadr u)))
        (else (let loop ((l (cdr u)) (st (list n v)))
                (cond ((or (not st) (null? l)) st)
                      ((not (pair? (car l))) (loop (cdr l) st))
                      (else (loop (cdr l) (rubi-fpl-scan (car l) (car st) (cadr st) x))))))))

(define (rubi-fractional-power-of-linear u n v x)
  (let ((st (rubi-fpl-scan u n v x)))
    (if st st #f)))

; SubstForFractionalPower[u,v,n,w,x] — IUF.m:1874: v^(m/n) -> x^m, x -> w
(define (rubi-subst-for-fractional-power u v n w x)
  (cond ((not (pair? u)) (if (equal? u x) w u))
        ((and (rubi-fractional-power-q u) (equal? (cadr u) v))
         (list '^ x (* n (caddr u))))
        (else (cons (car u)
                    (map (lambda (e) (rubi-subst-for-fractional-power e v n w x)) (cdr u))))))

; SubstForFractionalPowerOfLinear[u,x] — IUF.m:6057: (v n a+b*x 1/b) либо #f
(define (rubi-subst-for-fractional-power-of-linear u x)
  (let ((lst (rubi-fractional-power-of-linear u 1 #f x)))
    (if (or (not (pair? lst)) (equal? (cadr lst) #f))
        #f
        (let* ((n (car lst))
               (lin (cadr lst))
               (a (rubi-coefficient lin x 0))
               (b (rubi-coefficient lin x 1))
               (w (simplify (list '+ (list '* -1 (list '/ a b)) (list '^ x n))))
               (tmp (simplify (list '* (list '^ x (list '- n 1))
                                    (rubi-subst-for-fractional-power u lin n w x)))))
          (list (rubi-nonfree-factors tmp x) n lin
                (list '/ (rubi-free-factors tmp x) b))))))

(define (rubi-subst-for-fractional-power-of-quotient-of-linears u x) u)

; PseudoBinomialParts[u,x]: u = a + b*(c+d*x)^n с целым n > 2; возвращает (a b c d n), иначе #f.
; По исходнику (IntegrationUtilityFunctions.m, клауза PseudoBinomialParts, строка 1524):
; n = степень, d = Rt[старший коэффициент, n], c = a_{n-1}/(n*d^(n-1)), остаток должен быть
; свободен от x. Степень ограничена: expand разности (c+dx)^n дорожает как n.
(define (rubi-pseudo-binomial-parts u x)
  (let ((ue (and (rubi-polynomialq u x) (rubi-expand-cached u)))
        (n (and (rubi-polynomialq u x) (rubi-safe-degree u x))))
    (if (and (integer? n) (> n 2) (<= n 8))
        (let* ((d (rubi-rt (rubi-coefficient ue x n) n))
               (d1 (simplify (list '^ d (list '- n 1))))
               (c (simplify (list '/ (rubi-coefficient ue x (- n 1))
                                  (list '* n d1))))
               (pow (list '^ (list '+ c (list '* d x)) n))
               (a (rubi-simp (expand (list '- ue pow)))))
          (if (and (not (rubi-zero? a)) (not (contains-sym? a x))
                   (not (contains-sym? c x)) (not (contains-sym? d x)))
              (list a 1 c d n)
              #f))
        #f)))

(define (rubi-pseudo-binomial-q u x)
  (if (rubi-pseudo-binomial-parts u x) #t #f))

; PseudoBinomialPairQ[u,v,x]: у u и v одна и та же часть (c+d*x)^n (сравниваем c, d, n)
(define (rubi-pseudo-binomial-pair-q u v x)
  (let ((p (rubi-pseudo-binomial-parts u x)))
    (if (not p)
        #f
        (let ((q (rubi-pseudo-binomial-parts v x)))
          (and q
               (rubi-eqq (nth p 2) (nth q 2))
               (rubi-eqq (nth p 3) (nth q 3))
               (equal? (nth p 4) (nth q 4)))))))

; NormalizePseudoBinomial[u,x] = a + b*(c+d*x)^n по тем же частям
(define (rubi-normalize-pseudo-binomial u x)
  (let ((p (rubi-pseudo-binomial-parts u x)))
    (if (not p)
        (error "rubi: u не псевдобином")
        (list '+ (nth p 0)
              (list '* (nth p 1) (list '^ (list '+ (nth p 2) (list '* (nth p 3) x))
                                       (nth p 4)))))))
(define (rubi-fractional-power-factor-q u x) (rubi-stub 'rubi-fractional-power-factor-q))
; IntBinomialQ/IntQuadraticQ/IntLinearQ — применимость специальных биномиальных форм.
; Источник (Rubi 4.17.3.0, MIT), сверено с .m:
;   IntLinearQ    — IntegrationRules/1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/
;                   "1.1.1.2 (a+b x)^m (c+d x)^n.m", клауза после правил (строка 44);
;   IntBinomialQ  — .../1.1.3 General/"1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m", клауза (строка 73);
;   IntQuadraticQ — .../1.2.1 Quadratic/"1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m", клауза (строка 151).
; Смысл: «этот интеграл сводится к не-гипергеометрическим функциям»; если не сходится — правило
; из ветви AppellF1/Hypergeometric2F1 не применяем.

; IntLinearQ[a,b,c,d,m,n,x]: (a+b*x)^m*(c+d*x)^n берётся без гипергеометрических функций
(define (rubi-int-linear-q a b c d m n x)
  (or (rubi-igtq m 0)
      (rubi-igtq n 0)
      (rubi-integers-q (list (* 3 m) (* 3 n)))
      (rubi-integers-q (list (* 4 m) (* 4 n)))
      (rubi-integers-q (list (* 2 m) (* 6 n)))
      (rubi-integers-q (list (* 6 m) (* 2 n)))
      (rubi-iltq (+ m n) -1)
      (and (rubi-integerq (+ m n)) (rubi-rationalq m))))

; IntBinomialQ[a,b,c,d,n,p,q,x]: (a+b*x^n)^p*(c+d*x^n)^q — то же для двучленов по x^n
; У Rubi три определения под одним именем (в файлах правил): 7 аргументов — 1.1.3.2.m:118 (a b c n m p x),
; 8 — 1.1.3.3.m:73, 10 — 1.1.3.4.m:89 (a b c d e m n p q x); диспетчер — по числу аргументов.
(define (rubi-int-binomial-q a b c d n p q &rest more)
  (cond ((null? more) (rubi-int-binomial-q7 a b c d n p q))
        ((null? (cdr more)) (rubi-int-binomial-q8 a b c d n p q (car more)))
        ((and (pair? (cdr more)) (pair? (cddr more)) (null? (cdr (cddr more))))
         (rubi-int-binomial-q10 a b c d n p q (car more) (cadr more) (caddr more)))
        (else #f)))

; IntBinomialQ[a,b,c,n,m,p,x] (1.1.3.2.m:118): (c x)^m (a+b x^n)^p берётся без гипергеометрических функций.
; Порядок клауз и скобки — как в исходнике (&& сильнее ||).
(define (rubi-int-binomial-q7 a b c n m p x)
  (or (rubi-igtq p 0)
      (and (rubi-rationalq m) (rubi-integers-q (list n (* 2 p))))
      (rubi-integerq (+ (/ (+ m 1) n) p))
      (and (or (rubi-eqq n 2) (rubi-eqq n 4)) (rubi-integers-q (list (* 2 m) (* 4 p))))
      (and (rubi-eqq n 2) (rubi-integerq (* 6 p)) (or (rubi-integerq m) (rubi-integerq (- m p))))))

; IntBinomialQ[a,b,c,d,e,m,n,p,q,x] (1.1.3.4.m:89): (e x)^m (a+b x^n)^p (c+d x^n)^q без функций Аппеля.
(define (rubi-int-binomial-q10 a b c d e m n p q x)
  (or (rubi-integers-q (list p q))
      (rubi-igtq p 0)
      (rubi-igtq q 0)
      (and (rubi-eqq n 2) (or (rubi-integers-q (list m (* 2 p) (* 2 q)))
                             (rubi-integers-q (list (* 2 m) p (* 2 q)))
                             (rubi-integers-q (list (* 2 m) (* 2 p) q))))
      (and (rubi-eqq n 4) (or (rubi-integers-q (list m p (* 2 q)))
                             (rubi-integers-q (list m (* 2 p) q))))
      (and (rubi-eqq n 2) (rubi-integers-q (list (/ m 2) (+ p 1/3) q))
           (or (rubi-eqq (+ (* b c) (* 3 a d)) 0) (rubi-eqq (- (* b c) (* 9 a d)) 0)))
      (and (rubi-eqq n 2) (rubi-integers-q (list (/ m 2) (+ q 1/3) p))
           (or (rubi-eqq (+ (* a d) (* 3 b c)) 0) (rubi-eqq (- (* a d) (* 9 b c)) 0)))
      (and (rubi-eqq n 3) (rubi-integers-q (list (/ (- m 1) 3) q (- p 1/2)))
           (or (rubi-eqq (- (* b c) (* 4 a d)) 0) (rubi-eqq (+ (* b c) (* 8 a d)) 0)
               (rubi-eqq (- (* (^ b 2) (^ c 2)) (* 20 a b c d) (* 8 (^ a 2) (^ d 2))) 0)))
      (and (rubi-eqq n 3) (rubi-integers-q (list (/ (- m 1) 3) p (- q 1/2)))
           (or (rubi-eqq (- (* 4 b c) (* a d)) 0) (rubi-eqq (+ (* 8 b c) (* a d)) 0)
               (rubi-eqq (+ (* 8 (^ b 2) (^ c 2)) (* 20 a b c d) (* -1 (^ a 2) (^ d 2))) 0)))
      (and (rubi-eqq n 3) (or (rubi-integers-q (list m q (* 3 p))) (rubi-integers-q (list m p (* 3 q))))
           (rubi-eqq (+ (* b c) (* a d)) 0))
      (and (rubi-eqq n 3) (or (rubi-integers-q (list (/ (+ m 2) 3) (+ p 2/3) q))
                              (rubi-integers-q (list (/ (+ m 2) 3) (+ q 2/3) p))))
      (and (rubi-eqq n 3) (or (rubi-integers-q (list (/ m 3) (+ p 1/3) q))
                              (rubi-integers-q (list (/ m 3) (+ q 1/3) p))))))
(define (rubi-int-binomial-q8 a b c d n p q x)
  (or (rubi-integers-q (list p q))
      (rubi-igtq p 0)
      (rubi-igtq q 0)
      (and (or (rubi-eqq n 2) (rubi-eqq n 4))
           (or (rubi-integers-q (list p (* 4 q)))
               (rubi-integers-q (list (* 4 p) q))))
      (and (rubi-eqq n 2)
           (or (rubi-integers-q (list (* 2 p) (* 2 q)))
               (and (rubi-integers-q (list (* 3 p) q))
                    (rubi-eqq (+ (* b c) (* 3 a d)) 0))
               (and (rubi-integers-q (list p (* 3 q)))
                    (rubi-eqq (+ (* 3 b c) (* a d)) 0))))
      (and (rubi-eqq n 3)
           (or (rubi-integers-q (list (+ p 1/3) q))
               (rubi-integers-q (list (+ q 1/3) p))))
      (and (rubi-eqq n 3)
           (or (rubi-integers-q (list (+ p 2/3) q))
               (rubi-integers-q (list (+ q 2/3) p)))
           (rubi-eqq (+ (* b c) (* a d)) 0))))

; IntQuadraticQ[a,b,c,d,e,m,p,x]: (d+e*x)^m*(a+b*x+c*x^2)^p берётся без функций Аппеля
(define (rubi-int-quadratic-q a b c d e m p x)
  (or (rubi-integerq p)
      (rubi-igtq m 0)
      (rubi-integers-q (list (* 2 m) (* 2 p)))
      (rubi-integers-q (list m (* 4 p)))
      (and (rubi-integers-q (list m (+ p 1/3)))
           (or (rubi-eqq (+ (* c c d d) (* -1 b c d e) (* b b e e) (* -3 a c e e)) 0)
               (rubi-eqq (+ (* c c d d) (* -1 b c d e) (* -2 b b e e) (* 9 a c e e)) 0)))))
; LinearPairQ[u,v,x]: u и v линейны по x (и u ≠ x), а u/v не зависит от x — тогда замена x→v
; сводит интеграл к виду с одной «переменной» (Rubi/IntegrationUtilityFunctions.m, клауза
; LinearPairQ, строка 1387).
(define (rubi-linear-pair-q u v x)
  (and (rubi-linear-match-q u x)
       (rubi-linear-match-q v x)
       (not (equal? u x))
       (rubi-eqq (- (* (rubi-coefficient u x 0) (rubi-coefficient v x 1))
                    (* (rubi-coefficient u x 1) (rubi-coefficient v x 0)))
                 0)))
(define (rubi-nice-sqrt-q u x) (rubi-stub 'rubi-nice-sqrt-q))
; SimplerQ[u,v] (Rubi 4.17.3 IntegrationUtilityFunctions.m, строки 681-728; RUBI.S15): целые - по модулю
; (при u = -v проще отрицательное v), целое проще нецелого, дроби - по знаменателю, затем числителю,
; число проще нечисла, атом проще неатома (атомы и числа - по порядку), одинаковые головы и длины - по
; LeafCount, затем по первому различному аргументу, иначе LeafCount. Отступления: комплексные числа не
; разбираются; при равном LeafCount и разных головах (Not[OrderedQ[{v,u}]]) возвращается #f (канонического
; порядка Mathematica у нас нет). Раньше было просто LeafCount[u] < LeafCount[v] (SimplerQ[0,-1] = #f).
(define (rubi-simpler-q u v)
  (cond ((integer? u)
         (if (integer? v)
             (cond ((= u v) #f)
                   ((= u (- v)) (< v 0))
                   (else (< (abs u) (abs v))))
             #t))
        ((integer? v) #f)
        ((rubi-fractionq u)
         (if (rubi-fractionq v)
             (if (= (rubi-denom u) (rubi-denom v))
                 (rubi-simpler-q (rubi-numer u) (rubi-numer v))
                 (< (rubi-denom u) (rubi-denom v)))
             #t))
        ((rubi-fractionq v) #f)
        ((number? u) (if (number? v) (<= u v) #t))
        ((number? v) #f)
        ((not (pair? u))
         (cond ((pair? v) #t)
               ((and (symbol? u) (symbol? v)) (not (string<? (symbol->string v) (symbol->string u))))
               (else #t)))
        ((not (pair? v)) #f)
        ((equal? (car u) (car v))
         (if (= (length u) (length v))
             (if (= (rubi-leaf-count u) (rubi-leaf-count v))
                 (let loop ((a (cdr u)) (b (cdr v)))
                   (cond ((null? a) #f)
                         ((equal? (car a) (car b)) (loop (cdr a) (cdr b)))
                         (else (rubi-simpler-q (car a) (car b)))))
                 (< (rubi-leaf-count u) (rubi-leaf-count v)))
             (< (length u) (length v))))
        (else (< (rubi-leaf-count u) (rubi-leaf-count v)))))
; SimplerSqrtQ[u,v] (RUBI.S12): Sqrt[u] проще Sqrt[v]; отрицательный v при неотрицательном u - нет, обратное - да;
; иначе числа - по модулю, прочее - по LeafCount. Правила зовут с двумя аргументами (раньше арность 3 - ошибка).
; RUBI.S16: по IUF.m:736-764 (LtQ[v,0] - только числа; Rt[.,2]; целые, рациональные, PosQ, LeafCount;
; при полном равенстве - Not[OrderedQ[{v,u}]], порядок выражений Mathematica заменён порядком строк;
; SimplerSqrtQ[u,u] = False).
(define (rubi-simpler-sqrt-q u v &rest more)
  (cond ((and (rubi-ltq v 0) (not (rubi-ltq u 0))) #t)
        ((and (rubi-ltq u 0) (not (rubi-ltq v 0))) #f)
        (else
         (let ((su (rubi-rt u 2)) (sv (rubi-rt v 2)))
           (cond ((integer? su) (if (integer? sv) (< su sv) #t))
                 ((integer? sv) #f)
                 ((rubi-rationalq su) (if (rubi-rationalq sv) (< su sv) #t))
                 ((rubi-rationalq sv) #f)
                 ((rubi-posq u) (if (rubi-posq v) (< (rubi-leaf-count su) (rubi-leaf-count sv)) #t))
                 ((rubi-posq v) #f)
                 ((< (rubi-leaf-count su) (rubi-leaf-count sv)) #t)
                 ((< (rubi-leaf-count sv) (rubi-leaf-count su)) #f)
                 (else (not (or (equal? v u) (string<? (to-string v) (to-string u))))))))))
; Distrib[u,v]: u умножить на каждое слагаемое суммы v
(define (rubi-distrib u v)
  (if (rubi-sumq v)
      (cons '+ (map (lambda (t) (list '* u t)) (cdr v)))
      (list '* u v)))
; MinimumMonomialExponent[u,x]: наименьшая степень x среди одночленов многочлена u
(define (rubi-minimum-monomial-exponent u x)
  (let loop ((cl (rubi-coefficient-list u x)) (i 0))
    (cond ((null? cl) 0)
          ((not (rubi-zero? (car cl))) i)
          (else (loop (cdr cl) (+ i 1))))))
; QuadraticProductQ[u,x]: произведение квадратных трёхчленов (и свободных множителей)
(define (rubi-quadratic-product-q u x)
  (if (rubi-productq u)
      (every? (lambda (f) (or (not (contains-sym? f x)) (rubi-quadratic-q f x))) (cdr u))
      (rubi-quadratic-q u x)))
; Root[poly, k] (корень многочлена по номеру) не поддержан: отказ правила без исключения
(define (rubi-root &rest args) 'rubi-no-rule)
; SumSimplerQ[u,v] (IntegrationUtilityFunctions.m, SumSimplerQ/SumSimplerAuxQ, RUBI.S12): прибавление v к u
; даёт более простую сумму. Рациональные u, v: v = 0 — нет, v > 0 — u < -1, v < 0 — u >= -1;
; иначе SumSimplerAuxQ[Expand[u], Expand[v]]. Раньше было «u — сумма», и SumSimplerQ[m,1] всегда ложь
; (38 правил, 16 из них в 1.1.1).
; RUBI.S15 (строки 774-796 исходника): рациональные - v < 0 даёт u >= -v (было u >= -1); SumSimplerAuxQ
; рекурсивно по First/Rest (слагаемые - как есть: «все v», «какое-либо u» симметричны разбиению), а в базе -
; одинаковые NonnumericFactors и отношение NumericFactor[u]/NumericFactor[v] < -1/2 (или = -1/2 при
; NumericFactor[u] < 0). Раньше в базе было правило рациональных/LeafCount: SumSimplerQ[m-1,1] давал #f.
(define (rubi-sum-simpler-rat-q u v)
  (cond ((equal? v 0) #f)
        ((> v 0) (< u -1))
        (else (>= u (- v)))))
(define (rubi-sum-simpler-aux-q u v)
  (cond ((rubi-sumq v)
         (every? (lambda (t) (or (rubi-rationalq t) (rubi-sum-simpler-aux-q u t))) (cdr v)))
        ((rubi-sumq u)
         (any? (lambda (s) (rubi-sum-simpler-aux-q s v)) (cdr u)))
        (else
         (and (not (equal? v 0))
              (equal? (rubi-nonnumeric-factors u) (rubi-nonnumeric-factors v))
              (let ((nu (rubi-numeric-factor u)) (nv (rubi-numeric-factor v)))
                (and (not (equal? nv 0))
                     (let ((r (/ nu nv)))
                       (or (< r -1/2) (and (= r -1/2) (< nu 0))))))))))
; NumericFactor[u] / NonnumericFactors[u] (строки 1100-1144): вещественный числовой множитель и остальное.
; Сумма: НОД числовых множителей слагаемых (оба отрицательные - минус НОД; ветка ContentFactor при
; LeafCount < 50 даёт то же), нечисловая часть суммы - сумма, делённая на него.
(define (rubi-numeric-factor u)
  (cond ((number? u) u)
        ((not (pair? u)) 1)
        ((equal? (car u) '^)
         (if (and (rubi-rationalq (cadr u)) (rubi-fractionq (caddr u)))
             (if (> (caddr u) 0)
                 (/ 1 (rubi-denom (cadr u)))
                 (/ 1 (rubi-denom (/ 1 (cadr u)))))
             1))
        ((equal? (car u) '*) (apply * (map rubi-numeric-factor (cdr u))))
        ((equal? (car u) '+) (rubi-numeric-factor-sum (cdr u)))
        (else 1)))
(define (rubi-numeric-factor-sum ts)
  (if (null? (cdr ts))
      (rubi-numeric-factor (car ts))
      (let ((m (rubi-numeric-factor (car ts))) (n (rubi-numeric-factor-sum (cdr ts))))
        (if (and (rubi-rationalq m) (rubi-rationalq n))
            (if (and (< m 0) (< n 0)) (- (rubi-gcd (- m) (- n))) (rubi-gcd m n))
            1))))
(define (rubi-nonnumeric-factors u)
  (cond ((number? u) 1)
        ((not (pair? u)) u)
        ((equal? (car u) '^)
         (if (and (rubi-rationalq (cadr u)) (rubi-fractionq (caddr u)))
             (simplify (list '/ u (rubi-numeric-factor u)))
             u))
        ((equal? (car u) '*) (simplify (cons '* (map rubi-nonnumeric-factors (cdr u)))))
        ((equal? (car u) '+)
         (let ((n (rubi-numeric-factor u)))
           (if (or (equal? n 1) (equal? n 0)) u (expand (list '* (list '/ 1 n) u)))))
        (else u)))
(define (rubi-sum-simpler-q u v)
  (if (and (rubi-rationalq u) (rubi-rationalq v))
      (rubi-sum-simpler-rat-q u v)
      (rubi-sum-simpler-aux-q (expand u) (expand v))))
; IntegersQ[a, b, ...]: правила вызывают с несколькими аргументами, внутренние утилиты — со списком
(define (rubi-integers-q &rest l)
  (every? integer? (if (and (pair? l) (null? (cdr l)) (pair? (car l))) (car l) l)))
(define (rubi-atom-q x) (not (pair? x)))
; Неподдержанные специальные функции возвращают метку rubi-no-rule: правая часть с меткой отвергается
; (rubi-tainted?), перебор идёт к следующему правилу. Раньше здесь был error: исключение из глубокого
; стека сопоставителя стоило 150-400 мс (до 25 % бюджета задачи при 5-6 таких правилах).
; Hypergeometric2F1[a,b,c,z], AppellF1[a,b1,b2,c,x,y] — функции CAS (шаг SF.HYP, lib/specfun.lisp): порядок аргументов
; тот же, что в Mathematica; производные и eval-num есть, так что ответ проходит int-check. Иная арность — отказ правила.
(define (rubi-hypergeometric2-f1 &rest args)
  (if (= (length args) 4) (apply hypergeometric-2f1 args) 'rubi-no-rule))
(define (rubi-appell-f1 &rest args)
  (if (= (length args) 6) (apply appell-f1 args) 'rubi-no-rule))
; RUBI.E1: эллиптические интегралы Rubi. Mathematica (https://reference.wolfram.com/language/ref/EllipticF.html,
; EllipticE, EllipticPi) принимает ПАРАМЕТР m = k^2: F(phi|m) = Int_0^phi dt/Sqrt[1 - m Sin[t]^2],
; E(phi|m) = Int_0^phi Sqrt[1 - m Sin[t]^2] dt, Pi(n; phi|m) = Int_0^phi dt/((1 - n Sin[t]^2) Sqrt[1 - m Sin[t]^2]).
; Наши elliptic-f/e/pi (lib/elliptic.lisp) принимают МОДУЛЬ k (проверено: (diff x (elliptic-f x k)) = (1 - k^2 sin^2 x)^(-1/2));
; n в Pi одинаков. Правые части Rubi (файлы правил, имена elliptic-f/elliptic-e/rubi-elliptic-pi) строят ДАННЫЕ с
; параметром m; внутри поиска ответ остаётся «сырым» (m), а перевод m -> k = (sqrt m) делает rubi-ell-convert -
; копией перед int-check и в итоговом ответе (так вложенные ответы не переводятся дважды).
(define (rubi-ell-modulus m)
  (cond ((equal? m 0) 0) ((equal? m 1) 1) (else (simplify (list '^ m 1/2)))))
(define (rubi-ell-convert e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'elliptic-f) (= (length e) 3))
         (list 'elliptic-f (rubi-ell-convert (cadr e)) (rubi-ell-modulus (rubi-ell-convert (caddr e)))))
        ((and (equal? (car e) 'elliptic-e) (= (length e) 3))
         (list 'elliptic-e (rubi-ell-convert (cadr e)) (rubi-ell-modulus (rubi-ell-convert (caddr e)))))
        ((and (equal? (car e) 'elliptic-pi) (= (length e) 4))
         (list 'elliptic-pi (rubi-ell-convert (cadr e)) (rubi-ell-convert (caddr e))
               (rubi-ell-modulus (rubi-ell-convert (car (cdr (cdr (cdr e))))))))
        (else (cons (car e) (map rubi-ell-convert (cdr e))))))
(define (rubi-has-ell? e)
  (and (pair? e)
       (or (equal? (car e) 'elliptic-f) (equal? (car e) 'elliptic-e) (equal? (car e) 'elliptic-pi)
           (any? rubi-has-ell? (cdr e)))))
(define (rubi-elliptic-pi &rest args)
  (if (= (length args) 3) (cons 'elliptic-pi args) 'rubi-no-rule))

; --- RUBI.3: утилиты главы 1.1.1 и общие предикаты ---
; Семантика — по Rubi/IntegrationUtilityFunctions.m. Часть далёких от главы 1.1.1
; имён дана безопасными заглушками (&rest, чтобы не падать по арности): они отсеивают
; правило, а ответ всё равно проходит int-check.

(define (rubi-safe-degree u x) (try (degree u x) (lambda (err) -1)))

; LeafCount: атом — 1, узел — 1 + сумма детей
(define (rubi-leaf-count u)
  (if (not (pair? u))
      1
      (+ 1 (foldl (lambda (a e) (+ a (rubi-leaf-count e))) 0 (cdr u)))))

(define (rubi-head u) (if (pair? u) (car u) u))
; имена Mathematica, переписанные движком (rubi-fix-names)
(define (rubi-not-equal a b) (not (equal? a b)))
(define (rubi-part l i) (if (pair? l) (nth l (- i 1)) #f))
(define (rubi-diff u x) (diff x u))
(define (rubi-simpler-integrand-q a &rest rest) (rubi-stub 'rubi-simpler-integrand-q))
(define (rubi-member-q lst x) (member? x lst))
(define (rubi-independent-q u x) (rubi-freeq u x))
; Divides[y,u,x] — IUF.m:7442: u/y свободно от x → частное, иначе #f
(define (rubi-divides y u x)
  (let ((v (try (simplify (list '/ u y)) (lambda (err) #f))))
    (if (and v (rubi-freeq v x)) v #f)))
(define (rubi-perfect-square-q u)
  (and (integer? u) (>= u 0)
       (try (integer? (sqrt u)) (lambda (err) #f))))
(define (rubi-odd-q u) (and (integer? u) (not (even? u))))

; HalfIntegerQ[a,b]: a-b полуцелое
(define (rubi-half-integer-q a b)
  (and (number? a) (number? b)
       (equal? (simplify (list '- a b)) 1/2)))

; Bинoмиальные/квадратичные формы (по степени многочлена)
; RUBI.S12: по структуре (IntegrationUtilityFunctions.m, BinomialParts/TrinomialParts/MonomialQ), а не по
; степени многочлена: BinomialQ - a + b*x^n либо b*x^n (n != 0, a, b, n свободны от x), TrinomialQ -
; a + b*x^n + c*x^(2n), MonomialQ - c*x^n. Раньше BinomialQ = «степень 1», MonomialQ = тавтология.
; Слагаемое -> (степень . коэффициент) со степенью-выражением, свободным от x; иначе #f.
(define (rubi-bp-term t x)
  (cond ((not (contains-sym? t x)) (cons 0 t))
        ((equal? t x) (cons 1 1))
        ((and (pair? t) (equal? (car t) '^) (equal? (cadr t) x) (not (contains-sym? (caddr t) x)))
         (cons (caddr t) 1))
        ((and (pair? t) (equal? (car t) '*))
         (let loop ((fs (cdr t)) (n 0) (c '()))
           (cond ((null? fs) (cons n (cond ((null? c) 1) ((null? (cdr c)) (car c)) (else (cons '* (reverse c))))))
                 ((not (contains-sym? (car fs) x)) (loop (cdr fs) n (cons (car fs) c)))
                 (else (let ((p (rubi-bp-term (car fs) x)))
                         (if p (loop (cdr fs) (simplify (list '+ n (car p))) (if (equal? (cdr p) 1) c (cons (cdr p) c))) #f))))))
        (else #f)))
; сумма -> список (степень . коэффициент) со слиянием равных степеней; #f, если слагаемое не c*x^n
; слагаемые u: вложенные суммы и произведение «свободные множители * сумма» (BinomialParts: ProductQ
; со свободным First) раскрываются в слагаемые
(define (rubi-bp-flatten t x)
  (cond ((rubi-sumq t) (append-map (lambda (s) (rubi-bp-flatten s x)) (cdr t)))
        ((and (rubi-productq t) (contains-sym? t x))
         (let ((xf (filter (lambda (f) (contains-sym? f x)) (cdr t))))
           (if (and (equal? (length xf) 1) (rubi-sumq (car xf)))
               (let ((free (filter (lambda (f) (not (contains-sym? f x))) (cdr t))))
                 (append-map (lambda (s) (rubi-bp-flatten (cons '* (cons s free)) x)) (cdr (car xf))))
               (list t))))
        (else (list t))))
(define (rubi-bp-terms u x)
  (let loop ((ts (rubi-bp-flatten u x)) (acc '()))
    (if (null? ts)
        acc
        (let ((p (rubi-bp-term (car ts) x)))
          (and p
               (let ((hit (assoc-by-equal (car p) acc)))
                 (loop (cdr ts)
                       (if hit
                           (map (lambda (q) (if (equal? (car q) (car p)) (cons (car q) (simplify (list '+ (cdr q) (cdr p)))) q)) acc)
                           (append acc (list p))))))))))
(define (assoc-by-equal k l)
  (cond ((null? l) #f) ((equal? (car (car l)) k) (car l)) (else (assoc-by-equal k (cdr l)))))
; BinomialParts: (a b n) или #f
; RUBI.S16: BinomialParts/TrinomialParts начинаются с PolynomialQ[u,x] -> Exponent/Coefficient по раскрытому u
; (IUF.m:851-860): (a + b x)(a - b x) - двучлен a^2 - b^2 x^2. Структурный разбор - только если u не многочлен
; или раскрытие ничего не дало.
(define (rubi-bp-terms-poly u x)
  (or (rubi-bp-terms u x)
      (and (pair? u) (not (rubi-sumq u)) (rubi-poly-q-struct u x)
           (let ((w (rubi-expand-cached u)))
             (and (not (equal? w u)) (rubi-bp-terms w x))))))
(define (rubi-binomial-parts u x)
  (let ((ts (rubi-bp-terms-poly u x)))
    (and ts (pair? ts)
         (let ((consts (filter (lambda (p) (equal? (car p) 0)) ts))
               (vars (filter (lambda (p) (not (equal? (car p) 0))) ts)))
           (and (equal? (length vars) 1)
                (list (if (null? consts) 0 (cdr (car consts))) (cdr (car vars)) (car (car vars))))))))
; TrinomialParts: (a b c n) или #f; a может отсутствовать (0), b и c обязательны
(define (rubi-trinomial-parts u x)
  (let ((ts (rubi-bp-terms-poly u x)))
    (and ts (pair? ts)
         (let ((consts (filter (lambda (p) (equal? (car p) 0)) ts))
               (vars (filter (lambda (p) (not (equal? (car p) 0))) ts)))
           (and (equal? (length vars) 2)
                (let* ((p1 (car vars)) (p2 (cadr vars))
                       (lo (if (rubi-eqq (list '- (list '* 2 (car p1)) (car p2)) 0) p1 p2))
                       (hi (if (equal? lo p1) p2 p1)))
                  (and (rubi-eqq (list '- (list '* 2 (car lo)) (car hi)) 0)
                       (list (if (null? consts) 0 (cdr (car consts))) (cdr lo) (cdr hi) (car lo)))))))))
(define (rubi-binomial-q u x) (if (rubi-binomial-parts u x) #t #f))
; RUBI.S16: QuadraticQ = PolyQ[u,x,2] && Not[Coefficient[u,x,0]===0 && Coefficient[u,x,1]===0] (IUF.m:1380-1383):
; одночлен a x^2 - не квадратный трёхчлен. Раньше - только степень 2.
(define (rubi-quadratic-q u x)
  (and (rubi-poly-q u x 2)
       (not (and (equal? (rubi-coefficient u x 0) 0) (equal? (rubi-coefficient u x 1) 0)))))
; RUBI.S16: TrinomialQ (IUF.m:568-571) - ещё Not[QuadraticQ[u,x]] и Not[MatchQ[u, w^2 /; BinomialQ[w,x]]]
(define (rubi-trinomial-q u x)
  (and (rubi-trinomial-parts u x)
       (not (rubi-quadratic-q u x))
       (not (and (rubi-powerq u) (equal? (caddr u) 2) (rubi-binomial-q (cadr u) x)))))
; Match-предикаты (IUF.m:1419-1475) - MatchQ по образцу, без распределения и раскрытия: слагаемые суммы
; (x-свободные склеиваются в a_.), x-зависимые - ровно вида c*x^k. Раньше BinomialMatchQ = BinomialQ,
; QuadraticMatchQ = «многочлен степени 2» ((x+1)^2 проходил, c*(a+b*x) - двучлен).
(define (rubi-match-xterms u x)
  (let loop ((ts (if (rubi-sumq u) (cdr u) (list u))) (acc '()))
    (cond ((null? ts) (reverse acc))
          ((not (contains-sym? (car ts) x)) (loop (cdr ts) acc))
          (else (let ((p (rubi-bp-term (car ts) x)))
                  (and p (loop (cdr ts) (cons p acc))))))))
(define (rubi-binomial-match-q u x)
  (let ((ps (rubi-match-xterms u x)))
    (and ps (= (length ps) 1) #t)))
(define (rubi-quadratic-match-q u x)
  (let ((ps (rubi-match-xterms u x)))
    (and ps (pair? ps) (<= (length ps) 2)
         (every? (lambda (p) (or (equal? (car p) 1) (equal? (car p) 2))) ps)
         (any? (lambda (p) (equal? (car p) 2)) ps))))
(define (rubi-trinomial-match-q u x)
  (let ((ps (rubi-match-xterms u x)))
    (and ps (= (length ps) 2)
         (or (rubi-eqq (list '- (car (cadr ps)) (list '* 2 (car (car ps)))) 0)
             (rubi-eqq (list '- (car (car ps)) (list '* 2 (car (cadr ps)))) 0)))))
; BinomialDegree[u,x] = n из BinomialParts; не двучлен - 0 (Rubi бросил бы ошибку)
(define (rubi-binomial-degree u x)
  (let ((p (rubi-binomial-parts u x))) (if p (nth p 2) 0)))
(define (rubi-monomial-q u x)
  (let ((p (and (contains-sym? u x) (rubi-bp-term u x))))
    (and p (not (equal? (car p) 0)) #t)))
(define (rubi-discriminant a b c) (list '- (list '^ b 2) (list '* 4 a c)))
(define (rubi-power-of-linear-q u x)
  (and (pair? u) (equal? (car u) '^) (rubi-linear-match-q (cadr u) x)))
(define (rubi-power-of-linear-match-q u x) (rubi-power-of-linear-q u x))
(define (rubi-expand-expression u x) (simplify (expand u)))

; Слагаемое -> (степень . коэффициент), если это c*x^k (c не содержит x); иначе #f
(define (rubi-split-x-term t x)
  (cond ((not (contains-sym? t x)) (cons 0 t))
        ((equal? t x) (cons 1 1))
        ((and (pair? t) (equal? (car t) '^) (equal? (cadr t) x) (integer? (caddr t)))
         (cons (caddr t) 1))
        ((and (pair? t) (equal? (car t) '*))
         (let loop ((fs (cdr t)) (k 0) (rest '()))
           (cond ((null? fs)
                  (cons k (cond ((null? rest) 1)
                                ((null? (cdr rest)) (car rest))
                                (else (cons '* rest)))))
                 ((and (pair? (car fs)) (equal? (car (car fs)) '^)
                       (equal? (car (cdr (car fs))) x) (integer? (car (cdr (cdr (car fs))))))
                  (loop (cdr fs) (+ k (car (cdr (cdr (car fs))))) rest))
                 ((equal? (car fs) x) (loop (cdr fs) (+ k 1) rest))
                 (else (loop (cdr fs) k (cons (car fs) rest))))))
        (else (cons 0 t))))

; CoefficientList по x с произвольными (символьными) коэффициентами.
; expand дорог на больших выражениях, а один и тот же Px спрашивают разные предикаты — кэшируем
; результат на время одного rubi-integrate.
(define *rubi-expand-cache* (make-hash))
(define (rubi-expand-cached e)
  (let ((hit (hash-ref *rubi-expand-cache* e #f)))
    (if hit
        (cdr hit)
        (let ((v (expand e)))
          (hash-set! *rubi-expand-cache* e (cons #t v))
          v))))

(define (rubi-coefficient-list u x)
  (let* ((e (rubi-expand-cached u))
         (ts (if (rubi-sumq e) (cdr e) (list e)))
         (pairs (filter (lambda (p) p) (map (lambda (t) (rubi-split-x-term t x)) ts)))
         (mx (foldl (lambda (m p) (if (> (car p) m) (car p) m)) 0 pairs)))
    (let loop ((k 0) (acc '()))
      (if (> k mx)
          (reverse acc)
          (let ((cs (map cdr (filter (lambda (p) (equal? (car p) k)) pairs))))
            (loop (+ k 1)
                  (cons (cond ((null? cs) 0)
                              ((null? (cdr cs)) (car cs))
                              (else (simplify (cons '+ cs))))
                        acc)))))))

(define (rubi-expand-linear-product v u a b x)
  (let* ((uu (expand (subst (list (list x (list '/ (list '- x a) b))) u)))
         (lst (rubi-coefficient-list uu x))
         (base (list '+ a (list '* b x)))
         (terms
          (let loop ((k 0) (ls lst) (acc '()))
            (if (null? ls)
                (reverse acc)
                (let ((c (car ls)))
                  (loop (+ k 1) (cdr ls)
                        (if (and (number? c) (equal? c 0))
                            acc
                            (cons (simplify (list '* v c (list '^ base k))) acc))))))))
    (cond ((null? terms) v)
          ((null? (cdr terms)) (car terms))
          (else (cons '+ terms)))))
(define (rubi-normalize-power-of-linear u x) u)
(define (rubi-normalize-integrand u x) (simplify u))

; Content многочлена по x: НОД целых коэффициентов (со знаком плюс)
(define (rubi-content u x)
  (if (rubi-polynomialq u x)
      (let ((d (rubi-safe-degree u x)))
        (if (< d 0)
            1
            (let loop ((k 0) (g 0))
              (if (> k d)
                  (if (< g 0) (- g) g)
                  (let ((c (try (coeff u x k) (lambda (err) 0))))
                    (loop (+ k 1) (if (integer? c) (gcd g c) g)))))))
      1))

; Функции от тригонометрии/логарифма
(define (rubi-trig-heads)
  '(sin cos tan cot sec csc sinh cosh tanh coth sech csch))
(define (rubi-function-of-trig u x)
  (and (pair? u) (member? (car u) (rubi-trig-heads))))
(define (rubi-function-of-log u x) (and (pair? u) (equal? (car u) 'log)))
(define (rubi-trig-q u) (and (pair? u) (member? (car u) (rubi-trig-heads))))
(define (rubi-hyperbolic-q u)
  (and (pair? u) (member? (car u) '(sinh cosh tanh coth sech csch))))
(define (rubi-inverse-function-free-q u x)
  (not (and (pair? u)
            (member? (car u) '(asin acos atan acot asec acsc asinh acosh atanh acoth asech acsch)))))
(define (rubi-algebraic-function-q u x)
  (not (and (pair? u)
            (member? (car u) (cons 'log (cons 'exp (rubi-trig-heads)))))))
(define (rubi-complex-free-q u) (not (contains-sym? u '%i)))

; D[v,x] делит u без остатка
(define (rubi-derivative-divides v u x)
  (try (begin
         (let ((dv (diff v x)))
           (equal? 0 (simplify (poly-remainder u dv x)))))
       (lambda (err) #f)))

(define (rubi-poly-gcd a b x)
  (if (rubi-poly2? a b) (try (poly-gcd a b) (lambda (err) 1)) 1))
(define (rubi-quotient-of-linears-q u x) (rubi-stub 'rubi-quotient-of-linears-q))
(define (rubi-quotient-of-linears-parts u x) '())
(define (rubi-try-pure-tan-subst u x) u)
; DeactivateTrig/ActivateTrig (IUF.m:6180-6195). Инертных голов, как в Mathematica, в порте нет, поэтому
; роль DeactivateTrig играет маскировка: на время simplify головы tan/cot/sec/csc заменяются непрозрачными
; символами, которых simplify не касается, а после simplify возвращаются (это и есть ActivateTrig).
; Зачем: simplify переписывает их в sin/cos ((^ (tan x) 3) -> (* (^ (cos x) -3) (^ (sin x) 3))), и правила
; глав 4.3 и 4.5 с образцами на tan/sec не сопоставляются никогда — см. REPORT-RUBI-C0B. sin/cos и
; гиперболические головы simplify не трогает (проверено), их маскировать не нужно.
(define (rubi-inert-lost-heads) '(tan cot sec csc))
(define (rubi-inert-sym n) (string->symbol (string-append "rubi-inert-" (to-string n))))
(define (rubi-inert-node-in tab e)
  (cond ((null? tab) #f)
        ((equal? (cdr (car tab)) e) (car tab))
        (else (rubi-inert-node-in (cdr tab) e))))
; -> (маскированное выражение число-символов таблица «символ . узел»)
(define (rubi-inert-mask-walk e x n tab)
  (cond ((not (pair? e)) (list e n tab))
        ; маскируем только линейный аргумент — как DeactivateTrigAux (IUF.m:6201: TrigQ && LinearQ)
        ((and (member? (car e) (rubi-inert-lost-heads)) (null? (cddr e)) (rubi-linearq (cadr e) x))
         (let ((hit (rubi-inert-node-in tab e)))
           (if hit
               (list (car hit) n tab)
               (let ((sym (rubi-inert-sym n)))
                 (list sym (+ n 1) (append tab (list (cons sym e))))))))
        (else
         (let* ((a (rubi-inert-mask-walk (car e) x n tab))
                (b (rubi-inert-mask-walk (cdr e) x (cadr a) (caddr a))))
           (list (cons (car a) (car b)) (cadr b) (caddr b))))))
(define (rubi-inert-key-in tab s)
  (cond ((null? tab) #f)
        ((equal? (car (car tab)) s) (car tab))
        (else (rubi-inert-key-in (cdr tab) s))))
(define (rubi-inert-unmask e tab)
  (cond ((null? tab) e)
        ((pair? e) (cons (rubi-inert-unmask (car e) tab) (rubi-inert-unmask (cdr e) tab)))
        (else (let ((hit (rubi-inert-key-in tab e)))
                (if hit (cdr hit) e)))))
; узел -> (маскированное выражение таблица); таблицу понимает rubi-inert-unmask
(define (rubi-inert-mask u x)
  (let ((r (rubi-inert-mask-walk u x 0 '())))
    (list (car r) (caddr r))))
; --- RUBI.CH-C0c шаг 3: UnifyInertTrigFunction (IUF.m:6542-7362) и ReduceInertTrig (IUF.m:6492-6539) ---
; Задача пары: cos/cot/csc свести к sin/tan/sec, чтобы сработали правила глав 4.1/4.3/4.5 (для 4.2/4.4/4.6
; файлов правил нет и в самом Rubi), а фазу аргумента m*Pi привести к 0<=m<1/2 симметриями.
; ReduceInertTrig[func,m,u] — IUF.m:6509-6539 (все клаузы): m<0, m>=2, m>=1, m>=1/2, иначе func[m*Pi+u].
(define (rubi-inert-phase m u) (if (equal? m 0) u (list '+ (list '* m 'pi) u)))
; 6514-6519: при m<0 для этих функций знак меняется (cos и sec — нет)
(define (rubi-inert-sign-flips? func) (member? func '(sin tan cot csc)))
(define (rubi-reduce-inert-trig func m u)
  (cond ((< m 0)
         (if (>= m -1/4)
             (list func (rubi-inert-phase m u))                                  ; 6511-6512: |m| мал — оставляем
             (let ((r (rubi-reduce-inert-trig func (- 0 m) (list '* -1 u))))      ; 6514-6519
               (if (rubi-inert-sign-flips? func) (list '- r) r))))
        ((>= m 2) (rubi-reduce-inert-trig func (- m 2) u))                       ; 6520-6521: Mod[m,2]
        ((>= m 1)
         (let ((r (rubi-reduce-inert-trig func (- m 1) u)))                      ; 6522-6529
           (if (member? func '(sin cos sec csc)) (list '- r) r)))
        ((>= m 1/2)
         (cond ((equal? func 'sin) (rubi-reduce-inert-trig 'cos (- m 1/2) u))    ; 6530-6537
               ((equal? func 'cos) (list '- (rubi-reduce-inert-trig 'sin (- m 1/2) u)))
               ((equal? func 'tan) (list '- (rubi-reduce-inert-trig 'cot (- m 1/2) u)))
               ((equal? func 'cot) (list '- (rubi-reduce-inert-trig 'tan (- m 1/2) u)))
               ((equal? func 'sec) (list '- (rubi-reduce-inert-trig 'csc (- m 1/2) u)))
               (else (rubi-reduce-inert-trig 'sec (- m 1/2) u))))
        (else (list func (rubi-inert-phase m u)))))                              ; 6538
; DeactivateTrigAux[u,x] — IUF.m:6198-6219: у каждой тригонометрической функции линейного аргумента фаза
; сводится; остальное — рекурсия. Гиперболические клаузы (6210-6218) не перенесены: в порте они уходят в
; правила глав 4.1/4.3 как есть, а I*u[[1]] требует Simplify с комплексными — см. отчёт.
(define (rubi-deactivate-trig-aux u x)
  (cond ((not (pair? u)) u)
        ((and (null? (cddr u)) (member? (car u) (rubi-trig-heads)) (rubi-linearq (cadr u) x))
         (let ((split (rubi-inert-phase-split (cadr u) x)))
           (if split
               (rubi-reduce-inert-trig (car u) (car split) (cdr split))
               u)))
        (else (cons (car u) (map (lambda (a) (rubi-deactivate-trig-aux a x)) (cdr u))))))
; аргумент v = m*Pi + u с рациональным m -> (m . u); иначе #f (тогда ReduceInertTrig[func,u], IUF.m:6504)
(define (rubi-inert-phase-split v x)
  (if (and (pair? v) (equal? (car v) '+))
      (let loop ((ts (cdr v)) (m 0) (rest '()))
        (cond ((null? ts) (if (equal? m 0) #f (cons m (rubi-inert-sum-of (reverse rest)))))
              ((equal? (car ts) 'pi) (loop (cdr ts) (+ m 1) rest))
              ((and (pair? (car ts)) (equal? (car (car ts)) '*)
                    (member? 'pi (cdr (car ts))) (number? (cadr (car ts))))
               (loop (cdr ts) (+ m (cadr (car ts))) rest))
              (else (loop (cdr ts) m (cons (car ts) rest)))))
      #f))
(define (rubi-inert-sum-of ts)
  (cond ((null? ts) 0) ((null? (cdr ts)) (car ts)) (else (cons '+ ts))))
; UnifyInertTrigFunction[u,x] — IUF.m:6549-7362. Перенесено ядро: вынесение x-свободного множителя
; (6549-6551), cos[v] -> sin[v+Pi/2] (6588-6590), cot[v]^n -> tan[v]^(-n) и csc[v]^n -> sec[v]^(-n)
; (InertReciprocalQ, 6170), рекурсия по остальным узлам, по умолчанию u (7294).
; НЕ перенесены ~90 клауз для конкретных произведений двух тригонометрических множителей (6566-7361):
; они нужны, когда в одном произведении стоят разные головы одного аргумента (cos*csc и т.п.).
(define (rubi-unify-inert-trig-function u x)
  (cond ((not (pair? u)) u)
        ((and (equal? (car u) '*) (pair? (cdr u)) (not (contains-sym? (cadr u) x)))
         (list '* (cadr u) (rubi-unify-inert-trig-function (rubi-inert-mul-of (cddr u)) x)))
        ((and (equal? (car u) '^) (= (length (cdr u)) 2) (pair? (cadr u))
              (null? (cddr (cadr u))) (member? (car (cadr u)) (rubi-trig-heads))
              (rubi-linearq (cadr (cadr u)) x))
         (rubi-unify-trig-power (car (cadr u)) (cadr (cadr u)) (caddr u)))
        ((and (member? (car u) (rubi-trig-heads)) (null? (cddr u)) (rubi-linearq (cadr u) x))
         (rubi-unify-trig-power (car u) (cadr u) 1))
        (else (cons (car u) (map (lambda (a) (rubi-unify-inert-trig-function a x)) (cdr u))))))
(define (rubi-inert-mul-of ts)
  (cond ((null? ts) 1) ((null? (cdr ts)) (car ts)) (else (cons '* ts))))
(define (rubi-inert-neg n) (if (number? n) (- 0 n) (list '- n)))
(define (rubi-unify-trig-power f v n)
  (cond ((and (equal? f 'cos) (equal? n 1)) (list 'sin (list '+ v (list '/ 'pi 2))))
        ((equal? f 'cos) (list '^ (list 'sin (list '+ v (list '/ 'pi 2))) n))
        ((equal? f 'cot) (list '^ (list 'tan v) (rubi-inert-neg n)))
        ((equal? f 'csc) (list '^ (list 'sec v) (rubi-inert-neg n)))
        ((equal? n 1) (list f v))
        (else (list '^ (list f v) n))))

; rubi-deactivate-trig в правиле 4.1.0.1 #1 означает «тот же интеграл в инертной форме»; в порте головы уже
; инертные, поэтому для правил это тождество: фазовая унификация (rubi-deactivate-trig-aux +
; rubi-unify-inert-trig-function) включается только в точке нормализации и только при *rubi-inert-mask*.
(define (rubi-deactivate-trig u x) u)
; TrigSimplify[u] — IUF.m:2708-2709: тригонометрическое упрощение снизу вверх; рекурсия — IUF.m:2712-2717
; (атом и If не трогаем). TrigSimplifyAux — IUF.m:2719-2936; здесь реализованы клаузы базовых тождеств:
;   2740 a cos²+a sin²+v -> a+v; 2742 a sec²−a tan²+v -> a+v; 2744 a csc²−a cot²+v -> a+v;
;   2756 u+v sin²+w (u=−v) -> u cos²+w; 2759 (cos²) -> u sin²+w; 2762 u+v tan²+w (u=v) -> u sec²+w;
;   2765 (cot²) -> u csc²+w; 2768 u+v sec²+w (u=−v) -> v tan²+w; 2771 (csc²) -> v cot²+w.
; Не реализованы (см. REPORT-RUBI-C0B): 2723-2725 (базис a z^m+b z^n), 2751, 2775-2935.
; Сравнение коэффициентов — структурное, как === в исходнике (u=−v — это (* -1 u) после simplify).
(define (rubi-trig-sq-of t)
  (let ((b (and (pair? t) (equal? (car t) '^) (= (length (cdr t)) 2)
                (equal? (caddr t) 2) (cadr t))))
    (and (pair? b) (member? (car b) '(sin cos tan cot sec csc)) (= (length (cdr b)) 1) b)))
; слагаемое c*f(z)^2 -> (c f(z)) (два элемента), иначе #f
(define (rubi-trig-sq-term t)
  (let ((sq (rubi-trig-sq-of t)))
    (cond (sq (list 1 sq))
          ((and (pair? t) (equal? (car t) '*))
           (let loop ((fs (cdr t)) (coef '()) (hit #f))
             (cond ((null? fs)
                    (and hit (list (rubi-product-of (reverse coef)) hit)))
                   ((rubi-trig-sq-of (car fs))
                    (and (not hit) (loop (cdr fs) coef (rubi-trig-sq-of (car fs)))))
                   (else (loop (cdr fs) (cons (car fs) coef) hit)))))
          (else #f))))
(define (rubi-sum-of ts)
  (cond ((null? ts) 0) ((null? (cdr ts)) (car ts)) (else (cons '+ ts))))
(define (rubi-neg-struct? a b) (equal? (simplify (list '* -1 a)) b))
; замена слагаемых i и j: i выбросить, j заменить на new
(define (rubi-list-replace2 ts i j new)
  (let loop ((xs ts) (k 0) (acc '()))
    (cond ((null? xs) (rubi-sum-of (reverse acc)))
          ((equal? k i) (loop (cdr xs) (+ k 1) acc))
          ((equal? k j) (loop (cdr xs) (+ k 1) (cons new acc)))
          (else (loop (cdr xs) (+ k 1) (cons (car xs) acc))))))
; 2740/2742/2744: a*f(z)^2 + a'*g(z)^2 + v -> a + v для пар (cos,sin), (sec,tan), (csc,cot)
(define (rubi-trig-pair-clause ts)
  (let loop ((i 0))
    (and (< i (length ts))
         (let ((si (rubi-trig-sq-term (nth ts i))))
           (or (and si
                    (let inner ((j 0))
                      (and (< j (length ts))
                           (or (and (not (equal? i j))
                                    (let ((sj (rubi-trig-sq-term (nth ts j))))
                                      (and sj (rubi-trig-pair-rewrite ts i j si sj))))
                               (inner (+ j 1))))))
               (loop (+ i 1)))))))
(define (rubi-trig-pair-rewrite ts i j si sj)
  (let ((f (car (cadr si))) (g (car (cadr sj))) (a (car si)) (b (car sj))
        (z (cadr (cadr si))))
    (and (equal? z (cadr (cadr sj)))
         (cond ((and (or (and (equal? f 'cos) (equal? g 'sin))
                         (and (equal? f 'sin) (equal? g 'cos)))
                     (equal? a b))                                                  ; 2740
                (rubi-list-replace2 ts i j a))
               ((and (or (and (equal? f 'sec) (equal? g 'tan))
                         (and (equal? f 'tan) (equal? g 'sec)))
                     (rubi-neg-struct? b a))                                        ; 2742
                (rubi-list-replace2 ts i j a))
               ((and (or (and (equal? f 'csc) (equal? g 'cot))
                         (and (equal? f 'cot) (equal? g 'csc)))
                     (rubi-neg-struct? b a))                                        ; 2744
                (rubi-list-replace2 ts i j a))
               (else #f)))))
; 2756-2771: постоянное слагаемое i и v*f(z)^2 в j -> слагаемое (u или v)*g(z)^2, i выбрасываем
(define (rubi-trig-one-sq-clause ts)
  (let loop ((i 0))
    (and (< i (length ts))
         (let ((u (nth ts i)))
           (or (let inner ((j 0))
                 (and (< j (length ts))
                      (or (and (not (equal? i j))
                               (let ((sj (rubi-trig-sq-term (nth ts j))))
                                 (and sj (rubi-trig-one-sq-rewrite ts i j u sj))))
                          (inner (+ j 1)))))
               (loop (+ i 1)))))))
(define (rubi-trig-one-sq-rewrite ts i j u sj)
  (let* ((v (car sj)) (f (car (cadr sj))) (z (cadr (cadr sj)))
         (pair (cond ((equal? f 'sin) (and (rubi-neg-struct? u v) (list u 'cos)))   ; 2756
                     ((equal? f 'cos) (and (rubi-neg-struct? u v) (list u 'sin)))   ; 2759
                     ((equal? f 'tan) (and (equal? u v) (list u 'sec)))             ; 2762
                     ((equal? f 'cot) (and (equal? u v) (list u 'csc)))             ; 2765
                     ((equal? f 'sec) (and (rubi-neg-struct? u v) (list v 'tan)))   ; 2768
                     ((equal? f 'csc) (and (rubi-neg-struct? u v) (list v 'cot)))   ; 2771
                     (else #f))))
    (and pair
         (rubi-list-replace2 ts i j (rubi-trig-times (car pair) (list '^ (list (cadr pair) z) 2))))))
; TrigSimplifyAux[u] — IUF.m:2719-2936: сначала тождества с двумя квадратами, затем с одним; иначе u как есть.
; Арифметику здесь не трогаем: TrigSimplify по исходнику применяет только тригонометрические тождества,
; а simplify переупорядочивает произведение и переписывает tan² в sin²/cos², тогда как TrigSimplifyQ (2703)
; сравнивает результат с исходным u — из-за этого правило 4.7.5 #66 («u упрощается») срабатывало на любом
; нетригонометрическом входе (регрессия C0b: ∫x·e^(atanh(a·x)) переставал браться).
; Свёртка чисел в + и * — то, что в Mathematica делает автоматическое вычисление (Plus/Times): результат
; клаузы строится заново, поэтому (+ 1 2) и (* 3 1) надо свернуть самим. Порядок нетригонометрических
; множителей и слагаемых сохраняется: переупорядочивать нельзя (см. комментарий выше про TrigSimplifyQ).
(define (rubi-trig-fold-sum ts)
  (let loop ((s ts) (n 0) (num? #f) (out '()))
    (cond ((null? s)
           (if (null? out)
               n
               (let ((rest (reverse out)))
                 (cons '+ (if (and num? (not (equal? n 0))) (cons n rest) rest)))))
          ((number? (car s)) (loop (cdr s) (+ n (car s)) #t out))
          (else (loop (cdr s) n num? (cons (car s) out))))))
(define (rubi-trig-fold-prod fs)
  (let loop ((s fs) (n 1) (num? #f) (out '()))
    (cond ((null? s)
           (cond ((equal? n 0) 0)
                 ((null? out) n)
                 (else (let ((rest (reverse out)))
                         (cons '* (if (and num? (not (equal? n 1))) (cons n rest) rest))))))
          ((number? (car s)) (loop (cdr s) (* n (car s)) #t out))
          (else (loop (cdr s) n num? (cons (car s) out))))))
(define (rubi-trig-times c e) (if (and (number? c) (equal? c 1)) e (list '* c e)))
(define (rubi-trig-fold u)
  (cond ((not (pair? u)) u)
        ((equal? (car u) '+) (rubi-trig-fold-sum (map rubi-trig-fold (cdr u))))
        ((equal? (car u) '*) (rubi-trig-fold-prod (map rubi-trig-fold (cdr u))))
        (else (cons (car u) (map rubi-trig-fold (cdr u))))))
(define (rubi-trig-simplify-aux u)
  (rubi-trig-fold
   (if (and (pair? u) (equal? (car u) '+))
       (or (rubi-trig-pair-clause (cdr u)) (rubi-trig-one-sq-clause (cdr u)) u)
       u)))
(define (rubi-trig-simplify-recur u)
  (if (or (not (pair? u)) (equal? (car u) 'if))
      u
      (rubi-trig-simplify-aux (map rubi-trig-simplify-recur u))))
(define (rubi-trig-simplify u) (rubi-activate-trig (rubi-trig-simplify-recur u)))
; TrigSimplifyQ[u] — IUF.m:2703-2704: TrigSimplify действительно меняет u
(define (rubi-trig-simplify-q u)
  (not (equal? (rubi-activate-trig u) (rubi-trig-simplify u))))

(define (rubi-expand-trig u x) u)
(define (rubi-expand-trig-to-exp u x) u)
(define (rubi-expand-trig-expand u x) u)
(define (rubi-function-expand u x) u)
(define (rubi-rational-function-expand u x) u)
(define (rubi-rational-function-q u x) (and (rubi-polynomialq (numer u) x) (rubi-polynomialq (denom u) x)))
(define (rubi-rational-function-exponents u x) '())
; PiecewiseLinearQ[u,x]: производная u по x не зависит от x (IntegrationUtilityFunctions.m,
; клауза PiecewiseLinearQ, строка 7433). Три случая по исходнику: линейность, Log[c*F^v]
; с F и c, свободными от x, и v линейным, и пара F[G[v]] из таблицы обратных функций.
(define (rubi-prod-free-part fs x)
  (if (null? fs)
      1
      (let ((f (car fs)))
        (if (contains-sym? f x)
            (rubi-prod-free-part (cdr fs) x)
            (let ((r (rubi-prod-free-part (cdr fs) x)))
              (cond ((equal? r 1) f) (else (list '* f r))))))))

(define (rubi-piecewise-linear-pair-q f g)
  (member? (list f g) '((atanh tanh) (atanh coth) (acot coth) (acot tanh)
                        (atan tan) (atan cot) (acot cot) (acot tan))))

(define (rubi-piecewise-linear1-q u x)
  (or (rubi-linear-match-q u x)
      (and (pair? u) (equal? (car u) 'log) (equal? (length u) 2)
           (let ((w (cadr u)))
             (cond
               ((and (pair? w) (equal? (car w) '^))
                (and (not (contains-sym? (cadr w) x))
                     (rubi-linear-match-q (caddr w) x)))
               ((and (pair? w) (equal? (car w) '*))
                (let ((xp (let loop ((fs (cdr w)) (acc '()))
                            (cond ((null? fs) (cond ((null? acc) #f)
                                                    ((null? (cdr acc)) (car acc))
                                                    (else (cons '* acc))))
                                  ((contains-sym? (car fs) x) (loop (cdr fs) (cons (car fs) acc)))
                                  (else (loop (cdr fs) acc))))))
                  (and xp (pair? xp) (equal? (car xp) '^)
                       (not (contains-sym? (cadr xp) x))
                       (not (contains-sym? (rubi-prod-free-part (cdr w) x) x))
                       (rubi-linear-match-q (caddr xp) x))))
               (else #f))))
      (and (pair? u) (pair? (cadr u)) (equal? (length u) 2) (equal? (length (cadr u)) 2)
           (rubi-piecewise-linear-pair-q (car u) (car (cadr u)))
           (rubi-linear-match-q (cadr (cadr u)) x))))

; Двух- и трёхаргументная формы: PiecewiseLinearQ[u,x] и PiecewiseLinearQ[u,v,x]
(define (rubi-piecewise-linear-q u &rest rest)
  (let ((x (cond ((equal? (length rest) 1) (car rest))
                 ((equal? (length rest) 2) (cadr rest))
                 (else #f))))
    (and x
         (rubi-piecewise-linear1-q u x)
         (if (equal? (length rest) 2) (rubi-piecewise-linear1-q (car rest) x) #t))))
(define (rubi-function-of-exponential-q u x) (rubi-stub 'rubi-function-of-exponential-q))
(define (rubi-function-of-exponential u x) (rubi-stub 'rubi-function-of-exponential))
(define (rubi-function-of-exponential-function u x) (rubi-stub 'rubi-function-of-exponential-function))
(define (rubi-function-of-linear u x) (rubi-stub 'rubi-function-of-linear))
(define (rubi-function-of-square-root-of-quadratic u x) (rubi-stub 'rubi-function-of-square-root-of-quadratic))
(define (rubi-inverse-function-q u) (rubi-stub 'rubi-inverse-function-q))
(define (rubi-inverse-function-of-linear u x) (rubi-stub 'rubi-inverse-function-of-linear))
; ---------- KnownTrigIntegrandQ[u,x] — IUF.m:7384-7391 ----------
; u — «известный» тригонометрический подынтеграл над головами heads:
;   u === 1 (7385);
;   (a_.+b_.*f[e_.+f_.*x])^m_. (7386);
;   (a_.+b_.*f[..])^m_.*(A_.+B_.*f[..]) (7387);
;   A_.+C_.*f[..]^2 (7388);  A_.+B_.*f[..]+C_.*f[..]^2 (7389);
;   (a_.+b_.*f[..])^m_.*(A_.+C_.*f[..]^2) (7390);
;   (a_.+b_.*f[..])^m_.*(A_.+B_.*f[..]+C_.*f[..]^2) (7391);
; где f — голова из heads, а все прочие буквы (a,b,A,B,C,e,f,m) свободны от x.
; Как считаем: находим в u единственное тригонометрическое ядро k=(f арг) с линейным (или свободным
; от x) аргументом, подставляем k -> rubi-zz и смотрим на форму результата: клаузы 7388/7389 — это
; многочлен по zz степени ≤ 2 со свободными от x коэффициентами, 7386 — (линейный по zz)^m, а
; 7387/7390/7391 — произведение (линейного по zz)^m на такой многочлен (7387 — степень ≤ 1,
; частный случай). Допущение порта: свободный от x множитель считается многочленом степени 0
; (в исходнике клауза требует плюс A_+...), т.е. 3*(1+sin x)^2 у нас тоже «известный»; ответ
; всё равно проверяется сертификатом, поэтому расширение безопасно и снимает гонку с simplify.
;
; ядро: первый сверху вниз узел (f арг), f из heads, арг = e+f*x (e, f свободны от x)
(define (rubi-trig-kernel-in u heads x)
  (cond ((not (pair? u)) #f)
        ((and (member? (car u) heads)
              (null? (cddr u))
              (or (rubi-freeq (cadr u) x) (rubi-linearq (cadr u) x)))
         u)
        (else (let loop ((fs (cdr u)))
                (cond ((null? fs) #f)
                      (else (or (rubi-trig-kernel-in (car fs) heads x)
                                (loop (cdr fs)))))))))
; слагаемое b*zz (b свободно от x) или само zz
(define (rubi-zz-linear-term-q t zz x)
  (cond ((equal? t zz) #t)
        ((and (pair? t) (equal? (car t) '*))
         (cond ((and (= (length (cdr t)) 2) (equal? (cadr t) zz)) (rubi-freeq (caddr t) x))
               ((and (= (length (cdr t)) 2) (equal? (caddr t) zz)) (rubi-freeq (cadr t) x))
               (else #f)))
        (else #f)))
; v = a+b*zz, оба слагаемых свободны от x (база клаузы 7386)
(define (rubi-zz-lin-pair-q v zz x)
  (and (pair? v) (equal? (car v) '+) (= (length (cdr v)) 2)
       (let ((t1 (cadr v)) (t2 (caddr v)))
         (or (and (rubi-freeq t1 x) (rubi-zz-linear-term-q t2 zz x))
             (and (rubi-freeq t2 x) (rubi-zz-linear-term-q t1 zz x))))))
; v = (a+b*zz)^m, m свободно от x (клауза 7386)
(define (rubi-zz-pow-linear-q v zz x)
  (and (pair? v) (equal? (car v) '^) (= (length (cdr v)) 2)
       (rubi-freeq (caddr v) x)
       (rubi-zz-lin-pair-q (cadr v) zz x)))
; многочлен по zz степени 0..d со свободными от x коэффициентами (клаузы 7388/7389)
(define (rubi-zz-poly-q v zz x d)
  (and (rubi-polynomialq v zz)
       (let ((deg (rubi-safe-degree v zz)))
         (and (>= deg 0) (<= deg d)
              (let loop ((i 0))
                (cond ((> i deg) #t)
                      ; ошибка coeff (не многочлен) — считаем коэффициент зависящим от x, т.е. отказ
                      ((rubi-freeq (try (coeff v zz i) (lambda (err) x)) x) (loop (+ i 1)))
                      (else #f)))))))
; множители произведения; деление — умножение на отрицательную степень (Times/Power в Mathematica):
; 1/(a+b sec x)^2 — это (a+b sec x)^(-2), а не ((a+b sec x)^2)^(-1)
(define (rubi-negate-exponent f)
  (if (and (pair? f) (equal? (car f) '^) (= (length (cdr f)) 2))
      (let ((e (caddr f)))
        (list '^ (cadr f) (if (number? e) (- 0 e) (list '- e))))
      (list '^ f -1)))
(define (rubi-product-factors v)
  (cond ((and (pair? v) (equal? (car v) '*)) (cdr v))
        ((and (pair? v) (equal? (car v) '/) (= (length (cdr v)) 2))
         (append (rubi-product-factors (cadr v))
                 (map rubi-negate-exponent (rubi-product-factors (caddr v)))))
        (else (list v))))
(define (rubi-product-of xs)
  (cond ((null? xs) 1) ((null? (cdr xs)) (car xs)) (else (cons '* xs))))
(define (rubi-product-without fs i)
  (let loop ((xs fs) (k 0) (acc '()))
    (cond ((null? xs) (rubi-product-of (reverse acc)))
          ((equal? k i) (loop (cdr xs) (+ k 1) acc))
          (else (loop (cdr xs) (+ k 1) (cons (car xs) acc))))))
; v после подстановки ядра: клаузы 7386-7391
(define (rubi-known-trig-shape-q v zz x)
  (or (rubi-zz-lin-pair-q v zz x)      ; 7386 при m = 1
      (rubi-zz-pow-linear-q v zz x)    ; 7386
      (rubi-zz-poly-q v zz x 2)        ; 7388/7389
      (let ((fs (rubi-product-factors v)))
        (and (pair? (cdr fs))
             (let loop ((i 0))
               (and (< i (length fs))
                    (or (and (or (rubi-zz-pow-linear-q (nth fs i) zz x)
                                 (rubi-zz-lin-pair-q (nth fs i) zz x))
                             (let ((rest (rubi-product-without fs i)))
                               (or (rubi-zz-lin-pair-q rest zz x)     ; 7387
                                   (rubi-zz-poly-q rest zz x 2))))    ; 7390/7391
                        (loop (+ i 1)))))))))
; структурная замена подвыражения: subst из PolyBuiltins работает по многочленам и тригонометрический
; узел не заменяет, а simplify после подстановки переписывает tan² в sin²/cos² — здесь ни того, ни другого
(define (rubi-subst-tree u old new)
  (cond ((equal? u old) new)
        ((pair? u) (cons (rubi-subst-tree (car u) old new)
                         (rubi-subst-tree (cdr u) old new)))
        (else u)))
(define (rubi-known-trig-integrand-q heads u x)
  (or (equal? u 1)
      (let ((k (rubi-trig-kernel-in u heads x)))
        (and k (rubi-known-trig-shape-q (rubi-subst-tree u k 'rubi-zz) 'rubi-zz x)))))
; четыре обёртки — IUF.m:7368/7372/7376/7380
(define (rubi-known-sine-integrand-q u x) (rubi-known-trig-integrand-q '(sin cos) u x))
(define (rubi-known-tangent-integrand-q u x) (rubi-known-trig-integrand-q '(tan) u x))
(define (rubi-known-cotangent-integrand-q u x) (rubi-known-trig-integrand-q '(cot) u x))
(define (rubi-known-secant-integrand-q u x) (rubi-known-trig-integrand-q '(sec csc) u x))
(define (rubi-euler-integrand-q a &rest rest) (rubi-stub 'rubi-euler-integrand-q))
(define (rubi-calculus-free-q u x) #t)
(define (rubi-integral-free-q u x) (not (contains-sym? u 'integrate)))
(define (rubi-polynomial-in-q u x) (rubi-polynomialq u x))
(define (rubi-polynomial-in-subst u x) u)
; Слагаемое c*x^k (c не содержит x, k — число) → (k . c); иначе #f.
(define (rubi-x-monomial-term t x)
  (cond ((number? t) (cons 0 t))
        ((equal? t x) (cons 1 1))
        ((and (pair? t) (equal? (car t) '^) (equal? (cadr t) x) (number? (caddr t)))
         (cons (caddr t) 1))
        ; свободный от x множитель-символ или выражение — нулевая степень
        ((not (contains-sym? t x)) (cons 0 t))
        ((and (pair? t) (equal? (car t) '*))
         (let loop ((fs (cdr t)) (k 0) (rest '()))
           (cond ((null? fs)
                  (cons k (cond ((null? rest) 1)
                                ((null? (cdr rest)) (car rest))
                                (else (cons '* rest)))))
                 ((equal? (car fs) x) (loop (cdr fs) (+ k 1) rest))
                 ((and (pair? (car fs)) (equal? (car (car fs)) '^)
                       (equal? (cadr (car fs)) x) (number? (caddr (car fs))))
                  (loop (cdr fs) (+ k (caddr (car fs))) rest))
                 ((contains-sym? (car fs) x) #f)
                 (else (loop (cdr fs) k (cons (car fs) rest))))))
        (else #f)))

; Сумма по x → список (k . c) по возрастанию степени; #f, если хоть один член не моном
(define (rubi-x-monomial-sum u x)
  (if (and (pair? u) (equal? (car u) '+))
      (let loop ((ts (cdr u)) (acc '()))
        (cond ((null? ts)
               (sort acc (lambda (a b) (< (car a) (car b)))))
              (else (let ((p (rubi-x-monomial-term (car ts) x)))
                      (if p (loop (cdr ts) (cons p acc)) #f)))))
      #f))

; GeneralizedBinomialQ[u,x]: u = a*x^q + b*x^n, все коэффициенты и n-q ненулевые, n>q
; (IntegrationUtilityFunctions.m, клауза GeneralizedBinomialQ, строка 579)
(define (rubi-generalized-binomial-q u x)
  (let ((ts (rubi-x-monomial-sum u x)))
    (and ts
         (equal? (length ts) 2)
         (let* ((q (car (car ts))) (a (cdr (car ts)))
                (n (car (cadr ts))) (b (cdr (cadr ts))))
           (and (not (rubi-eqq a 0)) (not (rubi-eqq b 0))
                (rubi-posq (- n q)))))))

; GeneralizedTrinomialQ[u,x]: u = a*x^q + b*x^n + c*x^(2n-q), коэффициенты ненулевые
; (IntegrationUtilityFunctions.m, клауза GeneralizedTrinomialParts, строка 1058)
(define (rubi-generalized-trinomial-q u x)
  (let ((ts (rubi-x-monomial-sum u x)))
    (and ts
         (equal? (length ts) 3)
         (let* ((q (car (car ts))) (a (cdr (car ts)))
                (n (car (cadr ts))) (b (cdr (cadr ts)))
                (r (car (caddr ts))) (c (cdr (caddr ts))))
           (and (not (rubi-eqq a 0)) (not (rubi-eqq b 0)) (not (rubi-eqq c 0))
                (rubi-eqq r (- (* 2 n) q)))))))
(define (rubi-generalized-binomial-match-q u x) (rubi-generalized-binomial-q u x))
(define (rubi-generalized-trinomial-match-q u x) (rubi-generalized-trinomial-q u x))
(define (rubi-generalized-trinomial-degree a &rest rest) -1)
(define (rubi-power-variable-expn a &rest rest) (rubi-stub 'rubi-power-variable-expn))
(define (rubi-exponent e x) (rubi-safe-degree e x))
(define (rubi-int-sum u x) u)
; SubstPower[u, x, k]: подстановка x -> x^k в алгебраической функции u; (x^a)^r сводится к x^(a*r) (x > 0, как в Rubi)
(define (rubi-pow-of-pow e x)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) (quote ^)) (= (length e) 3) (pair? (cadr e)) (equal? (car (cadr e)) (quote ^))
              (equal? (cadr (cadr e)) x) (number? (caddr (cadr e))) (number? (caddr e)))
         (list (quote ^) x (* (caddr (cadr e)) (caddr e))))
        (else (cons (car e) (map (lambda (a) (rubi-pow-of-pow a x)) (cdr e))))))
(define (rubi-subst-power u x k)
  (simplify (rubi-pow-of-pow (subst (list (list x (list (quote ^) x k))) u) x)))
(define (rubi-split-product-at u x) (list u 1))

; Обёртки голов Rubi: инертная тригонометрия и служебные функции
(define (rubi-sin u) (list 'sin u))
(define (rubi-cos u) (list 'cos u))
(define (rubi-tan u) (list 'tan u))
(define (rubi-cot u) (list 'cot u))
(define (rubi-sec u) (list 'sec u))
(define (rubi-csc u) (list 'csc u))
(define (rubi-f u) (list 'f u))
(define (rubi-g u) (list 'g u))
(define (rubi-h u) (list 'h u))
(define (rubi-product-log u) (list 'lambert_w u))
(define (rubi-integral u x) (list 'integrate u x))
(define (rubi-erfi u) (list 'erfi u))
(define (rubi-erfc u) (list 'erfc u))
(define (rubi-fresnel-s u) (list 'fresnel_s u))
(define (rubi-fresnel-c u) (list 'fresnel_c u))
(define (rubi-sin-integral u) (list 'sin_integral u))
(define (rubi-cos-integral u) (list 'cos_integral u))
(define (rubi-sinh-integral u) (list 'sinh_integral u))
(define (rubi-cosh-integral u) (list 'cosh_integral u))
(define (rubi-exp-integral-e u) (list 'exp_integral_e u))
(define (rubi-exp-integral-ei u) (list 'exp_integral_ei u))
(define (rubi-log-integral u) (list 'log_integral u))
(define (rubi-log-gamma u) (list 'log_gamma u))
(define (rubi-poly-gamma a b c) (list 'poly_gamma a b c))
(define (rubi-hypergeometric-pfq a b c) (list 'hypergeometric_pfq a b c))
(define rubi-undefined 'undefined)

; --- ExpandIntegrand по первоисточнику (Rubi/IntegrationUtilityFunctions.m) ---
; Реализовано подмножество для произведений степеней линейных: правила
; ExpandIntegrand[u*(a+b*x)^m] (стр. 3558) и ExpandLinearProduct (стр. 4023).
; Всё остальное возвращается без изменений (как fallback первоисточника), чтобы
; правило Rubi не срабатывало на форме, которую мы не умеем раскрыть.

; (a+b*x) -> (a b); #f, если форма другая или a,b зависят от x
(define (rubi-binom-parts base x)
  (let ((m (ac-match (quote (+ ?a (* ?b x))) base :identities #t)))
    (and m
         (let ((a (cadr (assoc (quote ?a) m)))
               (b (cadr (assoc (quote ?b) m))))
           (and (not (contains-sym? a x)) (not (contains-sym? b x))
                (not (equal? b 0))
                (list a b))))))

(define (rubi-sum-length u)
  (if (rubi-sumq u) (length (cdr u)) 0))

; ExpandIntegrand[u*(a+b*x)^m, x] — выбор между разложением по (a+b*x) и Expand
(define (rubi-ei-binom u base m x)
  (let ((ab (rubi-binom-parts base x)))
    (if (not ab)
        (list '* u (list '^ base m))
        (let* ((a (car ab)) (b (cadr ab))
               (occ (list (quote ^) base m))
               (sum1 (rubi-expand-linear-product occ u a b x)))
          (if (or (not (integer? m)) (and (> m 2) (rubi-linear-match-q u x)))
              sum1
              (let ((sum2 (rubi-expand-expression (list (quote *) u occ) x)))
                (cond ((not (rubi-sumq sum2)) sum1)
                      ((> m 0)
                       (if (or (<= (rubi-sum-length sum2) (+ (rubi-safe-degree u x) 2))
                               (<= (rubi-leaf-count sum2) (* 2/3 (rubi-leaf-count sum1))))
                           sum2 sum1))
                      (else (if (<= (rubi-leaf-count sum2) (+ (rubi-leaf-count sum1) 2))
                                sum2 sum1)))))))))

; обход произведения: множитель-степень линейного + полиномиальный остаток u
(define (rubi-remove-nth l i)
  (let loop ((l l) (k 0) (acc '()))
    (cond ((null? l) (reverse acc))
          ((equal? k i) (loop (cdr l) (+ k 1) acc))
          (else (loop (cdr l) (+ k 1) (cons (car l) acc))))))

; PolynomialQuotientRemainder[u,v,x] -> (частное . остаток); #f, если деление не вышло
(define (rubi-poly-qr u v x)
  (and (rubi-poly2? u v)
       (try (cons (poly-quotient u v x) (poly-remainder u v x)) (lambda (err) #f))))

; множитель (^ v n) с целым n < 0 и полиномом v: (индекс v n) или #f
(define (rubi-ei-neg-power fs x)
  (let loop ((l fs) (i 0))
    (cond ((null? l) #f)
          ((and (pair? (car l)) (equal? (car (car l)) '^) (equal? (length (car l)) 3)
                (integer? (car (cdr (cdr (car l))))) (< (car (cdr (cdr (car l)))) 0)
                (rubi-polynomialq (car (cdr (car l))) x))
           (list i (car (cdr (car l))) (car (cdr (cdr (car l))))))
          (else (loop (cdr l) (+ i 1))))))

; второй бином (^ cbase n): (индекс cbase n) или #f
(define (rubi-ei-binom-at fs x skip)
  (let loop ((l fs) (i 0))
    (cond ((null? l) #f)
          ((equal? i skip) (loop (cdr l) (+ i 1)))
          ((and (pair? (car l)) (equal? (car (car l)) '^) (equal? (length (car l)) 3)
                (rubi-binom-parts (car (cdr (car l))) x))
           (list i (car (cdr (car l))) (car (cdr (cdr (car l))))))
          (else (loop (cdr l) (+ i 1))))))

(define (rubi-ei-prod-of fs)
  (cond ((null? fs) 1)
        ((null? (cdr fs)) (car fs))
        (else (cons '* fs))))

; ExpandIntegrand[u,v,x]: u * ExpandIntegrand[v,x] с распределением по несвободным членам
(define (rubi-ei-distribute u v x)
  (let* ((vv (rubi-expand-integrand v x))
         (ts (if (rubi-sumq vv) (cdr vv) (list vv)))
         (free (filter (lambda (t) (not (contains-sym? t x))) ts))
         (non (filter (lambda (t) (contains-sym? t x)) ts))
         (fp (cond ((null? free) 0) ((null? (cdr free)) (car free)) (else (cons '+ free)))))
    (simplify (expand
               (cons '+ (cons (list '* u fp)
                              (map (lambda (t) (list '* u t)) non)))))))

; u * v^n * (a+bx)^m при нецелом m (первоисточник, правила 3577 и 3584)
(define (rubi-ei-neg-m u v n base m x)
  (let* ((ab (rubi-binom-parts base x))
         (a (car ab)) (b (cadr ab))
         (occ (list '^ base m))
         (ip (if (number? m) (floor m) 0))
         (fp (if (number? m) (simplify (list '- m (floor m))) 0)))
    (cond
      ; 3577: m < -1 — делим на v^(-n)*(a+bx)^(-IntegerPart[m])
      ((and (number? m) (< m -1))
       (let* ((den (list '* (list '^ v (- n)) (list '^ base (- ip))))
              (qr (rubi-poly-qr u den x)))
         (and qr (not (equal? (car qr) 0))
              (simplify
               (list '+
                     (rubi-expand-integrand (list '* (car qr) (list '^ base fp)) x)
                     (if (equal? (cdr qr) 0) 0
                         (rubi-expand-integrand (list '* (cdr qr) (list '^ v n) occ) x)))))))
      ; 3584: Exponent[u] >= -n*Exponent[v]
      ((and (> (rubi-safe-degree v x) 0)
            (>= (rubi-safe-degree u x) (* (- n) (rubi-safe-degree v x))))
       (let* ((den (list '^ v (- n)))
              (qr (rubi-poly-qr u den x)))
         (and qr (not (equal? (car qr) 0))
              (simplify
               (list '+
                     (rubi-expand-integrand (list '* (car qr) occ) x)
                     (if (equal? (cdr qr) 0) 0
                         (rubi-expand-integrand (list '* (cdr qr) (list '^ v n) occ) x)))))))
      (else #f))))

(define (rubi-ei-prod u x)
  (let ((fs (cdr u)))
    (let loop ((i 0))
      (if (>= i (length fs))
          u
          (let ((f (nth fs i)))
            (if (and (pair? f) (equal? (car f) '^) (equal? (length f) 3)
                     (rubi-binom-parts (cadr f) x))
                (let* ((rest (rubi-remove-nth fs i))
                       (m (caddr f))
                       (uu (rubi-ei-prod-of rest))
                       (np (rubi-ei-neg-power rest x))
                       (res
                        (cond
                          ; 3553: второй бином (c+dx)^n, m не целое, n-m целое > 0
                          ((and (not (integer? m))
                                (let ((sb (rubi-ei-binom-at rest x -1)))
                                  (and sb (integer? (- (caddr sb) m)) (> (- (caddr sb) m) 0))))
                           (let* ((sb (rubi-ei-binom-at rest x -1))
                                  (rest2 (rubi-remove-nth rest (car sb)))
                                  (uu2 (list '* (rubi-ei-prod-of rest2) (list '^ (cadr f) m))))
                             (rubi-ei-distribute uu2 (list '^ (cadr sb) (caddr sb)) x)))
                          ; 3577/3584: дробное или отрицательное m при u * v^n
                          ((and np (not (integer? m)))
                           (let* ((u2 (rubi-ei-prod-of (rubi-remove-nth rest (car np)))))
                             (rubi-ei-neg-m u2 (cadr np) (caddr np) (cadr f) m x)))
                          ; 3558: полиномиальный остаток
                          ((rubi-polynomialq uu x) (rubi-ei-binom uu (cadr f) m x))
                          (else #f))))
                  (if res res (loop (+ i 1))))
                (loop (+ i 1))))))))

; (a + b*x^n) с целым n < 0: (a b n) или #f
(define (rubi-neg-power-parts base x)
  (let ((m (ac-match '(+ ?a (* ?b (^ x ?n))) base)))
    (and m
         (let ((a (cadr (assoc '?a m)))
               (b (cadr (assoc '?b m)))
               (n (cadr (assoc '?n m))))
           (and (integer? n) (< n 0)
                (not (contains-sym? a x)) (not (contains-sym? b x))
                (list a b n))))))

; рациональные дроби: разложение на простейшие (свой Apart, символьные коэффициенты)
(define (rubi-ei-apart u x)
  (let ((d (try (denom u) (lambda (err) 1))))
    (if (or (equal? d 1) (not (contains-sym? d x)))
        #f
        (let ((a (try (rubi-apart u x) (lambda (err) u))))
          (and (rubi-sumq a) a)))))

; c*x^m, где c свободен от x
(define (rubi-monomial-x? e x)
  (let ((p (rubi-split-x-term (expand e) x)))
    (and p (integer? (car p)) (>= (car p) 0)
         (not (contains-sym? (cdr p) x)))))

; 3428: x^m*(a + b*x^(-n))^p —> x^(m+n*p)*(b + a*x^n)^p (n < 0 целое, p целое)
(define (rubi-ei-neg-base u x)
  (let ((fs (cdr u)))
    (let loop ((i 0))
      (if (>= i (length fs))
          #f
          (let ((f (nth fs i)))
            (if (and (pair? f) (equal? (car f) '^) (equal? (length f) 3)
                     (integer? (caddr f))
                     (pair? (cadr f)) (equal? (car (cadr f)) '+)
                     (rubi-neg-power-parts (cadr f) x))
                (let* ((abn (rubi-neg-power-parts (cadr f) x))
                       (a (car abn)) (b (cadr abn)) (n (caddr abn)) (p (caddr f))
                       (rr (rubi-ei-prod-of (rubi-remove-nth fs i)))
                       (m (rubi-safe-degree rr x)))
                  (if (and (>= m 0) (rubi-monomial-x? rr x))
                      (rubi-expand-integrand
                       (list '* (list '^ x (+ m (* n p)))
                             (list '^ (list '+ b (list '* a (list '^ x (- n)))) p))
                       x)
                      #f))
                (loop (+ i 1))))))))

; ExpandIntegrand — две формы, как в первоисточнике: ExpandIntegrand[u,x] раскладывает u по x,
; ExpandIntegrand[u,v,x] раскладывает произведение u*v «по v» (правила 1.1.1.5 #4 и другие зовут
; именно трёхаргументную). Трёхаргументная форма раскрывает произведение и отдаёт сумму, если она вышла.
(define (rubi-expand-integrand u &rest rest)
  (cond ((equal? (length rest) 1) (rubi-expand-integrand-2 u (car rest)))
        ((equal? (length rest) 2)
         ; RUBI.ELL1.4: IUF.m:3384-3385 ExpandIntegrand[u,v,x] = DistributeOverTerms[u, ExpandIntegrand[v,x], x]:
         ; раскладывается только v, u остаётся множителем каждого слагаемого. Раньше раскрывалось всё произведение u*v,
         ; и (a + c x^4)^p (d/(d^2 - e^2 x^4) - e x^2/(...))^1 (1.2.2.3 #98) оставалось произведением с множителем-суммой
         ; (PolyQ его не принимал: 1.1.3.7 #45, 1.1.1.6 #7).
         ; Когда ExpandIntegrand[v,x] не дала суммы, сохраняется прежний путь (раскрытие u*v, apart): наш
         ; ExpandIntegrand[v,x] охватывает не все ветви IUF.m, и без запасного пути терялись ответы 1.1.3.4 (716 и др.).
         ; Распределение по IUF.m включается, только если прежний путь не дал суммы: там, где раскрытие u*v уже
         ; давало сумму, разложение иное (апарт по u*v) и ответы 1.1.3.4 (716 и др.) держатся на нём.
         (let* ((v (car rest)) (x (cadr rest)) (old (rubi-expand-integrand-2 (list '* u v) x)))
           (if (rubi-sumq old)
               old
               (let ((w (rubi-expand-integrand-2 v x)))
                 (if (rubi-sumq w) (rubi-distribute-over-terms u w x) old)))))
        (else u)))

; DistributeOverTerms[u,v,x] (IUF.m:3388-3392): u*FreeTerms[v] + u*Nonfree-слагаемые. MergeMonomials не применяется
; (в Rubi склеивает u*слагаемое при одинаковых линейных основаниях).
(define (rubi-distribute-over-terms u v x)
  (if (rubi-sumq v)
      (let ((free (filter (lambda (t) (not (contains-sym? t x))) (cdr v)))
            (dep (filter (lambda (t) (contains-sym? t x)) (cdr v))))
        (cons '+ (append (if (null? free) '() (list (list '* u (if (null? (cdr free)) (car free) (cons '+ free)))))
                         (map (lambda (t) (list '* u t)) dep))))
      (list '* u v)))

(define (rubi-expand-integrand-2 u x)
  (cond ((not (contains-sym? u x)) u)
        ; 3423: (a + b*x^(-n))^p, p целое —> x^(-n*p)*(b + a*x^n)^p
        ((and (pair? u) (equal? (car u) '^) (integer? (caddr u))
              (pair? (cadr u)) (equal? (car (cadr u)) '+)
              (rubi-neg-power-parts (cadr u) x))
         (let* ((abn (rubi-neg-power-parts (cadr u) x))
                (a (car abn)) (b (cadr abn)) (n (caddr abn)) (p (caddr u)))
           (rubi-expand-integrand
            (list '* (list '^ x (* n p))
                  (list '^ (list '+ b (list '* a (list '^ x (- n)))) p))
            x)))
        ((and (pair? u) (equal? (car u) (quote *)))
         (or (rubi-ei-neg-base u x)
             (let ((p (rubi-ei-prod u x))) (if (equal? p u) #f p))
             (rubi-ei-apart u x)
             u))
        ((and (pair? u) (equal? (car u) (quote ^))
              (integer? (caddr u)) (> (caddr u) 0) (rubi-linear-match-q (cadr u) x))
         (expand u))
        (else
         ; последняя ветвь первоисточника: ExpandExpression, если получилась сумма
         (let ((a (rubi-ei-apart u x)))
           (if a a
               (let ((v (rubi-expand-expression u x)))
                 (if (rubi-sumq v) v u)))))))
; --- SmartApart (Rubi/IntegrationUtilityFunctions.m, стр. 3897) ---
; Встроенный apart не раскладывает дроби с символьными коэффициентами (a, b), поэтому
; разложение на простейшие сделано своим методом неопределённых коэффициентов:
; знаменатель раскладывается factor'ом на ЛИНЕЙНЫЕ по x множители, неизвестные находятся solve'ом.

(define (rubi-atom? u) (not (pair? u)))

(define (rubi-zip2 f a b)
  (if (or (null? a) (null? b))
      '()
      (cons (f (car a) (car b)) (rubi-zip2 f (cdr a) (cdr b)))))

; знаменатель -> список (множитель . кратность); #f, если есть нелинейный множитель
(define (rubi-den-factors den x)
  (let ((f (factor den)))
    (let loop ((fs (if (rubi-productq f) (cdr f) (list f))) (acc '()))
      (cond ((null? fs) (reverse acc))
            ((and (pair? (car fs)) (equal? (car (car fs)) '^))
             (let ((b (cadr (car fs))) (m (caddr (car fs))))
               (if (and (integer? m) (> m 0) (equal? (rubi-safe-degree b x) 1))
                   (loop (cdr fs) (cons (cons b m) acc))
                   #f)))
            ((equal? (rubi-safe-degree (car fs) x) 1)
             (loop (cdr fs) (cons (cons (car fs) 1) acc)))
            (else #f)))))

; список (множитель . кратность) -> базис (множитель степень): f, f^2, ... по каждому множителю
(define (rubi-apart-basis facs)
  (let loop ((fs facs) (acc '()))
    (if (null? fs)
        (reverse acc)
        (let ((f (car (car fs))) (m (cdr (car fs))))
          (let inner ((k 1) (a acc))
            (if (> k m) (loop (cdr fs) a)
                (inner (+ k 1) (cons (list f k) a))))))))

(define (rubi-nth-or-0 l i)
  (if (or (< i 0) (>= i (length l))) 0 (nth l i)))

; коэффициент при x^j многочлена e (0, если степень меньше j)
(define (rubi-coeff-at e x j) (rubi-nth-or-0 (rubi-coefficient-list e x) j))

; solve возвращает множество решений; берём первый набор уравнений
(define (rubi-solve-pairs sol)
  (let ((l (if (equal? (type-of sol) 'set) (set->list sol)
               (if (pair? sol) sol (list sol)))))
    (if (and (pair? l) (pair? (car l)) (equal? (car (car l)) '=))
        l
        (if (pair? l) (car l) l))))

; разложение рациональной функции на простейшие по линейным множителям
(define (rubi-apart u x)
  (let* ((num (expand (numer u)))
         (den (expand (denom u)))
         (facs (rubi-den-factors den x)))
    (if (not facs)
        u
        (let* ((basis (rubi-apart-basis facs))
               (n (length basis))
               (vars (let loop ((i 1) (acc '()))
                       (if (> i n) (reverse acc)
                           (loop (+ i 1)
                                 (cons (string->symbol (string-append "rubi-c" (to-string i))) acc)))))
               (q (try (poly-quotient num den x) (lambda (err) 0)))
               (r (try (poly-remainder num den x) (lambda (err) num)))
               (dens (map (lambda (bk)
                            (try (poly-quotient den (list '^ (car bk) (cadr bk)) x)
                                 (lambda (err) #f)))
                          basis)))
          (if (member? #f dens)
              u
              (let* ((rc (rubi-coefficient-list r x))
                     (eqs
                      (let loop ((j 0) (acc '()))
                        (if (>= j n)
                            (reverse acc)
                            (let ((lhs (cons '+ (rubi-zip2 (lambda (v d)
                                                             (simplify (list '* v (rubi-coeff-at d x j))))
                                                           vars dens))))
                              (loop (+ j 1)
                                    (cons (list '= lhs (rubi-nth-or-0 rc j)) acc))))))
                     (sol (try (solve eqs vars) (lambda (err) #f))))
                (if (or (not sol) (null? sol))
                    u
                    (let* ((pairs (rubi-solve-pairs sol))
                           (val (lambda (v)
                                  (let ((e (car (filter (lambda (eq) (equal? (cadr eq) v)) pairs))))
                                    (and e (caddr e))))))
                      (if (not (every? (lambda (v) (val v)) vars))
                          u
                          (let ((terms
                                 (rubi-zip2 (lambda (bk v)
                                              (simplify (list '/ (val v)
                                                              (list '^ (car bk) (cadr bk)))))
                                            basis vars)))
                            (simplify (cons '+ (cons q terms)))))))))))))

; SmartApart: ядра, не зависящие от x (не атомы, не целые степени/суммы/произведения),
; заменяются на свежие символы, чтобы Apart не «рационализировал» их; затем замена обратно.
(define (rubi-kernel-list u x)
  (cond ((rubi-atom? u) '())
        ((and (pair? u) (equal? (car u) '^) (integer? (caddr u)))
         (rubi-kernel-list (cadr u) x))
        ((or (rubi-sumq u) (rubi-productq u))
         (let loop ((fs (cdr u)) (acc '()))
           (if (null? fs) acc
               (loop (cdr fs) (rubi-kernel-list-merge (rubi-kernel-list (car fs) x) acc)))))
        ((not (contains-sym? u x)) (list u))
        (else '())))

(define (rubi-kernel-list-merge a b)
  (let loop ((a a) (acc b))
    (cond ((null? a) acc)
          ((member? (car a) acc) (loop (cdr a) acc))
          (else (loop (cdr a) (cons (car a) acc))))))

(define (rubi-kernel-subst u x alst)
  (cond ((rubi-atom? u)
         (let ((p (assoc u alst))) (if p (cadr p) u)))
        ((and (pair? u) (equal? (car u) '^) (integer? (caddr u)))
         (list '^ (rubi-kernel-subst (cadr u) x alst) (caddr u)))
        ((or (rubi-sumq u) (rubi-productq u))
         (cons (car u) (map (lambda (e) (rubi-kernel-subst e x alst)) (cdr u))))
        ((not (contains-sym? u x))
         (let ((p (assoc u alst))) (if p (cadr p) u)))
        (else u)))

(define (rubi-ungensym u x alst)
  (cond ((rubi-atom? u)
         (let ((p (assoc u alst))) (if p (cadr p) u)))
        ((and (pair? u) (equal? (car u) '^) (integer? (caddr u)))
         (let ((b (rubi-ungensym (cadr u) x alst)) (m (caddr u)))
           (if (and (< m 0) (equal? b 0)) #f (list '^ b m))))
        ((or (rubi-sumq u) (rubi-productq u))
         (let ((xs (map (lambda (e) (rubi-ungensym e x alst)) (cdr u))))
           (if (member? #f xs) #f (cons (car u) xs))))
        ((not (contains-sym? u x))
         (let ((p (assoc u alst))) (if p (cadr p) u)))
        (else u)))

(define (rubi-smart-apart u x)
  (let ((kernels (rubi-kernel-list u x)))
    (if (null? kernels)
        (rubi-apart u x)
        (let* ((alst (let loop ((ks kernels) (i 1) (acc '()))
                       (if (null? ks) (reverse acc)
                           (loop (cdr ks) (+ i 1)
                                 (cons (list (car ks)
                                             (string->symbol (string-append "rubi-g" (to-string i))))
                                       acc)))))
               (t (rubi-apart (rubi-kernel-subst u x alst) x))
               (r (rubi-ungensym t x alst)))
          (if r r u)))))
