; integrate/parts.lisp — интегрирование по частям (LIATE) и раскрытие скобок (часть бывшего lib\integrate.lisp, шаг 21h').
; Регистрирует стратегии int-parts, int-expand. Загружается после integrate/trig.lisp.
(module integrate)

; ---------- интегрирование по частям (LIATE) ----------
; ∫ u dv = u·v − ∫ v du; u выбирается по LIATE: логарифм (1), обратные тригонометрические (2), многочлены/степени x (3),
; тригонометрические (4), показательные (5); степени x с отрицательным/дробным показателем — ранг 6 (хуже показательных).
; Одиночный множитель ранга 1–2 (log x ^ k, atan(x²)): u = e, dv = dx. Повтор — через рекурсию каскада (глубина < int-max-depth).
; Циклический случай (exp·sin, exp·cos): после двух шагов e3 = c·e (c без x) ⇒ I = (P1 − P2)/(1 − c).

(define (int-rank f x)
  (cond ((x-free? f x) 0)
        ((not (op-expr? f)) 3)
        ((equal? (car f) 'log) 1)
        ((member? (car f) '(asin acos atan acot asec acsc asinh acosh atanh acoth)) 2)
        ((member? (car f) '(sin cos tan cot sec csc sinh cosh tanh coth sech csch)) 4)
        ((equal? (car f) 'exp) 5)
        ((equal? (car f) '^)
         (cond ((x-free? (cadr f) x) 5)
               ((not (x-free? (caddr f) x)) 7)
               ((polynomial? (cadr f) x) (if (and (integer? (caddr f)) (> (caddr f) 0)) 3 6))
               (else (int-rank (cadr f) x))))
        ((polynomial? f x) 3)
        (else 6)))

(define (int-min-rank-factor fs x)
  (foldl (lambda (best f) (if (< (int-rank f x) (int-rank best x)) f best)) (car fs) (cdr fs)))

; e → (u dv) или #f
(define (int-remove-first u l)
  (cond ((null? l) '())
        ((equal? (car l) u) (cdr l))
        (else (cons (car l) (int-remove-first u (cdr l))))))

(define (int-liate-split e x)
  (let* ((all (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))
         (fs (filter (lambda (f) (not (x-free? f x))) all)))   ; множители без x — только в dv
    (cond ((null? fs) #f)
          ((null? (cdr fs))
           (and (<= (int-rank (car fs) x) 2)
                (list (car fs) (simplify (cons '* (cons 1 (int-remove-first (car fs) all)))))))
          (else
           (let ((u (int-min-rank-factor fs x)))
             (and (<= (int-rank u x) 5)
                  (list u (simplify (cons '* (cons 1 (int-remove-first u all)))))))))))

; один шаг: (P e2): P = u·v, e2 = v·u'. Шаг S.4, порядок как в учебнике: шаг int-parts-choice («Выбор u и dv»; внутри —
; вложенный шаг нахождения v = ∫ dv), затем int-parts-formula: ∫ e dx = P − ∫ e2 dx
(define (int-dx-sym x) (string->symbol (string-append "d" (to-string (int-p x)))))
(define (int-dv-form dv x) (if (equal? dv 1) (int-dx-sym x) (list '* (int-p dv) (int-dx-sym x))))

; INT.GAPS.4: приведение алгебраического выражения с одним квадратным радикалом s = √R к виду A + B·s (A, B рациональны
; по x): s → символ, числитель и знаменатель по модулю s² = R, затем умножение на сопряжённое знаменателя.
; Тождество в ℚ(x)[s]/(s²−R) — значение не меняется; d(log(x+√(x²+c))) = (1 + x/s)/(x+s) → 1/√(x²+c).
(define (int-s-subst e R sym)
  (cond ((not (op-expr? e)) e)
        (else (let ((as (map (lambda (a) (int-s-subst a R sym)) (cdr e))))
                (cond ((and (equal? (car e) 'sqrt) (= (length as) 1) (equal? (expand (car (cdr e))) R)) sym)
                      ((and (equal? (car e) '^) (= (length e) 3) (number? (caddr e)) (equal? (denom (caddr e)) 2)
                            (equal? (expand (cadr e)) R))
                       (list '^ sym (* 2 (caddr e))))
                      (else (cons (car e) as)))))))

; многочлен p по s → (A B): p = A + B·s при s² = R
(define (int-s-reduce p s R)
  (let loop ((cs (coefficients p s)) (even 0) (odd 0) (k 0))
    (if (null? cs)
        (list (expand even) (expand odd))
        (let ((term (list '* (car cs) (list '^ R (quotient k 2)))))
          (if (= (remainder k 2) 0)
              (loop (cdr cs) (list '+ even term) odd (+ k 1))
              (loop (cdr cs) even (list '+ odd term) (+ k 1)))))))

(define (int-rad-normalize e x)
  (let ((rs (int-dedupe (int-rad-bases e))))
    (if (and (= (length rs) 1) (int-algebraic-in? e x) (polynomial? (car rs) x) (not (x-free? (car rs) x)))
        (let* ((R (car rs)) (sym 'int-rn-s)
               (g (together (int-s-subst e R sym))))
          (if (and (not (contains-sym? g 'sqrt)) (polynomial? (numer g) sym) (polynomial? (denom g) sym))
              (let* ((nr (int-s-reduce (numer g) sym R)) (dr (int-s-reduce (denom g) sym R))
                     (a (car nr)) (b (cadr nr)) (p (car dr)) (q (cadr dr))
                     (den (expand (list '- (list '^ p 2) (list '* (list '^ q 2) R)))))
                (if (equal? den 0)
                    e
                    (let ((A (expand (list '- (list '* a p) (list '* b q R))))
                          (B (expand (list '- (list '* b p) (list '* a q)))))
                      (simplify (list '+ (together (list '/ A den))
                                      (list '* (together (list '/ B den)) (list '^ R 1/2)))))))
              e))
        e)))

(define (int-parts-step e u dv x d)
  (let* ((du (int-rad-normalize (int-diff x u) x))
         (v (with-step ('int-parts-choice "Выбор u и dv" (int-form e x)
                         :comment (lambda (v) (string-append "по правилу LIATE; du = " (int-mp (simplify du)) " dx; v = ∫ dv = " (int-mp v)
                                                             " (вложенный шаг ниже)"))
                         :after (lambda (v) (list 'list (list '= 'u (int-p u)) (list '= 'dv (int-dv-form dv x)))))
              (int-go dv x (+ d 1)))))
    (and v (let ((st (list (simplify (list '* u v)) (simplify (list '* v du)))))
             (if (step-log-enabled?)
                 (record-step 'int-parts-formula "Формула интегрирования по частям"
                              (string-append "∫ u dv = u·v − ∫ v du; здесь u = " (int-mp u) ", v = " (int-mp v) ", du = "
                                             (int-mp (simplify du)) " dx")
                              (int-form e x)
                              (list '+ (int-p (car st)) (list '* -1 (int-form (cadr st) x)))))
             st))))

(define (int-cyclic? e x)
  (let ((fs (filter (lambda (f) (not (x-free? f x))) (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))))
    (and (> (length fs) 1)
         (every? (lambda (f) (member? (int-rank f x) '(4 5))) fs)
         (any? (lambda (f) (= (int-rank f x) 4)) fs)
         (any? (lambda (f) (= (int-rank f x) 5)) fs))))

(define (int-parts-cyclic e x d)
  (let ((s1 (int-liate-split e x)))
    (and s1
         (let ((st1 (int-parts-step e (car s1) (cadr s1) x d)))
           (and st1
                (let ((s2 (int-liate-split (cadr st1) x)))
                  (and s2
                       (let ((st2 (int-parts-step (cadr st1) (car s2) (cadr s2) x d)))
                         (and st2
                              (let ((c (simplify (list '* (cadr st2) (list '^ e -1)))))
                                (and (x-free? c x) (not (equal? c 1))
                                     (let ((res (simplify (list '* (list '^ (list '+ 1 (list '* -1 c)) -1)
                                                                (list '+ (car st1) (list '* -1 (car st2)))))))
                                       (if (step-log-enabled?)
                                           (record-step 'int-parts-cycle "Циклический случай: решаем уравнение относительно интеграла"
                                                        (string-append "после двух шагов ∫ f dx = P1 − P2 + c·∫ f dx, c = " (int-mp c)
                                                                       "; ∫ f dx = (P1 − P2)/(1 − c)")
                                                        (int-form e x) (int-p res)))
                                       res))))))))))))

; чисто тригонометрическое произведение/степень (все множители с x — ранг 4, не меньше двух): по частям раздувает
; ветвление до минут (sin²x·cos 3x ≈ 15 с и невычисленно) — этим занимаются int-trig/int-prodsum
(define (int-pure-trig-product? e x)
  (and (op-expr? e) (equal? (car e) '*)
       (let ((fs (filter (lambda (f) (not (x-free? f x))) (cdr e))))
         (and (> (length fs) 1) (every? (lambda (f) (= (int-rank f x) 4)) fs)))))

(define (int-parts e x d)
  ; INT.FIX3.c: перебор u/dv на раздутых произведениях — короткий бюджет приёма
  (int-with-combinatorial-limit d (lambda () (int-parts-body e x d))))

(define (int-parts-body e x d)
  (and (< d int-max-depth)
       (not (int-pure-trig-product? e x))
       (or (and (int-cyclic? e x)
                (with-step ('int-by-parts "Интегрирование по частям (циклический случай)" (int-form e x)
                            :comment "по частям дважды: исходный интеграл возвращается с множителем c, получаем уравнение" :after int-p)
                  (int-parts-cyclic e x d)))
           (let ((s (int-liate-split e x)))
             (and s
                  (with-step ('int-by-parts "Интегрирование по частям" (int-form e x)
                              :comment "∫ u dv = u·v − ∫ v du; u выбирается по правилу LIATE (логарифм, обратная тригонометрия, алгебраическая, тригонометрия, показательная)"
                              :after int-p)
                    (let ((st (int-parts-step e (car s) (cadr s) x d)))
                      (and st
                           (let ((r (int-go (cadr st) x (+ d 1))))
                             (if r (simplify (list '+ (car st) (list '* -1 r))) (begin (attempt-fail "интеграл v·du не берётся (по частям не сходится)") #f)))))))))))

; ---------- две подстановки (шаг INT.SQ) ----------
; A. u = xⁿ (n символьное или числовое) для c·x^(kn−1)·F(xⁿ), k ≥ 1 целое: x^(kn−1) dx = u^(k−1) du / n.
;    Множитель (w·x)^m при нецелом m раскрывается в w^m·x^m (w > 0 — условие ответа, как у остальных параметров).
; B. v = √(c+d·x) при единственном линейном подкоренном: x = (v²−c)/d, dx = 2v/d dv; подынтегральное должно стать
;    рациональным по v и степенями линейных по v оснований (дешёвая проверка int-ratpow-ok? до интегрирования —
;    иначе (a+b·(c+dx)^(3/2))^p уходит в длинный путь по частям).

(define (int-pow-node? f) (and (op-expr? f) (equal? (car f) '^) (= (length f) 3)))

; (w·x)^m, m нецелое → (список множителей, список констант w)
(define (int-split-wx f x)
  (if (and (int-pow-node? f) (x-free? (caddr f) x) (not (and (number? (caddr f)) (integer? (caddr f))))
           (op-expr? (cadr f)) (equal? (car (cadr f)) '*))
      (let ((cs (filter (lambda (t) (x-free? t x)) (cdr (cadr f))))
            (vs (filter (lambda (t) (not (x-free? t x))) (cdr (cadr f)))))
        (if (and (pair? cs) (= (length vs) 1) (equal? (car vs) x)
                 (every? (lambda (c) (or (not (number? c)) (> c 0))) cs))
            (list (list (simplify (list '^ (simplify (cons '* cs)) (caddr f))) (list '^ x (caddr f)))
                  (filter (lambda (c) (not (number? c))) cs))
            (list (list f) '())))
      (list (list f) '())))

(define (int-x-powers e x)
  (cond ((not (op-expr? e)) '())
        ((and (int-pow-node? e) (equal? (cadr e) x) (x-free? (caddr e) x)) (list (caddr e)))
        (else (append-map (lambda (a) (int-x-powers a x)) (cdr e)))))

; x^s → u^(s/n) (s/n рациональное число); голый x или другая зависимость — #f.
; Нецелое s/n при целом s запрещено: x³ = (x⁶)^(1/2) только при x > 0, а x³ определена на всей оси
; (cas-hard-110 №101: ∫3x⁵e^(x³)/(x⁶+2x³+1) давал e^|x³|/(1+|x³|) — ложный ответ при x < 0).
; При нецелом s подынтегральное само требует x > 0, и замена верна на его области.
(define (int-xpow-subst e x n u)
  (cond ((equal? e x) #f)
        ((x-free? e x) e)
        ((not (op-expr? e)) e)
        ((and (int-pow-node? e) (equal? (cadr e) x) (x-free? (caddr e) x))
         (let ((r (simplify (list '* (caddr e) (list '^ n -1)))))
           (and (number? r) (rational-number? r)
                (or (integer? r) (not (and (number? (caddr e)) (integer? (caddr e)))))
                (list '^ u r))))
        (else (let ((as (map (lambda (a) (int-xpow-subst a x n u)) (cdr e))))
                (and (every? (lambda (a) a) as) (cons (car e) as))))))

(define (int-powsub-try e x d fs rest xp m n consts)
  (let* ((m1 (simplify (list '+ m 1)))
         (kq (simplify (list '* m1 (list '^ n -1)))))
    (and (number? kq) (integer? kq) (>= kq 1)
         (let* ((u (int-uvar d))
                (rs (map (lambda (f) (int-xpow-subst f x n u)) rest)))
           (and (every? (lambda (f) f) rs)
                (let ((q (simplify (cons '* (append (filter (lambda (f) (x-free? f x)) fs)
                                                    (list (list '^ u (- kq 1)) (list '^ n -1))
                                                    rs)))))
                  (and (x-free? q x)
                       (with-step ('int-substitution "Метод подстановки" (int-form e x)
                                   :comment (lambda (r) (string-append "u = " (int-mp (list '^ x n)) ", du = n·x^(n−1) dx; x^(kn−1) dx = u^(k−1) du / n, k = "
                                                                       (to-string kq)))
                                   :after int-p)
                         (let ((r (begin
                                    (if (step-log-enabled?)
                                        (record-step 'int-substitution-change "Замена переменной"
                                                     (string-append "подынтегральное выражение через u: " (int-mp q) " du")
                                                     (int-form e x) (int-form q u)))
                                    (int-go q u (+ d 1)))))
                           (if r
                               (begin
                                 (map (lambda (c) (record-condition (list '> c 0) "integrate: параметр считается положительным")) consts)
                                 (simplify (replace-expr r u (list '^ x n))))
                               (begin (attempt-fail "не удалось проинтегрировать выражение через u") #f)))))))))))

(define (int-powsub e x d)
  (and (< d int-max-depth) (op-expr? e)
       (let* ((fs0 (if (equal? (car e) '*) (cdr e) (list e)))
              (sp (map (lambda (f) (int-split-wx f x)) fs0))
              (fs (append-map car sp))
              (consts (append-map cadr sp))
              (vs (filter (lambda (f) (not (x-free? f x))) fs))
              (xps (filter (lambda (f) (or (equal? f x) (and (int-pow-node? f) (equal? (cadr f) x) (x-free? (caddr f) x)))) vs)))
         (and (= (length xps) 1)
              (let* ((xp (car xps))
                     (m (if (equal? xp x) 1 (caddr xp)))
                     (rest (int-remove-first xp vs))
                     (ns (filter (lambda (s) (and (not (equal? s 1)) (not (equal? s 0))))
                                 (int-dedupe (int-x-powers (cons '* rest) x)))))
                (and (pair? rest)
                     (int-first (lambda (n) (int-guard (lambda () (int-powsub-try e x d fs rest xp m n consts)))) ns)))))))

; B: единственное линейное подкоренное (denom показателя 2)
(define (int-lin-rad-base e x)
  (let ((bs (int-dedupe (int-rad-bases e))))
    (and (= (length bs) 1) (int-slope (car bs) x) (car bs))))

(define (int-radsub e B v)
  (cond ((not (op-expr? e)) e)
        ((and (int-pow-node? e) (number? (caddr e)) (equal? (denom (caddr e)) 2) (equal? (expand (cadr e)) B))
         (list '^ v (* 2 (caddr e))))
        (else (cons (car e) (map (lambda (a) (int-radsub a B v)) (cdr e))))))

; рационально по v, нецелые степени — только линейных по v оснований
(define (int-ratpow-ok? e v)
  (cond ((x-free? e v) #t)
        ((not (op-expr? e)) #t)
        ((not (member? (car e) '(+ * ^ - /))) #f)
        ((int-pow-node? e)
         (let ((s (caddr e)))
           (if (and (number? s) (integer? s))
               (int-ratpow-ok? (cadr e) v)
               (and (x-free? s v) (if (int-slope (cadr e) v) #t #f)))))
        (else (every? (lambda (a) (int-ratpow-ok? a v)) (cdr e)))))

; ∫ P(v)·(L(v))^s dv, L линейно по v, s без v и не целое: w = L, P((w−a0)/b) = Σ c_k w^k, ответ Σ c_k L^(k+s+1) / ((k+s+1)·b)
; (многочлен степени ≈ 7 общий каскад берёт ≈ 7 с, здесь — миллисекунды); иначе #f
(define (int-linpow-direct e v)
  (let* ((fs (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))
         (ps (filter (lambda (f) (and (int-pow-node? f) (int-slope (cadr f) v) (x-free? (caddr f) v)
                                      (not (and (number? (caddr f)) (integer? (caddr f))))))
                     fs)))
    (and (= (length ps) 1)
         (let* ((pw (car ps)) (L (cadr pw)) (s (caddr pw))
                (others (int-remove-first pw fs))
                (cs (filter (lambda (f) (x-free? f v)) others))
                (rest (simplify (cons '* (cons 1 (filter (lambda (f) (not (x-free? f v))) others))))))
           (and (polynomial? rest v)
                (let* ((b (int-slope L v)) (a0 (coeff L v 0)) (w '%lp) (ib '%ib)
                       (pw2 (expand (replace-expr rest v (list '* (list '+ w (list '* -1 a0)) ib))))
                       (n (degree pw2 w)))
                  (simplify
                   (list '* (cons '* cs)
                         (replace-expr
                          (cons '+ (map (lambda (k)
                                          (let ((e1 (simplify (list '+ k 1 s))))
                                            (list '* (coeff pw2 w k) (list '^ L e1) (list '^ e1 -1) ib)))
                                        (range (+ n 1))))
                          ib (list '^ b -1))))))))))

(define (int-sqrtsub e x d)
  (and (< d int-max-depth) (op-expr? e)
       (let ((B (int-lin-rad-base e x)))
         (and B
              (let* ((v (int-uvar d))
                     (dd (int-slope B x))
                     (c (coeff B x 0))
                     (xv (simplify (list '* (list '^ dd -1) (list '+ (list '^ v 2) (list '* -1 c)))))
                     (e1 (replace-expr (int-radsub e B v) x xv))
                     (q (and (x-free? e1 x) (int-ratpow-ok? e1 v)
                             (simplify (list '* e1 2 v (list '^ dd -1))))))
                (and q (x-free? q x)
                     (with-step ('int-substitution "Метод подстановки" (int-form e x)
                                 :comment (lambda (r) (string-append "v = √(" (int-mp B) "), x = (v² − c)/d, dx = 2v/d dv"))
                                 :after int-p)
                       (let ((r (begin
                                  (if (step-log-enabled?)
                                      (record-step 'int-substitution-change "Замена переменной"
                                                   (string-append "подынтегральное выражение через v: " (int-mp q) " dv")
                                                   (int-form e x) (int-form q v)))
                                  (or (int-linpow-direct q v) (int-go q v (+ d 1))))))
                         (if r
                             (simplify (replace-expr r v (list '^ B 1/2)))
                             (begin (attempt-fail "не удалось проинтегрировать выражение через v") #f))))))))))

(int-add-strategy int-powsub)
(int-add-strategy int-sqrtsub)
(int-add-strategy int-parts)

; ---------- раскрытие скобок (последний шанс) ----------
(define (int-expand e x d)
  ; INT.FIX3.c: раскрытие скобок — короткий бюджет приёма
  (int-with-combinatorial-limit d (lambda () (int-expand-body e x d))))

(define (int-expand-body e x d)
  (and (< d 3) (op-expr? e)
       (or (and (equal? (car e) '*) (any? (lambda (f) (and (op-expr? f) (equal? (car f) '+))) (cdr e)))
           (and (equal? (car e) '^) (op-expr? (cadr e)) (equal? (car (cadr e)) '+) (integer? (caddr e)) (> (caddr e) 1)))
       (let ((ex (expand e)))
         (and (not (equal? ex e))
              (with-step ('int-expand "Раскрытие скобок в подынтегральной функции" (int-form e x)
                          :comment "раскрываем скобки и интегрируем получившуюся сумму" :after int-p)
                (begin
                  (if (step-log-enabled?)
                      (record-step 'int-expand-brackets "Раскрытие скобок" "" (int-form e x) (int-form ex x)))
                  (let ((r (int-go ex x (+ d 1)))) (if r r (begin (attempt-fail "раскрытая сумма не интегрируется") #f)))))))))

(int-add-strategy int-expand)

; ---------- два квадратных радикала, нечётное подынтегральное (шаг INT.GAPS.4) ----------
; f = x·h(x²), радикалы √P₁(x²), √P₂(x²), P_i линейны по t = x². x dx = dt/2, h — функция t с двумя линейными
; радикалами. Подстановка u = √P₁(t) = √(a+bt): t = (u²−a)/b, dt = 2u du/b; радикал √P₂ становится √(квадратный по u) —
; один радикал, дальше обычный каскад (алгебраическая стратегия). Точное тождество (x² = t, u² = P₁), ветвей нет:
; u ≥ 0 — главное значение корня. Чётное f (√(x²+c)√(x²+d) без x) — эллиптика, сюда не берётся.
; Каждый ответ: int-check и численная проверка самого F (флаг *check-numeric-F* на время проверки = #t, нужен 'ok).
(define (int-rad-to-u e t P1 u a1 b1)
  (cond ((equal? e t) (list '* (list '^ b1 -1) (list '+ (list '^ u 2) (list '* -1 a1))))
        ((not (op-expr? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2))
         (int-rad-to-u (list '^ (cadr e) 1/2) t P1 u a1 b1))
        ((and (equal? (car e) '^) (= (length e) 3) (number? (caddr e)) (equal? (denom (caddr e)) 2))
         (if (equal? (expand (cadr e)) P1)
             (list '^ u (* 2 (caddr e)))
             (list '^ (expand (int-rad-to-u (cadr e) t P1 u a1 b1)) (caddr e))))
        (else (cons (car e) (map (lambda (a) (int-rad-to-u a t P1 u a1 b1)) (cdr e))))))

(define int-rubi-nested-time-limit 2)
(define (int-rubi-nested e x) (and int-rubi-enabled (int-rubi-nested-on e x)))
(define (int-rubi-nested-on e x)
  (let ((r (with-step ('rubi "Правила Rubi (вложенный интеграл с двумя радикалами)" (int-form e x)
                       :comment "остаток после «по частям»: интеграл с √P₁ и √P₂ без подстановки — таблица Rubi, ответ проверен дифференцированием"
                       :after (lambda (v) (if v (int-p v) "")))
             (int-guard-raw (lambda () (rubi-integrate-within e x int-rubi-nested-time-limit))))))
    (and r (not (equal? r 'unknown)) (not (int-has-integrate? r)) r)))

(define (int-F-numeric-ok? F f x)
  (let ((old *check-numeric-F*))
    (set! *check-numeric-F* #t)
    (let ((s (try (int-check-F-status F f x) (lambda (err) 'skip))))
      (set! *check-numeric-F* old)
      (equal? s 'ok))))

(define (int-two-rad-odd e x d)
  (and (< d int-max-depth) (int-algebraic-in? e x)
       (let ((bs (int-dedupe (int-rad-bases e))))
         (and (= (length bs) 2)
              (let* ((t 'int-tr-t)
                     (qt (int-xpow-subst (simplify (list '/ e x)) x 2 t)))
                (and qt (x-free? qt x)
                     (let ((pt (int-dedupe (int-rad-bases qt))))
                       (and (= (length pt) 2)
                            (every? (lambda (p) (int-slope p t)) pt)
                            (int-first (lambda (P1) (int-two-rad-odd-with e x d qt t P1)) pt)))))))))

(define (int-two-rad-odd-with e x d qt t P1)
  (let* ((u (int-uvar d)) (a1 (coeff P1 t 0)) (b1 (int-slope P1 t))
         (g (simplify (list '* (int-rad-to-u qt t P1 u a1 b1) u (list '^ b1 -1)))))
    (and (x-free? g x) (x-free? g t) (<= (length (int-dedupe (int-rad-bases g))) 1)
         (let ((r (with-step ('int-substitution "Подстановка t = x², u = √(a + b·t): один квадратный радикал" (int-form e x)
                              :comment "x dx = dt/2; u = √P₁(t): t = (u² − a)/b, dt = 2u du/b; радикал √P₂ становится квадратным по u"
                              :after int-p)
                    ; один радикал: интеграл по u — самостоятельная задача с глубиной 0 (на вложенных шагах алгебраические
                    ; стратегии и кривая рода 0 не зовутся); рекурсия сюда невозможна — у g не больше одного радикала
                    (int-go g u 0))))
           (and r
                (let ((F (simplify (replace-expr r u (list '^ (replace-expr P1 t (list '^ x 2)) 1/2)))))
                  (and (x-free? F u) (x-free? F t)
                       (int-check F e x) (int-F-numeric-ok? F e x)
                       F)))))))
