; risch/reduce.lisp — нормальная/специальная части, редукция Эрмита, логарифмическая часть (ЛРТ) над башней: подшаг 21k.3
;
; Источники — Бронштейн, Symbolic Integration I, гл. 5–6 (Эрмит, логарифмическая часть: MONOTOOL/INTHERTR/monomialIntegrate1).
; Представление — field.lisp: башня, многочлен K[θ] — список коэффициентов (старшая степень первой), θ — верхний моном башни tw.
; ДРОБЬ из K(θ) — пара (числитель знаменатель) из двух многочленов K[θ]. Вызовы из драйвера (21k.4): rs-hermite, rs-residue-integral.
; Только трансцендентные exp/log-уровни; для tan/нестандартных Dθ работает всё, кроме правила «специальных множителей нет» (оно общее: p | Dp).
;
; ---------- Определения ----------
; p ∈ K[θ] нормален, если НОД(p, Dp) = 1, и специален, если p | Dp (D — производная башни, rs-deriv-poly). Для exp специальны
; степени θ (с константой), для log — только константы из K. Знаменатель d = dn·ds: dn нормален, ds специален.
; f = a/d = P + an/dn + as/ds (rs-canonical). Эрмит применяется только к an/dn; P + as/ds идёт в остаток r.
;
; ---------- Эрмит (Мак, линейный) ----------
; dn = U·Vᵐ (V — бесквадратный множитель наибольшей кратности m ≥ 2, U взаимно прост с V): ищем B, C: B·(U·DV) + C·V = A/(1−m),
; deg B < deg V; тогда A/(U Vᵐ) = D(B/Vᵐ⁻¹) + ((1−m)·C − U·DB)/(U Vᵐ⁻¹). Условие НОД(U·DV, V) = 1 — нормальность V.
;
; ---------- ЛРТ ----------
; h = a/d, d бесквадратен и нормален, deg a < deg d. R(z) = res_θ(d, a − z·Dd) ∈ K[z] (z — символ rs-z, K — нижняя башня).
; R = c·∏Rᵢ^i (бесквадратное разложение по z); Qᵢ = НОД(Rᵢ, κ(Rᵢ)), κ(Σ aⱼzʲ) = Σ (Daⱼ)zʲ — множитель с КОНСТАНТНЫМИ корнями.
; Для Qᵢ — член ПРС Sᵢ степени i (кратность Rᵢ), сделанный унитарным по θ с коэффициентами по модулю Qᵢ. Тогда
;   ∫ h = Σᵢ Σ_{Qᵢ(α)=0} α·log Sᵢ(α, θ) + ∫ (h − D(Σ …)),  остаток — многочлен/ноль, если ВСЕ корни R константы.
; Флаг «элементарно»: Rᵢ = Qᵢ для всех i, т. е. R | κ(R); иначе (теорема Лиувилля, проект §1 п. 3) ∫ h неэлементарен.

(module risch)

(define rs-z '%rsz)                                                  ; переменная вычетов

; ---------- общее: степень, произведение, дроби ----------
(define (rs-pow p n) (if (= n 0) (list 1) (rs-mul p (rs-pow p (- n 1)))))
(define (rs-prod-factors fs) (foldl (lambda (acc fm) (rs-mul acc (rs-pow (car fm) (cadr fm)))) (list 1) fs))
(define (rs-top-theta tw) (if (rs-top tw) (rs-level-theta (rs-top tw)) (rs-tower-x tw)))   ; база (21k.7a): «моном» x

(define (rs-frac-add f g)
  (list (rs-add (rs-mul (car f) (cadr g)) (rs-mul (car g) (cadr f))) (rs-mul (cadr f) (cadr g))))
; сократить на НОД, знаменатель унитарен
(define (rs-frac-cancel f)
  (let* ((g (rs-gcd (car f) (cadr f))) (n (rs-quo (car f) g)) (d (rs-quo (cadr f) g)) (c (rs-inv (car d))))
    (list (rs-scale n c) (rs-scale d c))))
(define (rs-frac-expr tw f)
  (let ((th (rs-top-theta tw)))
    (simplify (list '* (rs-to-expr (car f) th) (list '^ (rs-to-expr (cadr f) th) -1)))))

; ---------- нормальная и специальная части ----------
(define (rs-special? tw f) (null? (rs-rem (rs-deriv-poly tw f) f)))   ; f | Df

; (rs-splitfactor-sqf tw p) → (lc нормальные специальные): p = lc·∏fᵐ, списки ((f m) …), fᵢ унитарные бесквадратные
(define (rs-splitfactor-sqf tw p)
  (let* ((sf (rs-sqfree p)) (fs (cdr sf)))
    (list (car sf)
          (filter (lambda (fm) (not (rs-special? tw (car fm)))) fs)
          (filter (lambda (fm) (rs-special? tw (car fm))) fs))))

; (rs-splitfactor tw p) → (pn ps): p = pn·ps, pn нормален (несёт старший коэффициент), ps специален унитарен
(define (rs-splitfactor tw p)
  (if (null? p)
      (list '() (list 1))
      (let ((r (rs-splitfactor-sqf tw p)))
        (list (rs-scale (rs-prod-factors (cadr r)) (car r)) (rs-prod-factors (caddr r))))))

; (rs-canonical tw a d) → (P (an dn) (as ds)): a/d = P + an/dn + as/ds, dn нормален, ds специален, deg an < deg dn, deg as < deg ds
(define (rs-canonical tw a d)
  (let* ((qr (rs-divmod a d)) (sp (rs-splitfactor tw d)) (dn (car sp)) (ds (cadr sp))
         (e (rs-diophantine ds dn (cadr qr))))                         ; s·ds + t·dn = r, deg s < deg dn
    (list (car qr) (list (car e) dn) (list (cadr e) ds))))

; ---------- редукция Эрмита ----------
(define (rs-hermite-normal tw a d g)                                 ; d унитарен и нормален, deg a < deg d, g — накопленная дробь
  (let* ((fs (cdr (rs-sqfree d))))
    (if (or (null? fs) (< (cadr (last fs)) 2))
        (list g (list a d))
        (let* ((fm (last fs)) (V (car fm)) (m (cadr fm)) (U (rs-quo d (rs-pow V m))) (dV (rs-deriv-poly tw V))
               (sol (rs-diophantine (rs-mul U dV) V (rs-scale a (rs-inv (- 1 m))))))
          (if (not sol)
              (error "risch: Эрмит — знаменатель не нормален (НОД(U·DV, V) ≠ 1)")
              (let* ((B (car sol)) (C (cadr sol)) (Vm (rs-pow V (- m 1))))
                (rs-hermite-normal tw
                                   (rs-sub (rs-scale C (- 1 m)) (rs-mul U (rs-deriv-poly tw B)))
                                   (rs-mul U Vm)
                                   (rs-frac-add g (list B Vm)))))))))

; (rs-hermite tw a d) → (g h r) — три дроби: a/d = Dg + h + r; знаменатель h унитарен, бесквадратен и нормален,
; r = P + as/ds (многочлен + специальная часть). d ≠ 0.
(define (rs-hermite tw a d)
  (let* ((cr (rs-canonical tw a d)) (nf (cadr cr)) (sf (caddr cr)) (dn (cadr nf)) (c (rs-inv (car dn)))
         (res (rs-hermite-normal tw (rs-scale (car nf) c) (rs-scale dn c) (list '() (list 1))))
         (h (cadr res)) (qr (rs-divmod (car h) (cadr h)))             ; для Dθ степени ≥ 2 (tan) в h может появиться многочлен
         (p (rs-add (car cr) (car qr))))
    (list (rs-frac-cancel (car res))
          (rs-frac-cancel (list (cadr qr) (cadr h)))
          (rs-frac-cancel (list (rs-add (rs-mul p (cadr sf)) (car sf)) (cadr sf))))))

; ---------- Лазар — Риобу — Трагер ----------
(define (rs-kappa lower p) (rs-trim (map (lambda (c) (rs-deriv lower c)) p)))

; ST.3д: данные последней резольвенты для шага журнала — (R(z) ((множитель кратность deg Q deg f) …)) или '()
(define rs-lrt-last '())

; коэффициенты члена ПРС (выражения от z) → многочлены от z по модулю Q
(define (rs-mod-q m Q) (map (lambda (c) (rs-rem (rs-from-expr c rs-z) Q)) m))

; унитарный по θ член ПРС по модулю Q: S = M / lc(M) в K[z]/(Q); #f, если lc необратим по модулю Q
(define (rs-reduce-member m Q)
  (let* ((zs (rs-mod-q m Q)) (e (rs-gcdex (car zs) Q)))
    (and (= (rs-deg (caddr e)) 0)
         (map (lambda (c) (rs-to-expr (rs-rem (rs-mul c (car e)) Q) rs-z)) zs))))

; пары (Q S) по бесквадратным множителям R: (list-of-(Q S) элементарно?) или #f
(define (rs-lrt-entries tw d prs fs lower)
  (if (null? fs)
      (list '() #t)
      (let* ((f (car (car fs))) (m (cadr (car fs))) (Q (rs-gcd f (rs-kappa lower f)))
             (rest (rs-lrt-entries tw d prs (cdr fs) lower)))
        (cond ((not rest) #f)
              ((< (rs-deg Q) 1) (list (car rest) #f))
              (else
               (let* ((mem (if (= m (rs-deg d)) (rs-monic d) (rs-prs-member prs m)))
                      (S (and mem (if (= m (rs-deg d)) mem (rs-reduce-member mem Q)))))
                 (cond ((not S) (rs-unknown "ЛРТ: нет члена ПРС нужной степени или старший коэффициент необратим по модулю Q" (list m Q)))
                       (else (list (cons (list Q S) (car rest))
                                   (and (cadr rest) (= (rs-deg Q) (rs-deg f))))))))))))

; Точный результант res_θ(a, b) по Евклиду в K(z)[θ]: res(a, b) = (−1)^{deg a·deg b}·lc(b)^{deg a − deg r}·res(b, r), r = a mod b.
; (21k.5) Нужен вместо члена ПРС степени 0: при deg b = deg a (exp-уровень: deg D d = deg d) ПРС дефектна и её последний член —
; не результант (∫ −2/(e^{2x}+1): член 2 − 2z вместо 4(z − 1)², кратность корня теряется).
(define (rs-resultant a b)
  (cond ((or (null? a) (null? b)) 0)
        ((= (rs-deg b) 0) (rs-nf (list '^ (car b) (rs-deg a))))
        ((= (rs-deg a) 0) (rs-nf (list '^ (car a) (rs-deg b))))
        (else
         (let ((r (rs-rem a b)) (da (rs-deg a)) (db (rs-deg b)))
           (if (null? r)
               0
               (rs-nf (list '* (if (= (remainder (* da db) 2) 1) -1 1) (list '^ (car b) (- da (rs-deg r))) (rs-resultant b r))))))))

; (rs-residue-reduce tw a d) → ((( Q S) …) элементарно?) | #f
; d унитарен/бесквадратен/нормален; многочленная часть a div d отбрасывается (её интегрирует драйвер). Q — многочлен от z (список
; коэффициентов в K, унитарный), S — унитарный многочлен K[θ] (список выражений от z, коэффициенты по модулю Q). Пусто — вычетов нет.
(define (rs-residue-reduce tw a d)
  (let ((a1 (rs-rem a d)))
    (if (or (null? a1) (< (rs-deg d) 1))
        (begin (set! rs-lrt-last '()) (list '() #t))
        (let* ((lower (rs-lower tw)) (Dd (rs-deriv-poly tw d))
               (b (rs-sub a1 (rs-scale Dd rs-z)))
               (prs (rs-prs d b))
               (res (rs-resultant d b)))
          (if (rs-zero? res)
              (begin (set! rs-lrt-last '()) (rs-unknown "ЛРТ: результант равен нулю" d))
              (let* ((R (rs-monic (rs-from-expr res rs-z))) (sf (rs-sqfree R)))
                ; ST.3д: резольвента и постоянство корней по множителям (Q = НОД(Rᵢ, κ(Rᵢ)))
                (set! rs-lrt-last
                      (list (rs-to-expr R rs-z)
                            (map (lambda (fm)
                                   (list (car fm) (cadr fm)
                                         (rs-deg (rs-gcd (car fm) (rs-kappa lower (car fm))))
                                         (rs-deg (car fm))))
                                 (cdr sf))))
                (rs-lrt-entries tw d prs (cdr sf) lower)))))))

; ---------- сборка ответа ----------
; Σ_{Q(z)=0} z·log S(z, θ) для одной пары: линейные множители Q над ℚ(параметры) — явные a·log S(a, θ); остальное — root-sum по tv
(define (rs-subst-z e c) (replace-expr e rs-z c))
(define (rs-linear-log tw S c)
  (list '* c (list 'log (rs-to-expr (map (lambda (e) (rs-nf (rs-subst-z e c))) S) (rs-top-theta tw)))))
(define (rs-rootsum-log tw S Qe tv)
  (root-sum tv Qe (list '* tv (list 'log (rs-subst-z (rs-to-expr S (rs-top-theta tw)) tv)))))

; (21k.5′) Q = a·z² + b с b/a = c² > 0 (корни ±ic), S = S₀ + z·S₁ (S₀, S₁ ∈ K[θ]): Σ z·log S = ic·(log(S₀ + icS₁) − log(S₀ − icS₁)) =
; −2c·atan(c·S₁/S₀) с точностью до константы. Так ∫ atan(eˣ)·eˣ/(1 + e^{2x}) получает atan(eˣ) вместо root-sum, который
; многочленная часть приняла бы за логарифм чужого аргумента. #f — не подходит (остаётся root-sum).
(define (rs-z-part e k)                                              ; коэффициент при z^k выражения e, многочленного по z (знаменатель без z), или #f
  (let* ((tg (together e)) (d (denom tg)))
    (and (not (contains-sym? d rs-z)) (rs-nf (list '* (coeff (numer tg) rs-z k) (list '^ d -1))))))
(define (rs-quad-atan tw S f tv)
  (let ((a2 (coeff f tv 2)) (a1 (coeff f tv 1)) (a0 (coeff f tv 0)))
    (and (equal? (degree f tv) 2) (rs-zero? a1)
         (let ((k (rs-nf (list '* a0 (list '^ a2 -1)))))
           (and (rational-number? k) (> k 0)
                (let* ((c (simplify (list '^ k 1/2))) (th (rs-top-theta tw))
                       (s0 (map (lambda (e) (rs-z-part e 0)) S)) (s1 (map (lambda (e) (rs-z-part e 1)) S)))
                  (and (every? (lambda (e) e) s0) (every? (lambda (e) e) s1) (not (every? rs-zero? s1))
                       (not (every? rs-zero? s0))
                       (simplify (list '* -2 c (list 'atan (rs-nf (list '* c (rs-to-expr s1 th) (list '^ (rs-to-expr s0 th) -1)))))))))))))
(define (rs-entry-terms tw entry tv)
  (let* ((Q (car entry)) (S (cadr entry)) (Qe (rs-to-expr Q tv)))
    (if (= (rs-deg Q) 1)
        (list (rs-linear-log tw S (rs-nf (list '* -1 (cadr Q)))))
        (let ((fl (try (cdr (factor-list Qe)) (lambda (err) (list (list Qe 1))))))
          (map (lambda (fm)
                 (let ((f (car fm)))
                   (if (equal? (degree f tv) 1)
                       (rs-linear-log tw S (rs-nf (list '* -1 (coeff f tv 0) (list '^ (coeff f tv 1) -1))))
                       (or (rs-quad-atan tw S f tv) (rs-rootsum-log tw S f tv)))))
               fl)))))

; (rs-log-part tw entries tv) → выражение от θ (без обратной подстановки)
(define (rs-log-part tw entries tv)
  (simplify (cons '+ (apply append (map (lambda (en) (rs-entry-terms tw en tv)) entries)))))

; (rs-residue-integral tw a d tv table) → (F элементарно?) | #f: логарифмическая часть ∫ a/d, обратная подстановка по table (tower.lisp)
(define (rs-residue-integral tw a d tv table)
  (let ((r (rs-residue-reduce tw a d)))
    (and r (list (rs-back-subst (rs-log-part tw (car r) tv) table) (cadr r)))))
