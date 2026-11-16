; integrate/blake.lisp — метод Блейка для псевдоэллиптических интегралов (шаг INT.ANSATZ.7)
;
; Источник метода и идея порта: S. Blake, «A Simple Method for Computing Some Pseudo-Elliptic Integrals in Terms of
; Elementary Functions», arXiv:2004.04910; реализация автора на Mathematica — github.com/stblake/algebraic_integration
; (MIT, Copyright (c) 2020 stblake; текст лицензии — THIRD-PARTY-NOTICES.md). Здесь — не построчный перевод, а порт алгоритма на Lisp.
;
; Подынтегральное  f = R(x)·r(x)^(j/m),  r — многочлен степени N > 2 над ℚ, R рациональна, 0 < j < m. Ищется подстановка Лорана
; u = s(x)/x^k, при которой  r(x) = xᴱ·(a₂u² + a₀)  (m = 2: «квадратичное подкоренное»)  или  r(x) = xᴱ·u  (линейное: u = r/xᴱ, m | E),
; и рациональная R̃(u) с  R̃(u(x)) = R(x)·x^(E·j/m)/u′(x); тогда  ∫f dx = ∫R̃(u)·(a₂u² + a₀)^(j/m) du  — вызов integrate по u
; (подкоренное степени ≤ 2), обратная подстановка и int-check по исходному f.
;   Радикандная часть (полиномиальная система Блейка r = a₂s² + a₁s·x^k + a₀x^(2k)) решена без Грёбнера: сдвигом u на константу
;   a₁ = 0, тогда r − a₀x^(2k) = a₂s² — совершенный квадрат; s делит D = x·r′ − 2k·r (x·P′ − 2k·P при P = r − a₀x^(2k)), поэтому
;   s — монический делитель степени N/2 многочлена D (перебор по factor-list), a₂ = старший коэффициент r, a₀ — остаток;
;   k = N/2 — тот же поиск для обращённого многочлена. Рациональная часть: R̃ = a(u)/b(u) — линейная система по значениям в
;   рациональных точках (nullspace над ℚ); степень R̃ известна заранее: deg g / deg u.
; Внутренние имена: bk-.
(module integrate
  (export int-blake int-blake-stats without-blake))

(define int-blake-enabled #t)
(define int-blake-time-limit 8)
(define bk-why #f)
(define bk-depth 0)
(define bk-info '())

(define (int-blake-stats) (list bk-why bk-info))
(define (without-blake thunk)
  (let ((old int-blake-enabled))
    (set! int-blake-enabled #f)
    (unwind-protect (thunk) (set! int-blake-enabled old))))

(define (bk-fail! why) (set! bk-why why) #f)
(define (bk-rat? v) (or (integer? v) (equal? (type-of v) 'rational)))

; ---------- многочлены как списки коэффициентов по возрастанию степеней (рациональные числа) ----------
(define (bk-trim a)
  (let loop ((r (reverse a)))
    (cond ((null? r) '())
          ((= (car r) 0) (loop (cdr r)))
          (else (reverse r)))))
(define (bk-deg a) (- (length (bk-trim a)) 1))
(define (bk-padd a b)
  (cond ((null? a) b) ((null? b) a)
        (else (cons (+ (car a) (car b)) (bk-padd (cdr a) (cdr b))))))
(define (bk-pscale c a) (map (lambda (v) (* c v)) a))
(define (bk-pmul a b)
  (if (null? a) '()
      (bk-padd (bk-pscale (car a) b) (cons 0 (bk-pmul (cdr a) b)))))
(define (bk-peval a v) (foldl (lambda (acc c) (+ (* acc v) c)) 0 (reverse a)))
(define (bk-pder a)
  (if (or (null? a) (null? (cdr a))) '()
      (let loop ((l (cdr a)) (i 1) (acc '()))
        (if (null? l) (reverse acc) (loop (cdr l) (+ i 1) (cons (* i (car l)) acc))))))
(define (bk-lc a) (let ((t (bk-trim a))) (if (null? t) 0 (car (reverse t)))))
(define (bk-poly-expr cs x) (coefficients->poly cs x))
(define (bk-coefs e x) (coefficients (expand e) x))

; ---------- разбор: f = R(x)·r(x)^(j/m) ----------
(define (bk-ratl? e x)
  (cond ((number? e) #t)
        ((symbol? e) (equal? e x))
        ((and (op-expr? e) (member? (car e) '(+ *))) (every? (lambda (u) (bk-ratl? u x)) (cdr e)))
        ((and (op-expr? e) (equal? (car e) '^) (integer? (nth e 2))) (bk-ratl? (nth e 1) x))
        (else #f)))
(define (bk-polyq? e x) (and (bk-ratl? e x) (polynomial? e x)))

; (множители-рациональные . радикалы), радикалы — ((основание . показатель) …); #f — не разобрать
(define (bk-flatten e x)
  (cond ((and (op-expr? e) (equal? (car e) '*))
         (let loop ((l (cdr e)) (rat '()) (rad '()))
           (if (null? l) (cons rat rad)
               (let ((p (bk-flatten (car l) x)))
                 (and p (loop (cdr l) (append rat (car p)) (append rad (cdr p))))))))
        ((and (op-expr? e) (equal? (car e) '^) (bk-rat? (nth e 2)) (not (integer? (nth e 2))))
         (and (bk-polyq? (nth e 1) x) (cons '() (list (cons (nth e 1) (nth e 2))))))
        ((bk-ratl? e x) (cons (list e) '()))
        (else #f)))

; результат: (R r m j N) — R выражение (рациональная часть), r — многочлен-выражение, m, j, N
; (sqrt B) → (^ B 1/2): math-eval и результаты упрощения пишут корень головой sqrt
(define (bk-has-sqrt? e)
  (and (pair? e) (or (equal? (car e) 'sqrt) (any? bk-has-sqrt? (cdr e)))))
(define (bk-unsqrt e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2)) (list '^ (bk-unsqrt (nth e 1)) 1/2))
        (else (cons (car e) (map bk-unsqrt (cdr e))))))

(define (bk-parse f0 x)
  (let* ((f (if (bk-has-sqrt? f0) (simplify (bk-unsqrt f0)) f0))
         (p (bk-flatten f x)))
    (cond ((not p) (bk-fail! (if (pair? (int-symbols f x)) 'parameters 'not-single-radical)))
          ((null? (cdr p)) (bk-fail! 'no-radical))
          (else
           (let* ((base (car (car (cdr p)))) (bexp (expand base)))
             (if (not (every? (lambda (rr) (equal? (expand (car rr)) bexp)) (cdr p)))
                 (bk-fail! 'several-radicals)
                 (let* ((q (apply + (map cdr (cdr p))))
                        (cs (bk-coefs bexp x)))
                   (cond ((not (every? bk-rat? cs)) (bk-fail! 'parameters))
                         ((integer? q) (bk-fail! 'integer-power))
                         (else (bk-normalize (cons '* (car p)) bexp q x))))))))))

(define (bk-normalize rat0 bexp q x)
  (let* ((m (denom q)) (n (numer q))
         (fl (factor-list bexp))
         (c (car fl)) (fs (cdr fl))
         (rr (map (lambda (fk) (modulo (cadr fk) m)) fs))
         ; r = c·Πfᵢ^(kᵢ mod m); оставшееся Πfᵢ^(n·(kᵢ − cᵢ)/m) — рациональная часть
         (rest (cons '* (map2 (lambda (fk cc) (list '^ (car fk) (quotient (* n (- (cadr fk) cc)) m))) fs rr)))
         (r (expand (cons '* (cons c (map2 (lambda (fk cc) (list '^ (car fk) cc)) fs rr)))))
         (nn (bk-deg (bk-coefs r x)))
         (j (modulo n m))
         (fl2 (floor (/ n m)))
         (rat (simplify (list '* rat0 rest (list '^ r fl2)))))
    (cond ; знак: при чётном m вынос fᵢ^(n·(kᵢ−cᵢ)/m) из-под корня верен только если этот показатель чётен — иначе теряется |fᵢ|
          ; (пилот c1b8d62: ∫√((5x+3)²) давал 5x²/2 + 3x — неверно при x < −3/5); множитель x — отдельный путь (x/|x|)·F̂ с численной проверкой
          ((and (even? m)
                (any? (lambda (b) b) (map2 (lambda (fk cc) (and (not (equal? (car fk) x)) (odd? (quotient (* n (- (cadr fk) cc)) m)))) fs rr)))
           (bk-fail! 'sign))
          ((<= nn 2)
           ; радикал после сокращения кратных множителей — квадратный (1/√(x⁴+4x+3) = 1/((x+1)·√(x²−2x+3))): интеграл упрощённой формы
           (if (or (not (= fl2 0)) (any? (lambda (d) (not (= d 0))) (map2 (lambda (fk cc) (- (cadr fk) cc)) fs rr)))
               (list 'reduced (list '* rat (list '^ r (/ j m))))
               (bk-fail! 'degree-le-2)))
          (else (list rat r m j nn)))))

; ---------- квадратичное подкоренное (m = 2): r = a₂·s² + a₀·x^(2k) ----------
; все наборы ((s a2 a0)) для степени k, 0 ≤ k < h, N = 2h; s монический степени h, a₂ = lc(r)
(define (bk-sq-sets rc k)
  (let* ((n (bk-deg rc)) (h (quotient n 2)))
    (if (or (odd? n) (< n 4)) '()
        (let* ((xr1 (cons 0 (bk-pder rc)))
               (dd (bk-trim (bk-padd xr1 (bk-pscale (* -2 k) rc)))))
          (if (null? dd) '()
              (let* ((fl (factor-list (bk-poly-expr dd 'x)))
                     (fs (map (lambda (fk) (cons (let ((cc (bk-coefs (car fk) 'x))) (bk-pscale (/ 1 (bk-lc cc)) cc)) (cadr fk))) (cdr fl)))
                     (a2 (bk-lc rc))
                     (res '()))
                (for-each (lambda (cur)
                            (let* ((s2 (bk-pmul cur cur))
                                   (tt (bk-trim (bk-padd rc (bk-pscale (- a2) s2)))))
                              (if (and (pair? tt) (= (bk-deg tt) (* 2 k))
                                       (every? (lambda (v) (= v 0)) (reverse (cdr (reverse tt)))))
                                  (set! res (cons (list cur a2 (car (reverse tt))) res)))))
                          (bk-divisors fs h))
                res))))))

; все произведения степеней из fs = ((многочлен . кратность) …) суммарной степени ровно h
(define (bk-divisors fs h)
  (let pick ((l fs) (cur '(1)) (dg 0))
    (cond ((= dg h) (list cur))
          ((> dg h) '())
          ((null? l) '())
          (else
           (let ((fp (car (car l))) (mu (cdr (car l))))
             (let mult ((i 0) (c cur) (d dg) (acc '()))
               (if (> i mu)
                   acc
                   (mult (+ i 1) (bk-pmul c fp) (+ d (bk-deg fp))
                         (append acc (pick (cdr l) c d))))))))))

; ---------- рациональная часть: R̃(u(x)) = g(x) ----------
(define bk-pts '(2 3 -2 5 -3 7 4 -4 6 -5 8 9 -6 10 11 -7 12 13 -8 14 15 -9 16 17 18 19 20 21 22 23 24 25))

(define (bk-ratf e x)
  (let* ((t (together e)))
    (cons (bk-coefs (numer t) x) (bk-coefs (denom t) x))))

; u = (un . ud), g = (gn . gd) — пары списков коэффициентов; ответ (a b) — коэффициенты a(u), b(u) по возрастанию, или #f
(define (bk-solve-rational u g)
  (let* ((eu (max (bk-deg (car u)) (bk-deg (cdr u))))
         (dg (max (bk-deg (car g)) (bk-deg (cdr g)))))
    (cond ((<= eu 0) #f)
          ((not (= (modulo dg eu) 0)) (bk-fail! 'degree-mismatch))
          (else
           (let* ((rho (quotient dg eu)) (nun (* 2 (+ rho 1))))
             (let loop ((pts bk-pts) (rows '()) (us '()))
               (cond
                 ((and (>= (length rows) (+ nun 4)) (>= (length us) (+ rho 4)))
                  (let ((ns (nullspace rows)))
                    (if (null? ns) (bk-fail! 'no-rational)
                        (let* ((v (car ns))
                               (a (take v (+ rho 1))) (b (drop v (+ rho 1))))
                          (list a b)))))
                 ((null? pts) (bk-fail! 'few-points))
                 (else
                  (let* ((xv (car pts))
                         (ud (bk-peval (cdr u) xv)) (gd (bk-peval (cdr g) xv)))
                    (if (or (= ud 0) (= gd 0))
                        (loop (cdr pts) rows us)
                        (let* ((uv (/ (bk-peval (car u) xv) ud))
                               (gv (/ (bk-peval (car g) xv) gd))
                               (pw (let pl ((i 0) (cur 1) (acc '()))
                                     (if (> i rho) (reverse acc) (pl (+ i 1) (* cur uv) (cons cur acc)))))
                               (row (append pw (map (lambda (v) (* -1 gv v)) pw))))
                          (loop (cdr pts) (cons row rows) (if (member? uv us) us (cons uv us))))))))))))))

; ---------- обратная подстановка ----------
; (^ B q) с B = rad(u) (u-форма) → r^q·x^(−E·q) при E·q целом; u → u(x)
; xs — x или |x| (вариант для x < 0: √(xᴱ·q(u)) = |x|^(E/2)·√q)
(define (bk-back e us ux rad r ee xs)
  (cond ((equal? e us) ux)
        ((not (pair? e)) e)
        ((and (equal? (car e) '^) (bk-rat? (nth e 2)) (not (integer? (nth e 2)))
              (equal? (expand (nth e 1)) rad)
              (integer? (* ee (nth e 2))))
         (list '* (list '^ r (nth e 2)) (list '^ xs (- (* ee (nth e 2))))))
        ((and (equal? (car e) 'sqrt) (= (length e) 2) (equal? (expand (nth e 1)) rad) (integer? (/ ee 2)))
         (list '* (list '^ r 1/2) (list '^ xs (- (/ ee 2)))))
        (else (cons (car e) (map (lambda (v) (bk-back v us ux rad r ee xs)) (cdr e))))))

; численная проверка самой F (центральная разность, int-F-point-verdict) в 8 точках обеих полуосей: ни одной «bad/gross», ≥ 5 «ok»
; (точки, где f не вещественна, дают skip)
(define bk-check-pts '(3/10 71/100 137/100 5/2 -3/10 -71/100 -7/5 -5/2))
(define (bk-numeric-ok? F f x)
  (let* ((ps (int-symbols (list '+ F f) x))
         (vals (map2 list ps (map (lambda (p) 1) ps)))
         (rs (map (lambda (p) (try (int-F-point-verdict F f x p vals) (lambda (e) 'skip))) bk-check-pts)))
    (and (null? (filter (lambda (r) (or (equal? r 'bad) (equal? r 'gross))) rs))
         (>= (length (filter (lambda (r) (equal? r 'ok)) rs)) 5))))

(define bk-trace #f)
(define bk-t0 0)
(define (bk-log tag v)
  (if bk-trace (begin (display tag) (display " ") (display (quotient (- (clock-us) bk-t0) 1000)) (display "ms ") (display v) (newline))))

(define (bk-try-sub f x rat r m j us ux rad-u ee info)
  ; ux — выражение u(x), rad-u — подкоренное в u (раскрытое), ee — показатель знаменателя: r = xᴱ·rad(u)
  (let* ((up (diff x ux))
         (g (together (list '* rat (list '^ x (/ (* ee j) m)) (list '^ up -1))))
         (uf (bk-ratf ux x))
         (gf (bk-ratf g x))
         (sol (begin (bk-log 'try info) (and (not (= (bk-deg (car gf)) -1)) (bk-solve-rational uf gf)))))
    (bk-log 'solved sol)
    (and sol
         (let* ((a (car sol)) (b (cadr sol))
                (ru (together (list '/ (bk-poly-expr a us) (bk-poly-expr b us))))
                (integrand (list '* ru (list '^ rad-u (/ j m))))
                (iu (try (int-blake-recurse integrand us) (lambda (e) #f))))
           (bk-log 'u-integral iu)
           (cond ((not iu) (bk-fail! 'u-integral-fails))
                 (else
                  (let* ((F0 (bk-back iu us ux (expand rad-u) r ee x))
                         (F (try (simplify F0) (lambda (e) F0))))
                    (bk-log 'back F)
                    (set! bk-info info)
                    (cond ((int-check F f x) F)
                          ; m = 2, E/2 нечётно: ответ x > 0 неверен при x < 0 (√(xᴱ q) = |x|^(E/2)·√q, F′ = −f при x < 0);
                          ; F̃ = (x/|x|)·F̂, F̂ — с |x| вместо x в обратной подстановке: верно на обеих полуосях
                          ((and (= m 2) (even? ee) (odd? (quotient ee 2)))
                           (let* ((G0 (list '* (list '* x (list '^ (list 'abs x) -1))
                                            (bk-back iu us ux (expand rad-u) r ee (list 'abs x))))
                                  (G (try (simplify G0) (lambda (e) G0))))
                             (bk-log 'signed G)
                             ; формальная производная от abs — sign (int-check не судит), поэтому численная проверка самого F
                             (if (bk-numeric-ok? G f x) G (bk-fail! 'check-fails))))
                          (else (bk-fail! 'check-fails))))))))))

(define (int-blake-recurse integrand us)
  (set! bk-depth (+ bk-depth 1))
  (let ((r (unwind-protect
             (let ((v (integrate integrand us)))
               (and v (not (equal? v 'unknown)) (not (int-has-integrate? v)) v))
             (set! bk-depth (- bk-depth 1)))))
    r))

; ---------- главная функция ----------
(define (bk-candidates r m nn x)
  ; список (вид параметры …)
  (let* ((rc (bk-coefs r x)) (h (quotient nn 2)))
    (append
     ; линейное: u = r/x^K, m | K, K ≤ N
     (let loop ((kk m) (acc '()))
       (if (> kk nn) (reverse acc) (loop (+ kk m) (cons (list 'lin kk) acc))))
     (if (and (= m 2) (even? nn))
         (append
          (let loop ((k 0) (acc '()))
            (if (>= k h) (reverse acc) (loop (+ k 1) (cons (list 'quad k) acc))))
          (list (list 'quad-rev)))
         '()))))

(define (bk-run-reduced f x g)
  (set! bk-why 'reduced-fails)
  (let ((iu (try (int-blake-recurse g x) (lambda (e) #f))))
    (and iu (let ((F (try (simplify iu) (lambda (e) iu))))
              (set! bk-info '(reduced))
              (if (int-check F f x) F (bk-fail! 'check-fails))))))

(define (bk-run f x)
  (let ((p (bk-parse f x)))
    (if (and p (equal? (car p) 'reduced))
        (bk-run-reduced f x (cadr p))
    (and p
         (let* ((rat (car p)) (r (cadr p)) (m (nth p 2)) (j (nth p 3)) (nn (nth p 4))
                (rc (bk-coefs r x)) (us 'bk-u)
                (cands (bk-candidates r m nn x)))
           (set! bk-why 'no-substitution)
           (let loop ((cs cands))
             (if (null? cs) #f
                 (let* ((c (car cs))
                        (res
                         (cond
                           ((equal? (car c) 'lin)
                            (let* ((kk (cadr c))
                                   (ux (together (list '* r (list '^ x (- kk))))))
                              (bk-try-sub f x rat r m j us ux us kk (list 'lin kk))))
                           ((equal? (car c) 'quad)
                            (let ((k (cadr c)))
                              (let sloop ((sets (bk-sq-sets rc k)))
                                (and (pair? sets)
                                     (or (let* ((s (car (car sets))) (a2 (cadr (car sets))) (a0 (nth (car sets) 2))
                                                (ux (together (list '* (bk-poly-expr s x) (list '^ x (- k)))))
                                                (rad (expand (list '+ (list '* a2 (list '^ us 2)) a0))))
                                           (bk-try-sub f x rat r m j us ux rad (* 2 k) (list 'quad k)))
                                         (sloop (cdr sets)))))))
                           (else
                            ; k = N/2: обращённый многочлен
                            (let* ((rev (reverse rc)) (sets (bk-sq-sets rev 0)))
                              (let sloop ((sets sets))
                                (and (pair? sets)
                                     (or (let* ((s (car (car sets))) (a2 (cadr (car sets))) (a0 (nth (car sets) 2))
                                                (ux (bk-poly-expr s (list '^ x -1)))
                                                (rad (expand (list '+ (list '* a2 (list '^ us 2)) a0))))
                                           (bk-try-sub f x rat r m j us (simplify ux) rad nn (list 'quad-rev)))
                                         (sloop (cdr sets))))))))))
                   (or res (loop (cdr cs)))))))))))

; (int-blake f x) → F (F′ = f, int-check) или #f; причина отказа — (int-blake-stats)
(define (int-blake f x)
  (set! bk-why #f) (set! bk-info '()) (set! bk-t0 (clock-us))
  (if (> bk-depth 0)
      (bk-fail! 'nested)
      (let ((r (call-with-time-limit int-blake-time-limit
                                     (lambda () (try (bk-run f x) (lambda (e) (bk-fail! 'error) #f))))))
        (cond ((and (pair? r) (equal? (car r) 'ok))
               (if (cadr r) (begin (set! bk-why #f) (cadr r)) #f))
              (else (bk-fail! 'timeout))))))

; дёшево: подынтегральное разбирается как R(x)·r(x)^(j/m) (без запуска поиска); внутри самого Блейка — нет
(define (bk-applicable? f x)
  (and (= bk-depth 0)
       (try (and (bk-parse f x) #t) (lambda (e) #f))))
