; INT.SF2: ответы через спецфункции для задач корпуса Rubi, которые integrate отдавал частичными/«неэлементарно».
; Классификация выборки sf-gap (research/intown/sf-gap.tsv): правило Rubi давало ПОЛНЫЙ ответ (Γ(a, z), Ei, erfi, Shi/Chi,
; ₂F₁), а каскад возвращал частичный ответ с невычисленным (integrate …) и Rubi после него не звал (int-rubi-complete,
; lib/integrate/api.lisp). Плюс численные значения и производные голов Rubi sin_integral/cos_integral/sinh_integral/
; cosh_integral и erf/erfi комплексного аргумента (SolveNum.fs, Differentiate.fs).

(define (sf2-re v) (cond ((number? v) v) ((and (pair? v) (equal? (car v) '+)) (cadr v)) (else 0)))
(define (sf2-im v) (cond ((number? v) 0)
                         ((and (pair? v) (equal? (car v) '+)) (let ((m (caddr v))) (if (pair? m) (cadr m) 0)))
                         ((and (pair? v) (equal? (car v) '*)) (cadr v))
                         (else 0)))
(define (sf2-near? a b tol) (and (number? a) (number? b) (< (abs (- a b)) tol)))

(deftest "sf2/1: Si, Shi, Chi — значения (Абрамовиц — Стиган 5.2) и головы Rubi sin_integral/…"
  (assert-true (sf2-near? (eval-num '(sin_integral 2.0)) 1.6054129768026948 1e-12))
  (assert-true (sf2-near? (eval-num '(sinh_integral 1.0)) 1.0572508753757286 1e-12))
  (assert-true (sf2-near? (eval-num '(sinh_integral -1.0)) -1.0572508753757286 1e-12))
  (assert-true (sf2-near? (eval-num '(cosh_integral 1.0)) 0.8378669409802082 1e-12))
  (assert-true (sf2-near? (eval-num '(Shi 3.0)) (eval-num '(sinh_integral 3.0)) 1e-14))
  (assert-true (sf2-near? (eval-num '(cos_integral 2.0)) (eval-num '(Ci 2.0)) 1e-14)))

(deftest "sf2/2: Chi отрицательного аргумента — главная ветвь Chi(−x) = Chi(x) + iπ (DLMF 6.4.?)"
  (let ((v (eval-num '(cosh_integral -1.0))))
    (assert-true (sf2-near? (sf2-re v) 0.8378669409802082 1e-12))
    (assert-true (sf2-near? (sf2-im v) 3.141592653589793 1e-12))))

(deftest "sf2/3: Shi/Si от мнимого аргумента — Shi(iz) = i·Si(z)"
  (let ((v (eval-num '(sinh_integral (* %i 1.0)))))
    (assert-true (sf2-near? (sf2-im v) 0.946083070367183 1e-12))
    (assert-true (sf2-near? (sf2-re v) 0 1e-12))))

(deftest "sf2/4: erf/erfi комплексного аргумента (DLMF 7.6.1; erfi z = −i·erf(iz))"
  (let ((e (eval-num '(erf (+ 1.0 (* %i 1.0)))))
        (ei (eval-num '(erfi (+ 1.0 (* %i 1.0))))))
    (assert-true (sf2-near? (sf2-re e) 1.3161512816979474 1e-12))
    (assert-true (sf2-near? (sf2-im e) 0.1904534692378347 1e-12))
    (assert-true (sf2-near? (sf2-re ei) 0.1904534692378347 1e-12))
    (assert-true (sf2-near? (sf2-im ei) 1.3161512816979474 1e-12))))

(deftest "sf2/5: производные голов Rubi sin_integral/cos_integral/sinh_integral/cosh_integral (int-check)"
  (assert-true (int-check '(sin_integral x) '(/ (sin x) x) 'x))
  (assert-true (int-check '(cos_integral (* 2 x)) '(/ (cos (* 2 x)) x) 'x))
  (assert-true (int-check '(sinh_integral x) '(/ (sinh x) x) 'x))
  (assert-true (int-check '(cosh_integral (* 3 x)) '(/ (cosh (* 3 x)) x) 'x)))

; частичный ответ каскада → полный ответ Rubi через спецфункцию; ответ проверен и численно (int-check-F-status = 'ok)
(define (sf2-full-ok f)
  (let ((F (integrate f 'x))
        (old integrate::*check-numeric-F*))
    (and (pair? F) (not (contains-sym? F 'integrate))
         (int-check F f 'x)
         (begin (set! integrate::*check-numeric-F* #t)
                (let ((st (unwind-protect (integrate::int-check-F-status F f 'x) (set! integrate::*check-numeric-F* old))))
                  (equal? st 'ok))))))

(deftest "sf2/6: ∫f^(a+bx²)·x⁶ — erfi (раньше частичный ответ с невычисленным ∫f^(a+bx²))"
  (let ((F (integrate (math-read "f**(a + b*x**2)*x**6") 'x)))
    (assert-true (not (contains-sym? F 'integrate)))
    (assert-true (contains-sym? F 'erfi))))

(deftest "sf2/7: ∫sinh²(a+bx)/(c+dx)² — Ei/Shi/Chi, полный проверенный ответ"
  (assert-true (sf2-full-ok (math-read "sinh(a + b*x)**2/(c + d*x)**2"))))

(deftest "sf2/8: ∫f^(a+bx+cx²)/(b+2cx)³ — Ei вместо частичного ответа"
  (assert-true (sf2-full-ok (math-read "f**(a + b*x + c*x**2)/(b + 2*c*x)**3"))))

(deftest "sf2/10: ∫sin x/x = Si(x), ∫sin 2x/x = Si(2x) — головы Rubi sin_integral в ответе переименованы"
  (assert-equal (integrate '(/ (sin x) x) 'x) '(Si x))
  (assert-equal (integrate '(/ (sin (* 2 x)) x) 'x) '(Si (* 2 x))))

(deftest "sf2/9: int-rubi-complete выключаем — прежний частичный ответ с (integrate …)"
  (let ((old integrate::int-rubi-complete-on))
    (set! integrate::int-rubi-complete-on #f)
    (let ((F (unwind-protect (integrate (math-read "f**(a + b*x**2)*x**6") 'x)
               (set! integrate::int-rubi-complete-on old))))
      (assert-true (contains-sym? F 'integrate)))))
