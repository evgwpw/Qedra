; INT.SFREAL: ответы integrate со спецфункциями записываются в вещественной форме там, где подынтегральное вещественно.
; ∫dx/ln x давал −Γ(0, −ln x) (ответ Rubi): при x > 1 это li(x) + iπ — производная верна, но первообразная комплексна.
; Таблица тождеств (lib/integrate/api.lisp, int-sf-rule) отбрасывает только постоянное слагаемое; принятие — int-check по f,
; вещественность и численная проверка самого ответа (int-check-F-status = 'ok).

(define (sfr-at e x p) (eval-num (subst (list (list x p)) e)))
(define (sfr-real? v) (and (number? v) (real-numeric? v)))

(deftest "sf-real/1: ∫1/ln x = li(x) — вещественно при x = 2 и x = 1/2"
  (let ((F (integrate '(/ 1 (log x)) 'x)))
    (assert-equal F '(li x))
    (assert-true (sfr-real? (sfr-at F 'x 2)))
    (assert-true (sfr-real? (sfr-at F 'x 1/2)))
    ; значения li: li(2) = 1,04516…, li(1/2) = −0,37867…
    (assert-true (< (abs (- (sfr-at F 'x 2) 1.0451637801174927)) 1e-9))
    (assert-true (< (abs (- (sfr-at F 'x 1/2) -0.37867104306108795)) 1e-9))))

(deftest "sf-real/2: ∫1/(x²·ln x), ∫x/ln x, ∫1/ln(2x), ∫x^a/ln x — li от подходящего аргумента"
  (let ((F1 (integrate '(/ 1 (* (^ x 2) (log x))) 'x))
        (F2 (integrate '(/ x (log x)) 'x))
        (F3 (integrate '(/ 1 (log (* 2 x))) 'x))
        (F4 (integrate '(/ (^ x a) (log x)) 'x)))
    (assert-equal F1 '(li (^ x -1)))
    (assert-equal F2 '(li (^ x 2)))
    (assert-true (sfr-real? (sfr-at F3 'x 2)))
    (assert-true (sfr-real? (sfr-at F3 'x 1/3)))
    (assert-true (int-check F3 '(/ 1 (log (* 2 x))) 'x))
    (assert-true (sfr-real? (sfr-at (subst '((a 3/2)) F4) 'x 2)))
    (assert-true (sfr-real? (sfr-at (subst '((a 3/2)) F4) 'x 1/2)))))

(deftest "sf-real/3: ∫sinh x / x — Ei вместо Γ(0, ±x), ответ вещественен при x > 0 и x < 0"
  (let ((F (integrate '(/ (sinh x) x) 'x)))
    (assert-true (int-check F '(/ (sinh x) x) 'x))
    (assert-true (not (contains-sym? F 'gamma)))
    (assert-true (sfr-real? (sfr-at F 'x 2)))
    (assert-true (sfr-real? (sfr-at F 'x -3/2)))))

(deftest "sf-real/3b: ∫sinh(a+bx)/(c+dx) — Γ(0, ±…) с мнимыми коэффициентами → Ei с вещественными, e → exp"
  (let* ((f '(/ (sinh (+ a (* b x))) (+ c (* d x))))
         (F (integrate f 'x))
         (pts '((a 17/10) (b 23/10) (c 19/10) (d 31/10))))
    (assert-true (int-check F f 'x))
    (assert-true (not (contains-sym? F 'gamma)))
    (assert-true (not (contains-sym? F '%i)))
    (assert-true (sfr-real? (eval-num (subst pts (subst '((x 3/10)) F)))))
    (assert-true (sfr-real? (eval-num (subst pts (subst '((x 3)) F)))))))

(deftest "sf-real/3c: Γ(−2, z) и Γ(−1, z) сводятся к Γ(0, z) рекуррентностью (DLMF 8.8.2) — значение не меняется"
  (let* ((F '(gamma -2 (* 3/2 x)))
         (G (integrate::int-sf-rewrite F 'x)))
    (assert-true (not (contains-sym? G 'gamma)))
    ; Ei вещественно: сравнение с Γ(−2, 3/2·x) при x = 1 (оба вещественны, мнимой части нет)
    (assert-true (< (abs (- (eval-num (subst '((x 1)) G)) (eval-num (subst '((x 1)) F)))) 1e-9))))

(deftest "sf-real/3d: ∫exp(a x²) — erf с мнимым аргументом (−a)^(1/2)·x → erfi(√a·x), eval-num считает ответ"
  (let* ((f '(exp (* a (^ x 2))))
         (F (integrate f 'x)))
    (assert-true (contains-sym? F 'erfi))
    (assert-true (not (contains-sym? F '%i)))
    (assert-true (int-check F f 'x))
    (assert-true (sfr-real? (eval-num (subst '((a 17/10)) (subst '((x 3/10)) F)))))
    (assert-true (sfr-real? (eval-num (subst '((a 17/10)) (subst '((x -2)) F)))))))

(deftest "sf-real/4: ∫e^x/x без параметров остаётся «неэлементарно» (переписывание его не трогает)"
  (let ((F (integrate '(/ (exp x) x) 'x)))
    (assert-true (contains-sym? F 'integrate))))

(deftest "sf-real/5: таблица тождеств — Γ(0, z) = −Ei(−z) (по модулю константы), Ei(ln u) = li(u), Ei(k ln u) = li(u^k)"
  (assert-equal (integrate::int-sf-rewrite '(* -1 (gamma 0 (* -1.0 (log x)))) 'x) '(li x))
  (assert-equal (integrate::int-sf-rewrite '(* -1 (gamma 0 (* -2.0 (log x)))) 'x) '(li (^ x 2)))
  (assert-equal (integrate::int-sf-rewrite '(Ei (* 3 (log x))) 'x) '(li (^ x 3)))
  (assert-equal (integrate::int-sf-rewrite '(exp_integral_ei (log x)) 'x) '(li x))
  ; erf(i·z) = i·erfi(z) — без отбрасывания
  (assert-equal (integrate::int-sf-rewrite '(erf (* %i x)) 'x) '(* %i (erfi x))))

(deftest "sf-real/6: подделка — ответ, чей перепис меняет не константу, не принимается"
  ; F = −Γ(0, −ln x) — первообразная 1/ln x. Для f = 1/(2 ln x) переписанный li(x) не проходит int-check: ответ как был
  (let* ((F '(* -1 (gamma 0 (* -1 (log x)))))
         (r (integrate::int-sf-real-final F '(/ 1 (* 2 (log x))) 'x)))
    (assert-equal r F))
  ; для верного f — принимается
  (let* ((F '(* -1 (gamma 0 (* -1 (log x)))))
         (r (integrate::int-sf-real-final F '(/ 1 (log x)) 'x)))
    (assert-equal r '(li x)))
  ; ответ без комплексных значений не трогается
  (let ((F '(erf x)))
    (assert-equal (integrate::int-sf-real-final F '(* 2 (^ pi -1/2) (exp (* -1 (^ x 2)))) 'x) F)))

(deftest "sf-real/7: выключатель int-sf-real-on — прежний комплексный ответ Rubi"
  (set! integrate::int-sf-real-on #f)
  (let ((F (unwind-protect (integrate '(/ 1 (log x)) 'x) (set! integrate::int-sf-real-on #t))))
    (assert-true (contains-sym? F 'gamma))))
