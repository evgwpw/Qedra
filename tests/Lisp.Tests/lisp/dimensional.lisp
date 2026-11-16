; INT.OWN.B9: int-dimensional (lib/integrate/dimensional.lisp) — определённые интегралы с параметрами:
; веса из однородности, константа C — квадратура при параметрах = 1 + PSLQ, ответ — после сверки при двух других наборах параметров.

(deftest "dimensional: ∫₀^∞ x²·e^(−a x²) = ¼·√π·a^(−3/2) — вес −3/2 из баланса, C = ¼√π по PSLQ"
  (assert-equal (int-dimensional '(* (^ x 2) (exp (* -1 a (^ x 2)))) 'x 0 'inf)
                '(* 1/4 (^ a -3/2) (^ pi 1/2))))

(deftest "dimensional: ∫₀^∞ dx/(x²+a²) = π/(2a), параметр положителен — условие в канале"
  (conditions-clear)
  (assert-equal (int-dimensional '(/ 1 (+ (^ x 2) (^ a 2))) 'x 0 'inf) '(* 1/2 (^ a -1) pi))
  (assert-true (any? (lambda (c) (equal? (car c) '(> a 0))) (conditions))))

(deftest "dimensional: предел — параметр: ∫₀^a √(a²−x²) dx = π a²/4"
  (assert-equal (int-dimensional '(^ (+ (^ a 2) (* -1 (^ x 2))) 1/2) 'x 0 'a) '(* 1/4 (^ a 2) pi)))

(deftest "dimensional: два параметра с одной группой весов — ∫₀^∞ dx/(a+b x²) = π/(2√(ab))"
  (assert-equal (int-dimensional '(/ 1 (+ a (* b (^ x 2)))) 'x 0 'inf) '(* 1/2 (^ a -1/2) (^ b -1/2) pi)))

(deftest "dimensional: ζ(3) и Γ(1/4) опознаются — ∫₀^∞ x²/(e^(ax)−1) и ∫₀^∞ e^(−a x⁴)"
  (assert-equal (int-dimensional '(* (^ x 2) (^ (+ -1 (exp (* a x))) -1)) 'x 0 'inf) '(* 2 (^ a -3) (zeta 3)))
  (assert-equal (int-dimensional '(exp (* -1 a (^ x 4))) 'x 0 'inf) '(* 1/4 (^ a -1/4) (gamma 1/4))))

(deftest "dimensional: две безразмерные группы — отказ «не этим методом» (∫₀^∞ sin(ax)e^(−bx) dx)"
  (assert-true (not (int-dimensional '(* (sin (* a x)) (exp (* -1 b x))) 'x 0 'inf)))
  (assert-equal (car (int-dimensional-info)) 'groups))

(deftest "dimensional: неоднородный log x — отказ (∫₀^∞ log x/(x²+a²) = π log a/(2a) — не одночлен)"
  (assert-true (not (int-dimensional '(/ (log x) (+ (^ x 2) (^ a 2))) 'x 0 'inf)))
  (assert-equal (car (int-dimensional-info)) 'groups))

(deftest "dimensional: подделка — навязанный неверный вес отвергается проверкой при других наборах параметров"
  (assert-true (not (int-dimensional-with '(exp (* -1 a (^ x 2))) 'x 0 'inf '(a) '(-1))))
  (assert-equal (car (int-dimensional-info)) 'verify-weight)
  (assert-equal (int-dimensional-with '(exp (* -1 a (^ x 2))) 'x 0 'inf '(a) '(-1/2)) '(* 1/2 (^ a -1/2) (^ pi 1/2))))

(deftest "dimensional: колебательный хвост (sin(ax)/x) — нет сходимости квадратуры, отказ, не догадка"
  (assert-true (not (int-dimensional '(/ (sin (* a x)) x) 'x 0 'inf)))
  (assert-equal (car (int-dimensional-info)) 'quad))

(deftest "dimensional: показатель-параметр x^s — не этим методом (нет весовой формы)"
  (assert-true (not (int-dimensional '(* (^ x s) (exp (* -1 x))) 'x 0 'inf)))
  (assert-equal (car (int-dimensional-info)) 'weights))
