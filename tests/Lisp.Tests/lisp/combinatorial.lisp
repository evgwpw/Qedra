; Lisp-тесты комбинаторных голов, подшаг 21l.0: точные значения (F#, Simplify.combinatorValue),
; правила rules.lisp, производные ψ/Γ/H, численные значения (eval-num), разбор/печать.

; --- точные значения ---
(deftest "комб/бином: C(n,k) целые"
  (assert-equal (simplify '(binomial 10 3)) 120)
  (assert-equal (simplify '(binomial 0 0)) 1)
  (assert-equal (simplify '(binomial 7 0)) 1)
  (assert-equal (simplify '(binomial 7 7)) 1)
  (assert-equal (simplify '(binomial 5 7)) 0)
  (assert-equal (simplify '(binomial 5 -1)) 0)
  (assert-equal (simplify '(binomial 20 10)) 184756))

(deftest "комб/гамма: Γ(n) = (n−1)!"
  (assert-equal (simplify '(gamma 1)) 1)
  (assert-equal (simplify '(gamma 5)) 24)
  (assert-equal (simplify '(gamma 10)) 362880)
  ; полюс и прочее — символьно
  (assert-equal (simplify '(gamma 0)) '(gamma 0))
  (assert-equal (simplify '(gamma -2)) '(gamma -2))
  (assert-equal (simplify '(gamma x)) '(gamma x)))

(deftest "комб/похгаммер: rf/ff"
  (assert-equal (simplify '(rf 3 0)) 1)
  (assert-equal (simplify '(rf 3 1)) 3)
  (assert-equal (simplify '(rf 3 2)) 12)
  (assert-equal (simplify '(rf 1/2 2)) 3/4)
  (assert-equal (simplify '(ff 5 0)) 1)
  (assert-equal (simplify '(ff 5 1)) 5)
  (assert-equal (simplify '(ff 5 3)) 60)
  (assert-equal (simplify '(ff 1/2 2)) -1/4))

(deftest "комб/гармонические: H_n, H_{n,m}"
  (assert-equal (simplify '(harmonic 0)) 0)
  (assert-equal (simplify '(harmonic 1)) 1)
  (assert-equal (simplify '(harmonic 4)) 25/12)
  (assert-equal (simplify '(harmonic 4 2)) 205/144)
  (assert-equal (simplify '(harmonic 2 2)) 5/4))

(deftest "комб/бернулли: числа"
  (assert-equal (simplify '(bernoulli 0)) 1)
  (assert-equal (simplify '(bernoulli 1)) -1/2)
  (assert-equal (simplify '(bernoulli 2)) 1/6)
  (assert-equal (simplify '(bernoulli 3)) 0)
  (assert-equal (simplify '(bernoulli 4)) -1/30)
  (assert-equal (simplify '(bernoulli 6)) 1/42)
  (assert-equal (simplify '(bernoulli 8)) -1/30)
  (assert-equal (simplify '(bernoulli 10)) 5/66))

(deftest "комб/бернулли: многочлены"
  (assert-equal (simplify '(bernoulli 0 x)) 1)
  (assert-equal (simplify '(bernoulli 1 x)) (simplify '(+ x -1/2)))
  ; B_3(x) = x^3 − 3/2 x^2 + 1/2 x
  (assert-true (equal? (simplify (list '- (simplify '(bernoulli 3 x))
                                          (simplify '(- (^ x 3) (* 3/2 (^ x 2)) (* -1/2 x)))))
                       0))
  ; B_4(x) = x^4 − 2x^3 + x^2 − 1/30
  (assert-true (equal? (simplify (list '- (simplify '(bernoulli 4 x))
                                          (simplify '(- (^ x 4) (* 2 (^ x 3)) (* -1 (^ x 2)) 1/30))))
                       0)))

; --- правила упрощения ---
(deftest "комб/правила: Γ и факториал"
  ; Γ(n+1) → n! для целого n (символ с декларацией не нужен: n не число — правило не сработает без integer-valued?)
  ; Γ(x+1) → x·Γ(x) для символа
  (assert-equal (simplify '(gamma (+ x 1))) '(* x (gamma x)))
  ; C(n,0) = 1, C(n,n) = 1
  (assert-equal (simplify '(binomial n 0)) 1)
  (assert-equal (simplify '(binomial n n)) 1)
  ; rf(x,1) = x
  (assert-equal (simplify '(rf x 1)) 'x)
  (assert-equal (simplify '(ff x 1)) 'x))

(deftest "комб/правила: ψ(1/2)"
  (assert-true (equal? (simplify (list '- (simplify '(psi 1/2))
                                          (simplify '(+ (* -1 euler-gamma) (* -2 (log 2))))))
                       0)))

; --- производные ---
(deftest "комб/дифф: ψ, Γ, H, факториал"
  (assert-equal (diff 'x '(psi x)) '(psi x 1))
  (assert-equal (diff 'x '(psi x 2)) '(psi x 3))
  (assert-true (equal? (simplify (list '- (diff 'x '(gamma x)) '(* (gamma x) (psi x)))) 0))
  ; d/dx H(x) = ψ(x+1) + euler-gamma
  (assert-true (equal? (simplify (list '- (diff 'x '(harmonic x))
                                          '(+ (psi (+ x 1)) euler-gamma)))
                       0)))

; --- численные значения (eval-num) ---
(deftest "комб/числа: ψ, Γ, C float"
  ; ψ(1) = −γ ≈ −0.5772
  (assert-true (let ((v (eval-num '(psi 1.0)))) (and (number? v) (< (abs (- v -0.5772156649015329)) 1e-9))))
  ; ψ(2) = 1 − γ
  (assert-true (let ((v (eval-num '(psi 2.0)))) (and (number? v) (< (abs (- v 0.4227843350980613)) 1e-9))))
  ; Γ(1/2) = √π
  (assert-true (let ((v (eval-num '(gamma 0.5)))) (and (number? v) (< (abs (- v 1.7724538509055159)) 1e-9))))
  ; ψ_1(1) = π²/6
  (assert-true (let ((v (eval-num '(psi 1.0 1)))) (and (number? v) (< (abs (- v 1.6449340668482264)) 1e-9))))
  ; H_10 float
  (assert-true (let ((v (eval-num '(harmonic 10.0)))) (and (number? v) (< (abs (- v 7381/2520)) 1e-9)))))

; --- разбор/печать ---
(deftest "комб/печать: Γ, ψ, C"
  (assert-equal (math-print '(gamma x)) "Γ(x)")
  (assert-equal (math-print '(psi x)) "ψ(x)")
  (assert-equal (math-print '(psi x 1)) "ψ(x, 1)")
  (assert-equal (math-print '(binomial n k)) "C(n, k)")
  (assert-equal (math-print '(harmonic n)) "harmonic(n)")
  ; чтение C(n, k), Γ(x), ψ(x)
  (assert-equal (math-read "C(n, k)") '(binomial n k))
  (assert-equal (math-read "Γ(x)") '(gamma x))
  (assert-equal (math-read "ψ(x)") '(psi x)))

; --- язык ---
(deftest "комб/язык: вызовы в mathlang"
  (assert-equal (math-eval "C(10, 3)") 120)
  (assert-equal (math-eval "gamma(5) + harmonic(4)") 313/12)
  (assert-equal (math-eval "bernoulli(2)") 1/6)
  (assert-equal (math-eval "rf(3, 2)") 12)
  (assert-equal (math-eval "gamma(x+1)") '(* x (gamma x)))
  (assert-true (let ((v (math-eval "psi(2.0)"))) (and (number? v) (< (abs (- v 0.4227843350980613)) 1e-9)))))

(deftest "21l.0: C(n,k) при отрицательном n — обобщённый: C(−1,2) = 1, C(−2,3) = −4, C(−3,0) = 1"
  (assert-equal (simplify '(binomial -1 2)) 1)
  (assert-equal (simplify '(binomial -2 3)) -4)
  (assert-equal (simplify '(binomial -3 0)) 1))
