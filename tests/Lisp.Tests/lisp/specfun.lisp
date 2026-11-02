; specfun.lisp — тесты шага SFn.1: Γ, B, ψ, ₚFq, hyperexpand, тождества, сертификаты

(deftest "Γ: целые и полуцелые значения"
  (assert-equal (sf-gamma 5) 24)
  (assert-equal (sf-gamma 1/2) '(^ pi 1/2))
  (assert-equal (sf-gamma 7/2) '(* 15/8 (^ pi 1/2)))
  (assert-equal (sf-gamma -1/2) '(* -2 (^ pi 1/2))))

(deftest "Γ: полюсы в целых ≤ 0"
  (assert-equal (sf-gamma 0) '(complex-infinity))
  (assert-equal (sf-gamma -3) '(complex-infinity))
  (assert-equal (specfun-simplify '(^ (gamma -2) -1)) 0))

(deftest "B: точные значения"
  (assert-equal (sf-beta 1/2 1/2) 'pi)
  (assert-equal (sf-beta 2 3) 1/12)
  (assert-equal (specfun-simplify '(beta 2 3)) 1/12)
  (assert-equal (sf-beta 'a 1) '(^ a -1))
  (assert-equal (sf-beta 0 2) '(complex-infinity)))

(deftest "Γ: рекуррентность Γ(z+3)/Γ(z+1)"
  (assert-equal (specfun-simplify '(/ (gamma (+ z 3)) (gamma (+ z 1)))) '(* (+ 1 z) (+ 2 z)))
  (assert-equal (specfun-simplify '(/ (gamma (+ z 2)) (gamma z))) '(* z (+ 1 z))))

(deftest "Γ: отражение Γ(1/3)Γ(2/3) = 2π/√3 и условие для символа"
  (assert-equal (specfun-simplify '(* (gamma 1/3) (gamma 2/3))) '(* 2/3 (^ 3 1/2) pi))
  (let ((r (capture-conditions (lambda () (specfun-simplify '(* (gamma z) (gamma (+ 1 (* -1 z)))))))))
    (assert-equal (car r) '(* pi (^ (sin (* pi z)) -1)))
    (assert-true (not (null? (cadr r))))))

(deftest "Γ: удвоение Лежандра"
  (assert-true (true? (specfun-check '(gamma (* 2 z)) (specfun-duplication '(gamma (* 2 z))) 'z)))
  (assert-equal (specfun-duplication-collapse '(* (gamma z) (gamma (+ z 1/2))))
                '(* (^ 2 (+ 1 (* -2 z))) (^ pi 1/2) (gamma (* 2 z))))
  (assert-true (true? (specfun-check '(* (gamma z) (gamma (+ z 1/2)))
                                     '(* (^ 2 (+ 1 (* -2 z))) (^ pi 1/2) (gamma (* 2 z))) 'z))))

(deftest "ψ: значения и сдвиг"
  (assert-equal (sf-digamma 1) '(* -1 euler-gamma))
  (assert-equal (sf-digamma 3) '(+ 3/2 (* -1 euler-gamma)))
  (assert-equal (sf-digamma 1/2) '(+ (* -1 euler-gamma) (* -2 (log 2))))
  (assert-equal (sf-digamma 0) '(complex-infinity))
  (assert-equal (sf-digamma '(+ z 1)) '(+ (^ z -1) (psi z)))
  (assert-equal (diff 'z '(gamma z)) '(* (gamma z) (psi z))))

(deftest "hyper: члены, сумма, редукции"
  (assert-equal (hyper-series '(hyper (1 1) (2) z) 3) '(+ 1 (* 1/2 z) (* 1/3 (^ z 2)) (* 1/4 (^ z 3))))
  (assert-equal (hyper-reduce '(hyper (a 0) (c) z)) 1)
  (assert-equal (hyper-reduce '(hyper (a b) (b) z)) '(hyper (a) () z))
  (assert-equal (hyper-reduce '(hyper (1 2) (3) 0)) 1)
  (assert-equal (hyper-term '(hyper (1 1) (2) z) 2) '(* 1/3 (^ z 2))))

(deftest "hyperexpand: ₀F₀, ₁F₀, ₂F₁(1,1;2)"
  (assert-equal (hyperexpand '(hyper () () z)) '(exp z))
  (assert-equal (hyperexpand '(hyper (a) () z)) '(^ (+ 1 (* -1 z)) (* -1 a)))
  (assert-equal (hyperexpand '(hyper (1 1) (2) z)) '(* -1 (^ z -1) (log (+ 1 (* -1 z))))))

(deftest "hyperexpand: atanh, asin, ₂F₁(a,b;b;z)"
  (assert-equal (hyperexpand '(hyper (1/2 1) (3/2) (^ z 2))) '(* (^ z -1) (atanh z)))
  (assert-equal (hyperexpand '(hyper (1/2 1/2) (3/2) (^ z 2))) '(* (^ z -1) (asin z)))
  (assert-equal (hyperexpand '(hyper (a b) (b) z)) '(^ (+ 1 (* -1 z)) (* -1 a))))

(deftest "hyperexpand: ₀F₁ — cos и sin"
  (assert-equal (hyperexpand '(hyper () (1/2) (* -1/4 (^ z 2)))) '(cos z))
  (assert-equal (hyperexpand '(hyper () (3/2) (* -1/4 (^ z 2)))) '(* (^ z -1) (sin z)))
  (assert-equal (hyperexpand '(hyper () (1/2) (* 1/4 (^ z 2)))) '(cosh z)))

(deftest "hyperexpand: Каммер ₁F₁ — erf"
  (assert-equal (hyperexpand '(hyper (1/2) (3/2) (* -1 (^ z 2)))) '(* 1/2 (^ pi 1/2) (^ z -1) (erf z)))
  (assert-equal (hyperexpand '(hyper (1) (2) z)) '(* (^ z -1) (+ -1 (exp z)))))

(deftest "hyperexpand: суммы Гаусса и Чу—Вандермонда"
  (assert-equal (hyperexpand '(hyper (1/2 1/2) (2) 1)) '(* 4 (^ pi -1)))
  (assert-equal (hyperexpand '(hyper (-3 2) (5) 1)) 2/7)
  ; условие Re(c−a−b) > 0: при c = a + b ряд расходится — формулы нет, условие записано
  (let ((r (capture-conditions (lambda () (hyperexpand '(hyper (1/2 1/2) (1) 1))))))
    (assert-equal (car r) '(hyper (1/2 1/2) (1) 1))
    (assert-true (not (null? (cadr r)))))
  ; символьные параметры: условие в канале
  (let ((r (capture-conditions (lambda () (hyperexpand '(hyper (a b) (c) 1))))))
    (assert-true (not (null? (cadr r))))))

(deftest "hyperexpand: оборванный ряд ₂F₁(−3,b;c;z) — кубический многочлен"
  (let ((p (hyperexpand '(hyper (-3 2) (5) z))))
    (assert-equal (degree p 'z) 3)
    (assert-equal (subst '(z 1) p) 2/7))
  (let ((p (hyperexpand '(hyper (-3 b) (c) z))))
    (assert-true (not (contains-sym? p 'hyper)))
    (assert-true (true? (specfun-check '(hyper (-3 b) (c) z) p '(b c z))))))

(deftest "hyperexpand: полуцелые семейства и ₂F₁(1,1;3/2)"
  (assert-equal (hyperexpand '(hyper (1 1) (3/2) (^ z 2))) '(* (^ z -1) (^ (+ 1 (* -1 (^ z 2))) -1/2) (asin z)))
  (assert-equal (hyperexpand '(hyper (a (+ a 1/2)) (1/2) (^ z 2)))
                '(* 1/2 (+ (^ (+ 1 z) (* -2 a)) (^ (+ 1 (* -1 z)) (* -2 a))))))

(deftest "hyperexpand: нет формулы — гипергеометрическая функция остаётся"
  (assert-equal (hyperexpand '(hyper (1 1 1) (2) z)) '(hyper (1 1 1) (2) z)))

(deftest "hyper-diff"
  (assert-equal (hyper-diff '(hyper (1 1) (2) z)) '(* 1/2 (hyper (2 2) (3) z))))

(deftest "numeric: сходимость и сравнение с замкнутой формой"
  (assert-true (< (abs (- (hyper-eval '(hyper (1 1) (2) 1/2)) (* 2 0.6931471805599453))) 1e-12))
  (assert-true (< (abs (- (hyper-eval '(hyper (1/2 1/2) (2) 1)) 1.2732395447351628)) 1e-12))
  (assert-true (not (hyper-eval '(hyper (1 1) (2) 3/2))))
  (assert-true (not (hyper-eval '(hyper (1) (0) 1/2)))))

(deftest "сертификат: таблица hyperexpand сверена с рядом (numeric)"
  (assert-equal (specfun-check-numeric '(hyper (1 1) (2) z) '(* -1 (^ z -1) (log (+ 1 (* -1 z)))) 'z) 'numeric)
  (assert-equal (specfun-check-numeric '(hyper (1/2 1) (3/2) (^ z 2)) '(* (^ z -1) (atanh z)) 'z) 'numeric)
  (assert-equal (specfun-check-numeric '(hyper (1/2 1/2) (3/2) (^ z 2)) '(* (^ z -1) (asin z)) 'z) 'numeric)
  (assert-equal (specfun-check-numeric '(hyper () (1/2) (* -1/4 (^ z 2))) '(cos z) 'z) 'numeric)
  (assert-equal (specfun-check-numeric '(hyper (1/2) (3/2) (* -1 (^ z 2))) '(* 1/2 (^ pi 1/2) (^ z -1) (erf z)) 'z) 'numeric)
  (assert-equal (specfun-check-numeric '(hyper (a (+ a 1/2)) (3/2) (^ z 2)) (hyperexpand '(hyper (a (+ a 1/2)) (3/2) (^ z 2))) '(a z)) 'numeric)
  (assert-equal (specfun-check-numeric '(hyper (1 1) (3/2) (^ z 2)) (hyperexpand '(hyper (1 1) (3/2) (^ z 2))) 'z) 'numeric))

(deftest "сертификат: точное совпадение и подделки"
  (assert-equal (specfun-check '(gamma 5) 24 '()) #t)
  (assert-equal (specfun-check '(hyper (1/2 1/2) (2) 1) '(/ 4 pi) '()) #t)
  (assert-equal (specfun-check '(/ (gamma (+ z 3)) (gamma (+ z 1))) '(* (+ z 1) (+ z 2)) 'z) #t)
  (assert-equal (specfun-check '(beta a b) '(/ (* (gamma a) (gamma b)) (gamma (+ a b))) '(a b)) 'numeric))

(deftest "сертификат: Γ(n+1/2) = (2n)!√π/(4^n n!) — числа, подделки отвергаются"
  (assert-equal (specfun-check-numeric '(gamma (+ n 1/2)) '(/ (* (factorial (* 2 n)) (^ pi 1/2)) (* (^ 4 n) (factorial n))) 'n) 'numeric)
  (assert-equal (specfun-check-numeric '(gamma (+ n 1/2)) '(/ (* (factorial (* 2 n)) (^ pi 1/2)) (* (^ 2 n) (factorial n))) 'n) #f)
  (assert-equal (specfun-check '(gamma 7/2) '(* 5/8 (^ pi 1/2)) '()) #f))

(deftest "сертификат: ложная сумма Гаусса и ложный знак"
  (assert-equal (specfun-check '(hyper (1/2 1/2) (2) 1) '(/ 2 pi) '()) #f)
  (assert-equal (specfun-check '(hyper (1/2 1/2) (2) 1) '(/ 4 (^ pi 2)) '()) #f)
  (assert-equal (specfun-check '(hyper (1 1) (2) z) '(* (^ z -1) (log (+ 1 (* -1 z)))) 'z) #f)
  (assert-equal (specfun-check '(hyper (1 1) (2) z) '(* -1 (^ z -1) (log (+ 1 (* -1 z)))) 'z) #t))
