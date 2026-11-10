; variational.lisp — тесты шагов CV.1–CV.2: вариационное исчисление

(define vt-y '(y x))
(define vt-yp '(diff (y x) x))
(define vt-ypp '(diff (diff (y x) x) x))
(define (vt-lhs eq) (cadr eq))


; ---------- CV.1: уравнения Эйлера — Лагранжа ----------

(deftest "EL: L = y'^2 → y'' = 0"
  (assert-equal (euler-lagrange '(^ (diff (y x) x) 2) '(y x))
                (list '= vt-ypp 0)))

(deftest "EL: L = y'^2 - y^2 → y'' + y = 0"
  (assert-equal (euler-lagrange '(+ (^ (diff (y x) x) 2) (* -1 (^ (y x) 2))) '(y x))
                (list '= (simplify (list '+ vt-ypp vt-y)) 0)))

(deftest "EL: длина дуги sqrt(1+y'^2) → y'' = 0"
  (assert-equal (euler-lagrange '(sqrt (+ 1 (^ (diff (y x) x) 2))) '(y x))
                (list '= vt-ypp 0)))

(deftest "EL: катеноид/цепная линия y·sqrt(1+y'^2) → y·y'' = 1 + y'^2"
  (let ((eq (euler-lagrange '(* (y x) (sqrt (+ 1 (^ (diff (y x) x) 2)))) '(y x))))
    (assert-equal (simplify (vt-lhs eq))
                  (simplify (list '+ -1 (list '* -1 (list '^ vt-yp 2)) (list '* vt-y vt-ypp))))))

(deftest "EL: брахистохрона → 1 + y'^2 + 2 y y'' = 0"
  (let ((eq (euler-lagrange '(sqrt (/ (+ 1 (^ (diff (y x) x) 2)) (y x))) '(y x))))
    (assert-equal (simplify (vt-lhs eq))
                  (simplify (list '+ 1 (list '^ vt-yp 2) (list '* 2 vt-y vt-ypp))))))

(deftest "Эйлер — Пуассон: L = y''^2 → y'''' = 0"
  (assert-equal (euler-lagrange '(^ (diff (diff (y x) x) x) 2) '(y x))
                (list '= '(diff (diff (diff (diff (y x) x) x) x) x) 0)))

(deftest "Эйлер — Пуассон: L = y''^2 + y'^2 + y^2 (порядок 4)"
  (let ((eq (euler-lagrange '(+ (^ (diff (diff (y x) x) x) 2) (^ (diff (y x) x) 2) (^ (y x) 2)) '(y x))))
    ;; 2y'''' − 2y'' + 2y = 0, нормировано на старший коэффициент
    (assert-equal (simplify (vt-lhs eq))
                  (simplify (list '+ '(diff (diff (diff (diff (y x) x) x) x) x) (list '* -1 vt-ypp) vt-y)))))

(deftest "EL: система L = y'^2 + z'^2 + 2yz"
  (let ((r (euler-lagrange '(+ (^ (diff (y x) x) 2) (^ (diff (z x) x) 2) (* 2 (y x) (z x))) '((y x) (z x)))))
    (assert-equal (length r) 2)
    (assert-equal (car r) (list '= (simplify (list '+ vt-ypp (list '* -1 '(z x)))) 0))
    (assert-equal (cadr r) (list '= (simplify (list '+ '(diff (diff (z x) x) x) (list '* -1 vt-y))) 0))))

(deftest "Эйлер — Остроградский: L = u_x^2 + u_y^2 → уравнение Лапласа"
  (assert-equal (euler-lagrange '(+ (^ (diff (u x y) x) 2) (^ (diff (u x y) y) 2)) '(u x y))
                (list '= '(+ (diff (diff (u x y) x) x) (diff (diff (u x y) y) y)) 0)))

(deftest "Эйлер — Остроградский: колебания струны L = u_t^2 - c^2 u_x^2"
  (let ((eq (euler-lagrange '(+ (^ (diff (u x t) t) 2) (* -1 (^ c 2) (^ (diff (u x t) x) 2))) '(u x t))))
    (assert-equal (simplify (vt-lhs eq))
                  (simplify (list '+ '(diff (diff (u x t) t) t) (list '* (list '* -1 (list '^ 'c 2)) '(diff (diff (u x t) x) x)))))))

; ---------- первые интегралы ----------

(deftest "Бельтрами: L = y·sqrt(1+y'^2) → y^2/(1+y'^2) = C1"
  (assert-equal (var-first-integrals '(* (y x) (sqrt (+ 1 (^ (diff (y x) x) 2)))) '(y x))
                (list (list '= (simplify '(/ (^ (y x) 2) (+ 1 (^ (diff (y x) x) 2)))) 'C1))))

(deftest "Бельтрами: брахистохрона → y(1 + y'^2) = C1"
  (assert-equal (var-first-integrals '(sqrt (/ (+ 1 (^ (diff (y x) x) 2)) (y x))) '(y x))
                (list (list '= (simplify '(* (y x) (+ 1 (^ (diff (y x) x) 2)))) 'C1))))

(deftest "Нет x, нет y: L = y'^2 → энергия и импульс"
  (let ((r (var-first-integrals '(^ (diff (y x) x) 2) '(y x))))
    (assert-equal (length r) 2)
    (assert-equal (cadr (cadr r)) (simplify '(* 2 (diff (y x) x))))))

(deftest "Нет первых интегралов: L = y'^2 + x·y"
  (assert-true (null? (var-first-integrals '(+ (^ (diff (y x) x) 2) (* x (y x))) '(y x)))))

(deftest "L без y: ∂L/∂y' = C1 (импульс)"
  (assert-equal (cadr (car (var-first-integrals '(+ (^ (diff (y x) x) 2) (* x (diff (y x) x))) '(y x))))
                (simplify '(+ x (* 2 (diff (y x) x))))))

; ---------- граничные условия ----------

(deftest "Естественное условие свободного конца: ∂L/∂y' = 0"
  (assert-equal (var-natural-conditions '(+ (^ (diff (y x) x) 2) (^ (y x) 2)) '(y x))
                (list (list '= (simplify '(* 2 (diff (y x) x))) 0))))

(deftest "Естественные условия при L = y''^2: p1 = -2y''', p2 = 2y''"
  (assert-equal (var-natural-conditions '(^ (diff (diff (y x) x) x) 2) '(y x))
                (list (list '= (simplify '(* -2 (diff (diff (diff (y x) x) x) x))) 0)
                      (list '= (simplify '(* 2 (diff (diff (y x) x) x))) 0))))

(deftest "Трансверсальность для L = y'^2 и кривой φ = 3 − x: (−1−y')y'·2 + y'^2 = 0"
  (let ((r (var-transversality '(^ (diff (y x) x) 2) '(y x) '(+ 3 (* -1 x)))))
    ;; L + (φ' − y')·L_y' = y'^2 + (−1 − y')·2y' = −y'^2 − 2y'
    (assert-equal (simplify (expand (cadr r))) (simplify '(+ (* -2 (diff (y x) x)) (* -1 (^ (diff (y x) x) 2)))))))

(deftest "Нётер: сохраняющиеся величины"
  (assert-equal (var-noether '(+ (^ (diff (y x) x) 2) (* -1 (^ (y x) 2))) '(y x))
                (list (list 'x-translation (simplify '(+ (^ (diff (y x) x) 2) (^ (y x) 2))))))
  (assert-equal (var-noether '(^ (diff (y x) x) 2) '(y x))
                (list (list 'x-translation (simplify '(^ (diff (y x) x) 2)))
                      (list 'shift 'y (simplify '(* 2 (diff (y x) x)))))))

(deftest "Геодезические на сфере: интеграл Клеро sin^2(t) f' / sqrt(1 + sin^2(t) f'^2) = C1"
  (let ((r (var-first-integrals '(sqrt (+ 1 (* (^ (sin t) 2) (^ (diff (f t) t) 2)))) '(f t))))
    (assert-equal (length r) 1)
    (assert-equal (caddr (car r)) 'C1)))

; ---------- CV.2: задачник ----------

(define vt-L1 '(sqrt (+ 1 (^ (diff (y x) x) 2))))
(define vt-L2 '(+ (^ (diff (y x) x) 2) (^ (y x) 2)))
(define vt-L3 '(+ (^ (diff (y x) x) 2) (* -1 (^ (y x) 2))))
(define vt-fix01 '((= (y 0) 0) (= (y 1) 1)))
(define vt-Lc '(* (y x) (sqrt (+ 1 (^ (diff (y x) x) 2)))))
(define vt-catcs '((= (y -1) (cosh 1)) (= (y 1) (cosh 1))))
(define vt-Lb '(sqrt (/ (+ 1 (^ (diff (y x) x) 2)) (y x))))

(define (vt-rhs r) (caddr (var-field r :extremal)))
(define (vt-kind r) (var-field r :kind))
(define (vt-num e x0) (eval-num (subst (list 'x x0) e)))
(define (vt-close? a b) (< (abs (- a b)) 1e-9))

(deftest "Кратчайший путь (0,0)–(1,1): y = x, минимум (выпуклость)"
  (let ((r (variational-solve vt-L1 '(y x) 0 1 vt-fix01)))
    (assert-equal (var-status r) 'ok)
    (assert-equal (vt-rhs r) 'x)
    (assert-equal (vt-kind r) 'minimum)
    (assert-equal (var-field r :check) #t)))

(deftest "L = y'^2 + y^2, y(0)=0, y(1)=1: sinh x / sinh 1, минимум"
  (let ((r (variational-solve vt-L2 '(y x) 0 1 vt-fix01)))
    (assert-equal (var-status r) 'ok)
    (assert-equal (vt-kind r) 'minimum)
    (assert-equal (var-field r :check) #t)
    (assert-true (vt-close? (vt-num (vt-rhs r) 1/2)
                            (vt-num '(/ (+ (exp x) (* -1 (exp (* -1 x)))) (+ (exp 1) (* -1 (exp -1)))) 1/2)))))

(deftest "L = y'^2 - y^2 на [0, π/2]: Лежандр + Якоби → минимум"
  (let ((r (variational-solve vt-L3 '(y x) 0 (/ 'pi 2) '((= (y 0) 0) (= (y (/ pi 2)) 1)))))
    (assert-equal (vt-rhs r) '(sin x))
    (assert-equal (vt-kind r) 'minimum)
    (let ((cl (var-field r :classification)))
      (assert-equal (var-field cl :legendre) 'strict)
      (assert-equal (var-field cl :jacobi) 'none))))

(deftest "L = y'^2 - y^2 на [0, 2π]: сопряжённая точка π внутри — НЕ минимум"
  (let ((r (variational-solve vt-L3 '(y x) 0 (* 2 'pi) '((= (y 0) 0) (= (y (* 2 pi)) 0)))))
    (assert-equal (vt-kind r) 'extremal)
    (let* ((cl (var-field r :classification)) (j (var-field cl :jacobi)))
      (assert-equal (car j) 'conjugate)
      (assert-true (vt-close? (cadr j) 3.141592653589793)))
    (assert-equal (var-field (var-classify vt-L3 '(y x) 0 (* 2 'pi) '(sin x) #t) :kind) 'extremal)))

(deftest "Якоби и Лежандр отдельно"
  (assert-equal (var-jacobi vt-L3 '(y x) 0 (/ 'pi 2) '(= (y x) (sin x))) 'none)
  (assert-equal (car (var-jacobi vt-L3 '(y x) 0 (* 2 'pi) '(= (y x) (sin x)))) 'conjugate)
  (assert-equal (var-legendre vt-L3 '(y x) 0 1 '(= (y x) (sin x))) 'strict)
  (assert-equal (var-legendre '(* -1 (^ (diff (y x) x) 2)) '(y x) 0 1 'x) 'negative))

(deftest "Выпуклость: гессиан L по (y, y')"
  (assert-equal (var-convex? vt-L1 '(y x)) #t)
  (assert-equal (var-convex? vt-L2 '(y x)) #t)
  (assert-equal (var-convex? vt-L3 '(y x)) #f))

(deftest "Цепная линия: y = cosh x проходит сертификат; подделки — нет"
  (assert-true (var-check vt-Lc '(y x) -1 1 vt-catcs '(cosh x)))
  (assert-equal (var-check vt-Lc '(y x) -1 1 vt-catcs '(= (y x) (* 2 (cosh x)))) #f)
  (assert-equal (var-check vt-Lc '(y x) -1 1 vt-catcs '(+ 1 (^ x 2))) #f)
  (assert-equal (var-check vt-Lc '(y x) -1 1 '((= (y -1) 1) (= (y 1) 1)) '(cosh x)) #f))

(deftest "Цепная линия: общее решение dsolve не получено — честно не «ok»"
  (let ((r (variational-solve vt-Lc '(y x) -1 1 vt-catcs)))
    (assert-true (member? (var-status r) '(family unknown)))
    (assert-equal (vt-kind r) 'extremal)))

(deftest "Подделки: неверная экстремаль и неверные краевые условия не проходят"
  (assert-equal (var-check '(^ (diff (y x) x) 2) '(y x) 0 1 vt-fix01 '(^ x 2)) #f)
  (assert-equal (var-check '(^ (diff (y x) x) 2) '(y x) 0 1 vt-fix01 '(* 2 x)) #f)
  (assert-true (var-check '(^ (diff (y x) x) 2) '(y x) 0 1 vt-fix01 'x))
  (assert-equal (var-check '(^ (diff (y x) x) 2) '(y x) 0 1 '((= (y 0) 0) (= (y 1) 2)) 'x) #f))

(deftest "Свободный конец: L = y'^2 + 2y, y(0)=0, y'(1)=0 → y = x^2/2 − x"
  (let ((r (variational-solve '(+ (^ (diff (y x) x) 2) (* 2 (y x))) '(y x) 0 1 '((= (y 0) 0)))))
    (assert-equal (vt-rhs r) (simplify '(+ (* 1/2 (^ x 2)) (* -1 x))))
    (assert-equal (vt-kind r) 'minimum)
    ;; неверный конец: y = x (y'(1) = 1 ≠ 0) не проходит естественное условие
    (assert-equal (var-check '(+ (^ (diff (y x) x) 2) (* 2 (y x))) '(y x) 0 1 '((= (y 0) 0)) '(+ (* 1/2 (^ x 2)) x)) #f)))

(deftest "Эйлер — Пуассон: L = y''^2, y(0)=0, y(1)=1, свободные наклоны → y = x"
  (let ((r (variational-solve '(^ (diff (diff (y x) x) x) 2) '(y x) 0 1 vt-fix01)))
    (assert-equal (vt-rhs r) 'x)
    (assert-equal (vt-kind r) 'minimum)))

(deftest "Брахистохрона: интеграл Бельтрами y(1+y'^2) постоянен на циклоиде, на подделке — нет"
  (let ((F (car (var-first-integrals vt-Lb '(y x)))))
    (assert-true (car (var-check-first-integral F '(y x) '(* r (+ t (* -1 (sin t)))) '(* r (+ 1 (* -1 (cos t)))) 't)))
    (assert-equal (car (var-check-first-integral F '(y x) '(* r (+ t (* -1 (sin t)))) '(* r (+ 1 (cos t))) 't)) #f)
    (assert-equal (car (var-check-first-integral F '(y x) 't '(^ t 2) 't)) #f)))

(deftest "Изопериметрическая: min ∫y'^2 при ∫y = 1, y(0)=y(1)=0 → y = 6x(1−x), λ = −24"
  (let ((r (var-isoperimetric '(^ (diff (y x) x) 2) '(y x) '(y x) 0 1 '((= (y 0) 0) (= (y 1) 0)) 1)))
    (assert-equal (var-status r) 'ok)
    (assert-equal (vt-rhs r) (simplify '(+ (* 6 x) (* -6 (^ x 2)))))
    (assert-equal (var-field r :lam) -24)
    (assert-equal (var-field r :check) #t)))

(deftest "Дидона: полуокружность — сертификат; подделки (λ, радиус, длина) — нет"
  (let ((G '(sqrt (+ 1 (^ (diff (y x) x) 2)))) (cs '((= (y -1) 0) (= (y 1) 0))) (c '(sqrt (+ 1 (* -1 (^ x 2))))))
    (assert-true (var-isoperimetric-check '(y x) G '(y x) -1 1 cs 'pi c -1))
    (assert-equal (var-isoperimetric-check '(y x) G '(y x) -1 1 cs 'pi c 1) #f)
    (assert-equal (var-isoperimetric-check '(y x) G '(y x) -1 1 cs 'pi '(* 2 (sqrt (+ 1 (* -1 (^ x 2))))) -1) #f)
    (assert-equal (var-isoperimetric-check '(y x) G '(y x) -1 1 cs 3 c -1) #f)))

(deftest "Дидона: окружность x = R cos t, y = R sin t удовлетворяет интегралу Бельтрами при λ = −R"
  (let ((F (car (var-first-integrals '(+ (y x) (* -1 (sqrt (+ 1 (^ (diff (y x) x) 2))))) '(y x)))))
    ;; L + λG при λ = −1 → интеграл y − 1/sqrt(1 + y'^2) = C1 на окружности радиуса 1
    (assert-true (car (var-check-first-integral F '(y x) '(cos t) '(sin t) 't)))
    (assert-equal (car (var-check-first-integral F '(y x) '(cos t) '(* 2 (sin t)) 't)) #f)))

(deftest "Нётер на задаче: энергия постоянна на экстремали y = sin x для L = y'^2 − y^2"
  (let ((e (cadr (car (var-noether vt-L3 '(y x))))))
    (assert-equal (simplify (ode-subst e '(y x) '(sin x))) 1)))

