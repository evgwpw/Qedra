; RUBI.CH8: глава 8 Rubi (специальные функции). Классификация 538 отказов пилота d025808 (research/rubi/ch8-notok.tsv)
; нашла не «условия», а поломки переноса: правые части звали голые polylog/zeta/erf (нет в диалекте — error),
; образцы 2.x/8.x были записаны именами исходника Rubi (ProductLog, Erfc, FresnelS…), а вход и ответы — головами диалекта
; (LambertW/lambert_w, erfc, Si, Ei…): правила на них не срабатывали; IntHide возвращала подынтегральное вместо интеграла;
; Dist звали с тремя аргументами; ExpIntegralE[n, z] — с одним; правило 9.3 #62 звало несуществующее not-equal?;
; у lambert_w, ζ(s, a), poly_gamma не было численного значения (ответ нельзя проверить — отказ int-check).

(define (ch8-near? a b tol)
  (and (number? a) (number? b) (<= (abs (- a b)) (* tol (+ 1 (abs b))))))
(define (ch8-at e pairs) (eval-num (foldl (lambda (acc p) (replace-expr acc (car p) (cadr p))) e pairs)))

; ответ r (первообразная) подходит к подынтегральному f в точке x0 при значениях параметров ps: F'(x0) ≈ f(x0) разностью
(define (ch8-antiderivative? f r x0 ps)
  (let* ((h 1e-5)
         (fp (ch8-at r (cons (list 'x (+ x0 h)) ps)))
         (fm (ch8-at r (cons (list 'x (- x0 h)) ps)))
         (fx (ch8-at f (cons (list 'x x0) ps))))
    (and (number? fp) (number? fm) (number? fx)
         (ch8-near? (/ (- fp fm) (* 2 h)) fx 1e-6))))

; бюджет движка повышен: загрузка правил входит в бюджет первого вызова, под нагрузкой тест иначе «пограничный по времени»
(define (ch8-integrate s)
  (let ((old rubi::rubi-time-limit))
    (unwind-protect
      (begin (set! rubi::rubi-time-limit 60.0)
             (rubi-integrate (math-read s) 'x))
      (set! rubi::rubi-time-limit old))))

(deftest "rubi-ch8/1: eval-num — W₀ Ламберта, ζ(s, a) Гурвица, poly_gamma(n, z)"
  (assert-true (ch8-near? (eval-num '(lambert_w 1.0)) 0.5671432904097838 1e-14))
  (assert-true (ch8-near? (eval-num '(lambert_w -0.2)) -0.25917110181907377 1e-14))
  (assert-true (ch8-near? (eval-num '(lambert_w 100.0)) 3.385630140290050 1e-13))
  (assert-true (ch8-near? (eval-num '(zeta 2 1.0)) 1.6449340668482264 1e-13))
  (assert-true (ch8-near? (eval-num '(zeta 0.5 1.0)) -1.4603545088095868 1e-12))
  (assert-true (ch8-near? (eval-num '(zeta 3 0.5)) 8.414394 1e-6))
  (assert-true (ch8-near? (eval-num '(poly_gamma 1 1.0)) 1.6449340668482264 1e-11)))

(deftest "rubi-ch8/2: производные ζ(s, u) и poly_gamma — численно"
  (let* ((e '(zeta 2.5 (+ 1.2 t))) (d (diff 't e)) (h 1e-6))
    (assert-true (ch8-near? (eval-num (replace-expr d 't 0.7))
                            (/ (- (eval-num (replace-expr e 't (+ 0.7 h))) (eval-num (replace-expr e 't (- 0.7 h)))) (* 2 h)) 1e-7)))
  (let* ((e '(poly_gamma 1 (+ 1.2 t))) (d (diff 't e)) (h 1e-6))
    (assert-true (ch8-near? (eval-num (replace-expr d 't 0.7))
                            (/ (- (eval-num (replace-expr e 't (+ 0.7 h))) (eval-num (replace-expr e 't (- 0.7 h)))) (* 2 h)) 1e-6))))

(deftest "rubi-ch8/3: IntHide[u, x] = Int[u, x] (IUF.m:16) — правило 3.3 #26; Dist с тремя аргументами"
  ; раньше IntHide возвращала подынтегральное, ответ правила 3.3 #26 отвергала проверка (в списке «bad» 13 задач)
  (let ((r (ch8-integrate "x*polylog(2, c*(a + b*x))")))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (ch8-antiderivative? '(* x (polylog 2 (* c (+ a (* b x))))) r 0.3 '((a 1.5) (b 2.0) (c 0.1)))))
  (assert-equal (expand '(* a (+ b c))) (rubi::rubi-dist 'a '(+ b c) 'x)))

(deftest "rubi-ch8/4: правая часть с erf — раньше «Неизвестный символ: erf»"
  (let ((r (ch8-integrate "erf(x)")))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (ch8-antiderivative? '(erf x) r 0.7 '()))))

(deftest "rubi-ch8/5: правила 8.8 (polylog) — раньше «Неизвестный символ: polylog»"
  (let ((r (ch8-integrate "x**4*polylog(2, a*x)")))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (ch8-antiderivative? '(* (^ x 4) (polylog 2 (* a x))) r 0.4 '((a 0.5)))))
  (let ((r (ch8-integrate "x**2*polylog(3, a*x**2)")))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (ch8-antiderivative? '(* (^ x 2) (polylog 3 (* a (^ x 2)))) r 0.4 '((a 0.5))))))

(deftest "rubi-ch8/6: правила 8.9 на вход LambertW (имя sympy) — образцы ProductLog, голова lambert_w"
  (let ((r (ch8-integrate "LambertW(a*x)**2/x**4")))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (ch8-antiderivative? '(* (^ (lambert_w (* a x)) 2) (^ x -4)) r 0.6 '((a 1.5))))))

; не решено (остаток главы 8, ответ не должен быть ложным): ζ Гурвица со степенью x — отказ, а не неверный ответ
(deftest "rubi-ch8/7: ζ Гурвица x²·ζ(s, a+bx) — отказ или верный ответ"
  (let ((r (ch8-integrate "x**2*zeta(s, a + b*x)")))
    (assert-true (or (equal? r 'unknown)
                     (ch8-antiderivative? '(* (^ x 2) (zeta 2.5 (+ 1.2 (* 0.7 x)))) (subst (list (list 's 2.5) (list 'a 1.2) (list 'b 0.7)) r) 0.5 '())))))
