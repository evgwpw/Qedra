; Lisp-тесты trigsimp и финальной нормализации ответов integrate, шаг N1.
; Форма: значения не меняются (проверяются int-check), ответы — короче и привычнее.

; --- trigsimp: свёртка четвёртых степеней ---
(deftest "trigsimp/N1: разность четвёртых степеней через разность квадратов"
  (assert-equal (trigsimp '(- (^ (sin x) 4) (^ (cos x) 4)))
                '(+ (* -1 (^ (cos x) 2)) (^ (sin x) 2)))
  (assert-equal (trigsimp '(- (^ (cos x) 4) (^ (sin x) 4)))
                '(+ (^ (cos x) 2) (* -1 (^ (sin x) 2)))))

(deftest "trigsimp/N1: сумма произведений — вынос общего квадрата (пифагор)"
  ; sin²x·cos²x + cos⁴x = cos²x
  (assert-equal (trigsimp '(+ (* (^ (sin x) 2) (^ (cos x) 2)) (^ (cos x) 4)))
                '(^ (cos x) 2))
  ; sin²x·cos²x + sin⁴x = sin²x
  (assert-equal (trigsimp '(+ (* (^ (sin x) 2) (^ (cos x) 2)) (^ (sin x) 4)))
                '(^ (sin x) 2)))

(deftest "trigsimp/N1: уже простое выражение не меняется"
  (assert-equal (trigsimp '(+ (^ (sin x) 2) (^ (cos x) 2))) 1)
  (assert-equal (trigsimp '(- 1 (^ (cos x) 2))) '(^ (sin x) 2))
  (assert-equal (trigsimp 'x) 'x)
  (assert-equal (trigsimp '(+ x 1)) '(+ 1 x)))

(deftest "trigsimp/N1: без тригонометрии — только сбор подобных через expand"
  ; (x+1)² короче раскрытого
  (assert-equal (trigsimp '(^ (+ x 1) 2)) '(^ (+ 1 x) 2)))

(deftest "trigsimp/N1: старый пример integrate(x·sin²x) сворачивается в развёрнутую сумму"
  ; до N1: -1/4*x^2 + x(1/2*x - 1/2*cos(x)*sin(x)) + 1/4*sin(x)^2 — не раскрыто/не собрано
  (assert-equal (trigsimp '(+ (* -1/4 (^ x 2)) (* x (+ (* 1/2 x) (* -1/2 (cos x) (sin x)))) (* 1/4 (^ (sin x) 2))))
                '(+ (* 1/4 (^ x 2)) (* -1/2 x (cos x) (sin x)) (* 1/4 (^ (sin x) 2)))))

(deftest "trigsimp/N1: cos⁴x из integrate раскрыт и собран"
  ; до N1: 1/4*cos(x)^3*sin(x) + 3/4(1/2*x + 1/2*cos(x)*sin(x))
  (assert-equal (trigsimp '(+ (* 1/4 (^ (cos x) 3) (sin x)) (* 3/4 (+ (* 1/2 x) (* 1/2 (cos x) (sin x))))))
                '(+ (* 3/8 x) (* 3/8 (cos x) (sin x)) (* 1/4 (^ (cos x) 3) (sin x)))))

; --- половинные углы: только внутри log/atan ---
(deftest "trigsimp/N1: половинные углы сворачиваются только в log/atan"
  (assert-equal (trigsimp-half-angle '(log (* (+ 1 (* -1 (cos x))) (^ (sin x) -1))))
                '(log (tan (* 1/2 x))))
  ; (1+cos u)/sin u → cot(u/2); хвостовой множитель сохраняется
  (assert-equal (trigsimp-half-angle '(atan (* (^ 3 1/2) (+ 1 (cos x)) (^ (sin x) -1))))
                '(atan (* (cot (* 1/2 x)) (^ 3 1/2))))
  ; вне log/atan — не трогаем
  (assert-equal (trigsimp-half-angle '(* (+ 1 (* -1 (cos x))) (^ (sin x) -1)))
                '(* (+ 1 (* -1 (cos x))) (^ (sin x) -1))))

; --- финальная доводка integrate ---
(deftest "integrate/N1: развёрнутая и собранная форма (по частям)"
  ; 1/2(−cos·eˣ + eˣ·sin) раскрыто — короче
  (assert-equal (integrate '(* (exp x) (sin x)) 'x)
                '(+ (* -1/2 (cos x) (exp x)) (* 1/2 (exp x) (sin x)))))

(deftest "integrate/N1: csc x — половинный угол в log"
  (assert-equal (integrate '(/ 1 (sin x)) 'x) '(log (tan (* 1/2 x)))))

(deftest "integrate/N1: 1/(2+cos x) — половинный угол в atan, множитель сохранён"
  (assert-equal (integrate '(/ 1 (+ 2 (cos x))) 'x)
                '(* -2/3 (^ 3 1/2) (atan (* (cot (* 1/2 x)) (^ 3 1/2))))))

(deftest "integrate/N1: старые формы без улучшения не меняются"
  ; x·eˣ и по частям без тригонометрии — как прежде
  (assert-equal (integrate '(* x (exp x)) 'x) '(+ (* x (exp x)) (* -1 (exp x))))
  ; частичный ответ Риша — как прежде (expand не применяется)
  (assert-equal (integrate '(* (^ x x) (log x)) 'x)
                '(+ (^ x x) (* -1 (integrate (^ x x) x)))))

(deftest "integrate/N1: ответы проходят проверку дифференцированием"
  (assert-true (int-check (integrate '(/ 1 (sin x)) 'x) '(/ 1 (sin x)) 'x))
  (assert-true (int-check (integrate '(/ 1 (+ 2 (cos x))) 'x) '(/ 1 (+ 2 (cos x))) 'x))
  (assert-true (int-check (integrate '(* x (^ (sin x) 2)) 'x) '(* x (^ (sin x) 2)) 'x))
  (assert-true (int-check (integrate '(^ (cos x) 4) 'x) '(^ (cos x) 4) 'x)))
