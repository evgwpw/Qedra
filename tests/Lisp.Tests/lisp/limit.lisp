; Lisp-тесты пределов (lib\limit.lisp), Шаг 20

(deftest "пределы: замечательные пределы в нуле"
  (assert-equal (limit '(/ (sin x) x) 'x 0) 1)
  (assert-equal (limit '(/ (- 1 (cos x)) (^ x 2)) 'x 0) 1/2)
  (assert-equal (limit '(/ (log (+ 1 x)) x) 'x 0) 1)
  (assert-equal (limit '(/ (- (exp x) 1) x) 'x 0) 1)
  (assert-equal (limit '(/ (tan x) x) 'x 0) 1)
  (assert-equal (limit '(/ (atan x) x) 'x 0) 1)
  (assert-equal (limit '(/ (- x (sin x)) (^ x 3)) 'x 0) 1/6)
  (assert-equal (limit '(/ (- (exp x) 1 x) (^ x 2)) 'x 0) 1/2))

(deftest "пределы: прямая подстановка и сокращение"
  (assert-equal (limit '(^ x 2) 'x 3) 9)
  (assert-equal (limit '(+ (* 2 x) 1) 'x 5) 11)
  (assert-equal (limit '(/ (- (^ x 2) 1) (- x 1)) 'x 1) 2)
  (assert-equal (limit '(/ (- (^ x 3) 8) (- x 2)) 'x 2) 12)
  (assert-equal (limit '(exp x) 'x 0) 1)
  (assert-equal (limit 5 'x 3) 5))

(deftest "пределы: число e и степенно-показательные"
  (assert-equal (limit '(^ (+ 1 (/ 1 x)) x) 'x 'inf) '(exp 1))
  (assert-equal (limit '(^ (+ 1 x) (/ 1 x)) 'x 0) '(exp 1))
  (assert-equal (limit '(^ x x) 'x 0 'plus) 1)
  (assert-equal (limit '(^ x (/ 1 x)) 'x 'inf) 1)
  (assert-equal (limit '(^ (cos x) (/ 1 (^ x 2))) 'x 0) '(exp -1/2)))

(deftest "пределы: логарифм и экспонента, рост"
  (assert-equal (limit '(* x (log x)) 'x 0 'plus) 0)
  (assert-equal (limit '(/ (log x) x) 'x 'inf) 0)
  (assert-equal (limit '(* (^ x 5) (exp (* -1 x))) 'x 'inf) 0)
  (assert-equal (limit '(/ (exp x) (^ x 10)) 'x 'inf) 'inf)
  (assert-equal (limit '(/ (^ x 2) (exp x)) 'x 'inf) 0)
  (assert-equal (limit '(- (exp x) x) 'x 'inf) 'inf)
  (assert-equal (limit '(log x) 'x 0 'plus) '-inf)
  (assert-equal (limit '(exp x) 'x '-inf) 0)
  (assert-equal (limit '(log x) 'x 'inf) 'inf))

(deftest "пределы: полюса и стороны"
  (assert-equal (limit '(/ 1 x) 'x 0) 'undefined)
  (assert-equal (limit '(/ 1 x) 'x 0 'plus) 'inf)
  (assert-equal (limit '(/ 1 x) 'x 0 'minus) '-inf)
  (assert-equal (limit '(/ 1 (^ x 2)) 'x 0) 'inf)
  (assert-equal (limit '(/ -1 (^ x 2)) 'x 0) '-inf)
  (assert-equal (limit '(/ 1 (- x 2)) 'x 2 'plus) 'inf)
  (assert-equal (limit '(/ x (- 1 x)) 'x 1 'minus) 'inf)
  (assert-equal (limit '(/ 1 (^ x 3)) 'x 0) 'undefined))

(deftest "пределы: рациональные функции на бесконечности"
  (assert-equal (limit '(/ (+ (^ x 2) 1) (- (* 2 (^ x 2)) 3)) 'x 'inf) 1/2)
  (assert-equal (limit '(/ (+ x 1) (^ x 2)) 'x 'inf) 0)
  (assert-equal (limit '(/ (^ x 3) (+ (^ x 2) 1)) 'x 'inf) 'inf)
  (assert-equal (limit '(/ (^ x 3) (+ (^ x 2) 1)) 'x '-inf) '-inf)
  (assert-equal (limit '(/ (^ x 2) (+ x 1)) 'x '-inf) '-inf)
  (assert-equal (limit '(/ (- 3 x) (+ (* 2 x) 1)) 'x 'inf) -1/2)
  (assert-equal (limit '(/ 1 x) 'x 'inf) 0))

(deftest "пределы: разности и корни"
  (assert-equal (limit '(- (sqrt (+ (^ x 2) x)) x) 'x 'inf) 1/2)
  (assert-equal (limit '(- (sqrt (+ (^ x 2) 1)) x) 'x 'inf) 0)
  (assert-equal (limit '(sqrt x) 'x 0 'plus) 0)
  (assert-equal (limit '(sqrt x) 'x 'inf) 'inf))

(deftest "пределы: тригонометрия и ограниченные функции"
  (assert-equal (limit '(tan x) 'x '(/ pi 2) 'plus) '-inf)
  (assert-equal (limit '(tan x) 'x '(/ pi 2) 'minus) 'inf)
  (assert-equal (limit '(tan x) 'x '(/ pi 2)) 'undefined)
  (assert-equal (limit '(/ (sin x) x) 'x 'inf) 0)
  (assert-equal (limit '(* x (sin (/ 1 x))) 'x 0) 0)
  (assert-equal (limit '(atan x) 'x 'inf) '(* 1/2 pi))
  (assert-equal (limit '(atan x) 'x '-inf) '(* -1/2 pi))
  (assert-equal (limit '(sin x) 'x 'inf) '(limit (sin x) x inf)))

(deftest "пределы: параметры"
  (assert-equal (limit '(/ (sin (* a x)) x) 'x 0) 'a)
  (assert-equal (limit '(/ (- (exp (* a x)) 1) x) 'x 0) 'a)
  (assert-equal (limit '(^ (+ 1 (/ a x)) x) 'x 'inf) '(exp a))
  (assert-equal (limit '(+ (* a x) b) 'x 2) (simplify '(+ (* 2 a) b))))

(deftest "пределы: модуль"
  (assert-equal (limit '(/ (abs x) x) 'x 0) 'undefined)
  (assert-equal (limit '(/ (abs x) x) 'x 0 'plus) 1)
  (assert-equal (limit '(/ (abs x) x) 'x 0 'minus) -1))

(deftest "пределы: невычисленная форма, а не ошибка"
  (assert-equal (limit '(sin x) 'x 'inf) '(limit (sin x) x inf))
  (assert-equal (limit '(* x (sin x)) 'x 'inf) '(limit (* x (sin x)) x inf))
  (assert-equal (limit '(sin x) 'x 'inf 'plus) '(limit (sin x) x inf plus))
  (assert-equal (limit '(f x) 'x 0) '(limit (f x) x 0))
  (assert-error (limit '(sin x) 3 0))
  (assert-error (limit '(sin x) 'x 0 'sideways)))

; ---------- алгоритм Грунца в limit (шаг 21j.3) ----------
; auto: старый каскад, затем Грунц (только на верхнем уровне); classic — без Грунца; gruntz — только Грунц.

(define (lg-with-mode mode thunk)
  (let ((old (set-algorithm 'limit mode)))
    (unwind-protect (thunk) (set-algorithm 'limit old))))
(define (lg-classic e x a &rest side) (lg-with-mode 'classic (lambda () (apply limit (append (list e x a) side)))))
(define (lg-gruntz e x a &rest side) (lg-with-mode 'gruntz (lambda () (apply limit (append (list e x a) side)))))
(define (lg-uneval? r) (and (pair? r) (equal? (car r) 'limit)))
(define (lg-num e x0) (eval-num (subst (list '= 'x x0) e)))

(deftest "пределы: переключатель limit — auto по умолчанию, classic без Грунца, gruntz только Грунц"
  (assert-equal (algorithm 'limit) 'auto)
  (let ((e '(- x (log (+ 1 (exp x))))))
    (assert-equal (limit e 'x 'inf) 0)
    (assert-equal (lg-gruntz e 'x 'inf) 0)
    (assert-true (lg-uneval? (lg-classic e 'x 'inf))))
  (assert-equal (algorithm 'limit) 'auto)
  ; gruntz: простые случаи тоже идут через Грунц
  (assert-equal (lg-gruntz '(/ (exp x) (^ x 2)) 'x 'inf) 'inf)
  (assert-equal (lg-gruntz '(/ (sin x) x) 'x 0) 1)
  (assert-true (lg-uneval? (lg-gruntz '(sin x) 'x 'inf)))
  ; classic = как до шага 21j.3
  (assert-equal (lg-classic '(/ (exp x) (^ x 2)) 'x 'inf) 'inf))

(deftest "пределы: Грунц берёт то, что старый каскад не брал (x → +∞)"
  (assert-equal (limit '(^ (+ (^ 3 x) (^ 5 x)) (/ 1 x)) 'x 'inf) 5)
  (assert-equal (limit '(^ (+ (^ 2 x) (^ 3 x)) (/ 1 x)) 'x 'inf) 3)
  (assert-equal (limit '(/ (exp x) (+ a (exp x))) 'x 'inf) 1)
  (assert-equal (limit '(- x (log (+ a (exp x)))) 'x 'inf) 0)
  ; 8.1, 8.2 диссертации
  (let ((e81 '(* (exp x) (- (exp (- (/ 1 x) (exp (- x)))) (exp (/ 1 x)))))
        (e82 '(* (exp x) (- (exp (+ (/ 1 x) (exp (- x)) (exp (- (^ x 2))))) (exp (- (/ 1 x) (exp (- (exp x)))))))))
    (assert-equal (limit e81 'x 'inf) -1)
    (assert-equal (limit e82 'x 'inf) 1)
    (assert-true (lg-uneval? (lg-classic e81 'x 'inf)))
    (assert-true (< (num-abs (- (lg-num e81 25.0) -1)) 0.05))
    (assert-true (< (num-abs (- (lg-num e82 25.0) 1)) 0.05)))
  ; 8.3, 8.5 — башни exp глубины ≥ 2 идут в Грунц первыми (шаг 21j.3′), старый каскад на них тратил 1–2 с на отказ
  (assert-equal (limit '(- (exp (/ (exp (- x (exp (- x)))) (- 1 (/ 1 x)))) (exp (exp x))) 'x 'inf) 'inf)
  (assert-equal (limit '(/ (exp (exp (exp (+ x (exp (- x)))))) (exp (exp (exp x)))) 'x 'inf) 'inf)
  (assert-equal (limit '(- (exp x) (exp (+ x (exp (- x))))) 'x 'inf) -1)
  (assert-equal (limit '(/ (exp x) (^ (+ 1 (/ 1 x)) (^ x 2))) 'x 'inf) '(exp 1/2))
  (assert-equal (limit '(^ (/ (+ (^ x 7) x 1) (+ (^ 2 x) (^ x 2))) (/ -1 x)) 'x 'inf) 2)
  (assert-equal (limit '(/ x (log (log (* x (exp x))))) 'x 'inf) 'inf)
  ; параметр без декларации, от знака которого зависит ответ — невычисленная форма
  (assert-true (lg-uneval? (limit '(^ (+ (^ a x) (^ 5 x)) (/ 1 x)) 'x 'inf))))

(deftest "пределы: Грунц при x → −∞"
  (assert-equal (limit '(/ (* x (exp x)) (+ (exp x) 1)) 'x '-inf) 0)
  (assert-equal (limit '(* 2 (cosh x) (exp x)) 'x '-inf) 1)
  (assert-equal (limit '(* 2 (sinh x) (exp x)) 'x '-inf) -1)
  (assert-equal (limit '(^ (+ (^ 2 x) (^ 3 x)) (/ 1 x)) 'x '-inf) 2)
  (assert-equal (limit '(- x (log (+ 1 (exp x)))) 'x '-inf) '-inf)
  (assert-equal (limit '(* (exp x) (+ 1 (exp (- x)))) 'x '-inf) 1)
  (assert-equal (limit '(* (exp (- x)) (- (exp x) 1)) 'x '-inf) '-inf)
  (assert-true (lg-uneval? (lg-classic '(/ (* x (exp x)) (+ (exp x) 1)) 'x '-inf)))
  (assert-true (< (num-abs (lg-num '(/ (* x (exp x)) (+ (exp x) 1)) -40.0)) 0.000001)))

(deftest "пределы: Грунц при x → a±, двусторонний"
  (assert-equal (limit '(* x (log x)) 'x 0 'plus) 0)
  (assert-equal (limit '(/ (exp (/ -1 x)) x) 'x 0 'plus) 0)
  (assert-equal (limit '(/ (exp (/ -1 x)) (^ x 3)) 'x 0 'plus) 0)
  (assert-equal (limit '(* (exp (/ -1 x)) (log x)) 'x 0 'plus) 0)
  (assert-equal (limit '(exp (/ -1 x)) 'x 0 'minus) 'inf)
  (assert-equal (limit '(exp (/ 1 x)) 'x 0 'plus) 'inf)
  (assert-equal (limit '(exp (/ 1 x)) 'x 0 'minus) 0)
  ; односторонние различны — undefined (как у прежнего limit)
  (assert-equal (limit '(exp (/ 1 x)) 'x 0) 'undefined)
  (assert-equal (limit '(exp (/ -1 x)) 'x 0) 'undefined)
  ; обе стороны дают 0 — значение
  (assert-equal (limit '(/ (exp (/ -1 (^ x 2))) x) 'x 0) 0)
  (assert-equal (limit '(* (exp (/ -1 (^ x 2))) (/ 1 (^ x 10))) 'x 0) 0)
  ; не в нуле: сведение x → a + 1/t
  (assert-equal (limit '(/ (exp (/ -1 (- x 1))) (- x 1)) 'x 1 'plus) 0)
  (assert-equal (limit '(exp (/ -1 (- x 1))) 'x 1 'minus) 'inf)
  (assert-equal (limit '(exp (/ 1 (- x 1))) 'x 1) 'undefined)
  (assert-true (lg-uneval? (lg-classic '(/ (exp (/ -1 x)) x) 'x 0 'plus)))
  (assert-true (< (num-abs (lg-num '(/ (exp (/ -1 x)) x) 0.01)) 0.000001)))

(deftest "пределы: прежние ответы не меняются — auto = classic там, где classic отвечает"
  (let ((cases (list (list '(/ (sin x) x) 'x 0)
                     (list '(^ (+ 1 (/ 1 x)) x) 'x 'inf)
                     (list '(/ (exp x) (^ x 2)) 'x 'inf)
                     (list '(- (exp x) x) 'x 'inf)
                     (list '(* x (log x)) 'x 0 'plus)
                     (list '(^ x x) 'x 0 'plus)
                     (list '(/ (- (exp x) 1) x) 'x 0)
                     (list '(/ (log (+ 1 x)) x) 'x 0)
                     (list '(/ (- (^ 2 x) 1) x) 'x 0)
                     (list '(^ (+ 1 (exp x)) (/ 1 x)) 'x '-inf)
                     (list '(^ (exp x) (exp (- x))) 'x 'inf)
                     (list '(- (/ 1 x) (/ 1 (log (+ 1 x)))) 'x 0 'plus)
                     (list '(/ (log x) (exp (- (/ 1 x)))) 'x 0 'plus)
                     (list '(* x (exp (- x)) (+ 1 (exp x))) 'x '-inf)
                     (list '(^ (+ (^ x 2) x) (/ 1 2)) 'x 'inf))))
    (map (lambda (c)
           (let ((c1 (apply lg-classic c)) (a1 (apply limit c)))
             (assert-equal a1 c1)
             (let ((g (apply lg-gruntz c)))
               ; где отвечает и Грунц — тот же ответ (формы e^(1/2) и т. п. сравниваем после simplify)
               (if (not (lg-uneval? g)) (assert-equal (simplify g) (simplify c1))))))
         cases)))

(deftest "пределы: ряды не дают неверный 0 при быстро растущих коэффициентах (8.14 раньше давал 1)"
  (let ((e '(/ (exp (exp (* 2 (log (+ (^ x 5) x)) (log (log x))))) (exp (exp (* 10 (log x) (log (log x))))))))
    (assert-true (lg-uneval? (lg-classic e 'x 'inf)))
    (assert-equal (limit e 'x 'inf) 'inf)))

; ---------- перекрёстная проверка classic ↔ gruntz (шаг 21j.3′) ----------
; Для каждого предела — режимы classic (без Грунца) и gruntz (только Грунц). Где отвечают оба — ответы должны совпадать
; (точно после simplify или численно); auto обязан совпасть с classic там, где classic отвечает, иначе — с gruntz.
; Нашлись и исправлены в 21j.3: 0^0 → 1 в lim-pow, ряды с быстро растущими коэффициентами (8.14).

(define (lg-same? a b)
  (or (equal? (simplify a) (simplify b))
      (and (not (member? a '(inf -inf undefined))) (not (member? b '(inf -inf undefined)))
           (let ((na (eval-num a)) (nb (eval-num b)))
             (and (number? na) (number? nb) (< (num-abs (- na nb)) 0.000000001))))))

(define lg-cross-cases
  (list
   (list '(/ (sin x) x) 'x 0) (list '(/ (- 1 (cos x)) (^ x 2)) 'x 0) (list '(/ (log (+ 1 x)) x) 'x 0)
   (list '(/ (- (exp x) 1) x) 'x 0) (list '(/ (tan x) x) 'x 0) (list '(/ (atan x) x) 'x 0)
   (list '(/ (- x (sin x)) (^ x 3)) 'x 0) (list '(/ (- (exp x) 1 x) (^ x 2)) 'x 0)
   (list '(^ x 2) 'x 3) (list '(/ (- (^ x 2) 1) (- x 1)) 'x 1)
   (list '(^ (+ 1 (/ 1 x)) x) 'x 'inf) (list '(^ (+ 1 x) (/ 1 x)) 'x 0) (list '(^ x x) 'x 0 'plus)
   (list '(^ x (/ 1 x)) 'x 'inf) (list '(^ (cos x) (/ 1 (^ x 2))) 'x 0) (list '(* x (log x)) 'x 0 'plus)
   (list '(/ (log x) x) 'x 'inf) (list '(* (^ x 5) (exp (* -1 x))) 'x 'inf) (list '(/ (exp x) (^ x 10)) 'x 'inf)
   (list '(/ (^ x 2) (exp x)) 'x 'inf) (list '(- (exp x) x) 'x 'inf) (list '(log x) 'x 0 'plus)
   (list '(exp x) 'x '-inf) (list '(- (sqrt (+ (^ x 2) x)) x) 'x 'inf) (list '(- (sqrt (+ (^ x 2) 1)) x) 'x 'inf)
   (list '(/ (- (exp (* a x)) 1) x) 'x 0) (list '(^ (+ 1 (/ a x)) x) 'x 'inf) (list '(/ (abs x) x) 'x 0 'plus)
   (list '(/ (- (^ 2 x) 1) x) 'x 0) (list '(^ (+ 1 (exp x)) (/ 1 x)) 'x '-inf) (list '(^ (exp x) (exp (- x))) 'x 'inf)
   (list '(- (/ 1 x) (/ 1 (log (+ 1 x)))) 'x 0 'plus) (list '(/ (log x) (exp (- (/ 1 x)))) 'x 0 'plus)
   (list '(* x (exp (- x)) (+ 1 (exp x))) 'x '-inf) (list '(exp (/ -1 (^ x 2))) 'x 0)
   (list '(* (exp x) (+ 1 (exp (- x)))) 'x '-inf) (list '(tanh x) 'x 'inf) (list '(tanh x) 'x '-inf)
   (list '(- x (log (+ 1 (exp x)))) 'x '-inf) (list '(/ (exp x) (+ 1 (exp x))) 'x 'inf)
   (list '(^ (+ x 1) (/ 1 (log (+ x 1)))) 'x 'inf) (list '(- (^ (+ (^ x 3) 1) 1/3) x) 'x 'inf)
   (list '(* (log x) (exp (/ -1 x))) 'x 0 'plus) (list '(^ (log x) (/ 1 x)) 'x 'inf) (list '(^ x (/ 1 (log x))) 'x 'inf)
   (list '(^ (+ 1 (/ 2 x)) (* 3 x)) 'x 'inf) (list '(^ (- 1 (/ 1 x)) x) 'x 'inf)
   (list '(* (- (exp (/ 1 x)) 1) x) 'x 'inf) (list '(/ (exp (* 2 x)) (exp x)) 'x '-inf)
   (list '(* x (- (log (+ x 1)) (log x))) 'x 'inf) (list '(/ (exp (^ x 2)) (exp x)) 'x 'inf)
   (list '(/ (log (+ 1 (exp x))) x) 'x '-inf) (list '(* (^ x 2) (exp (- (/ 1 x)))) 'x 0 'plus)
   (list '(^ (exp x) (/ 1 x)) 'x 'inf) (list '(/ (log (^ x 2)) (log x)) 'x 'inf)
   (list '(* (- (^ (+ 1 (/ 1 x)) x) (exp 1)) x) 'x 'inf) (list '(^ (^ x x) (/ 1 x)) 'x 'inf)
   (list '(^ (+ (exp x) x) (/ 1 x)) 'x 'inf) (list '(/ (log (+ x (exp x))) x) 'x 'inf)
   (list '(/ x (log (^ x (log (^ x (/ (log 2) (log x))))))) 'x 'inf)
   (list '(/ (* (log x) (- (log (+ (log x) (log (log x)))) (log (log x)))) (log (+ (log x) (log (log (log x)))))) 'x 'inf)))

(deftest "пределы: перекрёстная проверка classic и gruntz — где отвечают оба, ответы совпадают"
  (let ((n-both 0))
    (map (lambda (c)
           (let ((rc (apply lg-classic c)) (rg (apply lg-gruntz c)) (ra (apply limit c)))
             (if (and (not (lg-uneval? rc)) (not (lg-uneval? rg)))
                 (begin (set! n-both (+ n-both 1))
                        (assert-true (lg-same? rc rg)))
                 #f)
             ; auto: classic, если classic ответил; иначе то, что дал Грунц
             (assert-true (lg-same? ra (if (lg-uneval? rc) rg rc)))))
         lg-cross-cases)
    ; проверка самой проверки: сравниваются десятки пар, а не пустое множество
    (assert-true (> n-both 50))))

(deftest "пределы: Грунц-первым — башни exp-log быстро, ответы 8.x в auto"
  (let ((t0 (clock-us)))
    (assert-equal (limit '(/ (exp (exp (exp x))) (exp (exp (exp (- x (exp (- (exp (exp x))))))))) 'x 'inf) 1)
    (assert-equal (limit '(exp (/ (log (log (+ x (exp (* (log x) (log (log x))))))) (log (log (log (+ (exp x) x (log x))))))) 'x 'inf)
                  '(exp 1))
    (assert-equal (limit '(/ (- (exp (/ (* x (exp (- x))) (+ (exp (- x)) (exp (/ (* -2 (^ x 2)) (+ x 1)))))) (exp x)) x) 'x 'inf)
                  (simplify '(* -1 (exp 2))))
    (assert-equal (limit '(- (exp (exp (/ (exp x) (- 1 (/ 1 x))))) (exp (exp (/ (exp x) (- 1 (/ 1 x) (^ (log x) (- (log x)))))))) 'x 'inf)
                  '-inf)
    ; раньше эти четыре предела вместе занимали > 30 с (старый каскад отказывал); теперь — доли секунды. Порог щедрый (отладочная
    ; сборка, нагруженная машина), ловит возврат к прежнему порядку
    (assert-true (< (- (clock-us) t0) 20000000)))
  ; не exp-log: √(x + √x) − √x — старый каскад отказывает, последняя попытка Грунца отвечает
  (assert-equal (limit '(- (sqrt (+ x (sqrt x))) (sqrt x)) 'x 'inf) 1/2))

(deftest "θ и δ: пределы"
  ; ответ демо-осциллятора: θ(t−1), θ(t−2) → 1 при t → +∞
  (let ((x1 '(+ (* 3/2 (exp (- (- t 1))) (sin (* 2 (- t 1))) (heaviside (- t 1)))
                (* (- 2 (* 2 (exp (- (- t 2))) (cos (* 2 (- t 2)))) (* (exp (- (- t 2))) (sin (* 2 (- t 2))))) (heaviside (- t 2))))))
    (assert-equal (limit x1 't 'inf) 2)
    (assert-equal (limit x1 't '-inf) 0))
  (assert-equal (limit '(* (heaviside t) (sin t)) 't 0 'plus) 0)
  (assert-equal (limit '(heaviside t) 't 0 'minus) 0)
  (assert-equal (limit '(heaviside t) 't 0 'plus) 1)
  (assert-equal (limit '(heaviside t) 't 0) 'undefined)
  (assert-equal (limit '(heaviside (- 1 t)) 't 'inf) 0)
  (assert-equal (limit '(dirac (- t 3)) 't 'inf) 0)
  (assert-equal (limit '(dirac (- t 3)) 't '-inf) 0)
  (assert-equal (limit '(dirac (- t 3)) 't 0) 0))

(deftest "θ и δ: eval-num и график"
  (assert-equal (eval-num '(heaviside -1/4)) 0.0)
  (assert-equal (eval-num '(heaviside 1/4)) 1.0)
  (assert-equal (eval-num '(heaviside 0)) 0.5)
  (assert-equal (eval-num '(dirac 2)) 0.0)
  (assert-equal (eval-num '(dirac 0)) '(dirac 0))
  (assert-equal (nth (plot-info '(* (heaviside (- t 1)) (sin t)) 't 0 5) 7) '(1.0)))   ; 7 — значение после :jumps
