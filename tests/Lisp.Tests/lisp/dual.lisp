; dual.lisp — тесты шага CHECK.DUAL: значение и производная в точке через дуальные числа (lib/dual.lisp)

(define dt-pts '(3/10 47/100 71/100 137/100 11/5))
(define dt-params '(17/10 23/10 19/10 31/10 13/10 29/10 11/10 27/10))
(define (dt-env ps) (map2 list ps dt-params))
(define (dt-d e p env) (let ((r (dual-eval e 'x p env))) (and r (cdr r))))
(define (dt-v e p env) (let ((r (dual-eval e 'x p env))) (and r (car r))))
; |a − b| ≤ tol·|b| (относительно: абсолютный допуск скрывал малую, но настоящую невязку, как у t_2_3/350)
(define (dt-close? a b tol) (and (real-numeric? a) (real-numeric? b) (<= (abs (- a b)) (* tol (abs b)))))
; значение eval-num выражения в точке p при параметрах env
(define (dt-num e p env) (eval-num (subst (cons (list 'x p) env) e)))
; число точек, где dual-производная F совпала с f (eval-num f) до tol
(define (dt-matches F f env tol)
  (length (filter (lambda (p) (dt-close? (dt-d F p env) (dt-num f p env) tol)) dt-pts)))
; число точек, где dual-производная совпала с eval-num символьной производной diff
(define (dt-vs-diff e env tol)
  (dt-matches e (diff 'x e) env tol))

(deftest "dual: x·exp(x) — значение и производная"
  (let ((r (dual-eval '(* x (exp x)) 'x 3/10 '())))
    (assert-true (dt-close? (car r) (dt-num '(* x (exp x)) 3/10 '()) 1e-12))
    (assert-true (dt-close? (cdr r) (dt-num '(* (+ 1 x) (exp x)) 3/10 '()) 1e-12))))

(deftest "dual: совпадение с diff в 5 точках — алгебра, степени с переменным показателем, параметры"
  (for-each
   (lambda (e)
     (assert-equal (dt-vs-diff e (dt-env (list 'a 'b)) 1e-9) 5))
   '((^ (+ x a) (* b x))
     (* (^ x -3) (+ a (* b x)))
     (^ (+ 1 (* a (^ x 2))) -7/2)
     (/ (+ x a) (- x -2))
     (- (* a x) (^ x 3))
     (^ a (+ b x))
     (sqrt (+ x (* a b))))))

(deftest "dual: совпадение с diff — элементарные функции и обратные"
  (for-each
   (lambda (e)
     (assert-equal (dt-vs-diff e (dt-env (list 'a)) 1e-9) 5))
   '((exp (* a x))
     (log (+ x a))
     (* (sin (* a x)) (cos x))
     (tan (* x 1/2))
     (cot x)
     (sec x)
     (csc (* a x))
     (atan (* a x))
     (asin (* x 1/3))
     (acos (* x 1/3))
     (sinh (* a x))
     (cosh x)
     (tanh x)
     (sech x)
     (asinh (* a x))
     (atanh (* x 1/3))
     (log (log (+ x 2)))
     (exp (^ x 2)))))

(deftest "dual: совпадение с diff — спецфункции (erf, Ei, Si, Ci, polylog, 2F1, эллиптические)"
  (for-each
   (lambda (e)
     (assert-equal (dt-vs-diff e (dt-env (list 'a)) 1e-9) 5))
   '((erf (* a x))
     (erfi x)
     (Ei (* a x))
     (Si x)
     (Ci (+ x a))
     (hypergeometric-2f1 1/2 1/3 5/3 (* x 1/3))
     (elliptic-f (* x 1/2) 1/2)
     (elliptic-e (* x 1/2) 1/3)
     (gamma 2 (+ x 1)))))

; diff от polylog в точке не вычисляется (остаток diff), поэтому сверка с формулой: Li₂(x/3)′ = −ln(1 − x/3)/x
(deftest "dual: polylog — производная по формуле"
  (assert-equal (dt-matches '(polylog 2 (* x 1/3)) '(* -1 (log (+ 1 (* -1/3 x))) (^ x -1)) '() 1e-9) 5))

(deftest "dual: комплексные значения — log отрицательного, мнимая единица"
  (let ((r (dual-eval '(log (+ x -1)) 'x 3/10 '())))
    (assert-true (dt-close? (nth (car r) 1) (eval-num '(log 7/10)) 1e-12))
    (assert-true (dt-close? (nth (nth (car r) 2) 1) (eval-num 'pi) 1e-12))
    (assert-true (dt-close? (cdr r) (/ 1 (- 3/10 1)) 1e-12)))
  (let ((r (dual-eval '(+ (* 2 %i) (* x x)) 'x 3/10 '())))
    (assert-true (dt-close? (nth (car r) 1) 0.09 1e-12))
    (assert-true (dt-close? (cdr r) 0.6 1e-12)))
  ; ((x + i)^3)′ = 3 (x + i)²: действительная часть 3 (x² − 1)
  (let ((r (dual-eval-parts '(^ (+ x %i) 3) 'x 1/2 '())))
    (assert-true (dt-close? (car (cdr r)) (* 3 (- 1/4 1)) 1e-12))
    (assert-true (dt-close? (cdr (cdr r)) 3.0 1e-12))))

(deftest "dual: отказ #f — голова без производной, полюс, нет значения параметра, неизвестное имя"
  (assert-equal (dual-eval '(foo x) 'x 3/10 '()) #f)
  ; модуль эллиптической зависит от x: diff его не дифференцирует (даёт 0) — это не догадка, а отказ
  (assert-equal (dual-eval '(elliptic-f 1/2 x) 'x 3/10 '()) #f)
  (assert-equal (dual-eval '(log_gamma x) 'x 3/10 '()) #f)
  (assert-equal (dual-eval '(exp_integral_e 2 x) 'x 3/10 '()) #f)
  (assert-equal (dual-eval '(^ x -1) 'x 0 '()) #f)
  (assert-equal (dual-eval '(log x) 'x 0 '()) #f)
  (assert-equal (dual-eval '(abs x) 'x 0 '()) #f)
  (assert-equal (dual-eval '(* a x) 'x 3/10 '()) #f)
  (assert-equal (dual-eval '(root-sum t (+ (^ t 2) x) (* t (log (+ x t)))) 'x 3/10 '()) #f)
  (assert-equal (dual-eval '(integrate (sin x) x) 'x 3/10 '()) #f))

(deftest "dual: abs вне нуля — знак производной"
  (assert-true (dt-close? (dt-d '(abs (+ x -1)) 3/10 '()) -1 1e-12))
  (assert-true (dt-close? (dt-d '(abs (+ x -1)) 11/5 '()) 1 1e-12)))

; ---------- П2: подделки не проходят ----------
(define dt-fake-env '((a 17/10)))
(deftest "dual: верный ответ и его подделки — ∫ x·e^(a x)"
  (let ((f '(* x (exp (* a x))))
        (G '(* (exp (* a x)) (+ (* x (^ a -1)) (* -1 (^ a -2))))))
    (assert-equal (dt-matches G f dt-fake-env 1e-9) 5)
    ; F + 1e-3·x
    (assert-equal (dt-matches (list '+ G '(* 1/1000 x)) f dt-fake-env 1e-9) 0)
    ; F·(1 + 1e-3)
    (assert-equal (dt-matches (list '* 1001/1000 G) f dt-fake-env 1e-9) 0)
    ; сдвиг параметра в коэффициенте
    (assert-equal (dt-matches '(* (exp (* a x)) (+ (* x (^ (+ a 1/1000) -1)) (* -1 (^ (+ a 1/1000) -2)))) f dt-fake-env 1e-9) 0)
    ; потеряно слагаемое
    (assert-equal (dt-matches '(* (exp (* a x)) x (^ a -1)) f dt-fake-env 1e-9) 0)))

; ---------- П3: t_2_3/350, прежний неверный ответ порта ----------
; параметры подобраны так, чтобы c + d·x ≈ 1 (без катастрофического сокращения слагаемых F: при c + d·x ≈ 3–5 производная
; ~1e-9 при значении F ≈ 20, и double её не различает — оговорка карточки CHECK.DUAL)
(define dt-350-env '((F 17/10) (a 1/3) (b 3/2) (c 1/2) (d 1)))
(define dt-350-pts '(-1/4 -1/10 1/10 3/10 47/100))
(define (dt-matches-at F f env tol pts)
  (length (filter (lambda (p) (dt-close? (dt-d F p env) (dt-num f p env) tol)) pts)))
(define dt-350-f '(* (^ F (+ a (* b (^ (+ c (* d x)) -3)))) (^ (+ c (* d x)) -16)))
(define dt-350-old '(* -1/15 (^ F (+ a (* b (^ (+ c (* d x)) -3)))) (^ d -1) (^ (+ c (* d x)) -15)))
(define dt-350-ref
  '(* -1/3 (^ F (+ a (* b (^ (+ c (* d x)) -3)))) (^ b -5) (^ d -1) (^ (+ c (* d x)) -12)
      (+ (* -24 b (^ (+ c (* d x)) 9) (log F)) (* 12 (^ b 2) (^ (+ c (* d x)) 6) (^ (log F) 2))
         (* -4 (^ b 3) (^ (+ c (* d x)) 3) (^ (log F) 3)) (* (^ b 4) (^ (log F) 4)) (* 24 (^ (+ c (* d x)) 12)))
      (^ (log F) -5)))

(deftest "dual: t_2_3/350 — эталон Rubi сходится в 5 точках, старый неверный ответ расходится во всех"
  (assert-equal (dt-matches-at dt-350-ref dt-350-f dt-350-env 1e-9 dt-350-pts) 5)
  (assert-equal (dt-matches-at dt-350-old dt-350-f dt-350-env 1e-3 dt-350-pts) 0))

(deftest "dual: t_2_3/350 — старый ответ: относительная невязка велика в каждой из 5 точек"
  (for-each
   (lambda (p)
     (let ((d (dt-d dt-350-old p dt-350-env)) (f (dt-num dt-350-f p dt-350-env)))
       (assert-true (> (abs (- d f)) (* 1e-2 (abs f))))))
   dt-350-pts))

(deftest "dual: нет молчаливого нуля — производная от постоянной и от x вне головы"
  (assert-equal (dt-d '(* a b) 3/10 (dt-env (list 'a 'b))) 0.0)
  (assert-equal (dt-d 'x 3/10 '()) 1.0)
  (assert-equal (dual-eval 5 'x 3/10 '()) (cons 5.0 0.0)))

; CH4.SPEED: Ei от мнимого аргумента eval-num не вычисляет — проверка идёт через Γ(0, −u) (те же производные)
(deftest "int-check: ответ с Ei(i·d·x/2) принимается"
  (assert-true (int-check '(+ (* 1/2 %i (exp (* -1 %i c)) (Ei (* -1 %i d x))) (* -1/2 %i (exp (* %i c)) (Ei (* %i d x))))
                          '(* (sin (+ c (* d x))) (^ x -1)) 'x))
  ; неверный ответ с Ei остаётся отвергнутым
  (assert-true (not (int-check '(* 2 (Ei (* %i d x))) '(* (exp (* %i d x)) (^ x -1)) 'x))))
