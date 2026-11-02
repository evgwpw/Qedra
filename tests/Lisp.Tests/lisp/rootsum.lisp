; Lisp-тесты шага 21h: сумма по корням (root-sum t Q E) = Σ E по корням t многочлена Q; язык — rootsum(E, t, Q).

(define (rs-m s) (math-reset) (math-eval s))
(define (rs-mt s) (math-reset) (math-show (math-eval s)))
(define (rs-num e) (eval-num e))
(define (rs-close? a b) (< (abs (- a b)) 0.000000001))
; |комплексное число| невязки
(define (rs-zero? e) (< (num-abs e) 0.000000001))

; ---------- каноническая форма ----------

(deftest "root-sum: переименование связанной переменной — альфа-эквивалентные формы равны"
  (let ((a (root-sum 't '(+ 1 (* 3 (^ t 2))) '(* t (log (+ x (* 3/2 t) 1/2)))))
        (b (root-sum 's '(+ 1 (* 3 (^ s 2))) '(* s (log (+ x (* 3/2 s) 1/2))))))
    (assert-equal a b)
    (assert-equal (car a) 'root-sum)
    ; идемпотентность simplify
    (assert-equal (simplify a) a)))

(deftest "root-sum: связанная переменная не совпадает со свободным символом"
  ; t — параметр (свободный), связанная переменная — другая (s)
  (let ((r (root-sum 'u '(+ (* t (^ u 2)) 1) '(log (+ x (* u t))))))
    (assert-equal (car r) 'root-sum)
    (assert-equal (cadr r) 's)
    (assert-true (contains-sym? r 't))))

(deftest "root-sum: нормировка Q (знак, множитель), единственный неприводимый множитель"
  (assert-equal (root-sum 't '(+ -2 (* -2 (^ t 3))) '(* t t x))
                (root-sum 't '(+ 1 (^ t 3)) '(* t t x)))
  (assert-equal (root-sum 't '(+ -1 (^ t 3)) '(^ (+ x t) -1))
                (root-sum 'u '(+ 1 (* -1 (^ u 3))) '(^ (+ x u) -1))))

(deftest "root-sum: E = 0, E без t, Q без корней"
  (assert-equal (root-sum 't '(+ (^ t 3) t 1) 0) 0)
  (assert-equal (root-sum 't '(+ (^ t 3) t 1) '(* 2 x)) '(* 6 x))
  (assert-equal (root-sum 't 5 '(* t x)) 0))

(deftest "root-sum: линейность — сумма и вынос множителей без t"
  (let ((q '(+ (^ t 3) t 1)))
    (assert-equal (root-sum 't q '(+ (log (+ x t)) (log (+ x (* 2 t)))))
                  (simplify (list '+ (root-sum 't q '(log (+ x t))) (root-sum 't q '(log (+ x (* 2 t)))))))
    (assert-equal (root-sum 't q '(* a (log (+ x t))))
                  (simplify (list '* 'a (root-sum 't q '(log (+ x t))))))))

(deftest "root-sum: Q раскладывается — разворачивается в сумму, линейные множители — подстановка"
  ; (t − 1)(t² + 1): корень 1 подставляется, остаётся t² + 1
  (assert-equal (root-sum 't '(* (+ t -1) (+ (^ t 2) 1)) '(log (+ x t)))
                (simplify (list '+ '(log (+ 1 x)) (root-sum 't '(+ 1 (^ t 2)) '(log (+ x t))))))
  ; кратность считается: (t² + 1)²
  (assert-equal (root-sum 't '(^ (+ (^ t 2) 1) 2) '(log (+ x t)))
                (simplify (list '* 2 (root-sum 't '(+ 1 (^ t 2)) '(log (+ x t))))))
  ; полностью линейный Q
  (assert-equal (root-sum 't '(* (+ t -1) (+ t 2)) '(* t (log (+ x t))))
                (simplify '(+ (log (+ 1 x)) (* -2 (log (+ -2 x)))))))

(deftest "root-sum: многочлен от t — степенные суммы (формулы Ньютона)"
  (assert-equal (root-sum 't '(+ -3 (^ t 2)) 't) 0)
  (assert-equal (root-sum 't '(+ -1 (* -1 t) (^ t 3)) '(^ t 2)) 2)
  (assert-equal (root-sum 't '(+ -1 (* -1 t) (^ t 3)) '(^ t 5)) 5)
  ; Σ α² для t² − a t − 7: a² + 14
  (assert-equal (root-sum 't '(+ -7 (* -1 a t) (^ t 2)) '(^ t 2)) '(+ 14 (^ a 2))))

; ---------- печать и чтение ----------

(deftest "root-sum: печать math-print и чтение mathParse (round-trip)"
  (let ((r (root-sum 't '(+ 1 (* 5 t) (* 25 (^ t 2)) (* 125 (^ t 3)) (* 625 (^ t 4))) '(* t (log (+ x (* 5 t)))))))
    (assert-equal (math-print r) "rootsum(t*log(5t + x), t, 1 + 5t + 25t^2 + 125t^3 + 625t^4)")
    (assert-equal (math-read (math-print r)) r)
    (assert-equal (math-eval (math-show r)) r)))

(deftest "root-sum: язык — rootsum(E, t, Q) вычисляется в каноническую форму"
  (assert-equal (rs-m "rootsum(s*log(x + 5*s), s, 625*s^4 + 125*s^3 + 25*s^2 + 5*s + 1)")
                (root-sum 't '(+ 1 (* 5 t) (* 25 (^ t 2)) (* 125 (^ t 3)) (* 625 (^ t 4))) '(* t (log (+ x (* 5 t))))))
  (assert-equal (rs-mt "rootsum(t, t, t^2 - 3)") "0")
  (assert-equal (rs-mt "rootsum(1, t, t^3 + t + 1)") "3")
  (assert-equal (rs-mt "rootsum(1/(x - t), t, t^2 + 1) = rootsum(1/(x - s), s, s^2 + 1)") "true"))

(deftest "root-sum: невычисленная форма печатается и читается в режиме языка (math-show)"
  (let ((s (math-show (rs-m "rootsum(t*log(x + t), t, t^3 + t + 1)"))))
    (assert-equal s "rootsum(t*log(t + x), t, 1 + t + t^3)")
    (assert-equal (math-show (math-eval s)) s)))

; ---------- дифференцирование ----------

(deftest "root-sum: diff по x — внутрь суммы"
  (assert-equal (diff 'x (root-sum 't '(+ 1 (^ t 2)) '(* t (log (+ x t)))))
                (root-sum 't '(+ 1 (^ t 2)) '(* t (^ (+ x t) -1))))
  (assert-equal (rs-mt "diff(rootsum(t*log(x + t), t, t^3 + t + 1), x)") "rootsum(t/(t + x), t, 1 + t + t^3)")
  ; связанная переменная совпадает с переменной дифференцирования — тень: производная 0
  (assert-equal (diff 't (root-sum 't '(+ 1 (^ t 2)) '(* t (log (+ x t))))) 0))

(deftest "root-sum: diff, когда Q зависит от x (корни движутся) — сверка конечной разностью"
  (let* ((F (root-sum 't '(+ (^ t 3) (* x t) 1) '(^ (+ t x) -1)))
         (dF (diff 'x F))
         (h 0.00001) (x0 0.7)
         (fp (subst (list '= 'x (+ x0 h)) F)) (fm (subst (list '= 'x (- x0 h)) F))
         (an (subst (list '= 'x x0) dF)))
    ; конечная разность: погрешность ~ h²·f''' — сравниваем с относительным допуском 1e-5
    (assert-true (< (num-abs (list '- (list '* (/ 1 (* 2 h)) (list '- fp fm)) an))
                    (* 0.00001 (+ 1 (num-abs an)))))))

; ---------- подстановка и численное значение ----------

(deftest "root-sum: subst не трогает связанную переменную и не допускает захвата"
  (let ((F (root-sum 't '(+ 1 (^ t 2)) '(* t (log (+ x t))))))
    ; x := t — свободный t не должен захватываться связанным
    (let ((G (subst '(= x t) F)))
      (assert-true (contains-sym? G 't))
      ; значение при t = 2 совпадает со значением F при x = 2
      (assert-true (rs-zero? (list '- (subst '(= t 2) G) (subst '(= x 2) F)))))
    ; подстановка вместо связанной переменной F не меняет
    (assert-equal (subst '(= t 5) F) F)))

(deftest "root-sum: численное значение через комплексные корни Q (eval-num)"
  ; Σ 1/(2 − α), α² + 1 = 0: 4/5
  (assert-true (rs-close? (rs-num (subst '(= x 2) (root-sum 't '(+ 1 (^ t 2)) '(^ (+ x (* -1 t)) -1)))) 0.8))
  ; Σ_{α³ = 2} α·exp(α·0) · … : Σ log-free: Σ α/(x − α) при x = 3 для t³ − 2
  (let ((v (rs-num (subst '(= x 3) (root-sum 't '(+ -2 (^ t 3)) '(* t (^ (+ x (* -1 t)) -1)))))))
    ; Σ α/(3 − α) = Σ (3/(3−α) − 1) = 3·(3·9)/(27 − 2)... через P'(3)/P(3): Σ 1/(3−α) = P'(3)/P(3) = 27/25 ⇒ 3·27/25 − 3
    (assert-true (rs-close? v (- (/ 81 25) 3))))
  ; комплексные корни: Σ α·log(2 + α), α = ±i: i·(log(2 + i) − log(2 − i)) = −2·atan(1/2)
  (let ((z (subst '(= x 2) (root-sum 't '(+ 1 (^ t 2)) '(* t (log (+ x t)))))))
    (assert-true (rs-zero? (list '+ z 0.9272952180016122)))))

(deftest "root-sum: рациональное тело вычисляется ТОЧНО (рациональная арифметика по модулю Q), без шума больших корней"
  ; Σ 1/(x − α), α^6 = 2: Q'(x)/Q(x) = 6x^5/(x^6 − 2); при x = 3/10
  (let ((v (eval-num (subst '(= x 3/10) (root-sum 't '(+ -2 (^ t 6)) '(^ (+ x (* -1 t)) -1)))))
        (exact (/ (* 6 (^ 3/10 5)) (- (^ 3/10 6) 2))))
    (assert-true (< (abs (- v exact)) 0.000000000000001)))
  ; корни порядка 10^6 при коэффициентах до 10^18 — вычет-подобная сумма Σ α/(x − α)
  (let* ((Q2 '(+ -1000000000000000000 (* 1000001 (^ t 2)) (^ t 3)))
         (v2 (eval-num (subst '(= x 3/10) (root-sum 't Q2 '(* t (^ (+ x (* -1 t)) -1)))))))
    ; Σ α/(x − α) = x·Q'(x)/Q(x) − 3
    (let ((exact2 (- (/ (* 3/10 (+ (* 2 1000001 3/10) (* 3 (^ 3/10 2)))) (+ -1000000000000000000 (* 1000001 (^ 3/10 2)) (^ 3/10 3))) 3)))
      (assert-true (< (abs (- v2 exact2)) (* 0.00000000000001 (+ 1 (abs exact2))))))))

(deftest "root-sum: с параметрами — численно по подстановке параметров"
  (let ((F (root-sum 't '(+ (* a (^ t 2)) 1) '(* t (^ (+ x t) -1)))))
    ; Σ t/(x + t), a t² + 1 = 0: Σ = 2 − 2x²/(x² + 1/a) = 2/(a x² + 1)
    (assert-true (rs-zero? (list '- (subst '(= x 0.5) (subst '(= a 2.5) F)) (/ 2 (+ (* 2.5 0.25) 1)))))))
