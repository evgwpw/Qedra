; Lisp-тесты шага 18: решение уравнений.
; Коммит 1 — примитивы: мнимая единица %i, subst, «=» в инфиксе, resultant, nroots, real-roots.

; числа и %i-формы равны с точностью 1e-9 (для результатов nroots)
(define (near? z w)
  (let ((a (domain::split-imag z)) (b (domain::split-imag w)))
    (and (< (abs (- (car a) (car b))) 0.000000001)
         (< (abs (- (cadr a) (cadr b))) 0.000000001))))
(define (all-near? l1 l2)
  (and (= (length l1) (length l2))
       (every? (lambda (p) (near? (car p) (cadr p))) (map2 list l1 l2))))

; ---------- мнимая единица ----------

(deftest "%i: sqrt отрицательных рациональных"
  (assert-equal (sqrt -4) '(* 2 %i))
  (assert-equal (sqrt -1) '%i)
  (assert-equal (sqrt -1/4) '(* 1/2 %i))
  (assert-equal (simplify '(sqrt -9)) '(* 3 %i))
  (assert-equal (sqrt 4) 2))

(deftest "%i: sqrt неточного корня отрицательного числа — %i·√|a|, не NaN"
  (let ((r (sqrt -2)))
    (assert-true (contains-sym? r '%i))
    (assert-equal (simplify (list '^ r 2)) -2))
  (assert-equal (simplify '(^ -4 1/2)) '(* 2 %i)))

(deftest "%i: sqrt отрицательного float — комплексный float, не NaN"
  (assert-equal (type-of (sqrt -4.0)) 'complex))

(deftest "%i: степени %i по n mod 4"
  (assert-equal (simplify '(^ %i 2)) -1)
  (assert-equal (simplify '(^ %i 3)) '(* -1 %i))
  (assert-equal (simplify '(^ %i 4)) 1)
  (assert-equal (simplify '(^ %i 100)) 1)
  (assert-equal (simplify '(^ %i -1)) '(* -1 %i))
  (assert-equal (simplify '(^ %i -2)) -1))

(deftest "%i: произведения сворачиваются"
  (assert-equal (simplify '(* %i %i)) -1)
  (assert-equal (simplify '(* 2 %i 3 %i)) -6)
  (assert-equal (simplify '(* %i %i %i)) '(* -1 %i))
  (assert-equal (simplify '(+ %i (* 2 %i))) '(* 3 %i)))

(deftest "%i: (a + b%i)(a - b%i) = a² + b²"
  (assert-equal (expand '(* (+ 1 %i) (+ 1 (* -1 %i)))) 2)
  (assert-equal (expand '(^ (+ 1 %i) 2)) '(* 2 %i))
  (assert-equal (expand '(* (+ a (* b %i)) (+ a (* -1 b %i)))) '(+ (^ a 2) (^ b 2))))

(deftest "%i: домены"
  (assert-equal (in? '%i complexes) #t)
  (assert-equal (in? '%i reals) #f)
  (assert-equal (in? '%i integers) #f)
  (assert-equal (real? '%i) #f)
  (assert-equal (real? '(* 2 %i)) #f)
  (assert-equal (real? '(+ 1 (* 2 %i))) #f)
  (assert-equal (in? '(+ 1 (* 2 %i)) complexes) #t)
  (assert-equal (real? (simplify '(* %i %i))) #t))

; ---------- subst ----------

(deftest "subst: одно правило, список правил, пары"
  (assert-equal (subst '(= x 3) '(+ x (^ x 2))) 12)
  (assert-equal (subst '((= x 1) (= y 2)) '(+ x y)) 3)
  (assert-equal (subst '((x 1) (y 2)) '(+ (* 2 x) y)) 4)
  (assert-equal (subst '(x 2) '(* x z)) '(* 2 z)))

(deftest "subst: подстановка одновременная"
  (assert-equal (subst '((= x y) (= y x)) '(+ (* 2 x) y)) '(+ x (* 2 y)))
  (assert-equal (subst '((= x y) (= y 1)) 'x) 'y))

(deftest "subst: упрощение после подстановки, ядра, %i"
  (assert-equal (subst '(= x 0) '(+ 1 (sin x))) 1)    ; Шаг 21c: sin(0) = 0 считает ядро
  (assert-equal (subst '(= x (* 2 %i)) '(^ x 2)) -4)
  (assert-equal (subst '(= x 1) 'q) 'q)
  (assert-equal (subst '() '(+ x 1)) '(+ 1 x)))

(deftest "subst: подставить можно только символ"
  (assert-error (subst '(= (sin x) 1) '(sin x)))
  (assert-equal (subst '(= x 2) '(+ (sin x) (cos x))) (simplify '(+ (sin 2) (cos 2)))))

; ---------- инфиксное «=» и f(a, b) ----------

(deftest "math-read: равенство"
  (assert-equal (math-read "x^2 = 4") '(= (^ x 2) 4))
  (assert-equal (math-read "x + 1 = 2y") '(= (+ x 1) (* 2 y)))
  (assert-error (math-read "a = b = c")))

(deftest "math-print: равенство и round-trip"
  (assert-equal (math-print '(= (^ x 2) 4)) "x^2 = 4")
  (assert-equal (math-print '(= x (+ 1 y))) "x = 1 + y")
  (assert-equal (math-read (math-print '(= (^ x 2) 4))) '(= (^ x 2) 4))
  ; «-1» читается как (- 0 1) — сравниваем после упрощения сторон
  (assert-equal (map simplify (cdr (math-read (math-print '(= (+ -1 x) (* 3 y)))))) '((+ -1 x) (* 3 y)))
  (assert-equal (math-print '(+ 1 (= x 2))) "1 + (x = 2)"))

(deftest "math-read/print: %i и функции нескольких аргументов"
  (assert-equal (math-read "2%i + 1") '(+ (* 2 %i) 1))
  (assert-equal (math-print '(* 2 %i)) "2%i")
  (assert-equal (math-read (math-print '(+ 1 (* 2 %i)))) '(+ 1 (* 2 %i)))
  (assert-equal (math-read "f(a, b)") '(f a b))
  (assert-equal (math-read "solve(x^2 = 4, x)") '(solve (= (^ x 2) 4) x))
  (assert-equal (math-print '(solve (= (^ x 2) 4) x)) "solve(x^2 = 4, x)")
  (assert-equal (math-read "sin(x + 1)") '(sin (+ x 1))))

; ---------- resultant ----------

(deftest "resultant: известные пары"
  (assert-equal (resultant '(+ (^ x 2) -2) '(+ (^ x 2) -3) 'x) 1)
  (assert-equal (resultant '(+ x -1) '(+ x -2) 'x) -1)
  (assert-equal (resultant '(+ (* a x) b) '(+ (* c x) d) 'x) '(+ (* a d) (* -1 b c)))
  (assert-equal (resultant '(* (+ x -1) (+ x 1)) '(* (+ x -1) (+ x 5)) 'x) 0))

(deftest "resultant: многомерные, исключение переменной"
  (assert-equal (resultant '(+ (^ x 2) (^ y 2) -1) '(+ x (* -1 y)) 'x) '(+ -1 (* 2 (^ y 2))))
  (assert-equal (resultant '(+ (* x y) -1) '(+ x y -3) 'x) '(+ 1 (* -3 y) (^ y 2)))
  ; результант по другой переменной
  (assert-equal (resultant '(+ (* x y) -1) '(+ x y -3) 'y) '(+ 1 (* -3 x) (^ x 2))))

(deftest "resultant: x^2 - 2 и x - 3 (подстановка корня), константы"
  (assert-equal (resultant '(+ (^ x 2) -2) '(+ x -3) 'x) 7)
  (assert-equal (resultant 5 '(+ x 1) 'x) 5)
  (assert-equal (resultant '(+ x 1) 7 'x) 7)
  (assert-equal (resultant 0 '(+ x 1) 'x) 0))

; ---------- nroots ----------

(deftest "nroots: x² + 1 и x² - 3x + 2"
  (assert-true (all-near? (nroots '(+ (^ x 2) 1) 'x) '((* -1 %i) %i)))
  (assert-true (all-near? (nroots '(+ 2 (* -3 x) (^ x 2)) 'x) '(1 2))))

(deftest "nroots: x³ - 1 — три корня"
  (assert-true (all-near? (nroots '(+ (^ x 3) -1) 'x)
                          (list (list '+ -1/2 (list '* (* -1 (/ (sqrt 3.0) 2)) '%i))
                                (list '+ -1/2 (list '* (/ (sqrt 3.0) 2) '%i))
                                1))))

(deftest "nroots: x⁴ + 4 — корни ±1 ± i; корень 0; степень 1"
  (assert-true (all-near? (nroots '(+ 4 (^ x 4)) 'x)
                          '((+ -1 (* -1 %i)) (+ -1 (* 1 %i)) (+ 1 (* -1 %i)) (+ 1 (* 1 %i)))))
  (assert-true (all-near? (nroots '(* x (+ x -2)) 'x) '(0 2)))
  (assert-true (all-near? (nroots '(+ (* 2 x) -1) 'x) '(0.5))))

(deftest "nroots: степень 5 без формулы — невязка мала"
  (let ((roots (nroots '(+ 1 (* -1 x) (^ x 5)) 'x)))
    (assert-equal (length roots) 5)
    ; по формулам Виета: сумма корней = 0
    (assert-true (near? (simplify (cons '+ roots)) 0))))

(deftest "nroots: float-коэффициенты, константа"
  (assert-true (all-near? (nroots '(+ -2.25 (^ x 2)) 'x) '(-1.5 1.5)))
  (assert-equal (nroots 5 'x) '()))

; ---------- real-roots ----------

(deftest "real-roots: рациональные корни остаются рациональными"
  (assert-equal (real-roots '(+ x 1/2) 'x) '(-1/2))
  (assert-equal (real-roots '(+ (^ x 4) -1) 'x) '(-1 1))
  (assert-equal (real-roots '(* (+ x -1) (+ x -2) (+ x 3)) 'x) '(-3 1 2)))

(deftest "real-roots: иррациональные — алгебраические числа"
  (let ((r (real-roots '(+ (^ x 2) -2) 'x)))
    (assert-equal (length r) 2)
    (assert-true (alg? (car r)))
    (assert-true (< (car r) 0))
    (assert-true (> (cadr r) 7/5))
    (assert-true (< (cadr r) 3/2))
    (assert-equal (simplify (list '^ (cadr r) 2)) 2)))

(deftest "real-roots: смесь, кубический неприводимый, нет вещественных"
  (let ((r (real-roots '(+ (^ x 3) (* -2 x)) 'x)))
    (assert-equal (length r) 3)
    (assert-equal (cadr r) 0))
  (assert-equal (length (real-roots '(+ (^ x 3) -2) 'x)) 1)
  (assert-equal (real-roots '(+ (^ x 2) 1) 'x) '()))

(deftest "real-roots: многочлен не только от x — ошибка"
  (assert-error (real-roots '(+ (^ x 2) y) 'x)))

(deftest "factor-list: разложение списком"
  (assert-equal (factor-list '(+ (^ x 4) -1)) '(1 ((+ -1 x) 1) ((+ 1 x) 1) ((+ 1 (^ x 2)) 1)))
  (assert-equal (factor-list '(* 2 (^ (+ x -1) 2))) '(2 ((+ -1 x) 2))))

(deftest "eval-num, num-abs, string->symbol"
  (assert-true (near? (eval-num '(+ 1 (* 2 %i))) '(+ 1 (* 2 %i))))
  (assert-true (near? (eval-num '(sin 0)) 0))
  (assert-equal (eval-num '(+ x 1)) '(+ x 1))
  (assert-equal (num-abs '(+ x 1)) #f)
  (assert-true (< (abs (- (num-abs '(* 3 %i)) 3)) 0.000001))
  (assert-equal (string->symbol "k7") 'k7))

; ---------- solve: Коммит 2 — одно уравнение ----------

; решение v удовлетворяет уравнению (подстановка даёт тождество 0 = 0 точно или численно)
(define (satisfies? eq x v)
  (let ((m (num-abs (replace-expr (solve::equation->expr eq) x v))))   ; численно (алгебраические числа не упрощаем)
    (and m (< m 0.000001))))
(define (all-satisfy? eq x s)
  (every? (lambda (v) (or (root-of? v) (satisfies? eq x v))) (set->list s)))

; --- многочлены ---

(deftest "solve: линейное уравнение, форма (= a b) и выражение (= 0)"
  (assert-equal (solve '(= (+ (* 2 x) 3) 7) 'x) (set 2))
  (assert-equal (solve '(+ (* 2 x) -6) 'x) (set 3))
  (assert-equal (solve '(= x 1/2) 'x) (set 1/2))
  (assert-true (set? (solve '(= x 1) 'x))))

(deftest "solve: квадратное с рациональными корнями"
  (assert-equal (solve '(+ 6 (* -5 x) (^ x 2)) 'x) (set 2 3))
  (assert-equal (solve '(= (* 2 (^ x 2)) 8) 'x) (set -2 2))
  (assert-equal (solve '(+ (* 2 (^ x 2)) (* -3 x) -2) 'x) (set -1/2 2))
  (assert-equal (solve '(+ (^ x 2) (* -1/2 x)) 'x) (set 0 1/2))
  (assert-equal (solve '(^ (+ x -1) 2) 'x) (set 1)))

(deftest "solve: квадратное с иррациональными корнями — алгебраические числа"
  (let ((s (solve '(+ (^ x 2) -2) 'x)))
    (assert-equal (card s) 2)
    (assert-true (every? solve::contains-radical? (set->list s)))   ; корни в радикалах (^ 2 1/2)
    (assert-true (all-satisfy? '(+ (^ x 2) -2) 'x s)))
  (let ((s (solve '(+ (^ x 2) (* -2 x) -1) 'x)))
    (assert-equal (card s) 2)
    (assert-true (all-satisfy? '(+ (^ x 2) (* -2 x) -1) 'x s))))

(deftest "solve: квадратное с комплексными корнями"
  (let ((s (solve '(+ (^ x 2) x 1) 'x)))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (v) (contains-sym? v '%i)) (set->list s)))
    (assert-true (all-satisfy? '(+ (^ x 2) x 1) 'x s)))
  (assert-equal (solve '(+ (^ x 2) 4) 'x) (set '(* 2 %i) '(* -2 %i))))

(deftest "solve: x² + 1 — вещественный и комплексный домены"
  (assert-equal (assuming ((x reals)) (solve '(+ (^ x 2) 1) 'x)) (set))
  (assert-equal (solve '(+ (^ x 2) 1) 'x) (set '%i '(* -1 %i)))
  (assert-equal (solve (math-read "x^2 = -1") 'x) (set '%i '(* -1 %i))))

(deftest "solve: кубическое с рациональными корнями"
  (assert-equal (solve '(+ -1 (* 6 x) (* -11 (^ x 2)) (* 6 (^ x 3))) 'x) (set 1/3 1/2 1))
  (assert-equal (solve '(* (+ x -1) (+ x -2) (+ x 3)) 'x) (set -3 1 2)))

(deftest "solve: кубическое неприводимое — алгебраическое число и root-of"
  (let ((s (solve '(+ (^ x 3) -2) 'x)))
    (assert-equal (card s) 2)
    (assert-true (member? '(root-of (+ -2 (^ x 3)) x) (set->list s)))
    (assert-true (any? alg? (set->list s))))
  (let ((r (assuming ((x reals)) (solve '(+ (^ x 3) -2) 'x))))
    (assert-equal (card r) 1)
    (assert-true (alg? (car (set->list r))))
    (assert-equal (simplify (list '^ (car (set->list r)) 3)) 2)))

(deftest "solve: x^4 - 1, x^6 - 1, биквадратное"
  (assert-equal (solve '(+ (^ x 4) -1) 'x) (set -1 1 '%i '(* -1 %i)))
  (assert-equal (assuming ((x reals)) (solve '(+ (^ x 4) -1) 'x)) (set -1 1))
  (assert-equal (card (solve '(+ (^ x 6) -1) 'x)) 6)
  (assert-equal (solve '(+ 4 (* -5 (^ x 2)) (^ x 4)) 'x) (set -2 -1 1 2)))

(deftest "solve: x^5 - 1 — рациональный корень и root-of"
  (assert-equal (solve '(+ (^ x 5) -1) 'x) (set 1 '(root-of (+ 1 x (^ x 2) (^ x 3) (^ x 4)) x))))

; --- рациональные уравнения ---

(deftest "solve: рациональное уравнение — посторонний корень (знаменатель)"
  (assert-equal (solve '(= (/ x (- x 1)) (/ 1 (- x 1))) 'x) (set))
  (assert-equal (solve '(/ (- (^ x 2) 1) (- x 1)) 'x) (set -1))
  (assert-equal (solve '(= (/ (+ x 2) (- x 2)) 0) 'x) (set -2)))

(deftest "solve: рациональное уравнение с корнями"
  (let ((s (solve '(+ (/ 1 x) (/ 1 (+ x 1)) -1) 'x)))
    (assert-equal (card s) 2)
    (assert-true (all-satisfy? '(+ (/ 1 x) (/ 1 (+ x 1)) -1) 'x s)))
  (assert-equal (solve '(= (/ 1 x) 4) 'x) (set 1/4)))

; --- тождество, противоречие ---

(deftest "solve: тождество — домен переменной, противоречие — пустое множество"
  (assert-equal (solve '(= x x) 'x) complexes)
  (assert-equal (solve '(= (+ x 1) (+ 1 x)) 'x) complexes)
  (assert-equal (assuming ((x reals)) (solve '(= x x) 'x)) reals)
  (assert-equal (assuming ((x positive)) (solve '(= 0 0) 'x)) positive)
  (assert-equal (solve '(= 1 2) 'x) (set))
  (assert-equal (solve 5 'x) (set)))

; --- символьные коэффициенты ---

(deftest "solve: символьные коэффициенты — формулы"
  (assert-equal (solve '(= (+ (* a x) b) 0) 'x) (set '(* -1 (^ a -1) b)))
  (assert-equal (solve '(= (+ (^ x 2) (* -1 (^ a 2))) 0) 'x) (set 'a '(* -1 a)))
  (assert-equal (solve '(= (+ (* 2 x) y) 3) 'x) (set '(* 1/2 (+ 3 (* -1 y))))))

(deftest "solve: a·x² + b·x + c — две формулы с (sqrt D)"
  (let ((s (solve '(+ (* a (^ x 2)) (* b x) c) 'x)))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (v) (contains-sym? v 'sqrt)) (set->list s)))
    ; подстановка a=1, b=-3, c=2 даёт корни 1 и 2
    (let ((vals (map (lambda (v) (eval-num (subst '((= a 1) (= b -3) (= c 2)) v))) (set->list s))))
      (assert-true (every? (lambda (v) (or (near? v 1) (near? v 2))) vals))
      (assert-true (not (near? (car vals) (cadr vals)))))))

(deftest "solve: символьный многочлен степени 3 — root-of"
  (assert-equal (solve '(= (+ (^ x 3) (* -1 a)) 0) 'x) (set '(root-of (+ a (* -1 (^ x 3))) x))))

; --- обращение функций ---

(deftest "solve: exp и степень с показателем x"
  (assert-equal (solve '(- (exp x) 5) 'x) (set '(log 5)))
  (assert-equal (solve '(= (exp x) 1) 'x) (set 0))
  (assert-equal (solve '(= (^ 2 x) 8) 'x) (set 3))
  (assert-equal (solve '(= (exp (+ x 1)) 5) 'x) (set '(+ -1 (log 5)))))

(deftest "solve: exp(u) = отрицательное — главная ветвь только в ℂ"
  (assert-equal (assuming ((x reals)) (solve '(= (exp x) -2) 'x)) (set))
  (assert-equal (solve '(= (exp x) -2) 'x) (set '(+ (* %i pi) (log 2))))
  (assert-equal (solve '(= (exp x) 0) 'x) (set)))

(deftest "solve: log"
  (assert-equal (solve '(- (log x) 2) 'x) (set '(exp 2)))
  (assert-equal (solve '(= (log (+ x 1)) 2) 'x) (set '(+ -1 (exp 2)))))

(deftest "solve: exp(2x) — через (exp x)^2"
  (assert-equal (solve '(+ (exp (* 2 x)) (* -3 (exp x)) 2) 'x) (set 0 '(log 2)))
  (assert-equal (assuming ((x reals)) (solve '(= (exp (* 2 x)) 4) 'x)) (set '(log 2))))

(deftest "solve: sqrt, посторонний корень"
  (assert-equal (solve '(= (sqrt x) 3) 'x) (set 9))
  (assert-equal (solve '(= (sqrt x) -3) 'x) (set))
  (assert-equal (solve '(= (sqrt (+ x 2)) x) 'x) (set 2))
  (assert-equal (solve '(= (^ x 1/2) x) 'x) (set 0 1))
  (assert-equal (solve '(= (+ (sqrt (- x 1)) 1) (sqrt (+ x 4))) 'x) (set 5)))

(deftest "solve: sin — серии решений с целым параметром k"
  (let ((s (solve '(= (sin x) 0) 'x)))
    (assert-equal s (set '(* 2 k1 pi) '(+ pi (* 2 k1 pi))))
    (assert-equal (in? 'k1 integers) #t))
  (assert-equal (solve '(= (sin x) 1/2) 'x)
                (set '(+ (* 1/6 pi) (* 2 k1 pi)) '(+ (* 5/6 pi) (* 2 k1 pi))))
  (assert-equal (solve '(= (sin x) 1) 'x) (set '(+ (* 1/2 pi) (* 2 k1 pi)))))

(deftest "solve: cos, tan, аргумент — линейная функция"
  (assert-equal (solve '(= (cos x) 1/2) 'x)
                (set '(+ (* -1/3 pi) (* 2 k1 pi)) '(+ (* 1/3 pi) (* 2 k1 pi))))
  (assert-equal (solve '(= (tan x) 1) 'x) (set '(+ (* 1/4 pi) (* k1 pi))))
  (assert-equal (solve '(= (sin (* 2 x)) 1/2) 'x)
                (set '(+ (* 1/12 pi) (* k1 pi)) '(+ (* 5/12 pi) (* k1 pi)))))

(deftest "solve: sin x = 2 — нет вещественных решений"
  (assert-equal (assuming ((x reals)) (solve '(= (sin x) 2) 'x)) (set))
  (assert-equal (card (solve '(= (sin x) 2) 'x)) 2))

(deftest "solve: подстановка по ядру sin²x − sin x = 0"
  (assert-equal (solve '(- (^ (sin x) 2) (sin x)) 'x)
                (set '(* 2 k1 pi) '(+ pi (* 2 k1 pi)) '(+ (* 1/2 pi) (* 2 k2 pi)))))

(deftest "solve: степень и корень от выражения с x"
  (assert-equal (solve '(= (^ (+ x 1) 3) 8) 'x) (solve '(= (+ (^ x 3) (* 3 (^ x 2)) (* 3 x) -7) 0) 'x))
  (assert-equal (card (solve '(= (exp (^ x 2)) 5) 'x)) 2)
  (assert-equal (solve '(= (abs x) 3) 'x) (set -3 3))
  (assert-equal (solve '(= (abs x) -3) 'x) (set)))

; --- домены ---

(deftest "solve: домены отбрасывают решения"
  (assert-equal (assuming ((x positive)) (solve '(= (^ x 2) 4) 'x)) (set 2))
  (assert-equal (assuming ((x negative)) (solve '(= (^ x 2) 4) 'x)) (set -2))
  (assert-equal (assuming ((x naturals)) (solve '(+ (^ x 2) (* -1 x) -2) 'x)) (set 2))
  (assert-equal (assuming ((x integers)) (solve '(+ (^ x 2) (* -1 x) -1/2) 'x)) (set))
  (assert-equal (assuming ((x (interval 0 1))) (solve '(+ (^ x 2) (* -1 x) -2) 'x)) (set))
  (assert-equal (assuming ((x positive)) (solve '(+ (^ x 2) 4) 'x)) (set)))

(deftest "solve: вещественный домен и иррациональные корни"
  (let ((s (assuming ((x positive)) (solve '(+ (^ x 2) -2) 'x))))
    (assert-equal (card s) 1)
    (assert-true (> (eval-num (car (set->list s))) 1))))

; --- инфиксный ввод и проверка подстановкой ---

(deftest "solve: инфиксный ввод"
  (assert-equal (solve (math-read "x^2 = 4") 'x) (set -2 2))
  (assert-equal (solve (math-read "2x + 3 = 7") 'x) (set 2))
  (assert-equal (solve (math-read "x^2 - 5x + 6 = 0") 'x) (set 2 3))
  (assert-equal (solve (math-read "exp(x) = 5") 'x) (set '(log 5))))

(deftest "solve: решения подставляются в уравнение — тождество"
  (assert-equal (subst (list '= 'x 2) '(- (+ (^ x 2) 1) 5)) 0)
  (assert-true (all-satisfy? '(+ (^ x 3) (* -6 (^ x 2)) (* 11 x) -6) 'x (solve '(+ (^ x 3) (* -6 (^ x 2)) (* 11 x) -6) 'x)))
  (assert-true (all-satisfy? '(+ (^ x 4) (* -2 (^ x 2)) -1) 'x (solve '(+ (^ x 4) (* -2 (^ x 2)) -1) 'x)))
  (assert-true (all-satisfy? '(= (sqrt (+ x 3)) x) 'x (solve '(= (sqrt (+ x 3)) x) 'x))))

; --- ошибки ---

(deftest "solve: не умеем — ошибка, а не пустое множество"
  (assert-error (solve '(+ x (cos x)) 'x))
  (assert-error (solve '(= (* x (exp x)) 1) 'x))
  (assert-error (solve '(= x 1) 5))
  (assert-error (solve 'y 'x)))

; ---------- solve: Коммит 3 — системы уравнений ----------

; решение системы с параметрами при числовых значениях параметров pt ((= a 2) ...): невязка ~ 0
(define (sol-ok-at? eqs sol pt)
  (sol-satisfies? (map (lambda (e) (subst pt e)) eqs)
                  (map (lambda (e) (list '= (cadr e) (subst pt (caddr e)))) sol)))

(define (sol-satisfies? eqs sol)
  (every? (lambda (e)
            (let ((m (solve::residual (solve::equation->expr e) sol))) (and m (< m 0.000001))))
          eqs))

(deftest "solve: линейная система 2×2"
  (assert-equal (solve (list '(= (+ x y) 3) '(= (- x y) 1)) '(x y))
                (set '((= x 2) (= y 1)))))

(deftest "solve: линейная 3×3"
  (assert-equal (solve (list '(= (+ x y z) 6) '(= (- x y) 0) '(= (+ x (* 2 z)) 7)) '(x y z))
                (set '((= x 5/3) (= y 5/3) (= z 8/3))))
  (assert-equal (solve (list '(= (+ x (* 2 y) z) 4) '(= (- x y) 1) '(= (* 2 z) 2)) '(x y z))
                (set '((= x 5/3) (= y 2/3) (= z 1)))))

(deftest "solve: порядок переменных как в запросе"
  (assert-equal (solve (list '(= (+ x y) 3) '(= (- x y) 1)) '(y x))
                (set '((= y 1) (= x 2)))))

(deftest "solve: несовместная линейная система"
  (assert-equal (solve (list '(= (+ x y) 3) '(= (+ x y) 4)) '(x y)) (set))
  (assert-equal (solve (list '(= x 1) '(= x 2)) '(x)) (set)))

(deftest "solve: недоопределённая — свободные переменные остаются символами"
  (assert-equal (solve (list '(= (+ x y) 3) '(= (* 2 (+ x y)) 6)) '(x y))
                (set '((= x (+ 3 (* -1 y))) (= y y))))
  (assert-equal (solve (list '(= (+ x y z) 1)) '(x y z))
                (set '((= x (+ 1 (* -1 y) (* -1 z))) (= y y) (= z z)))))

(deftest "solve: недоопределённое решение применимо через subst"
  (let ((sol (car (set->list (solve (list '(= (+ x y) 3)) '(x y))))))
    (assert-equal (subst sol '(+ x y)) 3)))

(deftest "solve: символьная линейная система 2×2"
  (let* ((s (solve (list '(= (+ (* a x) (* b y)) e) '(= (+ (* c x) (* d y)) f)) '(x y)))
         (sol (car (set->list s))))
    (assert-equal (card s) 1)
    ; подстановка найденного решения в оба уравнения даёт тождество
    (assert-equal (together (subst sol '(- (+ (* a x) (* b y)) e))) 0)
    (assert-equal (together (subst sol '(- (+ (* c x) (* d y)) f))) 0)))

(deftest "solve: система с одним уравнением и одной переменной"
  (assert-equal (solve (list '(= (* 2 x) 6)) '(x)) (set '((= x 3))))
  (assert-equal (solve '(= (* 2 x) 6) '(x)) (set '((= x 3)))))

(deftest "solve: нелинейная 2×2 — окружность и прямая"
  (let* ((eqs (list '(= (+ (^ x 2) (^ y 2)) 1) '(= x y)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (sol) (sol-satisfies? eqs sol)) (set->list s)))))

(deftest "solve: нелинейная 2×2 — x·y = 1 и x + y = 3"
  (let* ((eqs (list '(= (* x y) 1) '(= (+ x y) 3)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (sol) (sol-satisfies? eqs sol)) (set->list s)))))

(deftest "solve: нелинейная 2×2 с рациональными решениями"
  (assert-equal (solve (list '(= (+ (^ x 2) (^ y 2)) 5) '(= (* x y) 2)) '(x y))
                (set '((= x -2) (= y -1)) '((= x -1) (= y -2)) '((= x 1) (= y 2)) '((= x 2) (= y 1))))
  (assert-equal (solve (list '(= (+ (^ x 2) y) 3) '(= y 2)) '(x y))
                (set '((= x -1) (= y 2)) '((= x 1) (= y 2)))))

(deftest "solve: нелинейная система без решений и комплексные решения"
  (assert-equal (solve (list '(= (+ (^ x 2) (^ y 2)) 1) '(= (+ x y) 5)) '(x y)) (solve (list '(= (+ (^ x 2) (^ y 2)) 1) '(= (+ x y) 5)) '(x y)))
  (assert-equal (assuming ((x reals) (y reals)) (solve (list '(= (+ (^ x 2) (^ y 2)) 1) '(= (+ x y) 5)) '(x y))) (set)))

(deftest "solve: домены переменных системы"
  (assert-equal (assuming ((x positive)) (solve (list '(= (* x y) 1) '(= (+ x y) 2)) '(x y)))
                (set '((= x 1) (= y 1))))
  (assert-equal (assuming ((x positive)) (solve (list '(= (^ x 2) 4) '(= y x)) '(x y)))
                (set '((= x 2) (= y 2)))))

(deftest "solve: систему в инфиксе и ошибки"
  (assert-equal (solve (list (math-read "x + y = 3") (math-read "x - y = 1")) '(x y))
                (set '((= x 2) (= y 1))))
  ; раньше — ошибка («только через root-of»); с шага 21i'' (3) — ответ с root-of для неразрешимых в радикалах ветвей
  (assert-true (> (card (solve (list '(= (+ (^ x 3) y) 1) '(= (+ x (^ y 3)) 1) '(= z 1)) '(x y z))) 0))
  (assert-error (solve (list '(= (+ (sin x) y) 1) '(= x y)) '(x y)))
  (assert-error (solve (list '(= x 1)) '())))

;; ---------- шаг 21i: нелинейные системы через базис Грёбнера ----------

(deftest "solve: система 3×3 через базис Грёбнера (симметрическая)"
  (assert-equal (solve (list '(= (+ (^ x 2) (^ y 2) (^ z 2)) 6) '(= (+ x y z) 4) '(= (* x y z) 2)) '(x y z))
                (set '((= x 1) (= y 1) (= z 2)) '((= x 1) (= y 2) (= z 1)) '((= x 2) (= y 1) (= z 1)))))

(deftest "solve: katsura-3 — четыре решения, подстановка в систему"
  (let* ((eqs (list '(+ x0 (* 2 x1) (* 2 x2) -1) '(+ (^ x0 2) (* 2 (^ x1 2)) (* 2 (^ x2 2)) (* -1 x0))
                    '(+ (* 2 x0 x1) (* 2 x1 x2) (* -1 x1))))
         (s (solve eqs '(x0 x1 x2))))
    (assert-equal (card s) 4)
    (assert-true (member? '((= x0 1) (= x1 0) (= x2 0)) (set->list s)))
    (assert-true (every? (lambda (sol) (sol-satisfies? eqs sol)) (set->list s)))))

(deftest "solve: система с решениями — алгебраическими числами (вещественные корни степени 4)"
  ; x² + y = 3, y² + x = 3 (по lex: многочлен от y степени 4 с иррациональными корнями)
  (let* ((eqs (list '(= (+ (^ x 2) y) 3) '(= (+ (^ y 2) x) 3)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 4)
    (assert-true (every? (lambda (sol) (sol-satisfies? eqs sol)) (set->list s)))))

(deftest "solve: несовместная нелинейная система — пустое множество"
  (assert-equal (solve (list '(= (* x y) 1) '(= x 0)) '(x y)) (set))
  (assert-equal (solve (list '(= (^ x 2) 1) '(= (^ x 2) 2) '(= y 0)) '(x y)) (set)))

(deftest "solve: кратный корень системы — одно решение"
  (assert-equal (solve (list '(^ x 2) '(- y 1)) '(x y)) (set '((= x 0) (= y 1)))))

(deftest "solve: бесконечно много решений нелинейной системы — ошибка"
  (assert-error (solve (list '(= (* x y) 1)) '(x y)))
  (assert-error (solve (list '(= (^ x 2) 1)) '(x y))))

;; ---------- шаг 21i'' (3): root-of в системах и параметры ----------

; решение, в котором root-of f v заменён вещественным корнем f: невязка системы ~ 0 (многочлены от корня верны для всех корней f)
(define (sol-ok-real-root? eqs sol)
  (let* ((ro (caddr (car (filter (lambda (e) (root-of? (caddr e))) sol))))
         (r (car (real-roots (cadr ro) (caddr ro))))
         (sol2 (map (lambda (e) (list '= (cadr e) (replace-expr (caddr e) ro r))) sol)))
    (sol-satisfies? eqs sol2)))

; решения системы: с root-of (невещественные корни) и явные (вещественные)
(define (nonreal-sols s) (filter (lambda (sol) (contains-sym? sol 'root-of)) (set->list s)))
(define (real-sols s) (filter (lambda (sol) (not (contains-sym? sol 'root-of))) (set->list s)))

(deftest "solve: root-of в системе — x³ − x − 1 = 0, y = x²: вещественный корень явно, root-of — остальные"
  (let* ((eqs (list '(+ (^ x 3) (* -1 x) -1) '(- y (^ x 2))))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-equal (length (real-sols s)) 1)
    (assert-true (sol-satisfies? eqs (car (real-sols s))))       ; x, y — алгебраические числа
    (assert-true (alg? (caddr (car (car (real-sols s))))))
    (let ((sol (car (nonreal-sols s))))
      (assert-equal (cadr (car sol)) 'x)
      (assert-equal (cadr (cadr sol)) 'y)
      (assert-true (root-of? (caddr (cadr sol))))      ; y = root-of(...), x — многочлен от корня
      (assert-true (sol-ok-real-root? eqs sol)))))

(deftest "solve: root-of в системе — порядок переменных меняет представление, не множество решений"
  (let* ((eqs (list '(+ (^ x 3) (* -1 x) -1) '(- y (^ x 2))))
         (s (solve eqs '(y x))))
    (assert-equal (card s) 2)
    (assert-true (sol-satisfies? eqs (car (real-sols s))))
    (assert-true (sol-ok-real-root? eqs (car (nonreal-sols s))))))

(deftest "solve: root-of в системе — многочлен степени 5 и рациональные ветви"
  (let* ((eqs (list '(+ (^ x 5) (* -1 x) -1) '(- (+ y (* -1 (^ x 2))) 3)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (sol-satisfies? eqs (car (real-sols s))))
    (assert-true (sol-ok-real-root? eqs (car (nonreal-sols s)))))
  ; рациональные корни остаются числами, вещественный иррациональный — алгебраическое число, остаток — root-of
  (let* ((eqs (list '(* (+ x -1) (+ (^ x 3) (* -1 x) -1)) '(- y x)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 3)
    (assert-equal (length (nonreal-sols s)) 1)
    (assert-true (member? '((= x 1) (= y 1)) (set->list s)))))

; шаг 21i'' (3′), п. 1: то же соглашение, что у одного уравнения (вещественные корни явно, root-of — остальные)
(deftest "solve: единое соглашение root-of — система y = x совпадает с одним уравнением"
  (let* ((one (set->list (solve '(+ (^ x 3) -2) 'x)))
         (s (solve (list '(+ (^ x 3) -2) '(- y x)) '(x y))))
    (assert-equal (length one) 2)                       ; алгебраическое число и (root-of ...)
    (assert-equal (card s) 2)
    (assert-equal (map (lambda (sol) (caddr (car sol))) (real-sols s)) (list (car (filter alg? one))))
    (assert-true (root-of? (caddr (car (car (nonreal-sols s))))))))

; п. 3: подстановка вещественного алгебраического корня степени 5 в многочлены (раньше — зависание)
(deftest "solve: x⁵ − x − 1 = 0 в системе — вещественный корень подставляется за секунды"
  (let* ((eqs (list '(+ (^ x 5) (* -1 x) -1) '(- y (^ x 4))))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (sol-satisfies? eqs (car (real-sols s)))))
  ; причина зависания — цепочка Штурма без сокращения содержимого: α⁵ = α + 1 для корня α многочлена x⁵ − x − 1
  (let ((a (car (real-roots '(+ (^ x 5) (* -1 x) -1) 'x))))
    (assert-true (< (num-abs (- (* a a a a a) (+ a 1))) 0.000001))))

; п. 2: декларации доменов в системах (вещественные неизвестные — без невещественных решений)
(deftest "solve: декларации доменов фильтруют решения системы"
  (let* ((eqs (list '(+ (^ x 3) (* -1 x) -1) '(- y (^ x 2))))
         (s (assuming ((x reals) (y reals)) (solve eqs '(x y)))))
    (assert-equal (card s) 1)
    (assert-true (sol-satisfies? eqs (car (set->list s)))))
  (assert-equal (assuming ((x reals) (y reals)) (solve (list '(+ (^ x 2) 1) '(- y x)) '(x y))) (set))
  (assert-equal (solve (list '(+ (^ x 2) 1) '(- y x)) '(x y)) (set '((= x %i) (= y %i)) '((= x (* -1 %i)) (= y (* -1 %i)))))
  (assert-equal (assuming ((x reals) (y reals)) (solve (list '(+ (^ x 3) -2) '(- y x)) '(x y)))
                (set (list (list '= 'x (car (real-roots '(+ (^ x 3) -2) 'x))) (list '= 'y (car (real-roots '(+ (^ x 3) -2) 'x)))))))

; п. 4: string-contains?
(deftest "string-contains?: подстрока в строке"
  (assert-true (string-contains? "система несовместна" "совместна"))
  (assert-equal (string-contains? "abc" "abd") #f)
  (assert-equal (string-contains? "ABC" "abc") #f)
  (assert-true (string-contains? "abc" ""))
  (assert-error (string-contains? "abc" 5)))

(deftest "solve: root-of в системе — отказы с понятной причиной"
  ; y² = x над ℚ(корень): уравнение второй степени по y — не умеем
  (let ((r (try (solve (list '(+ (^ x 3) (* -1 x) -1) '(- (^ y 2) x)) '(y x)) (lambda (e) (error-message e)))))
    (assert-true (string-contains? r "определяется уравнением степени 2")))
  ; иррациональные значения последующих неизвестных
  (assert-error (solve (list '(+ (^ y 2) -2) '(+ (^ x 3) (* -1 x) (* -1 y))) '(x y))))

(deftest "solve: параметры — x² + y² = r², x = y"
  (let* ((eqs (list '(= (+ (^ x 2) (^ y 2)) (^ r 2)) '(= x y)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (sol) (sol-ok-at? eqs sol '((= r 3)))) (set->list s)))
    (assert-true (every? (lambda (sol) (sol-ok-at? eqs sol '((= r 5/2)))) (set->list s)))))

(deftest "solve: параметры — x·y = a, x + y = b"
  (let* ((eqs (list '(= (* x y) a) '(= (+ x y) b)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (sol) (sol-ok-at? eqs sol '((= a 2) (= b 5)))) (set->list s)))
    (assert-true (every? (lambda (sol) (sol-ok-at? eqs sol '((= a 3) (= b 4)))) (set->list s)))))

(deftest "solve: параметры — a·x² + y = 1, x + y = 0 и окружность с прямой y = a·x"
  (let* ((eqs (list '(= (+ (* a (^ x 2)) y) 1) '(= (+ x y) 0)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (sol) (sol-ok-at? eqs sol '((= a 2)))) (set->list s))))
  (let* ((eqs (list '(= (+ (^ x 2) (^ y 2)) 1) '(= (* a x) y)))
         (s (solve eqs '(x y))))
    (assert-equal (card s) 2)
    (assert-true (every? (lambda (sol) (sol-ok-at? eqs sol '((= a 2)))) (set->list s)))))

(deftest "solve: параметры — несовместная система (единичный идеал) и совместная лишь при особых значениях"
  (assert-equal (solve (list '(= (+ (^ x 2) (^ y 2)) a) '(= (+ (^ x 2) (^ y 2)) (+ a 1))) '(x y)) (set))
  (assert-equal (solve (list '(= (* x y) a) '(= (* x y) (+ a 1))) '(x y)) (set))
  ; x·y = a и x·y = 2 совместны только при a = 2: ответа «пусто» для общих a недостаточно — отказ с условием
  (let ((r (try (solve (list '(= (* x y) a) '(= (* x y) 2)) '(x y)) (lambda (e) (error-message e)))))
    (assert-true (string-contains? r "совместна только при особых значениях параметров"))
    (assert-true (string-contains? r "-2 + a = 0")))
  (let ((r (try (solve (list '(= (+ (* a x) y) 1) '(= (^ x 2) 1) '(= (^ y 2) 1)) '(x y)) (lambda (e) (error-message e)))))
    (assert-true (string-contains? r "совместна только при особых значениях параметров"))
    (assert-true (string-contains? r "a^3 = 0"))))

(deftest "solve: параметры — отказы (root-of при параметрах, бесконечно много решений)"
  (let ((r (try (solve (list '(= (+ (^ x 3) (* -1 x) a) 0) '(= y x)) '(x y)) (lambda (e) (error-message e)))))
    (assert-true (string-contains? r "только через root-of"))
    (assert-true (string-contains? r "при параметрах")))
  (assert-error (solve (list '(= (* a x y) 1)) '(x y))))

(deftest "solve: параметры — журнал шагов фиксирует «общие значения параметров»"
  (let ((r (capture-step-log (lambda () (solve (list '(= (* x y) a) '(= (+ x y) b)) '(x y))))))
    (assert-equal (step-rules (cadr r)) '(polynomial-system parametric-basis groebner-basis generic-parameters))
    (assert-equal (step-title (step-find 'generic-parameters (cadr r))) "Ответ для общих значений параметров")))

(deftest "solve: журнал — рамка polynomial-system, треугольный вид (lex-базис)"
  (let ((r (capture-step-log (lambda () (solve (list '(= (+ (^ x 2) (^ y 2)) 5) '(= (* x y) 2)) '(x y))))))
    (assert-equal (step-rules (cadr r)) '(polynomial-system triangular-system groebner-basis fglm))
    (assert-equal (length (step-after (car (cadr r)))) 4)))

(deftest "solve: журнал — запасной путь (не многочлены) не оставляет рамки polynomial-system"
  (let ((r (capture-step-log (lambda () (try (solve (list '(= (+ x (exp y)) 1) '(= (- x (exp y)) 0)) '(x y)) (lambda (e) 'нет))))))
    (assert-equal (step-find 'polynomial-system (cadr r)) #f)))

; ---------- квадратные корни в радикалах (символьный (^ n 1/2)) ----------

(deftest "solve: x^2 = 2 и x^2 = 8 — корни в радикалах"
  (assert-equal (solve '(= (^ x 2) 2) 'x) (set '(^ 2 1/2) '(* -1 (^ 2 1/2))))
  (assert-equal (solve '(= (^ x 2) 8) 'x) (set '(* 2 (^ 2 1/2)) '(* -2 (^ 2 1/2)))))

(deftest "solve: x^2 - 2x - 1 = 0 — 1 ± √2; x^2 + 2 = 0 — ±√2·%i"
  (assert-equal (solve '(+ (^ x 2) (* -2 x) -1) 'x) (set '(+ 1 (^ 2 1/2)) '(+ 1 (* -1 (^ 2 1/2)))))
  (assert-equal (solve '(+ (^ x 2) 2) 'x) (set '(* (^ 2 1/2) %i) '(* -1 (^ 2 1/2) %i))))

(deftest "solve: смешанный (x²-2)(x-3); проверка подстановкой радикалов"
  (assert-equal (solve '(* (+ (^ x 2) -2) (+ x -3)) 'x) (set '(^ 2 1/2) 3 '(* -1 (^ 2 1/2))))
  (assert-equal (subst '(= x (^ 2 1/2)) '(+ (^ x 2) -2)) 0)
  (assert-equal (assuming ((x positive)) (solve '(= (^ x 2) 2) 'x)) (set '(^ 2 1/2))))

(deftest "simplify: вынос квадратного множителя; примитивный многочлен алгебраического числа"
  (assert-equal (simplify '(^ 8 1/2)) '(* 2 (^ 2 1/2)))
  (assert-equal (simplify '(^ 12 1/2)) '(* 2 (^ 3 1/2)))
  (assert-equal (simplify '(^ 2 1/2)) '(^ 2 1/2))
  (assert-equal (simplify '(^ 18 1/2)) '(* 3 (^ 2 1/2)))
  (assert-equal (real-roots '(+ (* 4 (^ x 2)) -8) 'x) (real-roots '(+ (^ x 2) -2) 'x)))
