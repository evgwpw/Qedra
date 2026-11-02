; Lisp-тесты AC-сопоставления (lib\match.lisp), шаг AC.1.
; Выражения даны в той форме, которую подаёт вызывающий (canonical или нет): ac-match не вызывает simplify,
; а инвариант подстановки сверяется уже после simplify обеих сторон.

(define (mt-has? sol l) (member? sol l))

; инвариант: для каждого решения (simplify (ac-subst образец привязки)) = (simplify выражение)
(define (mt-invariant? pat e)
  (let ((sols (ac-match-all pat e)))
    (and (list? sols)
         (every? (lambda (b) (equal? (simplify (ac-subst pat b)) (simplify e))) sols))))

(deftest "ac-match: * с сегментной — все упорядоченные пары"
  (let ((all (ac-match-all '(* ?a ?b ?r...) '(* 2 x y))))
    (assert-equal (length all) 6)
    (assert-true (mt-has? '((?a 2) (?b x) (?r... y)) all))
    (assert-true (mt-has? '((?a y) (?b 2) (?r... x)) all))
    (assert-equal (car all) '((?a 2) (?b x) (?r... y)))
    (assert-equal (ac-match '(* ?a ?b ?r...) '(* 2 x y)) '((?a 2) (?b x) (?r... y)))))

(deftest "ac-match: обычная переменная — ровно один аргумент"
  (assert-equal (ac-match '(* ?a ?b) '(* 2 x y)) #f)
  (assert-equal (ac-match-all '(* ?a ?b) '(* 2 x y)) '())
  (assert-equal (length (ac-match-all '(* ?a ?b ?c) '(* 2 x y))) 6)
  (assert-equal (length (ac-match-all '(* ?a ?b) '(* x y))) 2))

(deftest "ac-match: sin^2 + cos^2 среди лишних слагаемых"
  (let ((pat '(+ (^ (sin ?u) 2) (^ (cos ?u) 2) ?r...)))
    (assert-equal (ac-match pat '(+ 1 y (^ (sin x) 2) (^ (cos x) 2))) '((?u x) (?r... (+ 1 y))))
    (assert-equal (ac-match pat '(+ (^ (cos x) 2) y (^ (sin x) 2))) '((?u x) (?r... y)))
    (assert-equal (ac-match pat '(+ (^ (sin x) 2) (^ (cos x) 2))) '((?u x) (?r... 0)))
    (assert-equal (ac-match pat '(+ (^ (sin x) 2) (^ (cos z) 2) y)) #f)
    (assert-equal (ac-match pat '(+ (^ (sin x) 2) y)) #f)))

(deftest "ac-match: повторная переменная"
  (let ((pat '(+ ?x (* ?c ?x))))
    (assert-equal (ac-match pat '(+ x (* a x))) '((?x x) (?c a)))
    (assert-equal (ac-match pat '(+ (* a x) x)) '((?x x) (?c a)))
    (assert-equal (ac-match pat '(+ 1 y x (* a x))) #f)
    (assert-equal (ac-match '(+ ?x (* ?c ?x) ?r...) '(+ 1 y x (* a x))) '((?x x) (?c a) (?r... (+ 1 y))))
    (assert-equal (ac-match pat '(+ x (* a y))) #f)
    (assert-equal (ac-match '(+ ?x ?x) '(+ x y)) #f)
    (assert-equal (ac-match '(* ?x (sin ?x)) '(* y (sin y))) '((?x y)))
    (assert-equal (ac-match '(* ?x (sin ?x)) '(* y (sin z))) #f)))

(deftest "ac-match: пустая сегментная — нейтральный элемент"
  (assert-equal (ac-match '(* ?c... (sin ?u)) '(sin x)) '((?c... 1) (?u x)))
  (assert-equal (ac-match '(+ ?r... (sin ?u)) '(sin x)) '((?r... 0) (?u x)))
  (assert-equal (ac-match '(* ?c... (sin ?u)) '(* 2 (sin x))) '((?c... 2) (?u x)))
  (assert-equal (ac-match '(* ?c... (sin ?u)) '(* 2 (sin x) (cos x))) '((?c... (* 2 (cos x))) (?u x)))
  (assert-equal (ac-match '(* ?c... (sin ?u)) '(cos x)) #f)
  (assert-equal (ac-match '(+ x y ?r...) '(+ x)) #f)
  (assert-equal (ac-match '(+ x y ?r...) '(+ y x)) '((?r... 0))))

(deftest "ac-match: константы образца — обычные аргументы"
  (assert-equal (ac-match '(* 2 ?a) '(* 2 x)) '((?a x)))
  (assert-equal (ac-match '(* 2 ?a) '(* 3 x)) #f)
  (assert-equal (ac-match '(* 2 ?a ?r...) '(* 2 x y)) '((?a x) (?r... y)))
  (assert-equal (ac-match '(+ 1 ?a) '(+ x 1)) '((?a x))))

(deftest "ac-match: вложенные AC внутри функций и друг в друге"
  (assert-equal (length (ac-match-all '(sin (+ ?a ?b)) '(sin (+ x y)))) 2)
  (assert-equal (length (ac-match-all '(^ (+ ?a ?r...) 2) '(^ (+ x y z) 2))) 3)
  (assert-equal (ac-match '(^ (+ ?a ?r...) 2) '(^ (+ x y z) 3)) #f)
  (assert-equal (ac-match '(sin (* ?n pi ?r...)) '(sin (* 2 n pi))) '((?n 2) (?r... n)))
  (assert-equal (ac-match '(exp (* ?a (cos ?u))) '(exp (* 3 (cos (+ x y))))) '((?a 3) (?u (+ x y))))
  ; (+ ?b ?r...) подходит и к одному аргументу (остаток пуст), поэтому решений 4
  (let ((all (ac-match-all '(* ?a (+ ?b ?r...)) '(* 2 (+ 1 x y)))))
    (assert-equal (length all) 4)
    (assert-true (mt-has? '((?a 2) (?b 1) (?r... (+ x y))) all))
    (assert-true (mt-has? '((?a (+ 1 x y)) (?b 2) (?r... 0)) all))))

(deftest "ac-match: неAC-узлы позиционно, как match-bindings"
  (assert-equal (ac-match '(sin ?a) '(sin x)) '((?a x)))
  (assert-equal (ac-match '(f ?a ?b) '(f 1 2)) '((?a 1) (?b 2)))
  (assert-equal (ac-match '(f ?a ?b) '(f 1)) #f)
  (assert-equal (ac-match '(^ ?x ?n) '(^ y 3)) '((?x y) (?n 3)))
  (assert-equal (ac-match '(^ ?x ?n) '(^ 3 y)) '((?x 3) (?n y)))
  (assert-equal (ac-match '(sin ?a) '(cos x)) #f)
  (assert-equal (ac-match '(* ?a ?b) '(+ x y)) #f)
  (assert-equal (ac-match 'x 'x) '())
  (assert-equal (ac-match 'x 'y) #f)
  (assert-equal (ac-match '(= ?l ?r) '(= (+ x 1) 2)) '((?l (+ x 1)) (?r 2)))
  (assert-equal (ac-match '(+ ?a (* ?b x)) '(+ 1 (* 3 x))) (match-bindings '(+ ?a (* ?b x)) '(+ 1 (* 3 x)))))

(deftest "ac-match: вычитание, деление, вложенные суммы"
  (assert-equal (ac-match '(- ?a ?b) '(- x y)) '((?a x) (?b y)))
  (assert-equal (ac-match '(- ?a ?b) '(+ x (* -1 y))) '((?a x) (?b y)))
  (assert-equal (ac-match '(/ ?a ?b) '(* x (^ y -1))) '((?a x) (?b y)))
  (assert-true (list? (ac-match '(+ ?a ?b ?c) '(+ x (+ y z)))))
  (assert-equal (length (ac-match-all '(+ ?a ?b ?c) '(+ x (+ y z)))) 6))

(deftest "ac-match-all: без дублей, порядок фиксирован"
  (let ((a (ac-match-all '(+ ?a ?b) '(+ x y))) (b (ac-match-all '(+ ?a ?b) '(+ x y))))
    (assert-equal a '(((?a x) (?b y)) ((?a y) (?b x))))
    (assert-equal a b))
  (assert-equal (ac-match-all '(+ ?a ?b) '(+ x x)) '(((?a x) (?b x))))
  (assert-equal (ac-match-all '(sin ?a) '(cos x)) '()))

(deftest "ac-match: порядок аргументов выражения не влияет на множество решений"
  (let ((s1 (ac-match-all '(* ?a ?b ?r...) '(* 2 x y)))
        (s2 (ac-match-all '(* ?a ?b ?r...) '(* y 2 x))))
    (assert-equal (length s1) (length s2))
    (assert-true (every? (lambda (s) (mt-has? s s2)) s1))))

(deftest "ac-match: лимит перебора — #f и условие, а не «нет совпадения»"
  (let* ((e '(+ a b c d e f g h i j k l))
         (hard '(+ ?a ?b ?c ?d ?e ?f ?g ?g ?r...))
         (r (capture-conditions (lambda () (ac-match hard e)))))
    ; решения нет, но чтобы убедиться, нужен большой перебор: по умолчанию 10000 — отказ
    (assert-equal (car r) #f)
    (assert-equal (length (cadr r)) 1)
    (assert-equal (car (car (cadr r))) '(ac-match-limit 10000)))
  ; искусственно маленький лимит у ac-match-all и ac-match
  (let ((r (capture-conditions (lambda () (ac-match-all '(+ ?a ?b ?c ?d ?r...) '(+ a b c d e f g h) 50)))))
    (assert-equal (car r) #f)
    (assert-equal (car (car (cadr r))) '(ac-match-limit 50)))
  (let ((r (capture-conditions (lambda () (ac-match '(+ ?a ?b ?c ?d ?c ?r...) '(+ a b c d e f g h) 20)))))
    (assert-equal (car r) #f)
    (assert-equal (length (cadr r)) 1))
  ; хватило лимита — условий нет, решения полные
  (let ((r (capture-conditions (lambda () (ac-match-all '(+ ?a ?b) '(+ x y) 50)))))
    (assert-equal (length (car r)) 2)
    (assert-equal (cadr r) '()))
  ; первое решение находится быстро и при большой сумме
  (assert-equal (ac-match '(+ ?a ?b ?c ?d ?e ?f ?r...) '(+ a b c d e f g h i j k l))
                '((?a a) (?b b) (?c c) (?d d) (?e e) (?f f) (?r... (+ g h i j k l)))))

(deftest "ac-subst: подстановка, разворот сегментной, канонизация"
  (assert-equal (ac-subst '(* ?c... (sin ?u)) '((?c... 1) (?u x))) '(sin x))
  (assert-equal (ac-subst '(* ?c... (sin ?u)) '((?c... (* 2 y)) (?u x))) '(* 2 y (sin x)))
  (assert-equal (ac-subst '(+ ?a ?r...) '((?a x) (?r... (+ y z)))) '(+ x y z))
  (assert-equal (ac-subst '(+ ?a ?r...) '((?a x) (?r... 0))) 'x)
  (assert-equal (ac-subst '(+ ?a ?r...) '((?a x) (?r... (* 2 y)))) '(+ x (* 2 y)))
  (assert-equal (ac-subst '(+ ?b ?a) '((?a x) (?b 1))) '(+ 1 x))
  (assert-equal (ac-subst '(sin ?u) '((?u (+ x y)))) '(sin (+ x y)))
  ; непривязанная переменная остаётся
  (assert-equal (ac-subst '(+ ?a ?b) '((?a x))) '(+ ?b x)))

(deftest "инвариант: (ac-subst образец привязки) = выражение для каждого решения"
  (assert-true (mt-invariant? '(* ?a ?b ?r...) '(* 2 x y)))
  (assert-true (mt-invariant? '(+ (^ (sin ?u) 2) (^ (cos ?u) 2) ?r...) '(+ 1 y (^ (sin x) 2) (^ (cos x) 2))))
  (assert-true (mt-invariant? '(+ ?x (* ?c ?x) ?r...) '(+ 1 y x (* a x))))
  (assert-true (mt-invariant? '(* ?c... (sin ?u)) '(* 2 (sin x) (cos x))))
  (assert-true (mt-invariant? '(* ?c... (sin ?u)) '(sin x)))
  (assert-true (mt-invariant? '(* ?a (+ ?b ?r...)) '(* 2 (+ 1 x y))))
  (assert-true (mt-invariant? '(sin (* ?n pi ?r...)) '(sin (* 2 n pi))))
  (assert-true (mt-invariant? '(- ?a ?b) '(- x y)))
  (assert-true (mt-invariant? '(+ ?a ?b ?c) '(+ x (+ y z))))
  (assert-true (mt-invariant? '(^ (+ ?a ?r...) ?n) '(^ (+ x y z) 3))))

(deftest "ac-match: ошибки образца"
  (assert-error (ac-match '(+ ?a... ?b... x) '(+ x y)))
  (assert-error (ac-match '(sin ?a...) '(sin x)))
  (assert-error (ac-match '(f ?a... ?b) '(f 1 2))))

; ---------- Шаг AC.2: единицы (:identities) ----------

(deftest "единицы: без флага отсутствие аргумента — неудача"
  (assert-equal (ac-match '(* ?a x) 'x) #f)
  (assert-equal (ac-match '(+ x ?b) 'x) #f)
  (assert-equal (ac-match '(^ ?x ?n) 'x) #f)
  (assert-equal (ac-match '(* ?a (^ x ?n)) 'x) #f)
  (assert-equal (ac-match '(* ?a x) 'x :identities #f) #f))

(deftest "единицы: * даёт 1, + даёт 0, показатель — 1"
  (assert-equal (ac-match '(* ?a x) 'x :identities #t) '((?a 1)))
  (assert-equal (ac-match '(+ x ?b) 'x :identities #t) '((?b 0)))
  (assert-equal (ac-match '(^ ?x ?n) 'x :identities #t) '((?x x) (?n 1)))
  (assert-equal (ac-match '(* ?a (^ x ?n)) 'x :identities #t) '((?a 1) (?n 1)))
  (assert-equal (ac-match '(+ ?b (* ?c x)) 'x :identities #t) '((?b 0) (?c 1)))
  (assert-equal (ac-match '(+ ?b (* ?c (^ x ?n))) '(* 3 x) :identities #t) '((?b 0) (?c 3) (?n 1))))

(deftest "единицы: настоящие решения не затронуты, нет взрыва числа решений"
  ; аргументов хватает — единицы не нужны, решения те же, что без флага
  (assert-equal (ac-match-all '(* ?a ?b) '(* 2 x) :identities #t) (ac-match-all '(* ?a ?b) '(* 2 x)))
  (assert-equal (ac-match-all '(* ?a ?b ?r...) '(* 2 x y) :identities #t) (ac-match-all '(* ?a ?b ?r...) '(* 2 x y)))
  (assert-equal (ac-match '(* ?a ?b) '(* 2 x) :identities #t) '((?a 2) (?b x)))
  ; единица — только когда аргументов не осталось: одно решение, а не 2^k
  (assert-equal (ac-match-all '(* ?a ?b ?c) 'x :identities #t) '(((?a x) (?b 1) (?c 1))))
  (assert-equal (length (ac-match-all '(* ?a ?b ?c ?d) '(* x y) :identities #t)) 2)
  (assert-equal (ac-match-all '(* ?a ?b ?r...) 'x :identities #t) '(((?a x) (?b 1) (?r... 1))))
  ; константы образца единицей не заменяются
  (assert-equal (ac-match '(* 2 ?a) '(* 3 x) :identities #t) #f)
  (assert-equal (ac-match '(* 2 ?a) '(* 2) :identities #t) '((?a 1)))
  ; степень: настоящая степень не меняется
  (assert-equal (ac-match '(^ ?x ?n) '(^ y 3) :identities #t) '((?x y) (?n 3)))
  (assert-equal (ac-match '(* ?a (^ x ?n)) '(* 2 (^ x 3)) :identities #t) '((?a 2) (?n 3)))
  (assert-equal (ac-match '(* ?a (^ x ?n)) '(* 2 x) :identities #t) '((?a 2) (?n 1)))
  (assert-equal (ac-match '(* ?a (^ x ?n)) '(* 2 y) :identities #t) #f)
  ; повторная переменная и единица согласуются
  (assert-equal (ac-match '(* ?a ?a) 'x :identities #t) #f))

(deftest "единицы: инвариант подстановки"
  (let ((pairs '(((* ?a x) x) ((+ x ?b) x) ((* ?a (^ x ?n)) x) ((+ ?b (* ?c (^ x ?n))) (* 3 x))
                 ((^ ?x ?n) x) ((* ?a ?b ?c) x) ((* ?a ?b ?r...) x) ((* ?a (^ x ?n)) (* 2 x)))))
    (assert-true
     (every? (lambda (pe)
               (let ((sols (ac-match-all (car pe) (cadr pe) :identities #t)))
                 (and (list? sols) (not (null? sols))
                      (every? (lambda (b) (equal? (simplify (ac-subst (car pe) b)) (simplify (cadr pe)))) sols))))
             pairs))))

; ---------- Шаг AC.2: условия (:where) ----------

(deftest "условия: x-free? на коэффициенте"
  (let ((pat '(* ?c ?x)))
    (assert-equal (ac-match pat '(* 3 x) :where '(x-free? ?c 'x)) '((?c 3) (?x x)))
    ; первое решение без условия — c = x, x = 3; условие отбрасывает его и находит подходящее
    (assert-equal (ac-match pat '(* x 3)) '((?c x) (?x 3)))
    (assert-equal (ac-match pat '(* x 3) :where '(x-free? ?c 'x)) '((?c 3) (?x x)))
    (assert-equal (ac-match-all pat '(* y x) :where '(x-free? ?c 'x)) '(((?c y) (?x x))))
    (assert-equal (ac-match pat '(* x x) :where '(x-free? ?c 'x)) #f)
    (assert-equal (ac-match-all pat '(* x x) :where '(x-free? ?c 'x)) '())))

(deftest "условия: not equal?, сегментные и лимит"
  (assert-equal (ac-match-all '(+ ?a ?b) '(+ x 0) :where '(not (equal? ?a 0))) '(((?a x) (?b 0))))
  (assert-equal (ac-match '(* ?a ?r...) '(* x y) :where '(equal? ?r... 'x)) '((?a y) (?r... x)))
  ; условие-функция от привязок
  (assert-equal (ac-match '(* ?c ?x) '(* 3 x) :where (lambda (b) (equal? (cadr (car b)) 3))) '((?c 3) (?x x)))
  (assert-equal (ac-match '(* ?c ?x) '(* 3 x) :where '(lambda (b) (equal? (cadr (car b)) 4))) #f)
  ; условие #t / #f
  (assert-equal (ac-match '(+ ?a ?b) '(+ x y) :where #t) '((?a x) (?b y)))
  (assert-equal (ac-match '(+ ?a ?b) '(+ x y) :where #f) '((?a x) (?b y)))
  ; опции вместе: лимит числом, :limit и :where
  (let ((r (capture-conditions (lambda () (ac-match '(+ ?a ?b ?c ?d ?r...) '(+ a b c d e f g h) :where '(equal? ?a 'zz) 30)))))
    (assert-equal (car r) #f)
    (assert-equal (car (car (cadr r))) '(ac-match-limit 30)))
  (let ((r (capture-conditions (lambda () (ac-match-all '(+ ?a ?b) '(+ x y) :limit 50)))))
    (assert-equal (length (car r)) 2))
  (assert-error (ac-match '(+ ?a ?b) '(+ x y) ':bogus 1))
  (assert-error (ac-match '(+ ?a ?b) '(+ x y) :where)))

(deftest "условия: трёхзначность — integer-valued? и positive?"
  (let ((pat '(^ ?x ?n)))
    ; n = 3 — целое: подходит; n = 1/2 — нет (#f); n = mt2k — unknown: отбрасывается и фиксируется
    (assert-equal (ac-match pat '(^ y 3) :where '(integer-valued? ?n)) '((?x y) (?n 3)))
    (assert-equal (ac-match pat '(^ y 1/2) :where '(integer-valued? ?n)) #f)
    (assert-equal (capture-conditions (lambda () (ac-match pat '(^ y 1/2) :where '(integer-valued? ?n))))
                  '(#f ()))
    (let ((r (capture-conditions (lambda () (ac-match pat '(^ y mt2k) :where '(integer-valued? ?n))))))
      (assert-equal (car r) #f)
      (assert-equal (length (cadr r)) 1)
      (assert-equal (car (car (cadr r))) '(ac-where-unknown (integer-valued? mt2k))))
    (let ((r (capture-conditions (lambda () (ac-match-all pat '(^ y mt2k) :where '(positive? ?n))))))
      (assert-equal (car r) '())
      (assert-equal (car (car (cadr r))) '(ac-where-unknown (positive? mt2k))))
    ; unknown-кандидат не мешает найти подходящее решение (оно возвращается), но фиксируется
    (let ((r (capture-conditions (lambda () (ac-match '(+ (^ x ?n) (^ x ?m)) '(+ (^ x mt2k) (^ x 2)) :where '(integer-valued? ?n))))))
      (assert-equal (car r) '((?n 2) (?m mt2k)))
      (assert-equal (length (cadr r)) 1)
      (assert-equal (car (car (cadr r))) '(ac-where-unknown (integer-valued? mt2k))))
    ; подходящее решение найдено раньше unknown — условий нет
    (assert-equal (cadr (capture-conditions (lambda () (ac-match pat '(^ y 3) :where '(positive? ?n))))) '())))

(deftest "условия видят декларации и assuming"
  (let ((pat '(^ ?x ?n)))
    (assert-equal (ac-match pat '(^ y mt2k) :where '(integer-valued? ?n)) #f)
    (assert-equal (assuming ((mt2k integers)) (ac-match pat '(^ y mt2k) :where '(integer-valued? ?n)))
                  '((?x y) (?n mt2k)))
    (assert-equal (assuming ((mt2k positive)) (ac-match pat '(^ y mt2k) :where '(positive? ?n)))
                  '((?x y) (?n mt2k)))
    ; после assuming — снова unknown
    (assert-equal (ac-match pat '(^ y mt2k) :where '(positive? ?n)) #f)
    ; постоянная декларация
    (declare 'mt2m integers)
    (unwind-protect
      (assert-equal (ac-match pat '(^ y mt2m) :where '(integer-valued? ?n)) '((?x y) (?n mt2m)))
      (undeclare 'mt2m))))

(deftest "условия и единицы вместе"
  (assert-equal (ac-match '(* ?a (^ x ?n)) 'x :identities #t :where '(positive? ?n)) '((?a 1) (?n 1)))
  (assert-equal (ac-match '(* ?a (^ x ?n)) 'x :identities #t :where '(equal? ?n 2)) #f)
  (assert-equal (ac-match '(* ?a (^ x ?n)) '(* 2 (^ x 3)) :identities #t :where '(> ?n 1)) '((?a 2) (?n 3))))

(deftest "ac-pattern-var? и ac-segment-var?"
  (assert-true (ac-pattern-var? '?x))
  (assert-true (ac-pattern-var? '?r...))
  (assert-equal (ac-pattern-var? 'x) #f)
  (assert-equal (ac-pattern-var? 5) #f)
  (assert-true (ac-segment-var? '?r...))
  (assert-equal (ac-segment-var? '?x) #f))

; --- AC.5: поиск в подвыражениях ---

(deftest "ac-match-sub: вхождения в глубине, пути и порядок"
  (assert-equal (ac-match-sub '(sin ?u) '(+ 1 (sin x) (* 2 (sin y))))
                '(((1) ((?u x))) ((2 1) ((?u y)))))
  (assert-equal (ac-match-sub '(sin ?u) '(^ (sin x) 2)) '(((0) ((?u x)))))
  (assert-equal (ac-match-sub '(sin ?u) '(sin (sin x))) '((() ((?u (sin x)))) ((0) ((?u x)))))
  (assert-equal (ac-match-sub '(sin ?u) 'x) '())
  (assert-equal (ac-match-sub '(* 2 ?x) '(+ (* 2 a) (sin (* 2 b)))) '(((0) ((?x a))) ((1 0) ((?x b)))))
  ; само выражение — путь ()
  (assert-equal (ac-match-sub '(sin ?u) '(sin x)) '((() ((?u x))))))

(deftest "ac-match-sub: под-сумма и под-произведение с остатком"
  (let ((pat '(+ (sin ?u) (cos ?u))))
    (assert-equal (ac-match-sub pat '(+ (sin x) a (cos x))) '((() ((?u x)))))
    (assert-equal (ac-match-sub pat '(f (+ b (cos y) (sin y) a))) '(((0) ((?u y)))))
    ; точно по ac-match (без остатка) в большей сумме образец не находится
    (assert-equal (ac-match-sub pat '(+ (sin x) a (cos x)) :partial #f) '())
    (assert-equal (ac-match-sub pat '(+ (sin x) (cos x)) :partial #f) '((() ((?u x))))))
  (assert-equal (length (ac-match-sub '(* ?a ?b) '(* 2 x y))) 1)
  ; одиночный аргумент не считается суммой/произведением
  (assert-equal (ac-match-sub '(+ x ?r...) '(f x y)) '())
  (assert-equal (ac-match-sub '(+ x ?r...) '(+ x y z)) '((() ((?r... (+ y z))))))
  (assert-equal (ac-match-sub '(* 2 ?x) '(* 2 a c)) '((() ((?x a))))))

(deftest "ac-match-sub: вычитание и деление нормализуются, путь — по исходному выражению"
  (assert-equal (ac-match-sub '(+ ?a (* -1 ?b)) '(f (- p q))) '(((0) ((?a p) (?b q)))))
  (assert-equal (ac-match-sub '(* ?a (^ ?b -1)) '(g 1 (/ p q))) '(((1) ((?a p) (?b q))))))

(deftest "ac-match-sub: :where, :identities, лимит"
  (assert-equal (ac-match-sub '(sin ?u) '(+ (sin x) (sin y)) :where '(equal? ?u 'x)) '(((0) ((?u x)))))
  (assert-equal (ac-match-sub '(sin ?u) '(+ (sin x) (sin y)) :where '(equal? ?u 'z)) '())
  (assert-equal (ac-match-sub '(* ?a (^ x ?n)) '(+ x (* 3 (^ x 2))) :identities #t :where '(positive? ?n))
                '(((1) ((?a 3) (?n 2)))))
  ; :partial #f — по ac-match на каждом узле, одиночный x тоже находится (a = 1, n = 1)
  (assert-equal (ac-match-sub '(* ?a (^ x ?n)) '(+ x (* 3 (^ x 2))) :identities #t :partial #f :where '(positive? ?n))
                '(((0) ((?a 1) (?n 1))) ((1) ((?a 3) (?n 2))) ((1 1) ((?a 1) (?n 2))) ((1 1 0) ((?a 1) (?n 1)))))
  ; общий лимит на весь обход
  (let ((e '(+ (sin a) (sin b) (sin c) (sin d))))
    (assert-equal (length (ac-match-sub '(sin ?u) e)) 4)
    (let ((r (capture-conditions (lambda () (ac-match-sub '(sin ?u) e :limit 3)))))
      (assert-equal (car r) #f)
      (assert-equal (car (car (cadr r))) '(ac-match-limit 3)))
    (assert-equal (length (ac-match-sub '(sin ?u) e 200)) 4)))

(deftest "ac-replace-sub: первое и все вхождения"
  (let ((e '(+ (* 2 a) (sin (* 2 b)))))
    (assert-equal (ac-replace-sub '(* 2 ?x) '(sin ?x) e) '(+ (sin a) (sin (* 2 b))))
    (assert-equal (ac-replace-sub '(* 2 ?x) '(sin ?x) e :all #t) '(+ (sin a) (sin (sin b))))
    (assert-equal (ac-replace-sub '(cos ?x) 0 e) e)
    (assert-equal (ac-replace-sub '(sin ?x) 0 'a) 'a)
    (assert-equal (ac-replace-sub '(sin ?x) '(cos ?x) '(sin y)) '(cos y))))

(deftest "ac-replace-sub: остаток под-суммы сохраняется"
  (assert-equal (ac-replace-sub '(+ (^ (sin ?u) 2) (^ (cos ?u) 2)) 1 '(+ y (^ (sin x) 2) (^ (cos x) 2) z))
                (simplify '(+ 1 y z)))
  (assert-equal (ac-replace-sub '(+ (^ (sin ?u) 2) (^ (cos ?u) 2)) 1
                                '(f (+ (^ (sin x) 2) (^ (cos x) 2))))
                '(f 1))
  (assert-equal (ac-replace-sub '(* 2 ?x) '(sin ?x) '(* 2 a c)) (simplify '(* c (sin a))))
  (assert-equal (ac-replace-sub '(+ (^ (sin ?u) 2) (^ (cos ?u) 2)) 1
                                '(g (^ (+ q (^ (sin x) 2) (^ (cos x) 2)) 3)))
                (list 'g (list '^ (simplify '(+ 1 q)) 3))))

(deftest "ac-replace-sub: вложенная сумма разворачивается у предков; :all не заходит в замену"
  (let ((r (ac-replace-sub '(* 2 ?x) '(+ ?x 1) '(+ (* 2 a) b))))
    (assert-equal (car r) '+)
    (assert-equal (length r) 4)
    (assert-true (member? 'b r))
    (assert-true (member? 'a r)))
  (assert-equal (ac-replace-sub '(sin ?x) '(sin (sin ?x)) '(+ (sin a) (sin b)) :all #t)
                '(+ (sin (sin a)) (sin (sin b)))))

(deftest "ac-replace-sub: :where, лимит, инвариант эквивалентности"
  (assert-equal (ac-replace-sub '(sin ?u) 0 '(+ (sin x) (sin y)) :where '(equal? ?u 'y)) '(+ (sin x) 0))
  (let ((r (capture-conditions (lambda () (ac-replace-sub '(sin ?u) 0 '(+ (sin a) (sin b) (sin c)) :all #t :limit 3)))))
    (assert-equal (car r) #f)
    (assert-equal (car (car (cadr r))) '(ac-match-limit 3)))
  (let ((e '(+ (* 2 x) (sin (* a b)) (cos (* 3 c d)))))
    (assert-equal (simplify (- (ac-replace-sub '(* ?a ?b) '(* ?b ?a) e :all #t) e)) 0)
    (assert-equal (simplify (- (ac-replace-sub '(* ?a ?b) '(* ?b ?a) e) e)) 0)))

; ручной DAG: Eq (Real.sqrt (HPow.hPow ?x 2)) (abs ?x) — теорема из search-demo.dl
(define mt-nodes '((1 "#var" 0) (2 2 0) (3 "HPow.hPow" 2) (4 "Real.sqrt" 1) (5 "abs" 1) (6 "Eq" 2)))
(define mt-args '(((3 0) 1) ((3 1) 2) ((4 0) 3) ((5 0) 1) ((6 0) 4) ((6 1) 5)))
(define (mt-node-fn id) (cdr (assoc id mt-nodes)))
(define (mt-arg-fn id pos) (cadr (assoc (list id pos) mt-args)))

(deftest "pattern-from-dag: sqrt(x^2) = |x| и поиск в выражении"
  (let ((pat (pattern-from-dag 6 mt-node-fn mt-arg-fn lean-heads (lambda (id) 0))))
    (assert-equal pat '(= (sqrt (^ ?v0 2)) (abs ?v0)))
    (assert-equal (pattern-from-dag 6 mt-node-fn mt-arg-fn lean-heads) '(= (sqrt (^ ?v1 2)) (abs ?v1)))
    (assert-equal (ac-match-sub pat '(f 1 (= (sqrt (^ (+ a b) 2)) (abs (+ a b))))) '(((1) ((?v0 (+ a b))))))
    (assert-equal (ac-match-sub pat '(f 1 (= (sqrt (^ (+ a b) 2)) (abs (+ a c))))) '())
    (assert-equal (ac-replace-sub '(sqrt (^ ?v0 2)) '(abs ?v0) '(+ 1 (sqrt (^ (+ a b) 2))))
                  (simplify '(+ 1 (abs (+ a b)))))))

(deftest "pattern-from-dag: слияние + и *, головы, неизвестная голова"
  (let ((nodes '((10 "#var" 0) (11 "#var" 0) (12 "#var" 0) (13 "#var" 0) (14 "HAdd.hAdd" 2) (15 "HAdd.hAdd" 2)
                 (16 "HMul.hMul" 2) (17 "Foo.bar" 1) (18 "Real.pi" 0) (19 "HMul.hMul" 2)))
        (args '(((14 0) 10) ((14 1) 11) ((15 0) 14) ((15 1) 12) ((16 0) 15) ((16 1) 13)
                ((17 0) 18) ((19 0) 16) ((19 1) 17))))
    (let ((nf (lambda (id) (cdr (assoc id nodes))))
          (af (lambda (id pos) (cadr (assoc (list id pos) args))))
          (vf (lambda (id) (- id 10))))
      (assert-equal (pattern-from-dag 15 nf af lean-heads vf) '(+ ?v0 ?v1 ?v2))
      (assert-equal (pattern-from-dag 16 nf af lean-heads vf) '(* (+ ?v0 ?v1 ?v2) ?v3))
      (assert-equal (pattern-from-dag 19 nf af lean-heads vf) '(* (+ ?v0 ?v1 ?v2) ?v3 (Foo.bar pi)))
      (assert-equal (length (ac-match-sub (pattern-from-dag 15 nf af lean-heads vf) '(+ c a b d))) 1)
      (assert-equal (pattern-from-dag 17 nf af '(("Real.pi" tau)) vf) '(Foo.bar tau)))))

; --- AC-CACHE: кэш скомпилированных образцов (повторные вызовы, разные образцы, лимит, сброс при defrule) ---

(deftest "ac-cache: повторный вызов даёт тот же результат (успех, #f, ac-match-all, ac-subst, ac-match-sub)"
  (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(+ (* 3 (^ x 2)) 7)) '((?a 3) (?b 7)))
  (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(+ (* 3 (^ x 2)) 7)) '((?a 3) (?b 7)))
  (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(sin x)) #f)
  (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(sin x)) #f)
  (assert-equal (ac-match-all '(* ?a ?b) '(* x y)) '(((?a x) (?b y)) ((?a y) (?b x))))
  (assert-equal (ac-match-all '(* ?a ?b) '(* x y)) '(((?a x) (?b y)) ((?a y) (?b x))))
  (assert-equal (ac-subst '(+ (* ?a (^ x 2)) ?b) '((?a 2) (?b y))) '(+ (* 2 (^ x 2)) y))
  (assert-equal (ac-subst '(+ (* ?a (^ x 2)) ?b) '((?a 2) (?b y))) '(+ (* 2 (^ x 2)) y))
  (assert-equal (ac-match-sub '(* 2 x) '(+ (* 2 x) y)) '(((0) ())))
  (assert-equal (ac-match-sub '(* 2 x) '(+ (* 2 x) y)) '(((0) ()))))

(deftest "ac-cache: равные по equal? разные объекты и разные образцы не путаются"
  (let ((p1 '(+ (* ?a (^ x 2)) ?b)) (p2 (list '+ (list '* '?a (list '^ 'x 2)) '?b)))
    (assert-equal (ac-match p1 '(+ (* 3 (^ x 2)) 7)) '((?a 3) (?b 7)))
    (assert-equal (ac-match p2 '(+ (* 3 (^ x 2)) 7)) '((?a 3) (?b 7)))
    (assert-equal (ac-match '(+ x ?b) '(+ x 1)) '((?b 1)))
    (assert-equal (ac-match '(+ x ?a) '(+ x 1)) '((?a 1)))
    (assert-equal (ac-match '(+ y ?a) '(+ x 1)) #f)))

(deftest "ac-cache: переполнение (больше лимита разных образцов) — результаты верные, кэш сброшен и работает дальше"
  (define (fill i)
    (if (> i 300)
        #t
        (begin (ac-match (list '+ (list '* '?a (list '^ 'x i)) '?b) '(sin x)) (fill (+ i 1)))))
  (assert-true (fill 0))
  (assert-true (<= (length match::ac-cache) 256))
  (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(+ (* 3 (^ x 2)) 7)) '((?a 3) (?b 7)))
  (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(sin x)) #f))

(deftest "ac-cache: :where, :identities, :limit работают как раньше (условия не кэшируются)"
  (assert-equal (ac-match '(* ?a x) '(* -1 x) :identities #t) '((?a -1)))
  (assert-equal (ac-match '(* ?a x) '(* -1 x) :identities #t) '((?a -1)))
  (assert-equal (ac-match '(* x) '(* -1 x) :identities #t) #f)
  (assert-equal (ac-match '(+ x ?a) '(+ x 1) :limit 100) '((?a 1)))
  (let ((w (lambda (b) (and (equal? (cadr (assoc '?a b)) 3) #t))))
    (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(+ (* 3 (^ x 2)) 7) :where w) '((?a 3) (?b 7)))
    (assert-equal (ac-match '(+ (* ?a (^ x 2)) ?b) '(+ (* 4 (^ x 2)) 7) :where w) #f)))

(deftest "ac-cache: K-узел от simplify — константный подобразец упрощается и в кэше"
  (assert-equal (ac-match '(+ (* ?a (^ (+ 1 1) 2)) ?b) '(+ (* 3 4) 7)) '((?a 3) (?b 7)))
  (assert-equal (ac-match '(+ (* ?a (^ (+ 1 1) 2)) ?b) '(+ (* 3 4) 7)) '((?a 3) (?b 7)))
  (assert-equal (ac-match '(+ (* ?a (^ (+ 1 1) 2)) ?b) '(+ (* 3 (^ 2 2)) 7)) #f)
  (assert-equal (ac-match '(+ (* ?a (^ (+ 1 1) 2)) ?b) '(+ (* 3 (^ 2 2)) 7)) #f))

(deftest "ac-cache: после defrule кэш сбрасывается (K-узлы пересчитываются с новыми правилами)"
  (let ((ok (try (eval '(defrule acc-test-f (f (+ ?a ?b)) (* -1 (+ ?a ?b)))) (lambda (err) #f))))
    (assert-true ok)
    (assert-equal (simplify '(f (+ x y))) '(+ (* -1 x) (* -1 y)))
    ; сброс ленивый — при следующей вставке сверяется снимок (rule-names) и кэш очищается
    (let ((n (length match::ac-cache)))
      (ac-match (list 'g (list '+ 'x 'y)) (list 'g (list '+ 'x 'y)))
      (assert-true (<= (length match::ac-cache) n))
      (assert-true (> (length match::ac-cache) 0)))
    ; упрощение константного подобразца с НОВЫМ правилом: до defrule K = (h (+ x y)), после — 42, кэш сброшен
    (assert-equal (ac-match '(g6 (* ?a (acc-test-h (+ x y)))) '(g6 (* 2 (acc-test-h (+ x y))))) '((?a 2)))
    (let ((ok2 (try (eval '(defrule acc-test-h2 (acc-test-h (+ ?a ?b)) 42)) (lambda (err) #f))))
      (assert-true ok2)
      (assert-equal (ac-match '(g6 (* ?a (acc-test-h (+ x y)))) '(g6 (* 2 42))) '((?a 2))))
    (assert-true (equal? (remove-rule 'acc-test-f) #t))
    (assert-equal (simplify '(f (+ x y))) '(f (+ x y)))))
