; Lisp-тесты конечных множеств (lib\set.lisp), Шаг 16

(deftest "конструктор: сортировка и удаление дублей"
  (assert-equal (set->list (set 3 1 2 1 3)) '(1 2 3))
  (assert-equal (set->list (set 'b 2 1 'a)) '(1 2 a b))   ; числа < символы
  (assert-equal (card (set 1 1 1)) 1)
  (assert-equal (set->list (list->set '(5 4 5))) '(4 5)))

(deftest "равенство множеств — equal?, порядок не важен"
  (assert-equal (set 1 2 3) (set 3 2 1))
  (assert-equal (set 'x 'y) (set 'y 'x 'x))
  (assert-equal (equal? (set 1 2) (set 1 3)) #f))

(deftest "set?, card, empty-set?"
  (assert-equal (set? (set 1)) #t)
  (assert-equal (set? '(1 2)) #f)
  (assert-equal (set? 5) #f)
  (assert-equal (card (set)) 0)
  (assert-equal (card (set 1 2 3)) 3)
  (assert-equal (empty-set? (set)) #t)
  (assert-equal (empty-set? (set 1)) #f))

(deftest "печать множеств"
  (assert-equal (to-string (set 2 1 'x)) "{1, 2, x}")
  (assert-equal (to-string (set)) "{}")
  (assert-equal (math-print (set 1 '(^ x 2))) "{1, x^2}"))

(deftest "union"
  (assert-equal (union (set 1 2) (set 2 3)) (set 1 2 3))
  (assert-equal (union (set 1) (set 2) (set 3) (set 1)) (set 1 2 3))
  (assert-equal (union (set) (set 'a)) (set 'a))
  (assert-equal (union) (set)))

(deftest "intersection"
  (assert-equal (intersection (set 1 2 3) (set 2 3 4)) (set 2 3))
  (assert-equal (intersection (set 1 2 3) (set 2 3 4) (set 3 4 5)) (set 3))
  (assert-equal (intersection (set 1 2) (set 3 4)) (set))
  (assert-equal (intersection (set 'x 'y) (set 'y 'z)) (set 'y)))

(deftest "set-difference"
  (assert-equal (set-difference (set 1 2 3) (set 2)) (set 1 3))
  (assert-equal (set-difference (set 1 2) (set 1 2 3)) (set))
  (assert-equal (set-difference (set 1 2) (set)) (set 1 2)))

(deftest "in? для множеств: #t / #f / unknown"
  (assert-equal (in? 2 (set 1 2 3)) #t)
  (assert-equal (in? 'x (set 'x 1)) #t)
  (assert-equal (in? 5 (set 1 2 3)) #f)           ; все числа — совпадений нет
  (assert-equal (in? 'x (set)) #f)                ; пустое множество
  (assert-equal (in? 'z (set 'x 'y)) unknown)     ; символы могут оказаться равны
  (assert-equal (in? 1 (set 'x 2)) unknown)       ; в множестве есть символ
  (assert-equal (in? 'x (set 1 2)) unknown)       ; x может быть равен 1
  (assert-equal (in? 1.0 (set 1 2)) #t)           ; числа сравниваются по значению
  (assert-equal (in? '(+ a b) (set 1)) unknown))

(deftest "subset? для множеств"
  (assert-equal (subset? (set 1 2) (set 1 2 3)) #t)
  (assert-equal (subset? (set 1 4) (set 1 2 3)) #f)
  (assert-equal (subset? (set) (set 1)) #t)
  (assert-equal (subset? (set 1 2) (set 1 2)) #t)
  (assert-equal (subset? (set 'x) (set 'x 'y)) #t))

(deftest "subset? с символьными элементами: unknown"
  (assert-equal (subset? (set 'x) (set 'y)) unknown)
  (assert-equal (subset? (set 'x 1) (set 1 2)) unknown)
  ; но #f, если какой-то числовой элемент заведомо не входит
  (assert-equal (subset? (set 'x 5) (set 1 2)) #f))

(deftest "set-map и set-filter"
  (assert-equal (set-map (lambda (x) (* x x)) (set -2 -1 0 1 2)) (set 0 1 4))
  (assert-equal (set-map (lambda (x) (+ x 1)) (set 1 2)) (set 2 3))
  (assert-equal (set-filter (lambda (x) (> x 1)) (set 1 2 3)) (set 2 3))
  (assert-equal (set-filter (lambda (x) (> x 10)) (set 1 2 3)) (set)))

(deftest "power-set"
  (assert-equal (card (power-set (set 1 2 3))) 8)
  (assert-equal (power-set (set)) (set (set)))
  (assert-equal (power-set (set 1 2)) (set (set) (set 1) (set 2) (set 1 2)))
  (assert-equal (to-string (power-set (set 'a))) "{{}, {a}}"))

(deftest "множество множеств; элементы-выражения"
  (assert-equal (card (set (set 1) (set 1) (set 2))) 2)
  (assert-equal (card (set '(+ x 1) '(+ x 1) 'x)) 2)
  (assert-equal (in? (set 1) (set (set 1) (set 2))) #t))

(deftest "set->list вне множества — ошибка"
  (assert-error (set->list 5)))

; WASM.6a Д7: пересечение множества с интервалом и доменом
(deftest "WASM.6a Д7: множество ∩ интервал/домен"
  (assert-equal (intersection (set 2 5) (interval 0 3)) (set 2))
  (assert-equal (intersection (interval 0 3) (set 2 5)) (set 2))
  (assert-equal (intersection (set 1 2 3) (interval 2 3)) (set 2 3))
  (assert-equal (intersection (set 1 2 3) (interval 2 3 'open 'open)) (set))
  (assert-equal (intersection (set -1 1/2 3) nonnegative) (set 1/2 3))
  (assert-equal (intersection (set 1 2 3) (set 3 4) (interval 0 4)) (set 3)))
