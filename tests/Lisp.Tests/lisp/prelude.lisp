; Lisp-тесты prelude: списочные функции, try/error (Шаг 15b)

(deftest "map"
  (assert-equal (map (lambda (x) (* x x)) '(1 2 3)) '(1 4 9))
  (assert-equal (map car '()) '()))

(deftest "filter"
  (assert-equal (filter (lambda (x) (> x 1)) '(1 2 3)) '(2 3))
  (assert-equal (filter (lambda (x) #f) '(1 2)) '()))

(deftest "foldl"
  (assert-equal (foldl + 0 '(1 2 3 4)) 10)
  (assert-equal (foldl (lambda (acc x) (cons x acc)) '() '(1 2 3)) '(3 2 1)))

(deftest "reverse"
  (assert-equal (reverse '(1 2 3)) '(3 2 1))
  (assert-equal (reverse '()) '()))

(deftest "range"
  (assert-equal (range 4) '(0 1 2 3))
  (assert-equal (range 0) '()))

(deftest "every? и any?"
  (assert-true (every? integer? '(1 2 3)))
  (assert-true (not (every? integer? '(1 a))))
  (assert-true (any? symbol? '(1 a)))
  (assert-true (not (any? symbol? '(1 2)))))

(deftest "хвостовая рекурсия на 100000 итераций"
  (define (count n acc) (if (= n 0) acc (count (- n 1) (+ acc 1))))
  (assert-equal (count 100000 0) 100000))

(deftest "try: значение без ошибки"
  (assert-equal (try (+ 1 2) (lambda (e) 'oops)) 3))

(deftest "try: обработчик получает объект ошибки"
  (assert-equal (try (error "плохо" 42) error-message) "плохо 42")
  (assert-true (try (error "x") error?)))

(deftest "raise и error-data"
  (assert-equal (try (raise '(код 7)) error-data) '(код 7))
  (assert-true (null? (try (error "без данных") error-data))))

(deftest "assert-error ловит ошибку"
  (assert-error (car 5))
  (assert-error (error "boom"))
  (assert-error (/ 1 0)))

; шаг 21i: сортировка слиянием (устойчивая)
(deftest "sort: числа, устойчивость, пустой список"
  (assert-equal (sort '(3 1 2 5 4 1) <) '(1 1 2 3 4 5))
  (assert-equal (sort '() <) '())
  (assert-equal (sort '(7) <) '(7))
  (assert-equal (sort '((1 a) (0 b) (1 c) (0 d)) (lambda (p q) (< (car p) (car q)))) '((0 b) (0 d) (1 a) (1 c)))
  (assert-equal (sort (range 100) >) (reverse (range 100))))

; Шаг D3b: assert-equal — путь первого различия и подсказка равности по значению
(deftest "assert-equal: путь первого различия"
  (define (err-msg e) (error-message e))
  (assert-true (string-contains? (err-msg (try (assert-equal '(+ x 1) '(+ x 2)) (lambda (e) e)))
                                "первое различие в (2): получено 1, ожидалось 2"))
  (assert-true (string-contains? (err-msg (try (assert-equal '(+ (* 2 x) 3) '(+ (* 2 y) 3)) (lambda (e) e)))
                                "первое различие в (1 2): получено x, ожидалось y"))
  ; разные головы / длины — путь () (различие в корне)
  (assert-true (string-contains? (err-msg (try (assert-equal '(* 2 x) '(+ 2 x)) (lambda (e) e)))
                                "первое различие в (): получено (* 2 x)"))
  (assert-true (string-contains? (err-msg (try (assert-equal '(1 2) '(1 2 3)) (lambda (e) e)))
                                "первое различие в (): получено (1 2), ожидалось (1 2 3)")))

(deftest "assert-equal: разность simplify = 0 — другая форма"
  (define (err-msg2 e) (error-message e))
  (assert-true (string-contains? (err-msg2 (try (assert-equal '(+ x x) '(* 2 x)) (lambda (e) e)))
                                "равны по значению, другая форма"))
  ; разность не 0 — подсказки нет
  (assert-true (not (string-contains? (err-msg2 (try (assert-equal '(+ x 1) '(+ x 2)) (lambda (e) e)))
                                       "равны по значению"))))
