; Lisp-тесты трёхзначной логики (lib\logic.lisp), Шаг 16

(deftest "true? / false? / known?"
  (assert-equal (true? #t) #t)
  (assert-equal (true? #f) #f)
  (assert-equal (true? unknown) #f)
  (assert-equal (true? 1) #f)          ; truthy-значение — не #t
  (assert-equal (false? #f) #t)
  (assert-equal (false? unknown) #f)
  (assert-equal (known? #t) #t)
  (assert-equal (known? #f) #t)
  (assert-equal (known? unknown) #f))

(deftest "unknown в if истинен — нужен true?"
  (assert-equal (if unknown 'yes 'no) 'yes)
  (assert-equal (if (true? unknown) 'yes 'no) 'no))

(deftest "not3"
  (assert-equal (not3 #t) #f)
  (assert-equal (not3 #f) #t)
  (assert-equal (not3 unknown) unknown))

(deftest "and3: таблица Клини"
  (assert-equal (and3 #t #t) #t)
  (assert-equal (and3 #t #f) #f)
  (assert-equal (and3 #f unknown) #f)
  (assert-equal (and3 unknown #f) #f)
  (assert-equal (and3 #t unknown) unknown)
  (assert-equal (and3 unknown unknown) unknown))

(deftest "or3: таблица Клини"
  (assert-equal (or3 #f #f) #f)
  (assert-equal (or3 #t #f) #t)
  (assert-equal (or3 #t unknown) #t)
  (assert-equal (or3 unknown #t) #t)
  (assert-equal (or3 #f unknown) unknown)
  (assert-equal (or3 unknown unknown) unknown))

(deftest "n-арные and3 / or3 и пустые вызовы"
  (assert-equal (and3 #t #t #t #t) #t)
  (assert-equal (and3 #t unknown #t #f) #f)
  (assert-equal (and3 #t unknown #t) unknown)
  (assert-equal (or3 #f #f #f unknown) unknown)
  (assert-equal (or3 #f unknown #t) #t)
  (assert-equal (and3) #t)
  (assert-equal (or3) #f)
  (assert-equal (and3-all (list #t #t)) #t)
  (assert-equal (or3-all (list #f unknown)) unknown))

(deftest "не-булевы значения считаются неопределёнными"
  (assert-equal (and3 #t 5) unknown)
  (assert-equal (or3 #f 'x) unknown)
  (assert-equal (not3 5) unknown))
