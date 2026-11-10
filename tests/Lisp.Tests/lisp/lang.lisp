; lang.lisp — тесты шагов LANG.1 (ядро: строки, хеш-таблицы, числа, именованный let, печать float)
; и LANG.2 (управляющие формы, delay/force, потоки). Тесты файла делят окружение.

; ---------- LANG.1: строки ----------

(deftest "LANG: строки — length, substring, string-ref"
  (assert-equal 5 (string-length "hello"))
  (assert-equal "ell" (substring "hello" 1 4))
  (assert-equal "lo" (substring "hello" 3))
  (assert-equal "c" (string-ref "abc" 2))
  (assert-equal 0 (string-length "")))

(deftest "LANG: строки — string->list, list->string, upcase/downcase, сравнения"
  (assert-equal '("a" "b" "c") (string->list "abc"))
  (assert-equal "abc" (list->string '("a" "b" "c")))
  (assert-equal "ABC" (string-upcase "aBc"))
  (assert-equal "abc" (string-downcase "aBc"))
  (assert-true (string=? "ab" "ab"))
  (assert-true (string<? "ab" "ac"))
  (assert-true (string? "s"))
  (assert-true (not (string? 5))))

(deftest "LANG: строки — split, join, index"
  (assert-equal '("a" "b" "c") (string-split "a,b,c" ","))
  (assert-equal "a-b-c" (string-join '("a" "b" "c") "-"))
  (assert-equal 2 (string-index "hello" "ll"))
  (assert-true (not (string-index "hello" "zz")))
  (assert-equal "x,y" (string-join (string-split "x,y" ",") ",")))

(deftest "LANG: string->number точен (дробь 1/3), не-число — #f; number->string"
  (assert-equal 1/3 (string->number "1/3"))
  (assert-equal 42 (string->number "42"))
  (assert-true (not (string->number "abc")))
  (assert-equal "1/3" (number->string 1/3))
  (assert-equal "42" (number->string 42)))

(deftest "LANG: string-append требует строки; format ~a/~s"
  (assert-equal "ab" (string-append "a" "b"))
  (assert-error (string-append "a" 5))
  (assert-equal "x5-y\"z\"" (format "x~a-y~s" 5 "z"))
  (assert-equal "a~b" (format "a~~b"))
  (assert-equal 3 (string-length (format "a~%b"))))

(deftest "LANG: индекс вне строки — ошибка"
  (assert-error (string-ref "abc" 5))
  (assert-error (substring "abc" 1 9)))

; ---------- LANG.1: хеш-таблицы ----------

(deftest "LANG: хеш — set/ref/has/remove/count/keys, ключи по equal?"
  (let ((h (make-hash)))
    (hash-set! h 'a 1)
    (assert-equal 1 (hash-ref h 'a))
    (assert-true (hash-has? h 'a))
    (hash-set! h 'b 2)
    (assert-equal 2 (hash-count h))
    (hash-remove! h 'a)
    (assert-true (not (hash-has? h 'a)))
    (assert-equal 1 (hash-count h))
    (assert-equal '(b) (hash-keys h))))

(deftest "LANG: хеш — структурные ключи: выражения, рационалы 1/2=2/4, 1 и 1.0 различны"
  (let ((h (make-hash)))
    (hash-set! h '(+ x 1) 42)
    (assert-equal 42 (hash-ref h '(+ x 1)))
    (hash-set! h 1/2 'a)
    (hash-set! h 2/4 'b)
    (assert-equal 2 (hash-count h))
    (assert-equal 'b (hash-ref h 1/2))
    (hash-set! h 1 'int)
    (hash-set! h 1.0 'flt)
    (assert-equal 4 (hash-count h))
    (assert-equal 'flt (hash-ref h 1.0))
    (assert-equal 'int (hash-ref h 1))))

(deftest "LANG: хеш — умолчание при отсутствии ключа"
  (let ((h (make-hash)))
    (assert-true (not (hash-ref h 'nope)))
    (assert-equal 99 (hash-ref h 'nope 99))))

; ---------- LANG.1: числа ----------

(deftest "LANG: (^ q n) точно для рациональных и отрицательных n"
  (assert-equal 1/4 (^ 1/2 2))
  (assert-equal 1/4 (^ 2 -2))
  (assert-equal 1/8 (^ 2 -3))
  (assert-equal 4/9 (^ 2/3 2))
  (assert-equal 27/8 (^ 3/2 3)))

(deftest "LANG: abs на дроби — точная дробь"
  (assert-equal 3/4 (abs -3/4))
  (assert-equal 3/4 (abs 3/4)))

(deftest "LANG: round/truncate — половина от нуля / к нулю"
  (assert-equal 2 (round 3/2))
  (assert-equal -2 (round -3/2))
  (assert-equal 4 (round 7/2))
  (assert-equal 1 (round 5/4))
  (assert-equal -3 (truncate -7/2))
  (assert-equal 3 (truncate 7/2))
  (assert-equal 2 (ceiling 3/2))
  (assert-equal 1 (floor 3/2)))

(deftest "LANG: even?/odd?/zero?/positive-number?"
  (assert-true (even? 4))
  (assert-true (not (even? 5)))
  (assert-true (odd? 7))
  (assert-true (zero? 0))
  (assert-true (not (zero? 1/2)))
  (assert-true (positive-number? 1/2))
  (assert-true (not (positive-number? -1/2))))

(deftest "LANG: exact->inexact"
  (assert-equal 0.5 (exact->inexact 1/2))
  (assert-true (< 0.3333333 (exact->inexact 1/3) 0.33333334)))

(deftest "LANG: цепочечные сравнения"
  (assert-true (< 1 2 3))
  (assert-true (not (< 1 3 2)))
  (assert-true (<= 1 1 2))
  (assert-true (>= 3 3 1))
  (assert-true (> 3 2 1))
  (assert-true (= 2 2 2))
  (assert-true (not (= 2 2 3))))

(deftest "LANG: печать float отличима от целого"
  (assert-equal "2.0" (number->string 2.0))
  (assert-equal "2" (number->string 2)))

; ---------- LANG.1: именованный let ----------

(deftest "LANG: именованный let — сумма 0..9"
  (assert-equal 45 (let loop ((i 0) (acc 0))
                     (if (< i 10) (loop (+ i 1) (+ acc i)) acc))))

(deftest "LANG: именованный let — хвостовая рекурсия на 10^6 без роста стека"
  (let ((n 0))
    (set! n (let loop ((i 0)) (if (< i 1000000) (loop (+ i 1)) i)))
    (assert-equal 1000000 n)))

(deftest "LANG: именованный let — имя цикла не затеняет внешнюю переменную"
  (define (lang-named-outer) (let loop ((i 0)) (if (< i 3) (loop (+ i 1)) i)))
  (assert-equal 3 (lang-named-outer))
  ; обычный let не сломан
  (assert-equal 7 (let ((x 7)) x)))

; ---------- LANG.1: переопределение builtin — ошибка ----------

(deftest "LANG: define поверх builtin на верхнем уровне — ошибка; set! — явный путь"
  (assert-error (eval '(define (car x) x)))
  (define lang-car-orig car)
  (set! car (lambda (x) 'mine))
  (assert-equal 'mine (car '(1 2)))
  (set! car lang-car-orig)
  (assert-equal 1 (car '(1 2))))

; ---------- LANG.1: memoize на make-hash ----------

(deftest "LANG: memoize (dp) — повторный вызов с теми же аргументами из кэша"
  (defmemo (lang-fib n) (if (< n 2) n (+ (lang-fib (- n 1)) (lang-fib (- n 2)))))
  (assert-equal 832040 (lang-fib 30)))

; ---------- LANG.2: управляющие формы ----------

(deftest "LANG: when/unless — тело только при истинном/ложном условии, пустое тело — nil"
  (assert-equal 2 (when #t 1 2))
  (assert-equal '() (when #f 1 2))
  (assert-true (null? (when #t)))
  (assert-equal 7 (unless #f 7))
  (assert-equal '() (unless #t 7)))

(deftest "LANG: макросы не захватывают имена пользователя"
  (let ((tmp 1))
    (assert-equal 1 (when #t tmp)))
  (let ((r 5))
    ; тело delay использует свои ячейки; внешнее r не затеняется
    (assert-equal 5 (force (delay r)))))

(deftest "LANG: for-each — применение ради эффекта, порядок сохранён"
  (define lang-fe-log '())
  (for-each (lambda (x) (set! lang-fe-log (cons x lang-fe-log))) '(1 2 3))
  (assert-equal '(3 2 1) lang-fe-log)
  (assert-equal '() (for-each (lambda (x) x) '(1 2))))

(deftest "LANG: while — цикл до ложного условия"
  (let ((i 0) (acc 0))
    (while (< i 5)
      (set! acc (+ acc i))
      (set! i (+ i 1)))
    (assert-equal 10 acc))
  (let ((n 0))
    (while #f (set! n 1))
    (assert-equal 0 n)))

(deftest "LANG: do (как в Scheme) — шаги и результат; переменная без шага не меняется"
  (assert-equal 10 (do ((i 0 (+ i 1)) (acc 0 (+ acc i))) ((= i 5) acc)))
  (assert-equal 3 (do ((i 0 (+ i 1))) ((= i 3) i)))
  (assert-equal '(5 5) (do ((i 0 (+ i 1)) (k 5)) ((= i 5) (list k i))))
  (let ((lang-do-log '()))
    (do ((i 0 (+ i 1))) ((= i 2) (length lang-do-log))
      (set! lang-do-log (cons i lang-do-log)))))

(deftest "LANG: gensym — свежие уникальные символы"
  (let ((a (gensym)) (b (gensym)))
    (assert-true (symbol? a))
    (assert-true (not (equal? a b))))
  (assert-true (symbol? (gensym "m"))))

; ---------- LANG.2: delay/force и потоки ----------

(deftest "LANG: delay/force — мемоизация: тело вычисляется один раз"
  (define lang-df-count 0)
  (let ((p (delay (begin (set! lang-df-count (+ lang-df-count 1)) 42))))
    (assert-equal 42 (force p))
    (assert-equal 42 (force p))
    (assert-equal 42 (force p))
    (assert-equal 1 lang-df-count)))

(deftest "LANG: cons-stream — хвост ленивый; stream-take/car/cdr"
  (define (lang-ints n) (cons-stream n (lang-ints (+ n 1))))
  (assert-equal '(0 1 2 3 4) (stream-take (lang-ints 0) 5))
  (assert-equal 0 (stream-car (lang-ints 0)))
  (assert-equal 1 (stream-car (stream-cdr (lang-ints 0))))
  (assert-true (stream-null? '())))

(deftest "LANG: stream-map, stream-filter на бесконечном потоке"
  (define (lang-ints2 n) (cons-stream n (lang-ints2 (+ n 1))))
  (assert-equal '(0 4 16 36 64)
                (stream-take (stream-map (lambda (x) (* x x))
                                         (stream-filter (lambda (x) (= 0 (remainder x 2))) (lang-ints2 0))) 5)))

(deftest "LANG: бесконечный поток простых (решето на stream-filter)"
  (define (lang-nats n) (cons-stream n (lang-nats (+ n 1))))
  (define (lang-sift s)
    (let ((p (stream-car s)))
      (cons-stream p (lang-sift (stream-filter (lambda (x) (not (= 0 (remainder x p)))) (stream-cdr s))))))
  (assert-equal '(2 3 5 7 11 13 17 19 23 29) (stream-take (lang-sift (lang-nats 2)) 10)))
