; Lisp-тесты шага 21i: базисы Грёбнера (lib\groebner.lisp). Эталоны — Беккер–Вейспфеннинг (1993),
; Cox–Little–O'Shea 2.7 и частные случаи; инварианты — нормальная форма образующих равна 0,
; все S-многочлены базиса редуцируются к 0, базис приведённый, результат не зависит от стратегии и порядка входа.

; выражение → монический многочлен в порядке ord → выражение (эталоны над ℤ не монические)
(define (gbt-monic e vars ord)
  (groebner::gb-with-order ord
    (lambda () (groebner::gb-to-expr (groebner::gb-monic (groebner::gb-from-expr e vars)) vars))))

; базис совпадает с эталоном (с точностью до нормировки и порядка элементов)
(define (gbt-same? got expected vars ord)
  (let ((ex (map (lambda (e) (gbt-monic e vars ord)) expected)))
    (and (= (length got) (length ex))
         (every? (lambda (e) (member? e got)) ex))))

(define (gbt-check fs vars ord expected)
  (let ((g (groebner fs vars ord)))
    (if (not (gbt-same? g expected vars ord))
        (begin (display "получено: ") (display (map math-print g)) (newline)))
    (assert-true (gbt-same? g expected vars ord))))

(define (gbt m) (math m))
(define (gbts l) (map math l))

; внутренние многочлены (порядок ord) для проверок инвариантов
(define (gbt-polys es vars ord)
  (groebner::gb-with-order ord (lambda () (map (lambda (e) (groebner::gb-from-expr e vars)) es))))

; инварианты: каждый исходный многочлен редуцируется к 0, базис — базис Грёбнера (S-пары → 0), приведённый
(define (gbt-invariants fs vars ord)
  (let ((g (groebner fs vars ord)))
    (groebner::gb-with-order ord
      (lambda ()
        (let ((G (map (lambda (e) (groebner::gb-from-expr e vars)) g))
              (F (map (lambda (e) (groebner::gb-from-expr e vars)) fs)))
          (assert-true (every? (lambda (f) (null? (groebner::gb-nf f G))) F))
          (assert-true (groebner::gb-groebner? G))
          (assert-true (groebner::gb-reduced? G)))))
    g))

; ---------- эталон test_groebnertools.py: _do_test_groebner ----------

(deftest "groebner: эталон 1–3 (lex, вход уже базис)"
  (gbt-check (gbts '("x^2 + 2*x*y^2" "x*y + 2*y^3 - 1")) '(x y) 'lex (gbts '("x" "y^3 - 1/2")))
  (gbt-check (gbts '("2*x^2*y + y^2" "2*x^3 + x*y - 1")) '(y x) 'lex (gbts '("y" "x^3 - 1/2")))
  (gbt-check (gbts '("x - z^2" "y - z^3")) '(x y z) 'lex (gbts '("x - z^2" "y - z^3"))))

(deftest "groebner: эталон 4 — Cox–Little–O'Shea 2.7 (grlex)"
  (gbt-check (gbts '("x^3 - 2*x*y" "x^2*y + x - 2*y^2")) '(x y) 'grlex (gbts '("x^2" "x*y" "-1/2*x + y^2"))))

(deftest "groebner: эталон 5–8 — скрученная кубика (lex, grlex)"
  (gbt-check (gbts '("-x^2 + y" "-x^3 + z")) '(x y z) 'lex (gbts '("x^2 - y" "x*y - z" "x*z - y^2" "y^3 - z^2")))
  (gbt-check (gbts '("-x^2 + y" "-x^3 + z")) '(x y z) 'grlex (gbts '("y^3 - z^2" "x^2 - y" "x*y - z" "x*z - y^2")))
  (gbt-check (gbts '("-x^2 + z" "-x^3 + y")) '(x y z) 'lex (gbts '("x^2 - z" "x*y - z^2" "x*z - y" "y^2 - z^3")))
  (gbt-check (gbts '("-x^2 + z" "-x^3 + y")) '(x y z) 'grlex (gbts '("-y^2 + z^3" "x^2 - z" "x*y - z^2" "x*z - y"))))

(deftest "groebner: эталон 9–16 (lex, grlex)"
  (gbt-check (gbts '("x - y^2" "-y^3 + z")) '(x y z) 'lex (gbts '("x - y^2" "y^3 - z")))
  (gbt-check (gbts '("x - y^2" "-y^3 + z")) '(x y z) 'grlex (gbts '("x^2 - y*z" "x*y - z" "-x + y^2")))
  (gbt-check (gbts '("x - z^2" "y - z^3")) '(x y z) 'lex (gbts '("x - z^2" "y - z^3")))
  (gbt-check (gbts '("x - z^2" "y - z^3")) '(x y z) 'grlex (gbts '("x^2 - y*z" "x*z - y" "-x + z^2")))
  (gbt-check (gbts '("-y^2 + z" "x - y^3")) '(x y z) 'lex (gbts '("x - y*z" "y^2 - z")))
  (gbt-check (gbts '("-y^2 + z" "x - y^3")) '(x y z) 'grlex (gbts '("-x^2 + z^3" "x*y - z^2" "y^2 - z" "-x + y*z")))
  (gbt-check (gbts '("y - z^2" "x - z^3")) '(x y z) 'lex (gbts '("x - z^3" "y - z^2")))
  (gbt-check (gbts '("y - z^2" "x - z^3")) '(x y z) 'grlex (gbts '("-x^2 + y^3" "x*z - y^2" "-x + y*z" "-y + z^2"))))

(deftest "groebner: эталон 17 — рациональные коэффициенты (lex)"
  (gbt-check (gbts '("4*x^2*y^2 + 4*x*y + 1" "x^2 + y^2 - 1")) '(x y z) 'lex
             (gbts '("x - 4*y^7 + 8*y^5 - 7*y^3 + 3*y" "y^8 - 2*y^6 + 3/2*y^4 - 1/2*y^2 + 1/16"))))

(deftest "groebner: бенчмарк minpoly (lex, форма shape lemma)"
  (gbt-check (gbts '("x^3 + x + 1" "y^2 + y + 1" "(x + y)*z - (x^2 + y)")) '(x y z) 'lex
             (gbts '("x + 155/2067*z^5 - 355/689*z^4 + 6062/2067*z^3 - 3687/689*z^2 + 6878/2067*z - 25/53"
                     "y + 4/53*z^5 - 91/159*z^4 + 523/159*z^3 - 387/53*z^2 + 1043/159*z - 308/159"
                     "z^6 - 7*z^5 + 41*z^4 - 82*z^3 + 89*z^2 - 46*z + 13"))))

(define gbt-k3 (gbts '("x0 + 2*x1 + 2*x2 - 1" "x0^2 + 2*x1^2 + 2*x2^2 - x0" "2*x0*x1 + 2*x1*x2 - x1")))
(define gbt-k4 (gbts '("x0 + 2*x1 + 2*x2 + 2*x3 - 1" "x0^2 + 2*x1^2 + 2*x2^2 + 2*x3^2 - x0"
                       "2*x0*x1 + 2*x1*x2 + 2*x2*x3 - x1" "x1^2 + 2*x0*x2 + 2*x1*x3 - x2")))

(deftest "groebner: katsura-3 (эталон, lex и grlex)"
  (gbt-check gbt-k3 '(x0 x1 x2) 'lex
             (gbts '("-7 + 7*x0 + 8*x2 + 158*x2^2 - 420*x2^3" "7*x1 + 3*x2 - 79*x2^2 + 210*x2^3"
                     "x2 + x2^2 - 40*x2^3 + 84*x2^4")))
  (gbt-check gbt-k3 '(x0 x1 x2) 'grlex
             (gbts '("7*x1 + 3*x2 - 79*x2^2 + 210*x2^3" "-x1 + x2 - 3*x2^2 + 5*x1^2"
                     "-x1 - 4*x2 + 10*x1*x2 + 12*x2^2" "-1 + x0 + 2*x1 + 2*x2"))))

(deftest "groebner: katsura-4 (эталон, lex — 4 элемента, grlex — 8)"
  (gbt-check gbt-k4 '(x0 x1 x2 x3) 'lex
             (gbts '("5913075*x0 - 159690237696*x3^7 + 31246269696*x3^6 + 27439610544*x3^5 - 6475723368*x3^4 - 838935856*x3^3 + 275119624*x3^2 + 4884038*x3 - 5913075"
                     "1971025*x1 - 97197721632*x3^7 + 73975630752*x3^6 - 12121915032*x3^5 - 2760941496*x3^4 + 814792828*x3^3 - 1678512*x3^2 - 9158924*x3"
                     "5913075*x2 + 371438283744*x3^7 - 237550027104*x3^6 + 22645939824*x3^5 + 11520686172*x3^4 - 2024910556*x3^3 - 132524276*x3^2 + 30947828*x3"
                     "128304*x3^8 - 93312*x3^7 + 15552*x3^6 + 3144*x3^5 - 1120*x3^4 + 36*x3^3 + 15*x3^2 - x3")))
  (gbt-check gbt-k4 '(x0 x1 x2 x3) 'grlex
             (gbts '("393*x1 - 4662*x2^2 + 4462*x2*x3 - 59*x2 + 224532*x3^4 - 91224*x3^3 - 678*x3^2 + 2046*x3"
                     "-x1 + 196*x2^3 - 21*x2^2 + 60*x2*x3 - 18*x2 - 168*x3^3 + 83*x3^2 - 9*x3"
                     "-6*x1 + 1134*x2^2*x3 - 189*x2^2 - 466*x2*x3 + 32*x2 - 630*x3^3 + 57*x3^2 + 51*x3"
                     "33*x1 + 63*x2^2 + 2268*x2*x3^2 - 188*x2*x3 + 34*x2 + 2520*x3^3 - 849*x3^2 + 3*x3"
                     "7*x1^2 - x1 - 7*x2^2 - 24*x2*x3 + 3*x2 - 15*x3^2 + 5*x3"
                     "14*x1*x2 - x1 + 14*x2^2 + 18*x2*x3 - 4*x2 + 6*x3^2 - 2*x3"
                     "14*x1*x3 - x1 + 7*x2^2 + 32*x2*x3 - 4*x2 + 27*x3^2 - 9*x3"
                     "x0 + 2*x1 + 2*x2 + 2*x3 - 1"))))

(deftest "groebner: cyclic-4 в эталонном варианте (lex — 5 элементов, grlex — 9)"
  (let ((F (gbts '("a + b + c + d" "a*b + a*d + b*c + b*d" "a*b*c + a*b*d + a*c*d + b*c*d" "a*b*c*d - 1"))))
    (gbt-check F '(a b c d) 'lex
               (gbts '("4*a + 3*d^9 - 4*d^5 - 3*d" "4*b + 4*c - 3*d^9 + 4*d^5 + 7*d" "4*c^2 + 3*d^10 - 4*d^6 - 3*d^2"
                       "4*c*d^4 + 4*c - d^9 + 4*d^5 + 5*d" "d^12 - d^8 - d^4 + 1")))
    (gbt-check F '(a b c d) 'grlex
               (gbts '("3*b*c - c^2 + d^6 - 3*d^2" "-b + 3*c^2*d^3 - c - d^5 - 4*d" "-b + 3*c*d^4 + 2*c + 2*d^5 + 2*d"
                       "c^4 + 2*c^2*d^2 - d^4 - 2" "c^3*d + c*d^3 + d^4 + 1" "b*c^2 - c^3 - c^2*d - 2*c*d^2 - d^3"
                       "b^2 - c^2" "b*d + c^2 + c*d + d^2" "a + b + c + d")))))

(deftest "groebner: test_is_groebner, test_is_reduced (эталон)"
  (assert-true (groebner::gb-with-order 'grlex
                 (lambda () (groebner::gb-groebner? (gbt-polys (gbts '("x^2" "x*y" "-1/2*x + y^2")) '(x y) 'grlex)))))
  (assert-equal (groebner::gb-with-order 'grlex
                  (lambda () (groebner::gb-groebner? (gbt-polys (gbts '("x^3" "x*y" "-1/2*x + y^2")) '(x y) 'grlex))))
                #f)
  (assert-equal (groebner::gb-reduced? (gbt-polys (gbts '("x^2 + 2*x*y^2" "x*y + 2*y^3 - 1")) '(x y) 'lex)) #f)
  (assert-true (groebner::gb-reduced?
                 (gbt-polys (groebner (gbts '("x^2 + 2*x*y^2" "x*y + 2*y^3 - 1")) '(x y)) '(x y) 'lex))))

; ---------- частные случаи (groebner-tests.md §6) ----------

(deftest "groebner: частные случаи — пусто, нули, единичный идеал, повторы, нормировка"
  (assert-equal (groebner '() '(x)) '())
  (assert-equal (groebner '(0) '(x)) '())
  (assert-equal (groebner '(1) '(x)) '(1))
  (assert-equal (groebner '(x 1) '(x)) '(1))
  (assert-equal (groebner (gbts '("x - 1" "x - 2")) '(x)) '(1))
  (assert-equal (groebner '(x x x) '(x)) '(x))
  (assert-equal (groebner '((* 2 x)) '(x)) '(x))
  (assert-equal (groebner (gbts '("x*y - 1" "x" "y + 3")) '(x y)) '(1))
  (assert-equal (groebner (gbts '("x" "y - x")) '(x y)) '(x y))
  ; уравнения: a = b означает a - b
  (assert-equal (groebner (list '(= (^ x 2) 2)) '(x)) (list (gbt "x^2 - 2")))
  (assert-error (groebner '((+ x a)) '(x)))
  (assert-error (groebner '((sin x)) '(x)))
  (assert-error (groebner '(x) '()))
  (assert-error (groebner '(x) '(x) 'deglex)))

(deftest "groebner: раскраска графа в 3 цвета (бенчмарк раскраски) — без последнего ребра; с ним единичный идеал"
  (let* ((vs '(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
         (v (lambda (i) (nth vs (- i 1))))
         (edges '((1 2) (2 3) (1 4) (1 6) (1 12) (2 5) (2 7) (3 8) (3 10) (4 11) (4 9) (5 6) (6 7) (7 8) (8 9)
                  (9 10) (10 11) (11 12) (5 12) (5 9) (6 10) (7 11) (8 12) (3 4)))
         (I3 (map (lambda (x) (list '- (list '^ x 3) 1)) vs))
         (Ig (map (lambda (e) (let ((a (v (car e))) (b (v (cadr e))))
                                (list '+ (list '^ a 2) (list '* a b) (list '^ b 2))))
                  edges)))
    (gbt-check (append I3 (butlast Ig)) vs 'lex
               (gbts '("x1 + x11 + x12" "x2 - x11" "x3 - x12" "x4 - x12" "x5 + x11 + x12" "x6 - x11" "x7 - x12"
                       "x8 + x11 + x12" "x9 - x11" "x10 + x11 + x12" "x11^2 + x11*x12 + x12^2" "x12^3 - 1")))
    (assert-equal (groebner (append I3 Ig) vs) '(1))))

; ---------- инварианты ----------

; псевдослучайные многочлены (линейный конгруэнтный генератор — тесты детерминированы)
(define gbt-seed 12345)
(define (gbt-rand n)
  (set! gbt-seed (modulo (+ (* gbt-seed 1103515245) 12345) 2147483648))
  (modulo (quotient gbt-seed 65536) n))
(define (gbt-random-poly vars nterms maxdeg)
  (simplify (cons '+ (map (lambda (i)
                            (cons '* (cons (- (gbt-rand 7) 3)
                                           (map (lambda (v) (list '^ v (gbt-rand (+ maxdeg 1)))) vars))))
                          (range nterms)))))

(deftest "groebner: инварианты на псевдослучайных системах (lex, grlex, grevlex)"
  (set! gbt-seed 2026)
  (for-each-n 12
    (lambda (k)
      (let* ((vars (if (< k 6) '(x y) '(x y z)))
             (fs (list (gbt-random-poly vars 3 2) (gbt-random-poly vars 3 2) (gbt-random-poly vars 2 1)))
             (ord (nth '(lex grlex grevlex) (modulo k 3))))
        (gbt-invariants fs vars ord)))))

(define (for-each-n n f) (map f (range n)) #t)

(deftest "groebner: результат не зависит от стратегии выбора пар и порядка образующих"
  (let ((old (set-algorithm 'groebner-strategy 'normal)))
    (unwind-protect
      (let* ((F1 gbt-k4) (vars '(x0 x1 x2 x3))
             (a (groebner F1 vars 'grevlex))
             (b (groebner (reverse F1) vars 'grevlex))
             (c (begin (set-algorithm 'groebner-strategy 'sugar) (groebner F1 vars 'grevlex)))
             (d (groebner (reverse gbt-k3) '(x0 x1 x2) 'lex))
             (e (begin (set-algorithm 'groebner-strategy 'normal) (groebner gbt-k3 '(x0 x1 x2) 'lex))))
        (assert-equal b a)
        (assert-equal c a)
        (assert-equal d e))
      (set-algorithm 'groebner-strategy old))))

(deftest "groebner: базисы в разных порядках порождают один идеал"
  (let* ((vars '(x0 x1 x2))
         (gl (groebner gbt-k3 vars 'lex))
         (gr (groebner gbt-k3 vars 'grevlex)))
    (assert-true (every? (lambda (f) (equal? (normal-form f gr vars 'grevlex) 0)) gl))
    (assert-true (every? (lambda (f) (equal? (normal-form f gl vars 'lex) 0)) gr))
    (gbt-invariants gbt-k3 vars 'grevlex)
    (gbt-invariants gbt-k4 '(x0 x1 x2 x3) 'grevlex)))

(deftest "groebner: критерии Бухбергера работают (счётчики на katsura-4)"
  (algo-stats-reset 'groebner)
  (groebner gbt-k4 '(x0 x1 x2 x3) 'grevlex)
  (let* ((st (cdr (car (algo-stats 'groebner))))
         (n (lambda (k) (cadr (assoc k st)))))
    (assert-true (> (n 'product) 0))
    (assert-true (> (n 'chain) 0))
    (assert-equal (n 'calls) 1)
    (assert-equal (n 'basis) 7)
    ; редуцируется меньше трети всех пар (наивный Бухбергер — 253 редукции, MohammadHossinzehi)
    (assert-true (< (n 'reductions) 60))))

; ---------- нормальная форма, исключение ----------

(deftest "normal-form: упрощение по модулю соотношений (sdiehl test_ideal)"
  (let ((I (gbts '("x^2 - y" "y^2 - x"))))
    (assert-equal (normal-form (gbt "x^4 - x") I '(x y) 'grevlex) 0)
    (assert-true (not (equal? (normal-form (gbt "x + 1") I '(x y) 'grevlex) 0)))
    (assert-equal (normal-form (gbt "x^3 + y^3") I '(x y) 'grevlex) (gbt "2*x*y")))
  ; образующие — не обязательно базис; символы вне списка — параметры
  (assert-equal (normal-form (gbt "x^2 + a*x^3") (list (gbt "x^2 - 2")) '(x)) (gbt "2 + 2*a*x"))
  (assert-equal (normal-form '(= (^ x 2) 3) (list '(= (^ x 2) 2)) '(x)) -1))

(deftest "eliminate: исключение параметра и переменной"
  ; кривая x = t², y = t³: x³ − y²
  (assert-equal (eliminate (gbts '("x - t^2" "y - t^3")) '(t) '(x y)) (list (gbt "x^3 - y^2")))
  ; окружность: x = (1−t²)/(1+t²), y = 2t/(1+t²) → x² + y² − 1
  (assert-equal (eliminate (gbts '("x*(1 + t^2) - (1 - t^2)" "y*(1 + t^2) - 2*t")) '(t) '(x y))
                (list (gbt "x^2 + y^2 - 1")))
  ; исключение из katsura-3: многочлен только от x2 (тот же, что последний элемент lex-базиса)
  (assert-equal (eliminate gbt-k3 '(x0 x1) '(x2)) (list (gbt "x2^4 - 10/21*x2^3 + 1/84*x2^2 + 1/84*x2")))
  ; несовместная система: исключение даёт 1
  (assert-equal (eliminate (gbts '("x*y - 1" "x")) '(x) '(y)) '(1)))

; ---------- шаг 21i'' (2): FGLM ----------

; g — базис Грёбнера в порядке ord идеала fs: образующие редуцируются к 0, S-пары → 0, приведённый
(define (gbt-basis-ok? g fs vars ord)
  (groebner::gb-with-order ord
    (lambda ()
      (let ((G (map (lambda (e) (groebner::gb-from-expr e vars)) g))
            (F (map (lambda (e) (groebner::gb-from-expr e vars)) fs)))
        (and (every? (lambda (f) (null? (groebner::gb-nf f G))) F)
             (groebner::gb-groebner? G)
             (groebner::gb-reduced? G))))))

; FGLM из grevlex в lex совпадает с прямым lex
(define (gbt-fglm-same fs vars)
  (let ((g (groebner fs vars 'grevlex)))
    (assert-true (zero-dim? g vars 'grevlex))
    (assert-equal (fglm g vars 'grevlex 'lex) (groebner fs vars 'lex))))

(deftest "fglm: совпадает с прямым lex — katsura-3, katsura-4, cyclic-4, minpoly (эталон)"
  (gbt-fglm-same gbt-k3 '(x0 x1 x2))
  (gbt-fglm-same gbt-k4 '(x0 x1 x2 x3))
  (gbt-fglm-same (gbts '("a + b + c + d" "a*b + a*d + b*c + b*d" "a*b*c + a*b*d + a*c*d + b*c*d" "a*b*c*d - 1"))
                 '(a b c d))
  (gbt-fglm-same (gbts '("x^3 + x + 1" "y^2 + y + 1" "(x + y)*z - (x^2 + y)")) '(x y z))
  (gbt-fglm-same (gbts '("4*x^2*y^2 + 4*x*y + 1" "x^2 + y^2 - 1")) '(x y)))

(deftest "fglm: эталоны — katsura-4 (4 элемента, x3 степени 8)"
  (let ((r (fglm (groebner gbt-k4 '(x0 x1 x2 x3) 'grevlex) '(x0 x1 x2 x3) 'grevlex 'lex)))
    (assert-equal (length r) 4)
    (assert-true (gbt-same? r (gbts '("1971025*x1 - 97197721632*x3^7 + 73975630752*x3^6 - 12121915032*x3^5 - 2760941496*x3^4 + 814792828*x3^3 - 1678512*x3^2 - 9158924*x3"
                                       "128304*x3^8 - 93312*x3^7 + 15552*x3^6 + 3144*x3^5 - 1120*x3^4 + 36*x3^3 + 15*x3^2 - x3"
                                       "5913075*x2 + 371438283744*x3^7 - 237550027104*x3^6 + 22645939824*x3^5 + 11520686172*x3^4 - 2024910556*x3^3 - 132524276*x3^2 + 30947828*x3"
                                       "5913075*x0 - 159690237696*x3^7 + 31246269696*x3^6 + 27439610544*x3^5 - 6475723368*x3^4 - 838935856*x3^3 + 275119624*x3^2 + 4884038*x3 - 5913075"))
                            '(x0 x1 x2 x3) 'lex))))

(deftest "fglm: любые порядки — из grlex и lex, в grlex и grevlex"
  (gbt-check (gbts '("x^3 - 2*x*y" "x^2*y + x - 2*y^2")) '(x y) 'grlex (gbts '("x^2" "x*y" "-1/2*x + y^2")))
  (assert-equal (fglm (groebner gbt-k3 '(x0 x1 x2) 'grlex) '(x0 x1 x2) 'grlex 'lex) (groebner gbt-k3 '(x0 x1 x2) 'lex))
  (assert-equal (fglm (groebner gbt-k3 '(x0 x1 x2) 'lex) '(x0 x1 x2) 'lex 'grevlex) (groebner gbt-k3 '(x0 x1 x2) 'grevlex))
  (assert-equal (fglm (groebner gbt-k4 '(x0 x1 x2 x3) 'lex) '(x0 x1 x2 x3) 'lex 'grlex) (groebner gbt-k4 '(x0 x1 x2 x3) 'grlex))
  (assert-equal (fglm (groebner gbt-k3 '(x0 x1 x2) 'grevlex) '(x0 x1 x2) 'grevlex 'grevlex) (groebner gbt-k3 '(x0 x1 x2) 'grevlex)))

(deftest "fglm: katsura-5 (5 переменных) и cyclic-5 — инварианты lex-базиса"
  (let* ((k5 (gbts '("x0 + 2*x1 + 2*x2 + 2*x3 + 2*x4 - 1" "x0^2 + 2*x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 - x0"
                     "2*x0*x1 + 2*x1*x2 + 2*x2*x3 + 2*x3*x4 - x1" "x1^2 + 2*x0*x2 + 2*x1*x3 + 2*x2*x4 - x2"
                     "2*x1*x2 + 2*x0*x3 + 2*x1*x4 - x3")))
         (v '(x0 x1 x2 x3 x4))
         (r (fglm (groebner k5 v 'grevlex) v 'grevlex 'lex)))
    (assert-equal (length r) 5)                          ; форма shape lemma: 4 линейных по старшим + многочлен от x4
    (assert-true (gbt-basis-ok? r k5 v 'lex))
    (assert-equal (degree (nth r 4) 'x4) 16))             ; 2^4 решений
  (let* ((c5 (gbts '("a + b + c + d + e" "a*b + b*c + c*d + d*e + e*a" "a*b*c + b*c*d + c*d*e + d*e*a + e*a*b"
                     "a*b*c*d + b*c*d*e + c*d*e*a + d*e*a*b + e*a*b*c" "a*b*c*d*e - 1")))
         (v '(a b c d e))
         (r (fglm (groebner c5 v 'grevlex) v 'grevlex 'lex)))
    (assert-true (gbt-basis-ok? r c5 v 'lex))
    (assert-equal (degree (car (reverse r)) 'e) 15)))     ; cyclic-5: 70 решений, но не в общем положении — степень 15

(deftest "fglm: отказ на не нульмерном идеале, особые случаи"
  (assert-true (zero-dim? (groebner gbt-k3 '(x0 x1 x2) 'grevlex) '(x0 x1 x2) 'grevlex))
  (assert-equal (zero-dim? (groebner (gbts '("x*y - 1")) '(x y) 'grevlex) '(x y) 'grevlex) #f)
  (assert-equal (zero-dim? (groebner (gbts '("x^2 - 1")) '(x y) 'grevlex) '(x y) 'grevlex) #f)
  (assert-equal (zero-dim? '() '(x y)) #f)
  ; настоящий cyclic-4 (циклические произведения) — решения образуют кривые: не нульмерный, groebner-lex считает прямой lex
  (let* ((c4 (gbts '("a + b + c + d" "a*b + b*c + c*d + d*a" "a*b*c + b*c*d + c*d*a + d*a*b" "a*b*c*d - 1")))
         (g (groebner c4 '(a b c d) 'grevlex)))
    (assert-equal (zero-dim? g '(a b c d) 'grevlex) #f)
    (assert-error-fn (lambda () (fglm g '(a b c d) 'grevlex 'lex)))
    (assert-equal (groebner-lex c4 '(a b c d)) (groebner c4 '(a b c d) 'lex)))
  (assert-error (fglm (gbts '("x*y - 1")) '(x y) 'grevlex 'lex))
  (assert-error (fglm (gbts '("x^2 - 1")) '(x y) 'lex 'grevlex))
  (assert-error (fglm '() '(x y) 'grevlex 'lex))
  (assert-error (fglm (gbts '("x - 1" "y - 2")) '(x y) 'grevlex 'block))
  ; единичный идеал и точка
  (assert-equal (fglm '(1) '(x y) 'grevlex 'lex) '(1))
  (assert-true (zero-dim? '(1) '(x y)))
  (assert-equal (fglm (gbts '("x - 1" "y - 2")) '(x y) 'grevlex 'lex) (gbts '("x - 1" "y - 2")))
  ; одна переменная
  (assert-equal (fglm (gbts '("x^3 - 2")) '(x) 'lex 'grevlex) (gbts '("x^3 - 2"))))

(deftest "groebner-lex: нульмерный — как прямой lex, не нульмерный — прямой lex"
  (assert-equal (groebner-lex gbt-k3 '(x0 x1 x2)) (groebner gbt-k3 '(x0 x1 x2) 'lex))
  (assert-equal (groebner-lex (gbts '("x*y - 1" "x^2 - y")) '(x y)) (groebner (gbts '("x*y - 1" "x^2 - y")) '(x y) 'lex))
  (assert-equal (groebner-lex (gbts '("x*y - 1")) '(x y)) (gbts '("x*y - 1")))
  (assert-equal (groebner-lex (gbts '("x*y - 1" "x")) '(x y)) '(1)))

(deftest "fglm: журнал шагов"
  (let ((r (capture-step-log (lambda () (groebner-lex gbt-k3 '(x0 x1 x2))))))
    (assert-equal (step-rules (cadr r)) '(groebner-basis fglm))
    (assert-equal (step-title (cadr (cadr r))) "Смена порядка мономов (FGLM)")))

(deftest "groebner: журнал шагов"
  (let ((r (capture-step-log (lambda () (groebner (gbts '("x - t^2" "y - t^3")) '(t x y))))))
    (assert-equal (length (car r)) 4)
    (assert-equal (step-rule (car (cadr r))) 'groebner-basis)
    (assert-equal (step-title (car (cadr r))) "Базис Грёбнера")
    (assert-equal (step-level (car (cadr r))) 'main)))

(deftest "счётчики и переключатели из Lisp: algo-stats-register, algo-count, algorithm-register"
  (assert-true (algo-stats-register 'test.lisp-group '(a b)))
  (algo-stats-reset 'test.lisp-group)
  (assert-equal (algo-count 'test.lisp-group 'a) 1)
  (assert-equal (algo-count 'test.lisp-group 'b 5) 5)
  (assert-equal (algo-stats 'test.lisp-group) '((test.lisp-group (a 1) (b 5))))
  (assert-error (algo-count 'test.lisp-group 'c))
  (assert-error (algo-stats-register 'test.lisp-group '(a)))
  (assert-equal (algorithm-register 'test-switch '(one two) 'one) 'one)
  (assert-equal (set-algorithm 'test-switch 'two) 'one)
  (assert-equal (algorithm-register 'test-switch '(one two) 'one) 'two)
  (set-algorithm 'test-switch 'one)
  (assert-error (algorithm-register 'test-switch2 '(one two) 'three))
  (assert-equal (algorithm 'groebner-strategy) 'normal))

; ---------- F#-версия (Groebner.fs) против эталонной Lisp-версии ----------

; базис и счётчики при заданной реализации
; (шаг 21i'' (1): счётчики арифметики коэффициентов — ratops, coefbits, maxbits — включены, groebner-diag = stats)
(define (gbt-run impl fs vars ord)
  (let ((old (set-algorithm 'groebner impl)) (old-diag (set-algorithm 'groebner-diag 'stats)))
    (unwind-protect
      (begin
        (algo-stats-reset 'groebner)
        (let ((g (groebner fs vars ord)))
          (list g (cdr (car (algo-stats 'groebner))))))
      (set-algorithm 'groebner-diag old-diag)
      (set-algorithm 'groebner old))))

(define (gbt-same-impl fs vars ord)
  (let ((a (gbt-run 'lisp fs vars ord)) (b (gbt-run 'fsharp fs vars ord)))
    (assert-equal (car b) (car a))                 ; тот же приведённый базис
    (assert-equal (cadr b) (cadr a))))             ; те же счётчики: пары, критерии, редукции — шаг в шаг

(deftest "groebner: F# = Lisp — базисы и счётчики (katsura, cyclic-4, эталон)"
  (assert-equal (algorithm 'groebner) 'fsharp)
  (gbt-same-impl gbt-k3 '(x0 x1 x2) 'lex)
  (gbt-same-impl gbt-k3 '(x0 x1 x2) 'grlex)
  (gbt-same-impl gbt-k4 '(x0 x1 x2 x3) 'grevlex)
  (gbt-same-impl gbt-k4 '(x0 x1 x2 x3) 'lex)
  (gbt-same-impl (gbts '("a + b + c + d" "a*b + b*c + c*d + d*a" "a*b*c + b*c*d + c*d*a + d*a*b" "a*b*c*d - 1"))
                 '(a b c d) 'grevlex)
  (gbt-same-impl (gbts '("4*x^2*y^2 + 4*x*y + 1" "x^2 + y^2 - 1")) '(x y) 'lex)
  (gbt-same-impl (gbts '("x*y - 1" "x" "y + 3")) '(x y) 'lex))

(deftest "groebner: F# = Lisp — sugar, блочный порядок, псевдослучайные системы"
  (let ((old (set-algorithm 'groebner-strategy 'sugar)))
    (unwind-protect
      (gbt-same-impl gbt-k4 '(x0 x1 x2 x3) 'grevlex)
      (set-algorithm 'groebner-strategy old)))
  (gbt-same-impl (gbts '("x - t^2" "y - t^3" "z - t^4")) '(t x y z) '(block 1))
  (set! gbt-seed 77)
  (for-each-n 8
    (lambda (k)
      (let ((vars (if (< k 4) '(x y) '(x y z))))
        (gbt-same-impl (list (gbt-random-poly vars 3 2) (gbt-random-poly vars 3 2) (gbt-random-poly vars 2 2))
                       vars (nth '(lex grlex grevlex) (modulo k 3)))))))

(deftest "groebner: диагностика — topsteps/tailsteps, ratops/coefbits/maxbits только при groebner-diag, трасса"
  (let* ((n (lambda (st k) (cadr (assoc k st))))
         (off (let ((old (set-algorithm 'groebner-diag 'off)))
                (algo-stats-reset 'groebner)
                (groebner gbt-k4 '(x0 x1 x2 x3) 'grevlex)
                (set-algorithm 'groebner-diag old)
                (cdr (car (algo-stats 'groebner)))))
         (on (cadr (gbt-run 'fsharp gbt-k4 '(x0 x1 x2 x3) 'grevlex))))
    (assert-equal (n off 'ratops) 0)
    (assert-equal (n off 'maxbits) 0)
    (assert-true (> (n off 'topsteps) 0))
    (assert-equal (n off 'topsteps) (n on 'topsteps))
    (assert-equal (n off 'tailsteps) (n on 'tailsteps))
    (assert-true (> (n on 'ratops) 0))
    (assert-true (> (n on 'coefbits) (n on 'ratops)))
    (assert-true (> (n on 'maxbits) 2))
    ; трасса (stderr / stdout) не меняет результат и счётчики
    (let ((old (set-algorithm 'groebner-diag 'trace)) (oldi (set-algorithm 'groebner 'fsharp)))
      (algo-stats-reset 'groebner)
      (groebner gbt-k3 '(x0 x1 x2) 'grevlex)
      (set-algorithm 'groebner oldi)
      (set-algorithm 'groebner-diag old)
      (assert-true (> (n (cdr (car (algo-stats 'groebner))) 'maxbits) 0)))))

(deftest "groebner: F# — cyclic-5 (grevlex, 20 элементов) и предел числа редукций"
  (let ((g (groebner (gbts '("a + b + c + d + e" "a*b + b*c + c*d + d*e + e*a" "a*b*c + b*c*d + c*d*e + d*e*a + e*a*b"
                             "a*b*c*d + b*c*d*e + c*d*e*a + d*e*a*b + e*a*b*c" "a*b*c*d*e - 1"))
                     '(a b c d e) 'grevlex)))
    (assert-equal (length g) 20))
  (let ((old groebner::gb-max-reductions))
    (set! groebner::gb-max-reductions 3)
    (unwind-protect
      (begin
        (assert-error (groebner gbt-k4 '(x0 x1 x2 x3) 'grevlex))
        (assert-error (gbt-run 'lisp gbt-k4 '(x0 x1 x2 x3) 'grevlex)))
      (set! groebner::gb-max-reductions old))))
