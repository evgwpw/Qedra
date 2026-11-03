; Lisp-тесты вычислителя входного математического языка (lib\mathlang.lisp), Шаг 21
;
; (mlt "программа") — значение последнего оператора, напечатанное в синтаксисе языка (math-show).
; Каждый deftest выполняется в свежем окружении: переменные и функции языка не переходят между тестами.
; Шаг 21c: декларации (x :∈ D) — состояние сессии; math-reset снимает и их.

; Шаг 21a: каждая проверка начинается с чистых переменных и функций языка (math-reset): проверки одного deftest независимы
(define (mlt s) (math-reset) (math-show (math-eval s)))
; то же без сброса: продолжение сессии (декларации и присваивания предыдущих вызовов сохраняются)
(define (mls s) (math-show (math-eval s)))

; ---------- арифметика, присваивание ----------

(deftest "арифметика чисел"
  (assert-equal (mlt "2 + 3*4") "14")
  (assert-equal (mlt "1/3 + 1/6") "1/2")
  (assert-equal (mlt "2^10") "1024")
  (assert-equal (mlt "-5 + 2") "-3")
  (assert-equal (mlt "7/2*2") "7"))

(deftest "символьное упрощение результата"
  (assert-equal (mlt "x + x") "2x")
  (assert-equal (mlt "(x + 1)^2 - x^2") "-x^2 + (1 + x)^2")
  (assert-equal (mlt "x*x*x") "x^3"))

(deftest "присваивание: значение подставляется"
  (assert-equal (mlt "a := 5") "5")
  (assert-equal (mlt "a := 5; a^2") "25")
  (assert-equal (mlt "a := x + 1; a*2") "2(1 + x)")
  (assert-equal (mlt "a := 5; b := a + 1; b") "6"))

; Шаг 21a: ожидание изменено — значение переменной вычисляется заново при использовании (как в Derive)
(deftest "имя без значения — символ; значение пересчитывается при использовании"
  (assert-equal (mlt "zzz") "zzz")
  (assert-equal (mlt "y := x^2; x := 3; y") "9"))

(deftest "clear и a := снимают присваивание"
  (assert-equal (mlt "a := 5; clear(a); a") "a")
  (assert-equal (mlt "a := 5; a :=; a") "a")
  (assert-equal (mlt "f(x) := x + 1; clear(f); f(2)") "f(2)")
  (assert-equal (mlt "a := 1; b := 2; clear(); a + b") "a + b"))

(deftest "e и π; пользовательское e"
  (assert-equal (mlt "e") "exp(1)")
  (assert-equal (mlt "e^x") "exp(x)")
  (assert-equal (mlt "e^0") "1")
  (assert-equal (mlt "π") "pi")
  (assert-equal (mlt "pi*2") "2pi")
  (assert-equal (mlt "e := 5; e + 1") "6"))

; ---------- пространства имён ----------

(deftest "переменные языка не затирают функции библиотеки и наоборот"
  (assert-equal (mlt "map := 5; map") "5")
  (assert-equal (mlt "union := 3; {1} ∪ {2}") "{1, 2}")
  (assert-equal (map car '((1) (2))) '(1 2))
  (define zq7 99)
  (assert-equal (mlt "zq7") "zq7"))

(deftest "функция языка с именем библиотечной функции — приоритет у функции языка"
  (assert-equal (mlt "det(m) := 42; det(1)") "42")
  (math-reset)
  (assert-equal (mlt "det([[1, 2], [3, 4]])") "-2"))

(deftest "1/0 — ошибка вычисления, а не разбора"
  (assert-equal (math-read-program "1/0") '((/ 1 0)))
  (assert-error (math-eval "1/0"))
  (assert-equal (mlt "if(true, 1, 1/0)") "1"))

; ---------- функции ----------

(deftest "определение функции и вызов (пример сеанса)"
  (assert-equal (mlt "f(x) := x^2 + sin(x)") "f(x) := x^2 + sin(x)")
  (assert-equal (mlt "f(x) := x^2 + sin(x); a := 5; f(a)") "25 + sin(5)")
  (assert-equal (mlt "f(x) := x^2 + sin(x); f(y + 1)") "(1 + y)^2 + sin(1 + y)"))

(deftest "функция нескольких аргументов"
  (assert-equal (mlt "g(x, y) := x*y + 1; g(3, 4)") "13")
  (assert-equal (mlt "g(x, y) := x - y; g(a, a)") "0")
  (assert-equal (mlt "h() := 7; h()") "7"))

(deftest "рекурсия: факториал и Фибоначчи"
  (assert-equal (mlt "fact(n) := if(n = 0, 1, n*fact(n - 1)); fact(10)") "3628800")
  (assert-equal (mlt "fact(n) := if(n = 0, 1, n*fact(n - 1)); fact(20)") "2432902008176640000")
  (assert-equal (mlt "fib(n) := if(n < 2, n, fib(n - 1) + fib(n - 2)); fib(15)") "610"))

(deftest "рекурсия с символьным аргументом — невычисленный if"
  (assert-equal (mlt "fact(n) := if(n = 0, 1, n*fact(n - 1)); fact(m)")
                "if(m = 0, 1, m*fact(m - 1))"))

(deftest "параметры функции локальны: глобальная переменная с тем же именем не портится"
  (assert-equal (mlt "a := 10; k(a) := a*2; k(3); a") "10")
  (assert-equal (mlt "a := 10; k(a) := a*2; k(3)") "6")
  (assert-equal (mlt "x := 7; g(x) := x + 1; g(2)") "3")
  (assert-equal (mlt "x := 7; g(x) := x + 1; g(x)") "8"))

(deftest "лексическая область: тело видит глобальные переменные, а не параметры вызывающей функции"
  (assert-equal (mlt "w(x) := x + c; h(c) := w(1); c := 100; h(5)") "101")
  (assert-equal (mlt "p(x) := a; a := 10; p(5)") "10"))

(deftest "вызов функции из функции"
  (assert-equal (mlt "f(x) := x^2; g(x) := f(x) + 1; g(2)") "5")
  (assert-equal (mlt "f(v) := v[1] + v[2]; f([3, 4])") "7"))

(deftest "ошибка арности пользовательской функции"
  (assert-error (math-eval "f(x) := x; f(1, 2)"))
  (assert-error (math-eval "f(x, x) := x")))

(deftest "неизвестные функции остаются невычисленными формами"
  (assert-equal (mlt "foo(1, y)") "foo(1, y)")
  (assert-equal (mlt "a := 2; foo(a + 1)") "foo(3)")
  (assert-equal (mlt "foo()") "foo()"))

; ---------- условия и логика ----------

(deftest "if: известное условие"
  (assert-equal (mlt "if(1 < 2, 10, 20)") "10")
  (assert-equal (mlt "if(2 < 1, 10, 20)") "20")
  (assert-equal (mlt "if(1 = 1.0, a, b)") "a"))

(deftest "if: ленивые ветки (невыбранная не вычисляется)"
  (assert-equal (mlt "if(true, 1, 1/0)") "1")
  (assert-equal (mlt "if(false, 1/0, 2)") "2"))

(deftest "if: unknown — невычисленный if с подстановкой значений"
  (assert-equal (mlt "if(uq > 0, 1, 2)") "if(uq > 0, 1, 2)")
  (assert-equal (mlt "g(y) := if(y > 0, y, -y); g(uq)") "if(uq > 0, uq, -uq)")
  (assert-equal (mlt "g(y) := if(y > 0, y, -y); g(-3)") "3")
  (assert-equal (mlt "g(y) := if(y > 0, y, -y); g(4)") "4"))

(deftest "and, or, not — трёхзначные"
  (assert-equal (mlt "true and false") "false")
  (assert-equal (mlt "true or false") "true")
  (assert-equal (mlt "not (1 = 2)") "true")
  (assert-equal (mlt "uq > 0 and false") "false")
  (assert-equal (mlt "uq > 0 or true") "true")
  (assert-equal (mlt "uq > 0 and true") "uq > 0")
  (assert-equal (mlt "uq > 0 or false") "uq > 0")
  (assert-equal (mlt "not (uq > 0)") "not uq > 0")
  (assert-equal (mlt "1 < 2 and 2 < 3 and 3 < 4") "true"))

(deftest "отношения"
  (assert-equal (mlt "x = x") "true")
  (assert-equal (mlt "2 = 3") "false")
  (assert-equal (mlt "1 /= 2") "true")
  (assert-equal (mlt "2 >= 2") "true")
  (assert-equal (mlt "3 <= 2") "false")
  (assert-equal (mlt "1/2 < 2/3") "true")
  (assert-equal (mlt "x + 1 > x") "true")
  (assert-equal (mlt "uq < 1") "uq < 1")
  (assert-equal (mlt "a := 3; a + 2 = 5") "true"))

(deftest "отношения: знак из деклараций"
  (assert-equal (mlt "pq :∈ ℕ; pq >= 0") "true")
  (assert-equal (mls "pq < 0") "false")      ; та же сессия: декларация pq ещё действует
  (math-reset))

(deftest "равенство без решения остаётся уравнением"
  (assert-equal (mlt "x^2 = 2") "x^2 = 2")
  (assert-equal (mlt "x + 2 = 5") "2 + x = 5"))

(deftest "строки и булевы значения"
  (assert-equal (math-eval "\"привет\"") "привет")
  (assert-equal (mlt "\"a\" = \"b\"") "false")
  (assert-equal (mlt "\"a\" = \"a\"") "true")
  (assert-error (math-eval "1 < \"a\"")))

; ---------- векторы и матрицы ----------

(deftest "векторы и индексация с 1"
  (assert-equal (mlt "v := [1, 2, 3]; v") "[1, 2, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; v[2]") "2")
  (assert-equal (mlt "v := [1, 2, 3]; v[1] + v[3]") "4")
  (assert-equal (mlt "[x, x^2][2]") "x^2"))

(deftest "индекс вне границ — ошибка; символьный индекс — невычисленная форма"
  (assert-error (math-eval "v := [1, 2, 3]; v[4]"))
  (assert-error (math-eval "v := [1, 2, 3]; v[0]"))
  (assert-error (math-eval "v := [1, 2, 3]; v[1, 2]"))
  (assert-equal (mlt "w[i]") "w[i]")
  (assert-equal (mlt "v := [1, 2, 3]; v[i]") "[1, 2, 3][i]"))

(deftest "матрицы: литерал, индексы, строка"
  (assert-equal (mlt "[[1, 2], [3, 4]]") "[[1, 2], [3, 4]]")
  (assert-equal (mlt "m := [[1, 2], [3, 4]]; m[2, 1]") "3")
  (assert-equal (mlt "m := [[1, 2], [3, 4]]; m[1]") "[1, 2]")
  (assert-equal (mlt "m := [[1, 2], [3, 4]]; m[2][2]") "4")
  (assert-error (math-eval "[[1, 2], [3]]"))
  ; Шаг 21a: ожидание изменено — пустой вектор [] допустим (нужен для append и результатов select/vector)
  (assert-equal (mlt "[]") "[]"))

(deftest "арифметика векторов и матриц"
  (assert-equal (mlt "[1, 2, 3] + [1, 1, 1]") "[2, 3, 4]")
  (assert-equal (mlt "2*[1, 2]") "[2, 4]")
  (assert-equal (mlt "[1, 2]*[3, 4]") "11")
  (assert-equal (mlt "[[1, 2], [3, 4]]*[[1, 0], [0, 1]]") "[[1, 2], [3, 4]]")
  (assert-equal (mlt "-[1, 2]") "[-1, -2]"))

(deftest "det и inv"
  (assert-equal (mlt "det([[1, 2], [3, 4]])") "-2")
  (assert-equal (mlt "inv([[1, 2], [3, 4]])") "[[-2, 1], [3/2, -1/2]]")
  (assert-equal (mlt "det([[a, b], [c, d]])") "a*d - b*c"))

; ---------- множества и домены ----------

(deftest "множества и операции"
  (assert-equal (mlt "s := {1, 2, 3} ∪ {3, 4}") "{1, 2, 3, 4}")
  (assert-equal (mlt "{1, 2, 3} ∩ {2, 3, 4}") "{2, 3}")
  (assert-equal (mlt "{1, 2, 3} \\ {2}") "{1, 3}")
  (assert-equal (mlt "{}") "{}")
  (assert-equal (mlt "{3, 1, 3, 2}") "{1, 2, 3}")
  (assert-equal (mlt "union({1}, {2})") "{1, 2}")
  (assert-equal (mlt "intersection({1, 2}, {2, 3})") "{2}")
  (assert-equal (mlt "{1, 2} ∩ {2, 3} ∪ {9}") "{2, 9}")
  (assert-equal (mlt "card({1, 2, 3})") "3"))

(deftest "равенство множеств и принадлежность"
  (assert-equal (mlt "{2, 1} = {1, 2}") "true")
  (assert-equal (mlt "{1} = {2}") "false")
  (assert-equal (mlt "2 ∈ {1, 2}") "true")
  (assert-equal (mlt "5 ∈ {1, 2}") "false")
  (assert-equal (mlt "uq ∈ {1, 2}") "unknown")
  (assert-equal (mlt "5 ∉ {1, 2}") "true")
  (assert-equal (mlt "subset?({1}, {1, 2})") "true"))

(deftest "домены: декларация и принадлежность"
  (assert-equal (mlt "ℝ") "ℝ")
  (assert-equal (mlt "dq :∈ ℝ") "dq ∈ ℝ")
  (assert-equal (mls "dq ∈ ℝ") "true")
  (assert-equal (mls "dq ∈ ℤ") "unknown")
  (assert-equal (mlt "3 ∈ ℤ") "true")
  (assert-equal (mlt "1/2 ∈ ℤ") "false")
  (assert-equal (mlt "dq :in ℤ; dq ∈ ℤ") "true")
  (undeclare 'dq))

(deftest "декларация влияет на solve"
  (assert-equal (mlt "solve(sq^2 + 1 = 0, sq)") "{%i, -%i}")
  (assert-equal (mlt "sq :∈ ℝ; solve(sq^2 + 1 = 0, sq)") "{}")
  (undeclare 'sq))

; ---------- математические функции ----------

(deftest "элементарные функции от точных чисел остаются символьными"
  (assert-equal (mlt "sin(5)") "sin(5)")
  (assert-equal (mlt "sin(0)") "0")
  (assert-equal (mlt "cos(0)") "1")
  (assert-equal (mlt "exp(0)") "1")
  (assert-equal (mlt "log(1)") "0")
  (assert-equal (mlt "exp(2)") "exp(2)")
  (assert-equal (mlt "sin(x) + sin(x)") "2sin(x)"))

(deftest "элементарные функции от float — численно"
  (assert-equal (type-of (math-eval "sin(0.5)")) 'float)
  (assert-true (< (abs (- (math-eval "sin(0.5)") 0.479425538604203)) 0.000001)))

(deftest "целое дробное число печатается с .0 (иначе при чтении получилось бы точное целое)"
  (assert-equal (mlt "1.0") "1.0")
  (assert-equal (mlt "-3.0") "-3.0")
  (assert-equal (mlt "0.5") "0.5")
  (assert-equal (mlt "2.0*x") "2.0*x")
  (assert-equal (mlt "f(a := 1.0) := a") "f(a := 1.0) := a"))

(deftest "sqrt, abs, мнимая единица"
  (assert-equal (mlt "sqrt(4)") "2")
  (assert-equal (mlt "sqrt(1/4)") "1/2")
  (assert-equal (mlt "sqrt(8)") "2*2^(1/2)")   ; Шаг 21c: вынос квадрата в ядре simplify
  (assert-equal (mlt "sqrt(-4)") "2%i")
  (assert-equal (mlt "sqrt(x)") "sqrt(x)")
  (assert-equal (mlt "abs(-3)") "3")
  (assert-equal (mlt "abs(x)") "abs(x)")
  (assert-equal (mlt "%i^2") "-1")
  (assert-equal (mlt "ⅈ*ⅈ") "-1")
  (assert-equal (mlt "i^2") "i^2"))

(deftest "факториал"
  (assert-equal (mlt "5!") "120")
  (assert-equal (mlt "0!") "1")
  (assert-equal (mlt "n!") "n!")
  (assert-equal (mlt "(2 + 3)!") "120")
  (assert-error (math-eval "(-1)!")))

(deftest "factor, expand, simplify, apart"
  (assert-equal (mlt "factor(x^2 - 1)") "(-1 + x)(1 + x)")
  (assert-equal (mlt "expand((x + 1)^3)") "1 + 3x + 3x^2 + x^3")
  (assert-equal (mlt "simplify(sin(x)^2 + cos(x)^2)") "1")
  (assert-equal (mlt "apart(1/(x^2 - 1), x)") "1/(2(-1 + x)) - 1/(2(1 + x))"))

(deftest "имена Lisp-функций с дефисом пишутся через подчёркивание"
  (assert-equal (mlt "poly_gcd(x^2 - 1, x - 1)") "-1 + x")
  (assert-equal (mlt "power_set({1, 2})") "{{}, {1}, {2}, {1, 2}}")
  (assert-equal (mlt "set_difference({1, 2}, {2})") "{1}"))

(deftest "subst: три формы записи"
  (assert-equal (mlt "subst(x^2 + 1, x, 2)") "5")
  (assert-equal (mlt "subst(x^2 + 1, x = 2)") "5")
  (assert-equal (mlt "subst(x^2 + y, [x = 1, y = 2])") "3")
  (assert-equal (mlt "subst(x = 3, x^2)") "9"))

; ---------- анализ: diff, integrate, limit, solve, series ----------

(deftest "diff: выражение, переменная, порядок"
  (assert-equal (mlt "diff(x^3, x)") "3x^2")
  (assert-equal (mlt "diff(x^3, x, 2)") "6x")
  (assert-equal (mlt "diff(sin(x)*x, x)") "x*cos(x) + sin(x)")
  (assert-equal (mlt "diff([x, x^2], x)") "[1, 2x]")
  (assert-error (math-eval "diff(x^2, 3)"))
  (assert-error (math-eval "diff(x^2)")))

(deftest "integrate: пример сеанса и определённые интегралы"
  (assert-equal (mlt "f(x) := x^2 + sin(x); integrate(f(x), x)") "1/3*x^3 - cos(x)")
  (assert-equal (mlt "integrate(x*sin(x), x)") "-x*cos(x) + sin(x)")
  (assert-equal (mlt "integrate(x^2, x, 0, 1)") "1/3")
  (assert-equal (mlt "integrate(1/x, x, 1, e)") "1"))

(deftest "integrate: невычисленный интеграл печатается как integrate(...)"
  (assert-equal (mlt "integrate(foo(x), x)") "integrate(foo(x), x)"))

(deftest "переменная интегрирования с присвоенным значением — понятная ошибка"
  (assert-error (math-eval "x := 5; integrate(x^2, x)"))
  (assert-equal (try (math-eval "x := 5; integrate(x^2, x)") (lambda (e) (error-message e)))
                "x имеет значение 5 — переменная интегрирования не должна быть присвоена; снимите присваивание: x :=")
  (assert-equal (mlt "x := 5; clear(x); integrate(x^2, x)") "1/3*x^3"))

(deftest "limit"
  (assert-equal (mlt "limit(sin(x)/x, x, 0)") "1")
  (assert-equal (mlt "limit(1/x, x, ∞)") "0")
  (assert-equal (mlt "limit(1/x, x, 0, plus)") "∞")
  (assert-equal (mlt "limit(1/x, x, 0, minus)") "-∞")
  (assert-equal (mlt "limit(1/x, x, -∞)") "0")
  (assert-equal (mlt "limit((1 + 1/x)^x, x, ∞)") "exp(1)")
  (assert-equal (mlt "limit(x^2, x, 3)") "9"))

(deftest "series и taylor"
  (assert-equal (mlt "taylor(exp(x), x, 0, 4)") "1 + x + 1/2*x^2 + 1/6*x^3")
  (assert-equal (mlt "series(exp(x), x, 0, 3)") "1 + x + 1/2*x^2 + O(x^3)")
  (assert-equal (mlt "series(sin(x), x, 0, 6)") "x - 1/6*x^3 + 1/120*x^5 + O(x^6)"))

(deftest "solve: уравнения и системы"
  (assert-equal (mlt "solve(x^2 = 2, x)") "{2^(1/2), -2^(1/2)}")
  (assert-equal (mlt "solve(x^2 - 5x + 6 = 0, x)") "{2, 3}")
  (assert-equal (mlt "solve(2x + 1 = 0, x)") "{-1/2}")
  (assert-equal (mlt "solve([x + y = 3, x - y = 1], [x, y])") "{[x = 2, y = 1]}"))

; ---------- программы, разбор, ошибки ----------

(deftest "несколько операторов, комментарии, продолжение строк"
  (assert-equal (mlt "a := 1 // комментарий\nb := a + 1\nb") "2")
  (assert-equal (mlt "a := [1,\n 2,\n 3]; a[3]") "3")
  (assert-equal (mlt "a := 1 +\n 2; a") "3"))

(deftest "пустая программа и math-eval-tree"
  (assert-equal (math-eval "") '())
  (assert-equal (math-eval "// только комментарий") '())
  (assert-equal (math-eval-tree '(+ 1 2)) 3)
  (assert-equal (math-eval-tree (car (math-read-program "2 + 3"))) 5))

(deftest "ошибка разбора — с номером строки и позиции, без Lisp-стека"
  (assert-equal (try (math-eval "x := )") (lambda (e) (error-message e)))
                "math: строка 1, позиция 6: неожиданный токен «)»")
  (assert-equal (try (math-eval "a := 1\nb := 2 $") (lambda (e) (error-message e)))
                "math: строка 2, позиция 8: недопустимый символ «$»"))

(deftest "load-math: файл не найден — ошибка"
  (assert-error (load-math "/нет/такого/файла.mth"))
  (assert-error (math-eval "load(\"/нет/такого/файла.mth\")"))
  (assert-error (math-eval "load(5)")))

; ======================= Шаг 21a: программирование =======================

(define (mle s) (math-reset) (try (math-eval s) (lambda (e) (error-message e))))     ; текст ошибки

; ---------- переменные: ленивое повторное вычисление ----------

(deftest "присваивание вычисляет правую часть; использование пересчитывает значение"
  (assert-equal (mlt "n := 5; n := n + 1") "6")
  (assert-equal (mlt "y := x^2; x := 3; y") "9")
  (assert-equal (mlt "y := x^2; x := 3; x := 4; y") "16")
  (assert-equal (mlt "y := x^2 + 1; x := 2; clear(x); y") "1 + x^2")
  (assert-equal (mlt "a := b + 1; b := c * 2; c := 5; a") "11")
  (assert-equal (mlt "v := [x, x^2]; x := 3; v") "[3, 9]")
  (assert-equal (mlt "s := {x, 1}; x := 2; s") "{1, 2}")
  (assert-equal (mlt "g := if(w > 0, w, -w); w := -4; g") "4")
  (assert-equal (mlt "f(t) := t + a; a := 1; b := f(a); a := 10; b") "2"))

(deftest "циклическое определение — ошибка при присваивании"
  (assert-equal (mle "x := x + 1") "циклическое определение x")
  (assert-equal (mle "a := b; b := a") "циклическое определение b")
  (assert-equal (mle "a := a") "циклическое определение a")
  (assert-equal (mle "y := x^2; x := y + 1") "циклическое определение x")
  (assert-equal (mlt "x := 1; x := x + 1; x") "2"))

(deftest "переменная solve/integrate/diff/limit/series/taylor не должна быть присвоена"
  (assert-equal (mle "x := 7; solve(x^2 - 5x + 6 = 0, x)")
                "x имеет значение 7 — переменная решения не должна быть присвоена; снимите присваивание: x :=")
  (assert-equal (mle "x := 7; diff(x^2, x)")
                "x имеет значение 7 — переменная дифференцирования не должна быть присвоена; снимите присваивание: x :=")
  (assert-equal (mle "x := 7; limit(1/x, x, 0)")
                "x имеет значение 7 — переменная предела не должна быть присвоена; снимите присваивание: x :=")
  (assert-equal (mle "x := 7; series(sin(x), x, 0, 3)")
                "x имеет значение 7 — переменная разложения не должна быть присвоена; снимите присваивание: x :=")
  (assert-equal (mle "x := 7; taylor(sin(x), x, 0, 3)")
                "x имеет значение 7 — переменная разложения не должна быть присвоена; снимите присваивание: x :=")
  (assert-equal (mle "y := 2; solve([x + y = 3, x - y = 1], [x, y])")
                "y имеет значение 2 — переменная решения не должна быть присвоена; снимите присваивание: y :=")
  (assert-equal (mlt "x := 7; clear(x); solve(x^2 - 5x + 6 = 0, x)") "{2, 3}")
  ; проверка идёт ДО вычисления остальных аргументов (иначе была бы ошибка деления на ноль)
  (assert-equal (mle "x := 7; integrate(1/0, x)")
                "x имеет значение 7 — переменная интегрирования не должна быть присвоена; снимите присваивание: x :=")
  ; параметр функции, равный самому себе, — не присваивание
  (assert-equal (mlt "g(x) := integrate(x^2, x); g(x)") "1/3*x^3"))

; ---------- prog, loop, exit, return ----------

(deftest "prog: последовательное вычисление, значение последнего"
  (assert-equal (mlt "prog(a := 1, b := a + 1, a + b)") "3")
  (assert-equal (mlt "prog(a := 5, a := a*2); a") "10")
  (assert-equal (mlt "prog(1, 2, 3)") "3"))

(deftest "loop: сумма 1..100"
  (assert-equal (mlt "s := 0; k := 1; loop(if(k > 100, exit), s := s + k, k := k + 1); s") "5050"))

(deftest "loop: НОД Евклида"
  (assert-equal (mlt "a := 48; b := 18; loop(if(b = 0, exit), t := mod(a, b), a := b, b := t); a") "6")
  (assert-equal (mlt "gcd2(a, b) := prog(loop(if(b = 0, exit(a)), t := mod(a, b), a := b, b := t)); gcd2(1071, 462)") "21"))

(deftest "loop: exit(v) — значение цикла; exit без значения — false"
  (assert-equal (mlt "loop(exit(42))") "42")
  (assert-equal (mlt "loop(exit)") "false")
  (assert-equal (mlt "k := 0; loop(k := k + 1, if(k = 3, exit(k*100)))") "300"))

(deftest "loop: метод Ньютона для sqrt(2) с выходом по точности (float)"
  (assert-true (< (abs (- (math-eval "x := 1.0; loop(y := x/2 + 1/x, if(abs(y - x) < 0.000000001, exit), x := y); y")
                          1.4142135623730951))
                  0.000000001)))

(deftest "return: выход из функции из середины цикла"
  (assert-equal (mlt "first_gt(n, lim) := prog(k := 1, loop(if(k*k > lim, return(k)), k := k + 1)); first_gt(1, 50)") "8")
  (assert-equal (mlt "f(n) := prog(if(n < 0, return(-1)), n + 100); f(-5)") "-1")
  (assert-equal (mlt "f(n) := prog(if(n < 0, return(-1)), n + 100); f(5)") "105")
  ; return вне функции — завершает оператор верхнего уровня
  (assert-equal (mlt "prog(a := 1, return(a + 41), a := 0)") "42")
  (assert-equal (mlt "prog(a := 1, return(a + 41), a := 0); a") "1")
  (assert-equal (mlt "return(7)") "7"))

(deftest "return из вложенных циклов и вызов функции с return из выражения"
  (assert-equal (mlt "find(n) := prog(i := 1, loop(j := 1, loop(if(i*j = n, return(i)), if(j > 10, exit), j := j + 1), i := i + 1)); find(14)") "2")
  (assert-equal (mlt "sg(x) := if(x < 0, return(-1), 1); sg(-3) + sg(3)") "0"))

(deftest "exit вне цикла — ошибка; ошибка внутри цикла не теряется"
  (assert-equal (mle "exit") "exit: вне цикла loop")
  (assert-equal (mle "f(x) := exit; f(1)") "exit: вне цикла loop")
  (assert-error (math-eval "loop(1/0)"))
  (assert-error (math-eval "loop()")))

(deftest "loop: предохранитель числа итераций, set_loop_limit"
  (assert-equal (mlt "set_loop_limit(100)") "100")
  (assert-equal (mle "set_loop_limit(100); loop(1)")
                "loop: превышен лимит итераций 100 (изменить: set_loop_limit(n); выход из цикла — exit)")
  (assert-equal (mlt "set_loop_limit(100); k := 0; loop(k := k + 1, if(k = 50, exit)); k") "50")
  (assert-error (math-eval "set_loop_limit(0)"))
  (assert-error (math-eval "set_loop_limit(x)"))
  (math-eval "set_loop_limit(1000000)"))

; ---------- локальные переменные и параметры по умолчанию ----------

(deftest "параметры по умолчанию — локальные переменные (факториал итеративно)"
  (assert-equal (mlt "fact(n, r := 1, i := 2) := prog(loop(if(i > n, exit), r := r*i, i := i + 1), r); fact(10)") "3628800")
  (assert-equal (mlt "fact(n, r := 1, i := 2) := prog(loop(if(i > n, exit), r := r*i, i := i + 1), r); fact(20)")
                "2432902008176640000")
  ; локальные не портят глобальные одноимённые
  (assert-equal (mlt "r := 77; i := 88; fact(n, r := 1, i := 2) := prog(loop(if(i > n, exit), r := r*i, i := i + 1), r); fact(5); r + i") "165"))

(deftest "значения по умолчанию вычисляются при вызове и видят предыдущие параметры"
  (assert-equal (mlt "c(a, b := a*2) := a + b; c(3)") "9")
  (assert-equal (mlt "c(a, b := a*2) := a + b; c(3, 1)") "4")
  (assert-equal (mlt "d := 10; c(a, b := d) := a + b; d := 20; c(1)") "21"))

(deftest "арность функции с параметрами по умолчанию"
  (assert-equal (mle "c(a, b := 1) := a; c()") "c: ожидается аргументов от 1 до 2, получено 0")
  (assert-equal (mle "c(a, b := 1) := a; c(1, 2, 3)") "c: ожидается аргументов от 1 до 2, получено 3")
  (assert-error (math-eval "c(a := 1, b) := a"))
  (assert-error (math-eval "c(a := 1, a := 2) := a")))

(deftest "присваивание внутри функции: локальное — меняет локальную, иначе — глобальную"
  (assert-equal (mlt "n := 0; h(x) := prog(x := x + 1, n := n + 10, x); h(5)") "6")
  (assert-equal (mlt "n := 0; h(x) := prog(x := x + 1, n := n + 10, x); h(5); n") "10")
  (assert-equal (mlt "x := 100; h(x) := prog(x := x + 1, x); h(5); x") "100"))

(deftest "функция с параметрами по умолчанию печатается и читается обратно"
  (assert-equal (mlt "f(n, s := 0, k := 1) := n + s + k") "f(n, s := 0, k := 1) := n + s + k")
  (assert-equal (mlt "f(n, s := 0, k := 1) := n + s + k; f(1)") "2"))

; ---------- if с четырьмя ветвями ----------

(deftest "if(c, a, b, u) и if(c, a) без else"
  (assert-equal (mlt "if(zq > 0, 1, 2, 3)") "3")
  (assert-equal (mlt "if(1 > 0, 1, 2, 3)") "1")
  (assert-equal (mlt "if(1 < 0, 1, 2, 3)") "2")
  (assert-equal (mlt "if(1 < 2, 10)") "10")
  (assert-equal (mlt "if(1 > 2, 10)") "false")
  (assert-equal (mlt "if(zq > 0, 10)") "if(zq > 0, 10)")
  (assert-error (math-eval "if(1)"))
  (assert-error (math-eval "if(1, 2, 3, 4, 5)")))

; ---------- присваивание элементу ----------

(deftest "v[i] := e — изменённая копия, разделяемые значения не мутируются"
  (assert-equal (mlt "v := [1, 2, 3]; v[2] := 20; v") "[1, 20, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; v[2] := 20") "20")
  (assert-equal (mlt "v := [1, 2, 3]; w := v; v[1] := 9; w") "[1, 2, 3]")
  (assert-equal (mlt "m := [[1, 2], [3, 4]]; m[2, 1] := 9; m") "[[1, 2], [9, 4]]")
  (assert-equal (mlt "v := [1, 2, 3]; v[1] := x; x := 5; v") "[5, 2, 3]")
  (assert-equal (mlt "f(v) := prog(v[1] := 100, v); u := [1, 2]; f(u)") "[100, 2]")
  (assert-equal (mlt "f(v) := prog(v[1] := 100, v); u := [1, 2]; f(u); u") "[1, 2]")
  (assert-equal (mlt "v := [0, 0, 0]; k := 1; loop(if(k > 3, exit), v[k] := k*k, k := k + 1); v") "[1, 4, 9]"))

(deftest "присваивание элементу: ошибки"
  (assert-error (math-eval "v := [1, 2, 3]; v[4] := 1"))
  (assert-error (math-eval "v := [1, 2, 3]; v[0] := 1"))
  (assert-error (math-eval "v := [1, 2, 3]; v[1, 1] := 1"))
  (assert-error (math-eval "q := 5; q[1] := 2"))
  (assert-error (math-eval "m := [[1, 2], [3, 4]]; m[1] := 7"))
  (assert-error (math-eval "v := [1, 2]; v[x] := 1")))

; ---------- print ----------

(deftest "print печатает и возвращает последний аргумент"
  (assert-equal (mlt "print(1, 2, x + 1)") "1 + x")
  (assert-equal (mlt "print()") "false"))

(deftest "разбор: присваивание в аргументах и параметры по умолчанию"
  (assert-equal (math-read-program "prog(a := 1, b := a)") '((prog (:= a 1) (:= b a))))
  (assert-equal (math-read-program "v[2] := 5") '((:= (m-index v 2) 5)))
  (assert-equal (math-read-program "f(n, s := 0) := n") '((:= (f n (:= s 0)) n)))
  (assert-equal (math-read-program "a := b := 1") '((:= a (:= b 1)))))

; ---------- функции-итераторы: vector, sum, product, select, iterate, iterates ----------

(deftest "vector(e, k, n), vector(e, k, m, n), vector(e, k, m, n, step)"
  (assert-equal (mlt "vector(k^2, k, 5)") "[1, 4, 9, 16, 25]")
  (assert-equal (mlt "vector(k^2, k, 2, 6)") "[4, 9, 16, 25, 36]")
  (assert-equal (mlt "vector(k, k, 10, 1, -3)") "[10, 7, 4, 1]")
  (assert-equal (mlt "vector(k, k, 1, 10, 4)") "[1, 5, 9]")
  (assert-equal (mlt "vector(k/2, k, 1, 3)") "[1/2, 1, 3/2]")
  (assert-equal (mlt "vector(x^k, k, 0, 3)") "[1, x, x^2, x^3]")
  (assert-equal (mlt "vector(k, k, 3, 1)") "[]"))

(deftest "vector: перебор элементов вектора и множества; вложенные — матрица"
  (assert-equal (mlt "vector(k^2, k, [1, 3, 5])") "[1, 9, 25]")
  (assert-equal (mlt "vector(k + 1, k, {3, 1, 2})") "[2, 3, 4]")
  (assert-equal (mlt "vector(vector(i*j, j, 3), i, 3)") "[[1, 2, 3], [2, 4, 6], [3, 6, 9]]")
  (assert-equal (mlt "m := [[1, 2], [3, 4]]; vector(first(r), r, m)") "[1, 3]"))

(deftest "vector: таблица значений функции; k — локальная переменная"
  (assert-equal (mlt "f(x) := x^2 - 1; vector(f(t), t, 0, 3)") "[-1, 0, 3, 8]")
  (assert-equal (mlt "f(x) := x^2 - 1; vector([t, f(t)], t, 0, 2)") "[[0, -1], [1, 0], [2, 3]]")
  ; глобальное k не используется и не портится
  (assert-equal (mlt "k := 5; vector(k, k, 3)") "[1, 2, 3]")
  (assert-equal (mlt "k := 5; vector(k, k, 3); k") "5")
  (assert-equal (mlt "k := 5; vector(k + j, j, 2)") "[6, 7]"))

(deftest "vector: границы не числа — ошибка"
  (assert-error (math-eval "vector(k, k, a, b)"))
  (assert-error (math-eval "vector(k, k, 1, 5, 0)")))

(deftest "sum и product с числовыми границами"
  (assert-equal (mlt "sum(k, k, 1, 100)") "5050")
  (assert-equal (mlt "sum(k^2, k, 1, 10)") "385")
  (assert-equal (mlt "sum(1/k^2, k, 1, 4)") "205/144")
  (assert-equal (mlt "sum(k, k, 5, 1)") "0")
  (assert-equal (mlt "sum(k, k, 1, 10, 3)") "22")
  (assert-equal (mlt "product(k, k, 1, 10)") "3628800")
  (assert-equal (mlt "product(k, k, 5, 1)") "1")
  (assert-equal (mlt "product(1 - 1/k^2, k, 2, 4)") "5/8"))

(deftest "sum: ряд численно (float)"
  (assert-true (< (abs (- (math-eval "sum(1.0/k^2, k, 1, 1000)") 1.6439345666815615)) 0.0000001))
  (assert-true (< (abs (- (math-eval "sum(1.0/k!, k, 0, 15)") 2.718281828459045)) 0.000001)))

(deftest "sum с символьным слагаемым и символьными границами"
  (assert-equal (mlt "sum(x^k, k, 0, 3)") "1 + x + x^2 + x^3")
  (assert-equal (mlt "sum(x*k, k, 1, 3)") "6x")
  (assert-equal (mlt "product(x + k, k, 1, 2)") "(1 + x)(2 + x)")
  ; символьные границы sum — символьное суммирование (21l.1): геометрическая формула
  (assert-equal (mlt "sum(x^k, k, 0, n)") "(-1 + x^(1 + n))/(-1 + x)")
  ; символьные границы product — символьное произведение (21l.8): ∏ k = n!
  (assert-equal (mlt "product(k, k, 1, n)") "n!")
  (assert-equal (mlt "sum(x^k, k, 0, n); sum(x^k, k, 0, 2)") "1 + x + x^2")
  ; присвоенные границы подставляются, ленивое значение пересчитывается
  ; (распознанная сумма — формула: подстановка n в формулу, m-simp; эквивалентна прямой сумме при x ≠ 1)
  (assert-equal (mlt "s := sum(x^k, k, 0, n); n := 2; s") "(-1 + x^3)/(-1 + x)")
  (assert-equal (mlt "n := 3; sum(k, k, 1, n)") "6"))

(deftest "sum и product от вектора и множества"
  (assert-equal (mlt "sum([1, 2, 3, 4])") "10")
  (assert-equal (mlt "product([1, 2, 3, 4])") "24")
  (assert-equal (mlt "sum({1, 5, 10})") "16")
  (assert-equal (mlt "sum([x, x, 1])") "1 + 2x")
  (assert-equal (mlt "sum(k^2, k, [1, 2, 3])") "14")
  (assert-equal (mlt "v := [2, 3, 4]; sum(v) + product(v)") "33"))

(deftest "sum/product: переменная суммирования локальна"
  (assert-equal (mlt "k := 100; sum(k, k, 1, 3)") "6")
  (assert-equal (mlt "k := 100; sum(k, k, 1, 3); k") "100")
  (assert-equal (mlt "f(n) := sum(k^2, k, 1, n); f(10)") "385")
  (assert-equal (mlt "f(n) := sum(k*n, k, 1, 3); f(2)") "12"))

(deftest "функция языка с именем итератора перекрывает его"
  (assert-equal (mlt "sum(a, b) := a*b; sum(2, 3)") "6")
  (assert-equal (mlt "sum := 5; sum + 1") "6"))

(deftest "iterate: n-кратная композиция (метод Ньютона)"
  (assert-equal (mlt "iterate(x^2, x, 2, 3)") "256")
  (assert-equal (mlt "iterate(x + 1, x, 0, 0)") "0")
  (assert-equal (mlt "iterate(x/2 + 1/x, x, 1, 3)") "577/408")
  (assert-true (< (abs (- (math-eval "iterate(x/2 + 1/x, x, 1.0, 6)") 1.4142135623730951)) 0.000000001))
  (assert-equal (mlt "iterate(2*x, x, y, 3)") "8y")
  (assert-error (math-eval "iterate(x + 1, x, 0, a)"))
  (assert-error (math-eval "iterate(x + 1, x, 0, -1)")))

(deftest "iterates: вектор [x0, x1, ..., xn]"
  (assert-equal (mlt "iterates(x/2 + 1/x, x, 1, 3)") "[1, 3/2, 17/12, 577/408]")
  (assert-equal (mlt "iterates(2*x, x, 1, 5)") "[1, 2, 4, 8, 16, 32]")
  (assert-equal (mlt "iterates(x, x, 7, 0)") "[7]")
  (assert-equal (mlt "iterates(x + a, x, 0, 2)") "[0, a, 2a]"))

(deftest "iterate без n — до неподвижной точки"
  (assert-true (< (abs (- (math-eval "iterate(cos(x), x, 1.0)") 0.7390851332151607)) 0.0000001))
  (assert-equal (mlt "iterate(x/2, x, 0)") "0")
  (assert-equal (mlt "iterate(1, x, 5)") "1")
  ; предохранитель: расходящаяся итерация
  (assert-equal (mle "set_loop_limit(20); iterate(x + 1, x, 0)")
                "iterate: неподвижная точка не найдена за 20 итераций (set_loop_limit(n) меняет лимит)")
  (math-eval "set_loop_limit(1000000)"))

(deftest "select(условие, k, v): фильтр вектора, диапазона и множества"
  (assert-equal (mlt "select(mod(k, 2) = 0, k, 1, 10)") "[2, 4, 6, 8, 10]")
  (assert-equal (mlt "select(k > 2, k, [1, 5, 2, 7])") "[5, 7]")
  (assert-equal (mlt "select(k > 100, k, 1, 5)") "[]")
  (assert-equal (mlt "select(k > 1, k, {1, 2, 3})") "[2, 3]")
  ; неопределённое условие — элемент не берётся
  (assert-equal (mlt "select(k > a, k, 1, 3)") "[]"))

(deftest "select: простые числа (проверка — функция языка с return)"
  (assert-equal (mlt "isp(n) := prog(if(n < 2, return(false)), d := 2, loop(if(d*d > n, return(true)), if(mod(n, d) = 0, return(false)), d := d + 1)); select(isp(k), k, 2, 30)")
                "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"))

(deftest "dimension, append, reverse, first, rest, last, position"
  (assert-equal (mlt "dimension([1, 2, 3])") "3")
  (assert-equal (mlt "dimension([[1, 2, 3], [4, 5, 6]])") "[2, 3]")
  (assert-equal (mlt "dimension({1, 2})") "2")
  (assert-equal (mlt "dimension([])") "0")
  (assert-equal (mlt "append([1, 2], [3])") "[1, 2, 3]")
  (assert-equal (mlt "append([1], [2, 3], [4])") "[1, 2, 3, 4]")
  (assert-equal (mlt "append([], [1])") "[1]")
  (assert-equal (mlt "reverse([1, 2, 3])") "[3, 2, 1]")
  (assert-equal (mlt "first([4, 5, 6])") "4")
  (assert-equal (mlt "rest([4, 5, 6])") "[5, 6]")
  (assert-equal (mlt "rest([4])") "[]")
  (assert-equal (mlt "last([4, 5, 6])") "6")
  (assert-equal (mlt "position(5, [4, 5, 6])") "2")
  (assert-equal (mlt "position(9, [4, 5, 6])") "0")
  (assert-error (math-eval "first([])"))
  (assert-error (math-eval "first(5)"))
  (assert-error (math-eval "append([1], 2)")))

(deftest "накопление результата: [] и append в цикле"
  (assert-equal (mlt "r := []; k := 1; loop(if(k > 5, exit), r := append(r, [k*k]), k := k + 1); r") "[1, 4, 9, 16, 25]"))

(deftest "iterate/vector внутри функции видят её локальные переменные"
  (assert-equal (mlt "f(n, a := 2) := vector(k*a, k, n); f(3)") "[2, 4, 6]")
  (assert-equal (mlt "g(x0) := iterate(x/2 + 1/x, x, x0, 2); g(1)") "17/12"))

; ======================= Шаг 21b: компиляция AST в Lisp =======================

; v[i] := e меняет вектор на месте, если он принадлежит только переменной; иначе — копия (значения не разделяются)
(deftest "v[i] := e: копирование при записи, разделяемые векторы не портятся"
  (assert-equal (mlt "v := [1, 2, 3]; w := v; w[1] := 5; v") "[1, 2, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; w := v; w[1] := 5; w") "[5, 2, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; v[1] := 9; w := v; v[2] := 8; w") "[9, 2, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; v[1] := 9; w := v; v[2] := 8; v") "[9, 8, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; v[1] := 9; v[2] := 8; v[3] := 7; v") "[9, 8, 7]")
  (assert-equal (mlt "f(v) := prog(v[1] := 100, v[2] := 200, v); u := [1, 2, 3]; f(u); u") "[1, 2, 3]")
  (assert-equal (mlt "f(v) := prog(v[1] := 100, v[2] := 200, v); u := [1, 2, 3]; f(u)") "[100, 200, 3]")
  ; локальная копия, отданная наружу (w := v), больше не меняется на месте
  (assert-equal (mlt "f(v) := prog(v[1] := 1, w := v, v[2] := 2, w); a := [0, 0]; f(a)") "[1, 0]")
  (assert-equal (mlt "f(v) := prog(v[1] := 1, w := v, v[2] := 2, w); a := [0, 0]; f(a); a") "[0, 0]")
  ; значение переменной, пересчитываемое при чтении (с символами), тоже не разделяется
  (assert-equal (mlt "v := [1, 2, 3]; v[1] := x; x := 5; v[2] := 9; v") "[5, 9, 3]")
  (assert-equal (mlt "v := [x, 2]; w := v; v[2] := 7; x := 1; w") "[1, 2]")
  ; индексы и правая часть вычисляются до чтения вектора
  (assert-equal (mlt "v := [1, 2, 3]; v[1] := prog(v[2] := 7, 5); v") "[5, 7, 3]")
  (assert-equal (mlt "v := [1, 2, 3]; v[2] := v[1] + v[3]; v") "[1, 4, 3]"))

(deftest "v[i] := e: ошибки (тексты)"
  (assert-equal (mle "v := [1, 2, 3]; v[5] := 0") "индекс 5 вне границ 1..3")
  (assert-equal (mle "v := [1, 2]; v[1, 1] := 0") "присваивание элементу: нужно по одному индексу на каждое измерение")
  (assert-equal (mle "q := 5; q[1] := 2") "q — не вектор и не матрица, присваивание элемента невозможно")
  (assert-equal (mle "v := [1, 2]; v[x] := 1") "присваивание элементу: индексы — целые числа")
  (assert-equal (mle "m := [[1, 2], [3, 4]]; m[1] := 7") "присваивание элементу: нужно по одному индексу на каждое измерение")
  (assert-equal (mle "v := [1, 2, 3]; v[7]") "индекс 7 вне границ 1..3")
  (assert-equal (mle "m := [[1, 2], [3, 4]]; m[3]") "индекс 3 вне границ 1..2")
  (assert-equal (mle "f(v) := prog(v[9] := 1, v); f([1, 2])") "индекс 9 вне границ 1..2"))

(deftest "return/exit в «операторных» позициях и через исключения"
  (assert-equal (mlt "f(n) := prog(if(n < 0, return(-1)), if(n = 0, return(0)), n*2); f(-3) + f(0)*10 + f(4)") "7")
  (assert-equal (mlt "f(n) := if(n > 0, return(1), return(2)); f(5) + f(-5)") "3")
  (assert-equal (mlt "f() := loop(if(true, exit(7))); f() + 1") "8")
  ; exit в аргументе итератора внутри цикла — через исключение
  (assert-equal (mlt "k := 0; loop(k := k + 1, vector(if(k > 3, exit), j, 2)); k") "4")
  ; return из тела итератора
  (assert-equal (mlt "f(n) := vector(if(k > 2, return(k), k), k, n); f(5)") "3")
  (assert-equal (mlt "f(n) := vector(if(k > 2, return(k), k), k, n); f(2)") "[1, 2]")
  ; ветвь с продолжением больше порога (продолжение через общую функцию)
  (assert-equal (mlt "s := 0; k := 0; loop(if(k >= 5, exit, prog(a := 1, b := 2, c := 3, d := 4)), k := k + 1, s := s + k + a + b + c + d); s") "65")
  ; вложенные циклы: exit относится к внутреннему
  (assert-equal (mlt "n := 0; i := 0; loop(if(i >= 3, exit), j := 0, loop(if(j >= 4, exit), n := n + 1, j := j + 1), i := i + 1); n") "12")
  ; неопределённое условие — цикл продолжается (по лимиту)
  (assert-equal (mle "set_loop_limit(30); loop(if(zq > 0, exit))")
                "loop: превышен лимит итераций 30 (изменить: set_loop_limit(n); выход из цикла — exit)")
  (math-eval "set_loop_limit(1000000)")
  (assert-equal (mle "f(x) := g(exit); f(1)") "exit: вне цикла loop"))

(deftest "хвостовая рекурсия функций языка и глубокая нехвостовая"
  (assert-equal (mlt "cnt(n, acc := 0) := if(n = 0, acc, cnt(n - 1, acc + 1)); cnt(100000)") "100000")
  (assert-equal (mlt "fct(n) := if(n = 0, 1, n*fct(n - 1)); fct(200) > 10") "true"))

(deftest "поздняя привязка: переопределение функции, определение после вызывающей, clear"
  (assert-equal (mlt "g(x) := h(x) + 1; h(x) := x; a := g(1); h(x) := 10*x; a + g(1)") "13")
  (assert-equal (mlt "g(x) := h(x) + 1; g(1)") "1 + h(1)")
  (assert-equal (mlt "g(x) := h(x) + 1; h(x) := 5; g(1)") "6")
  (assert-equal (mlt "g(x) := h(x) + 1; h(x) := 5; clear(h); g(1)") "1 + h(1)")
  (assert-equal (mlt "f := 5; f(x) := x + f; f(1)") "6")
  (assert-equal (mlt "f(x) := x + 1; f := 5; f + f(1)") "7"))

(deftest "функция с именем итератора, определённая после вызывающей, меняет её смысл; clear возвращает итератор"
  (assert-equal (mlt "q(x) := sum(k, k, 1, x); q(4)") "10")
  (assert-equal (mle "q(x) := sum(k, k, 1, x); sum(p, r) := p*r; q(4)") "sum: ожидается аргументов 2, получено 4")
  (assert-equal (mlt "q(x) := sum(k, k, 1, x); sum(p, r) := p*r; clear(sum); q(4)") "10")
  (assert-equal (mlt "q(x) := sum(k, k, 1, x); sum(p, r) := p*r; sum(2, 3)") "6"))

(deftest "быстрая арифметика не меняет результат: числа и символы"
  (assert-equal (mlt "1/2 + 1/3") "5/6")
  (assert-equal (mlt "1/3*3") "1")
  (assert-equal (mlt "0.5 + 1/2") "1.0")
  (assert-equal (mlt "7/2 - 7/2") "0")
  (assert-equal (mlt "a := 2; a/3 + x") "2/3 + x")
  (assert-equal (mlt "2*x + 3*x") "5x")
  (assert-error (math-eval "1/0"))
  (assert-error (math-eval "x := 0; 1/x")))

(deftest "параметр функции и переменная итератора затеняют глобальные, присваивание идёт в нужную область"
  (assert-equal (mlt "k := 5; f(k) := vector(k*j, j, 3); f(2)") "[2, 4, 6]")
  (assert-equal (mlt "k := 5; f(k) := vector(k*j, j, 3); f(2); k") "5")
  (assert-equal (mlt "f(n) := prog(s := 0, vector(prog(s := s + k, s), k, n)); f(4)") "[1, 3, 6, 10]")
  (assert-equal (mlt "f(n) := prog(s := 0, vector(prog(s := s + k, s), k, n), s); f(4)") "10")
  (assert-equal (mlt "f(n) := vector(prog(n := n + 1, n), k, 3); f(10)") "[11, 12, 13]"))

; ---------- Шаг 21d: интервалы ----------

(deftest "интервалы: литералы читаются, печать однозначна"
  (assert-equal (mlt "[0, 1)") "[0, 1)")
  (assert-equal (mlt "(0, 1]") "(0, 1]")
  (assert-equal (mlt "(0, 1)") "(0, 1)")
  (assert-equal (mlt "(0, ∞)") "(0, ∞)")
  (assert-equal (mlt "(-∞, 0]") "(-∞, 0]")
  (assert-equal (mlt "[1/2, 3)") "[1/2, 3)")
  (assert-equal (mlt "[-1.5, 2*3)") "[-1.5, 6)")
  ; закрытый интервал печатается вызовом: запись [a, b] — вектор
  (assert-equal (mlt "interval(0, 1)") "interval(0, 1)")
  (assert-equal (mlt "[0, 1]") "[0, 1]")
  (assert-true (interval? (math-eval "[0, 1)")))
  (assert-true (not (interval? (math-eval "[0, 1]")))))

(deftest "интервалы: функция interval и бесконечности inf, ∞"
  (assert-equal (mlt "interval(0, inf, closed, open)") "[0, ∞)")
  (assert-equal (mlt "interval(0, 1, open, open)") "(0, 1)")
  (assert-equal (mlt "interval(-inf, 5, open, closed)") "(-∞, 5]")
  (assert-equal (mlt "interval(0, 1, closed, closed)") "interval(0, 1)")
  (assert-equal (mlt "interval(0, ∞, closed, closed)") "[0, ∞)")      ; бесконечный конец всегда открыт
  (assert-error (math-eval "interval(a, 1)"))
  (assert-error (math-eval "[1, 2, 3)")))

(deftest "интервалы: print читается обратно в то же значение (round-trip)"
  (let ((srcs '("[0, 1)" "(0, 1]" "(0, 1)" "(0, ∞)" "(-∞, 0]" "[1/2, 7/3)" "[-1.5, 2.5)" "interval(0, 1)"
                "interval(3, 3)" "interval(2, 1)" "(-∞, ∞)" "[0, ∞)")))
    (map (lambda (s)
           (let* ((v (begin (math-reset) (math-eval s)))
                  (printed (math-show v))
                  (back (begin (math-reset) (math-eval printed))))
             (assert-true (equal? v back))))
         srcs)))

(deftest "интервалы: домены x :∈ (0, ∞), x :∈ [0, 1], in?"
  ; имена ivx… не пересекаются с другими тестами: декларации лежат в plist символов, общем для процесса
  (assert-equal (mlt "ivx :∈ (0, ∞)") "ivx ∈ (0, ∞)")
  (assert-equal (mlt "ivx :∈ (0, ∞); solve(ivx^2 = 4, ivx)") "{2}")
  (assert-equal (mlt "ivy :∈ [0, 1]") "ivy ∈ interval(0, 1)")
  (assert-equal (mlt "ivy :∈ [0, 1]; ivy ∈ [0, 2]") "true")
  (assert-equal (mlt "ivz :∈ [0, 4]; solve(ivz^2 = 4, ivz)") "{2}")
  (assert-equal (mlt "ivw :∈ [0, 1]; solve(ivw^2 = 4, ivw)") "{}")
  (assert-equal (mlt "1/2 ∈ [0, 1]") "true")
  (assert-equal (mlt "2 ∈ (0, 2)") "false")
  (assert-equal (mlt "2 ∈ (0, 2]") "true")
  (assert-equal (mlt "in?(3, [0, 1])") "false")
  (assert-equal (mlt "declare(ivq, [0, 1]); ivq ∈ [-1, 2]") "true")
  (math-reset))

(deftest "интервалы: круглые скобки без запятой — по-прежнему группировка"
  (assert-equal (mlt "(1 + 2)*3") "9")
  (assert-equal (mlt "2*(3 + 4)") "14")
  (assert-equal (mlt "[(1 + 2), 4]") "[3, 4]"))

; ---------- шаг 21i: базисы Грёбнера ----------
(deftest "groebner, normal_form, eliminate в языке"
  (assert-equal (mlt "groebner([x^2 + 2*x*y^2, x*y + 2*y^3 - 1], [x, y])") "[x, -1/2 + y^3]")
  (assert-equal (mlt "groebner([x^3 - 2*x*y, x^2*y + x - 2*y^2], [x, y], grlex)") "[x^2, x*y, -1/2*x + y^2]")
  (assert-equal (mlt "normal_form(x^3 + y^3, [x^2 - y, y^2 - x], [x, y], grevlex)") "2x*y")
  (assert-equal (mlt "normal_form(x^2 + a, [x^2 = 2], [x])") "2 + a")
  (assert-equal (mlt "eliminate([x - t^2, y - t^3], [t], [x, y])") "[x^3 - y^2]")
  (assert-equal (mlt "groebner([x - 1, x - 2], [x])") "[1]")
  (assert-equal (mlt "solve([x^2 + y^2 = 5, x*y = 2], [x, y])")

                "{[x = -2, y = -1], [x = -1, y = -2], [x = 1, y = 2], [x = 2, y = 1]}"))

(deftest "puiseux в языке (A2.2)"
  (assert-equal (mlt "puiseux(y^2 - x^3, x, y, 3)") "[(2 ((1 3/2))), (2 ((-1 3/2)))]"))

; ---------- A3′.7: эллиптические головы в языке ----------

(deftest "a3p7: эллиптические интегралы — печать и ввод"
  (assert-equal (mlt "EllipticF(x, 1/2)") "EllipticF(x, 1/2)")
  (assert-equal (mlt "EllipticK(1/2) + EllipticE(1/2)") "EllipticE(1/2) + EllipticK(1/2)")
  (assert-equal (mlt "EllipticPi(1/2, x, 1/2)") "EllipticPi(1/2, x, 1/2)")
  ; ответ интегратора печатается головой EllipticF и читается обратно (round-trip через math-eval)
  (assert-equal (mlt "integrate(1/sqrt(1-x^4), x)")
                "1/2*2^(1/2)*EllipticF(asin(2^(1/2)*x/sqrt(1 + x^2)), 1/2*2^(1/2))")
  (assert-equal (mls "EllipticF(x, 1/2)") "EllipticF(x, 1/2)"))

; ---------- NT.4: теория чисел в языке ----------

(deftest "NT.4: теория чисел в языке — имена, векторы и результаты"
  (assert-equal (mlt "powmod(3, 12345, 1000000007)") "964676307")
  (assert-equal (mlt "invmod(3, 11)") "4")
  (assert-equal (mlt "crt([2, 3, 2], [3, 5, 7])") "[23, 105]")
  (assert-equal (mlt "crt([1, 2], [2, 4])") "false")
  (assert-equal (mlt "isprime(2^31 - 1)") "true")
  (assert-equal (mlt "isprime(561)") "false")
  (assert-equal (mlt "factorint(360)") "((2 3) (3 2) (5 1))")
  (assert-equal (mlt "totient(1000000)") "400000")
  (assert-equal (mlt "pell(61)") "(1766319049 226153980)")
  (assert-equal (mlt "pell_negative(13)") "(18 5)")
  (assert-equal (mlt "pell_solutions(2, 3)") "((3 2) (17 12) (99 70))")
  (assert-equal (mlt "sum_of_two_squares(2210)") "(41 23)")
  (assert-equal (mlt "pythagorean_triples(30)")
                "((3 4 5) (5 12 13) (8 15 17) (7 24 25) (20 21 29))")
  (assert-equal (mlt "solve_linear_diophantine(3, 5, 7)") "((4 -1) (5 -3))")
  ; конечное поле GF(2⁸): {53}⁻¹ = {CA} = 202
  (assert-equal (mlt "gf_to_int(gf(2, x^8 + x^4 + x^3 + x + 1, x), gf_inv(gf(2, x^8 + x^4 + x^3 + x + 1, x), 83))") "202")
  (let ((c (math-eval "prime_certificate(97)")))       ; сертификат — дерево, проверяем его целиком
    (assert-equal (car c) 97)
    (assert-true (pratt-check c))))

; ---------- WASM.6a Д2: inverse в языке ----------

(deftest "WASM.6a Д2: inverse([[…]]) вычисляется и проверяется умножением"
  (assert-equal (mlt "inverse([[1, 2], [3, 4]])") "[[-2, 1], [3/2, -1/2]]")
  (assert-equal (mlt "inverse([[1, 2], [3, 4]])*[[1, 2], [3, 4]]") "[[1, 0], [0, 1]]")
  (assert-equal (mlt "[[1, 2], [3, 4]]*inverse([[1, 2], [3, 4]])") "[[1, 0], [0, 1]]")
  ; вырожденная матрица — ошибка «матрица вырождена», а не невычисленный вызов
  (assert-equal (mle "inverse([[1, 2], [2, 4]])") "inv: матрица вырождена (det = 0)"))

; ---------- WASM.6a Д5: ротор в ℝ² — скаляр ----------

(deftest "WASM.6a Д5: curl в ℝ² — скалярное выражение, в ℝ³ — вектор"
  (assert-equal (mlt "curl([x*y, x*y], [x, y])") "-x + y")
  (assert-equal (mlt "curl([y, -x, 0], [x, y, z])") "[0, 0, -2]")
  (assert-equal (mlt "curl([x^2, x*y], [x, y])") "y"))

; ---------- русские записи функций: arcsin, arctg, tg, ctg, … ----------

(deftest "имена arcsin/arccos/arctg/arcctg/tg/ctg/cosec читаются как asin/acos/atan/acot/tan/cot/csc"
  (assert-equal (mlt "arccos(0)") "1/2*pi")
  (assert-equal (mlt "arctg(1)") "1/4*pi")
  (assert-equal (mlt "arctan(1)") "1/4*pi")
  (assert-equal (mlt "tg(pi/4)") "1")
  (assert-equal (mlt "ctg(pi/4)") "1")
  (assert-equal (mlt "cosec(pi/2)") "1")
  (assert-equal (mlt "arcctg(x)") "acot(x)")
  (assert-equal (mlt "arcsinh(x)") "asinh(x)")
  (assert-equal (mlt "arsh(x) + arch(x) + arth(x)") (mlt "asinh(x) + acosh(x) + atanh(x)"))
  (assert-equal (mlt "diff(arcsinh(x), x)") (mlt "diff(asinh(x), x)"))
  (assert-equal (mlt "diff(arcsin(x), x)") "1/sqrt(1 - x^2)")
  (assert-equal (mlt "integrate(tg(x), x)") "-log(cos(x))")
  ; переменная с таким именем — по-прежнему переменная
  (assert-equal (mlt "tg := 5; tg + 1") "6"))

(deftest "** — степень, как ^: правоассоциативна, с унарным минусом"
  (assert-equal (mlt "x**2") "x^2")
  (assert-equal (mlt "2**3**2") "512")
  (assert-equal (mlt "x**-1") "1/x")
  (assert-equal (mlt "-x**2") "-x^2")
  (assert-equal (mlt "(a+b*x)**(1/2)") (mlt "(a+b*x)^(1/2)"))
  (assert-equal (mlt "2*x**3") "2x^3"))
