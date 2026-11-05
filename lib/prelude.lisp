; prelude.lisp — библиотека на Lisp, загружается при создании глобального окружения
; (каталог lib\ копируется в выходной каталог сборки). Здесь живут CAS-типы,
; написанные на Lisp поверх механизма Шага 14 (объекты, векторы, deftype, defmethod).
; Шаг 15: базовые списочные функции и тензор (tensor.lisp).

; Шаг 21h': модуль prelude — базовые списочные и векторные функции (экспорт); вспомогательные «-acc»/«-onto»/«-from» приватны.
; Остальные библиотеки загружаются отсюда, каждая — своим модулем (первая форма файла: (module имя (export ...)))
(module prelude
  (export prelude-loaded range
          take drop last butlast member? append-map sort vector-map vector-map2
          when unless for-each while do gensym delay force cons-stream stream-car stream-cdr
          stream-null? stream-take stream-map stream-filter))

(define prelude-loaded #t)

; --- LANG.2: управляющие формы (макросы; тела — с TCO) ---

; (when условие тело...) — тело, если условие истинно, иначе (); unless — наоборот
(defmacro (when c &rest body) `(if ,c (begin ,@body) '()))
(defmacro (unless c &rest body) `(if ,c '() (begin ,@body)))

; (for-each f l ...) — применить f к элементам (коротчайший список), ради эффекта; → ()
(defmacro (for-each f l &rest more)
  (if (null? more)
      `(begin (map ,f ,l) '())
      `(begin (map2 ,f ,l ,(car more)) '())))

; (while условие тело...) — повторять, пока условие истинно; → ()
; имя цикла — gensym при раскрытии: имена пользователя не захватываются
(defmacro (while c &rest body)
  (let ((loop (gensym "while-")))
    `(let ,loop ()
       (if ,c (begin ,@body (,loop)) '()))))

; (do ((var init [step]) ...) (тест [результат]) тело...) — как в Scheme: связывает переменные,
; пока тест ложен — выполняет тело и сдвигает переменные (step не указан — переменная не меняется);
; тест истинен → результат (по умолчанию ())
(defmacro (do vars exit &rest body)
  (let ((loop (gensym "do-")))
    (let ((test (car exit))
          (result (if (null? (cdr exit)) '(begin) (cadr exit)))
          (steps (map (lambda (v) (if (or (null? (cddr v)) (null? (caddr v))) (car v) (caddr v))) vars)))
      `(let ,loop ,(map (lambda (v) (list (car v) (cadr v))) vars)
         (if ,test
             ,result
             (begin ,@body (,loop ,@steps)))))))

; (gensym [префикс]) — свежий символ вида g1, g2… (глобальный счётчик; для макросов без захвата имён)
(define *gensym-counter* 0)
(define (gensym &rest args)
  (set! *gensym-counter* (+ *gensym-counter* 1))
  (let ((prefix (if (null? args) "g" (car args))))
    (string->symbol (string-append (if (string? prefix) prefix (to-string prefix))
                                    (number->string *gensym-counter*)))))

; --- LANG.2: delay/force и потоки ---

; Обещание: пара ('promise . замыкание) с мемоизацией; ячейки — gensym при раскрытии (имена пользователя не захватываются)
(defmacro (delay expr)
  (let ((done (gensym "promise-done-")) (val (gensym "promise-val-")) (r (gensym "promise-r-")))
    `(cons 'promise
           (let ((,done #f) (,val #f))
             (lambda ()
               (if ,done ,val (let ((,r ,expr)) (set! ,done #t) (set! ,val ,r) ,r)))))))

; (force p) — вычислить обещание (мемоизирует); прочее значение — как есть
(define (force p)
  (if (and (pair? p) (equal? (car p) 'promise))
      ((cdr p))
      p))

; (cons-stream a b) — поток: голова строгая, хвост — обещание (b НЕ вычисляется при построении)
(defmacro (cons-stream a b)
  `(cons ,a (delay ,b)))
(define (stream-car s) (car s))
(define (stream-cdr s) (force (cdr s)))
(define (stream-null? s) (null? s))
(define (stream-take s n)
  (if (or (= n 0) (stream-null? s))
      '()
      (cons (stream-car s) (stream-take (stream-cdr s) (- n 1)))))
(define (stream-map f s)
  (if (stream-null? s)
      '()
      (cons-stream (f (stream-car s)) (stream-map f (stream-cdr s)))))
(define (stream-filter p? s)
  (if (stream-null? s)
      '()
      (let ((h (stream-car s)))
        (if (p? h)
            (cons-stream h (stream-filter p? (stream-cdr s)))
            (stream-filter p? (stream-cdr s))))))

; --- Списки (все функции хвосторекурсивны через накопитель — TCO в eval) ---

; Шаг 21i' (e): reverse, map, map2, filter, foldl, any?, every? — builtin на F# (ListBuiltins.fs): быстрое применение
; лямбды без списка аргументов. Ниже — оставшиеся списочные функции на Lisp (используют reverse из builtin)
; (reverse-onto l acc) — перевёрнутый l поверх acc (нужен sort-merge)
(define (reverse-onto l acc)
  (if (null? l) acc (reverse-onto (cdr l) (cons (car l) acc))))

; (range n) — (0 1 ... n-1)
(define (range-acc i acc)
  (if (< i 0) acc (range-acc (- i 1) (cons i acc))))
(define (range n) (range-acc (- n 1) '()))

; (take l n), (drop l n), (last l), (butlast l), (member? x l) — вспомогательные
(define (take-acc l n acc)
  (if (or (<= n 0) (null? l)) (reverse acc) (take-acc (cdr l) (- n 1) (cons (car l) acc))))
(define (take l n) (take-acc l n '()))
(define (drop l n) (if (or (<= n 0) (null? l)) l (drop (cdr l) (- n 1))))
(define (last l) (if (null? (cdr l)) (car l) (last (cdr l))))
(define (butlast l) (take l (- (length l) 1)))
(define (member? x l)
  (cond ((null? l) #f)
        ((equal? x (car l)) #t)
        (else (member? x (cdr l)))))
(define (append-map f l) (apply append (map f l)))
;
; (sort l less?) — устойчивая сортировка слиянием (шаг 21i; раньше сортировки в библиотеке не было — модули писали
; вставки сами): (sort '(3 1 2) <) → (1 2 3); less? — строгий порядок, равные элементы сохраняют исходный порядок
(define (sort-merge a b less? acc)
  (cond ((null? a) (reverse-onto acc b))
        ((null? b) (reverse-onto acc a))
        ((less? (car b) (car a)) (sort-merge a (cdr b) less? (cons (car b) acc)))
        (else (sort-merge (cdr a) b less? (cons (car a) acc)))))
(define (sort-split l n acc)                    ; первые n элементов (в обратном порядке) и остаток
  (if (= n 0) (cons acc l) (sort-split (cdr l) (- n 1) (cons (car l) acc))))
(define (sort l less?)
  (let ((n (length l)))
    (if (< n 2)
        l
        (let ((h (sort-split l (quotient n 2) '())))
          (sort-merge (sort (reverse (car h)) less?) (sort (cdr h) less?) less? '())))))

; --- Векторы-массивы ---

; (vector-map f v) — новый вектор из (f компонент) для каждого компонента v
(define (vector-map-from f v r i)
  (if (< i (vlength v))
      (begin (vset! r i (f (vref v i))) (vector-map-from f v r (+ i 1)))
      r))
(define (vector-map f v) (vector-map-from f v (make-vector (vlength v) 0) 0))

; (vector-map2 f u v) — покомпонентно по двум векторам одинаковой длины
(define (vector-map2-from f u v r i)
  (if (< i (vlength r))
      (begin (vset! r i (f (vref u i) (vref v i))) (vector-map2-from f u v r (+ i 1)))
      r))
(define (vector-map2 f u v) (vector-map2-from f u v (make-vector (vlength u) 0) 0))

; Тензор (Шаг 15) — написан на Lisp поверх объектов, векторов и defmethod
(load (string-append lib-dir "tensor.lisp"))

; Шаг 16: трёхзначная логика, конечные множества, домены с декларациями, условные правила упрощения.
; Порядок важен: logic → set → domain → rules (набор join-strings для печати множеств — из tensor.lisp)
(load (string-append lib-dir "logic.lisp"))
(load (string-append lib-dir "set.lisp"))
(load (string-append lib-dir "domain.lisp"))
(load (string-append lib-dir "rules.lisp"))

; Шаг AC.1: AC-сопоставление с образцом (+ и * — мультимножества, сегментные переменные ?r...); только builtins
(load (string-append lib-dir "match.lisp"))

; Шаг 17: обёртки над многочленами и рациональными функциями (builtins — на F#)
(load (string-append lib-dir "poly.lisp"))

; Шаг A1: поле ℚ(α) = ℚ[t]/(m) — арифметика, минимальный многочлен, примитивный элемент (21m A1.1–A1.2)
(load (string-append lib-dir "algnum.lisp"))
(load (string-append lib-dir "puiseux.lisp"))

; Шаг NT.1: теория чисел на целых числах (модулярная арифметика, КТО, простота, факторизация) с сертификатами
(load (string-append lib-dir "numtheory.lisp"))

; Шаг NT.3: конечные поля GF(pⁿ) (арифметика с сертификатами, неприводимость по Рабину, разложение Кантора–Цассенхауса)
(load (string-append lib-dir "gf.lisp"))

; Шаг FLD.1: алгоритмы один раз для любого поля (после algnum, numtheory, gf)
(load (string-append lib-dir "field.lisp"))

; Шаг A3.1/A3.2: плоские кривые: особые точки, род, параметризация (после puiseux и field)
(load (string-append lib-dir "curves.lisp"))

; Шаг A3′.3: головы эллиптических интегралов (конструкторы; численные значения — в F#)
(load (string-append lib-dir "elliptic.lisp"))

; Шаг A1.5: денестинг радикалов глубины 2 и нормальная форма ℚ(α) (после algnum)
(load (string-append lib-dir "denest.lisp"))
; (alg-equal? e1 e2) — точное равенство выражений с радикалами (2 арг);
; прежняя функция поля (alg-equal? F a b) из algnum работает через 3 аргумента
(define alg-equal-field? alg-equal?)
(set! alg-equal?
      (lambda (a b &rest rest)
        (if (null? rest)
            (alg-equal-expr? a b)
            (alg-equal-field? a b (car rest)))))

; Шаг S.1: пошаговые решения — макросы with-step и steps (до модулей, которые пишут шаги: макрос раскрывается при
; компиляции вызывающей функции)
(load (string-append lib-dir "steps.lisp"))

; Шаг 18: решение уравнений (после rules и poly: опирается на домены, множества, factor-list, real-roots)
(load (string-append lib-dir "solve.lisp"))
; Шаг LA.1: линейная алгебра (после solve: solve::rref-step, factor-list, solve; тензор загружен выше)
(load (string-append lib-dir "linalg.lisp"))
; Шаг RE.1: C-конечные последовательности (после linalg: свёрка с mat-power в тестах)
(load (string-append lib-dir "cfinite.lisp"))
  ; Шаг LP.1: линейное программирование (двухфазный симплекс, правило Бленда)
  (load (string-append lib-dir "lp.lisp"))
; Шаг DP.1: динамическое программирование с сертификатами (после lp)
(load (string-append lib-dir "dp.lisp"))
; Шаг CN.1: интервальная арифметика с точными рациональными концами
(load (string-append lib-dir "interval.lisp"))
; Шаг R4: нуль замкнутых констант (интервалы + тождества + unknown; после interval, denest, numtheory; до risch)
(load (string-append lib-dir "constzero.lisp"))
; Шаг DIM.1: величины с единицами, перевод, проверка размерности
(load (string-append lib-dir "units.lisp"))
; Шаг OPT.1: критические точки, гессиан, множители Лагранжа (после solve и linalg)
(load (string-append lib-dir "optimize.lisp"))
; Шаг 21i: базисы Грёбнера (после solve: rational-number?; solve вызывает groebner для нелинейных систем)
(load (string-append lib-dir "groebner.lisp"))

; Шаг N1: финальная тригонометрическая нормализация (trigsimp; до integrate — его финальная доводка использует)
(load (string-append lib-dir "trigsimp.lisp"))

; Шаг 19: символьное интегрирование (после solve: использует x-free?, replace-expr, numeric-poly?, real-roots)
; Шаг 21h': integrate разрезан на части (каталог integrate\); порядок = порядок регистрации стратегий каскада
(load (string-append lib-dir "integrate/core.lisp"))
(load (string-append lib-dir "integrate/rational.lisp"))
(load (string-append lib-dir "integrate/trig.lisp"))
; Шаг A3′.1: теорема Чебышёва о биномиальном дифференциале (после trig — общий каскад)
(load (string-append lib-dir "integrate/chebyshev.lisp"))
; Шаг A3′.3: приведение к эллиптическим формам Лежандра (F/E), численная проверка
(load (string-append lib-dir "integrate/elliptic.lisp"))
; Шаг A3′.2: интегралы на кривых рода 0 (после эллиптики)
(load (string-append lib-dir "integrate/genus0.lisp"))
; Шаг A4.1a: целый базис и алгебраический Эрмит для y^n = P
(load (string-append lib-dir "integrate/algebraic.lisp"))
; Шаг A4.2: целый базис общей кривой (ван Хуй через Пюизё)
(load (string-append lib-dir "integrate/intbasis.lisp"))
; Шаг A5.1: места, ряды и вычеты гиперэллиптической кривой y² = P
(load (string-append lib-dir "integrate/divisor.lisp"))
; Шаг R5.3a: арифметика Кантора якобиана y² = P(x), deg P нечётна
(load (string-append lib-dir "integrate/cantor.lisp"))
; Шаг R1-хвост: места над ℚ(α) степени ≥ 3 в логарифмической части y² = P
(load (string-append lib-dir "integrate/placesnf.lisp"))
; Шаг R3: гладкие коники рода 0 и смешанный случай Риша (после алгебраической стратегии, до parts)
(load (string-append lib-dir "integrate/mixed.lisp"))
(load (string-append lib-dir "integrate/parts.lisp"))
(load (string-append lib-dir "integrate/check.lisp"))
; параметры в интегралах: разбор случаев по знаку/нулю параметра, piecewise
(load (string-append lib-dir "integrate/param.lisp"))
(load (string-append lib-dir "integrate/api.lisp"))

; Шаг ODE.0: каркас ОДУ (после integrate/solve/linalg)
(load (string-append lib-dir "ode/core.lisp"))
; Шаг ODE.1: первый порядок
(load (string-append lib-dir "ode/first-order.lisp"))
; Шаг ODE.2: точные уравнения, интегрирующий множитель, Риккати, Клеро/Лагранж
(load (string-append lib-dir "ode/exact.lisp"))

; Шаг G1: перестановочные группы (Шрайер — Симс, смежные классы, Тодд — Коксетер)
(load (string-append lib-dir "group.lisp"))
; Шаг GAL: группа Галуа (транзитивные группы ≤ 7, Дедекинд, дискриминант)
(load (string-append lib-dir "galois.lisp"))
; Шаг ODE.3: линейные с постоянными коэффициентами
(load (string-append lib-dir "ode/linear.lisp"))
; Шаг ODE.4a: уравнение Эйлера–Коши
(load (string-append lib-dir "ode/euler.lisp"))
; Шаг ODE.4a: задача Коши (условия в dsolve)
(load (string-append lib-dir "ode/cauchy.lisp"))
; Шаг ODE.5a: системы x′ = A·x + f, ОДУ ↔ система
(load (string-append lib-dir "ode/systems.lisp"))
; Шаг ODE.5b: понижение порядка, уравнения без y и автономные
(load (string-append lib-dir "ode/reduction.lisp"))
; Шаг ODE.7: ряды — обыкновенная точка (Тейлор) и метод Фробениуса
(load (string-append lib-dir "ode/series.lisp"))
; Шаг ODE.8a: алгоритм Ковачича (нормальная форма, условия, случай 1)
(load (string-append lib-dir "ode/kovacic.lisp"))
; Шаг ODE.9: ответы dsolve через головы Бесселя/Эйри/Лежандра/₂F₁ (после Ковачича и голов SFn.2)
(load (string-append lib-dir "ode/specfun-ode.lisp"))

; Шаг 21k: алгоритм Риша — арифметика K[θ] над башней exp-log (подшаг 21k.1; дальше tower/reduce/driver/rde)
(load (string-append lib-dir "risch/field.lisp"))
(load (string-append lib-dir "risch/tower.lisp"))
(load (string-append lib-dir "risch/reduce.lisp"))
(load (string-append lib-dir "risch/rde.lisp"))
(load (string-append lib-dir "risch/prde.lisp"))
(load (string-append lib-dir "risch/tan.lisp"))
(load (string-append lib-dir "risch/driver.lisp"))
(load (string-append lib-dir "risch/special.lisp"))

; Шаг DF.1: внешнее исчисление — дифференциальные формы и векторный анализ (после integrate)
(load (string-append lib-dir "forms.lisp"))
; Шаг MINT.a: кратные интегралы, замена переменных с якобианом, интегралы первого рода (после forms и integrate)
(load (string-append lib-dir "multiint.lisp"))
; Шаг PROB: вероятность и статистика — распределения как данные, pdf/cdf/моменты, выборка, Байес (после integrate и summation)
(load (string-append lib-dir "prob.lisp"))

; Шаг 20: ряды Тейлора/Лорана (после integrate: значения функций в точке считает simplify)
(load (string-append lib-dir "series.lisp"))
; Шаг 21j.1: пределы exp-log-функций по Грунцу (MRV) — после series (ряды по ω), до limit; в limit пока не встроен
(load (string-append lib-dir "gruntz.lisp"))
; Шаг 20: пределы (ряды, Лопиталь, арифметика с ±inf)
(load (string-append lib-dir "limit.lisp"))

; Шаг 15b: мини-фреймворк тестов (deftest, assert-equal, assert-true, assert-error)
(load (string-append lib-dir "test.lisp"))

; Шаг 21l.1: символьное суммирование (диспетчер sum-symbolic для sum с символьными границами;
; каскад sum-strategies L0–L2: линейность, Карр, Фаульхабер, геометрическая, harmonic)
(load (string-append lib-dir "summation/core.lisp"))
; Шаг 21l.2: классификатор гипергеометрических термов (hyper-ratio), poly-shift, дисперсия
(load (string-append lib-dir "summation/hyper.lisp"))
; Шаг 21l.3: алгоритм Госпера — gosper-normal/gosper-term/gosper-sum;
; стратегия подключается к каскаду sum-strategies внутри самого модуля (gosper.lisp)
(load (string-append lib-dir "summation/gosper.lisp"))
; Шаг 21l.4: рациональное суммирование по Абрамову — abramov-decompose/abramov-sum;
; стратегия подключается к каскаду внутри модуля (abramov.lisp), после Госпера
(load (string-append lib-dir "summation/abramov.lisp"))
(load (string-append lib-dir "summation/zeilberger.lisp"))
(load (string-append lib-dir "summation/hyper-solve.lisp"))
(load (string-append lib-dir "summation/product.lisp"))

; Шаг 21: вычислитель входного математического языка (после всех библиотек: вызывает solve/integrate/limit/series/...)
(load (string-append lib-dir "mathlang/runtime.lisp"))
(load (string-append lib-dir "mathlang/compiler.lisp"))

; Шаг P1: двумерные графики в SVG (plot-sample, plot-svg, plot, plot-info)
(load (string-append lib-dir "plot.lisp"))

; Шаг TR.1: преобразование Лапласа (laplace, inverse-laplace, laplace-check, convolve, heaviside, dirac)
(load (string-append lib-dir "laplace.lisp"))

; Шаг TR.3: Z-преобразование, разностные уравнения, преобразование Фурье
(load (string-append lib-dir "transforms.lisp"))

; Шаг SOS: неравенства многочленов — суммы квадратов, AM-GM, сертификаты (prove-nonneg, sos-check)
(load (string-append lib-dir "sos.lisp"))
; Шаг DI.1: несобственные определённые интегралы (definite-integral, definite-check, definite-convergence)
(load (string-append lib-dir "definite.lisp"))
; Шаг CV: вариационное исчисление (euler-lagrange, var-first-integrals, variational-solve, …)
(load (string-append lib-dir "variational.lisp"))
; Шаг SFn.1: Γ, B, ψ, гипергеометрические ₚFq, hyperexpand, сертификаты (specfun-simplify, hyperexpand, specfun-check)
(load (string-append lib-dir "specfun.lisp"))
