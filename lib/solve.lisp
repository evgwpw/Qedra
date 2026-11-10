; solve.lisp — решение уравнений (Шаг 18). Логика — на Lisp; вычислительное ядро (factor-list, real-roots,
; together/numer/denom, coeff/degree, subst, eval-num) — F#-примитивы шагов 17 и 18.
;
; (solve уравнение x) — уравнение: (= a b) или выражение (означает = 0). Результат — МНОЖЕСТВО решений (тип set).
;   * нет решений → пустое множество; тождество → домен/интервал x (объявленный или complexes);
;   * решения, для которых (in? решение D) = #f хотя бы для одного ограничения D из деклараций x, отбрасываются;
;     unknown — остаются (условных решений не порождаем);
;   * без деклараций x ∈ ℂ: комплексные решения (в %i-форме) возвращаются.
; Соглашения:
;   (root-of p x) — элемент множества: «остальные (невещественные) корни неприводимого многочлена p» (кратность не возвращается);
;       для нелинейных уравнений-обёрток (корни сложной функции от x) — «остальные решения уравнения p = 0».
;   k1, k2, ... — целочисленные параметры бесконечных серий решений (sin, cos, tan); символы объявляются integers;
;       нумерация начинается с k1 при каждом вызове solve.
;   Символьные коэффициенты: степень 1–2 — формулы (без ветвления по обращению старшего коэффициента в 0), выше — root-of.
;   Для log/exp в ℂ ветви 2πi·k не добавляются (главная ветвь): exp(u) = -c → u = log c + %i·pi.
; Не умеем → ошибка «solve: не умею решать ...» (молчаливого пустого множества не бывает).

; Шаг 21h': модуль solve. Экспорт — solve и предикаты/подстановка, которыми пользуются integrate, series, limit
; (rational-number?, real-numeric?, x-free?, root-of?, numeric-poly?, replace-expr); остальное (в т. ч. find-pivot,
; перекрывавший одноимённый из tensor.lisp) — приватное
(module solve
  (export solve solve-check rational-number? real-numeric? x-free? root-of? numeric-poly? replace-expr))

; ---------- вспомогательное ----------

(define (rational-number? v) (or (integer? v) (equal? (type-of v) 'rational)))
(define (real-numeric? v) (and (number? v) (not (equal? (type-of v) 'complex))))
(define (x-free? e x) (not (contains-sym? e x)))
(define (root-of? v) (and (list? v) (not (null? v)) (equal? (car v) 'root-of)))

(define (solve-fail e x)
  (error (string-append "solve: не умею решать " (math-print e) " относительно " (to-string x))))

; уравнение → выражение (левая часть минус правая)
(define (equation->expr eq)
  (if (and (list? eq) (not (null? eq)) (equal? (car eq) '=))
      (simplify (list '- (cadr eq) (caddr eq)))
      (simplify eq)))

(define (mk-log v) (if (equal? v 1) 0 (simplify (list 'log v))))
(define (mk-exp v) (simplify (list 'exp v)))

; новый целочисленный параметр k1, k2, ... (счётчик сбрасывается в начале solve)
(define *k-counter* 0)
(define *solve-ks* '())
(define (fresh-k)
  (set! *k-counter* (+ *k-counter* 1))
  (let ((k (string->symbol (string-append "k" (to-string *k-counter*)))))
    (declare k integers)
    (set! *solve-ks* (cons k *solve-ks*))
    k))

; ---------- шаги (шаг S.4) ----------
; Рамки with-step: solve-equation (верх), solve-move-terms, solve-linear / solve-quadratic / solve-polynomial (по степени),
; solve-factor, solve-substitution, solve-inverse-function / solve-isolate, solve-square, solve-trig-ratio,
; solve-clear-denominator, solve-exclude-denominator-roots, solve-check-roots, solve-domain-filter, solve-linear-system.
; Всё, что нужно только шагам, считается под (step-log-enabled?) или внутри with-step (при выключенном журнале — не вычисляется).

; основная переменная текущего solve (имена в шагах)
(define *solve-var* 'x)

; временная переменная %t в шагах пишется как t (u, если неизвестная — t)
(define (st-tname) (if (equal? *solve-var* 't) 'u 't))
(define (st-disp e) (if (contains-sym? e '%t) (replace-expr e '%t (st-tname)) e))
(define (st-var x) (if (equal? x '%t) (st-tname) x))

; многочлен по x в порядке убывания степеней (2x² − 5x + 6, а не 6 − 5x + 2x²) — для шагов
(define (st-negative-term? t)
  (or (and (real-numeric? t) (< t 0))
      (and (op-expr? t) (equal? (car t) '*) (real-numeric? (cadr t)) (< (cadr t) 0))))

; члены, отрицательные — через вычитание: x^2 - 5x + 6 (а не x^2 + (-5)x + 6)
(define (st-sum-form terms)
  (foldl (lambda (acc t) (if (st-negative-term? t) (list '- acc (simplify (list '* -1 t))) (list '+ acc t)))
         (car terms) (cdr terms)))

(define (st-desc p x)
  (if (and (symbol? x) (not (x-free? p x)) (polynomial? p x))
      (let ((d (degree p x)))
        (if (integer? d)
            (let ((terms (filter (lambda (t) (not (equal? t 0)))
                                 (map (lambda (j) (simplify (list '* (coeff p x j) (list '^ x j))))
                                      (map (lambda (j) (- d j)) (range (+ d 1)))))))
              (if (null? terms) p (st-sum-form terms)))
            p))
      p))

; уравнение «p = 0» относительно x для шагов
(define (st-eq p x) (list '= (st-desc (st-disp p) (st-var x)) 0))

; решения → «x = a», «x = a or x = b» или пустое множество
(define (st-sols x r)
  (cond ((null? r) (list->set '()))
        ((null? (cdr r)) (list '= (st-var x) (st-disp (car r))))
        (else (cons 'or (map (lambda (v) (list '= (st-var x) (st-disp v))) r)))))

(define (st-list l) (cons 'list (map st-disp l)))

; значение в скобках, если оно отрицательное или составное
(define (st-pn v)
  (let ((s (math-print (st-disp v))))
    (if (or (string-contains? s "-") (string-contains? s " ")) (string-append "(" s ")") s)))

(define (st-quiet thunk) (if (step-log-enabled?) (call-quietly thunk) (thunk)))

; пояснение к решению многочлена степени 1, 2 или выше
(define (solve-deg p x) (let ((d (degree p x))) (if (integer? d) d 0)))

(define (solve-linear-comment p x r)
  (let ((a (coeff p x 1)) (b (coeff p x 0)))
    (string-append "ax + b = 0 ⇒ x = −b/a; здесь a = " (math-print a) ", b = " (math-print b)
                   (if (number? a) "" "; условие a ≠ 0 записано в conditions"))))

(define (solve-quadratic-comment p x cx)
  (let* ((a (coeff p x 2)) (b (coeff p x 1)) (c (coeff p x 0))
         (D (expand (list '- (list '^ b 2) (list '* 4 a c))))
         (head (string-append "a = " (math-print a) ", b = " (math-print b) ", c = " (math-print c)
                              "; дискриминант D = b² − 4ac = " (st-pn b) "² − 4·" (st-pn a) "·" (st-pn c)
                              " = " (math-print D))))
    (cond ((not (number? D)) (string-append head "; корни x = (−b ± √D)/(2a)"))
          ((> D 0) (string-append head " > 0: два корня x = (−b ± √D)/(2a)"))
          ((= D 0) (string-append head ": один корень x = −b/(2a)"))
          (cx (string-append head " < 0: два комплексных корня x = (−b ± √D)/(2a)"))
          (else (string-append head " < 0: вещественных корней нет")))))

(define (solve-polynomial-comment p x cx r)
  (string-append "многочлен степени " (to-string (solve-deg p x))
                 (if (numeric-poly? p x)
                     (string-append " без рациональных корней: вещественные корни — алгебраические числа (изоляция корней по Штурму)"
                                    (if (any? root-of? r) "; остальные (невещественные) корни записаны как root-of" ""))
                     " с параметрами: корни записаны как root-of")))

(define (solve-deg-rule d) (cond ((= d 1) 'solve-linear) ((= d 2) 'solve-quadratic) (else 'solve-polynomial)))
(define (solve-deg-title d)
  (cond ((= d 1) "Линейное уравнение") ((= d 2) "Квадратное уравнение") (else "Уравнение высокой степени")))

; рамка по степени многочлена p (корни — прежний алгоритм solve-poly-plain)
(define (solve-poly-step p x cx)
  (with-step ((solve-deg-rule (solve-deg p x)) (solve-deg-title (solve-deg p x)) (st-eq p x)
              :comment (lambda (r) (let ((d (solve-deg p x)))
                                     (cond ((= d 1) (solve-linear-comment p x r))
                                           ((= d 2) (solve-quadratic-comment p x cx))
                                           (else (solve-polynomial-comment p x cx r)))))
              :after (lambda (r) (st-sols x r)))
    (solve-poly-plain p x cx)))

; разложение на множители: p = c·f1^k1·…; «после» — произведение, дети — решения каждого множителя
(define (st-product fl x)
  (cons '* (append (if (equal? (car fl) 1) '() (list (car fl)))
                   (map (lambda (pe) (let ((f (st-desc (st-disp (car pe)) (st-var x))))
                                       (if (= (cadr pe) 1) f (list '^ f (cadr pe)))))
                        (cdr fl)))))

(define (solve-factor-step e fs fl x cx)
  (with-step ('solve-factor "Разложение на множители" (st-eq e x)
              :comment (lambda (r) (string-append "произведение равно нулю, когда хотя бы один множитель равен нулю: "
                                                  (foldl (lambda (acc pe) (string-append acc (if (equal? acc "") "" " или ")
                                                                                         (math-print (st-desc (st-disp (car pe)) (st-var x))) " = 0"))
                                                         "" fs)))
              :after (lambda (r) (list '= (st-product fl x) 0)))
    (append-map (lambda (pe) (solve-poly-step (car pe) x cx)) fs)))

; решение выражения-многочлена e (= 0) по x; биквадратные с точными радикалами — radical-roots (A1.6).
; Перехват — только когда над ℚ многочлен неприводим (один множитель кратности 1 степени 4):
; иначе прежний путь (x^4−1 и т. п. раскладываются и решаются как раньше).
(define (solve-poly-plain e x cx)
  (let* ((fl (factor-list e)) (body (cdr fl)))
    (if (and (= (length body) 1)
             (= (cadr (car body)) 1)
             (= (degree (car (car body)) x) 4))
        (let ((r (try (radical-roots e x) (lambda (err) #f))))
          (if (and r (not (null? r)))
              r
              (append-map (lambda (pe) (solve-factor (car pe) x cx)) body)))
        (append-map (lambda (pe) (solve-factor (car pe) x cx)) body))))

; решение содержит параметр серии или root-of — не проверяется подстановкой
(define (special-solution? s)
  (or (contains-sym? s 'root-of) (any? (lambda (k) (contains-sym? s k)) *solve-ks*)))

; ---------- нормализация: sqrt → степень 1/2 ----------
; (exp(n·u) = (exp u)^n упрощатель сливает сам — Шаг 21c; ядро exp(u) выделяет subst-exp-kernel)

(define (norm-tree e)
  (if (op-expr? e)
      (let ((args (map norm-tree (cdr e))) (h (car e)))
        (cond ((and (equal? h 'sqrt) (= (length args) 1)) (list '^ (car args) 1/2))
              (else (cons h args))))
      e))

; целое n, для которого a = n·w (a, w — упрощённые), иначе #f
(define (exp-int-multiple a w)
  (cond ((equal? a w) 1)
        ((and (op-expr? a) (equal? (car a) '*) (integer? (cadr a)))
         (let ((rest (cdr (cdr a))))
           (if (equal? (if (= (length rest) 1) (car rest) (cons '* rest)) w) (cadr a) #f)))
        (else #f)))

; замена ядра u = exp(w) на %t, при этом exp(n·w) (n целое) → %t^n
(define (subst-exp-kernel e u)
  (cond ((equal? e u) '%t)
        ((and (op-expr? e) (equal? (car e) 'exp) (= (length e) 2) (equal? (car u) 'exp)
              (exp-int-multiple (simplify (cadr e)) (cadr u)))
         (list '^ '%t (exp-int-multiple (simplify (cadr e)) (cadr u))))
        ((op-expr? e) (cons (car e) (map (lambda (a) (subst-exp-kernel a u)) (cdr e))))
        (else e)))

; замена всех вхождений выражения u на v
(define (replace-expr e u v)
  (cond ((equal? e u) v)
        ((op-expr? e) (cons (car e) (map (lambda (a) (replace-expr a u v)) (cdr e))))
        (else e)))

; ---------- корни многочлена ----------

; многочлен только от x и чисел (других символов и ядер нет)
(define (numeric-poly? f x) (every? (lambda (v) (equal? v x)) (variables f)))

; квадратное уравнение с числовым дискриминантом D; a, b — числа или выражения
(define (numeric-quadratic a b D cx)
  (let ((den-inv (simplify (list '^ (list '* 2 a) -1)))
        (nb (simplify (list '- b))))
    ; корень — символьный (^ D 1/2) с выносом квадратного множителя (не builtin sqrt: он даёт алгебраическое число);
    ; точный квадрат даёт рациональное число, отрицательный D — %i-форму
    (cond ((= D 0) (list (simplify (list '* nb den-inv))))
          ((or (> D 0) cx)
           (let ((s (simplify (list '^ D 1/2))))
             (list (expand (list '* den-inv (list '+ nb s)))
                   (expand (list '* den-inv (list '+ nb (list '* -1 s)))))))
          (else '()))))

(define (symbolic-quadratic a b D)
  (let ((den-inv (list '^ (list '* 2 a) -1))
        (s (list 'sqrt D)))
    (list (simplify (list '* den-inv (list '+ (list '- b) s)))
          (simplify (list '* den-inv (list '+ (list '- b) (list '* -1 s)))))))

(define (quadratic-roots a b c cx)
  (let ((D (expand (list '- (list '^ b 2) (list '* 4 a c)))))
    (cond ((number? D) (numeric-quadratic a b D cx))
          ; a x² + c = 0 с символьным c: x = ±√(-c/a)
          ((equal? b 0)
           (let ((s (list 'sqrt (simplify (list '* -1 c (list '^ a -1))))))
             (list s (simplify (list '* -1 s)))))
          (else (symbolic-quadratic a b D)))))

; заметка о разрешимости в радикалах для неприводимого множителя степени 5…7 (шаг GAL.3):
; ответ не меняется (корни — алгебраические числа и root-of, радикалы не выписываются), но в канал условий
; пишется доказанный факт — «в радикалах не выражается (группа Галуа S5, сертификат)» либо «разрешимо в радикалах
; (группа Галуа F20, сертификат)»; группа не определена точнее, но все кандидаты одного рода — так и сказано;
; не доказано — ничего не пишется
(define (solve-radical-note f x d)
  (if (and (>= d 5) (<= d 7))
      (let* ((v (galois-solvability f x)) (verdict (car v)))
        (if (equal? verdict 'unknown)
            #f
            (record-condition
             (list (if verdict 'solvable-by-radicals 'not-solvable-by-radicals) f)
             (string-append "solve: " (if verdict "разрешимо в радикалах" "в радикалах не выражается")
                            " ("
                            (if (equal? (nth v 1) :group)
                                (string-append "группа Галуа " (to-string (nth v 2)) ", сертификат")
                                (string-append "группа Галуа среди " (to-string (nth v 2)) ", все "
                                               (if verdict "разрешимы" "неразрешимы") "; сертификат кандидатов"))
                            ")"))))
      #f))

; неприводимый множитель степени >= 3: вещественные корни — алгебраические числа;
; если есть невещественные (и домен допускает) — добавляется (root-of f x)
(define (high-degree-roots f x cx)
  (if (numeric-poly? f x)
      (let ((rr (real-roots f x)) (d (degree f x)))
        (solve-radical-note f x d)
        (if (and cx (< (length rr) d))
            (append rr (list (list 'root-of f x)))
            rr))
      (list (list 'root-of f x))))

; условие применимости: нечисловой коэффициент/множитель, на который делит формула, ненулевой
(define (solve-nonzero-condition c why)
  ; числовые множители (2a ≠ 0 → a ≠ 0) отбрасываются — условие на каждый нечисловой неприводимый множитель
  (if (not (number? c))
      (map (lambda (f) (if (not (number? f)) (record-condition (list '/= f 0) (string-append "solve: " why))))
           (map car (cdr (factor-list c))))))

(define (solve-factor f x cx)
  (let ((d (degree f x)))
    (cond ((not (integer? d)) '())
          ((= d 0) '())
          ((= d 1)
           (solve-nonzero-condition (coeff f x 1) "коэффициент при x в линейном уравнении")
           (list (simplify (list '* (list '- (coeff f x 0)) (list '^ (coeff f x 1) -1)))))
          ((= d 2)
           (solve-nonzero-condition (coeff f x 2) "старший коэффициент квадратного уравнения")
           (quadratic-roots (coeff f x 2) (coeff f x 1) (coeff f x 0) cx))
          (else (high-degree-roots f x cx)))))

; многочлен по x (возможно с параметрами): корни неприводимых множителей над ℤ.
; Множители без x (параметры) считаются ненулевыми.
; Шаги (S.5, честность): степень 1 или единственный неприводимый множитель — рамка solve-linear/-quadratic/-polynomial
; (формула с дискриминантом — только для неприводимого квадратного); несколько множителей или кратность — solve-factor
(define (solve-poly e x cx)
  (if (not (step-log-enabled?))
      (solve-poly-plain e x cx)
      (let ((d (solve-deg e x)))
        (if (= d 1)
            (solve-poly-step e x cx)
            (let* ((fl (factor-list e))
                   (fs (filter (lambda (pe) (>= (solve-deg (car pe) x) 1)) (cdr fl))))
              (cond ((null? fs) '())
                    ((and (null? (cdr fs)) (= (cadr (car fs)) 1)) (solve-poly-step e x cx))
                    (else (solve-factor-step e fs fl x cx))))))))

; ---------- обращение функций: u(x) = v → значения x ----------

(define (asin-value c)
  (cond ((equal? c 0) 0) ((equal? c 1/2) '(* 1/6 pi)) ((equal? c 1) '(* 1/2 pi))
        ((equal? c -1/2) '(* -1/6 pi)) ((equal? c -1) '(* -1/2 pi))
        (else (list 'asin c))))
(define (acos-value c)
  (cond ((equal? c 0) '(* 1/2 pi)) ((equal? c 1/2) '(* 1/3 pi)) ((equal? c 1) 0)
        ((equal? c -1/2) '(* 2/3 pi)) ((equal? c -1) 'pi)
        (else (list 'acos c))))
(define (atan-value c)
  (cond ((equal? c 0) 0) ((equal? c 1) '(* 1/4 pi)) ((equal? c -1) '(* -1/4 pi))
        (else (list 'atan c))))

; целое k, при котором b^k = v (рациональные положительные b, v), иначе #f
(define (exact-log-search b v k)
  (cond ((> k 60) #f)
        ((= (simplify (list '^ b k)) v) k)
        ((= (simplify (list '^ b (- k))) v) (- k))
        (else (exact-log-search b v (+ k 1)))))
(define (exact-log b v)
  (cond ((and (rational-number? b) (rational-number? v) (> b 0) (> v 0) (not (= b 1)))
         (if (= v 1) 0 (exact-log-search b v 1)))
        (else #f)))

; шаги: сумма/произведение — solve-isolate (перенос слагаемого, деление), функции — solve-inverse-function
(define (invert-rule u) (if (and (op-expr? u) (member? (car u) '(+ *))) 'solve-isolate 'solve-inverse-function))
(define (invert-title u)
  (cond ((not (op-expr? u)) "Обращение")
        ((equal? (car u) '+) "Перенос слагаемых без неизвестной")
        ((equal? (car u) '*) "Деление на множитель без неизвестной")
        (else "Обращение функции")))
(define (invert-comment u v)
  (let ((h (if (op-expr? u) (car u) #f)))
    (cond ((equal? h '+) "слагаемые, не содержащие неизвестную, переносятся в правую часть")
          ((equal? h '*) "обе части делятся на множитель без неизвестной (он считается ненулевым)")
          ((equal? h 'exp) "exp(w) = v ⇒ w = log v (для v ≠ 0; в ℝ нужно v > 0)")
          ((equal? h 'log) "log(w) = v ⇒ w = exp(v)")
          ((equal? h 'sin) "sin w = v ⇒ w = arcsin v + 2πk или w = π − arcsin v + 2πk, k — целое")
          ((equal? h 'cos) "cos w = v ⇒ w = ±arccos v + 2πk, k — целое")
          ((equal? h 'tan) "tan w = v ⇒ w = arctan v + πk, k — целое")
          ((equal? h 'abs) "|w| = v ⇒ w = v или w = −v (v ≥ 0)")
          ((member? h '(^ sqrt)) "степенное уравнение: w^n = v ⇒ корни n-й степени из v (чётная степень — оба знака); b^w = v ⇒ w = log v / log b")
          (else ""))))

(define (invert u v x cx)
  (cond ((equal? u x) (list v))
        ((not (step-log-enabled?)) (invert-core u v x cx))
        (else (with-step ((invert-rule u) (invert-title u) (list '= (st-disp u) (st-disp v))
                          :comment (invert-comment u v)
                          :after (lambda (r) (st-sols x r)))
                (invert-core u v x cx)))))

(define (invert-core u v x cx)
  (cond ((not (op-expr? u)) (solve-fail u x))
        (else
         (let ((h (car u)) (args (cdr u)))
           (cond ((equal? h '+) (invert-sum args v x cx))
                 ((equal? h '*) (invert-prod args v x cx))
                 ((equal? h '^) (invert-pow (car args) (cadr args) v x cx))
                 ((equal? h 'sqrt) (invert-pow (car args) 1/2 v x cx))
                 ((equal? h 'exp) (invert-exp (car args) v x cx))
                 ((equal? h 'log) (invert (car args) (mk-exp v) x cx))
                 ((equal? h 'abs) (invert-abs (car args) v x cx))
                 ((equal? h 'sin) (invert-sin (car args) v x cx))
                 ((equal? h 'cos) (invert-cos (car args) v x cx))
                 ((equal? h 'tan) (invert-tan (car args) v x cx))
                 (else (solve-fail u x)))))))

(define (invert-all ws u v x cx)
  (append-map (lambda (w) (invert u w x cx)) ws))

; сумма: x только в одном слагаемом
(define (invert-sum args v x cx)
  (let ((dep (filter (lambda (a) (contains-sym? a x)) args))
        (rest (filter (lambda (a) (x-free? a x)) args)))
    (if (= (length dep) 1)
        (invert (car dep) (simplify (list '- v (cons '+ rest))) x cx)
        (solve-fail (cons '+ args) x))))

; произведение: x только в одном множителе, остальные считаются ненулевыми
(define (invert-prod args v x cx)
  (let ((dep (filter (lambda (a) (contains-sym? a x)) args))
        (rest (filter (lambda (a) (x-free? a x)) args)))
    (if (= (length dep) 1)
        (begin
          (solve-nonzero-condition (simplify (cons '* rest)) "множитель без неизвестной, на который делится уравнение")
          (invert (car dep) (simplify (list '* v (list '^ (cons '* rest) -1))) x cx))
        (solve-fail (cons '* args) x))))

; b^n = v (n — целое > 1): корни многочлена z^n - v, затем обращение b
(define (power-inversion b n v x cx)
  (if (= n 1)
      (invert b v x cx)
      (let ((zs (solve-poly (simplify (list '+ (list '^ '%z n) (list '* -1 v))) '%z cx)))
        (append-map (lambda (z)
                      (if (root-of? z)
                          (list (list 'root-of (simplify (list '- (list '^ b n) v)) x))
                          (invert b z x cx)))
                    zs))))

(define (invert-pow b e v x cx)
  (cond ((and (x-free? e x) (integer? e))
         (cond ((> e 0) (power-inversion b e v x cx))
               ((equal? v 0) '())
               (else (invert-pow b (- e) (simplify (list '^ v -1)) x cx))))
        ((and (x-free? e x) (equal? (type-of e) 'rational))
         ; b^(p/q) = v  ⇒  b^p = v^q (главное значение корня чётной степени неотрицательно)
         (let ((p (numer e)) (q (denom e)))
           (if (and (real-numeric? v) (< v 0) (= (mod q 2) 0))
               '()
               (invert (simplify (list '^ b p)) (simplify (list '^ v q)) x cx))))
        ((x-free? b x)
         ; b^e = v  ⇒  e = log v / log b (точное целое, если v — степень b)
         (let ((k (exact-log b v)))
           (invert e (if k k (simplify (list '/ (mk-log v) (mk-log b)))) x cx)))
        (else (solve-fail (list '^ b e) x))))

(define (invert-exp w v x cx)
  (cond ((equal? v 0) '())
        ((real-numeric? v)
         (cond ((> v 0) (invert w (mk-log v) x cx))
               (cx (invert w (simplify (list '+ (mk-log (- v)) (list '* '%i 'pi))) x cx))
               (else '())))
        (else (invert w (mk-log v) x cx))))

(define (invert-abs w v x cx)
  (cond ((and (real-numeric? v) (< v 0)) '())
        ((equal? v 0) (invert w 0 x cx))
        (else (invert-all (list v (simplify (list '* -1 v))) w v x cx))))

; sin/cos вне [-1, 1] при вещественном домене решений не имеют
(define (out-of-unit? v) (and (real-numeric? v) (or (> v 1) (< v -1))))

(define (invert-sin w v x cx)
  (if (and (not cx) (out-of-unit? v))
      '()
      (let ((a (asin-value v)) (k (fresh-k)))
        (invert-all (list (simplify (list '+ a (list '* 2 k 'pi)))
                          (simplify (list '+ 'pi (list '* -1 a) (list '* 2 k 'pi))))
                    w v x cx))))

(define (invert-cos w v x cx)
  (if (and (not cx) (out-of-unit? v))
      '()
      (let ((a (acos-value v)) (k (fresh-k)))
        (invert-all (list (simplify (list '+ a (list '* 2 k 'pi)))
                          (simplify (list '+ (list '* -1 a) (list '* 2 k 'pi))))
                    w v x cx))))

(define (invert-tan w v x cx)
  (let ((a (atan-value v)) (k (fresh-k)))
    (invert-all (list (simplify (list '+ a (list '* k 'pi)))) w v x cx)))

; ---------- решение выражения (= 0) ----------

(define (radical-kernel? k)
  (and (op-expr? k) (equal? (car k) '^) (equal? (caddr k) 1/2)))

; многочлен от единственного x-зависимого ядра u: решаем относительно t = u, затем обращаем u(x) = t
(define (solve-by-kernel e u x cx)
  (let ((e2 (simplify (subst-exp-kernel e u))))
    (if (or (contains-sym? e2 x) (not (polynomial? e2 '%t)))
        (solve-fail e x)
        (with-step ('solve-substitution "Замена переменной" (st-eq e x)
                    :comment (string-append (to-string (st-tname)) " = " (math-print u)
                                            ": уравнение становится многочленом от " (to-string (st-tname))
                                            "; найдя его корни, возвращаемся к x")
                    :after (lambda (r) (st-eq e2 '%t)))
          (append-map (lambda (tv)
                        (if (root-of? tv)
                            (list (list 'root-of e x))
                            (invert u tv x cx)))
                      (solve-poly e2 '%t cx))))))

; уравнение, линейное по радикалу r = w^(1/2): A + B r = 0 ⇒ A² - B² w = 0 (посторонние корни отсеет проверка)
(define (solve-radical e r x cx depth)
  (if (= (degree e r) 1)
      (let* ((a (coeff e r 0)) (b (coeff e r 1))
             (e2 (expand (list '- (list '^ a 2) (list '* (list '^ b 2) (cadr r))))))
        (with-step ('solve-square "Возведение в квадрат" (st-eq e x)
                    :comment "A + B√w = 0 ⇒ A² − B²·w = 0; возведение в квадрат может дать посторонние корни — они отсеиваются проверкой подстановкой"
                    :after (lambda (r) (st-eq e2 x)))
          (solve-expression e2 x cx (+ depth 1))))
      (solve-fail e x)))

; пара ядер sin w, cos w с одним аргументом (tan w simplify превращает в sin/cos)
(define (find-op ks h)
  (let ((l (filter (lambda (k) (and (op-expr? k) (equal? (car k) h))) ks)))
    (if (null? l) #f (car l))))
(define (sincos-pair ks)
  (and (= (length ks) 2)
       (let ((s (find-op ks 'sin)) (c (find-op ks 'cos)))
         (and s c (equal? (cadr s) (cadr c)) (list s c)))))

; a·sin w + b·cos w = 0 (a, b без x) ⇒ tan w = -b/a
(define (solve-sincos e s c x cx)
  (let* ((a (coeff e s 1)) (b (coeff (coeff e s 0) c 1)))
    (if (and (not (equal? a 0)) (x-free? a x) (x-free? b x)
             (equal? (simplify (list '- e (list '+ (list '* a s) (list '* b c)))) 0))
        (let ((tv (simplify (list '* -1 b (list '^ a -1)))))
          (with-step ('solve-trig-ratio "Деление на косинус: уравнение для тангенса" (st-eq e x)
                      :comment "a·sin w + b·cos w = 0 ⇒ tan w = −b/a (cos w = 0 не даёт корней: тогда и sin w = 0)"
                      :after (lambda (r) (list '= (list 'tan (cadr s)) tv)))
            (invert-tan (cadr s) tv x cx)))
        (solve-fail e x))))

; ---------- шаг PL: уравнения типа Ламберта ----------
; e = P0(x) + P1(x)·exp(w), w = b·x + d (b, d без x, b ≠ 0):
;   (X)  P1 = c·x, P0 = γ (без x):      c·x·e^(b x + d) = −γ        ⇒ x = W(−b·γ·e^(−d)/c)/b
;   (L)  P1 = c, P0 = p·x + q (p ≠ 0):  p·x + q + c·e^(b x + d) = 0  ⇒ x = −q/p − W((b·c/p)·e^(d − b·q/p))/b
; W — главная ветвь W₀ (lambert_w). Вещественные корни: аргумент ≥ 0 — единственный корень (W₀); отрицательный: < −1/e — корней
; нет, иначе их два (W₀ и W₋₁, ветви W₋₁ нет — отказ). Без декларации (ℂ) — главная ветвь W₀ и условие lambert-principal-branch
; (остальные комплексные корни — W_k). Корень принимается только после численной проверки подстановкой (polylog-evalf).
(define (lw-find-exp e x)
  (cond ((not (pair? e)) #f)
        ((and (equal? (car e) 'exp) (= (length e) 2) (not (x-free? (cadr e) x))) e)
        (else (let loop ((l (cdr e)))
                (if (null? l)
                    #f
                    (or (lw-find-exp (car l) x) (loop (cdr l))))))))

(define (lw-lin w x)   ; w = b·x + d → (b d) | #f
  (let ((s (simplify w)))
    (and (polynomial? s x) (= (degree s x) 1)
         (let ((b (simplify (coeff s x 1))) (d (simplify (coeff s x 0))))
           (and (x-free? b x) (x-free? d x) (not (equal? b 0)) (list b d))))))

(define (lw-symbols e)   ; все символы-операнды выражения (без голов), без повторов
  (cond ((symbol? e) (list e))
        ((pair? e) (foldl (lambda (acc a) (foldl (lambda (acc2 s) (if (member? s acc2) acc2 (append acc2 (list s)))) acc (lw-symbols a))) '() (cdr e)))
        (else '())))

(define (lw-test-points e x)   ; пробные значения параметров: список правил подстановки (без x)
  (let ((ps (filter (lambda (s) (not (or (equal? s x) (member? s '(pi %i e))))) (lw-symbols e))))
    (list (let loop ((l ps) (i 0) (acc '())) (if (null? l) acc (loop (cdr l) (+ i 1) (cons (list (car l) (+ 1/2 (/ i 3))) acc))))
          (let loop ((l ps) (i 0) (acc '())) (if (null? l) acc (loop (cdr l) (+ i 1) (cons (list (car l) (+ 7/5 (/ i 4))) acc)))))))

(define (lw-verify e x sol)
  (let ((tests (lw-test-points e x)))
    (let loop ((ts tests) (ok 0))
      (if (null? ts)
          (> ok 0)
          (let* ((r (car ts))
                 (ev (try (polylog-evalf (subst (list x (if (null? r) sol (subst r sol))) (if (null? r) e (subst r e)))) (lambda (er) #f))))
            (cond ((not ev) (loop (cdr ts) ok))
                  ((< (abs ev) 0.000001) (loop (cdr ts) (+ ok 1)))
                  (else #f)))))))

(define (solve-lambert e x cx)
  (let ((ex (lw-find-exp e x)))
    (and ex
         (let ((bd (lw-lin (cadr ex) x)))
           (and bd
                (let* ((f (replace-expr e ex '%lw)))
                  (and (polynomial? f '%lw) (= (degree f '%lw) 1)
                       (let ((p1 (simplify (coeff f '%lw 1))) (p0 (simplify (coeff f '%lw 0))) (b (car bd)) (d (cadr bd)))
                         (let ((sol
                                (cond ((and (not (x-free? p1 x)) (polynomial? p1 x) (= (degree p1 x) 1)
                                            (equal? (simplify (coeff p1 x 0)) 0) (x-free? p0 x))
                                       (let* ((c (simplify (coeff p1 x 1)))
                                              (s (simplify (list '* -1 b p0 (list 'exp (list '* -1 d)) (list '^ c -1)))))
                                         (cons s (simplify (list '* (list 'lambert_w s) (list '^ b -1))))))
                                      ((and (x-free? p1 x) (not (equal? p1 0)) (polynomial? p0 x) (= (degree p0 x) 1))
                                       (let* ((p (simplify (coeff p0 x 1))) (q (simplify (coeff p0 x 0)))
                                              (dd (simplify (list '+ d (list '* -1 b q (list '^ p -1)))))
                                              (s (simplify (list '* b p1 (list '^ p -1) (list 'exp dd)))))
                                         (cons s (simplify (list '+ (list '* -1 q (list '^ p -1))
                                                                 (list '* -1 (list 'lambert_w s) (list '^ b -1)))))))
                                      (else #f))))
                           (and sol
                                (let* ((s (car sol)) (v (cdr sol))
                                       (sn (try (polylog-evalf s) (lambda (er) #f))))
                                  (cond ((and (not cx) sn (< sn 0))
                                         (if (< sn (- (/ 1.0 (eval-num '(exp 1))))) '() #f))
                                        ((and (not cx) (not sn)) #f)
                                        ((not (lw-verify e x v)) #f)
                                        (else
                                         (if (or cx (not sn))
                                             (record-condition (list 'lambert-principal-branch x)
                                                               "главная ветвь W₀ функции Ламберта; остальные комплексные корни — ветви W_k"))
                                         (list v))))))))))))))

(define (solve-kernel e x cx depth)
  (let* ((ks (filter (lambda (k) (contains-sym? k x)) (variables e)))
         (others (filter (lambda (k) (not (equal? k x))) ks))
         (radicals (filter radical-kernel? others))
         (sc (sincos-pair ks)))
    (cond ((> depth 6) (solve-fail e x))
          ((and (= (length ks) 1) (not (equal? (car ks) x))) (solve-by-kernel e (car ks) x cx))
          (sc (solve-sincos e (car sc) (cadr sc) x cx))
          ((not (null? radicals)) (solve-radical e (car radicals) x cx depth))
          (else (let ((r (solve-lambert e x cx))) (if r r (solve-fail e x)))))))

; e — числитель (без знаменателя с x)
(define (solve-numerator e x cx depth)
  (cond ((x-free? e x) '())
        ((polynomial? e x) (solve-poly e x cx))
        (else (solve-kernel e x cx depth))))

; кандидат не обращает знаменатель в нуль (нечисловой результат — оставляем)
(define (den-nonzero? den s x)
  (if (special-solution? s)
      #t
      (let ((m (num-abs (replace-expr den x s))))
        (if m
            (> m 0.000000001)
            (not (equal? (subst (list '= x s) den) 0))))))

(define (solve-expression e x cx depth)
  (let* ((tg (together e))
         (den (denom tg)))
    (if (and (step-log-enabled?) (not (x-free? den x)))
        (record-step 'solve-clear-denominator "Умножение на знаменатель"
                     "дробь равна нулю, когда числитель равен нулю, а знаменатель не равен нулю" (st-eq e x) (st-eq (numer tg) x)))
    (let ((sols (solve-numerator (numer tg) x cx depth)))
      (if (x-free? den x)
          sols
          (let ((ok (filter (lambda (s) (den-nonzero? den s x)) sols)))
            (if (and (step-log-enabled?) (< (length ok) (length sols)))
                (record-step 'solve-exclude-denominator-roots "Исключение корней знаменателя"
                             (string-append "знаменатель " (math-print (st-disp den)) " обращается в нуль при отброшенных значениях")
                             (st-list sols) (st-list ok)))
            ok)))))

; ---------- проверка подстановкой и фильтрация по доменам ----------

(define (sqrt->pow e)
  (if (op-expr? e)
      (let ((args (map sqrt->pow (cdr e))))
        (if (and (equal? (car e) 'sqrt) (= (length args) 1))
            (list '^ (car args) 1/2)
            (cons (car e) args)))
      e))

; решение s удовлетворяет уравнению e0 = 0: точно (together·expand), иначе численно; нечисловое — оставляем
(define (solution-ok? e0 s x)
  (let ((m (num-abs (replace-expr e0 x s))))     ; численно, без simplify (алгебраические числа)
    (if m
        (< m 0.000001)
        (let ((r2 (together (expand (sqrt->pow (subst (list '= x s) e0))))))
          (cond ((equal? r2 0) #t)
                ((number? r2) #f)
                (else #t))))))

(define (candidate-ok? e0 s x)
  (or (special-solution? s) (solution-ok? e0 s x)))

; серии решений с параметром k раскрываем: (* 1/2 (+ a (* 2 k pi))) → a/2 + k·pi
(define (tidy s)
  (if (and (special-solution? s) (not (contains-sym? s 'root-of))) (expand s) s))

; содержит квадратный радикал (^ n 1/2) (после simplify n — целое без квадратных множителей, т. е. иррациональный корень)
(define (contains-radical? e)
  (and (op-expr? e)
       (or (and (equal? (car e) '^) (equal? (caddr e) 1/2) (integer? (cadr e)))
           (any? contains-radical? (cdr e)))))

(define (domain-ok? s ds)
  (every? (lambda (c)
            (and (not (equal? (in? s c) #f))
                 ; рациональное число + рациональное · √n (n не квадрат) иррационально: не лежит в ℕ, ℤ, ℚ
                 (not (and (domain? c) (<= (domain-rank c) 2) (contains-radical? s)))))
          ds))

(define (domain-set ds)
  (if (null? (cdr ds)) (car ds) (apply intersection ds)))

; отбор корней: шаг записывается, только если что-то отброшено
(define (st-filter-step rule title comment before after)
  (if (< (length after) (length before))
      (record-step rule title comment (st-list before) (st-list after))))

; шаг S.4: уравнение a = b → a − b = 0 (если правая часть не нуль)
(define (st-move-terms eq x)
  (if (and (list? eq) (not (null? eq)) (equal? (car eq) '=) (not (equal? (caddr eq) 0)))
      (record-step 'solve-move-terms "Перенос слагаемых в левую часть" "уравнение a = b равносильно a − b = 0"
                   eq (st-eq (equation->expr eq) x))))

(define (st-equation eq) (if (and (list? eq) (not (null? eq)) (equal? (car eq) '=)) eq (list '= eq 0)))

(define (solve-single eq x)
  (set! *k-counter* 0)
  (set! *solve-ks* '())
  (set! *solve-var* x)
  (with-step ('solve-equation (string-append "Решение уравнения относительно " (to-string x)) (st-equation eq))
    (solve-single-core eq x)))

(define (solve-single-core eq x)
  (let* ((ds (constraints-of x))
         (cx (every? (lambda (c) (equal? c complexes)) ds))
         (e0 (norm-tree (equation->expr eq)))
         (tg (together e0)))
    (cond ((equal? tg 0) (domain-set ds))
          ((x-free? tg x)
           (if (number? tg) (set) (solve-fail e0 x)))
          (else
           (if (step-log-enabled?) (st-move-terms eq x))
           (let* ((cands (solve-expression e0 x cx 0))
                  (ok (filter (lambda (s) (candidate-ok? e0 s x)) cands))
                  (tidied (map tidy ok))
                  (res (filter (lambda (s) (domain-ok? s ds)) tidied)))
             (if (step-log-enabled?)
                 (begin
                   (st-filter-step 'solve-check-roots "Проверка корней подстановкой"
                                   "посторонние корни (например, после возведения в квадрат) отбрасываются" cands ok)
                   (st-filter-step 'solve-domain-filter "Отбор корней по области значений"
                                   (string-append "решения, не принадлежащие объявленной области значений " (to-string x) ", отбрасываются")
                                   tidied res)))
             (list->set res))))))

; ---------- системы уравнений ----------
; (solve (list ур1 ур2 ...) (list x y ...)) → множество решений; решение — список равенств ((= x v1) (= y v2))
; в порядке переменных запроса (применимо через subst).
;   * линейные системы (коэффициенты могут быть символьными): метод Гаусса–Жордана с together на каждом шаге;
;     символьный ведущий элемент считается ненулевым (без ветвления); несовместная → {}; недоопределённая — свободные
;     переменные остаются символами: ((= x (+ 1 (* -1 y))) (= y y));
;   * нелинейные полиномиальные системы с рациональными коэффициентами (шаг 21i): приведённый lex-базис Грёбнера
;     (переменные — в порядке запроса, последняя — младшая) имеет треугольную форму: для каждой переменной v_k есть
;     элементы базиса только от v_k … v_n; решения строятся с конца — корни одномерного многочлена (существующий solve:
;     формулы, радикалы, алгебраические числа), подстановка в элементы для следующей переменной; несовместная система
;     (базис (1)) → {}; бесконечно много решений (свободная переменная) — ошибка; неприводимые множители без радикалов —
;     вещественные корни — явно, невещественные — (root-of f v) (как у одного уравнения), остальные неизвестные — многочлены от корня (шаг 21i'' (3));
;     символы вне списка неизвестных — параметры: ответ для общих значений параметров (lex по (неизвестные, параметры));
;   * нелинейные 2×2 с параметрами/иррациональными коэффициентами (запасной путь): результанты по каждой переменной
;     дают кандидатов, пары проверяются численно подстановкой в оба уравнения;
;   * остальное — ошибка «solve: не умею».

(define (lref l i) (if (= i 0) (car l) (lref (cdr l) (- i 1))))
(define (remove-at l i)
  (if (= i 0) (cdr l) (cons (car l) (remove-at (cdr l) (- i 1)))))
(define (index-of-first pred l i)
  (cond ((null? l) #f) ((pred (car l)) i) (else (index-of-first pred (cdr l) (+ i 1)))))

(define (system-fail eqs vars)
  (error (string-append "solve: не умею решать систему " (to-string eqs) " относительно " (to-string vars))))

; e (выражение = 0) линейно по vars → (c1 ... cn rhs), где Σ ci·vi = rhs; иначе #f
(define (linear-row e vars)
  (let* ((tg (together e)) (den (denom tg)) (num (numer tg)))
    (if (not (every? (lambda (v) (x-free? den v)) vars))
        #f
        (let* ((cs (map (lambda (v) (coeff num v 1)) vars))
               (c0 (subst (map (lambda (v) (list '= v 0)) vars) num))
               (lin (cons '+ (cons c0 (map2 (lambda (c v) (list '* c v)) cs vars)))))
          (if (and (every? (lambda (c) (every? (lambda (v) (x-free? c v)) vars)) cs)
                   (equal? (together (list '- num lin)) 0))
              (append (map (lambda (c) (together c)) cs) (list (together (list '* -1 c0))))
              #f)))))

(define (row-sub r s f) (map2 (lambda (a b) (together (list '- a (list '* f b)))) r s))
(define (row-scale r f) (map (lambda (a) (together (list '* f a))) r))
(define (elim r pn col)
  (let ((f (lref r col))) (if (equal? f 0) r (row-sub r pn f))))

; done — пары (столбец . строка) с единичным ведущим элементом; rest — строки без ведущих (все коэффициенты нули)
(define (rref-step done rest col n)
  (if (= col n)
      (cons done rest)
      (let ((i (index-of-first (lambda (r) (not (equal? (lref r col) 0))) rest 0)))
        (if (not i)
            (rref-step done rest (+ col 1) n)
            (let* ((p (lref rest i))
                   (pn (row-scale p (together (list '^ (lref p col) -1))))
                   (rest2 (map (lambda (r) (elim r pn col)) (remove-at rest i)))
                   (done2 (map (lambda (d) (cons (car d) (elim (cdr d) pn col))) done)))
              (rref-step (append done2 (list (cons col pn))) rest2 (+ col 1) n))))))

(define (gj-pivot done col)
  (let ((l (filter (lambda (d) (= (car d) col)) done))) (if (null? l) #f (cdr (car l)))))

(define (solve-linear rows vars)
  (let* ((n (length vars))
         (res (rref-step '() rows 0 n))
         (done (car res)) (rest (cdr res)))
    (if (any? (lambda (r) (not (equal? (last r) 0))) rest)
        (list)                                            ; несовместная система
        (let ((free (filter (lambda (j) (not (gj-pivot done j))) (range n))))
          (list
           (map2 (lambda (v j)
                   (let ((p (gj-pivot done j)))
                     (list '= v
                           (if p
                               (together (cons '+ (cons (last p)
                                                        (map (lambda (k) (list '* -1 (lref p k) (lref vars k))) free))))
                               v))))
                 vars (range n)))))))

; значение v в решении sol ((= x a) ...) удовлетворяет ограничениям домена
(define (solution-in-domains? sol)
  (every? (lambda (eq) (domain-ok? (caddr eq) (constraints-of (cadr eq)))) sol))

; модуль невязки выражения при численной подстановке всех значений решения
(define (residual e sol)
  (num-abs (foldl (lambda (acc eq) (replace-expr acc (cadr eq) (caddr eq))) e sol)))

(define (roots-of-resultant p v)
  (let ((rs (if (x-free? p v) '() (st-quiet (lambda () (solve-expression p v #t 0))))))
    (if (any? root-of? rs) (error "solve: не умею решать систему: корни результанта выражаются только через root-of") rs)))

(define (solve-nonlinear-resultant es vars)
  (if (not (and (= (length es) 2) (= (length vars) 2)))
      (system-fail es vars)
      (let* ((x (car vars)) (y (cadr vars))
             (tgs (map together es))
             (nums (map numer tgs)))
        (if (not (and (every? (lambda (tg) (and (x-free? (denom tg) x) (x-free? (denom tg) y))) tgs)
                      (every? (lambda (e) (and (polynomial? e x) (polynomial? e y))) nums)))
            (system-fail es vars)
            (let ((ry (resultant (car nums) (cadr nums) x))
                  (rx (resultant (car nums) (cadr nums) y)))
              (if (or (equal? ry 0) (equal? rx 0))
                  (system-fail es vars)                    ; общий множитель: бесконечно много решений
                  (let* ((ys (roots-of-resultant ry y))
                         (xs (roots-of-resultant rx x))
                         (pairs (append-map (lambda (a) (map (lambda (b) (list (list '= x a) (list '= y b))) ys)) xs))
                         (rs (map (lambda (p) (map (lambda (e) (residual e p)) nums)) pairs)))
                    (if (any? (lambda (r) (any? (lambda (m) (not m)) r)) rs)
                        (system-fail es vars)              ; параметры: численная проверка невозможна
                        (map car (filter (lambda (pr) (every? (lambda (m) (< m 0.000001)) (cdr pr)))
                                         (map2 cons pairs rs)))))))))))

;; ---------- нелинейные полиномиальные системы: базис Грёбнера (шаг 21i) ----------

(define (has-float? e)
  (cond ((number? e) (not (or (rational-number? e) (alg? e))))
        ((op-expr? e) (any? has-float? (cdr e)))
        (else #f)))

; числители уравнений, если система — многочлены от vars с рациональными коэффициентами (знаменатели без vars), иначе #f
(define (rational-poly-system es vars)
  (let ((tgs (map together es)))
    (and (every? (lambda (tg) (every? (lambda (v) (x-free? (denom tg) v)) vars)) tgs)
         (let ((nums (map numer tgs)))
           (and (every? (lambda (n) (and (not (has-float? n))
                                         (every? (lambda (k) (member? k vars)) (variables n))
                                         (every? (lambda (v) (polynomial? n v)) vars)))
                        nums)
                nums)))))

; значение выражения равно нулю: численно (|·| < 1e-6) или точно (expand); нечисловое и ненулевое — #f
(define (vanishes? e)
  (let ((m (num-abs e)))
    (if m (< m 0.000001) (equal? (expand e) 0))))

; --- параметры (шаг 21i'' (3)): символы вне списка неизвестных — коэффициенты из ℚ(параметры) ---
; *sol-params* — параметры текущей системы ('() — параметров нет). Базис строится lex по (неизвестные, параметры):
; параметры — младший блок, поэтому это базис Грёбнера над ℚ(параметры), если старшие коэффициенты ≠ 0 («общие значения»)
(define *sol-params* '())

; 0 / не 0 / «не знаю» для значения без численной оценки (параметры): #t, #f, 'unknown
(define *param-test-values* '(3/2 -5/7 11/3 2/9 7/5))
(define (param-point shift)
  (map2 (lambda (p j) (list '= p (+ shift (lref *param-test-values* (mod j 5))))) *sol-params* (range (length *sol-params*))))

; точное «= 0» доказывает нуль; иначе проверка в двух рациональных точках параметров (численно): это эвристика,
; не доказательство, но отличает верные формулы от неверных
(define (zero-status e)
  (let ((m (num-abs e)))
    (if m
        (< m 0.000001)
        (let ((r2 (together (expand (sqrt->pow e)))))
          (cond ((equal? r2 0) #t)
                ((number? r2) #f)
                (else
                 (let ((ms (map (lambda (sh)
                                  (num-abs (foldl (lambda (acc eq) (replace-expr acc (cadr eq) (caddr eq))) e (param-point sh))))
                                '(0 1/3))))
                   (cond ((any? (lambda (v) (not v)) ms) 'unknown)
                         ((every? (lambda (v) (< v 0.000001)) ms) #t)
                         (else #f)))))))))

; проверка «обращается в нуль» для подстановки в систему; с параметрами неопределённость — отказ, а не «нет»
(define (sol-vanishes? e)
  (if (null? *sol-params*)
      (vanishes? e)
      (let ((s (zero-status e)))
        (if (equal? s 'unknown)
            (error (string-append "solve: не умею проверить подстановкой решение системы с параметрами "
                                  (to-string *sol-params*) " (невязка " (math-print e) ")"))
            s))))

; --- расширение ℚ(α), α — корень неприводимого f (root-of): значения неизвестных — многочлены от символа %r ---

(define (rem-r e fr) (if (equal? e 0) 0 (poly-remainder e fr '%r)))

; коэффициенты при степенях u приводятся по модулю fr
(define (reduce-in-ext e u fr)
  (if (equal? e 0)
      0
      (let ((d (degree e u)))
        (expand (cons '+ (map (lambda (i) (list '* (rem-r (coeff e u i) fr) (list '^ u i))) (range (+ d 1))))))))

; (g s t): s·a + t·b = g (расширенный алгоритм Евклида по r)
(define (poly-ext-gcd a b r)
  (if (equal? b 0)
      (list a 1 0)
      (let* ((q (poly-quotient a b r)) (rm (poly-remainder a b r)) (res (poly-ext-gcd b rm r)))
        (list (car res) (caddr res) (expand (list '- (cadr res) (list '* (caddr res) q)))))))

; обратный к c по модулю fr (fr неприводим, c не делится на fr)
(define (inv-mod c fr)
  (let ((res (poly-ext-gcd c fr '%r)))
    (if (not (number? (car res)))
        (error "solve: внутренняя ошибка: элемент расширения не обратим")
        (rem-r (expand (list '* (cadr res) (list '^ (car res) -1))) fr))))

(define (ext-fail why)
  (error (string-append "solve: не умею решать систему: " why)))

; c — численно корень многочлена f из (root-of f v)
(define (root-of-zero? r v c)
  (let ((m (num-abs (replace-expr (cadr r) v c)))) (and m (< m 0.000001))))

; ветвь «остальные корни неприводимого f для переменной v» (root-of): остальные неизвестные — многочлены от корня
(define (ext-solve G vars k part fr es)
  (if (< k 0)
      (list part)
      (let* ((u (lref vars k))
             (later (drop vars (+ k 1)))
             (ps (filter (lambda (e) (not (equal? e 0)))
                         (map (lambda (g) (reduce-in-ext (expand (subst part g)) u fr)) (basis-for-var G u later)))))
        (cond ((null? ps)
               (error (string-append "solve: система " (to-string es) " имеет бесконечно много решений (свободная переменная "
                                     (to-string u) ")")))
              ((any? (lambda (p) (x-free? p u)) ps) '())     ; ненулевой элемент поля ℚ(α): ветвь без решений
              (else
               (let ((p (foldl (lambda (b q) (if (< (degree q u) (degree b u)) q b)) (car ps) (cdr ps))))
                 (if (not (= (degree p u) 1))
                     (ext-fail (string-append "переменная " (to-string u) " в расширении ℚ(корень root-of) определяется уравнением степени "
                                              (to-string (degree p u)) " (общее положение нарушено)")))
                 (let ((val (rem-r (expand (list '* -1 (coeff p u 0) (inv-mod (coeff p u 1) fr))) fr)))
                   (if (every? (lambda (q) (equal? (rem-r (expand (subst (list '= u val) q)) fr) 0)) ps)
                       (ext-solve G vars (- k 1) (cons (list '= u val) part) fr es)
                       '()))))))))

; решения с корнем f (неприводимый многочлен переменной v, root-of): %r → (root-of f v); как и для одного уравнения,
; это только «остальные» (невещественные) корни f, вещественные корни разобраны отдельно явными алгебраическими числами
(define (ext-branch G vars k part ps v f es)
  (cond ((not (null? *sol-params*))
         (ext-fail (string-append "корни многочлена от " (to-string v) " выражаются только через root-of, при параметрах это не поддерживается")))
        ((not (every? (lambda (eq) (rational-number? (caddr eq))) part))
         (ext-fail (string-append "корни многочлена от " (to-string v) " выражаются только через root-of, а последующие неизвестные иррациональны")))
        ((not (every? (lambda (q) (equal? (poly-remainder q f v) 0)) ps)) '())   ; f неприводим: общих корней нет
        (else
         (let* ((fr (subst (list '= v '%r) f))
                (re (list 'root-of f v))
                (parts (ext-solve G vars (- k 1) (cons (list '= v '%r) part) fr es)))
           (map (lambda (pt) (map (lambda (eq) (list '= (cadr eq) (replace-expr (caddr eq) '%r re))) pt)) parts)))))

; элементы базиса G для переменной v (индекс k): зависят от v и только от v, v_{k+1}, …, v_n (и параметров)
(define (basis-for-var G v later0)
  (basis-for-var* G v (append later0 *sol-params*)))
(define (basis-for-var* G v later)
  (filter (lambda (g) (and (contains-sym? g v)
                           (every? (lambda (u) (or (equal? u v) (member? u later))) (variables g))))
          G))

; домен переменной допускает комплексные значения (нет деклараций, кроме complexes)
(define (var-complex? v) (every? (lambda (c) (equal? c complexes)) (constraints-of v)))

; решения треугольной системы: переменные vars (k — индекс текущей, с конца), part — найденные (= v значение)
(define (triangular-solve G vars k part es)
  (if (< k 0)
      (list part)
      (let* ((v (lref vars k))
             (later (drop vars (+ k 1)))
             (ps (filter (lambda (e) (not (equal? e 0)))
                         (map (lambda (g) (expand (subst part g))) (basis-for-var G v later)))))
        (cond ((null? ps)
               (error (string-append "solve: система " (to-string es) " имеет бесконечно много решений (свободная переменная "
                                     (to-string v) ")")))
              ((any? (lambda (p) (x-free? p v)) ps)
               ; константа без v: ненулевое число — ветвь без решений; выражение с параметрами — решения лишь при особых значениях
               (if (and (not (null? *sol-params*)) (any? (lambda (p) (and (x-free? p v) (not (number? p)))) ps))
                   (error (string-append "solve: решения системы " (to-string es) " существуют только при особых значениях параметров: "
                                         (foldl (lambda (acc g) (string-append acc (if (equal? acc "") "" ", ") (math-print g) " = 0")) ""
                                                (filter (lambda (p) (and (x-free? p v) (not (number? p)))) ps))))
                   '()))
              (else
               (let* ((p (foldl (lambda (b q) (if (< (degree q v) (degree b v)) q b)) (car ps) (cdr ps)))
                      ; соглашение одного уравнения: вещественные корни — явно (рациональные, радикалы, алгебраические числа),
                      ; (root-of f v) — только остальные (невещественные) корни; домен v без комплексных значений — только вещественные
                      (all (map tidy-value (st-quiet (lambda () (solve-expression p v (var-complex? v) 0)))))
                      (roots (filter root-of? all))
                      (cands (filter (lambda (c) (not (root-of? c))) all)))
                 (append
                  (append-map (lambda (c)
                                (if (every? (lambda (q) (sol-vanishes? (subst (list '= v c) q))) ps)
                                    (triangular-solve G vars (- k 1) (cons (list '= v c) part) es)
                                    '()))
                              cands)
                  ; корни, не выражающиеся в радикалах: решение через root-of, остальные неизвестные — многочлены от корня
                  (append-map (lambda (r) (ext-branch G vars k part ps v (cadr r) es)) roots))))))))

; значение с радикалами/%i — раскрыть скобки: (* -1/2 (+ -5 …)) → 5/2 + …
(define (tidy-value c) (if (op-expr? c) (expand c) c))

; параметры системы: символы числителей, не входящие в vars (порядок появления); #f — есть не-символьные ядра или вещественные числа
(define (system-params es vars)
  (let* ((tgs (map together es))
         (nums (map numer tgs))
         (ks (append-map variables (append nums (map denom tgs)))))
    (and (every? (lambda (k) (or (member? k vars) (and (symbol? k) (not (member? k '(pi e %i)))))) ks)
         (foldl (lambda (acc k) (if (or (member? k vars) (member? k acc)) acc (append acc (list k)))) '() ks))))

; числители уравнений-многочленов от vars с коэффициентами из ℚ(параметры) → (числа . параметры), иначе #f
(define (param-poly-system es vars)
  (let ((params (system-params es vars)))
    (and params (not (null? params))
         (let* ((tgs (map together es)) (nums (map numer tgs)))
           (and (every? (lambda (n) (and (not (has-float? n)) (every? (lambda (v) (polynomial? n v)) vars))) nums)
                (cons nums params))))))

; старший (lex по vars) коэффициент элемента базиса — многочлен от параметров
(define (lex-lead-coeff g vars)
  (let ((v (index-of-first (lambda (w) (contains-sym? g w)) vars 0)))
    (if v
        (let ((w (lref vars v))) (lex-lead-coeff (coeff g w (degree g w)) vars))
        g)))

; условия общности: неконстантные множители старших коэффициентов и знаменателей
(define (generic-conditions G dens vars)
  (let ((lcs (append (map (lambda (g) (lex-lead-coeff g vars)) (filter (lambda (g) (any? (lambda (w) (contains-sym? g w)) vars)) G))
                     dens)))
    (foldl (lambda (acc f) (if (or (number? f) (member? f acc)) acc (append acc (list f))))
           '()
           (append-map (lambda (c) (if (number? c) '() (map car (cdr (factor-list c))))) lcs))))

; решения системы с параметрами: lex-базис по (vars, параметры); ответ — для общих значений параметров
(define (solve-param-system pp es vars)
  (let* ((nums (car pp)) (params (cdr pp))
         ; шаг S.1: рамка — шаг groebner-basis самого groebner становится вложенным
         (G (with-step ('parametric-basis "Базис Грёбнера с параметрами" (cons 'list es)
                        :comment "параметры рассматриваются как переменные младшего блока: базис над ℚ(параметры), если старшие коэффициенты ненулевые"
                        :after (lambda (G) (cons 'list G)))
              (groebner nums (append vars params) 'lex)))
         (pure (filter (lambda (g) (and (not (number? g)) (not (any? (lambda (w) (contains-sym? g w)) vars)))) G)))
    (cond ((equal? G '(1)) '())                                   ; идеал единичный: решений нет ни при каких значениях параметров
          ((not (null? pure))
           (error (string-append "solve: система " (to-string es) " совместна только при особых значениях параметров: "
                                 (foldl (lambda (acc g) (string-append acc (if (equal? acc "") "" ", ") (math-print g) " = 0")) "" pure)
                                 "; для общих значений решений нет")))
          (else
           (let ((conds (generic-conditions G (map (lambda (e) (denom (together e))) es) vars)))
             ; условия применимости ответа — в канал условий (всегда, не только при журнале шагов)
             (map (lambda (c) (record-condition (list '/= c 0) "solve: ответ для общих значений параметров (множитель старшего коэффициента или знаменателя)")) conds)
             (if (step-log-enabled?)
                 (record-step 'generic-parameters "Ответ для общих значений параметров"
                              (string-append "решения верны при общих значениях параметров " (to-string params)
                                             "; при обращении в нуль старших коэффициентов и знаменателей (условия ниже) система может вести себя иначе")
                              (cons 'list params) (cons 'list conds)))
             (set! *sol-params* params)
             (let* ((r (triangular-solve G vars (- (length vars) 1) '() es))
                    (ok (filter (lambda (sol) (every? (lambda (n) (sol-vanishes? (subst sol n))) nums)) r)))
               (set! *sol-params* '())
               ok))))))

; #f — система не полиномиальная над ℚ (запасной путь); иначе список решений.
; Шаг S.1: рамка polynomial-system — сквозной пример with-step: шаги базисов внутри становятся вложенными;
; результат #f (система не полиномиальная) отбрасывает рамку — запасной путь не оставляет шума в журнале
(define (solve-polynomial-system es vars)
  (with-step ('polynomial-system "Нелинейная система: метод базисов Грёбнера" (cons 'list es)
              :comment "система многочленов приводится к треугольному виду, затем решается обратной подстановкой"
              :after (lambda (sols) (if (null? sols) (list->set '()) sols)))
    (let ((nums (rational-poly-system es vars)))
      (if (not nums)
          (let ((pp (param-poly-system es vars)))
            (and pp (solve-param-system pp es vars)))
          ; lex-базис: нульмерная система — grevlex + FGLM (шаг 21i'' (2)), иначе прямой lex
          (let ((G (with-step ('triangular-system "Приведение к треугольному виду (lex-базис Грёбнера)" (cons 'list es)
                               :comment "лексикографический базис Грёбнера: последний многочлен — от одной переменной"
                               :after (lambda (G) (cons 'list G)))
                     (groebner-lex nums vars))))
            (if (equal? G '(1))
                '()
                (filter (lambda (sol) (or (contains-sym? sol 'root-of) (every? (lambda (n) (vanishes? (subst sol n))) nums)))
                        (triangular-solve G vars (- (length vars) 1) '() es))))))))

(define (solve-nonlinear es vars)
  (let ((r (solve-polynomial-system es vars)))
    (if (equal? r #f) (solve-nonlinear-resultant es vars) r)))

; шаг S.4: линейная система — одна крупная рамка (метод Гаусса–Жордана); внутренние операции со строками не пишутся
(define (st-equations eqs)
  (cons 'list (map (lambda (q) (if (and (list? q) (not (null? q)) (equal? (car q) '=)) q (list '= q 0)))
                   (if (op-expr? eqs) (list eqs) eqs))))

(define (st-system-answer sols)
  (cond ((null? sols) (list->set '()))
        ((null? (cdr sols)) (car sols))
        (else sols)))

(define (solve-linear-step eqs rows vars)
  (with-step ('solve-linear-system "Линейная система: метод Гаусса–Жордана" (st-equations eqs)
              :comment (lambda (sols)
                         (cond ((null? sols) "система несовместна: после приведения матрицы получена строка 0 = c, c ≠ 0")
                               ((any? (lambda (eq) (equal? (cadr eq) (caddr eq))) (car sols))
                                "система недоопределена: свободные переменные остаются параметрами, остальные выражены через них")
                               (else "расширенная матрица приводится к ступенчатому виду (ведущие элементы нормируются и исключаются из остальных строк): единственное решение")))
              :after st-system-answer)
    (solve-linear rows vars)))

(define (solve-system eqs vars)
  (if (or (null? vars) (not (every? symbol? vars)))
      (error "solve: переменные системы — непустой список символов, получено" vars)
      (let* ((es (begin (set! *sol-params* '()) (map equation->expr (if (op-expr? eqs) (list eqs) eqs))))
             (rows (map (lambda (e) (linear-row e vars)) es))
             (sols (if (every? (lambda (r) r) rows)
                       (solve-linear-step eqs rows vars)
                       (solve-nonlinear es vars))))
        (list->set (filter solution-in-domains? sols)))))

; (solve уравнение x) — одно уравнение; (solve (list ур ...) (list x ...)) — система
(define (solve eq x)
  (cond ((symbol? x) (solve-single eq x))
        ((and (list? x) (not (null? x))) (solve-system eq x))
        (else (error "solve: переменная — символ или список символов, получено" x))))

; ---------- проверка решений подстановкой (шаг 22.6, сертификат substitution) ----------

(define sc-params '(17/10 23/10 19/10 31/10 13/10 29/10 11/10 27/10))   ; значения параметров при численной проверке
(define sc-tol 0.00000001)

; символы-параметры выражения (без констант pi, %i)
(define (sc-free-syms e)
  (filter (lambda (s) (and (symbol? s) (not (member? s '(pi %i))))) (try (variables e) (lambda (err) '()))))

(define (sc-dedupe l)
  (foldl (lambda (acc a) (if (member? a acc) acc (append acc (list a)))) '() l))

; численная невязка уравнения e (лево − право) в решении sol ((= x v) ...): параметры — пробные числа.
; → (состояние значение): numeric (мала), bad (велика), skip (не вычисляется)
(define (sc-numeric e sol r)
  (let* ((names (map cadr sol))
         (ps (filter (lambda (s) (not (member? s names)))
                     (sc-dedupe (append (sc-free-syms e) (append-map (lambda (eq) (sc-free-syms (caddr eq))) sol)))))
         (vals (map2 list ps sc-params))
         (e1 (foldl (lambda (acc eq) (replace-expr acc (cadr eq) (caddr eq))) e sol))
         (n (try (num-abs (eval-num (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr))) e1 vals)))
                 (lambda (err) #f))))
    (cond ((not n) (list 'skip r))
          ((< n sc-tol) (list 'numeric n))
          (else (list 'bad (if r r n))))))

; невязка уравнения e в решении sol: exact — символьно 0 (simplify, затем expand+together)
(define (sc-residual e sol)
  (if (contains-sym? sol 'root-of)
      (list 'skip '())
      (let ((r (try (let ((s (simplify (subst sol e))))
                      (if (equal? s 0) 0 (simplify (together (expand s)))))
                    (lambda (err) #f))))
        (if (equal? r 0) (list 'exact 0) (sc-numeric e sol r)))))

(define (sc-worst sts)
  (cond ((member? 'bad sts) 'bad)
        ((member? 'skip sts) 'skip)
        ((member? 'numeric sts) 'numeric)
        (else 'exact)))

; (solve-check уравнения x решения) → (итог ((решение состояние (невязки)) ...)); решения — список (set->list ответа solve).
; итог: exact (все символьно), numeric (в том числе численно), partial (часть не проверена: root-of), skip (ничего не
; проверено), bad (есть решение с ненулевой невязкой), empty (решений нет)
(define (solve-check eqs x sols)
  (let* ((es (map equation->expr (if (or (not (list? eqs)) (op-expr? eqs)) (list eqs) eqs)))
         (rows (map (lambda (s)
                      (let* ((se (if (symbol? x) (list (list '= x s)) s))
                             (rs (map (lambda (e) (sc-residual e se)) es)))
                        (list s (sc-worst (map car rs)) (map cadr rs))))
                    sols))
         (sts (map cadr rows)))
    (list (cond ((null? sts) 'empty)
                ((member? 'bad sts) 'bad)
                ((every? (lambda (s) (equal? s 'exact)) sts) 'exact)
                ((every? (lambda (s) (equal? s 'skip)) sts) 'skip)
                ((member? 'skip sts) 'partial)
                (else 'numeric))
          rows)))
