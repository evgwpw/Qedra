; limit.lisp — пределы (Шаг 20); грузится после series.lisp
;
; (limit e x a)          — двусторонний предел при x → a
; (limit e x a 'plus)    — справа (x → a+);  (limit e x a 'minus) — слева
; a — число, символ, выражение без x или 'inf / '-inf (символы как в domain.lisp).
; Результат: значение, 'inf, '-inf, 'undefined (односторонние пределы различны) или невычисленная форма
; (limit e x a) / (limit e x a plus) — «не умею»; ошибкой не бывает (кроме неверных аргументов).
;
; Каскад lim-main (d — глубина рекурсии):
;   1. lim-combine: пределы подвыражений и определённое их сочетание (арифметика с ±inf: lim-add, lim-mul, lim-pow);
;      неопределённости (inf − inf, 0·inf, 0/0, 1^inf, ...) дают #f — «идём дальше»;
;      ограниченные осциллирующие множители (sin, cos, atan...) учитываются: ограниченное · 0 = 0, ограниченное + inf = inf;
;   2. ряды (lim-by-series): ведущий член c·(x−a)^k ряда Лорана; при x → ±inf подстановка x = ±1/t, t → 0+;
;   3. степени с переменным показателем: f^g = exp(g·log f) (lim-by-power);
;   4. правило Лопиталя для 0/0 и inf/inf (и 0·inf → частное), глубина ≤ lim-max-depth (lim-by-lhopital);
;   5. вынесение слагаемого (lim-by-sum), модуль (lim-by-abs);
;   6. алгоритм Грунца (lim-by-gruntz, модуль gruntz, шаги 21j.3, 21j.3′) — только на верхнем уровне; сведение к
;      x → +∞; отказ Грунца = #f (невычисленная форма). Место: exp-log с «башней» глубины ≥ 2 (lim-tower-depth) — ПЕРВЫМ
;      (до п. 1: старый каскад на них отказывает секундами); простые — последним, после п. 1–5, на любых выражениях.
; Переключатель (algorithm 'limit): auto (по умолчанию) | classic (без Грунца) | gruntz (только Грунц).
; Все внутренние имена — с префиксом lim-.

; Шаг 21h': модуль limit; lim-add (арифметика с ±inf) экспортируется для несобственных интегралов (integrate)
(module limit
  (export limit lim-add))

(define lim-max-depth 12)
(define lim-widths '(8 16 32))

; ---------- шаги (шаг S.4) ----------
; Верхняя рамка limit («Предел при x → a»); внутри — сработавший приём: limit-substitution (прямая подстановка),
; limit-combine (пределы подвыражений), limit-series (ведущий член ряда; при x → ±∞ внутри рамки limit-infinity — замена
; x = ±1/t), limit-power (f^g = exp(g·log f)), limit-lhopital (0/0, ∞/∞), limit-factor-leading (T1 + T2 = T1·(1 + T2/T1)),
; limit-abs (раскрытие модуля). Неудачные приёмы — рамки с результатом #f — отбрасываются. «До»/«после» шагов — невычисленные
; формы (limit e x a): checkSteps их не сравнивает.

(define (lim-quiet thunk) (if (step-log-enabled?) (call-quietly thunk) (thunk)))

(define (lim-pt-str a) (cond ((equal? a 'inf) "+∞") ((equal? a '-inf) "-∞") (else (math-print a))))
(define (lim-val-str v) (cond ((not v) "не существует") ((equal? v 'inf) "+∞") ((equal? v '-inf) "-∞")
                              ((equal? v 'undefined) "не определён") (else (math-print v))))
(define (lim-side-str side) (cond ((equal? side 'plus) " справа") ((equal? side 'minus) " слева") (else "")))
(define (lim-form e x a side) (if (equal? side 'both) (list 'limit e x a) (list 'limit e x a side)))
(define (lim-title x a side) (string-append "Предел при " (to-string x) " → " (lim-pt-str a) (lim-side-str side)))
; имя переменной ряда при x → ±∞ (в шагах — t, u, если неизвестная t)
(define (lim-tvar x) (if (equal? x 't) 'u 't))

(define (lim-join-limits args vs x)
  (foldl (lambda (acc p)
           (if (x-free? (car p) x)
               acc
               (string-append acc (if (equal? acc "") "" ", ") "lim " (math-print (car p)) " = " (lim-val-str (cadr p)))))
         "" (map2 list args vs)))

; ---------- значения: выражение (конечное), 'inf, '-inf ----------

(define (lim-inf? v) (or (equal? v 'inf) (equal? v '-inf)))
(define (lim-flip v) (if (equal? v 'inf) '-inf 'inf))

; знак конечного значения: 1, -1, 0 или #f (неизвестен)
(define (lim-sign c)
  (let ((n (int-num c)))
    (if n
        (cond ((> n 0) 1) ((< n 0) -1) (else 0))
        (let ((s (try (sign-of c) (lambda (err) 'unknown))))
          (cond ((equal? s 'positive) 1) ((equal? s 'negative) -1) ((equal? s 'zero) 0) (else #f))))))

(define (lim-signed s) (cond ((not s) #f) ((> s 0) 'inf) ((< s 0) '-inf) (else #f)))

(define (lim-add a b)
  (cond ((and (lim-inf? a) (lim-inf? b)) (if (equal? a b) a #f))
        ((lim-inf? a) a)
        ((lim-inf? b) b)
        (else (simplify (list '+ a b)))))

(define (lim-mul-inf i c)   ; i — ±inf, c — конечное
  (let ((s (lim-sign c)))
    (cond ((not s) #f) ((= s 0) #f) ((> s 0) i) (else (lim-flip i)))))

(define (lim-mul a b)
  (cond ((and (lim-inf? a) (lim-inf? b)) (if (equal? a b) 'inf '-inf))
        ((lim-inf? a) (lim-mul-inf a b))
        ((lim-inf? b) (lim-mul-inf b a))
        (else (simplify (list '* a b)))))

; функция от конечных значений: подстановка и свёртка констант; расходящиеся значения (0^-1, log 0) и выход в
; комплексные числа — #f (неопределённость)
(define (lim-finite-op h args)
  (let ((r (int-guard (lambda () (simplify (cons h args))))))
    (cond ((not r) #f)
          ((ser-bad? r) #f)
          ((and (contains-sym? r '%i) (not (contains-sym? args '%i))) #f)
          (else r))))

(define (lim-fn-inf h v)
  (let ((p (equal? v 'inf)))
    (cond ((equal? h 'exp) (if p 'inf 0))
          ((member? h '(log ln sqrt acosh)) (if p 'inf #f))
          ((equal? h 'atan) (if p '(* 1/2 pi) '(* -1/2 pi)))
          ((equal? h 'acot) 0)
          ((member? h '(tanh coth)) (if p 1 -1))
          ((member? h '(sinh asinh)) v)
          ((equal? h 'cosh) 'inf)
          ((equal? h 'abs) 'inf)
          ((member? h '(sech csch)) 0)
          (else #f))))

(define lim-fn-names '(exp log ln sqrt sin cos tan cot sec csc sinh cosh tanh coth sech csch asin acos atan acot asinh acosh atanh abs))

(define (lim-fn h v) (if (lim-inf? v) (lim-fn-inf h v) (lim-finite-op h (list v))))

(define (lim-pow-inf-base b e)   ; b = ±inf, e конечный
  (let ((s (lim-sign e)))
    (cond ((not s) #f)
          ((= s 0) #f)
          ((> s 0) (cond ((equal? b 'inf) 'inf)
                         ((integer? e) (if (= (mod e 2) 0) 'inf '-inf))
                         (else #f)))
          (else (if (or (equal? b 'inf) (integer? e)) 0 #f)))))

(define (lim-pow-inf-exp b e)    ; e = ±inf
  (cond ((lim-inf? b) (cond ((equal? b '-inf) #f) ((equal? e 'inf) 'inf) (else 0)))
        (else
         (let ((n (int-num b)))
           (cond ((not n) #f)
                 ((< (abs (- n 1)) 0.000000000001) #f)
                 ((> n 1) (if (equal? e 'inf) 'inf 0))
                 ((> n 0) (if (equal? e 'inf) 0 'inf))
                 (else #f))))))

(define (lim-pow b e)
  (cond ((and (equal? b 0) (equal? e 0)) #f)   ; 0^0 — неопределённость (раньше давало 1: (2^x + 3^x)^(1/x) при x → −∞)
        ((and (not (lim-inf? b)) (not (lim-inf? e))) (lim-finite-op '^ (list b e)))
        ((lim-inf? e) (lim-pow-inf-exp b e))
        (else (lim-pow-inf-base b e))))

(define (lim-fold-op f vs) (foldl (lambda (acc v) (and acc (f acc v))) (car vs) (cdr vs)))

(define (lim-op h vs)
  (cond ((equal? h '+) (lim-fold-op lim-add vs))
        ((equal? h '*) (lim-fold-op lim-mul vs))
        ((and (equal? h '^) (= (length vs) 2)) (lim-pow (car vs) (cadr vs)))
        ((and (equal? h 'sqrt) (= (length vs) 1)) (lim-pow (car vs) 1/2))
        ((and (member? h lim-fn-names) (= (length vs) 1)) (lim-fn h (car vs)))
        (else #f)))

; ---------- ограниченные выражения ----------

(define (lim-bounded? e x)
  (cond ((x-free? e x) #t)
        ((op-expr? e)
         (cond ((member? (car e) '(sin cos atan acot tanh sech)) #t)
               ((member? (car e) '(+ *)) (every? (lambda (a) (lim-bounded? a x)) (cdr e)))
               ((and (equal? (car e) '^) (integer? (caddr e)) (> (caddr e) 0)) (lim-bounded? (cadr e) x))
               (else #f)))
        (else #f)))

; ---------- шаг 1: пределы подвыражений ----------

(define (lim-values args x a side d)
  (map (lambda (z) (let ((v (lim-main z x a side (+ d 1)))) (if (equal? v 'undefined) #f v))) args))

(define (lim-combine-vs e args vs x)
  (cond ((every? (lambda (v) v) vs) (lim-op (car e) vs))
        ((member? (car e) '(+ *)) (lim-combine-bounded (car e) args vs x))
        (else #f)))

(define (lim-combine-plain e x a side d)
  (let* ((args (cdr e)) (vs (lim-values args x a side d)))
    (lim-combine-vs e args vs x)))

; прямая подстановка: пределы всех аргументов конечны и результат равен значению выражения в точке
(define (lim-direct? e x a r vs)
  (and (not (lim-inf? a)) (not (lim-inf? r)) (every? (lambda (v) (and v (not (lim-inf? v)))) vs)
       (equal? r (try (simplify (subst (list '= x a) e)) (lambda (err) #f)))))

(define (lim-combine-comment e args vs x)
  (string-append (cond ((equal? (car e) '+) "предел суммы равен сумме пределов")
                       ((equal? (car e) '*) "предел произведения равен произведению пределов")
                       ((equal? (car e) '^) "предел степени вычисляется по пределам основания и показателя")
                       (else "функция непрерывна: предел аргумента подставляется в функцию"))
                 ": " (lim-join-limits args vs x)))

; журнал включён: пределы подвыражений сначала считаются тихо; прямая подстановка — один шаг без вложенных,
; иначе рамка limit-combine с вложенными шагами подпределов
(define (lim-combine-logged e x a side d)
  (let* ((args (cdr e))
         (vs (call-quietly (lambda () (lim-values args x a side d))))
         (r (lim-combine-vs e args vs x)))
    (cond ((not r)
           (with-step ('limit-combine "Предел через пределы частей" (lim-form e x a side))
             (attempt-fail "пределы частей не определены (неопределённость)")
             #f))
          ((lim-direct? e x a r vs)
           (record-step 'limit-substitution "Прямая подстановка"
                        (string-append "функция непрерывна в точке " (to-string x) " = " (lim-pt-str a)
                                       ", предел равен значению: " (math-print r))
                        (lim-form e x a side) r)
           r)
          (else
           (with-step ('limit-combine "Предел через пределы частей" (lim-form e x a side)
                       :comment (lim-combine-comment e args vs x))
             (lim-combine-plain e x a side d))))))

(define (lim-combine e x a side d)
  (cond ((not (op-expr? e)) #f)
        ((step-log-enabled?) (lim-combine-logged e x a side d))
        (else (lim-combine-plain e x a side d))))

; часть слагаемых/множителей без предела, но ограничена: ограниченное·0 = 0, ограниченное + (±inf) = ±inf
(define (lim-combine-bounded h args vs x)
  (let ((bad (filter (lambda (p) (not (cadr p))) (map2 list args vs)))
        (good (filter (lambda (v) v) vs)))
    (if (or (null? good) (not (every? (lambda (p) (lim-bounded? (car p) x)) bad)))
        #f
        (let ((r (lim-op h good)))
          (cond ((and (equal? h '*) (equal? r 0)) 0)
                ((and (equal? h '+) (lim-inf? r)) r)
                (else #f))))))

; ---------- шаг 2: ряды ----------

; ведущий член c·t^k, t = x − a, по стороне
(define (lim-from-lead k c side)
  (cond ((> k 0) 0)
        ((= k 0) (simplify c))
        (else
         (let ((s (lim-sign c)))
           (cond ((not s) #f)
                 ((= s 0) #f)
                 ((equal? side 'plus) (lim-signed s))
                 ((equal? side 'minus) (lim-signed (if (= (mod k 2) 0) s (- 0 s))))
                 ((= (mod k 2) 0) (lim-signed s))
                 (else 'undefined))))))

; коэффициент без exp(…L…) и степеней с L в показателе: рост не быстрее многочлена от L
(define (lim-tame-slow? c)
  (cond ((not (op-expr? c)) #t)
        ((and (equal? (car c) 'exp) (contains-sym? (cdr c) '%L)) #f)
        ((and (equal? (car c) '^) (= (length c) 3) (contains-sym? (caddr c) '%L)) #f)
        (else (every? lim-tame-slow? (cdr c)))))

; коэффициент с log(x − a): «медленная» величина, предел при L = log t → −inf (только справа)
(define (lim-from-slow s k c side)
  (if (not (equal? side 'plus))
      #f
      (let ((c2 (replace-expr c (ser-lg s) '%L)))
        (if (contains-sym? c2 (ser-var s))
            #f
            (let ((v (lim-quiet (lambda () (lim-main c2 '%L '-inf 'both 0)))))
              (cond ((or (not v) (equal? v 'undefined)) #f)
                    ;; k > 0 и коэффициент → ±∞: 0 только для «ручного» роста (полином от L, log L); exp(…L…) или
                    ;; L^L растёт быстрее любой степени t = e^L — не знаем (шаг 21j.3: 8.14 давал неверное 1)
                    ((> k 0) (if (or (not (lim-inf? v)) (lim-tame-slow? c2)) 0 #f))
                    ((= k 0) v)
                    ((equal? v 'inf) 'inf)
                    ((equal? v '-inf) '-inf)
                    (else (lim-signed (lim-sign v)))))))))

; все коэффициенты ряда растут не быстрее многочлена от L = log t (иначе отброшенные члены могут обогнать степень t)
(define (lim-series-tame? s)
  (every? (lambda (c) (lim-tame-slow? (replace-expr c (ser-lg s) '%L))) (ser-cs s)))

(define (lim-from-series s side)
  (let ((k (ser-val s)) (c (car (ser-cs s))))
    (cond ((not (lim-series-tame? s)) #f)
          ((contains-sym? c (ser-var s)) (lim-from-slow s k c side))
          (else (lim-from-lead k c side)))))

; ненулевой ряд выражения: рабочий порядок растёт, пока не появится ненулевой член
(define (lim-series-try e x a ws)
  (if (null? ws)
      #f
      (let ((s (try (lim-quiet (lambda () (ser-compute e x a (car ws)))) (lambda (err) (if (ser-precision-err? err) 'retry #f)))))
        (cond ((not s) #f)
              ((or (equal? s 'retry) (null? (ser-cs s))) (lim-series-try e x a (cdr ws)))
              (else s)))))

; ряд при x → a; для ±inf — по переменной %t (x = ±1/t, t → 0+)
(define (lim-series-obj e x a)
  (cond ((equal? a 'inf) (lim-series-try (simplify (replace-expr e x '(^ %t -1))) '%t 0 lim-widths))
        ((equal? a '-inf) (lim-series-try (simplify (replace-expr e x '(* -1 (^ %t -1)))) '%t 0 lim-widths))
        (else (lim-series-try e x a lim-widths))))

(define (lim-eff-side a side) (if (lim-inf? a) 'plus side))

; пояснение шага limit-series: ведущий член ряда c·t^k и вывод по степени k
(define (lim-series-comment s x a)
  (let* ((k (ser-val s)) (c (car (ser-cs s))) (tv (if (lim-inf? a) (lim-tvar x) x))
         (base (cond ((or (lim-inf? a) (equal? a 0)) tv)
                     ((and (real-numeric? a) (< a 0)) (list '+ x (- 0 a)))
                     (else (list '- x a))))
         (slow (contains-sym? c (ser-var s)))
         (lead (if slow
                   (replace-expr c (ser-var s) tv)
                   (let ((p (cond ((= k 0) 1) ((= k 1) base) (else (list '^ base k)))))
                     (cond ((equal? p 1) c) ((equal? c 1) p) (else (list '* c p))))))
         (verdict (cond (slow "коэффициент содержит log: предел коэффициента берётся по L = log t → −∞")
                        ((> k 0) "степень положительна, поэтому предел равен 0")
                        ((= k 0) "степень равна нулю, поэтому предел равен коэффициенту")
                        (else "степень отрицательна: предел бесконечен, знак определяется знаком коэффициента и стороной")))
         (head (string-append (if (lim-inf? a) (string-append "в переменной " (to-string tv) " (t → 0+): ") "")
                              "ведущий член ряда " (math-print lead) " (степень " (to-string k) "): " verdict)))
    (if (lim-inf? a) head (string-append head "; ряд: " (math-print s)))))

(define (lim-by-series-core e x a side)
  (let ((s (lim-series-obj e x a)))
    (and s (with-step ('limit-series "Разложение в ряд: ведущий член"
                       (if (lim-inf? a)
                           (lim-form (simplify (replace-expr e x (if (equal? a 'inf) (list '^ (lim-tvar x) -1) (list '* -1 (list '^ (lim-tvar x) -1)))))
                                     (lim-tvar x) 0 'plus)
                           (lim-form e x a side))
                       :comment (lambda (r) (lim-series-comment s x a)))
             (let ((v (lim-from-series s (lim-eff-side a side)))) (if v v (begin (attempt-fail "ведущий член ряда не даёт предела") #f)))))))

; x → ±∞: рамка limit-infinity (замена x = ±1/t), внутри — ряд по t
(define (lim-by-series e x a side)
  (if (and (step-log-enabled?) (lim-inf? a))
      (with-step ('limit-infinity (string-append "Замена " (to-string x) " = " (if (equal? a 'inf) "1/" "-1/") (to-string (lim-tvar x)) ", " (to-string (lim-tvar x)) " → 0+")
                  (lim-form e x a side)
                  :comment "предел при x → ∞ сводится к пределу при t → 0+ от выражения, в котором x заменено на ±1/t")
        (lim-by-series-core e x a side))
      (lim-by-series-core e x a side)))

; знак выражения u вблизи a по стороне: 1, -1 или #f
(define (lim-sign-near u x a side)
  (let ((s (lim-series-obj u x a)))
    (if (or (not s) (contains-sym? (car (ser-cs s)) (ser-var s)))
        #f
        (let ((sg (lim-sign (car (ser-cs s)))) (k (ser-val s)) (sd (lim-eff-side a side)))
          (cond ((or (not sg) (= sg 0)) #f)
                ((equal? sd 'plus) sg)
                ((equal? sd 'minus) (if (= (mod k 2) 0) sg (- 0 sg)))
                ((= (mod k 2) 0) sg)
                (else #f))))))

; ---------- модуль: abs(u) → ±u по знаку u вблизи точки (на данной стороне) ----------

(define (lim-has-abs? e) (and (op-expr? e) (or (equal? (car e) 'abs) (any? lim-has-abs? (cdr e)))))

; #f, если знак аргумента abs определить не удалось
(define (lim-resolve-abs e x a side)
  (cond ((not (op-expr? e)) e)
        ((and (equal? (car e) 'abs) (= (length e) 2) (not (x-free? (cadr e) x)))
         (let ((u (lim-resolve-abs (cadr e) x a side)))
           (and u (let ((sg (lim-sign-near u x a side)))
                    (cond ((not sg) #f) ((> sg 0) u) (else (simplify (list '* -1 u))))))))
        (else
         (let ((args (map (lambda (z) (lim-resolve-abs z x a side)) (cdr e))))
           (and (every? (lambda (v) v) args) (cons (car e) args))))))

(define (lim-by-abs-core e x a side)
  (let ((one (lambda (sd) (let ((r (lim-resolve-abs e x a sd))) (and r (lim-main r x a sd 1))))))
    (cond ((lim-inf? a) (one 'plus))
          ((not (equal? side 'both)) (one side))
          (else (let ((p (one 'plus)) (m (one 'minus)))
                  (cond ((or (not p) (not m)) #f)
                        ((equal? p m) p)
                        (else 'undefined)))))))

(define (lim-by-abs e x a side)
  (if (not (lim-has-abs? e))
      #f
      (with-step ('limit-abs "Раскрытие модуля" (lim-form e x a side)
                  :comment "знак аргумента модуля определяется вблизи точки; |u| заменяется на u или −u, двусторонний предел — сравнение односторонних")
        (lim-by-abs-core e x a side))))

; ---------- θ и δ: heaviside(u) → 0/1 по знаку u вблизи точки, dirac(u) → 0 при u ↛ 0 ----------
; Односторонний предел через скачок определён (θ(t) при t → 0⁺ равен 1), двусторонний с разными
; сторонами — 'undefined; знак u не определён или u → 0 у δ — #f (предел не вычислен).

(define (lim-has-step? e x)
  (and (op-expr? e)
       (or (and (member? (car e) '(heaviside dirac)) (= (length e) 2) (not (x-free? (cadr e) x)))
           (any? (lambda (z) (lim-has-step? z x)) (cdr e)))))

(define (lim-resolve-step e x a side)
  (cond ((not (op-expr? e)) e)
        ((and (equal? (car e) 'heaviside) (= (length e) 2) (not (x-free? (cadr e) x)))
         (let ((sg (lim-sign-near (cadr e) x a side)))
           (cond ((not sg) #f) ((> sg 0) 1) (else 0))))
        ((and (equal? (car e) 'dirac) (= (length e) 2) (not (x-free? (cadr e) x)))
         (let ((sg (lim-sign-near (cadr e) x a side)))
           (and sg (let ((lu (lim-main (cadr e) x a side 1)))
                     (and lu (not (equal? lu 0)) 0)))))
        (else
         (let ((args (map (lambda (z) (lim-resolve-step z x a side)) (cdr e))))
           (and (every? (lambda (v) v) args) (cons (car e) args))))))

(define (lim-by-step-core e x a side)
  (let ((one (lambda (sd) (let ((r (lim-resolve-step e x a sd))) (and r (lim-main r x a sd 1))))))
    (cond ((lim-inf? a) (one 'plus))
          ((not (equal? side 'both)) (one side))
          (else (let ((p (one 'plus)) (m (one 'minus)))
                  (cond ((or (not p) (not m)) #f)
                        ((equal? p m) p)
                        (else 'undefined)))))))

(define (lim-by-step e x a side)
  (if (not (lim-has-step? e x))
      #f
      (with-step ('limit-step "Ступенька Хевисайда и дельта" (lim-form e x a side)
                  :comment "θ(u) заменяется на 1 или 0 по знаку u вблизи точки, δ(u) — на 0 (u не стремится к 0); двусторонний предел — сравнение односторонних")
        (lim-by-step-core e x a side))))

; ---------- шаг 3: f^g = exp(g·log f) ----------

(define (lim-by-power e x a side d)
  (if (and (op-expr? e) (equal? (car e) '^) (= (length e) 3) (not (x-free? (caddr e) x)) (< d lim-max-depth))
      (let ((g (simplify (list '* (caddr e) (list 'log (cadr e))))))
        (with-step ('limit-power "Степень с переменным показателем" (lim-form e x a side)
                    :comment "f^g = exp(g·log f), поэтому lim f^g = exp(lim g·log f)")
          (let ((v (with-step ('limit-power-exponent "Предел показателя g·log f" (lim-form g x a side))
                     (lim-main g x a side (+ d 1)))))
            (cond ((or (not v) (equal? v 'undefined)) #f)
                  ((equal? v 'inf) 'inf)
                  ((equal? v '-inf) 0)
                  (else (lim-finite-op 'exp (list v)))))))
      #f))

; INT.DEF2: u^r с числовым r < 0 и u → 0: ±∞ по знаку u вблизи точки (x^(−1/2) → ∞ при x → 0+); на вложенном уровне
; (atan(x^(−1/2))) ряд Пюизё и Грунц не вызываются, поэтому знак берётся напрямую
(define (lim-by-neg-power e x a side d)
  (if (and (op-expr? e) (equal? (car e) '^) (= (length e) 3) (real-numeric? (caddr e)) (< (caddr e) 0)
           (not (x-free? (cadr e) x)) (< d lim-max-depth))
      (let ((v (lim-quiet (lambda () (lim-main (cadr e) x a side (+ d 1))))))
        (if (equal? v 0)
            (let ((s (lim-sign-near (cadr e) x a side)))
              (cond ((not s) #f)
                    ((> s 0) 'inf)
                    ((integer? (caddr e)) (if (even? (caddr e)) 'inf '-inf))
                    (else #f)))
            #f))
      #f))

; ---------- шаг 4: правило Лопиталя ----------

(define (lim-zero? v) (and v (not (lim-inf? v)) (equal? v 0)))

; произведение списка множителей
(define (lim-prod fs) (if (null? fs) 1 (simplify (cons '* fs))))

; степень с отрицательным числовым показателем: основание в знаменателе
(define (lim-den-factor? f)
  (and (op-expr? f) (equal? (car f) '^) (= (length f) 3) (real-numeric? (caddr f)) (< (caddr f) 0)))

; обратная величина множителя (Шаг 21c: 1/exp(u) → exp(-u), (b^e)^-1 → b^-e делает сам simplify)
(define (lim-recip f) (simplify (list '^ f -1)))

; список из двух выражений (числитель знаменатель) или #f
(define (lim-split-quotient e x a side d)
  (let* ((fs (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))
         (dens (filter lim-den-factor? fs)))
    (if (not (null? dens))
        (list (lim-prod (filter (lambda (f) (not (lim-den-factor? f))) fs))
              (lim-prod (map (lambda (f) (simplify (list '^ (cadr f) (- 0 (caddr f))))) dens)))
        ;; 0·inf: множители с пределом 0 переносим в знаменатель
        (let* ((vs (lim-quiet (lambda () (lim-values fs x a side d))))
               (zs (filter (lambda (p) (lim-zero? (cadr p))) (map2 list fs vs)))
               (rest (filter (lambda (p) (not (lim-zero? (cadr p)))) (map2 list fs vs))))
          (if (and (every? (lambda (v) v) vs) (not (null? zs)) (any? (lambda (p) (lim-inf? (cadr p))) rest))
              (list (lim-prod (map car rest))
                    (lim-prod (map (lambda (p) (lim-recip (car p))) zs)))
              #f)))))

(define (lim-lhopital-form? ln ld)
  (and ln ld (not (equal? ln 'undefined)) (not (equal? ld 'undefined))
       (or (and (lim-zero? ln) (lim-zero? ld))
           (and (lim-inf? ln) (lim-inf? ld)))))

(define (lim-by-lhopital e x a side d)
  (if (>= d lim-max-depth)
      #f
      (let ((nd (lim-split-quotient e x a side d)))
        (if (not nd)
            #f
            (let ((ln (lim-quiet (lambda () (lim-main (car nd) x a side (+ d 1)))))
                  (ld (lim-quiet (lambda () (lim-main (cadr nd) x a side (+ d 1))))))
              (if (not (lim-lhopital-form? ln ld))
                  #f
                  (let ((dn (lim-quiet (lambda () (simplify (diff x (car nd))))))
                        (dd (lim-quiet (lambda () (simplify (diff x (cadr nd)))))))
                    (if (equal? dd 0)
                        #f
                        (with-step ('limit-lhopital "Правило Лопиталя" (lim-form e x a side)
                                    :comment (string-append "неопределённость " (if (lim-zero? ln) "0/0" "∞/∞") ": числитель "
                                                            (math-print (car nd)) " → " (lim-val-str ln) ", знаменатель "
                                                            (math-print (cadr nd)) " → " (lim-val-str ld)
                                                            "; lim f/g = lim f′/g′"))
                          (if (step-log-enabled?)
                              (record-step 'limit-derivatives "Производные числителя и знаменателя" ""
                                           (lim-form (list '/ (car nd) (cadr nd)) x a side)
                                           (lim-form (list '/ dn dd) x a side)))
                          (let ((v (lim-main (simplify (list '* dn (list '^ dd -1))) x a side (+ d 1)))) (if v v (begin (attempt-fail "предел производных не вычислен") #f))))))))))))

; ---------- разность растущих слагаемых: T1 + T2 + ... = Ti·(1 + Σ Tj/Ti) ----------

(define (lim-sum-try e x a side d terms)
  (if (null? terms)
      #f
      (let ((ti (car terms)))
        (or (with-step ('limit-factor-leading "Вынесение слагаемого за скобку" (lim-form e x a side)
                        :comment (string-append "T1 + T2 + … = T·(1 + (остальные)/T), где T = " (math-print ti)
                                                ": предел сводится к lim T · (1 + lim (остальные)/T)"))
              (let* ((others (filter (lambda (z) (not (equal? z ti))) (cdr e)))
                     (r (simplify (cons '+ (map (lambda (z) (simplify (list '* z (lim-recip ti)))) others))))
                     (v (lim-main r x a side (+ d 1))))
                (and v (not (lim-inf? v)) (not (equal? v 'undefined))
                     (let ((s (simplify (list '+ 1 v))) (lt (lim-main ti x a side (+ d 1))))
                       (and lt (not (equal? lt 'undefined)) (not (equal? s 0)) (lim-mul lt s))))))
            (lim-sum-try e x a side d (cdr terms))))))

(define (lim-by-sum e x a side d)
  (if (and (op-expr? e) (equal? (car e) '+) (< d 3))
      (lim-sum-try e x a side d (filter (lambda (z) (not (x-free? z x))) (cdr e)))
      #f))

; ---------- алгоритм Грунца (шаг 21j.3) ----------
; Место в каскаде: В КОНЦЕ и только на верхнем уровне (d = 0). Так прежние ответы и шаги (Лопиталь для eˣ/x² и т. п.)
; не меняются: Грунц лишь достраивает то, что старый каскад не взял. Цена — время отказа старого каскада (до 16 с на
; сложных башнях exp-log, 8.20); для них есть (set-algorithm 'limit 'gruntz). Внутри рекурсии (подпределы, производные
; Лопиталя) Грунц не вызывается: на растущих выражениях он только тратит время. Попытка — только если в выражении есть
; exp/log/гиперболические или степень с x в показателе (иначе #f).
; Переключатель (algorithm 'limit): auto — каскад с Грунцем; classic — без Грунца; gruntz — только Грунц.
; Сведение к x → +∞ (gruntz-limitinf): x → −∞ — x = −t, x → a+ — x = a + 1/t, x → a− — x = a − 1/t (t → +∞); t — свежий %lx.
; Двусторонний при конечном a — оба, равны → значение, разные → undefined; отказ любой стороны → #f.

(algorithm-register 'limit '(auto gruntz classic) 'auto)

(define lim-gr-heads '(exp log ln sinh cosh tanh coth sech csch asinh acosh atanh acoth))

(define (lim-gr-relevant? e x)
  (and (op-expr? e) (not (x-free? e x))
       (or (member? (car e) lim-gr-heads)
           (and (equal? (car e) '^) (= (length e) 3) (not (x-free? (caddr e) x)))
           (any? (lambda (z) (lim-gr-relevant? z x)) (cdr e)))))

; подстановка x → f(t), где t → +∞, для стороны dir ('plus/'minus; для ±inf не используется)
(define (lim-gr-sub a dir)
  (cond ((equal? a 'inf) '%lx)
        ((equal? a '-inf) (list '* -1 '%lx))
        ((equal? dir 'plus) (list '+ a (list '^ '%lx -1)))
        (else (list '+ a (list '* -1 (list '^ '%lx -1))))))

(define (lim-gr-mrv-str ms) (string-append "{" (foldl (lambda (acc m) (string-append acc (if (equal? acc "") "" ", ") (math-print m))) "" ms) "}"))

; крупные подшаги (только при включённом журнале; считаются тихо, повторно): MRV-множество и ведущий член ω^e
(define (lim-gr-explain e1 tv v)
  (let ((info (try (call-quietly (lambda () (list (gruntz-mrv e1 '%lx) (gruntz-leadterm e1 '%lx))))
                   (lambda (err) #f))))
    (if (and info (car info) (cadr info))
        (let* ((d (lambda (z) (replace-expr z '%lx tv)))
               (ms (map d (car info))) (lt (cadr info)) (tf (lim-form (d e1) tv 'inf 'plus)))
          (record-step 'limit-gruntz-mrv "Самые быстрые подвыражения (MRV)"
                       (string-append "множество MRV: " (lim-gr-mrv-str ms)
                                      "; в него входят подвыражения, растущие быстрее всех остальных (одного класса роста)")
                       tf (cons 'vector ms))
          (record-step 'limit-gruntz-lead "Ведущий член ω^e"
                       (string-append "ω — быстрая величина, стремящаяся к 0+; ведущий член c·ω^e: c = " (math-print (d (car lt)))
                                      ", e = " (math-print (cadr lt))
                                      "; при e > 0 предел 0, при e < 0 — ±∞ по знаку c, при e = 0 — предел c")
                       tf v)))))

; одна сторона / бесконечность: значение, 'inf, '-inf или #f
(define (lim-gr-side e x a dir)
  (let* ((sub (simplify (lim-gr-sub a dir)))
         (e1 (simplify (replace-expr e x sub)))
         (tv (lim-tvar x)))
    (if (and (step-log-enabled?) (not (equal? a 'inf)))
        (record-step 'limit-gruntz-substitution
                     (string-append "Замена " (to-string x) " = " (math-print (replace-expr sub '%lx tv)))
                     (string-append "предел при " (to-string x) " → " (lim-pt-str a)
                                    (if (lim-inf? a) "" (if (equal? dir 'plus) "+" "−"))
                                    " сводится к пределу при " (to-string tv) " → +∞ (замена " (to-string x) " = "
                                    (math-print (replace-expr sub '%lx tv)) ")")
                     (lim-form e x a dir) (lim-form (replace-expr e1 '%lx tv) tv 'inf 'plus)))
    (let ((v (lim-quiet (lambda () (gruntz-limitinf e1 '%lx)))))
      (if (and v (step-log-enabled?)) (lim-gr-explain e1 tv v))
      v)))

(define (lim-gr-core e x a side)
  (cond ((lim-inf? a) (lim-gr-side e x a 'plus))
        ((not (equal? side 'both)) (lim-gr-side e x a side))
        (else (let* ((p (lim-gr-side e x a 'plus)) (m (and p (lim-gr-side e x a 'minus))))
                (cond ((or (not p) (not m)) #f)
                      ((equal? p m) p)
                      (else 'undefined))))))

(define (lim-by-gruntz e x a side &rest force)
  (let ((mode (algorithm 'limit)))
    (if (or (equal? mode 'classic) (and (equal? mode 'auto) (null? force) (not (lim-gr-relevant? e x))))
        #f
        (with-step ('limit-gruntz "Сравнение скоростей роста (алгоритм Грунца)" (lim-form e x a side)
                    :comment "выделяется множество самых быстро меняющихся подвыражений (MRV), через него выражается малая величина ω → 0+, предел определяется ведущим членом c·ω^e")
          (let ((v (lim-gr-core e x a side))) (if v v (begin (attempt-fail "алгоритм Грунца не определил предел") #f)))))))

; Порядок auto при d = 0 (шаг 21j.3′): exp-log с «башней» глубины ≥ lim-tower-min (2) — Грунц ПЕРВЫМ (combine/ряды/Лопиталь
; на таких выражениях тратят секунды и десятки секунд на отказ, а Грунц — 15–60 мс); простые (eˣ/x², (1+1/x)ˣ, x ln x)
; — прежний каскад combine → series → power → lhopital → sum → abs (шаги Лопиталя/рядов, как в учебнике), Грунц — последним.
(define lim-tower-min 2)
(define (lim-gruntz-first? e x) (and (equal? (algorithm 'limit) 'auto) (lim-gr-relevant? e x)))

; глубина вложенности exp/log/гиперболических с x внутри (башня)
(define (lim-tower-depth e x)
  (if (and (op-expr? e) (not (x-free? e x)))
      (let ((m (foldl (lambda (acc z) (max acc (lim-tower-depth z x))) 0 (cdr e))))
        (if (or (member? (car e) lim-gr-heads)
                (and (equal? (car e) '^) (= (length e) 3) (not (x-free? (caddr e) x))))
            (+ m 1)
            m))
      0))

; ---------- каскад ----------

(define (lim-main e0 x a side d)
  (let ((e (simplify e0)))
    (cond ((x-free? e x) e)
          ((equal? e x) a)
          ((lim-has-step? e x) (lim-by-step e x a side))
          ((equal? (algorithm 'limit) 'gruntz) (lim-by-gruntz e x a side))
          (else
           (let* ((gr? (and (= d 0) (lim-gruntz-first? e x)))   ; Грунц применим (exp-log, верхний уровень)
                  (depth (if gr? (lim-tower-depth e x) 0))
                  (tower? (>= depth lim-tower-min)))
             (or (and tower? (lim-by-gruntz e x a side))
                 (lim-combine e x a side d)
                 (lim-by-series e x a side)
                 (lim-by-power e x a side d)
                 (lim-by-neg-power e x a side d)
                 (lim-by-lhopital e x a side d)
                 (lim-by-sum e x a side d)
                 (lim-by-abs e x a side)
                 ; последняя попытка: простые exp-log (глубина < lim-tower-min), затем любые выражения верхнего уровня
                 ; (корни, дроби степеней: √(x+√x) − √x), на которых Грунц отвечает, а старый каскад — нет
                 (and (= d 0) (not tower?) (lim-by-gruntz e x a side #t))))))))

; (limit e x a [side]) — см. заголовок файла
(define (limit e x a0 &rest more)
  (let ((side (if (null? more) 'both (car more))) (a (simplify a0)))
    (cond ((not (symbol? x)) (error "limit: переменная — символ"))
          ((not (member? side '(both plus minus))) (error "limit: сторона — 'plus или 'minus"))
          ((not (x-free? a x)) (error "limit: точка не должна содержать переменную"))
          (else
           (let ((r (int-guard (lambda ()
                                 (with-step ('limit (lim-title x a side) (lim-form e x a side))
                                   (let ((v (lim-main e x a side 0))) (if v v (begin (attempt-fail "предел не вычислен: приёмы каскада не дали значения") #f))))))))
             (cond (r r)
                   ((null? more) (list 'limit e x a))
                   (else (list 'limit e x a side))))))))
